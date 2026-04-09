import discord
from discord.ext import commands
import re
import random
import ast
import json
import os
from collections import defaultdict

# ---------- 骰子核心 ----------
class DiceResult:
    def __init__(self, raw_expr, rolls, total=None, text=None, success=None, filtered_rolls=None):
        self.raw_expr = raw_expr
        self.rolls = rolls
        self.total = total
        self.text = text
        self.success = success
        self.filtered_rolls = filtered_rolls

    def format(self):
        rolls_str = ', '.join(map(str, self.rolls))
        base = f"{self.raw_expr}：{self.text or ''}"
        base += f" {self.total} [{rolls_str}]" if self.total is not None else f" {rolls_str}"
        if self.filtered_rolls:
            base += f"\n符合條件：{', '.join(map(str, self.filtered_rolls))}"
        if self.success is not None:
            base += f" 成功數 {self.success}"
        return base

def roll_dice(sides): return random.randint(1, sides)

def parse_modifiers(expr):
    mod_match = re.search(r'(kh(\d*)|kl(\d*)|dh(\d*)|dl(\d*))$', expr, re.I)
    keep = drop = None
    keep_low = drop_low = False
    if mod_match:
        g = mod_match.group
        if g(1): keep = int(g(2) or 1)
        elif g(3): keep, keep_low = int(g(4) or 1), True
        elif g(5): drop = int(g(6) or 1)
        elif g(7): drop, drop_low = int(g(8) or 1), True
        expr = expr[:mod_match.start()]
    comp_match = re.search(r'([<>]=?|==|!=)(-?\d+(?:\.\d+)?)$', expr)
    comp_op, comp_val = (comp_match.group(1), float(comp_match.group(2))) if comp_match else (None, None)
    if comp_match: expr = expr[:comp_match.start()]
    return expr, keep, drop, keep_low, drop_low, comp_op, comp_val

def evaluate_arithmetic(expr, val):
    try:
        tree = ast.parse(expr.replace('roll', str(val)), mode='eval')
        for node in ast.walk(tree):
            if not isinstance(node, (ast.Expression, ast.BinOp, ast.Add, ast.Sub, ast.Mult, ast.Div, ast.Constant, ast.UnaryOp, ast.USub)):
                raise ValueError
        return eval(compile(tree, '<string>', 'eval'))
    except: return None

def dice_dy(expr):
    m = re.match(r'^(\d+)D(\d+)(.*)$', expr, re.I)
    if not m: return None
    count, sides = int(m.group(1)), int(m.group(2))
    base_expr, keep, drop, keep_low, drop_low, comp_op, comp_val = parse_modifiers(f"{count}D{sides}{m.group(3)}")
    rolls = [roll_dice(sides) for _ in range(count)]
    if keep is not None:
        rolls = sorted(rolls, reverse=not keep_low)[:keep]
    elif drop is not None:
        rolls = sorted(rolls, reverse=drop_low)[drop:]
    total = sum(rolls)
    if any(op in base_expr for op in '+-*/'):
        total = evaluate_arithmetic(base_expr, total) or total
    filtered, success = None, None
    if comp_op:
        filtered = [r for r in rolls if eval(f"{r}{comp_op}{comp_val}")]
        success = len(filtered)
    return DiceResult(expr, rolls, total, success=success, filtered_rolls=filtered)

def dice_by(expr):
    m = re.match(r'^(\d+)B(\d+)([Ss]?)(.*)$', expr, re.I)
    if not m: return None
    count, sides, sort_flag = int(m.group(1)), int(m.group(2)), m.group(3).upper() == 'S'
    rest = m.group(4).strip()
    comp_op = comp_val = None
    if rest:
        if rest.startswith('D'):
            comp_op, comp_val = '<=', float(rest[1:])
        else:
            m2 = re.match(r'([<>]=?|==|!=)(-?\d+(?:\.\d+)?)', rest)
            if m2: comp_op, comp_val = m2.group(1), float(m2.group(2))
            else:
                try: comp_val, comp_op = float(rest), '>='
                except: pass
    rolls = [roll_dice(sides) for _ in range(count)]
    if sort_flag: rolls.sort(reverse=True)
    filtered = success = None
    if comp_op:
        filtered = [r for r in rolls if eval(f"{r}{comp_op}{comp_val}")]
        success = len(filtered)
    return DiceResult(expr, rolls, success=success, filtered_rolls=filtered)

def dice_d66(subtype=''):
    d1, d2 = roll_dice(6), roll_dice(6)
    if subtype == 's': rolls, val = sorted([d1, d2]), d1*10+d2
    elif subtype == 'n': rolls, val = sorted([d1, d2], reverse=True), d1*10+d2
    else: val, rolls = d1*10+d2, [d1, d2]
    return DiceResult(f"D66{subtype}", rolls, total=val)

def dice_uy(expr):
    m = re.match(r'^(\d+)U(\d+)\s+(\d+)(?:\s+(\d+))?$', expr, re.I)
    if not m: return None
    count, sides, trigger, threshold = int(m.group(1)), int(m.group(2)), int(m.group(3)), int(m.group(4)) if m.group(4) else None
    all_rolls = []
    def roll_bonus():
        r = roll_dice(sides)
        all_rolls.append(r)
        if r == trigger: roll_bonus()
    for _ in range(count): roll_bonus()
    total = sum(all_rolls)
    success = sum(1 for r in all_rolls if r > threshold) if threshold else None
    return DiceResult(expr, all_rolls, total=total, success=success)

def parse_dice_expression(expr):
    expr = expr.strip()
    if re.match(r'^D66([sn]?)$', expr, re.I):
        return dice_d66(re.match(r'^D66([sn]?)$', expr, re.I).group(1).lower())
    if re.match(r'^\d+U\d+\s+\d+', expr, re.I): return dice_uy(expr)
    if re.match(r'^\d+B\d+', expr, re.I): return dice_by(expr)
    if re.match(r'^\d+D\d+', expr, re.I): return dice_dy(expr)
    return None

def multi_roll(times, dice_expr):
    results = []
    for _ in range(min(times, 30)):
        res = parse_dice_expression(dice_expr)
        if not res: return None
        results.append(res)
    return results

# ---------- CoC 七版 ----------
def coc_check(skill, bonus=0):
    num = abs(bonus)+1
    rolls = []
    for _ in range(num):
        t, u = random.randint(0,9), random.randint(0,9)
        v = t*10+u or 100
        rolls.append(v)
    if bonus > 0:
        final = min(rolls)
        desc = f"獎勵骰 (+{bonus})：骰出 {rolls} 取最低 {final}"
    elif bonus < 0:
        final = max(rolls)
        desc = f"懲罰骰 ({-bonus})：骰出 {rolls} 取最高 {final}"
    else:
        final, desc = rolls[0], "普通擲骰"
    if final == 1: level = "大成功"
    elif final <= skill//5: level = "極限成功"
    elif final <= skill//2: level = "困難成功"
    elif final <= skill: level = "一般成功"
    else:
        if final == 100 or (skill < 50 and final >= 96): level = "大失敗"
        else: level = "失敗"
    return final, level, desc, rolls

# ---------- PBTA ----------
def pbta_check(expr):
    m = re.match(r'^2d6([+-]\d+)?$', expr, re.I)
    if not m: return None
    mod = int(m.group(1) or 0)
    r1, r2 = random.randint(1,6), random.randint(1,6)
    total = r1+r2+mod
    result = "完全成功" if total>=10 else ("部分成功／代價成功" if total>=7 else "失敗")
    return r1, r2, mod, total, result

def roll_dice_expr(expr):
    m = re.match(r'^(\d+)d(\d+)$', expr, re.I)
    if m: return sum(random.randint(1, int(m.group(2))) for _ in range(int(m.group(1))))
    try: return int(expr)
    except: return 0

# ---------- 輔助函式 ----------
async def send_embed(ctx, title, desc=None, color=0x00aaff, fields=None, footer=None):
    embed = discord.Embed(title=title, description=desc, color=color)
    if fields:
        for name, value, inline in fields:
            embed.add_field(name=name, value=value, inline=inline)
    if footer:
        embed.set_footer(text=footer, icon_url=ctx.author.display_avatar.url if hasattr(ctx.author, 'display_avatar') else None)
    await ctx.channel.send(embed=embed)

async def send_private(user, content, alias_name=None, orig_author=None):
    if alias_name and orig_author:
        content = content.replace(orig_author.display_name, alias_name, 1)
    try:
        dm = await user.create_dm()
        await dm.send(content)
        return True
    except:
        return False

# ---------- 骰表儲存管理 ----------
class TableManager:
    def __init__(self, filename='tables_data.json'):
        self.filename = filename
        self.data = defaultdict(lambda: defaultdict(list))
        self.load()
    def load(self):
        if os.path.exists(self.filename):
            with open(self.filename, 'r', encoding='utf-8') as f:
                raw = json.load(f)
                self.data = defaultdict(lambda: defaultdict(list))
                for uid, tables in raw.items():
                    self.data[int(uid)] = tables
    def save(self):
        with open(self.filename, 'w', encoding='utf-8') as f:
            json.dump({str(k): v for k, v in self.data.items()}, f, ensure_ascii=False, indent=2)
    def add(self, user_id, name, dice_expr, options):
        self.data[user_id].append({'name': name, 'dice': dice_expr, 'options': options})
        self.save()
    def delete(self, user_id, index):
        if 0 <= index < len(self.data[user_id]):
            del self.data[user_id][index]
            self.save()
            return True
        return False
    def delete_by_name(self, user_id, name):
        for i, t in enumerate(self.data[user_id]):
            if t['name'] == name:
                del self.data[user_id][i]
                self.save()
                return True
        return False
    def list(self, user_id):
        return self.data[user_id]
    def get(self, user_id, index):
        if 0 <= index < len(self.data[user_id]):
            return self.data[user_id][index]
        return None
    def get_by_name(self, user_id, name):
        for t in self.data[user_id]:
            if t['name'] == name:
                return t
        return None

# ---------- GM 與自訂指令管理 ----------
class GMManager:
    def __init__(self, f='gm_data.json'):
        self.f, self.data = f, defaultdict(list)
        if os.path.exists(f):
            with open(f) as fp: self.data = defaultdict(list, {int(k): v for k, v in json.load(fp).items()})
    def save(self):
        with open(self.f, 'w') as fp: json.dump({str(k): v for k, v in self.data.items()}, fp, indent=2)
    def add(self, gid, uid, alias=None): self.data[gid].append({'user_id': uid, 'alias': alias or f"GM{len(self.data[gid])+1}"}); self.save()
    def remove(self, gid, idx):
        if 0<=idx<len(self.data[gid]): del self.data[gid][idx]; self.save(); return True
    def clear(self, gid): self.data[gid] = []; self.save()
    def list(self, gid): return self.data[gid]
    def users(self, gid): return [gm['user_id'] for gm in self.data[gid]]
    def alias(self, gid, uid):
        for gm in self.data[gid]:
            if gm['user_id'] == uid: return gm['alias']

class CmdManager:
    def __init__(self, f='cmd_data.json'):
        self.f, self.data = f, defaultdict(dict)
        if os.path.exists(f):
            with open(f) as fp: self.data = defaultdict(dict, {int(k): v for k, v in json.load(fp).items()})
    def save(self):
        with open(self.f, 'w') as fp: json.dump({str(k): v for k, v in self.data.items()}, fp, indent=2)
    def add(self, gid, kw, cmd): self.data[gid][kw] = cmd; self.save()
    def edit(self, gid, kw, cmd):
        if kw in self.data[gid]: self.data[gid][kw] = cmd; self.save(); return True
    def delete(self, gid, kw):
        if kw in self.data[gid]: del self.data[gid][kw]; self.save(); return True
    def clear(self, gid): self.data[gid] = {}; self.save()
    def get(self, gid, kw): return self.data[gid].get(kw)
    def items(self, gid): return list(self.data[gid].items())

# ---------- Discord Bot ----------
intents = discord.Intents.default()
intents.message_content = True
bot = commands.Bot(command_prefix='!', intents=intents)
gm = GMManager()
cmd = CmdManager()
table_mgr = TableManager()

# ---------- 暗骰統一處理 ----------
async def handle_private_roll(message, expr, target):
    if parse_dice_expression(expr):
        await handle_roll(message, expr, target)
        return
    # CoC
    cc = re.match(r'^(cc(?:[12]?|n[12]?)?)(?:\s+(.*))?$', expr, re.I)
    if cc:
        cmd_part, args = cc.group(1).lower(), cc.group(2) or ""
        bonus = 0
        if cmd_part == 'cc1': bonus = 1
        elif cmd_part == 'cc2': bonus = 2
        elif cmd_part == 'ccn1': bonus = -1
        elif cmd_part == 'ccn2': bonus = -2
        parts = args.split(maxsplit=1)
        if not parts:
            await send_embed(message, "❌ 缺少技能值", color=0xff0000)
            return
        try:
            skill = int(parts[0])
        except:
            await send_embed(message, "❌ 技能值需為數字", color=0xff0000)
            return
        skill_name = parts[1] if len(parts)>1 else ""
        final, level, desc, _ = coc_check(skill, bonus)
        output = f"**COC 七版檢定**"
        if bonus>0: output += f" (+{bonus}獎勵骰)"
        elif bonus<0: output += f" ({-bonus}懲罰骰)"
        output += f"\n{skill_name} ({skill}%)" if skill_name else f"\n技能值 {skill}"
        output += f"\n{desc} → 最終擲骰 {final} → **{level}**"
        await _send_private_result(message, output, target)
        return
    # PBTA
    p = re.match(r'^p(?:\s+(2d6[+-]?\d*)?(?:\s+(.*))?)?$', expr, re.I)
    if p:
        dice = p.group(1) or "2d6"
        move = p.group(2) or ""
        res = pbta_check(dice)
        if not res:
            await send_embed(message, "❌ 格式錯誤，請用：p 2d6[+/-修正] [移動名稱]", color=0xff0000)
            return
        r1,r2,mod,total,result = res
        output = f"**PBTA 擲骰**\n"
        if move: output += f"移動：{move}\n"
        output += f"骰子：{r1}+{r2} + {mod} = {total}\n結果：{result}"
        await _send_private_result(message, output, target)
        return
    await send_embed(message, "⚠️ 暗骰僅支援 CoC(cc) 與 PBTA(p)", color=0xffaa00)

async def _send_private_result(message, output, target):
    gms = gm.users(message.guild.id)
    alias = gm.alias(message.guild.id, message.author.id)
    if target == 'self':
        if await send_private(message.author, f"{message.author.display_name} 暗骰：\n{output}", alias, message.author):
            await message.add_reaction('📬')
        else:
            await send_embed(message, "❌ 無法私訊給您自己", desc="請檢查您的隱私設定，允許伺服器成員直接訊息。", color=0xff0000)
    elif target == 'gm':
        recipients = set(gms) | {message.author.id}
        ok = 0
        for uid in recipients:
            if uid == message.author.id:
                user = message.author
            else:
                user = message.guild.get_member(uid)
                if not user:
                    try:
                        user = await message.guild.fetch_member(uid)
                    except:
                        continue
            if user and await send_private(user, f"{message.author.display_name} 暗骰：\n{output}", alias, message.author):
                ok += 1
        if ok:
            await message.add_reaction('📬')
        else:
            await send_embed(message, "❌ 私訊失敗", desc="可能原因：未設定 GM、GM 關閉私訊、或您未開啟私訊。", color=0xff0000)
    elif target == 'gm_only':
        recipients = set(gms)
        if message.author.id not in gms:
            recipients.discard(message.author.id)
        ok = 0
        for uid in recipients:
            user = message.guild.get_member(uid)
            if not user:
                try:
                    user = await message.guild.fetch_member(uid)
                except:
                    continue
            if user and await send_private(user, f"{message.author.display_name} 暗骰：\n{output}", alias, message.author):
                ok += 1
        if ok:
            await message.add_reaction('🔒')
        else:
            await send_embed(message, "❌ 私訊失敗", desc="無法私訊給任何 GM，請確認 GM 已登記且開啟私訊。", color=0xff0000)

async def handle_roll(message, roll_expr, target='channel'):
    res = parse_dice_expression(roll_expr)
    if not res:
        await send_embed(message, "❌ 無效骰子指令", desc=roll_expr, color=0xff0000)
        return
    embed = discord.Embed(title="🎲 擲骰結果", description=res.format(), color=0x00aaff)
    embed.set_footer(text=message.author.display_name, icon_url=message.author.display_avatar.url)
    if target == 'channel':
        await message.channel.send(embed=embed)
    elif target == 'self':
        if await send_private(message.author, f"{message.author.display_name} 擲骰：\n{res.format()}", None, message.author):
            await message.add_reaction('📬')
        else:
            await send_embed(message, "❌ 私訊失敗", desc="無法發送私訊給您，請檢查隱私設定。", color=0xff0000)
    elif target == 'gm':
        gms_ids = gm.users(message.guild.id)
        alias = gm.alias(message.guild.id, message.author.id)
        success = False
        for uid in gms_ids:
            user = message.guild.get_member(uid)
            if not user:
                try:
                    user = await message.guild.fetch_member(uid)
                except:
                    continue
            if user and await send_private(user, f"{message.author.display_name} 擲骰：\n{res.format()}\n(來自 {message.author.display_name})", alias, message.author):
                success = True
        if await send_private(message.author, f"{message.author.display_name} 擲骰：\n{res.format()}", alias, message.author):
            success = True
        if success:
            await message.add_reaction('📬')
        else:
            await send_embed(message, "❌ 私訊失敗", desc="無法私訊給 GM 或您自己。", color=0xff0000)
    elif target == 'gm_only':
        gms_ids = gm.users(message.guild.id)
        recipients = set(gms_ids)
        if message.author.id not in gms_ids:
            recipients.discard(message.author.id)
        alias = gm.alias(message.guild.id, message.author.id)
        success = False
        for uid in recipients:
            user = message.guild.get_member(uid)
            if not user:
                try:
                    user = await message.guild.fetch_member(uid)
                except:
                    continue
            if user and await send_private(user, f"{message.author.display_name} 擲骰：\n{res.format()}\n(僅 GM 可見)", alias, message.author):
                success = True
        if success:
            await message.add_reaction('🔒')
        else:
            await send_embed(message, "❌ 私訊失敗", desc="無法私訊給任何 GM。", color=0xff0000)

# ---------- 骰表查詢與儲存（支援單行逗號分隔） ----------
async def roll_table(message, args):
    if not args:
        await send_embed(message, "📋 骰表指令說明", desc="`.rt save 名稱 骰子 選項1,選項2,...`\n`.rt list`\n`.rt del 序號/名稱`\n`.rt 序號 [骰子]`", color=0x00aaff)
        return

    parts = args.split(maxsplit=1)
    first = parts[0].lower()
    rest = parts[1] if len(parts) > 1 else ""

    if first == 'save':
        # 解析: 名稱, 骰子, 選項列表（可選）
        save_parts = rest.split(maxsplit=2)
        if len(save_parts) < 2:
            await send_embed(message, "❌ 格式錯誤", desc=".rt save 名稱 骰子 選項1,選項2,...", color=0xff0000)
            return
        name = save_parts[0]
        dice_expr = save_parts[1]
        if len(save_parts) >= 3:
            opts_str = save_parts[2]
            opts = [opt.strip() for opt in opts_str.split(',') if opt.strip()]
        else:
            # 多行模式（備用）
            lines = message.content.strip().split('\n')
            if len(lines) > 1:
                opts = [line.strip() for line in lines[1:] if line.strip()]
            else:
                await send_embed(message, "❌ 缺少選項", desc="請在同一行用逗號分隔選項，或換行輸入選項", color=0xff0000)
                return

        if not opts:
            await send_embed(message, "❌ 無選項", color=0xff0000)
            return

        mapping = {}
        auto = 1
        for opt in opts:
            m = re.match(r'^(\d+)[:：\s]+(.*)$', opt)
            if m:
                idx = int(m.group(1))
                text = m.group(2).strip()
                mapping[idx] = text
            else:
                mapping[auto] = opt
                auto += 1

        table_mgr.add(message.author.id, name, dice_expr, mapping)
        await send_embed(message, "✅ 骰表已儲存", desc=f"名稱：{name}\n骰子：{dice_expr}\n選項數：{len(mapping)}", color=0x00aa00)
        return

    if first == 'list':
        tables = table_mgr.list(message.author.id)
        if not tables:
            await send_embed(message, "📋 您還沒有儲存任何骰表", desc="使用 `.rt save 名稱 骰子 選項1,選項2,...` 來儲存", color=0xffaa00)
            return
        desc = ""
        for idx, t in enumerate(tables):
            desc += f"**{idx}**. {t['name']} - `{t['dice']}` ({len(t['options'])}項)\n"
        await send_embed(message, "📋 您的骰表列表", desc=desc, footer=message.author.display_name)
        return

    if first == 'del':
        if not rest:
            await send_embed(message, "❌ 請提供要刪除的序號或名稱", color=0xff0000)
            return
        try:
            idx = int(rest)
            if table_mgr.delete(message.author.id, idx):
                await send_embed(message, "✅ 已刪除骰表", desc=f"序號 {idx}", color=0x00aa00)
            else:
                await send_embed(message, "❌ 序號無效", color=0xff0000)
        except ValueError:
            if table_mgr.delete_by_name(message.author.id, rest):
                await send_embed(message, "✅ 已刪除骰表", desc=f"名稱：{rest}", color=0x00aa00)
            else:
                await send_embed(message, "❌ 找不到該名稱", color=0xff0000)
        return

    # 查表：第一個參數為序號
    try:
        idx = int(first)
    except ValueError:
        await send_embed(message, "❌ 無效的序號", desc="請使用數字序號，或 `.rt save/list/del`", color=0xff0000)
        return

    tables = table_mgr.list(message.author.id)
    if not tables or idx >= len(tables) or idx < 0:
        await send_embed(message, "❌ 序號無效", desc=f"您共有 {len(tables)} 個骰表", color=0xff0000)
        return

    table = tables[idx]
    dice_expr = rest if rest else table['dice']
    dice_res = parse_dice_expression(dice_expr)
    if not dice_res or dice_res.total is None:
        await send_embed(message, "❌ 無效的骰子表達式", desc=dice_expr, color=0xff0000)
        return

    val = dice_res.total
    options = table['options']
    if val in options:
        embed = discord.Embed(title="🎲 骰表結果", color=0x00aaff)
        embed.add_field(name="骰表", value=table['name'], inline=True)
        embed.add_field(name="擲骰", value=f"{dice_expr} = {val}", inline=True)
        embed.add_field(name="命中項目", value=options[val], inline=False)
        embed.set_footer(text=message.author.display_name, icon_url=message.author.display_avatar.url)
        await message.channel.send(embed=embed)
    else:
        await send_embed(message, "❌ 骰值超出範圍", desc=f"骰出 {val}，有效編號 {min(options)}～{max(options)}", color=0xff0000)

# ---------- 點命令處理 ----------
async def handle_dot_command(message, cmd):
    if cmd.startswith('help'):
        await send_embed(message, "📖 D!ce 機器人使用說明", fields=[
            ("🎲 通用骰子", "`xDy`, `kh/kl/dh/dl`, `>=t`\n`xBy` (S排序), `xUy`, `D66`", False),
            ("🔢 多重擲骰", "`.次數 骰子` 如 `.5 3D6`", False),
            ("🎯 CoC 七版", "`.cc 技能值 [名稱]`\n`.cc1/cc2`獎勵 `.ccn1/ccn2`懲罰\n聯合檢定 `.cc 80,60 鬥毆,魅惑`\n多次檢定 `.10 cc 20`", False),
            ("🎲 PBTA", "`.p 2d6[+/-修正] [移動名稱]`", False),
            ("📋 骰表", "`.rt 序號 [骰子]` - 查已儲存骰表\n`.rt save/list/del` - 管理骰表", False),
            ("🧠 SAN檢定", "`.sc 目前SAN 成功損失 失敗損失`", False),
            ("📈 成長檢定", "`.dp 技能值 名稱` (失敗才成長)", False),
            ("📐 計算", "`.calc 表達式` 或直接 `1d3+2`", False),
            ("🔒 暗骰", "`dr 指令`, `ddr 指令`, `dddr 指令`", False),
            ("👑 GM管理", "`.drgm addgm [化名]`, `.drgm show`, `.drgm del 編號/all`", False),
            ("🔧 自訂指令", "`.cmd add 關鍵字 指令`, `.cmd 關鍵字`", False),
            ("🎲 其他", "`.int 最小 最大`, `.help`", False)
        ], footer=message.author.display_name)
        return

    if cmd.startswith(('rt', 'rolltable')):
        await roll_table(message, cmd[2:].strip() if cmd.startswith('rt') else cmd[8:].strip())
        return

    if cmd.startswith('rtx'):
        args = cmd[3:].strip()
        parts = args.split(maxsplit=1)
        if not parts:
            await send_embed(message, "❌ 請提供骰表序號或名稱", color=0xff0000)
            return
        identifier = parts[0]
        dice_override = parts[1] if len(parts) > 1 else None
        tables = table_mgr.list(message.author.id)
        if not tables:
            await send_embed(message, "📋 您尚未儲存任何骰表", desc="使用 `.rt save` 儲存", color=0xffaa00)
            return
        try:
            idx = int(identifier)
            if 0 <= idx < len(tables):
                table = tables[idx]
            else:
                await send_embed(message, "❌ 序號無效", color=0xff0000)
                return
        except ValueError:
            table = table_mgr.get_by_name(message.author.id, identifier)
            if not table:
                await send_embed(message, "❌ 找不到該名稱", color=0xff0000)
                return
        dice_expr = dice_override if dice_override else table['dice']
        dice_res = parse_dice_expression(dice_expr)
        if not dice_res or dice_res.total is None:
            await send_embed(message, "❌ 無效骰子表達式", desc=dice_expr, color=0xff0000)
            return
        val = dice_res.total
        options = table['options']
        if val in options:
            embed = discord.Embed(title="🎲 骰表結果", color=0x00aaff)
            embed.add_field(name="骰表", value=table['name'], inline=True)
            embed.add_field(name="擲骰", value=f"{dice_expr} = {val}", inline=True)
            embed.add_field(name="命中項目", value=options[val], inline=False)
            embed.set_footer(text=message.author.display_name, icon_url=message.author.display_avatar.url)
            await message.channel.send(embed=embed)
        else:
            await send_embed(message, "❌ 骰值超出範圍", desc=f"骰出 {val}，有效編號 {min(options)}～{max(options)}", color=0xff0000)
        return

    mm = re.match(r'^(\d+)\s+(.+)$', cmd)
    if mm:
        times, rest = int(mm.group(1)), mm.group(2).strip()
        cc = re.match(r'^(cc(?:[12]?|n[12]?)?)(?:\s+(.*))?$', rest, re.I)
        if cc:
            cmd_part, args = cc.group(1).lower(), cc.group(2) or ""
            bonus = 0
            if cmd_part == 'cc1': bonus = 1
            elif cmd_part == 'cc2': bonus = 2
            elif cmd_part == 'ccn1': bonus = -1
            elif cmd_part == 'ccn2': bonus = -2
            parts = args.split(maxsplit=1)
            if not parts:
                await send_embed(message, "❌ 缺少技能值", color=0xff0000)
                return
            try:
                svals = [int(x) for x in parts[0].split(',')]
            except:
                await send_embed(message, "❌ 技能值格式錯誤", color=0xff0000)
                return
            snames = [x.strip() for x in (parts[1].split(',') if len(parts)>1 else [])]
            snames += [''] * (len(svals) - len(snames))
            results = []
            for i in range(min(times,30)):
                for sv, sn in zip(svals, snames):
                    final, level, desc, _ = coc_check(sv, bonus)
                    line = f"{sn} ({sv}%)" if sn else f"技能值 {sv}"
                    line += f" → {desc} → 最終擲骰 {final} → **{level}**"
                    results.append(f"第{i+1}次：{line}")
            title = f"多重 CoC 檢定（{min(times,30)}次）"
            if bonus>0: title += f" (+{bonus}獎勵骰)"
            elif bonus<0: title += f" ({-bonus}懲罰骰)"
            await send_embed(message, title, desc="\n".join(results), footer=message.author.display_name)
            return
        else:
            res = multi_roll(times, rest)
            if res:
                desc = "\n".join([f"{i+1}: {r.format()}" for i,r in enumerate(res)])
                await send_embed(message, f"多重擲骰：{rest} ({times}次)", desc=desc, footer=message.author.display_name)
            else:
                await send_embed(message, "❌ 多重擲骰失敗", desc=rest, color=0xff0000)
            return

    if cmd.startswith('int'):
        p = cmd.split()
        if len(p)==3:
            try:
                lo, hi = sorted([int(p[1]), int(p[2])])
                val = random.randint(lo, hi)
                await send_embed(message, "🎲 隨機整數", desc=f".int {lo} {hi}：{val}", footer=message.author.display_name)
            except: await send_embed(message, "❌ 格式錯誤", desc=".int 最小 最大", color=0xff0000)
        else: await send_embed(message, "❌ 格式錯誤", desc=".int 最小 最大", color=0xff0000)
        return

    if cmd.startswith('calc'):
        expr = cmd[4:].strip()
        if not expr:
            await send_embed(message, "❌ 缺少表達式", desc=".calc (1D100+5)/2", color=0xff0000)
            return
        def repl(m):
            d = parse_dice_expression(m.group(0))
            return str(d.total) if d and d.total is not None else (str(sum(d.rolls)) if d and d.rolls else m.group(0))
        rep = re.sub(r'(\d+[DBU]\d+[Ss]?(?:\s+\d+)?|D66[sn]?)', repl, expr, flags=re.I)
        try:
            allowed = (ast.Expression, ast.BinOp, ast.Add, ast.Sub, ast.Mult, ast.Div, ast.FloorDiv, ast.Mod, ast.Pow,
                       ast.UnaryOp, ast.USub, ast.Constant, ast.Compare, ast.Lt, ast.LtE, ast.Gt, ast.GtE, ast.Eq, ast.NotEq)
            tree = ast.parse(rep, mode='eval')
            for node in ast.walk(tree):
                if not isinstance(node, allowed): raise ValueError
            result = eval(compile(tree, '<string>', 'eval'))
            await send_embed(message, "📐 計算結果", desc=f"{expr}\n= {result}", footer=message.author.display_name)
        except Exception as e:
            await send_embed(message, "❌ 表達式錯誤", desc=str(e), color=0xff0000)
        return

    if cmd.startswith(('coc','cc')):
        bonus = 0
        m_ccn = re.match(r'^ccn([12]?)(.*)$', cmd, re.I)
        if m_ccn:
            bonus = -1 if not m_ccn.group(1) else -int(m_ccn.group(1))
            rest = m_ccn.group(2).strip()
        else:
            m_cc = re.match(r'^cc([12]?)(.*)$', cmd, re.I)
            if m_cc:
                bonus = 0 if not m_cc.group(1) else int(m_cc.group(1))
                rest = m_cc.group(2).strip()
            else:
                rest = cmd[3:].strip() if cmd.startswith('coc') else cmd[2:].strip()
        if not rest:
            await send_embed(message, "❌ 缺少技能值", desc=".cc 80 鬥毆", color=0xff0000)
            return
        parts = rest.split(maxsplit=1)
        svals = [int(x) for x in parts[0].split(',')]
        snames = [x.strip() for x in (parts[1].split(',') if len(parts)>1 else [])]
        snames += [''] * (len(svals) - len(snames))
        out = []
        for sv, sn in zip(svals, snames):
            final, level, desc, _ = coc_check(sv, bonus)
            line = f"{sn} ({sv}%)" if sn else f"技能值 {sv}"
            line += f"\n{desc} → 最終擲骰 {final} → **{level}**"
            out.append(line)
        title = "COC 七版檢定"
        if bonus>0: title += f" (+{bonus}獎勵骰)"
        elif bonus<0: title += f" ({-bonus}懲罰骰)"
        await send_embed(message, title, desc="\n\n".join(out), footer=message.author.display_name)
        return

    if cmd.startswith(('pbta','p')):
        rest = cmd[3:].strip() if cmd.startswith('pbta') else cmd[1:].strip()
        if not rest:
            await send_embed(message, "❌ 缺少骰子", desc=".p 2d6+2", color=0xff0000)
            return
        p = rest.split(maxsplit=1)
        dice = p[0]
        move = p[1] if len(p)>1 else ""
        res = pbta_check(dice)
        if not res:
            await send_embed(message, "❌ 格式錯誤", desc=".p 2d6[+/-修正] [移動名稱]", color=0xff0000)
            return
        r1,r2,mod,total,result = res
        embed = discord.Embed(title="🎲 PBTA 擲骰", color=0x00aaff)
        if move: embed.add_field(name="移動", value=move, inline=False)
        embed.add_field(name="骰子結果", value=f"{r1}+{r2} + {mod} = {total}", inline=False)
        embed.add_field(name="判定結果", value=result, inline=False)
        embed.set_footer(text=message.author.display_name, icon_url=message.author.display_avatar.url)
        await message.channel.send(embed=embed)
        return

    if cmd.startswith('sc'):
        args = cmd[2:].strip()
        p = args.split()
        if len(p)<3:
            await send_embed(message, "❌ 格式錯誤", desc=".sc 目前SAN 成功損失 失敗損失", color=0xff0000)
            return
        cur = int(p[0])
        suc_loss, fail_loss = p[1], p[2]
        roll = random.randint(1,100)
        if roll <= cur:
            loss = roll_dice_expr(suc_loss)
            text = f"理智檢定成功！損失 {loss} 點 SAN。"
        else:
            loss = roll_dice_expr(fail_loss)
            text = f"理智檢定失敗！損失 {loss} 點 SAN。"
        embed = discord.Embed(title="🧠 SAN 檢定", color=0x00aa00 if roll<=cur else 0xaa0000)
        embed.add_field(name="目前 SAN", value=cur, inline=True)
        embed.add_field(name="擲骰", value=roll, inline=True)
        embed.add_field(name="結果", value=text, inline=False)
        embed.add_field(name="剩餘 SAN", value=cur-loss, inline=True)
        embed.set_footer(text=message.author.display_name, icon_url=message.author.display_avatar.url)
        await message.channel.send(embed=embed)
        return

    if cmd.startswith('dp') or cmd.startswith('成長檢定') or cmd.startswith('幕間成長'):
        args = cmd[2:].strip() if cmd.startswith('dp') else cmd[4:].strip()
        if not args:
            await send_embed(message, "❌ 缺少參數", desc=".dp 50 騎乘 60 鬥毆", color=0xff0000)
            return
        toks = args.split()
        if len(toks)%2:
            await send_embed(message, "❌ 參數需成對", desc="技能值 名稱", color=0xff0000)
            return
        out = []
        for i in range(0, len(toks), 2):
            try:
                sv, name = int(toks[i]), toks[i+1]
                gr = random.randint(1,100)
                if gr > sv:
                    inc = random.randint(1,10)
                    out.append(f"{name} ({sv}%) → 成長檢定 {gr} 失敗，獲得成長 +{inc}%，新技能值 {sv+inc}")
                else:
                    out.append(f"{name} ({sv}%) → 成長檢定 {gr} 成功（或持平），未成長")
            except: continue
        if out:
            await send_embed(message, "📈 成長檢定（失敗才成長）", desc="\n".join(out), footer=message.author.display_name)
        else:
            await send_embed(message, "❌ 無法解析", color=0xff0000)
        return

    if cmd.startswith('drgm'):
        sub = cmd[4:].strip()
        if sub.startswith('addgm'):
            alias = sub.split(maxsplit=1)[1] if len(sub.split())>1 else None
            gm.add(message.guild.id, message.author.id, alias)
            await send_embed(message, "✅ 登記成功", desc=f"{message.author.display_name} 已登記為 GM" + (f" (化名：{alias})" if alias else ""), color=0x00aa00)
        elif sub == 'show':
            gms = gm.list(message.guild.id)
            if gms:
                desc = "\n".join([f"{i}: {message.guild.get_member(g['user_id']).display_name} (化名：{g['alias']})" for i,g in enumerate(gms)])
                await send_embed(message, "👑 GM 列表", desc=desc)
            else: await send_embed(message, "ℹ️ 無 GM", color=0xffaa00)
        elif sub.startswith('del'):
            parts = sub.split()
            if len(parts)==2:
                if parts[1].lower() == 'all':
                    gm.clear(message.guild.id)
                    await send_embed(message, "✅ 已清除所有 GM", color=0x00aa00)
                else:
                    try:
                        idx = int(parts[1])
                        if gm.remove(message.guild.id, idx):
                            await send_embed(message, "✅ 刪除成功", desc=f"已刪除編號 {idx}", color=0x00aa00)
                        else: await send_embed(message, "❌ 編號無效", color=0xff0000)
                    except: await send_embed(message, "❌ 請輸入數字編號或 all", color=0xff0000)
            else: await send_embed(message, "❌ 格式錯誤", desc=".drgm del 編號/all", color=0xff0000)
        else: await send_embed(message, "❌ 未知子命令", desc="addgm, show, del", color=0xff0000)
        return

    if cmd.startswith('cmd'):
        sub = cmd[3:].strip()
        if sub.startswith('add'):
            p = sub.split(maxsplit=2)
            if len(p)>=3:
                cmd.add(message.guild.id, p[1], p[2])
                await send_embed(message, "✅ 自訂指令已新增", desc=f"`{p[1]}` -> `{p[2]}`", color=0x00aa00)
            else: await send_embed(message, "❌ 格式錯誤", desc=".cmd add 關鍵字 指令", color=0xff0000)
        elif sub.startswith('edit'):
            p = sub.split(maxsplit=2)
            if len(p)>=3 and cmd.edit(message.guild.id, p[1], p[2]):
                await send_embed(message, "✅ 已修改", desc=f"`{p[1]}` -> `{p[2]}`", color=0x00aa00)
            else: await send_embed(message, "❌ 修改失敗", color=0xff0000)
        elif sub == 'show':
            items = cmd.items(message.guild.id)
            if items:
                desc = "\n".join([f"{i}: `{kw}` -> `{c}`" for i,(kw,c) in enumerate(items)])
                await send_embed(message, "🔧 自訂指令列表", desc=desc)
            else: await send_embed(message, "ℹ️ 無自訂指令", color=0xffaa00)
        elif sub.startswith('del'):
            p = sub.split()
            if len(p)==2:
                if p[1].lower() == 'all':
                    cmd.clear(message.guild.id)
                    await send_embed(message, "✅ 已清除所有自訂指令", color=0x00aa00)
                else:
                    try:
                        idx = int(p[1])
                        items = cmd.items(message.guild.id)
                        if 0<=idx<len(items):
                            kw = items[idx][0]
                            cmd.delete(message.guild.id, kw)
                            await send_embed(message, "✅ 刪除成功", desc=f"已刪除編號 {idx} 的 `{kw}`", color=0x00aa00)
                        else: await send_embed(message, "❌ 編號無效", color=0xff0000)
                    except: await send_embed(message, "❌ 請輸入數字編號或 all", color=0xff0000)
            else: await send_embed(message, "❌ 格式錯誤", desc=".cmd del 編號/all", color=0xff0000)
        else:
            if sub:
                c = cmd.get(message.guild.id, sub)
                if not c:
                    try:
                        idx = int(sub)
                        items = cmd.items(message.guild.id)
                        if 0<=idx<len(items): c = items[idx][1]
                    except: pass
                if c:
                    await on_message(message, custom_content=c)
                else: await send_embed(message, "❌ 找不到關鍵字", color=0xff0000)
            else: await send_embed(message, "❌ 缺少子命令", color=0xff0000)
        return

    if cmd.startswith(('ccrt','ccsu','cc7build','cc6build','cc7bg','chase')):
        await send_embed(message, "🚧 開發中", desc=f"指令 {cmd.split()[0]} 敬請期待", color=0xffaa00)
        return

    await send_embed(message, "❓ 未知點命令", desc="輸入 .help", color=0xff0000)

@bot.event
async def on_message(message, custom_content=None):
    if custom_content is not None:
        class Fake:
            def __init__(self, orig, c): self.author=orig.author; self.channel=orig.channel; self.guild=orig.guild; self.content=c; self.add_reaction=orig.add_reaction
        await on_message(Fake(message, custom_content))
        return
    if message.author.bot: return
    content = message.content.strip()
    if not content: return
    low = content.lower()
    if low == 'help':
        await handle_dot_command(message, 'help')
        return
    if low.startswith('dddr '):
        await handle_private_roll(message, content[5:].strip(), 'gm_only')
        return
    if low.startswith('ddr '):
        await handle_private_roll(message, content[4:].strip(), 'gm')
        return
    if low.startswith('dr '):
        await handle_private_roll(message, content[3:].strip(), 'self')
        return
    if re.match(r'^(cc(?:[12]?|n[12]?)?)', content, re.I):
        await handle_dot_command(message, content)
        return
    if re.match(r'^p(?:\s+2d6)', content, re.I):
        await handle_dot_command(message, content)
        return
    if content.startswith('.'):
        await handle_dot_command(message, content[1:].strip())
        return
    dice_res = parse_dice_expression(content)
    if dice_res:
        embed = discord.Embed(title="🎲 擲骰結果", description=dice_res.format(), color=0x00aaff)
        embed.set_footer(text=message.author.display_name, icon_url=message.author.display_avatar.url)
        await message.channel.send(embed=embed)
        return
    m = re.match(r'^([0-9]+[DBU][0-9]+[Ss]?(?:\s+\d+)?|D66[sn]?)', content, re.I)
    if m:
        dice_part = m.group(1)
        text_part = content[m.end():].strip()
        dice_res = parse_dice_expression(dice_part)
        if dice_res:
            dice_res.text = text_part or None
            embed = discord.Embed(title="🎲 擲骰結果", description=dice_res.format(), color=0x00aaff)
            embed.set_footer(text=message.author.display_name, icon_url=message.author.display_avatar.url)
            await message.channel.send(embed=embed)
        else:
            await send_embed(message, "❌ 無法解析骰子", desc=dice_part, color=0xff0000)
        return

if __name__ == "__main__":
    TOKEN = os.getenv('DISCORD_TOKEN')
    if not TOKEN:
        print("錯誤：請設定 DISCORD_TOKEN 環境變數")
        exit(1)
    bot.run(TOKEN)