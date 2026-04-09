import discord
from discord.ext import commands
import re
import random
import ast
import json
import os
from collections import defaultdict

# ---------- 骰子核心函式 ----------
class DiceResult:
    def __init__(self, raw_expr, rolls, total=None, text=None, success=None, details=None, filtered_rolls=None, arithmetic=None):
        self.raw_expr = raw_expr
        self.rolls = rolls
        self.total = total
        self.text = text
        self.success = success
        self.details = details
        self.filtered_rolls = filtered_rolls
        self.arithmetic = arithmetic  # 例如 "+3" 或 "*2+1"

    def format(self):
        rolls_str = ', '.join(map(str, self.rolls))
        # 若有算術附加部分且 total 已計算，使用詳細算式格式
        if self.arithmetic and self.total is not None and self.arithmetic.strip():
            sum_rolls = sum(self.rolls)
            base = f"{self.raw_expr}： {sum_rolls}[{rolls_str}]{self.arithmetic} = {self.total}"
            if self.text:
                base = f"{self.text} {base}"
            return base
        # 一般格式
        if self.total is not None:
            base = f"{self.raw_expr}：{self.text or ''} {self.total} [{rolls_str}]"
        else:
            base = f"{self.raw_expr}：{self.text or ''} {rolls_str}"
        if self.filtered_rolls is not None and len(self.filtered_rolls) > 0:
            filtered_str = ', '.join(map(str, self.filtered_rolls))
            base += f"\n符合條件：{filtered_str}"
        if self.success is not None:
            base += f" 成功數 {self.success}"
        return base

def roll_dice(sides):
    return random.randint(1, sides)

def parse_modifiers(expr):
    mod_pattern = re.compile(r'(?:kh(\d*)|kl(\d*)|dh(\d*)|dl(\d*))$', re.I)
    mod_match = mod_pattern.search(expr)
    keep = None
    drop = None
    keep_low = False
    drop_low = False
    if mod_match:
        if mod_match.group(1):
            keep = int(mod_match.group(1)) if mod_match.group(1) else 1
        elif mod_match.group(2):
            keep = int(mod_match.group(2)) if mod_match.group(2) else 1
            keep_low = True
        elif mod_match.group(3):
            drop = int(mod_match.group(3)) if mod_match.group(3) else 1
        elif mod_match.group(4):
            drop = int(mod_match.group(4)) if mod_match.group(4) else 1
            drop_low = True
        expr = expr[:mod_match.start()]
    comp_pattern = re.compile(r'([<>]=?|==|!=)(-?\d+(?:\.\d+)?)$')
    comp_match = comp_pattern.search(expr)
    comp_op = None
    comp_val = None
    if comp_match:
        comp_op = comp_match.group(1)
        comp_val = float(comp_match.group(2))
        expr = expr[:comp_match.start()]
    return expr, keep, drop, keep_low, drop_low, comp_op, comp_val

def evaluate_arithmetic(expr, roll_value):
    expr = expr.replace('roll', str(roll_value))
    try:
        allowed_nodes = (ast.Expression, ast.BinOp, ast.Add, ast.Sub, ast.Mult, ast.Div, ast.Constant, ast.UnaryOp, ast.USub)
        tree = ast.parse(expr, mode='eval')
        for node in ast.walk(tree):
            if not isinstance(node, allowed_nodes):
                raise ValueError
        return eval(compile(tree, '<string>', 'eval'))
    except:
        return None

def dice_dy(expr):
    m = re.match(r'^(\d+)D(\d+)(.*)$', expr, re.I)
    if not m:
        return None
    count = int(m.group(1))
    sides = int(m.group(2))
    rest = m.group(3)
    full_expr = f"{count}D{sides}{rest}"
    base_expr, keep, drop, keep_low, drop_low, comp_op, comp_val = parse_modifiers(full_expr)
    rolls = [roll_dice(sides) for _ in range(count)]
    if keep is not None:
        sorted_rolls = sorted(rolls, reverse=not keep_low)
        rolls = sorted_rolls[:keep]
    elif drop is not None:
        sorted_rolls = sorted(rolls, reverse=drop_low)
        rolls = sorted_rolls[drop:]
    total = sum(rolls)
    arithmetic_part = ""
    if '+' in base_expr or '-' in base_expr or '*' in base_expr or '/' in base_expr:
        # 提取算術部分 (例如 "+3" 或 "*2+1")
        dice_part = f"{count}D{sides}"
        if base_expr.startswith(dice_part):
            arithmetic_part = base_expr[len(dice_part):]
        calc_total = evaluate_arithmetic(base_expr, total)
        if calc_total is not None:
            total = calc_total
    filtered = None
    success = None
    if comp_op:
        if comp_op == '>':
            filtered = [r for r in rolls if r > comp_val]
            success = len(filtered)
        elif comp_op == '<':
            filtered = [r for r in rolls if r < comp_val]
            success = len(filtered)
        elif comp_op == '>=':
            filtered = [r for r in rolls if r >= comp_val]
            success = len(filtered)
        elif comp_op == '<=':
            filtered = [r for r in rolls if r <= comp_val]
            success = len(filtered)
        elif comp_op == '==':
            filtered = [r for r in rolls if r == comp_val]
            success = len(filtered)
        elif comp_op == '!=':
            filtered = [r for r in rolls if r != comp_val]
            success = len(filtered)
    return DiceResult(expr, rolls, total, success=success, filtered_rolls=filtered, arithmetic=arithmetic_part)

def dice_by(expr):
    m = re.match(r'^(\d+)B(\d+)([Ss]?)(.*)$', expr, re.I)
    if not m:
        return None
    count = int(m.group(1))
    sides = int(m.group(2))
    sort_flag = m.group(3).upper() == 'S'
    rest = m.group(4).strip()
    comp_op = None
    comp_val = None
    if rest:
        if rest.startswith(' '):
            rest = rest.lstrip()
        if rest.startswith('D'):
            comp_op = '<='
            comp_val = float(rest[1:])
        elif rest.startswith(('>', '<', '=', '!')):
            m_comp = re.match(r'([<>]=?|==|!=)(-?\d+(?:\.\d+)?)', rest)
            if m_comp:
                comp_op = m_comp.group(1)
                comp_val = float(m_comp.group(2))
        else:
            try:
                comp_val = float(rest)
                comp_op = '>='
            except:
                pass
    rolls = [roll_dice(sides) for _ in range(count)]
    if sort_flag:
        rolls.sort(reverse=True)
    filtered = None
    success = None
    if comp_op:
        if comp_op == '>':
            filtered = [r for r in rolls if r > comp_val]
            success = len(filtered)
        elif comp_op == '<':
            filtered = [r for r in rolls if r < comp_val]
            success = len(filtered)
        elif comp_op == '>=':
            filtered = [r for r in rolls if r >= comp_val]
            success = len(filtered)
        elif comp_op == '<=':
            filtered = [r for r in rolls if r <= comp_val]
            success = len(filtered)
        elif comp_op == '==':
            filtered = [r for r in rolls if r == comp_val]
            success = len(filtered)
        elif comp_op == '!=':
            filtered = [r for r in rolls if r != comp_val]
            success = len(filtered)
    return DiceResult(expr, rolls, total=None, success=success, details={'sorted': sort_flag}, filtered_rolls=filtered)

def dice_d66(subtype=''):
    d1 = roll_dice(6)
    d2 = roll_dice(6)
    if subtype == 's':
        rolls = sorted([d1, d2])
        value = rolls[0] * 10 + rolls[1]
    elif subtype == 'n':
        rolls = sorted([d1, d2], reverse=True)
        value = rolls[0] * 10 + rolls[1]
    else:
        value = d1 * 10 + d2
        rolls = [d1, d2]
    return DiceResult(f"D66{subtype}", rolls, total=value)

def dice_uy(expr):
    m = re.match(r'^(\d+)U(\d+)\s+(\d+)(?:\s+(\d+))?$', expr, re.I)
    if not m:
        return None
    count = int(m.group(1))
    sides = int(m.group(2))
    trigger = int(m.group(3))
    threshold = int(m.group(4)) if m.group(4) else None
    all_rolls = []
    def roll_with_bonus():
        r = roll_dice(sides)
        all_rolls.append(r)
        if r == trigger:
            roll_with_bonus()
        return r
    for _ in range(count):
        roll_with_bonus()
    total = sum(all_rolls)
    max_possible = count * sides
    success = None
    if threshold is not None:
        success = sum(1 for r in all_rolls if r > threshold)
    return DiceResult(expr, all_rolls, total=total, success=success, details={'max': max_possible})

def parse_dice_expression(expr):
    expr = expr.strip()
    m_d66 = re.match(r'^D66([sn]?)$', expr, re.I)
    if m_d66:
        return dice_d66(m_d66.group(1).lower())
    if re.match(r'^\d+U\d+\s+\d+', expr, re.I):
        return dice_uy(expr)
    if re.match(r'^\d+B\d+', expr, re.I):
        return dice_by(expr)
    if re.match(r'^\d+D\d+', expr, re.I):
        return dice_dy(expr)
    return None

def multi_roll(times, dice_expr):
    times = min(times, 30)
    results = []
    for i in range(times):
        res = parse_dice_expression(dice_expr)
        if res:
            results.append(res)
        else:
            return None
    return results

# ---------- CoC 七版 ----------
def coc_check(skill_value, bonus_dice=0):
    num_rolls = abs(bonus_dice) + 1
    rolls = []
    for _ in range(num_rolls):
        tens = random.randint(0, 9)
        units = random.randint(0, 9)
        val = tens * 10 + units
        if val == 0:
            val = 100
        rolls.append(val)
    if bonus_dice > 0:
        final_roll = min(rolls)
        bonus_desc = f"獎勵骰 (+{bonus_dice})：骰出 {rolls} 取最低 {final_roll}"
    elif bonus_dice < 0:
        final_roll = max(rolls)
        bonus_desc = f"懲罰骰 ({-bonus_dice})：骰出 {rolls} 取最高 {final_roll}"
    else:
        final_roll = rolls[0]
        bonus_desc = "普通擲骰"
    if final_roll == 1:
        level = "大成功"
    elif final_roll <= skill_value // 5:
        level = "極限成功"
    elif final_roll <= skill_value // 2:
        level = "困難成功"
    elif final_roll <= skill_value:
        level = "一般成功"
    else:
        if final_roll == 100:
            level = "大失敗"
        elif skill_value < 50 and final_roll >= 96:
            level = "大失敗"
        else:
            level = "失敗"
    return final_roll, level, bonus_desc, rolls

# ---------- PBTA 功能 ----------
def pbta_check(expr):
    m = re.match(r'^2d6([+-]\d+)?$', expr, re.I)
    if not m:
        return None
    mod = int(m.group(1)) if m.group(1) else 0
    r1 = random.randint(1, 6)
    r2 = random.randint(1, 6)
    total = r1 + r2 + mod
    if total >= 10:
        result = "完全成功"
    elif total >= 7:
        result = "部分成功／代價成功"
    else:
        result = "失敗"
    return r1, r2, mod, total, result

def roll_dice_expr(expr):
    m = re.match(r'^(\d+)d(\d+)$', expr, re.I)
    if m:
        times = int(m.group(1))
        sides = int(m.group(2))
        return sum(random.randint(1, sides) for _ in range(times))
    else:
        try:
            return int(expr)
        except:
            return 0

async def san_check(message, args):
    parts = args.split()
    if len(parts) < 3:
        embed = discord.Embed(title="❌ 格式錯誤", description="`.sc 目前SAN 成功損失 失敗損失`\n例如：`.sc 50 0 1d6` 或 `.sc 70 1 1d4+1`", color=0xff0000)
        await message.channel.send(embed=embed)
        return
    current_san = int(parts[0])
    success_loss = parts[1]
    fail_loss = parts[2]
    roll = random.randint(1, 100)
    if roll <= current_san:
        loss = roll_dice_expr(success_loss)
        result_text = f"理智檢定成功！損失 {loss} 點 SAN。"
    else:
        loss = roll_dice_expr(fail_loss)
        result_text = f"理智檢定失敗！損失 {loss} 點 SAN。"
    new_san = current_san - loss
    embed = discord.Embed(title="🧠 SAN 檢定", color=0x00aa00 if roll <= current_san else 0xaa0000)
    embed.add_field(name="目前 SAN", value=str(current_san), inline=True)
    embed.add_field(name="擲骰結果", value=str(roll), inline=True)
    embed.add_field(name="結果", value=result_text, inline=False)
    embed.add_field(name="剩餘 SAN", value=str(new_san), inline=True)
    embed.set_footer(text=message.author.display_name, icon_url=message.author.display_avatar.url)
    await message.channel.send(embed=embed)

async def development_check(message, args):
    if not args:
        embed = discord.Embed(title="❌ 格式錯誤", description="請提供技能值與名稱，例如：`.dp 50 騎乘 60 鬥毆`", color=0xff0000)
        await message.channel.send(embed=embed)
        return
    tokens = args.split()
    if len(tokens) % 2 != 0:
        embed = discord.Embed(title="❌ 參數錯誤", description="參數必須成對：技能值 名稱", color=0xff0000)
        await message.channel.send(embed=embed)
        return
    results = []
    for i in range(0, len(tokens), 2):
        try:
            skill_val = int(tokens[i])
            skill_name = tokens[i+1]
        except:
            continue
        growth_roll = random.randint(1, 100)
        if growth_roll > skill_val:
            increase = random.randint(1, 10)
            results.append(f"{skill_name} ({skill_val}%) → 成長檢定 {growth_roll} 失敗，獲得成長 +{increase}%，新技能值 {skill_val+increase}")
        else:
            results.append(f"{skill_name} ({skill_val}%) → 成長檢定 {growth_roll} 成功（或持平），未成長")
    if results:
        embed = discord.Embed(title="📈 成長檢定（失敗才成長）", color=0x00aaff)
        embed.description = "\n".join(results)
        embed.set_footer(text=message.author.display_name, icon_url=message.author.display_avatar.url)
        await message.channel.send(embed=embed)
    else:
        embed = discord.Embed(title="❌ 無法解析", description="請使用：`.dp 技能值 技能名稱`", color=0xff0000)
        await message.channel.send(embed=embed)

# ---------- GM 管理 ----------
class GMManager:
    def __init__(self, filename='gm_data.json'):
        self.filename = filename
        self.data = defaultdict(list)
        self.load()
    def load(self):
        if os.path.exists(self.filename):
            with open(self.filename, 'r', encoding='utf-8') as f:
                raw = json.load(f)
                self.data = defaultdict(list, {int(k): v for k, v in raw.items()})
    def save(self):
        with open(self.filename, 'w', encoding='utf-8') as f:
            json.dump({str(k): v for k, v in self.data.items()}, f, ensure_ascii=False, indent=2)
    def add_gm(self, guild_id, user_id, alias=None):
        if not alias:
            alias = f"GM{len(self.data[guild_id])+1}"
        self.data[guild_id].append({'user_id': user_id, 'alias': alias})
        self.save()
    def remove_gm(self, guild_id, index):
        if 0 <= index < len(self.data[guild_id]):
            del self.data[guild_id][index]
            self.save()
            return True
        return False
    def clear_gms(self, guild_id):
        self.data[guild_id] = []
        self.save()
    def get_gms(self, guild_id):
        return self.data[guild_id]
    def get_gm_users(self, guild_id):
        return [gm['user_id'] for gm in self.data[guild_id]]

class CmdManager:
    def __init__(self, filename='cmd_data.json'):
        self.filename = filename
        self.data = defaultdict(dict)
        self.load()
    def load(self):
        if os.path.exists(self.filename):
            with open(self.filename, 'r', encoding='utf-8') as f:
                raw = json.load(f)
                self.data = defaultdict(dict, {int(k): v for k, v in raw.items()})
    def save(self):
        with open(self.filename, 'w', encoding='utf-8') as f:
            json.dump({str(k): v for k, v in self.data.items()}, f, ensure_ascii=False, indent=2)
    def add_cmd(self, guild_id, keyword, command):
        self.data[guild_id][keyword] = command
        self.save()
    def edit_cmd(self, guild_id, keyword, command):
        if keyword in self.data[guild_id]:
            self.data[guild_id][keyword] = command
            self.save()
            return True
        return False
    def del_cmd(self, guild_id, keyword):
        if keyword in self.data[guild_id]:
            del self.data[guild_id][keyword]
            self.save()
            return True
        return False
    def clear_cmds(self, guild_id):
        self.data[guild_id] = {}
        self.save()
    def get_cmd(self, guild_id, keyword):
        return self.data[guild_id].get(keyword)
    def list_cmds(self, guild_id):
        return list(self.data[guild_id].items())

# ---------- Discord Bot ----------
intents = discord.Intents.default()
intents.message_content = True
bot = commands.Bot(command_prefix='!', intents=intents)

gm_manager = GMManager()
cmd_manager = CmdManager()

def get_alias(guild_id, user_id):
    for gm in gm_manager.get_gms(guild_id):
        if gm['user_id'] == user_id:
            return gm['alias']
    return None

async def send_private(ctx_or_msg, user, content, alias_name=None):
    if alias_name:
        content = content.replace(f"{ctx_or_msg.author.display_name}", alias_name, 1)
    try:
        dm = await user.create_dm()
        await dm.send(content)
        return True
    except discord.Forbidden:
        await ctx_or_msg.channel.send(f"⚠️ 無法私訊給 {user.display_name}，請對方在 Discord 設定中開啟「允許伺服器成員直接訊息」。")
        return False
    except Exception as e:
        await ctx_or_msg.channel.send(f"⚠️ 私訊失敗：{e}")
        return False

async def handle_roll(message, roll_expr, target_type='channel'):
    res = parse_dice_expression(roll_expr)
    if not res:
        embed = discord.Embed(title="❌ 無效的骰子指令", description=roll_expr, color=0xff0000)
        await message.channel.send(embed=embed)
        return
    embed = discord.Embed(title="🎲 擲骰結果", description=res.format(), color=0x00aaff)
    embed.set_footer(text=message.author.display_name, icon_url=message.author.display_avatar.url)
    if target_type == 'channel':
        await message.channel.send(embed=embed)
    elif target_type == 'self':
        await send_private(message, message.author, f"{message.author.display_name} 擲骰：\n{res.format()}")
        await message.add_reaction('📬')
    elif target_type == 'gm':
        gms = gm_manager.get_gm_users(message.guild.id)
        if gms:
            alias = get_alias(message.guild.id, message.author.id)
            for gm_id in gms:
                gm_user = message.guild.get_member(gm_id)
                if gm_user:
                    await send_private(message, gm_user, f"{message.author.display_name} 擲骰：\n{res.format()}\n(來自 {message.author.display_name})", alias_name=alias)
            await send_private(message, message.author, f"{message.author.display_name} 擲骰：\n{res.format()}", alias_name=alias)
            await message.add_reaction('📬')
        else:
            embed = discord.Embed(title="⚠️ 未設定 GM", description="此伺服器尚未設定 GM，請使用 `.drgm addgm` 登記。", color=0xffaa00)
            await message.channel.send(embed=embed)
    elif target_type == 'gm_only':
        gms = gm_manager.get_gm_users(message.guild.id)
        recipients_ids = set(gms)
        if message.author.id not in gms:
            recipients_ids.discard(message.author.id)
        success_count = 0
        alias = get_alias(message.guild.id, message.author.id)
        for uid in recipients_ids:
            if uid == message.author.id:
                user = message.author
            else:
                try:
                    user = await message.guild.fetch_member(uid)
                except:
                    user = None
            if user:
                if await send_private(message, user, f"{message.author.display_name} 擲骰：\n{res.format()}\n(僅 GM 可見)", alias_name=alias):
                    success_count += 1
        if success_count > 0:
            await message.add_reaction('🔒')
        else:
            embed = discord.Embed(title="❌ 私訊失敗", description="無法私訊給任何 GM，請檢查隱私設定。", color=0xff0000)
            await message.channel.send(embed=embed)
    return

# ---------- 算式計算核心（共用） ----------
def compute_expression(expr, author=None):
    """計算數學表達式（支援骰子），成功返回 embed，失敗返回 None"""
    def replace_dice(match):
        dice_expr = match.group(0)
        res = parse_dice_expression(dice_expr)
        if res and res.total is not None:
            return str(res.total)
        elif res and res.rolls:
            return str(sum(res.rolls))
        else:
            return dice_expr

    dice_pattern = re.compile(r'(\d+[DBU]\d+[Ss]?(?:\s+\d+)?|D66[sn]?)', re.I)
    replaced_expr = dice_pattern.sub(replace_dice, expr)
    try:
        allowed_nodes = (ast.Expression, ast.BinOp, ast.Add, ast.Sub, ast.Mult, ast.Div, ast.FloorDiv, ast.Mod, ast.Pow,
                         ast.UnaryOp, ast.USub, ast.Constant, ast.Compare, ast.Lt, ast.LtE, ast.Gt, ast.GtE, ast.Eq, ast.NotEq)
        tree = ast.parse(replaced_expr, mode='eval')
        for node in ast.walk(tree):
            if not isinstance(node, allowed_nodes):
                raise ValueError("不允許的運算")
        result = eval(compile(tree, '<string>', 'eval'))
        embed = discord.Embed(title="📐 計算結果", description=f"{expr}\n= {result}", color=0x00aaff)
        if author:
            embed.set_footer(text=author.display_name, icon_url=author.display_avatar.url)
        return embed
    except Exception as e:
        return None

# ---------- 點命令處理 ----------
async def handle_dot_command(message, cmd):
    """處理點命令，回傳 True 表示已處理"""
    if cmd.startswith('help'):
        embed = discord.Embed(title="📖 D!ce 機器人使用說明", color=0x00aaff)
        embed.add_field(name="🎲 通用骰子指令", value="`xDy` - 擲 x 粒 y 面骰，例如 `2D6`\n`xDy kh/kl/dh/dl` - 保留/放棄最高/最低骰，例如 `4D6kh1`\n`xDy >= t` - 篩選符合條件的骰子，例如 `3D6>=4`\n`xBy` - 不加總骰子，可加 `S` 排序，`>=t` 篩選\n`xUy z` - 獎勵骰系統\n`D66`, `D66s`, `D66n` - 六面骰組合", inline=False)
        embed.add_field(name="🔢 多重擲骰", value="`.次數 骰子指令` - 例如 `.5 3D6`（最多30次）", inline=False)
        embed.add_field(name="🎯 CoC 七版檢定", value="`.cc 技能值 [技能名稱]` - 普通檢定\n`.cc1/cc2` 獎勵骰，`.ccn1/ccn2` 懲罰骰\n支援聯合檢定：`.cc 80,60 鬥毆,魅惑`\n多次檢定：`.10 cc 20`", inline=False)
        embed.add_field(name="🎲 PBTA 檢定", value="`.p 2d6[+/-修正] [移動名稱]` - 例如 `.p 2d6+2`", inline=False)
        embed.add_field(name="🧠 理智檢定", value="`.sc 目前SAN 成功損失 失敗損失` - 例如 `.sc 50 0 1d6`", inline=False)
        embed.add_field(name="📈 成長檢定", value="`.dp 技能值 技能名稱` - 失敗才成長1d10", inline=False)
        embed.add_field(name="📐 計算功能", value="`.calc 表達式` - 支援骰子\n直接輸入算式：`1d3+2` → `[3]+2=5`", inline=False)
        embed.add_field(name="🔒 暗骰（私訊）", value="`dr 指令` - 結果私訊給自己\n`ddr 指令` - 私訊給 GM 與自己\n`dddr 指令` - 僅私訊給 GM（執行者若非 GM 不收）", inline=False)
        embed.add_field(name="👑 GM 管理", value="`.drgm addgm [化名]` - 登記為 GM\n`.drgm show` - 顯示 GM 列表\n`.drgm del 編號/all` - 刪除 GM", inline=False)
        embed.add_field(name="🔧 自訂指令", value="`.cmd add 關鍵字 指令` - 例如 `.cmd add 戰鬥 cc 80 鬥毆`\n`.cmd 關鍵字` - 執行自訂指令", inline=False)
        embed.add_field(name="🎲 其他", value="`.int 最小 最大` - 隨機整數\n`.help` - 顯示此說明", inline=False)
        embed.set_footer(text=message.author.display_name, icon_url=message.author.display_avatar.url)
        await message.channel.send(embed=embed)
        return True

    # 多重擲骰 .次數 指令
    multi_match = re.match(r'^(\d+)\s+(.+)$', cmd)
    if multi_match:
        times = int(multi_match.group(1))
        rest = multi_match.group(2).strip()
        cc_match = re.match(r'^(cc(?:[12]?|n[12]?)?)(?:\s+(.*))?$', rest, re.I)
        if cc_match:
            cmd_part = cc_match.group(1).lower()
            args = cc_match.group(2) or ""
            bonus_dice = 0
            if cmd_part == 'cc1':
                bonus_dice = 1
            elif cmd_part == 'cc2':
                bonus_dice = 2
            elif cmd_part == 'ccn1':
                bonus_dice = -1
            elif cmd_part == 'ccn2':
                bonus_dice = -2
            parts = args.split(maxsplit=1)
            if not parts:
                embed = discord.Embed(title="❌ 缺少技能值", description="請提供技能值", color=0xff0000)
                await message.channel.send(embed=embed)
                return True
            try:
                skill_values_part = parts[0]
                skill_names_part = parts[1] if len(parts) > 1 else ""
                skill_values = [int(x.strip()) for x in skill_values_part.split(',')]
                skill_names = [x.strip() for x in skill_names_part.split(',')] if skill_names_part else []
                while len(skill_names) < len(skill_values):
                    skill_names.append("")
            except:
                embed = discord.Embed(title="❌ 技能值格式錯誤", description="請使用數字，多個技能用逗號分隔", color=0xff0000)
                await message.channel.send(embed=embed)
                return True
            results = []
            for i in range(min(times, 30)):
                for sv, sn in zip(skill_values, skill_names):
                    final_roll, level, bonus_desc, all_rolls = coc_check(sv, bonus_dice)
                    line = f"{sn} ({sv}%)" if sn else f"技能值 {sv}"
                    line += f" → {bonus_desc} → 最終擲骰 {final_roll} → **{level}**"
                    results.append(f"第{i+1}次：{line}")
            if results:
                embed = discord.Embed(title=f"多重 CoC 檢定（{min(times,30)}次）", color=0x00aaff)
                if bonus_dice > 0:
                    embed.title += f" (+{bonus_dice}獎勵骰)"
                elif bonus_dice < 0:
                    embed.title += f" ({-bonus_dice}懲罰骰)"
                embed.description = "\n".join(results)
                embed.set_footer(text=message.author.display_name, icon_url=message.author.display_avatar.url)
                await message.channel.send(embed=embed)
            else:
                embed = discord.Embed(title="❌ 無法執行檢定", description="請檢查參數", color=0xff0000)
                await message.channel.send(embed=embed)
            return True
        else:
            results = multi_roll(times, rest)
            if results:
                embed = discord.Embed(title=f"多重擲骰：{rest} ({times}次)", color=0x00aaff)
                desc = ""
                for i, r in enumerate(results, 1):
                    desc += f"{i}: {r.format()}\n"
                embed.description = desc
                embed.set_footer(text=message.author.display_name, icon_url=message.author.display_avatar.url)
                await message.channel.send(embed=embed)
            else:
                embed = discord.Embed(title="❌ 多重擲骰失敗", description=rest, color=0xff0000)
                await message.channel.send(embed=embed)
            return True

    if cmd.startswith('int'):
        parts = cmd.split()
        if len(parts) == 3:
            try:
                low = int(parts[1])
                high = int(parts[2])
                if low > high:
                    low, high = high, low
                val = random.randint(low, high)
                embed = discord.Embed(title="🎲 隨機整數", description=f".int {low} {high}：{val}", color=0x00aaff)
                embed.set_footer(text=message.author.display_name, icon_url=message.author.display_avatar.url)
                await message.channel.send(embed=embed)
            except:
                embed = discord.Embed(title="❌ 格式錯誤", description="格式：`.int 最小 最大`", color=0xff0000)
                await message.channel.send(embed=embed)
        else:
            embed = discord.Embed(title="❌ 格式錯誤", description="格式：`.int 最小 最大`", color=0xff0000)
            await message.channel.send(embed=embed)
        return True

    if cmd.startswith('calc'):
        expr = cmd[4:].strip()
        if not expr:
            embed = discord.Embed(title="❌ 缺少表達式", description="請提供表達式，例如：`.calc 5+3*2` 或 `.calc (1D100+5)/2`", color=0xff0000)
            await message.channel.send(embed=embed)
            return True
        embed = compute_expression(expr, message.author)
        if embed:
            await message.channel.send(embed=embed)
        else:
            embed = discord.Embed(title="❌ 表達式錯誤", description="請檢查算式是否正確，例如 `5+3*2` 或 `(1d6+2)*2`", color=0xff0000)
            await message.channel.send(embed=embed)
        return True

    # CoC 七版
    if cmd.startswith(('coc', 'cc')):
        bonus_dice = 0
        rest = ""
        m_ccn = re.match(r'^ccn([12]?)(.*)$', cmd, re.I)
        if m_ccn:
            suffix = m_ccn.group(1)
            rest = m_ccn.group(2).strip()
            if suffix == '1':
                bonus_dice = -1
            elif suffix == '2':
                bonus_dice = -2
            else:
                bonus_dice = -1
        else:
            m_cc = re.match(r'^cc([12]?)(.*)$', cmd, re.I)
            if m_cc:
                suffix = m_cc.group(1)
                rest = m_cc.group(2).strip()
                if suffix == '1':
                    bonus_dice = 1
                elif suffix == '2':
                    bonus_dice = 2
                else:
                    bonus_dice = 0
            else:
                if cmd.startswith('coc'):
                    rest = cmd[3:].strip()
                else:
                    rest = cmd[2:].strip()
        if not rest:
            embed = discord.Embed(title="❌ 缺少技能值", description="請提供技能值，例如：`.cc 80 鬥毆` 或 `.cc1 80`", color=0xff0000)
            await message.channel.send(embed=embed)
            return True
        parts = rest.split(maxsplit=1)
        skill_values_part = parts[0]
        skill_names_part = parts[1] if len(parts) > 1 else ""
        skill_values = [int(x.strip()) for x in skill_values_part.split(',')]
        skill_names = [x.strip() for x in skill_names_part.split(',')] if skill_names_part else []
        while len(skill_names) < len(skill_values):
            skill_names.append("")
        output_lines = []
        for sv, sn in zip(skill_values, skill_names):
            final_roll, level, bonus_desc, all_rolls = coc_check(sv, bonus_dice)
            line = f"{sn} ({sv}%)" if sn else f"技能值 {sv}"
            line += f"\n{bonus_desc} → 最終擲骰 {final_roll} → **{level}**"
            output_lines.append(line)
        embed = discord.Embed(title="COC 七版檢定", color=0x00aaff)
        if bonus_dice > 0:
            embed.title += f" (+{bonus_dice}獎勵骰)"
        elif bonus_dice < 0:
            embed.title += f" ({-bonus_dice}懲罰骰)"
        embed.description = "\n\n".join(output_lines)
        embed.set_footer(text=message.author.display_name, icon_url=message.author.display_avatar.url)
        await message.channel.send(embed=embed)
        return True

    # PBTA 檢定 (支援 .p 和 .pbta)
    if cmd.startswith(('pbta', 'p')):
        rest = cmd[3:].strip() if cmd.startswith('pbta') else cmd[1:].strip()
        if not rest:
            embed = discord.Embed(title="❌ 缺少骰子表達式", description="請提供骰子表達式，例如：`.p 2d6+2` 或 `.p 2d6-1 迷蹤步`", color=0xff0000)
            await message.channel.send(embed=embed)
            return True
        parts = rest.split(maxsplit=1)
        dice_expr = parts[0]
        move_name = parts[1] if len(parts) > 1 else ""
        res = pbta_check(dice_expr)
        if not res:
            embed = discord.Embed(title="❌ 格式錯誤", description="請使用：`.p 2d6[+/-修正] [移動名稱]`", color=0xff0000)
            await message.channel.send(embed=embed)
            return True
        r1, r2, mod, total, result = res
        embed = discord.Embed(title="🎲 PBTA 擲骰", color=0x00aaff)
        if move_name:
            embed.add_field(name="移動", value=move_name, inline=False)
        embed.add_field(name="骰子結果", value=f"{r1}+{r2} + {mod} = {total}", inline=False)
        embed.add_field(name="判定結果", value=result, inline=False)
        embed.set_footer(text=message.author.display_name, icon_url=message.author.display_avatar.url)
        await message.channel.send(embed=embed)
        return True

    if cmd.startswith('sc'):
        await san_check(message, cmd[2:].strip())
        return True

    if cmd.startswith('dp') or cmd.startswith('成長檢定') or cmd.startswith('幕間成長'):
        args = cmd[2:].strip() if cmd.startswith('dp') else cmd[4:].strip()
        await development_check(message, args)
        return True

    if cmd.startswith('drgm'):
        sub = cmd[4:].strip()
        if sub.startswith('addgm'):
            parts = sub.split(maxsplit=1)
            alias = parts[1] if len(parts) > 1 else None
            gm_manager.add_gm(message.guild.id, message.author.id, alias)
            embed = discord.Embed(title="✅ 登記成功", description=f"已將 {message.author.display_name} 登記為 GM" + (f" (化名：{alias})" if alias else ""), color=0x00aa00)
            await message.channel.send(embed=embed)
        elif sub == 'show':
            gms = gm_manager.get_gms(message.guild.id)
            if gms:
                embed = discord.Embed(title="👑 GM 列表", color=0x00aaff)
                desc = ""
                for idx, gm in enumerate(gms):
                    user = message.guild.get_member(gm['user_id'])
                    name = user.display_name if user else f"未知使用者({gm['user_id']})"
                    desc += f"{idx}: {name} (化名：{gm['alias']})\n"
                embed.description = desc
                await message.channel.send(embed=embed)
            else:
                embed = discord.Embed(title="ℹ️ 目前沒有登記 GM", color=0xffaa00)
                await message.channel.send(embed=embed)
        elif sub.startswith('del'):
            parts = sub.split()
            if len(parts) == 2:
                if parts[1].lower() == 'all':
                    gm_manager.clear_gms(message.guild.id)
                    embed = discord.Embed(title="✅ 已清除所有 GM", color=0x00aa00)
                    await message.channel.send(embed=embed)
                else:
                    try:
                        idx = int(parts[1])
                        if gm_manager.remove_gm(message.guild.id, idx):
                            embed = discord.Embed(title="✅ 刪除成功", description=f"已刪除編號 {idx} 的 GM", color=0x00aa00)
                            await message.channel.send(embed=embed)
                        else:
                            embed = discord.Embed(title="❌ 編號無效", color=0xff0000)
                            await message.channel.send(embed=embed)
                    except:
                        embed = discord.Embed(title="❌ 請輸入數字編號或 all", color=0xff0000)
                        await message.channel.send(embed=embed)
            else:
                embed = discord.Embed(title="❌ 格式錯誤", description="格式：`.drgm del 編號` 或 `.drgm del all`", color=0xff0000)
                await message.channel.send(embed=embed)
        else:
            embed = discord.Embed(title="❌ 未知子命令", description="可用子命令：addgm [化名], show, del 編號/all", color=0xff0000)
            await message.channel.send(embed=embed)
        return True

    if cmd.startswith('cmd'):
        sub = cmd[3:].strip()
        if sub.startswith('add'):
            parts = sub.split(maxsplit=2)
            if len(parts) >= 3:
                keyword = parts[1]
                command = parts[2]
                cmd_manager.add_cmd(message.guild.id, keyword, command)
                embed = discord.Embed(title="✅ 自訂指令已新增", description=f"`{keyword}` -> `{command}`", color=0x00aa00)
                await message.channel.send(embed=embed)
            else:
                embed = discord.Embed(title="❌ 格式錯誤", description="格式：`.cmd add 關鍵字 指令`", color=0xff0000)
                await message.channel.send(embed=embed)
        elif sub.startswith('edit'):
            parts = sub.split(maxsplit=2)
            if len(parts) >= 3:
                keyword = parts[1]
                command = parts[2]
                if cmd_manager.edit_cmd(message.guild.id, keyword, command):
                    embed = discord.Embed(title="✅ 自訂指令已修改", description=f"`{keyword}` -> `{command}`", color=0x00aa00)
                    await message.channel.send(embed=embed)
                else:
                    embed = discord.Embed(title="❌ 關鍵字不存在", color=0xff0000)
                    await message.channel.send(embed=embed)
            else:
                embed = discord.Embed(title="❌ 格式錯誤", description="格式：`.cmd edit 關鍵字 新指令`", color=0xff0000)
                await message.channel.send(embed=embed)
        elif sub == 'show':
            cmds = cmd_manager.list_cmds(message.guild.id)
            if cmds:
                embed = discord.Embed(title="🔧 自訂指令列表", color=0x00aaff)
                desc = ""
                for idx, (kw, cmd_str) in enumerate(cmds):
                    desc += f"{idx}: `{kw}` -> `{cmd_str}`\n"
                embed.description = desc
                await message.channel.send(embed=embed)
            else:
                embed = discord.Embed(title="ℹ️ 目前沒有自訂指令", color=0xffaa00)
                await message.channel.send(embed=embed)
        elif sub.startswith('del'):
            parts = sub.split()
            if len(parts) == 2:
                if parts[1].lower() == 'all':
                    cmd_manager.clear_cmds(message.guild.id)
                    embed = discord.Embed(title="✅ 已清除所有自訂指令", color=0x00aa00)
                    await message.channel.send(embed=embed)
                else:
                    try:
                        idx = int(parts[1])
                        cmds = cmd_manager.list_cmds(message.guild.id)
                        if 0 <= idx < len(cmds):
                            kw = cmds[idx][0]
                            cmd_manager.del_cmd(message.guild.id, kw)
                            embed = discord.Embed(title="✅ 刪除成功", description=f"已刪除編號 {idx} 的關鍵字 `{kw}`", color=0x00aa00)
                            await message.channel.send(embed=embed)
                        else:
                            embed = discord.Embed(title="❌ 編號無效", color=0xff0000)
                            await message.channel.send(embed=embed)
                    except:
                        embed = discord.Embed(title="❌ 請輸入數字編號或 all", color=0xff0000)
                        await message.channel.send(embed=embed)
            else:
                embed = discord.Embed(title="❌ 格式錯誤", description="格式：`.cmd del 編號` 或 `.cmd del all`", color=0xff0000)
                await message.channel.send(embed=embed)
        else:
            if sub:
                cmd_str = cmd_manager.get_cmd(message.guild.id, sub)
                if not cmd_str:
                    try:
                        idx = int(sub)
                        cmds = cmd_manager.list_cmds(message.guild.id)
                        if 0 <= idx < len(cmds):
                            cmd_str = cmds[idx][1]
                    except:
                        pass
                if cmd_str:
                    await on_message(message, custom_content=cmd_str)
                else:
                    embed = discord.Embed(title="❌ 找不到該關鍵字或編號", color=0xff0000)
                    await message.channel.send(embed=embed)
            else:
                embed = discord.Embed(title="❌ 缺少子命令", description="請提供 add, edit, show, del, 或關鍵字", color=0xff0000)
                await message.channel.send(embed=embed)
        return True

    if cmd.startswith(('ccrt', 'ccsu', 'cc7build', 'cc6build', 'cc7bg', 'chase')):
        embed = discord.Embed(title="🚧 開發中", description=f"指令 `{cmd.split()[0]}` 正在開發中，請期待後續版本。", color=0xffaa00)
        await message.channel.send(embed=embed)
        return True

    embed = discord.Embed(title="❓ 未知的點命令", description="輸入 `.help` 查看所有功能。", color=0xff0000)
    await message.channel.send(embed=embed)
    return True

@bot.event
async def on_message(message, custom_content=None):
    if custom_content is not None:
        class FakeMessage:
            def __init__(self, orig, content):
                self.author = orig.author
                self.channel = orig.channel
                self.guild = orig.guild
                self.content = content
                self.add_reaction = orig.add_reaction
        fake = FakeMessage(message, custom_content)
        await on_message(fake)
        return

    if message.author.bot:
        return
    content = message.content.strip()
    if not content:
        return

    lower_content = content.lower()
    # 無點 help
    if lower_content == 'help':
        embed = discord.Embed(title="📖 D!ce 機器人使用說明", color=0x00aaff)
        embed.add_field(name="🎲 通用骰子指令", value="`xDy` - 擲 x 粒 y 面骰，例如 `2D6`\n`xDy kh/kl/dh/dl` - 保留/放棄最高/最低骰\n`xDy >= t` - 篩選符合條件的骰子\n`xBy` - 不加總骰子，可加 `S` 排序\n`xUy z` - 獎勵骰系統\n`D66`, `D66s`, `D66n`", inline=False)
        embed.add_field(name="🔢 多重擲骰", value="`.次數 骰子指令` - 例如 `.5 3D6`（最多30次）", inline=False)
        embed.add_field(name="🎯 CoC 七版檢定", value="`.cc 技能值 [技能名稱]`\n`.cc1/cc2` 獎勵骰，`.ccn1/ccn2` 懲罰骰\n支援聯合檢定：`.cc 80,60 鬥毆,魅惑`\n多次檢定：`.10 cc 20`", inline=False)
        embed.add_field(name="🎲 PBTA 檢定", value="`.p 2d6[+/-修正] [移動名稱]` - 例如 `.p 2d6+2`", inline=False)
        embed.add_field(name="🧠 理智檢定", value="`.sc 目前SAN 成功損失 失敗損失`", inline=False)
        embed.add_field(name="📈 成長檢定", value="`.dp 技能值 技能名稱` - 失敗才成長1d10", inline=False)
        embed.add_field(name="📐 計算功能", value="`.calc 表達式` - 支援骰子\n直接輸入算式：`1d3+2` → `[3]+2=5`", inline=False)
        embed.add_field(name="🔒 暗骰（私訊）", value="`dr 指令` - 結果私訊給自己\n`ddr 指令` - 私訊給 GM 與自己\n`dddr 指令` - 僅私訊給 GM", inline=False)
        embed.add_field(name="👑 GM 管理", value="`.drgm addgm [化名]`\n`.drgm show`\n`.drgm del 編號/all`", inline=False)
        embed.add_field(name="🔧 自訂指令", value="`.cmd add 關鍵字 指令`\n`.cmd 關鍵字`", inline=False)
        embed.add_field(name="🎲 其他", value="`.int 最小 最大` - 隨機整數\n`.help` - 顯示此說明", inline=False)
        embed.set_footer(text=message.author.display_name, icon_url=message.author.display_avatar.url)
        await message.channel.send(embed=embed)
        return

    # dddr
    if lower_content.startswith('dddr '):
        expr = content[5:].strip()
        if parse_dice_expression(expr) is not None:
            await handle_roll(message, expr, 'gm_only')
        else:
            # 嘗試匹配 CoC 指令
            cc_match = re.match(r'^(cc(?:[12]?|n[12]?)?)(?:\s+(.*))?$', expr, re.I)
            if cc_match:
                cmd_part = cc_match.group(1).lower()
                args = cc_match.group(2) or ""
                bonus_dice = 0
                if cmd_part == 'cc1':
                    bonus_dice = 1
                elif cmd_part == 'cc2':
                    bonus_dice = 2
                elif cmd_part == 'ccn1':
                    bonus_dice = -1
                elif cmd_part == 'ccn2':
                    bonus_dice = -2
                parts = args.split(maxsplit=1)
                if not parts:
                    embed = discord.Embed(title="❌ 缺少技能值", description="請提供技能值", color=0xff0000)
                    await message.channel.send(embed=embed)
                    return
                try:
                    skill_val = int(parts[0])
                except:
                    embed = discord.Embed(title="❌ 技能值必須為數字", color=0xff0000)
                    await message.channel.send(embed=embed)
                    return
                skill_name = parts[1] if len(parts) > 1 else ""
                final_roll, level, bonus_desc, all_rolls = coc_check(skill_val, bonus_dice)
                output = f"**COC 七版檢定**\n"
                if bonus_dice > 0:
                    output += f" (+{bonus_dice}獎勵骰)\n"
                elif bonus_dice < 0:
                    output += f" ({-bonus_dice}懲罰骰)\n"
                if skill_name:
                    output += f"{skill_name} ({skill_val}%)\n"
                else:
                    output += f"技能值 {skill_val}\n"
                output += f"{bonus_desc} → 最終擲骰 {final_roll} → **{level}**"
                gms = gm_manager.get_gm_users(message.guild.id)
                recipients_ids = set(gms)
                if message.author.id not in gms:
                    recipients_ids.discard(message.author.id)
                success_count = 0
                alias = get_alias(message.guild.id, message.author.id)
                for uid in recipients_ids:
                    if uid == message.author.id:
                        user = message.author
                    else:
                        try:
                            user = await message.guild.fetch_member(uid)
                        except:
                            user = None
                    if user:
                        if await send_private(message, user, f"{message.author.display_name} 暗骰：\n{output}", alias_name=alias):
                            success_count += 1
                if success_count > 0:
                    await message.add_reaction('🔒')
                else:
                    embed = discord.Embed(title="❌ 私訊失敗", description="無法私訊給 GM，請檢查隱私設定。", color=0xff0000)
                    await message.channel.send(embed=embed)
            else:
                # 嘗試匹配 PBTA 指令
                p_match = re.match(r'^p(?:\s+(2d6[+-]?\d*)?(?:\s+(.*))?)?$', expr, re.I)
                if p_match:
                    dice_part = p_match.group(1) if p_match.group(1) else "2d6"
                    move_name = p_match.group(2) if p_match.group(2) else ""
                    res = pbta_check(dice_part)
                    if not res:
                        embed = discord.Embed(title="❌ 格式錯誤", description="請使用：`p 2d6[+/-修正] [移動名稱]`", color=0xff0000)
                        await message.channel.send(embed=embed)
                        return
                    r1, r2, mod, total, result = res
                    output = f"**PBTA 擲骰**\n"
                    if move_name:
                        output += f"移動：{move_name}\n"
                    output += f"骰子：{r1}+{r2} + {mod} = {total}\n結果：{result}"
                    gms = gm_manager.get_gm_users(message.guild.id)
                    recipients_ids = set(gms)
                    if message.author.id not in gms:
                        recipients_ids.discard(message.author.id)
                    success_count = 0
                    alias = get_alias(message.guild.id, message.author.id)
                    for uid in recipients_ids:
                        if uid == message.author.id:
                            user = message.author
                        else:
                            try:
                                user = await message.guild.fetch_member(uid)
                            except:
                                user = None
                        if user:
                            if await send_private(message, user, f"{message.author.display_name} 暗骰：\n{output}", alias_name=alias):
                                success_count += 1
                    if success_count > 0:
                        await message.add_reaction('🔒')
                    else:
                        embed = discord.Embed(title="❌ 私訊失敗", description="無法私訊給 GM，請檢查隱私設定。", color=0xff0000)
                        await message.channel.send(embed=embed)
                else:
                    embed = discord.Embed(title="⚠️ 不支援的暗骰", description="目前暗骰僅支援 CoC 指令 (cc) 與 PBTA 指令 (p)，其他指令請使用點命令前綴。", color=0xffaa00)
                    await message.channel.send(embed=embed)
        return

    # ddr
    if lower_content.startswith('ddr '):
        expr = content[4:].strip()
        if parse_dice_expression(expr) is not None:
            await handle_roll(message, expr, 'gm')
        else:
            cc_match = re.match(r'^(cc(?:[12]?|n[12]?)?)(?:\s+(.*))?$', expr, re.I)
            if cc_match:
                cmd_part = cc_match.group(1).lower()
                args = cc_match.group(2) or ""
                bonus_dice = 0
                if cmd_part == 'cc1':
                    bonus_dice = 1
                elif cmd_part == 'cc2':
                    bonus_dice = 2
                elif cmd_part == 'ccn1':
                    bonus_dice = -1
                elif cmd_part == 'ccn2':
                    bonus_dice = -2
                parts = args.split(maxsplit=1)
                if not parts:
                    embed = discord.Embed(title="❌ 缺少技能值", description="請提供技能值", color=0xff0000)
                    await message.channel.send(embed=embed)
                    return
                try:
                    skill_val = int(parts[0])
                except:
                    embed = discord.Embed(title="❌ 技能值必須為數字", color=0xff0000)
                    await message.channel.send(embed=embed)
                    return
                skill_name = parts[1] if len(parts) > 1 else ""
                final_roll, level, bonus_desc, all_rolls = coc_check(skill_val, bonus_dice)
                output = f"**COC 七版檢定**\n"
                if bonus_dice > 0:
                    output += f" (+{bonus_dice}獎勵骰)\n"
                elif bonus_dice < 0:
                    output += f" ({-bonus_dice}懲罰骰)\n"
                if skill_name:
                    output += f"{skill_name} ({skill_val}%)\n"
                else:
                    output += f"技能值 {skill_val}\n"
                output += f"{bonus_desc} → 最終擲骰 {final_roll} → **{level}**"
                gms = gm_manager.get_gm_users(message.guild.id)
                recipients = set(gms)
                recipients.add(message.author.id)
                success_count = 0
                alias = get_alias(message.guild.id, message.author.id)
                for uid in recipients:
                    if uid == message.author.id:
                        user = message.author
                    else:
                        try:
                            user = await message.guild.fetch_member(uid)
                        except:
                            user = None
                    if user:
                        if await send_private(message, user, f"{message.author.display_name} 暗骰：\n{output}", alias_name=alias):
                            success_count += 1
                if success_count > 0:
                    await message.add_reaction('📬')
                else:
                    embed = discord.Embed(title="❌ 私訊失敗", description="無法私訊，請檢查隱私設定。", color=0xff0000)
                    await message.channel.send(embed=embed)
            else:
                p_match = re.match(r'^p(?:\s+(2d6[+-]?\d*)?(?:\s+(.*))?)?$', expr, re.I)
                if p_match:
                    dice_part = p_match.group(1) if p_match.group(1) else "2d6"
                    move_name = p_match.group(2) if p_match.group(2) else ""
                    res = pbta_check(dice_part)
                    if not res:
                        embed = discord.Embed(title="❌ 格式錯誤", description="請使用：`p 2d6[+/-修正] [移動名稱]`", color=0xff0000)
                        await message.channel.send(embed=embed)
                        return
                    r1, r2, mod, total, result = res
                    output = f"**PBTA 擲骰**\n"
                    if move_name:
                        output += f"移動：{move_name}\n"
                    output += f"骰子：{r1}+{r2} + {mod} = {total}\n結果：{result}"
                    gms = gm_manager.get_gm_users(message.guild.id)
                    recipients = set(gms)
                    recipients.add(message.author.id)
                    success_count = 0
                    alias = get_alias(message.guild.id, message.author.id)
                    for uid in recipients:
                        if uid == message.author.id:
                            user = message.author
                        else:
                            try:
                                user = await message.guild.fetch_member(uid)
                            except:
                                user = None
                        if user:
                            if await send_private(message, user, f"{message.author.display_name} 暗骰：\n{output}", alias_name=alias):
                                success_count += 1
                    if success_count > 0:
                        await message.add_reaction('📬')
                    else:
                        embed = discord.Embed(title="❌ 私訊失敗", description="無法私訊，請檢查隱私設定。", color=0xff0000)
                        await message.channel.send(embed=embed)
                else:
                    embed = discord.Embed(title="⚠️ 不支援的暗骰", description="目前暗骰僅支援 CoC 指令 (cc) 與 PBTA 指令 (p)，其他指令請使用點命令前綴。", color=0xffaa00)
                    await message.channel.send(embed=embed)
        return

    # dr
    if lower_content.startswith('dr '):
        expr = content[3:].strip()
        if parse_dice_expression(expr) is not None:
            await handle_roll(message, expr, 'self')
        else:
            cc_match = re.match(r'^(cc(?:[12]?|n[12]?)?)(?:\s+(.*))?$', expr, re.I)
            if cc_match:
                cmd_part = cc_match.group(1).lower()
                args = cc_match.group(2) or ""
                bonus_dice = 0
                if cmd_part == 'cc1':
                    bonus_dice = 1
                elif cmd_part == 'cc2':
                    bonus_dice = 2
                elif cmd_part == 'ccn1':
                    bonus_dice = -1
                elif cmd_part == 'ccn2':
                    bonus_dice = -2
                parts = args.split(maxsplit=1)
                if not parts:
                    embed = discord.Embed(title="❌ 缺少技能值", description="請提供技能值", color=0xff0000)
                    await message.channel.send(embed=embed)
                    return
                try:
                    skill_val = int(parts[0])
                except:
                    embed = discord.Embed(title="❌ 技能值必須為數字", color=0xff0000)
                    await message.channel.send(embed=embed)
                    return
                skill_name = parts[1] if len(parts) > 1 else ""
                final_roll, level, bonus_desc, all_rolls = coc_check(skill_val, bonus_dice)
                output = f"**COC 七版檢定**\n"
                if bonus_dice > 0:
                    output += f" (+{bonus_dice}獎勵骰)\n"
                elif bonus_dice < 0:
                    output += f" ({-bonus_dice}懲罰骰)\n"
                if skill_name:
                    output += f"{skill_name} ({skill_val}%)\n"
                else:
                    output += f"技能值 {skill_val}\n"
                output += f"{bonus_desc} → 最終擲骰 {final_roll} → **{level}**"
                if await send_private(message, message.author, f"{message.author.display_name} 暗骰：\n{output}"):
                    await message.add_reaction('📬')
                else:
                    embed = discord.Embed(title="❌ 私訊失敗", description="無法私訊，請檢查隱私設定。", color=0xff0000)
                    await message.channel.send(embed=embed)
            else:
                p_match = re.match(r'^p(?:\s+(2d6[+-]?\d*)?(?:\s+(.*))?)?$', expr, re.I)
                if p_match:
                    dice_part = p_match.group(1) if p_match.group(1) else "2d6"
                    move_name = p_match.group(2) if p_match.group(2) else ""
                    res = pbta_check(dice_part)
                    if not res:
                        embed = discord.Embed(title="❌ 格式錯誤", description="請使用：`p 2d6[+/-修正] [移動名稱]`", color=0xff0000)
                        await message.channel.send(embed=embed)
                        return
                    r1, r2, mod, total, result = res
                    output = f"**PBTA 擲骰**\n"
                    if move_name:
                        output += f"移動：{move_name}\n"
                    output += f"骰子：{r1}+{r2} + {mod} = {total}\n結果：{result}"
                    if await send_private(message, message.author, f"{message.author.display_name} 暗骰：\n{output}"):
                        await message.add_reaction('📬')
                    else:
                        embed = discord.Embed(title="❌ 私訊失敗", description="無法私訊，請檢查隱私設定。", color=0xff0000)
                        await message.channel.send(embed=embed)
                else:
                    embed = discord.Embed(title="⚠️ 不支援的暗骰", description="目前暗骰僅支援 CoC 指令 (cc) 與 PBTA 指令 (p)，其他指令請使用點命令前綴。", color=0xffaa00)
                    await message.channel.send(embed=embed)
        return

    # 不帶點的 cc 家族指令 (公開)
    cc_match = re.match(r'^(cc(?:[12]?|n[12]?)?)(?:\s+(.*))?$', content, re.I)
    if cc_match:
        cmd_part = cc_match.group(1).lower()
        args = cc_match.group(2) or ""
        fake_cmd = f".{cmd_part} {args}".strip()
        await handle_dot_command(message, fake_cmd[1:])
        return

    # 不帶點的 p 指令 (公開)
    p_match = re.match(r'^p(?:\s+(2d6[+-]?\d*)?(?:\s+(.*))?)?$', content, re.I)
    if p_match:
        dice_part = p_match.group(1) if p_match.group(1) else "2d6"
        move_name = p_match.group(2) if p_match.group(2) else ""
        res = pbta_check(dice_part)
        if res:
            r1, r2, mod, total, result = res
            embed = discord.Embed(title="🎲 PBTA 擲骰", color=0x00aaff)
            if move_name:
                embed.add_field(name="移動", value=move_name, inline=False)
            embed.add_field(name="骰子結果", value=f"{r1}+{r2} + {mod} = {total}", inline=False)
            embed.add_field(name="判定結果", value=result, inline=False)
            embed.set_footer(text=message.author.display_name, icon_url=message.author.display_avatar.url)
            await message.channel.send(embed=embed)
        else:
            embed = discord.Embed(title="❌ 格式錯誤", description="請使用：`p 2d6[+/-修正] [移動名稱]`", color=0xff0000)
            await message.channel.send(embed=embed)
        return

    if content.startswith('.'):
        cmd = content[1:].strip()
        await handle_dot_command(message, cmd)
        return

    # 嘗試將整段訊息當作骰子表達式解析
    dice_res = parse_dice_expression(content)
    if dice_res is not None:
        embed = discord.Embed(title="🎲 擲骰結果", description=dice_res.format(), color=0x00aaff)
        embed.set_footer(text=message.author.display_name, icon_url=message.author.display_avatar.url)
        await message.channel.send(embed=embed)
        return

    # 向後相容：分離骰子部分與附帶文字
    dice_pattern = re.compile(r'^([0-9]+[DBU][0-9]+[Ss]?(?:\s+[0-9]+)?|D66[sn]?)', re.I)
    match = dice_pattern.match(content)
    if match:
        dice_part = match.group(1)
        text_part = content[match.end():].strip()
        dice_res = parse_dice_expression(dice_part)
        if dice_res:
            dice_res.text = text_part if text_part else None
            embed = discord.Embed(title="🎲 擲骰結果", description=dice_res.format(), color=0x00aaff)
            embed.set_footer(text=message.author.display_name, icon_url=message.author.display_avatar.url)
            await message.channel.send(embed=embed)
        else:
            embed = discord.Embed(title="❌ 無法解析骰子指令", description=dice_part, color=0xff0000)
            await message.channel.send(embed=embed)
        return

    # 直接算式計算（無點前綴）
    has_operator = re.search(r'[+\-*/%]|[\*]{2}|//', content)
    has_dice = re.search(r'\d+[Dd]\d+', content)
    if has_operator or has_dice:
        embed = compute_expression(content, message.author)
        if embed:
            await message.channel.send(embed=embed)
            return

if __name__ == "__main__":
    TOKEN = os.getenv('DISCORD_TOKEN')
    if not TOKEN:
        print("錯誤：找不到 DISCORD_TOKEN 環境變數。請在 Railway 設定 Variables 或在本機執行前設定環境變數。")
        exit(1)
    bot.run(TOKEN)