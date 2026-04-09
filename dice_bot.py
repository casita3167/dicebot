import discord
from discord.ext import commands
import re
import random
import ast
import json
import os
from collections import defaultdict

# ---------- 安全求值函式 ----------
def safe_eval(expr_str: str) -> float:
    """
    安全地計算只包含數字、基本運算符、括號、** 的表達式。
    回傳計算結果，若表達式不安全或無效則回傳 None。
    """
    # 允許的字元：數字、空格、基本運算符、括號、點、負號（開頭或運算符後）
    # 注意：不允許任何字母（除了 e 科學記號，但我們禁止）
    if re.search(r'[^0-9\s\+\-\*\/\(\)\.\*\*]', expr_str):
        return None
    # 避免連續兩個運算符等危險模式（簡單過濾）
    if re.search(r'[\+\-\*\/]{2,}', expr_str):
        return None
    try:
        # 限制命名空間，只允許基本數學函數（可選）
        allowed_globals = {
            '__builtins__': {},
            'abs': abs,
            'round': round,
        }
        result = eval(expr_str, allowed_globals, {})
        # 確保結果為數字
        if isinstance(result, (int, float)):
            return result
        return None
    except Exception:
        return None

def safe_compute_with_dice(expr: str) -> (float, str):
    """
    將表達式中的骰子替換為數值，然後用 safe_eval 計算。
    回傳 (結果, 替換後表達式字串) 或 (None, None)
    """
    def replace_dice(match):
        dice_expr = match.group(0)
        # 嘗試解析為骰子
        res = parse_dice_expression(dice_expr)
        if res and res.total is not None:
            return str(res.total)
        elif res and res.rolls:
            return str(sum(res.rolls))
        else:
            multi = parse_multi_dice(dice_expr)
            if multi:
                return str(multi[0])
            return dice_expr

    # 骰子模式（排除表情符號中的數字）
    dice_pattern = re.compile(r'(?<![:<])(\d+[DBU]\d+[Ss]?(?:\s+\d+)?|D66[sn]?|\d+[Dd]\d+\+\d+[Dd]\d+)(?![:>])', re.I)
    replaced = dice_pattern.sub(replace_dice, expr)
    # 再次處理可能殘留的骰子（如單獨的 3d6）
    replaced = dice_pattern.sub(replace_dice, replaced)
    result = safe_eval(replaced)
    return result, replaced

# ---------- 輔助：移除表情符號 ----------
def remove_discord_emoji(text: str) -> str:
    """移除 Discord 自訂表情符號（如 :frog8: 或 <:name:123>）"""
    return re.sub(r'<a?:\w+:\d+>|:\w+:', '', text)

# ---------- 骰子核心函式（保持原有，但使用新的安全計算）----------
class DiceResult:
    # 保持原樣，略...
    def __init__(self, raw_expr, rolls, total=None, text=None, success=None, details=None, filtered_rolls=None, arithmetic=None):
        self.raw_expr = raw_expr
        self.rolls = rolls
        self.total = total
        self.text = text
        self.success = success
        self.details = details
        self.filtered_rolls = filtered_rolls
        self.arithmetic = arithmetic

    def format(self):
        rolls_str = ', '.join(map(str, self.rolls))
        if self.arithmetic and self.total is not None and self.arithmetic.strip():
            sum_rolls = sum(self.rolls)
            base = f"{self.raw_expr}： {sum_rolls}[{rolls_str}]{self.arithmetic} = {self.total}"
            if self.text:
                base = f"{self.text} {base}"
            return base
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
    # 保持原樣
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

def dice_dy(expr):
    m = re.match(r'^(\d+)D(\d+)(.*)$', expr, re.I)
    if not m:
        return None
    count = int(m.group(1))
    sides = int(m.group(2))
    rest = m.group(3)

    if re.search(r'\d+[Dd]\d+', rest, re.I):
        return None

    full_expr = f"{count}D{sides}{rest}"
    base_expr, keep, drop, keep_low, drop_low, comp_op, comp_val = parse_modifiers(full_expr)
    rolls = [roll_dice(sides) for _ in range(count)]
    if keep is not None:
        sorted_rolls = sorted(rolls, reverse=not keep_low)
        rolls = sorted_rolls[:keep]
    elif drop is not None:
        sorted_rolls = sorted(rolls, reverse=drop_low)
        rolls = sorted_rolls[drop:]
    sum_rolls = sum(rolls)
    total = sum_rolls
    arithmetic_part = ""

    dice_part = f"{count}D{sides}"
    if base_expr != dice_part and ('+' in base_expr or '-' in base_expr or '*' in base_expr or '/' in base_expr):
        if base_expr.startswith(dice_part):
            arithmetic_part = base_expr[len(dice_part):]
            full_arithmetic_expr = f"{sum_rolls}{arithmetic_part}"
            calc_total = safe_eval(full_arithmetic_expr)  # 使用統一安全函式
            if calc_total is not None:
                total = calc_total
            else:
                return None

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
    # 保持原樣（不涉及算術）
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

def parse_multi_dice(expr):
    tokens = re.finditer(r'(?<![:<])([+-]?\s*\d+[Dd]\d+|[+-]?\s*\d+)(?![:>])', expr, re.I)
    total = 0
    details_parts = []
    for token in tokens:
        part = token.group().strip()
        if not part:
            continue
        sign = 1
        if part[0] in '+-':
            sign = -1 if part[0] == '-' else 1
            part = part[1:].strip()
        res = parse_dice_expression(part)
        if res and res.rolls:
            val = res.total if res.total is not None else sum(res.rolls)
            rolls_str = ','.join(map(str, res.rolls))
            details_parts.append(f"{'+' if sign == 1 else '-'}{part}[{rolls_str}]")
            total += sign * val
        else:
            try:
                val = int(part)
                details_parts.append(f"{'+' if sign == 1 else '-'}{part}")
                total += sign * val
            except ValueError:
                return None
    if len(details_parts) < 2:
        return None
    details_str = ''.join(details_parts).lstrip('+')
    return total, f"{details_str} = {total}"

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

# ---------- 成長檢定（已存在）----------
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

# ---------- GM 管理（保持原樣）----------
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

# ---------- 抽籤表（伺服器隔離 + 持久化）----------
class TableManager:
    def __init__(self, filename='tables.json'):
        self.filename = filename
        self.data = defaultdict(dict)  # {guild_id: {table_name: [items]}}
        self.load()
    def load(self):
        if os.path.exists(self.filename):
            with open(self.filename, 'r', encoding='utf-8') as f:
                raw = json.load(f)
                self.data = defaultdict(dict, {int(k): v for k, v in raw.items()})
    def save(self):
        # 將 defaultdict 轉為普通 dict 儲存
        to_save = {str(k): v for k, v in self.data.items()}
        with open(self.filename, 'w', encoding='utf-8') as f:
            json.dump(to_save, f, ensure_ascii=False, indent=2)
    def add_table(self, guild_id, name, items):
        self.data[guild_id][name] = items
        self.save()
    def get_table(self, guild_id, name):
        return self.data[guild_id].get(name)
    def list_tables(self, guild_id):
        return list(self.data[guild_id].items())
    def del_table(self, guild_id, name):
        if name in self.data[guild_id]:
            del self.data[guild_id][name]
            self.save()
            return True
        return False
    def clear_tables(self, guild_id):
        self.data[guild_id] = {}
        self.save()

# ---------- Discord Bot ----------
intents = discord.Intents.default()
intents.message_content = True
bot = commands.Bot(command_prefix='.', intents=intents)

gm_manager = GMManager()
cmd_manager = CmdManager()
table_manager = TableManager()

# ---------- 其他功能 ----------
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

# ---------- 獨立路由函式 ----------
async def handle_coc_roll(message, args, target_type, bonus_dice=0):
    """處理 CoC 檢定"""
    if not args:
        await send_result(message, "❌ 缺少技能值", title="COC 檢定錯誤", color=0xff0000, target_type=target_type)
        return
    parts = args.split(maxsplit=1)
    skill_values_part = parts[0]
    skill_names_part = parts[1] if len(parts) > 1 else ""
    try:
        skill_values = [int(x.strip()) for x in skill_values_part.split(',')]
        skill_names = [x.strip() for x in skill_names_part.split(',')] if skill_names_part else []
        while len(skill_names) < len(skill_values):
            skill_names.append("")
    except:
        await send_result(message, "技能值必須為數字，多個技能用逗號分隔", title="COC 檢定錯誤", color=0xff0000, target_type=target_type)
        return
    output_lines = []
    for sv, sn in zip(skill_values, skill_names):
        final_roll, level, bonus_desc, all_rolls = coc_check(sv, bonus_dice)
        line = f"{sn} ({sv}%)" if sn else f"技能值 {sv}"
        line += f"\n{bonus_desc} → 最終擲骰 {final_roll} → **{level}**"
        output_lines.append(line)
    title = "COC 七版檢定"
    if bonus_dice > 0:
        title += f" (+{bonus_dice}獎勵骰)"
    elif bonus_dice < 0:
        title += f" ({-bonus_dice}懲罰骰)"
    await send_result(message, "\n\n".join(output_lines), title=title, target_type=target_type)

async def handle_pbta_roll(message, args, target_type):
    """處理 PBTA 檢定"""
    if not args:
        await send_result(message, "請提供骰子表達式，例如：`p 2d6+2`", title="PBTA 格式錯誤", color=0xff0000, target_type=target_type)
        return
    parts = args.split(maxsplit=1)
    dice_expr = parts[0]
    move_name = parts[1] if len(parts) > 1 else ""
    res = pbta_check(dice_expr)
    if not res:
        await send_result(message, "請使用：`2d6[+/-修正]`", title="PBTA 格式錯誤", color=0xff0000, target_type=target_type)
        return
    r1, r2, mod, total, result = res
    if move_name:
        content = f"移動：{move_name}\n骰子結果：{r1}+{r2} + {mod} = {total}\n判定結果：{result}"
    else:
        content = f"骰子結果：{r1}+{r2} + {mod} = {total}\n判定結果：{result}"
    await send_result(message, content, title="🎲 PBTA 擲骰", target_type=target_type)

async def handle_sc_roll(message, args, target_type):
    """處理理智檢定"""
    parts = args.split()
    if len(parts) < 3:
        await send_result(message, "格式錯誤，請使用：`目前SAN 成功損失 失敗損失`\n例如：`50 0 1d6`", title="SAN 檢定錯誤", color=0xff0000, target_type=target_type)
        return
    try:
        current_san = int(parts[0])
        success_loss = parts[1]
        fail_loss = parts[2]
    except:
        await send_result(message, "參數錯誤，請檢查數字格式", title="SAN 檢定錯誤", color=0xff0000, target_type=target_type)
        return
    roll = random.randint(1, 100)
    if roll <= current_san:
        loss = roll_dice_expr(success_loss)
        result_text = f"理智檢定成功！損失 {loss} 點 SAN。"
    else:
        loss = roll_dice_expr(fail_loss)
        result_text = f"理智檢定失敗！損失 {loss} 點 SAN。"
    new_san = current_san - loss
    content = f"目前 SAN：{current_san}\n擲骰結果：{roll}\n結果：{result_text}\n剩餘 SAN：{new_san}"
    color = 0x00aa00 if roll <= current_san else 0xaa0000
    await send_result(message, content, title="🧠 SAN 檢定", color=color, target_type=target_type)

async def handle_int_roll(message, args, target_type):
    """處理隨機整數"""
    parts = args.split()
    if len(parts) != 2:
        await send_result(message, "格式：`最小 最大`", title="隨機整數錯誤", color=0xff0000, target_type=target_type)
        return
    try:
        low = int(parts[0])
        high = int(parts[1])
        if low > high:
            low, high = high, low
        val = random.randint(low, high)
        await send_result(message, f".int {low} {high}：{val}", title="🎲 隨機整數", target_type=target_type)
    except:
        await send_result(message, "請輸入兩個整數", title="隨機整數錯誤", color=0xff0000, target_type=target_type)

async def handle_calc_roll(message, expr, target_type):
    """處理計算（支援骰子）"""
    if not expr:
        await send_result(message, "請提供表達式，例如：`5+3*2` 或 `(1D100+5)/2`", title="計算錯誤", color=0xff0000, target_type=target_type)
        return
    # 移除表情符號
    expr = remove_discord_emoji(expr)
    result, replaced = safe_compute_with_dice(expr)
    if result is not None:
        content = f"{expr}\n= {result}" if replaced != expr else f"{expr} = {result}"
        await send_result(message, content, title="📐 計算結果", target_type=target_type)
    else:
        await send_result(message, "表達式錯誤，請檢查算式", title="計算錯誤", color=0xff0000, target_type=target_type)

async def send_result(message, content, title=None, color=0x00aaff, target_type='channel'):
    """統一的結果發送函式"""
    embed = discord.Embed(title=title, description=content, color=color)
    embed.set_footer(text=message.author.display_name, icon_url=message.author.display_avatar.url)
    if target_type == 'channel':
        await message.channel.send(embed=embed)
    elif target_type == 'self':
        await send_private(message, message.author, f"{message.author.display_name} 的暗骰結果：\n{content}")
        await message.add_reaction('📬')
    elif target_type == 'gm':
        gms = gm_manager.get_gm_users(message.guild.id)
        if gms:
            alias = get_alias(message.guild.id, message.author.id)
            for gm_id in gms:
                gm_user = message.guild.get_member(gm_id)
                if gm_user:
                    await send_private(message, gm_user, f"{message.author.display_name} 的暗骰結果：\n{content}\n(來自 {message.author.display_name})", alias_name=alias)
            await send_private(message, message.author, f"{message.author.display_name} 的暗骰結果：\n{content}", alias_name=alias)
            await message.add_reaction('📬')
        else:
            await message.channel.send(embed=discord.Embed(title="⚠️ 未設定 GM", description="此伺服器尚未設定 GM，請使用 `.drgm addgm` 登記。", color=0xffaa00))
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
                user = message.guild.get_member(uid)
            if user:
                if await send_private(message, user, f"{message.author.display_name} 的暗骰結果 (僅 GM 可見)：\n{content}", alias_name=alias):
                    success_count += 1
        if success_count > 0:
            await message.add_reaction('🔒')
        else:
            await message.channel.send(embed=discord.Embed(title="❌ 私訊失敗", description="無法私訊給任何 GM，請檢查隱私設定。", color=0xff0000))

async def handle_roll(message, roll_expr, target_type='channel'):
    """路由函式：根據表達式類型分發到對應處理器"""
    # 移除表情符號
    roll_expr = remove_discord_emoji(roll_expr)
    lower_expr = roll_expr.lower().strip()

    # CC / CoC
    cc_match = re.match(r'^(cc|cc[12]|ccn[12]?|coc)(?:\s+(.*))?$', lower_expr, re.I)
    if cc_match:
        cmd_part = cc_match.group(1).lower()
        args = cc_match.group(2) or ""
        bonus_dice = 0
        if cmd_part in ('cc1', 'coc1'):
            bonus_dice = 1
        elif cmd_part == 'cc2':
            bonus_dice = 2
        elif cmd_part == 'ccn1':
            bonus_dice = -1
        elif cmd_part == 'ccn2':
            bonus_dice = -2
        elif cmd_part == 'ccn':
            bonus_dice = -1
        await handle_coc_roll(message, args, target_type, bonus_dice)
        return

    # PBTA
    p_match = re.match(r'^(p|pbta)\s+(2d6[+-]?\d*)(?:\s+(.*))?$', lower_expr, re.I)
    if p_match:
        dice_expr = p_match.group(2)
        move_name = p_match.group(3) if p_match.group(3) else ""
        await handle_pbta_roll(message, f"{dice_expr} {move_name}".strip(), target_type)
        return

    # SC
    sc_match = re.match(r'^sc\s+(.+)$', lower_expr, re.I)
    if sc_match:
        await handle_sc_roll(message, sc_match.group(1), target_type)
        return

    # INT
    int_match = re.match(r'^int\s+(\d+)\s+(\d+)$', lower_expr)
    if int_match:
        await handle_int_roll(message, f"{int_match.group(1)} {int_match.group(2)}", target_type)
        return

    # CALC
    calc_match = re.match(r'^calc\s+(.+)$', lower_expr)
    if calc_match:
        await handle_calc_roll(message, calc_match.group(1), target_type)
        return

    # 一般骰子表達式
    res = parse_dice_expression(roll_expr)
    if res:
        await send_result(message, res.format(), title="🎲 擲骰結果", target_type=target_type)
        return

    multi = parse_multi_dice(roll_expr)
    if multi:
        total, details = multi
        await send_result(message, f"{roll_expr}\n{details}", title="🎲 多重骰組相加", target_type=target_type)
        return

    await send_result(message, f"無效的骰子指令：{roll_expr}", title="❌ 錯誤", color=0xff0000, target_type=target_type)

# ---------- 點命令處理（包含 help、抽籤表、自訂指令等）----------
async def handle_dot_command(message, cmd):
    """處理 . 開頭的命令"""
    if cmd.startswith('help'):
        await show_help(message, cmd[4:].strip())
        return True

    # 處理 .rts 相關指令（使用 table_manager）
    if cmd.startswith('rts'):
        content = cmd[3:].strip()
        guild_id = message.guild.id
        if content == 'list':
            tables = table_manager.list_tables(guild_id)
            if not tables:
                await message.channel.send("📭 目前沒有任何抽籤表。")
            else:
                embed = discord.Embed(title="📋 抽籤表列表", color=0x00aaff)
                desc = ""
                for name, items in tables:
                    desc += f"**{name}**：{len(items)} 個項目\n"
                embed.description = desc
                embed.set_footer(text=message.author.display_name, icon_url=message.author.display_avatar.url)
                await message.channel.send(embed=embed)
            return True
        if content.startswith('del '):
            table_name = content[4:].strip()
            if table_manager.del_table(guild_id, table_name):
                await message.channel.send(f"✅ 已刪除抽籤表【{table_name}】")
            else:
                await message.channel.send(f"❌ 找不到抽籤表【{table_name}】")
            return True
        if content == 'clear':
            table_manager.clear_tables(guild_id)
            await message.channel.send("✅ 已清空所有抽籤表")
            return True
        # 建立表格
        match = re.split(r'[：:]', content, maxsplit=1)
        if len(match) < 2:
            await message.channel.send("格式不對喔！請用：`.rts 名稱：項目1,項目2...` 或 `.rts list` 或 `.rts del 名稱` 或 `.rts clear`")
            return True
        table_name = match[0].strip()
        items = [i.strip() for i in match[1].split(',') if i.strip()]
        if not items:
            await message.channel.send("項目好像是空的？")
            return True
        table_manager.add_table(guild_id, table_name, items)
        await message.channel.send(f"✅ 搞定！已紀錄【{table_name}】，共 {len(items)} 個項目。")
        return True

    # 多重擲骰 .次數 指令（略，保持原樣，但注意移除表情符號）
    multi_match = re.match(r'^(\d+)\s+(.+)$', cmd)
    if multi_match:
        times = int(multi_match.group(1))
        rest = multi_match.group(2).strip()
        # 可選：支援多重 CoC 檢定
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
                await message.channel.send(embed=discord.Embed(title="❌ 缺少技能值", color=0xff0000))
                return True
            try:
                skill_values_part = parts[0]
                skill_names_part = parts[1] if len(parts) > 1 else ""
                skill_values = [int(x.strip()) for x in skill_values_part.split(',')]
                skill_names = [x.strip() for x in skill_names_part.split(',')] if skill_names_part else []
                while len(skill_names) < len(skill_values):
                    skill_names.append("")
            except:
                await message.channel.send(embed=discord.Embed(title="❌ 技能值格式錯誤", color=0xff0000))
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
                await message.channel.send(embed=discord.Embed(title="❌ 無法執行檢定", color=0xff0000))
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
                await message.channel.send(embed=discord.Embed(title="❌ 多重擲骰失敗", description=rest, color=0xff0000))
            return True

    # 其他指令：int, calc, cc, p, sc, dp, drgm, cmd 等（保持原樣但調用新的路由）
    if cmd.startswith('int'):
        parts = cmd.split()
        if len(parts) == 3:
            await handle_int_roll(message, f"{parts[1]} {parts[2]}", 'channel')
        else:
            await message.channel.send(embed=discord.Embed(title="❌ 格式錯誤", description="格式：`.int 最小 最大`", color=0xff0000))
        return True

    if cmd.startswith('calc'):
        expr = cmd[4:].strip()
        await handle_calc_roll(message, expr, 'channel')
        return True

    if cmd.startswith(('coc', 'cc')):
        # 解析獎勵骰等，然後呼叫 handle_coc_roll
        bonus_dice = 0
        rest = ""
        m_ccn = re.match(r'^ccn([12]?)(.*)$', cmd, re.I)
        if m_ccn:
            suffix = m_ccn.group(1)
            rest = m_ccn.group(2).strip()
            bonus_dice = -1 if suffix != '2' else -2
        else:
            m_cc = re.match(r'^cc([12]?)(.*)$', cmd, re.I)
            if m_cc:
                suffix = m_cc.group(1)
                rest = m_cc.group(2).strip()
                bonus_dice = int(suffix) if suffix else 0
            else:
                if cmd.startswith('coc'):
                    rest = cmd[3:].strip()
                else:
                    rest = cmd[2:].strip()
        await handle_coc_roll(message, rest, 'channel', bonus_dice)
        return True

    if cmd.startswith(('pbta', 'p')):
        rest = cmd[3:].strip() if cmd.startswith('pbta') else cmd[1:].strip()
        await handle_pbta_roll(message, rest, 'channel')
        return True

    if cmd.startswith('sc'):
        await handle_sc_roll(message, cmd[2:].strip(), 'channel')
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

    # 未知指令
    await message.channel.send(embed=discord.Embed(title="❓ 未知的點命令", description="輸入 `.help` 查看所有功能。", color=0xff0000))
    return True

async def show_help(message, category):
    """顯示幫助，從 help.json 讀取"""
    if not os.path.exists('help.json'):
        await message.channel.send("❌ 找不到幫助文件 help.json")
        return
    with open('help.json', 'r', encoding='utf-8') as f:
        help_data = json.load(f)
    if not category:
        # 顯示所有分類列表
        embed = discord.Embed(title="📖 D!ce 機器人幫助", color=0x00aaff)
        categories = list(help_data.keys())
        embed.description = "可用分類：`" + "`, `".join(categories) + "`\n使用 `.help 分類名` 查看詳細說明。"
        embed.set_footer(text=message.author.display_name, icon_url=message.author.display_avatar.url)
        await message.channel.send(embed=embed)
    else:
        text = help_data.get(category)
        if text:
            embed = discord.Embed(title=f"📖 {category} 幫助", description=text, color=0x00aaff)
            embed.set_footer(text=message.author.display_name, icon_url=message.author.display_avatar.url)
            await message.channel.send(embed=embed)
        else:
            await message.channel.send(f"❌ 沒有「{category}」這個分類。使用 `.help` 查看所有分類。")

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

    # 移除表情符號（避免觸發）
    clean_content = remove_discord_emoji(content)

    # 抽籤表功能：$名稱
    if clean_content.startswith('$'):
        table_name = clean_content[1:].strip()
        guild_id = message.guild.id
        items = table_manager.get_table(guild_id, table_name)
        if items:
            idx = random.randint(0, len(items)-1)
            result_item = items[idx]
            await message.channel.send(f"[{idx+1}] {result_item}")
            return

    lower_content = clean_content.lower()
    # 無點 help
    if lower_content == 'help':
        await show_help(message, "")
        return

    # dddr / ddr / dr 暗骰
    if lower_content.startswith('dddr '):
        expr = content[5:].strip()  # 原始內容（保留未移除表情？但移除較安全）
        expr = remove_discord_emoji(expr)
        await handle_roll(message, expr, 'gm_only')
        return
    if lower_content.startswith('ddr '):
        expr = content[4:].strip()
        expr = remove_discord_emoji(expr)
        await handle_roll(message, expr, 'gm')
        return
    if lower_content.startswith('dr '):
        expr = content[3:].strip()
        expr = remove_discord_emoji(expr)
        await handle_roll(message, expr, 'self')
        return

    # 不帶點的 cc/p 家族（公開）
    cc_match = re.match(r'^(cc(?:[12]?|n[12]?)?)(?:\s+(.*))?$', clean_content, re.I)
    if cc_match:
        cmd_part = cc_match.group(1).lower()
        args = cc_match.group(2) or ""
        fake_cmd = f".{cmd_part} {args}".strip()
        await handle_dot_command(message, fake_cmd[1:])
        return

    p_match = re.match(r'^p(?:\s+(2d6[+-]?\d*)?(?:\s+(.*))?)?$', clean_content, re.I)
    if p_match:
        dice_part = p_match.group(1) if p_match.group(1) else "2d6"
        move_name = p_match.group(2) if p_match.group(2) else ""
        await handle_pbta_roll(message, f"{dice_part} {move_name}".strip(), 'channel')
        return

    if content.startswith('.'):
        cmd = content[1:].strip()
        await handle_dot_command(message, cmd)
        return

    # 嘗試當作骰子表達式或計算式
    dice_res = parse_dice_expression(clean_content)
    if dice_res is not None:
        await send_result(message, dice_res.format(), title="🎲 擲骰結果", target_type='channel')
        return

    multi = parse_multi_dice(clean_content)
    if multi:
        total, details = multi
        await send_result(message, f"{clean_content}\n{details}", title="🎲 多重骰組相加", target_type='channel')
        return

    # 向後相容：分離骰子部分與附帶文字
    dice_pattern = re.compile(r'^([0-9]+[DBU][0-9]+[Ss]?(?:\s+[0-9]+)?|D66[sn]?)', re.I)
    match = dice_pattern.match(clean_content)
    if match:
        dice_part = match.group(1)
        text_part = clean_content[match.end():].strip()
        dice_res = parse_dice_expression(dice_part)
        if dice_res:
            dice_res.text = text_part if text_part else None
            await send_result(message, dice_res.format(), title="🎲 擲骰結果", target_type='channel')
        else:
            await message.channel.send(embed=discord.Embed(title="❌ 無法解析骰子指令", description=dice_part, color=0xff0000))
        return

    # 算式計算（無點）
    has_operator = re.search(r'[+\-*/%]|[\*]{2}|//', clean_content)
    has_dice = re.search(r'\d+[Dd]\d+', clean_content)
    if has_operator or has_dice:
        result, replaced = safe_compute_with_dice(clean_content)
        if result is not None:
            embed = discord.Embed(title="📐 計算結果", description=f"{clean_content}\n= {result}", color=0x00aaff)
            embed.set_footer(text=message.author.display_name, icon_url=message.author.display_avatar.url)
            await message.channel.send(embed=embed)
            return

    await bot.process_commands(message)

if __name__ == "__main__":
    TOKEN = os.getenv('DISCORD_TOKEN')
    if not TOKEN:
        print("錯誤：找不到 DISCORD_TOKEN 環境變數。請在 Railway 設定 Variables 或在本機執行前設定環境變數。")
        exit(1)
    bot.run(TOKEN)