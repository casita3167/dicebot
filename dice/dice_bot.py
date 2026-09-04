"""CoC 七版 Discord 骰子機器人

檔案結構索引（由上而下）：
  1. 安全求值／訊息前處理（safe_eval、db 代換、骰子訊息判斷）
  2. 骰子核心（DiceResult、xDy／xBy／D66／xUy、多重骰組）
  3. CoC 七版檢定（coc_check、成長規則、PBTA、成長檢定 .dp）
  4. 持久化（JsonStore 與各 Manager、TableManager/MongoDB）
  5. 角色卡系統（解析、顯示、選單 UI、欄位調整）
  6. Bot 初始化與全域暫存狀態（pc_pending／init／chase／瘋狂檢定）
  7. 團務收尾 .save
  8. GM 判定與私訊/成長/瘋狂路由
  9. 各 roll handler（.cc／.p／.sc／.int／.calc／send_result）
 10. 角色卡建立／編輯／Google 試算表匯入
 11. 先攻 .init 與追逐 .chase
 12. handle_dot_command（所有 . 指令分派）
 13. 說明選單 .help（文案放在 help.md，開機讀入；分類→第一層／更多兩層）
 14. on_message 主入口
"""
import discord
from discord.ext import commands
import re
import random
import json
import os
import time
import csv
import aiohttp
from io import StringIO
from urllib.parse import quote as urlquote
from collections import defaultdict
from dotenv import load_dotenv
from pymongo import MongoClient

# ---------- 載入環境變數 ----------
load_dotenv()

# ---------- 安全求值函式 ----------
def safe_eval(expr_str: str) -> float:
    if re.search(r'[^0-9\s\+\-\*\/\(\)\.%]', expr_str):
        return None
    # 擋連續運算子（如 2++3、2*+3），但先把合法的 ** 與 // 拿掉再檢查，
    # 否則次方／整除會被誤擋；真的畸形的算式（如 2****3）最後 eval 會炸並回 None。
    stripped = expr_str.replace('**', '').replace('//', '')
    if re.search(r'[\+\-\*\/%]{2,}', stripped):
        return None
    try:
        allowed_globals = {
            '__builtins__': {},
            'abs': abs,
            'round': round,
        }
        result = eval(expr_str, allowed_globals, {})
        if isinstance(result, (int, float)):
            return result
        return None
    except Exception:
        return None

def safe_compute_with_dice(expr: str):
    def replace_dice(match):
        dice_expr = match.group(0)
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

    dice_pattern = re.compile(r'(?<![:<])(\d+[DBU]\d+[Ss]?(?:\s+\d+)?|D66[sn]?|\d+[Dd]\d+\+\d+[Dd]\d+)(?![:>])', re.I)
    replaced = dice_pattern.sub(replace_dice, expr)
    replaced = dice_pattern.sub(replace_dice, replaced)
    result = safe_eval(replaced)
    return result, replaced

def remove_discord_emoji(text: str) -> str:
    return re.sub(r'<a?:\w+:\d+>|:\w+:', '', text)

_DB_TOKEN_RE = re.compile(r'\+\s*db\b', re.I)
_ANY_DICE_RE = re.compile(r'\d+[dD]\d+')

def _resolve_active_db_string(message):
    """回傳 (db_signed_str, alias)；沒有啟用角色卡或角色卡沒有 DB 資料時回傳 (None, None)。
    db_signed_str 一定帶正負號，例如 '+1D6'、'-2'、'+0'。"""
    if not message.guild:
        return None, None
    guild_id, channel_id, user_id = message.guild.id, message.channel.id, message.author.id
    alias = pc_active_manager.get_active(guild_id, channel_id, user_id)
    if not alias:
        return None, None
    card = pc_card_manager.get_card(guild_id, user_id, alias)
    if not card or card.get('db') is None:
        return None, None
    db_raw = str(card['db']).strip()
    db_signed = db_raw if db_raw[:1] in '+-' else f'+{db_raw}'
    return db_signed, alias

def substitute_db_token(text, message):
    """
    認「+db」這個寫法，換成本頻道目前啟用角色卡的 DB 值，直接把「+db」整段換成 DB 本身
    帶的正負號＋數值（例如 '1d6+db' → '1d6-2' 或 '1d6+1D6'），不用括號、也不會出現雙重負號。
    只要整句話裡有出現任一個骰子項（如 1d6），"+db" 不需要緊接在骰子後面也會觸發，
    所以「1d6+1+db」「1d6 + 1d4 + 2 + db」這種在 +db 前面還夾了其他加減項的複雜寫法也都能正確代換。
    其他寫法（例如「1d4-db」或單獨一個 db，或整句話裡完全沒有骰子項）一律不處理，維持原樣。
    回傳 (處理後文字, 錯誤訊息或None)：
    - 沒有符合的 +db 寫法：原樣傳回，錯誤訊息為 None
    - 有符合寫法但本頻道沒有啟用角色卡（或角色卡沒有 DB 資料）：文字回傳 None，並附上錯誤訊息
    """
    if not _DB_TOKEN_RE.search(text) or not _ANY_DICE_RE.search(text):
        return text, None
    db_signed, alias = _resolve_active_db_string(message)
    if db_signed is None:
        return None, "訊息裡用了 `db`，但本頻道尚未啟用角色卡（或角色卡沒有 DB 資料）。請先用 `.pc` 叫出面板，按【啟用】選擇要使用的角色卡。"
    replaced = _DB_TOKEN_RE.sub(lambda m: db_signed, text)
    return replaced, None


# 骰子指令開頭的完整規則：骰子本體（含加減/保留丟棄/比較）之後，如果還有文字，
# 中間一定要有空白隔開才算合法骰子指令（例如「1d6 忠誠」可以，「3d6的話」不行——
# 後者是提到骰子的中文句子，不是要骰骰子）。looks_like_dice_or_math 跟
# split_dice_and_label 共用這份規則，避免兩邊標準不一致造成誤判。
_DICE_HEAD_LABEL_RE = re.compile(
    r'^(\d+[dDbBuU]\d+(?:[+\-]\d+(?:[dD]\d+)?)*(?:\s*(?:kh|kl|dh|dl)\d*)?(?:\s*[<>]=?\s*-?\d+)?|[Dd]66[sn]?)'
    r'(?:\s+(.+))?$',
    re.I
)

# 車卡等場合常見的「骰子 x 倍數」寫法：(3d6)5、(3d6)x5、(2d6+6)*5、3d6x5……
# 跟 _DICE_HEAD_LABEL_RE 分開一個規則，是因為隱含乘法（不寫運算子，直接接數字）
# 只有在骰子外面包了括號時才成立——沒括號的「3d6 5」是既有「骰子 說明文字」語法，
# 不能被吃成乘法，所以沒括號時一定要寫明確的 x 或 * 才算數。
_DICE_MULTIPLY_HEAD_RE = re.compile(
    r'^(\(\s*\d+[dD]\d+(?:[+\-]\d+)?\s*\)\s*(?:[xX*]\s*)?\d+'
    r'|\d+[dD]\d+(?:[+\-]\d+)?\s*[xX*]\s*\d+)'
    r'(?:\s+(.+))?$'
)

def looks_like_dice_or_math(text: str) -> bool:
    """
    只在以下情況回傳 True：
    1. 訊息開頭是骰子指令（如 2d6、1d6+3、3d6+1d4），
       後面可以接空白與任意說明文字（如 1d6 忠誠、2d6+1 魅力檢定），
       但骰子指令跟後面的文字之間一定要有空白，否則不算（如「3d6的話」不觸發）。
    2. 整條訊息是純數學算式（含有運算符且全部由數字/符號組成，不含中文）。
    純數字（如 123）不觸發。
    骰子指令嵌在文字中間（如「我今天1d6」）不觸發。
    """
    text = text.strip()
    if not text:
        return False

    # 情況1：骰子指令開頭（後面可以接任意說明，包含中文，但中間要有空白）
    if _DICE_HEAD_LABEL_RE.match(text) or _DICE_MULTIPLY_HEAD_RE.match(text):
        return True

    # 情況2以下：含有中文 → 不觸發
    if re.search(r'[\u4e00-\u9fff\u3000-\u303f\uff00-\uffef]', text):
        return False

    # 情況2：整條訊息是純數學算式（有運算符，且全由數字/符號組成）
    if re.match(r'^[0-9(]', text):
        allowed_chars = re.compile(r'^[0-9+\-*/%().\s]+$')
        if allowed_chars.match(text) and re.search(r'\d', text) and re.search(r'[+\-*/%]', text):
            return True

    return False


def split_dice_and_label(text: str):
    """
    將「骰子指令 說明文字」拆分為 (骰子部分, 說明文字)。
    例如：「1d6 忠誠」→ ('1d6', '忠誠')
          「2d6+1」 → ('2d6+1', '')
    跟 looks_like_dice_or_math 共用同一份規則，只要後者判定為 True，這裡就一定能
    成功拆分（不會落到「無法解析」的情況）。
    """
    text = text.strip()
    m = _DICE_HEAD_LABEL_RE.match(text)
    if m:
        dice_part = m.group(1).strip()
        label = (m.group(2) or '').strip()
        return dice_part, label
    m2 = _DICE_MULTIPLY_HEAD_RE.match(text)
    if m2:
        dice_part = m2.group(1).strip()
        label = (m2.group(2) or '').strip()
        return dice_part, label
    return text, ''

# ---------- 骰子核心 ----------
class DiceResult:
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
            if self.text:
                base = f"{self.raw_expr}： {self.text}\n{sum_rolls}[{rolls_str}]{self.arithmetic} = {self.total}"
            else:
                base = f"{self.raw_expr}： {sum_rolls}[{rolls_str}]{self.arithmetic} = {self.total}"
            return base
        if self.text:
            # 說明文字獨立第一行，結果在第二行
            header = f"{self.raw_expr}： {self.text}"
            if self.total is not None:
                result_line = f"{self.total}[{rolls_str}]"
            else:
                result_line = rolls_str
            base = f"{header}\n{result_line}"
        else:
            if self.total is not None:
                base = f"{self.raw_expr}： {self.total}[{rolls_str}]"
            else:
                base = f"{self.raw_expr}： {rolls_str}"
        if self.filtered_rolls is not None and len(self.filtered_rolls) > 0:
            filtered_str = ', '.join(map(str, self.filtered_rolls))
            base += f"\n符合條件：{filtered_str}"
        if self.success is not None:
            base += f" 成功數 {self.success}"
        return base

def roll_dice(sides):
    return random.randint(1, sides)

# 比較運算子對應表：供 dice_dy / dice_by 共用，避免重複的 if/elif 判斷
_COMPARISON_OPS = {
    '>': lambda r, v: r > v,
    '<': lambda r, v: r < v,
    '>=': lambda r, v: r >= v,
    '<=': lambda r, v: r <= v,
    '==': lambda r, v: r == v,
    '!=': lambda r, v: r != v,
}

def filter_by_comparison(rolls, comp_op, comp_val):
    """依比較運算子（>、<、>=、<=、==、!=）篩選骰子結果。
    回傳 (filtered_rolls, success_count)；沒有比較條件時回傳 (None, None)。"""
    if not comp_op:
        return None, None
    op_func = _COMPARISON_OPS.get(comp_op)
    if op_func is None:
        return None, None
    filtered = [r for r in rolls if op_func(r, comp_val)]
    return filtered, len(filtered)

def parse_modifiers(expr):
    mod_pattern = re.compile(r'(?:kh(\d*)|kl(\d*)|dh(\d*)|dl(\d*))$', re.I)
    mod_match = mod_pattern.search(expr)
    keep = None
    drop = None
    keep_low = False
    drop_low = False
    if mod_match:
        # group 是空字串代表「有打修飾詞但沒帶數字」（如 4d6kh），視為 1；
        # 之前用 truthy 判斷會把空字串當成沒匹配，導致修飾詞被吃掉卻不生效。
        if mod_match.group(1) is not None:
            keep = int(mod_match.group(1) or 1)
        elif mod_match.group(2) is not None:
            keep = int(mod_match.group(2) or 1)
            keep_low = True
        elif mod_match.group(3) is not None:
            drop = int(mod_match.group(3) or 1)
        elif mod_match.group(4) is not None:
            drop = int(mod_match.group(4) or 1)
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
        # dh（丟最大）→ 由大到小排、跳過前 drop 顆；dl（丟最小）→ 由小到大排
        sorted_rolls = sorted(rolls, reverse=not drop_low)
        rolls = sorted_rolls[drop:]
    sum_rolls = sum(rolls)
    total = sum_rolls
    arithmetic_part = ""

    dice_part = f"{count}D{sides}"
    if base_expr != dice_part and ('+' in base_expr or '-' in base_expr or '*' in base_expr or '/' in base_expr):
        if base_expr.startswith(dice_part):
            arithmetic_part = base_expr[len(dice_part):]
            full_arithmetic_expr = f"{sum_rolls}{arithmetic_part}"
            calc_total = safe_eval(full_arithmetic_expr)
            if calc_total is not None:
                total = calc_total
            else:
                return None

    filtered, success = filter_by_comparison(rolls, comp_op, comp_val)

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
        if rest[:1].upper() == 'D':
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
    filtered, success = filter_by_comparison(rolls, comp_op, comp_val)
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
    success = None
    if threshold is not None:
        success = sum(1 for r in all_rolls if r > threshold)
    return DiceResult(expr, all_rolls, total=total, success=success, details={})

# 統一乘號：讓玩家打 x／X 或 * 都當乘號看待。只在「數字或右括號」後面緊接著數字的 x/X 才轉換，
# 避免誤觸其他字母用途（骰子表達式裡沒有其他地方會出現這種「數字 x 數字」的組合）。
_MULTIPLY_X_RE = re.compile(r'(?<=[\d)])[xX](?=\d)')

def _normalize_multiply_symbol(expr):
    return _MULTIPLY_X_RE.sub('*', expr)

# 「括號骰子 + 外部倍數」：(3d6)5、(3d6)x5、(2d6+6)*5……常見於車卡等批次骰值場合。
# 括號內先算完（含裡面自己的加減），骰完的總和才乘以括號外的數字——
# 括號優先、乘除在加減之後，是我們要記住的順序規則；沒寫運算子時（如 (3d6)5）視為隱含乘法。
_PAREN_DICE_MULTIPLY_RE = re.compile(
    r'^\(\s*(?P<inner>\d+[Dd]\d+(?:[+\-]\d+)?)\s*\)\s*\*?\s*(?P<mult>\d+)$'
)

def parse_paren_dice_multiply(expr):
    m = _PAREN_DICE_MULTIPLY_RE.match(expr)
    if not m:
        return None
    inner_res = dice_dy(m.group('inner'))
    if inner_res is None or inner_res.total is None:
        return None
    mult = int(m.group('mult'))
    total = inner_res.total * mult
    # 顯示時乘號一律用 x：例如「9[3,6] x5 = 45」或「15[3,6]+6 x5 = 105」（括號內若有加減，
    # inner_res.arithmetic 已經算進 total 裡，這裡只是照順序把文字接上去給玩家看）。
    arithmetic = f"{inner_res.arithmetic or ''} x{mult}"
    return DiceResult(expr, inner_res.rolls, total, arithmetic=arithmetic)

def parse_dice_expression(expr):
    expr = expr.strip()
    # 計算用 normalized（x 轉成 *），但標題（raw_expr）保留玩家原本打的字，
    # 顯示乘號時再統一換回 x，讓輸入寫 x 或 * 都行、回覆一律看到 x。
    normalized = _normalize_multiply_symbol(expr)
    paren_res = parse_paren_dice_multiply(normalized)
    if paren_res is not None:
        paren_res.raw_expr = expr
        return paren_res
    m_d66 = re.match(r'^D66([sn]?)$', normalized, re.I)
    if m_d66:
        return dice_d66(m_d66.group(1).lower())
    if re.match(r'^\d+U\d+\s+\d+', normalized, re.I):
        return dice_uy(normalized)
    if re.match(r'^\d+B\d+', normalized, re.I):
        return dice_by(normalized)
    if re.match(r'^\d+D\d+', normalized, re.I):
        res = dice_dy(normalized)
        if res is not None:
            res.raw_expr = expr
            if res.arithmetic and '*' in res.arithmetic:
                res.arithmetic = res.arithmetic.replace('*', ' x')
        return res
    return None

def parse_multi_dice(expr):
    tokens = list(re.finditer(r'(?<![:<])([+-]?\s*\d+[Dd]\d+|[+-]?\s*\d+)(?![:>])', expr, re.I))
    if not tokens:
        return None
    has_dice = any(re.search(r'[Dd]', t.group()) for t in tokens)
    if not has_dice:
        return None
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
    """多重擲骰。回傳每一次的顯示字串清單；任一次無法解析則回傳 None。
    先試單一骰組（parse_dice_expression），失敗再退回多骰相加（parse_multi_dice），
    這樣 .N 也能吃 `1d6+1d10` 這種不同骰子相加的寫法，跟一般擲骰一致。"""
    times = min(times, 30)
    lines = []
    for _ in range(times):
        res = parse_dice_expression(dice_expr)
        if res:
            lines.append(res.format())
            continue
        multi = parse_multi_dice(dice_expr)
        if multi:
            _total, details = multi
            lines.append(details)
        else:
            return None
    return lines

# ---------- CoC 七版 ----------
def parse_range(s: str):
    """
    將 '1' 或 '1-5' 這類字串解析為 (low, high) 整數區間。
    解析失敗回傳 None。
    """
    s = s.strip()
    m = re.match(r'^(\d+)\s*-\s*(\d+)$', s)
    if m:
        low, high = int(m.group(1)), int(m.group(2))
        if low > high:
            low, high = high, low
        return (low, high)
    if s.isdigit():
        v = int(s)
        return (v, v)
    return None

def format_range(rng):
    """將 (low, high) 區間格式化為顯示字串：單一值顯示 'N'，範圍顯示 'low-high'。"""
    return f"{rng[0]}" if rng[0] == rng[1] else f"{rng[0]}-{rng[1]}"

def coc_check(skill_value, bonus_dice=0, crit_range=None, fumble_range=None):
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

    if crit_range:
        is_crit = crit_range[0] <= final_roll <= crit_range[1]
    else:
        is_crit = final_roll == 1

    if fumble_range:
        is_fumble = fumble_range[0] <= final_roll <= fumble_range[1]
    else:
        is_fumble = (final_roll == 100) or (skill_value < 50 and final_roll >= 96)

    if is_crit:
        level = "大成功"
    elif is_fumble:
        level = "大失敗"
    elif final_roll <= skill_value // 5:
        level = "極限成功"
    elif final_roll <= skill_value // 2:
        level = "困難成功"
    elif final_roll <= skill_value:
        level = "一般成功"
    else:
        level = "失敗"
    return final_roll, level, bonus_desc, rolls

# 成長檢定規則：大成功/極限成功/困難成功/一般成功都算「成功過」，可以在結團後用 .dp 成長
_GROWTH_SUCCESS_LEVELS = {"大成功", "極限成功", "困難成功", "一般成功"}

def is_growable_success(level):
    return level in _GROWTH_SUCCESS_LEVELS

# 這些屬性／技能無法透過擲骰成功進行成長（.dp 成長檢定），所以 .end 清單裡
# 不把它們的成功計入「可成長」，但大成功／大失敗次數仍照常記錄。
# SAN／理智：`.cc san` 只是拿目前 SAN 當技能值做判定，理智不會靠通過檢定成長，一併排除。
NON_GROWABLE_SKILLS = {
    "力量", "敏捷", "意志", "體質", "外貌", "教育", "體型", "智力",
    "靈感", "知識", "克蘇魯神話",
    "SAN", "san", "理智",
}

# cc/coc 加值骰、懲罰骰後綴對照表：供各處統一換算 bonus_dice，避免重複的 if/elif 判斷
_CC_BONUS_MAP = {
    'cc1': 1, 'coc1': 1,
    'cc2': 2, 'coc2': 2,
    'ccn': -1, 'ccn1': -1,
    'ccn2': -2,
}

def cc_bonus_dice(token):
    """依 cc/coc 後綴（cc1、cc2、ccn、ccn1、ccn2、coc1、coc2）換算 bonus_dice，其餘一律視為 0（普通擲骰）。"""
    return _CC_BONUS_MAP.get(token.lower(), 0)

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
    """把 SAN 損失之類的表達式擲成整數：支援純數字（`5`）、骰子（`1d6`）、
    骰子帶算式（`1d6+1`、`2d10-2`）。無法解析時回傳 0。"""
    expr = (expr or '').strip()
    res = parse_dice_expression(expr)
    if res is not None and res.total is not None:
        return int(res.total)
    try:
        return int(expr)
    except ValueError:
        return 0

# ---------- 成長檢定 ----------
def _growth_check_line(skill_name, skill_val):
    """單一技能的成長檢定（失敗才成長），回傳結果文字。"""
    growth_roll = random.randint(1, 100)
    if growth_roll > skill_val:
        increase = random.randint(1, 10)
        return f"{skill_name} ({skill_val}%) → 成長檢定 {growth_roll} 失敗，獲得成長 +{increase}%，新技能值 {skill_val+increase}"
    return f"{skill_name} ({skill_val}%) → 成長檢定 {growth_roll} 成功（或持平），未成長"

async def development_check(message, args):
    if not args:
        embed = discord.Embed(
            title="❌ 格式錯誤",
            description="請提供技能值與名稱，例如：`.dp 50 騎乘 60 鬥毆`\n已啟用角色卡時，也可以只打技能名稱，例如：`.dp 騎乘 鬥毆`，數值會自動代入卡上目前的技能值。",
            color=0xff0000,
        )
        await message.channel.send(embed=embed)
        return
    tokens = args.split()

    # 「技能值 技能名稱」成對格式：偶數個 token，且每個奇數位置（0, 2, 4...）都能解析成整數。
    is_manual_pairs = len(tokens) > 0 and len(tokens) % 2 == 0
    if is_manual_pairs:
        for i in range(0, len(tokens), 2):
            try:
                int(tokens[i])
            except ValueError:
                is_manual_pairs = False
                break

    if is_manual_pairs:
        results = []
        for i in range(0, len(tokens), 2):
            skill_val = int(tokens[i])
            skill_name = tokens[i+1]
            results.append(_growth_check_line(skill_name, skill_val))
        embed = discord.Embed(title="📈 成長檢定（失敗才成長）", color=0x00aaff)
        embed.description = "\n".join(results)
        embed.set_footer(text=message.author.display_name, icon_url=message.author.display_avatar.url)
        await message.channel.send(embed=embed)
        return

    # 純技能名稱格式：需要本頻道已啟用角色卡，逐一從卡上抓目前技能值。
    guild_id, channel_id, user_id = message.guild.id, message.channel.id, message.author.id
    active_alias, card, error_embed = _lookup_active_card(guild_id, channel_id, user_id)
    if error_embed:
        await message.channel.send(embed=error_embed)
        return

    results = []
    not_found = []
    for skill_name in tokens:
        if skill_name.lower() in ('luk', 'luck') or skill_name == '幸運':
            luck_val = card.get('luck')
            if luck_val is None:
                not_found.append(skill_name)
                continue
            results.append(_growth_check_line('幸運', luck_val))
            continue
        entry = find_pc_skill_entry(card, skill_name)
        if not entry:
            not_found.append(skill_name)
            continue
        _, _, matched_name, skill_val = entry
        results.append(_growth_check_line(matched_name, skill_val))

    if not results:
        embed = discord.Embed(
            title="❌ 角色卡上找不到這些技能",
            description="找不到：" + "、".join(not_found) + "\n請確認技能名稱，或改用 `.dp 技能值 技能名稱` 手動指定數值。",
            color=0xff0000,
        )
        await message.channel.send(embed=embed)
        return

    desc = "\n".join(results)
    if not_found:
        desc += "\n\n⚠️ 角色卡上找不到：" + "、".join(not_found)
    embed = discord.Embed(title="📈 成長檢定（失敗才成長）", color=0x00aaff)
    embed.description = desc
    embed.set_footer(text=f"{active_alias}／{message.author.display_name}", icon_url=message.author.display_avatar.url)
    await message.channel.send(embed=embed)

# ---------- JSON 持久化基底類別 ----------
class JsonStore:
    """簡易 JSON 檔案持久化基底類別，統一讀寫與錯誤處理邏輯。
    子類別可覆寫 _default_data()／_decode(raw)／_encode() 來客製化資料結構。
    （原本 GMManager／CmdManager 讀檔沒有做例外處理，檔案損毀時會直接讓機器人
    啟動失敗；這裡統一補上跟 CritRangeManager／ActiveGMManager 一致的容錯行為。）
    """
    def __init__(self, filename):
        self.filename = filename
        self.data = self._default_data()
        self.load()

    def _default_data(self):
        return {}

    def _decode(self, raw):
        return raw

    def _encode(self):
        return self.data

    def load(self):
        if not os.path.exists(self.filename):
            return
        try:
            with open(self.filename, 'r', encoding='utf-8') as f:
                raw = json.load(f)
            self.data = self._decode(raw)
        except Exception as e:
            print(f"⚠️ 讀取 {self.filename} 失敗，將以空白設定啟動：{e}")
            self.data = self._default_data()

    def save(self):
        with open(self.filename, 'w', encoding='utf-8') as f:
            json.dump(self._encode(), f, ensure_ascii=False, indent=2)

# ---------- GM 管理 ----------
class GMManager(JsonStore):
    """
    GM 名單以「頻道」為單位登記：`.drgm addgm` 只會把人加入目前這個頻道的名單，
    同一人可以在不同頻道各自登記（或不登記），不同頻道的名單彼此獨立，
    不再依賴 Discord 的頻道管理權限或手動綁定去判斷。
    """
    def __init__(self, filename='gm_data.json'):
        super().__init__(filename)  # key: "guild_id:channel_id" -> [{'user_id':.., 'alias':..}, ...]

    def _default_data(self):
        return defaultdict(list)

    def _decode(self, raw):
        return defaultdict(list, raw)

    def _encode(self):
        return dict(self.data)

    def _key(self, guild_id, channel_id):
        # 討論串視同母頻道（見 effective_channel_id）：頻道登記的 GM 在其討論串一樣是 GM
        return f"{guild_id}:{effective_channel_id(channel_id)}"
    def add_gm(self, guild_id, channel_id, user_id, alias=None):
        key = self._key(guild_id, channel_id)
        if not alias:
            alias = f"GM{len(self.data[key])+1}"
        self.data[key].append({'user_id': user_id, 'alias': alias})
        self.save()
    def remove_gm(self, guild_id, channel_id, index):
        key = self._key(guild_id, channel_id)
        if 0 <= index < len(self.data[key]):
            del self.data[key][index]
            self.save()
            return True
        return False
    def clear_gms(self, guild_id, channel_id):
        self.data[self._key(guild_id, channel_id)] = []
        self.save()
    def get_gms(self, guild_id, channel_id):
        return self.data[self._key(guild_id, channel_id)]
    def get_gm_users(self, guild_id, channel_id):
        return [gm['user_id'] for gm in self.get_gms(guild_id, channel_id)]
    def is_gm_anywhere_in_guild(self, guild_id, user_id):
        """判斷這個人是否為本伺服器「任何頻道」登記過的 GM，不限目前頻道。
        用於「GM 代管角色卡」這類跨頻道功能：只要在同伺服器任一頻道登記為 GM，就能對任何玩家動手。"""
        prefix = f"{guild_id}:"
        for key, gms in self.data.items():
            if key.startswith(prefix) and any(gm['user_id'] == user_id for gm in gms):
                return True
        return False

# ---------- 大成功/大失敗自訂範圍（每位 GM 各自設定） ----------
class CritRangeManager(JsonStore):
    def __init__(self, filename='crit_range_data.json'):
        super().__init__(filename)  # {guild_id: {user_id: {'crit': [..], 'fumble': [..]}}}

    def _default_data(self):
        return {}

    def _decode(self, raw):
        migrated = {}
        format_changed = False
        for g, users in raw.items():
            try:
                gid = int(g)
            except (TypeError, ValueError):
                format_changed = True
                continue
            # 舊版格式是每個伺服器共用一組設定：{'crit': [...], 'fumble': [...]}
            # 新版格式是每位 GM 各自一組：{user_id: {'crit': [...], 'fumble': [...]}}
            if isinstance(users, dict) and ('crit' in users or 'fumble' in users):
                format_changed = True
                continue
            try:
                migrated[gid] = {int(u): v for u, v in users.items()}
            except (TypeError, ValueError, AttributeError):
                format_changed = True
                continue
        if format_changed:
            print(f"⚠️ {self.filename} 內含舊版大成功/大失敗設定格式，已自動略過舊資料。請各位 GM 使用 `.drgm ran 大成功/大失敗` 重新設定一次。")
            self.data = migrated
            self.save()
        return migrated

    def _encode(self):
        return {str(g): {str(u): v for u, v in users.items()} for g, users in self.data.items()}

    def set_range(self, guild_id, user_id, crit_range, fumble_range):
        self.data.setdefault(guild_id, {})[user_id] = {'crit': list(crit_range), 'fumble': list(fumble_range)}
        self.save()
    def get_range(self, guild_id, user_id):
        entry = self.data.get(guild_id, {}).get(user_id)
        if not entry:
            return None, None
        return tuple(entry['crit']), tuple(entry['fumble'])
    def clear_range(self, guild_id, user_id):
        if guild_id in self.data and user_id in self.data[guild_id]:
            del self.data[guild_id][user_id]
            self.save()
            return True
        return False

# ---------- 成長紀錄頻道白名單（每位 GM 各自維護） ----------
class GrowthChannelWhitelist(JsonStore):
    """GM 指定「哪些頻道可以記錄成長」。每位 GM 各自一份清單（跟大成功/大失敗設定一樣以 user_id 分開），
    存 guild 層。判斷某頻道能不能記時取『所有 GM 清單的聯集』——實務上一個頻道只有一位主 GM，
    聯集只是保險，不會互相打架。

    重要：這份白名單刻意「不」經過 effective_channel_id 正規化，存的是原始的頻道／討論串 id。
    也就是說討論串要自己加進白名單才算，不會因為母頻道在清單上就跟著算——這是 GM 明確要的行為
    （母頻道記不記、跟某條討論串記不記，可以分開控制）。
    注意：這跟 growth_manager／pc_active_manager 用母頻道 id 當 key 是兩回事——
    白名單只是「這個頻道（或討論串）准不准記」的閘門；一旦准了、開始記之後，
    session 與角色卡啟用仍照原本『討論串併入母頻道』的規則走。
    """
    def __init__(self, filename='growth_channel_whitelist.json'):
        super().__init__(filename)  # {guild_id: {user_id: [channel_id, ...]}}

    def _default_data(self):
        return {}

    def _decode(self, raw):
        migrated = {}
        for g, users in raw.items():
            try:
                gid = int(g)
            except (TypeError, ValueError):
                continue
            try:
                migrated[gid] = {int(u): [int(c) for c in chans] for u, chans in users.items()}
            except (TypeError, ValueError, AttributeError):
                continue
        return migrated

    def _encode(self):
        return {str(g): {str(u): list(chans) for u, chans in users.items()} for g, users in self.data.items()}

    def add(self, guild_id, user_id, channel_id):
        """把頻道加進某 GM 的白名單。回傳 True＝新增成功，False＝原本就在清單裡。"""
        chans = self.data.setdefault(guild_id, {}).setdefault(user_id, [])
        if channel_id in chans:
            return False
        chans.append(channel_id)
        self.save()
        return True

    def remove(self, guild_id, user_id, channel_id):
        """把頻道移出某 GM 的白名單。回傳 True＝移除成功，False＝原本就不在清單裡。"""
        chans = self.data.get(guild_id, {}).get(user_id)
        if not chans or channel_id not in chans:
            return False
        chans.remove(channel_id)
        self.save()
        return True

    def clear(self, guild_id, user_id):
        """清空某 GM 的白名單。回傳被清掉的頻道數。"""
        chans = self.data.get(guild_id, {}).get(user_id)
        if not chans:
            return 0
        n = len(chans)
        self.data[guild_id][user_id] = []
        self.save()
        return n

    def get_channels(self, guild_id, user_id):
        """回傳某 GM 自己白名單裡的頻道 id 清單。"""
        return list(self.data.get(guild_id, {}).get(user_id, []))

    def is_guild_empty(self, guild_id):
        """整個伺服器有沒有任何 GM 設過白名單。
        （備用：成長紀錄的模式判斷已改為逐頻道看『本頻道 GM』，見 _channel_uses_strict_whitelist，
        目前不再用這個伺服器層級的判斷當閘門。）"""
        users = self.data.get(guild_id, {})
        return not any(chans for chans in users.values())

    def is_allowed(self, guild_id, channel_id):
        """這個頻道（原始 id，不正規化）在不在任何一位 GM 的白名單裡。"""
        users = self.data.get(guild_id, {})
        return any(channel_id in chans for chans in users.values())

    def is_allowed_by(self, guild_id, user_id, channel_id):
        """這個頻道在不在『指定這位 GM』自己的白名單裡（面板列『尚未加入』時用）。"""
        return channel_id in self.data.get(guild_id, {}).get(user_id, [])


# ---------- 同頻道登記多位 GM 時，指定套用哪位的大成功/大失敗設定 ----------
class ActiveGMManager(JsonStore):
    """
    一個頻道如果只登記了一位 GM，會自動套用他的大成功/大失敗設定，不需要額外指定。
    只有當同一頻道登記了兩位（以上）GM 時，才需要用 `.drgm ran bind` 從『這個頻道自己的名單』
    裡指定其中一位作為套用對象；`.drgm ran unbind` 可以解除指定。
    """
    def __init__(self, filename='channel_active_gm.json'):
        super().__init__(filename)  # {"guild_id:channel_id": gm_user_id}

    def _key(self, guild_id, channel_id):
        # 討論串視同母頻道（見 effective_channel_id）：頻道指定的判定範圍在其討論串一樣套用
        return f"{guild_id}:{effective_channel_id(channel_id)}"
    def set_active(self, guild_id, channel_id, gm_user_id):
        self.data[self._key(guild_id, channel_id)] = gm_user_id
        self.save()
    def clear_active(self, guild_id, channel_id):
        key = self._key(guild_id, channel_id)
        if key in self.data:
            del self.data[key]
            self.save()
            return True
        return False
    def get_active(self, guild_id, channel_id):
        return self.data.get(self._key(guild_id, channel_id))

class CmdManager(JsonStore):
    def __init__(self, filename='cmd_data.json'):
        super().__init__(filename)

    def _default_data(self):
        return defaultdict(dict)

    def _decode(self, raw):
        return defaultdict(dict, {int(k): v for k, v in raw.items()})

    def _encode(self):
        return {str(k): v for k, v in self.data.items()}

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

# ---------- NPC／怪物簡易卡（GM 專用，`.npc`） ----------
class NpcCardManager(JsonStore):
    """跟角色卡（PCCardManager）分開存放，故意做得很陽春：只有 HP、DB、任意技能／屬性數值三種欄位，
    不做角色卡那套匯入格式解析與欄位驗證。以 guild 層共用（不分頻道），比照 `.pc gm` 的精神——
    同伺服器內任一頻道登記過 GM 即可管理，方便同一份怪物清單在不同場次／頻道間重複使用。"""
    def __init__(self, filename='npc_card_data.json'):
        super().__init__(filename)  # {guild_id: {name: {'hp':int|None,'hp_max':int|None,'db':str|None,'skills':{name:int}}}}

    def _default_data(self):
        return {}

    def _decode(self, raw):
        return {int(g): npcs for g, npcs in raw.items()}

    def _encode(self):
        return {str(g): npcs for g, npcs in self.data.items()}

    def _guild(self, guild_id):
        return self.data.setdefault(guild_id, {})

    def get(self, guild_id, name):
        return self._guild(guild_id).get(name)

    def upsert(self, guild_id, name, hp=None, db=None, skills=None):
        """`.npc add`：整張建立或覆蓋。"""
        self._guild(guild_id)[name] = {'hp': hp, 'hp_max': hp, 'db': db, 'skills': dict(skills or {})}
        self.save()
        return self._guild(guild_id)[name]

    def merge(self, guild_id, name, hp=None, db=None, skills=None):
        """`.npc edit`：局部更新，只覆蓋有給的欄位；技能是合併（新增/覆寫單一技能），不是整組換掉。
        找不到卡片時回傳 None，讓呼叫端提示先用 `.npc` 面板新增。"""
        card = self._guild(guild_id).get(name)
        if not card:
            return None
        if hp is not None:
            card['hp'] = hp
            if card.get('hp_max') is None or hp > card['hp_max']:
                card['hp_max'] = hp
        if db is not None:
            card['db'] = db
        if skills:
            card.setdefault('skills', {}).update(skills)
        self.save()
        return card

    def delete(self, guild_id, name):
        if name in self._guild(guild_id):
            del self.data[guild_id][name]
            self.save()
            return True
        return False

    def list_names(self, guild_id):
        return list(self._guild(guild_id).keys())

    def adjust_hp(self, guild_id, name, num, is_relative):
        """回傳 (舊值, 新值)；找不到卡片回傳 (None, None)。"""
        card = self._guild(guild_id).get(name)
        if not card:
            return None, None
        old = card.get('hp') or 0
        new = (old + num) if is_relative else num
        card['hp'] = new
        self.save()
        return old, new

_NPC_FIELD_RE = re.compile(r'^(\S+?)=(\S+)$')

def _parse_npc_fields(tokens):
    """把 `.npc add/edit` 裡 `欄位=值` 這種 token 清單拆成 (hp, db, skills, 看不懂的原始 token 清單)。
    `HP=` 認得數字，`DB=` 原樣存字串（可以是骰子式如 +1D4），其餘 `技能=數字` 一律當技能／屬性。"""
    hp, db, skills, errors = None, None, {}, []
    for tok in tokens:
        m = _NPC_FIELD_RE.match(tok)
        if not m:
            errors.append(tok)
            continue
        key, val = m.group(1), m.group(2)
        key_lower = key.lower()
        if key_lower == 'hp':
            if not re.match(r'^-?\d+$', val):
                errors.append(tok)
                continue
            hp = int(val)
        elif key_lower == 'db':
            db = val
        else:
            if not re.match(r'^-?\d+$', val):
                errors.append(tok)
                continue
            skills[key] = int(val)
    return hp, db, skills, errors

def _format_npc_card(card):
    lines = []
    if card.get('hp') is not None:
        hp_max = card.get('hp_max')
        lines.append(f"HP：{card['hp']}" + (f" / {hp_max}" if hp_max is not None and hp_max != card['hp'] else ""))
    if card.get('db'):
        lines.append(f"DB：{card['db']}")
    skills = card.get('skills') or {}
    if skills:
        lines.append("技能：" + "、".join(f"{k} {v}%" for k, v in skills.items()))
    return "\n".join(lines) if lines else "（尚未填寫任何欄位）"

# `.npc form` 用的網頁版表單網址（純前端小工具，貼劇本自動辨識用，見 index.html）。
# 部署到 GitHub Pages 之類的靜態網站後，把網址換成你自己的。
NPC_FORM_URL = "https://casita3167.github.io/dicebot/npc_card_form/"

class NpcCardFormModal(discord.ui.Modal):
    """`.npc` 面板上按鈕跳出的 Discord 原生表單，取代原本的文字指令 `.npc add` / `.npc edit`。
    跟網頁版表單（index.html）分工：網頁版負責『貼劇本自動辨識』，這個 Modal 負責『人在 Discord 裡就手動填』。"""
    def __init__(self, guild_id, mode):
        super().__init__(title="➕ 建立/覆蓋 NPC 卡" if mode == 'add' else "✏️ 局部更新 NPC 卡")
        self.guild_id = guild_id
        self.mode = mode
        self.name_input = discord.ui.TextInput(label="名稱（不可有空白）", placeholder="例：淺瘋者", max_length=50)
        self.hp_input = discord.ui.TextInput(label="HP（留空可不填）", placeholder="例：15", required=False, max_length=10)
        self.db_input = discord.ui.TextInput(label="DB 傷害加值（留空可不填）", placeholder="例：+1D4", required=False, max_length=20)
        self.skills_input = discord.ui.TextInput(
            label="屬性／技能，一行一個「名稱=數值」",
            style=discord.TextStyle.paragraph,
            placeholder="鬥毆=50\n巨爪=60\n閃避=40",
            required=False,
            max_length=800,
        )
        for item in (self.name_input, self.hp_input, self.db_input, self.skills_input):
            self.add_item(item)

    async def on_submit(self, interaction: discord.Interaction):
        if not gm_manager.is_gm_anywhere_in_guild(self.guild_id, interaction.user.id):
            await interaction.response.send_message(embed=discord.Embed(title="❌ 僅限 GM 使用", description="請先在任一頻道用 `.drgm addgm` 登記為 GM。", color=0xff0000), ephemeral=True)
            return
        name = str(self.name_input.value or '').strip()
        if not name or re.search(r'\s', name):
            await interaction.response.send_message(embed=discord.Embed(title="❌ 名稱不可空白或含空格", color=0xff0000), ephemeral=True)
            return
        hp_raw = str(self.hp_input.value or '').strip()
        hp = None
        if hp_raw:
            if not re.match(r'^-?\d+$', hp_raw):
                await interaction.response.send_message(embed=discord.Embed(title="❌ HP 必須是整數", color=0xff0000), ephemeral=True)
                return
            hp = int(hp_raw)
        db = str(self.db_input.value or '').strip() or None
        tokens = str(self.skills_input.value or '').split()
        _, _, skills, errors = _parse_npc_fields(tokens)
        if errors:
            await interaction.response.send_message(embed=discord.Embed(title="❌ 技能欄位格式錯誤", description=f"看不懂：{'、'.join(errors)}\n格式必須是 `名稱=數值`（一行一個）。", color=0xff0000), ephemeral=True)
            return
        if self.mode == 'add':
            card = npc_card_manager.upsert(self.guild_id, name, hp=hp, db=db, skills=skills)
            title = f"✅ 已建立/覆蓋 NPC 卡：{name}"
        else:
            card = npc_card_manager.merge(self.guild_id, name, hp=hp, db=db, skills=skills)
            if not card:
                await interaction.response.send_message(embed=discord.Embed(title="❌ 找不到 NPC", description=f"「{name}」還沒建立，請改選「新增/覆蓋」。", color=0xff0000), ephemeral=True)
                return
            title = f"✅ 已更新 NPC 卡：{name}"
        await interaction.response.send_message(embed=discord.Embed(title=title, description=_format_npc_card(card), color=0x00aaff))

NPC_PAGE_SIZE = 25  # Discord 選單一次最多 25 個選項

class NpcPagedSelect(discord.ui.Select):
    """`.npc` 面板「🗑️ 刪除 NPC」／「🔍 查看 NPC」按鈕共用的分頁選單，只負責顯示「目前這一頁」的選項，
    實際的換頁跟按鈕都交給 NpcPagedSelectView 管理（照抄 PCPagedSelect 的分頁模式）。"""
    def __init__(self, view_ref, page_names):
        self.view_ref = view_ref
        options = [discord.SelectOption(label=name[:100], value=name[:100]) for name in page_names]
        placeholder = "選擇要刪除的 NPC…" if view_ref.mode == 'del' else "選擇要查看的 NPC…"
        super().__init__(placeholder=placeholder, options=options, min_values=1, max_values=1)

    async def callback(self, interaction: discord.Interaction):
        await self.view_ref.handle_select(interaction, self.values[0])

class NpcPagedNavButton(discord.ui.Button):
    """分頁用的「上一頁／下一頁」按鈕，只有超過 25 個 NPC 才會出現。"""
    def __init__(self, view_ref, direction):
        super().__init__(
            label="◀️ 上一頁" if direction < 0 else "▶️ 下一頁",
            style=discord.ButtonStyle.secondary,
            row=1,
        )
        self.view_ref = view_ref
        self.direction = direction

    async def callback(self, interaction: discord.Interaction):
        await self.view_ref.change_page(interaction, self.direction)

class NpcPagedSelectView(discord.ui.View):
    """`.npc` 面板「🗑️ 刪除 NPC」（mode='del'）／「🔍 查看 NPC」（mode='show'）共用：
    NPC 數量在 25 個以內只顯示單一選單，超過會自動分頁。NPC 清單是 guild 共用（不分玩家），
    所以不像角色卡選單要分 user_id／actor_id，只需要 actor_id 防止別人手滑動到別人叫出來的選單；
    mode='del' 的 GM 身分檢查刻意留到選到人之後才做第二次（按鈕那關已經擋過一次），
    避免選單開著的這段時間 GM 身分被收回卻沒即時擋下來。"""
    def __init__(self, mode, guild_id, actor_id, names):
        super().__init__(timeout=60)
        self.mode = mode
        self.guild_id = guild_id
        self.actor_id = actor_id
        self.names = names
        self.page = 0
        self._rebuild()

    @property
    def total_pages(self):
        return max(1, (len(self.names) - 1) // NPC_PAGE_SIZE + 1)

    def _rebuild(self):
        self.clear_items()
        start = self.page * NPC_PAGE_SIZE
        self.add_item(NpcPagedSelect(self, self.names[start:start + NPC_PAGE_SIZE]))
        if self.total_pages > 1:
            prev_btn = NpcPagedNavButton(self, -1)
            next_btn = NpcPagedNavButton(self, 1)
            prev_btn.disabled = (self.page <= 0)
            next_btn.disabled = (self.page >= self.total_pages - 1)
            self.add_item(prev_btn)
            self.add_item(next_btn)

    def make_embed(self):
        title = "🗑️ 刪除 NPC" if self.mode == 'del' else "🔍 查看 NPC"
        desc = "請選擇 NPC："
        if self.total_pages > 1:
            desc += f"（第 {self.page + 1}／{self.total_pages} 頁，共 {len(self.names)} 個）"
        return discord.Embed(title=title, description=desc, color=0x00aaff)

    async def _check_actor(self, interaction):
        if interaction.user.id != self.actor_id:
            await interaction.response.send_message("這不是你叫出來的選單喔，請自己打 `.npc` 開啟面板操作。", ephemeral=True)
            return False
        return True

    async def change_page(self, interaction: discord.Interaction, direction):
        if not await self._check_actor(interaction):
            return
        self.page = max(0, min(self.total_pages - 1, self.page + direction))
        self._rebuild()
        await interaction.response.edit_message(embed=self.make_embed(), view=self)

    async def handle_select(self, interaction: discord.Interaction, name):
        if not await self._check_actor(interaction):
            return
        card = npc_card_manager.get(self.guild_id, name)
        if not card:
            await interaction.response.edit_message(embed=discord.Embed(title="❌ 這張 NPC 卡已經不存在了", color=0xff0000), view=None)
            return
        if self.mode == 'del':
            if not gm_manager.is_gm_anywhere_in_guild(self.guild_id, interaction.user.id):
                await interaction.response.send_message(embed=discord.Embed(title="❌ 僅限 GM 使用", description="請先在任一頻道用 `.drgm addgm` 登記為 GM。", color=0xff0000), ephemeral=True)
                return
            npc_card_manager.delete(self.guild_id, name)
            await interaction.response.edit_message(embed=discord.Embed(title="✅ 已刪除 NPC 卡", description=name, color=0x00aaff), view=None)
        else:  # 'show'
            await interaction.response.edit_message(embed=discord.Embed(title=f"🗒️ {name}", description=_format_npc_card(card), color=0x00aaff), view=None)

class NpcFormView(discord.ui.View):
    """`.npc form` 回傳的面板：連到網頁版表單的連結按鈕，加四個直接跳 Discord 互動元件的按鈕。"""
    def __init__(self, guild_id):
        super().__init__(timeout=300)
        self.guild_id = guild_id
        self.add_item(discord.ui.Button(label="📝 開啟網頁表單（可貼劇本自動辨識）", style=discord.ButtonStyle.link, url=NPC_FORM_URL))

    @discord.ui.button(label="➕ 新增/覆蓋 NPC", style=discord.ButtonStyle.primary)
    async def add_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not gm_manager.is_gm_anywhere_in_guild(self.guild_id, interaction.user.id):
            await interaction.response.send_message(embed=discord.Embed(title="❌ 僅限 GM 使用", description="請先在任一頻道用 `.drgm addgm` 登記為 GM。", color=0xff0000), ephemeral=True)
            return
        await interaction.response.send_modal(NpcCardFormModal(self.guild_id, 'add'))

    @discord.ui.button(label="✏️ 局部更新 NPC", style=discord.ButtonStyle.secondary)
    async def edit_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not gm_manager.is_gm_anywhere_in_guild(self.guild_id, interaction.user.id):
            await interaction.response.send_message(embed=discord.Embed(title="❌ 僅限 GM 使用", description="請先在任一頻道用 `.drgm addgm` 登記為 GM。", color=0xff0000), ephemeral=True)
            return
        await interaction.response.send_modal(NpcCardFormModal(self.guild_id, 'edit'))

    @discord.ui.button(label="🔍 查看 NPC", style=discord.ButtonStyle.secondary)
    async def show_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        names = npc_card_manager.list_names(self.guild_id)
        if not names:
            await interaction.response.send_message(embed=discord.Embed(title="❌ 目前沒有任何 NPC 卡", color=0xff0000), ephemeral=True)
            return
        view = NpcPagedSelectView('show', self.guild_id, interaction.user.id, names)
        await interaction.response.send_message(embed=view.make_embed(), view=view, ephemeral=True)

    @discord.ui.button(label="🗑️ 刪除 NPC", style=discord.ButtonStyle.danger)
    async def del_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not gm_manager.is_gm_anywhere_in_guild(self.guild_id, interaction.user.id):
            await interaction.response.send_message(embed=discord.Embed(title="❌ 僅限 GM 使用", description="請先在任一頻道用 `.drgm addgm` 登記為 GM。", color=0xff0000), ephemeral=True)
            return
        names = npc_card_manager.list_names(self.guild_id)
        if not names:
            await interaction.response.send_message(embed=discord.Embed(title="❌ 目前沒有任何 NPC 卡", color=0xff0000), ephemeral=True)
            return
        view = NpcPagedSelectView('del', self.guild_id, interaction.user.id, names)
        await interaction.response.send_message(embed=view.make_embed(), view=view, ephemeral=True)

# ---------- 結團成長紀錄 ----------
def _channel_uses_strict_whitelist(guild_id, channel_id):
    """這個頻道要走『嚴格白名單模式』還是『自動模式』。

    只看『本頻道登記的 GM』：只要其中任一位 GM 設過（非空）白名單，這個頻道就走嚴格模式——
    照白名單決定記不記（頻道不在名單內＝視為 GM 明確排除，不記）。
    頻道沒有 GM、或這些 GM 都沒設過白名單 → 自動模式（玩家自己啟用角色卡或 `.start` 才記，
    且只記本人；沒人開卡／沒人 .start 的頻道自然不會有紀錄）。

    刻意「只看本頻道的 GM」而不是看整個伺服器：這樣『沒有 GM 的頻道』不會被別團 GM 在別的
    頻道設的白名單連坐關掉，符合「沒 GM 就自動記」的需求。GM 名單沿用母頻道正規化
    （見 gm_manager._key），所以討論串跟著它母頻道的 GM 判斷。
    定義成獨立函式（而非寫死在 manager 裡）是因為 gm_manager／whitelist 物件在檔案較後面
    才建立，這裡在呼叫時（執行期）才參照到它們。"""
    gm_users = gm_manager.get_gm_users(guild_id, channel_id)
    return any(growth_channel_whitelist.get_channels(guild_id, u) for u in gm_users)


def _growth_recording_open(guild_id, channel_id):
    """成長紀錄是否『仍在累加』（除了要有進行中的 session，由各 record_* 自行檢查）。
    - 嚴格模式（本頻道 GM 設了白名單）：這個頻道要在白名單裡才繼續累加，否則停止累加
      （已記錄的內容保留）。用原始 channel_id 查，討論串各自算。
    - 自動模式（本頻道沒 GM，或 GM 沒設白名單）：開放累加；真正的閘門是各 record_* 都要求
      該使用者有進行中的 session（由 `.start` 或啟用角色卡建立），所以只有『自己開卡或 .start』
      的玩家才會被記，且只記本人。
    定義成獨立函式而非寫死在 manager 裡，是因為相關物件在檔案較後面才建立，
    這裡在呼叫時（執行期）才參照到它。"""
    if _channel_uses_strict_whitelist(guild_id, channel_id):
        return growth_channel_whitelist.is_allowed(guild_id, channel_id)
    return True


class GrowthManager(JsonStore):
    """
    以「使用者 + 頻道」為單位記錄一段 `.start`～`.end` 期間內、該使用者自己做過的
    技能檢定結果，方便結團時列出「這次哪些技能成功過、可以拿去 `.dp` 成長」。
    只記錄下指令的人自己，且限定在同一個頻道；不會記錄其他人的檢定。
    只計算「一般頻道可見、不帶獎勵/懲罰骰」的檢定：暗骰（dr/ddr/dddr）跟
    cc1/cc2/ccn1/ccn2 這類獎勵骰、懲罰骰檢定都不列入計算。
    結果本身也有篩選：只記錄「成功、大成功、大失敗」，普通的「失敗」不記錄。
    """
    def __init__(self, filename='growth_data.json'):
        super().__init__(filename)  # key: "guild:channel:user" -> {'skills': {name: {...}}, 'unnamed': {...}}

    def _default_data(self):
        return {}

    def _key(self, guild_id, channel_id, user_id):
        # 討論串視同母頻道（見 effective_channel_id）：在母頻道 .start 後於討論串擲骰一樣會記錄
        return f"{guild_id}:{effective_channel_id(channel_id)}:{user_id}"

    def is_active(self, guild_id, channel_id, user_id):
        return self._key(guild_id, channel_id, user_id) in self.data

    def start_session(self, guild_id, channel_id, user_id):
        self.data[self._key(guild_id, channel_id, user_id)] = {
            'skills': {},
            'unnamed': {'count': 0, 'links': []},
            'san_loss': {'total': 0, 'entries': []},
            'adjustments': [],
            'madness': {'entries': []},
        }
        self.save()

    def record_check(self, guild_id, channel_id, user_id, skill_name, skill_value, level):
        """記錄一次有填技能名稱的檢定；只有在該使用者於本頻道有進行中的紀錄時才會生效。
        呼叫端（maybe_record_growth）已保證只有成功／大成功／大失敗才會呼叫到這裡。"""
        session = self.data.get(self._key(guild_id, channel_id, user_id))
        if session is None:
            return
        # 頻道中途被移出白名單（或白名單被清空）後停止累加，已記錄的保留
        if not _growth_recording_open(guild_id, channel_id):
            return
        entry = session['skills'].setdefault(skill_name, {
            'success': False, 'total': 0,
            'crit_count': 0, 'fumble_count': 0,
            'last_skill_value': skill_value,
        })
        entry['total'] += 1
        entry['last_skill_value'] = skill_value
        if level == '大成功':
            entry['crit_count'] += 1
        elif level == '大失敗':
            entry['fumble_count'] += 1
        # 力量/敏捷/意志/體質/外貌/教育/體型/智力/靈感/知識/克蘇魯神話等屬性
        # 不能透過擲骰成功進行成長，所以不標記為「可成長」；大成功/大失敗次數仍照常記錄在上面。
        if is_growable_success(level) and skill_name not in NON_GROWABLE_SKILLS:
            entry['success'] = True
        self.save()

    def record_unnamed_check(self, guild_id, channel_id, user_id, link):
        """記錄一次沒有填技能名稱的檢定：只累計次數，並保留訊息連結方便事後回頭辨認是哪個技能。"""
        session = self.data.get(self._key(guild_id, channel_id, user_id))
        if session is None:
            return
        # 頻道中途被移出白名單（或白名單被清空）後停止累加，已記錄的保留
        if not _growth_recording_open(guild_id, channel_id):
            return
        unnamed = session.setdefault('unnamed', {'count': 0, 'links': []})
        unnamed['count'] += 1
        unnamed['links'].append(link)
        self.save()

    def record_san_loss(self, guild_id, channel_id, user_id, alias, roll, success, loss, new_san, link):
        """記錄一次 SAN 檢定造成的理智損失；只有在該使用者於本頻道有進行中的紀錄時才會生效。
        舊資料可能沒有 'san_loss' 欄位，用 setdefault 補上，避免對舊紀錄操作時出錯。"""
        session = self.data.get(self._key(guild_id, channel_id, user_id))
        if session is None:
            return
        # 頻道中途被移出白名單（或白名單被清空）後停止累加，已記錄的保留
        if not _growth_recording_open(guild_id, channel_id):
            return
        san_loss = session.setdefault('san_loss', {'total': 0, 'entries': []})
        san_loss['total'] += loss
        san_loss['entries'].append({
            'alias': alias, 'roll': roll, 'success': success,
            'loss': loss, 'new_san': new_san, 'link': link,
        })
        self.save()

    def record_madness(self, guild_id, channel_id, user_id, alias, san_loss, int_value, roll, level, link):
        """記錄一次「單次損失超過5點SAN後，智力檢定成功、角色陷入瘋狂」事件；
        只有在該使用者於本頻道有進行中的紀錄時才會生效。
        舊資料可能沒有 'madness' 欄位，用 setdefault 補上，避免對舊紀錄操作時出錯。"""
        session = self.data.get(self._key(guild_id, channel_id, user_id))
        if session is None:
            return
        # 頻道中途被移出白名單（或白名單被清空）後停止累加，已記錄的保留
        if not _growth_recording_open(guild_id, channel_id):
            return
        madness = session.setdefault('madness', {'entries': []})
        madness['entries'].append({
            'alias': alias, 'san_loss': san_loss, 'int_value': int_value,
            'roll': roll, 'level': level, 'link': link,
        })
        self.save()

    def record_adjustment(self, guild_id, channel_id, user_id, alias, field_name, old_val, new_val, is_relative, num):
        """記錄一次 `.pc adj` 造成的欄位/技能增減；只有在該使用者於本頻道有進行中的紀錄時才會生效。
        舊資料可能沒有 'adjustments' 欄位，用 setdefault 補上，避免對舊紀錄操作時出錯。"""
        session = self.data.get(self._key(guild_id, channel_id, user_id))
        if session is None:
            return
        # 頻道中途被移出白名單（或白名單被清空）後停止累加，已記錄的保留
        if not _growth_recording_open(guild_id, channel_id):
            return
        adjustments = session.setdefault('adjustments', [])
        adjustments.append({
            'alias': alias, 'field': field_name,
            'old': old_val, 'new': new_val,
            'is_relative': is_relative, 'num': num,
        })
        self.save()

    def end_session(self, guild_id, channel_id, user_id):
        """結束紀錄並回傳這段期間的 {'skills':..., 'unnamed':...}；沒有進行中的紀錄則回傳 None。"""
        session = self.data.pop(self._key(guild_id, channel_id, user_id), None)
        if session is not None:
            self.save()
            return session
        return None

# ---------- 角色卡 ----------
class PCCardManager(JsonStore):
    """
    角色卡以「伺服器 + 使用者 + 角色名稱」為單位儲存，同一人可以存多張角色卡（不同角色名稱）。
    資料透過 `.pc` 貼上文字後自動解析（見 parse_pc_card_text），存成結構化欄位方便之後查詢/顯示。
    """
    def __init__(self, filename='pc_card_data.json'):
        super().__init__(filename)  # {guild_id: {user_id: {alias: card_dict}}}

    def _default_data(self):
        return {}

    def _decode(self, raw):
        return raw

    def _encode(self):
        return self.data

    def get_all(self, guild_id, user_id):
        return self.data.get(str(guild_id), {}).get(str(user_id), {})

    def get_card(self, guild_id, user_id, alias):
        return self.data.get(str(guild_id), {}).get(str(user_id), {}).get(alias)

    def save_card(self, guild_id, user_id, alias, card):
        gid, uid = str(guild_id), str(user_id)
        self.data.setdefault(gid, {}).setdefault(uid, {})[alias] = card
        self.save()

    def delete_card(self, guild_id, user_id, alias):
        gid, uid = str(guild_id), str(user_id)
        try:
            del self.data[gid][uid][alias]
            self.save()
            return True
        except KeyError:
            return False

    def find_card_by_alias_in_guild(self, guild_id, alias):
        """跨玩家搜尋：在整個伺服器裡找『角色名稱剛好是這個』的角色卡，不管是哪個 Discord 使用者存的。
        用在 GM 操作追逐時，只靠角色名稱就能自動拉角色卡數值（例如MOV），不用知道是哪個玩家的帳號。
        先比對完全相符；比對不到再忽略空白/符號比對一次。回傳 [(user_id, alias, card), ...]，可能有多筆（同名）。"""
        guild_data = self.data.get(str(guild_id), {})
        matches = [(uid, alias, cards[alias]) for uid, cards in guild_data.items() if alias in cards]
        if matches:
            return matches
        norm_target = _normalize_for_match(alias)
        for uid, cards in guild_data.items():
            for a, card in cards.items():
                if _normalize_for_match(a) == norm_target:
                    matches.append((uid, a, card))
        return matches

# 解析角色卡貼上文字用的正規化與欄位擷取
_PC_ATTR_LABELS = ['力量', '敏捷', '意志', '體質', '外貌', '教育', '體型', '智力']

def normalize_pc_card_text(text):
    """把全形符號轉半形，方便統一用同一套正規表達式解析（不影響技能名稱裡的中文字）。"""
    trans = str.maketrans({
        '：': ':', '／': '/', '（': '(', '）': ')', '，': ',', '　': ' ',
        '＋': '+', '－': '-',
    })
    return text.translate(trans)

def parse_pc_card_text(raw_text):
    """
    解析類似以下格式的角色卡文字（對應使用者試算表公式輸出的格式）：
        角色名稱：XXX
        HP：0／0 MP：0／0
        SAN：0／(0) LUK：0
        力量：0 敏捷：0 意志：0
        體質：0 外貌：0 教育：0
        體型：0 智力：0 靈感：0
        體格：-2
        DB：-2 MOV：8
        [技能列表]
        偵查：25
        [戰鬥列表]
        鬥毆：25
        [技能]
        拉丁文-語言：25
    找不到的欄位會是 None／空清單，不會噴錯。
    """
    # 試算表複製多行儲存格時，常會整段被包上一層雙引號（例如 "角色名稱：...二-漢文：35"），
    # 這裡先把最外層的引號拆掉，避免「角色名稱：」那一行比對不到而變成「未命名角色」。
    text = raw_text.strip()
    if len(text) >= 2 and text[0] == '"' and text[-1] == '"':
        text = text[1:-1]
    text = text.replace('""', '"')  # Excel/試算表用兩個雙引號表示一個字面上的雙引號

    text = normalize_pc_card_text(text)
    lines = [l.strip() for l in text.splitlines()]

    data = {
        'name': None,
        'hp_cur': None, 'hp_max': None,
        'mp_cur': None, 'mp_max': None,
        'san_cur': None, 'san_max': None,
        'luck': None, 'idea': None,
        'attributes': {},
        'build': None, 'db': None, 'mov': None,
        'skills': [], 'combat': [], 'extra_skills': [],
    }

    section = None
    for line in lines:
        if not line:
            continue
        header_m = re.match(r'^\[(.+)\]$', line)
        if header_m:
            header = header_m.group(1)
            if '技能列表' in header:
                section = 'skills'
            elif '戰鬥列表' in header:
                section = 'combat'
            elif header == '技能':
                section = 'extra'
            else:
                section = None
            continue

        if section is not None:
            parts = line.split(':', 1)
            if len(parts) == 2:
                sk_name = parts[0].strip()
                sk_val_raw = parts[1].strip()
                try:
                    sk_val = int(sk_val_raw)
                except ValueError:
                    sk_val = sk_val_raw
                if sk_name:
                    target = {'skills': data['skills'], 'combat': data['combat'], 'extra': data['extra_skills']}[section]
                    target.append((sk_name, sk_val))
            continue

        m = re.match(r'^角色名稱\s*:\s*(.+)$', line)
        if m:
            data['name'] = m.group(1).strip()

        m = re.search(r'\bHP\s*:\s*(-?\d+)\s*/\s*(-?\d+)', line, re.I)
        if m:
            data['hp_cur'], data['hp_max'] = int(m.group(1)), int(m.group(2))

        m = re.search(r'\bMP\s*:\s*(-?\d+)\s*/\s*(-?\d+)', line, re.I)
        if m:
            data['mp_cur'], data['mp_max'] = int(m.group(1)), int(m.group(2))

        m = re.search(r'\bSAN\s*:\s*(-?\d+)\s*/\s*\(*(-?\d+)\)*', line, re.I)
        if m:
            data['san_cur'], data['san_max'] = int(m.group(1)), int(m.group(2))

        m = re.search(r'\bLUK\s*:\s*(-?\d+)', line, re.I)
        if m:
            data['luck'] = int(m.group(1))

        m = re.search(r'靈感\s*:\s*(-?\d+)', line)
        if m:
            data['idea'] = int(m.group(1))

        for label in _PC_ATTR_LABELS:
            am = re.search(rf'{label}\s*:\s*(-?\d+)', line)
            if am:
                data['attributes'][label] = int(am.group(1))

        m = re.search(r'體格\s*:\s*(-?\d+)', line)
        if m:
            data['build'] = int(m.group(1))

        m = re.search(r'\bDB\s*:\s*([+\-]?[\w\d]+)', line, re.I)
        if m:
            data['db'] = m.group(1)

        m = re.search(r'\bMOV\s*:\s*(-?\d+)', line, re.I)
        if m:
            data['mov'] = int(m.group(1))

    return data

def pc_card_has_content(card):
    """判斷解析結果是否「至少抓到一些東西」，避免把完全不相關的訊息誤存成空白角色卡。"""
    if card is None:
        return False
    if card['name'] or card['skills'] or card['combat'] or card['extra_skills']:
        return True
    if card['hp_max'] is not None or card['san_max'] is not None or card['attributes']:
        return True
    return False

def format_pc_card_embed(card, alias, author):
    def g(v):
        return v if v is not None else '?'
    attrs = card.get('attributes', {})
    def a(k):
        return attrs.get(k, '?')

    name_line = card.get('name') or alias
    header_lines = [
        f"角色名稱：**{pc_display_label(alias, card)}**",
        f"HP：{g(card['hp_cur'])}／{g(card['hp_max'])}　MP：{g(card['mp_cur'])}／{g(card['mp_max'])}",
        f"SAN：{g(card['san_cur'])}／({g(card['san_max'])})　LUK：{g(card['luck'])}",
        f"力量：{a('力量')} 敏捷：{a('敏捷')} 意志：{a('意志')}",
        f"體質：{a('體質')} 外貌：{a('外貌')} 教育：{a('教育')}",
        f"體型：{a('體型')} 智力：{a('智力')} 靈感：{g(card['idea'])}",
        f"體格：{g(card['build'])}　DB：{g(card['db'])}　MOV：{g(card['mov'])}",
    ]

    embed = discord.Embed(title=f"🗂️ {name_line}", description="\n".join(header_lines), color=0x00aaff)

    def add_list_field(title, items):
        if not items:
            return
        lines = [f"{n}：{v}" for n, v in items]
        chunk, length, part = [], 0, 1
        for line in lines:
            if length + len(line) + 1 > 1000:
                embed.add_field(name=title if part == 1 else f"{title}（續{part}）", value="\n".join(chunk), inline=False)
                chunk, length = [], 0
                part += 1
            chunk.append(line)
            length += len(line) + 1
        if chunk:
            embed.add_field(name=title if part == 1 else f"{title}（續{part}）", value="\n".join(chunk), inline=False)

    add_list_field("🎯 技能列表", card.get('skills'))
    add_list_field("⚔️ 戰鬥列表", card.get('combat'))
    add_list_field("🛠️ 技能", card.get('extra_skills'))

    embed.set_footer(text=author.display_name, icon_url=author.display_avatar.url)
    return embed

def format_pc_quick_status(card, alias, author):
    """`.data` 用的簡易角色卡摘要：角色名稱、HP、MP、SAN、LUK。"""
    def g(v):
        return v if v is not None else '?'
    desc = (
        f"**{pc_display_label(alias, card)}**\n"
        f"❤️ HP：{g(card['hp_cur'])}／{g(card['hp_max'])}\n"
        f"🔵 MP：{g(card['mp_cur'])}／{g(card['mp_max'])}\n"
        f"🧠 SAN：{g(card['san_cur'])}／({g(card['san_max'])})\n"
        f"🍀 LUK：{g(card['luck'])}"
    )
    embed = discord.Embed(title="📇 角色狀態", description=desc, color=0x00aaff)
    embed.set_footer(text=author.display_name, icon_url=author.display_avatar.url)
    return embed

# 「本頻道目前啟用中角色卡」：{"guild:channel:user": alias}
# 用 `.pc 角色名稱` 啟用；換頻道要重新啟用（跟角色卡本身的儲存無關，儲存不分頻道）。
class PCActiveManager(JsonStore):
    def __init__(self, filename='pc_active_data.json'):
        super().__init__(filename)

    def _default_data(self):
        return {}

    def _key(self, guild_id, channel_id, user_id):
        # 討論串視同母頻道（見 effective_channel_id）：在頻道啟用的卡，於其討論串一樣生效
        return f"{guild_id}:{effective_channel_id(channel_id)}:{user_id}"

    def set_active(self, guild_id, channel_id, user_id, alias):
        self.data[self._key(guild_id, channel_id, user_id)] = alias
        self.save()

    def get_active(self, guild_id, channel_id, user_id):
        return self.data.get(self._key(guild_id, channel_id, user_id))

    def clear_active(self, guild_id, channel_id, user_id):
        key = self._key(guild_id, channel_id, user_id)
        if key in self.data:
            del self.data[key]
            self.save()
            return True
        return False

    def get_all_active_in_channel(self, guild_id, channel_id):
        """回傳這個頻道目前所有『有啟用角色卡』的使用者：[(user_id, alias), ...]。
        用在追逐等功能，列出『頻道內有開卡的人』給 GM 從選單勾選，不用手動打字輸入名字。"""
        prefix = f"{guild_id}:{effective_channel_id(channel_id)}:"
        result = []
        for key, alias in self.data.items():
            if key.startswith(prefix):
                try:
                    user_id = int(key[len(prefix):])
                except ValueError:
                    continue
                result.append((user_id, alias))
        return result

def _normalize_for_match(s):
    """忽略空白與符號，只留下文字/數字本身，方便『葉山 蒼真』跟『葉山蒼真』視為同一個名稱。"""
    return re.sub(r'\W+', '', s or '')

def pc_display_label(alias, card):
    """角色名稱一律等於角色卡的代稱（key），只有極少數舊資料（用 edit 覆蓋過、新舊角色名稱不同）才會不一樣，
    這時額外附註原本角色卡裡的角色名稱，避免混淆。"""
    name = card.get('name') if card else None
    if not name or name == alias:
        return alias
    return f"{alias}（角色卡內角色名稱：{name}）"

def resolve_pc_alias(guild_id, user_id, text):
    """依輸入文字找角色卡：先比對角色名稱是否完全相符，找不到再忽略空白/符號比對一次。
    回傳 (alias, card)；找不到回傳 (None, None)。"""
    card = pc_card_manager.get_card(guild_id, user_id, text)
    if card:
        return text, card
    target_norm = _normalize_for_match(text)
    if target_norm:
        for a, c in pc_card_manager.get_all(guild_id, user_id).items():
            if _normalize_for_match(a) == target_norm or _normalize_for_match(c.get('name') or '') == target_norm:
                return a, c
    return None, None

def fuzzy_find_pc_cards(guild_id, user_id, text):
    """在『完全相符／忽略符號完全相符』（resolve_pc_alias）都找不到時，用『部分包含』再找一次
    （例如輸入「葉山」可以比對到角色名稱是「葉山蒼真」的卡）。
    回傳符合的 [(alias, card), ...] 清單（可能有 0、1 或多筆，由呼叫端決定要不要讓玩家選）。"""
    query_norm = _normalize_for_match(text)
    if not query_norm:
        return []
    matches = []
    for a, c in pc_card_manager.get_all(guild_id, user_id).items():
        name_norm = _normalize_for_match(c.get('name') or '')
        if query_norm in _normalize_for_match(a) or (name_norm and query_norm in name_norm):
            matches.append((a, c))
    return matches

def fuzzy_match_skill(skill_lookup, query):
    """在角色卡的技能對照表裡找符合的技能：完全相符 > 忽略符號完全相符 > 部分包含。
    回傳符合的 [(技能名稱, 數值), ...] 清單。"""
    if query in skill_lookup:
        return [(query, skill_lookup[query])]
    q_norm = _normalize_for_match(query)
    if not q_norm:
        return []
    exact_norm = [(n, v) for n, v in skill_lookup.items() if _normalize_for_match(n) == q_norm]
    if exact_norm:
        return exact_norm
    return [(n, v) for n, v in skill_lookup.items() if q_norm in _normalize_for_match(n)]

def growth_channel_gate(guild_id, channel_id):
    """成長紀錄的頻道閘門。回傳 (allowed, reason)：
      allowed=True  → 這個頻道可以開始／進行成長紀錄
      allowed=False → 不行，reason 是給使用者看的說明字串

    分兩種模式（見 _channel_uses_strict_whitelist）：
    - 嚴格模式（本頻道 GM 設了白名單）：需同時滿足
        1. 這個頻道（或討論串，原始 id）在某位 GM 的白名單裡
        2. 這個頻道有人啟用角色卡（沒人開卡的頻道不記；用開卡當『這是正式跑團場地』的訊號）
    - 自動模式（本頻道沒 GM，或 GM 沒設白名單）：一律放行。觸發本身就是玩家自己啟用角色卡或
      `.start`，所以不再要求「頻道有人開卡」——是誰觸發就記誰、只記本人。
    注意：白名單查『原始 channel_id』（討論串要各自加），開卡／GM 判斷則沿用母頻道正規化。
    """
    if _channel_uses_strict_whitelist(guild_id, channel_id):
        if not growth_channel_whitelist.is_allowed(guild_id, channel_id):
            return False, "這個頻道不在 GM 的成長紀錄白名單內，不會記錄成長。\n如需記錄，請 GM 在本頻道打 `.drgm rec` 開面板加入。"
        if not pc_active_manager.get_all_active_in_channel(guild_id, channel_id):
            return False, "這個頻道目前沒有任何人啟用角色卡，暫不記錄成長。請先用 `.pc` 面板【啟用】角色卡。"
        return True, None
    return True, None


def start_growth_on_pc_activate(guild_id, channel_id, user_id):
    """啟用角色卡時，若本頻道符合成長紀錄條件，視同呼叫 `.start` 開始（或重新開始）本頻道的
    成長紀錄，回傳要附加的提示文字；不符合條件時不開始，回傳空字串（不打擾玩家）。
    注意：這裡是「啟用當下」，本人這張卡已經算開好了，所以連嚴格模式的『頻道有開卡』一定成立；
    自動模式（本頻道沒 GM／GM 沒設白名單）一律放行，等於一啟用角色卡就自動幫本人開紀錄。
    真正會擋下來的只有嚴格模式下『本頻道不在白名單裡』這一關。"""
    allowed, _reason = growth_channel_gate(guild_id, channel_id)
    if not allowed:
        return ""
    already_active = growth_manager.is_active(guild_id, channel_id, user_id)
    growth_manager.start_session(guild_id, channel_id, user_id)
    if already_active:
        return "\n📈 本頻道原本就有一份進行中的成長紀錄，已重新開始一份新的（`.end` 查看清單）。"
    return "\n📈 已同時開始記錄你在本頻道的成長清單（`.end` 查看清單）。"

PC_PAGE_SIZE = 25  # Discord 選單一次最多 25 個選項

class PCPagedSelect(discord.ui.Select):
    """`.pc show` / `.pc del` / `.pc edit` 共用的分頁選單，只負責顯示「目前這一頁」的選項，
    實際的換頁跟按鈕都交給 PCPagedSelectView 管理。"""
    def __init__(self, view_ref, page_matches):
        self.view_ref = view_ref
        options = [
            discord.SelectOption(label=pc_display_label(alias, card)[:100], value=alias[:100])
            for alias, card in page_matches
        ]
        placeholder = {
            'show': "選擇要查看的角色卡…",
            'del': "選擇要刪除的角色卡…",
            'edit': "選擇要編輯的角色卡…",
            'use': "選擇要啟用的角色卡…",
        }[view_ref.mode]
        super().__init__(placeholder=placeholder, options=options, min_values=1, max_values=1)

    async def callback(self, interaction: discord.Interaction):
        await self.view_ref.handle_select(interaction, self.values[0])

class PCPagedNavButton(discord.ui.Button):
    """分頁用的「上一頁／下一頁」按鈕，只有超過 25 張角色卡時才會出現。"""
    def __init__(self, view_ref, direction):
        super().__init__(
            label="◀️ 上一頁" if direction < 0 else "▶️ 下一頁",
            style=discord.ButtonStyle.secondary,
            row=1,
        )
        self.view_ref = view_ref
        self.direction = direction

    async def callback(self, interaction: discord.Interaction):
        await self.view_ref.change_page(interaction, self.direction)

class PCPagedSelectView(discord.ui.View):
    """`.pc show`（mode='show'）／`.pc del`（mode='del'）／`.pc edit`（mode='edit'）共用：
    角色卡數量在 25 張以內只顯示單一選單；超過 25 張會自動分頁，
    多出「上一頁／下一頁」按鈕，換頁時重建選單但不用重新查詢資料。
    mode='edit' 時，選單的 callback 本身就是一次互動，可以直接跳出編輯 Modal，
    不需要再多一次按鈕確認（Discord 規定 Modal 只能從互動裡開，選單 callback 算數）。"""
    def __init__(self, mode, message, guild_id, user_id, matches, title, channel_id=None, actor_id=None):
        super().__init__(timeout=60)
        self.mode = mode
        self.message = message  # 給 mode='edit' 時建立 PcCardEditModal 用
        self.guild_id = guild_id
        self.user_id = user_id  # 角色卡歸屬的使用者
        self.channel_id = channel_id  # 給 mode='use' 啟用角色卡用
        self.matches = matches
        self.title = title
        self.page = 0
        # actor_id：允許操作這個選單的人。一般情況等於 user_id（自己動自己的卡）；
        # GM 代管刪除時，user_id 是被代管的玩家、actor_id 是實際按按鈕的 GM。
        self.actor_id = actor_id if actor_id is not None else user_id
        self._rebuild()

    @property
    def total_pages(self):
        return max(1, (len(self.matches) - 1) // PC_PAGE_SIZE + 1)

    def _rebuild(self):
        self.clear_items()
        start = self.page * PC_PAGE_SIZE
        self.add_item(PCPagedSelect(self, self.matches[start:start + PC_PAGE_SIZE]))
        if self.total_pages > 1:
            prev_btn = PCPagedNavButton(self, -1)
            next_btn = PCPagedNavButton(self, 1)
            prev_btn.disabled = (self.page <= 0)
            next_btn.disabled = (self.page >= self.total_pages - 1)
            self.add_item(prev_btn)
            self.add_item(next_btn)

    def make_embed(self):
        desc = "請選擇要操作的角色卡："
        if self.total_pages > 1:
            desc += f"（第 {self.page + 1}／{self.total_pages} 頁，共 {len(self.matches)} 張）"
        return discord.Embed(title=self.title, description=desc, color=0x00aaff)

    async def _check_author(self, interaction):
        if interaction.user.id != self.actor_id:
            if self.actor_id != self.user_id:
                await interaction.response.send_message("這不是你叫出來的代管選單喔，請自己用 `.pc` 面板的【代管角色卡】。", ephemeral=True)
            else:
                hint = {"show": "面板的【查看】", "del": "面板的【刪除】", "edit": "面板的【編輯】", "use": "面板的【啟用】"}[self.mode]
                await interaction.response.send_message(f"這不是你叫出來的選單喔，請自己輸入 {hint}。", ephemeral=True)
            return False
        return True

    async def change_page(self, interaction: discord.Interaction, direction):
        if not await self._check_author(interaction):
            return
        self.page = max(0, min(self.total_pages - 1, self.page + direction))
        self._rebuild()
        await interaction.response.edit_message(embed=self.make_embed(), view=self)

    async def handle_select(self, interaction: discord.Interaction, alias):
        if not await self._check_author(interaction):
            return
        card = pc_card_manager.get_card(self.guild_id, self.user_id, alias)
        if not card:
            await interaction.response.edit_message(embed=discord.Embed(title="❌ 這張角色卡已經不存在了", color=0xff0000), view=None)
            return
        if self.mode == 'show':
            # 卡片數值只給查看的人自己看；公開通知誰查看了哪張卡（同一頻道大家都看得到，但看不到內容）
            is_gm_mode = self.actor_id != self.user_id
            await interaction.response.send_message(embed=format_pc_card_embed(card, alias, interaction.user), ephemeral=True)
            try:
                if is_gm_mode:
                    public_desc = f"GM 代管查看：<@{self.user_id}> 的「{alias}」（內容只有查看的 GM 看得到）"
                else:
                    public_desc = f"角色名稱：{alias}（內容只有本人看得到）"
                await interaction.followup.send(embed=discord.Embed(title="📇 已私下顯示角色卡", description=public_desc, color=0x00aaff))
            except discord.HTTPException:
                pass
            try:
                await interaction.message.edit(view=None)
            except discord.HTTPException:
                pass
        elif self.mode == 'del':
            pc_card_manager.delete_card(self.guild_id, self.user_id, alias)
            is_gm_mode = self.actor_id != self.user_id
            owner_line = f"\n所屬玩家：<@{self.user_id}>" if is_gm_mode else ""
            await interaction.response.send_message(embed=discord.Embed(title="✅ 已刪除角色卡", description=f"角色名稱：{alias}{owner_line}", color=0x00aaff), ephemeral=True)
            try:
                public_desc = f"GM 代管刪除：<@{self.user_id}> 的「{alias}」" if is_gm_mode else None
                await interaction.followup.send(embed=discord.Embed(title="🗑️ 已刪除一張角色卡", description=public_desc, color=0x00aaff))
            except discord.HTTPException:
                pass
            try:
                await interaction.message.edit(view=None)
            except discord.HTTPException:
                pass
        elif self.mode == 'edit':
            await interaction.response.send_modal(PcCardEditModal(self.message, card, alias))
            try:
                await interaction.message.edit(view=None)
            except discord.HTTPException:
                pass
        else:  # 'use'
            pc_active_manager.set_active(self.guild_id, self.channel_id, self.user_id, alias)
            growth_note = start_growth_on_pc_activate(self.guild_id, self.channel_id, self.user_id)
            await interaction.response.send_message(
                embed=discord.Embed(
                    title="✅ 已在本頻道啟用角色卡",
                    description=f"角色名稱：**{pc_display_label(alias, card)}**\n之後在本頻道用 `.cc 技能名稱` 會自動抓這張卡的數值。換頻道要重新啟用。{growth_note}",
                    color=0x00aaff,
                ),
            )
            try:
                await interaction.message.edit(view=None)
            except discord.HTTPException:
                pass

class PCEditConfirmView(discord.ui.View):
    """`.pc edit 名字` 剛好比對到一張角色卡時，用一個按鈕確認再開編輯 Modal。
    Discord 規定 Modal 只能從互動（按鈕/選單）裡開，純文字指令沒辦法直接跳出視窗，
    所以這裡需要先跳個按鈕當「互動」，按下去才真正開編輯視窗。"""
    def __init__(self, message, guild_id, user_id, alias):
        super().__init__(timeout=60)
        self.message = message
        self.guild_id = guild_id
        self.user_id = user_id
        self.alias = alias

    @discord.ui.button(label="✏️ 開始編輯", style=discord.ButtonStyle.primary)
    async def edit_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.user_id:
            await interaction.response.send_message("這不是你叫出來的按鈕喔，請自己用 `.pc` 叫出面板後按【編輯】。", ephemeral=True)
            return
        card = pc_card_manager.get_card(self.guild_id, self.user_id, self.alias)
        if not card:
            await interaction.response.edit_message(embed=discord.Embed(title="❌ 這張角色卡已經不存在了", color=0xff0000), view=None)
            return
        self.stop()
        for child in self.children:
            child.disabled = True
        await interaction.response.send_modal(PcCardEditModal(self.message, card, self.alias))
        try:
            await interaction.message.edit(view=self)
        except discord.HTTPException:
            pass

class PCAliasSelect(discord.ui.Select):
    """`.pc 文字` 部分比對到多張角色卡時，讓玩家選擇要啟用哪一張。"""
    def __init__(self, author_id, guild_id, channel_id, user_id, matches):
        self.author_id = author_id
        self.guild_id = guild_id
        self.channel_id = channel_id
        self.user_id = user_id
        options = [
            discord.SelectOption(label=pc_display_label(alias, card)[:100], value=alias[:100])
            for alias, card in matches[:25]
        ]
        super().__init__(placeholder="選擇要啟用的角色卡…", options=options, min_values=1, max_values=1)

    async def callback(self, interaction: discord.Interaction):
        if interaction.user.id != self.author_id:
            await interaction.response.send_message("這不是你叫出來的選單喔，請自己用 `.pc` 叫出面板後按【啟用】。", ephemeral=True)
            return
        alias = self.values[0]
        card = pc_card_manager.get_card(self.guild_id, self.user_id, alias)
        if not card:
            await interaction.response.edit_message(embed=discord.Embed(title="❌ 這張角色卡已經不存在了", color=0xff0000), view=None)
            return
        pc_active_manager.set_active(self.guild_id, self.channel_id, self.user_id, alias)
        growth_note = start_growth_on_pc_activate(self.guild_id, self.channel_id, self.user_id)
        embed = discord.Embed(
            title="✅ 已在本頻道啟用角色卡",
            description=f"角色名稱：**{pc_display_label(alias, card)}**\n之後在本頻道用 `.cc 技能名稱` 會自動抓這張卡的數值。換頻道要重新啟用。{growth_note}",
            color=0x00aaff,
        )
        # 詳細說明只給本人；公開通知誰啟用了哪張卡（同一頻道大家看得到，選單本身已收掉）
        await interaction.response.send_message(embed=embed, ephemeral=True)
        try:
            await interaction.followup.send(
                embed=discord.Embed(title="✅ 已啟用角色卡", description=f"{interaction.user.display_name} → 「{pc_display_label(alias, card)}」", color=0x00aaff),
            )
        except discord.HTTPException:
            pass
        try:
            await interaction.message.edit(view=None)
        except discord.HTTPException:
            pass

class PCAliasSelectView(discord.ui.View):
    def __init__(self, author_id, guild_id, channel_id, user_id, matches):
        super().__init__(timeout=60)
        self.add_item(PCAliasSelect(author_id, guild_id, channel_id, user_id, matches))

# ---------- .pc 主面板（建立／啟用／查看／編輯／刪除 五顆按鈕） ----------
def pc_owner(message):
    """角色卡實際歸屬的使用者：一般情況下就是操作者本人（message.author）。
    GM 代管建立/刪除角色卡時，message 會額外掛一個 owner 屬性指向被代管的玩家，
    這樣角色卡才會存進「對方」帳號底下，而不是誤存到 GM 自己名下。"""
    return getattr(message, 'owner', None) or message.author

def pc_actor_hint(message):
    """跳出「請本人按下方按鈕」這類提示時，用來稱呼該由誰來按：
    一般情況是操作者自己（本人），GM 代管時改指名 GM（因為對方本人不會出現在這個流程裡）。"""
    owner = pc_owner(message)
    return "本人" if owner.id == message.author.id else f"{message.author.mention}（GM）"

class _InteractionMessageShim:
    """把 interaction 包裝成長得像 message 的替身（只提供 guild／author／channel／owner）。
    面板按鈕是「誰按算誰的」，不能沿用面板建立者的 message，所以用按按鈕那個人的
    interaction 包一個替身，讓 PcCardEditModal／_finalize_pc_card_save／run_pc_sheet_import
    這些原本吃 message 的舊函式不用改就能直接沿用。
    owner：GM 代管建立時傳入被代管的玩家，角色卡會存進 owner 底下；不傳則等於操作者本人。"""
    def __init__(self, interaction: discord.Interaction, owner=None):
        self.guild = interaction.guild
        self.author = interaction.user
        self.channel = interaction.channel
        self.owner = owner or interaction.user

class _MessageOwnerShim:
    """GM 代管角色卡「上傳檔案」流程專用：包一層讓 author 維持操作者本人（GM，用於權限判斷／訊息署名），
    owner 則是角色卡實際要存進哪個使用者底下。上傳檔案沒辦法從 Modal 完成，得等頻道下一則訊息，
    所以這裡包的是真的 discord.Message，不是 interaction。"""
    def __init__(self, message, owner):
        self.guild = message.guild
        self.author = message.author
        self.channel = message.channel
        self.owner = owner

class PCSheetUrlModal(discord.ui.Modal, title="🔗 從 Google 試算表匯入角色卡"):
    """`.pc` 面板「建立 → Google 試算表網址」跳出的表單：貼上連結送出後，
    走跟 `.pc url` 一模一樣的匯入流程（HKTRPG → Roll20 JSON → DC 文字團簡表）。"""
    def __init__(self, owner=None):
        super().__init__()
        self.owner = owner  # GM 代管建立時傳入被代管的玩家，None 代表操作者本人
        self.url_input = discord.ui.TextInput(
            label="試算表連結（要設成「知道連結的人皆可檢視」）",
            placeholder="https://docs.google.com/spreadsheets/d/xxxxx/edit",
            style=discord.TextStyle.short,
            required=True,
            max_length=500,
        )
        self.add_item(self.url_input)

    async def on_submit(self, interaction: discord.Interaction):
        sheet_url = str(self.url_input.value).strip()
        if not PC_SHEET_ID_RE.search(sheet_url):
            await interaction.response.send_message(
                embed=discord.Embed(title="❌ 無法辨識試算表連結", description="請確認貼的是完整的 Google 試算表網址。", color=0xff0000),
                ephemeral=True,
            )
            return
        # 先用 ephemeral 回掉這次互動（3 秒內必須回應），實際進度與結果照 `.pc url` 慣例發在頻道裡
        await interaction.response.send_message(
            embed=discord.Embed(title="🔄 正在讀取試算表…", description="請稍候，結果會發在頻道裡。", color=0x00aaff),
            ephemeral=True,
        )
        await run_pc_sheet_import(_InteractionMessageShim(interaction, owner=self.owner), sheet_url, send_progress=False)

class PCPasteTextModal(discord.ui.Modal, title="🗂️ 貼上角色卡"):
    """`.pc` 面板「建立 → 貼上文字」跳出的表單：一次貼滿 Roll20 匯入碼或 DC 文字團簡表送出，
    送出後走跟 `.pc set` 貼文字一樣的解析流程（handle_pc_paste）。
    這裡改用 Modal 而不是等頻道下一則訊息，是因為 Discord 一般訊息上限只有 2000 字，
    Roll20 匯出的 JSON 常常因為跳脫字元（\\", \\n 等）在更早就被 Discord 用戶端擋下；
    Modal 單一欄位上限是 4000 字，塞得下絕大多數角色卡。"""
    def __init__(self, owner=None):
        super().__init__()
        self.owner = owner  # GM 代管建立時傳入被代管的玩家，None 代表操作者本人
        self.card_text = discord.ui.TextInput(
            label="Roll20 匯入碼 或 DC 文字團簡表",
            style=discord.TextStyle.paragraph,
            required=True,
            max_length=4000,
            placeholder='貼上像 [{"character_name":...}] 這樣的 Roll20 JSON，或是戳卡版的文字團簡表',
        )
        self.add_item(self.card_text)

    async def on_submit(self, interaction: discord.Interaction):
        # ephemeral defer：後續（成功卡片存根或錯誤訊息）都照 handle_pc_paste 原本的規則發在頻道裡
        await interaction.response.defer(ephemeral=True)
        await handle_pc_paste(_InteractionMessageShim(interaction, owner=self.owner), str(self.card_text.value), None)

class PCCreateMethodSelect(discord.ui.Select):
    """`.pc` 面板按下「建立」後跳出的選單：選擇要「貼上文字」「上傳檔案」還是「Google 試算表網址」。
    owner：GM 代管建立時傳入被代管的玩家，None 代表操作者本人在幫自己建。"""
    def __init__(self, owner=None):
        self.owner = owner
        options = [
            discord.SelectOption(label="📋 貼上文字", value="paste", description="Roll20 匯入碼或 DC 文字團簡表"),
            discord.SelectOption(label="📎 上傳檔案", value="upload", description="上傳 .txt／.json 檔案"),
            discord.SelectOption(label="🔗 貼上試算表網址", value="url", description="戳卡／Roll20／HKTRPG 模板，試算表需可檢視"),
        ]
        super().__init__(placeholder="選擇要用哪種方式建立角色卡…", options=options, min_values=1, max_values=1)

    async def callback(self, interaction: discord.Interaction):
        if self.values[0] == "paste":
            # 跳 Modal 讓使用者直接貼一大段文字進去
            await interaction.response.send_modal(PCPasteTextModal(owner=self.owner))
        elif self.values[0] == "upload":
            # 不跳 Modal（Discord Modal 不支援夾帶檔案），改成跟 `.pc set` 一樣進入等待狀態，
            # 之後在本頻道傳一則附加 .txt／.json 的訊息就會被 on_message 的 pc_pending 邏輯接住解析。
            # 等待狀態一律用操作者（按按鈕的人）的身分登記，GM 代管時另外記下要存進誰的帳號底下（owner_id）。
            guild_id, channel_id, user_id = interaction.guild.id, interaction.channel.id, interaction.user.id
            pc_pending[(guild_id, channel_id, user_id)] = {
                'alias': None,
                'expire': time.time() + PC_PENDING_TIMEOUT,
                'owner_id': self.owner.id if self.owner else None,
            }
            target_note = f"（會存進 {self.owner.mention} 帳號底下）" if self.owner else ""
            await interaction.response.send_message(
                embed=discord.Embed(
                    title="📎 上傳角色卡檔案",
                    description=f"請在 {PC_PENDING_TIMEOUT} 秒內，於本頻道上傳 Roll20 匯入碼或 DC 文字團簡表的 `.txt`／`.json` 檔案。{target_note}",
                    color=0x00aaff,
                ),
                ephemeral=True,
            )
        else:  # url
            await interaction.response.send_modal(PCSheetUrlModal(owner=self.owner))

class PCCreateMethodView(discord.ui.View):
    def __init__(self, owner=None):
        super().__init__(timeout=60)
        self.add_item(PCCreateMethodSelect(owner=owner))

# 車卡：531／752 兩種骰屬性方案。純骰數字給玩家自己抄去填角色卡，不會直接寫入角色卡。
# 531：5 次 (3d6)x5 選 5 項填 力量/敏捷/意志/體質/外貌；3 次 (2d6+6)x5 選填 教育/體型/智力；1 次 (3d6)x5 填 幸運。
# 752：7 次 (3d6)x5 選 5 項填 力量/敏捷/意志/體質/外貌；5 次 (2d6+6)x5 選 3 項填 教育/體型/智力；2 次 (3d6)x5 選 1 項填 幸運。
_CAR_CARD_SCHEMES = {
    '531': {
        'label': '531 車卡',
        # 每組：(欄位說明, 骰幾次, 骰種, 該組×5結果總和的保底；None＝不保底)
        'groups': [
            ('力量、敏捷、意志、體質、外貌（5 項）', 5, '3d6', 245),  # 五項合計 <245 就整組重骰
            ('教育、體型、智力（3 項）', 3, '2d6+6', None),
            ('幸運', 1, '3d6', None),
        ],
    },
    '752': {
        'label': '752 車卡',
        # 752 是「多骰自己挑」，玩家本來就會挑高的，故不設保底
        'groups': [
            ('力量、敏捷、意志、體質、外貌（挑 5 項）', 7, '3d6', None),
            ('教育、體型、智力（挑 3 項）', 5, '2d6+6', None),
            ('幸運（挑 1 項）', 2, '3d6', None),
        ],
    },
}

def _roll_car_card_die(kind):
    """kind 是 '3d6' 或 '2d6+6'。回傳 (骰子點數清單, 骰子總和, x5 後的結果)。
    骰實際骰子相加，天生就是山丘（鐘形）分佈；額外 house rule：3d6 若骰出 [1,1,1]
    （最慘的屬性 15）給「一次」重骰機會——重骰後照單全收，所以 [1,1,1] 仍可能出現，
    但機率從 0.46% 降到約 0.002%（1/216 的平方），罕見但非 0。乘法呈現一律用 x 不用 *。"""
    if kind == '3d6':
        dice = [roll_dice(6) for _ in range(3)]
        if dice == [1, 1, 1]:                 # 三顆全 1 只給一次重骰；若又中就認了，故機率非 0
            dice = [roll_dice(6) for _ in range(3)]
        total = sum(dice)
    else:  # 2d6+6
        dice = [roll_dice(6) for _ in range(2)]
        total = sum(dice) + 6
    return dice, total, total * 5

def build_car_card_embed(scheme_key):
    scheme = _CAR_CARD_SCHEMES[scheme_key]
    embed = discord.Embed(
        title=f"🎲 {scheme['label']}",
        description="骰出來的數字自己挑，填進要建立的角色卡屬性欄位裡（本次骰值不會自動寫入角色卡）。",
        color=0x00aaff,
    )
    for group in scheme['groups']:
        field_label, times, kind = group[0], group[1], group[2]
        min_sum = group[3] if len(group) > 3 else None
        die_label = kind if kind == '3d6' else '(2d6+6)'
        # 有設保底的組（如 531 的五項主屬性）：整組重骰，直到 ×5 結果總和達門檻。
        # 設安全上限避免萬一門檻設太高導致卡死；245 這種合理門檻幾次就會過。
        rolls = [_roll_car_card_die(kind) for _ in range(times)]
        if min_sum is not None:
            for _ in range(10000):
                if sum(r[2] for r in rolls) >= min_sum:
                    break
                rolls = [_roll_car_card_die(kind) for _ in range(times)]
        lines = []
        for dice, total, result in rolls:
            dice_str = ','.join(map(str, dice))
            if kind == '3d6':
                lines.append(f"{die_label} x5 → [{dice_str}]={total} x 5 = {result}")
            else:
                lines.append(f"{die_label} x5 → [{dice_str}]={sum(dice)}+6={total} x 5 = {result}")
        if min_sum is not None:
            lines.append(f"— 本組合計 {sum(r[2] for r in rolls)}（保底 ≥{min_sum}，未達整組重骰）")
        embed.add_field(name=f"{field_label}　{die_label} x5，骰 {times} 次", value="\n".join(lines), inline=False)
    return embed

class CarCardSchemeSelect(discord.ui.Select):
    def __init__(self):
        options = [
            discord.SelectOption(label=scheme['label'], value=key)
            for key, scheme in _CAR_CARD_SCHEMES.items()
        ]
        super().__init__(placeholder="選擇 531 或 752 車卡…", options=options, min_values=1, max_values=1)

    async def callback(self, interaction: discord.Interaction):
        await interaction.response.send_message(embed=build_car_card_embed(self.values[0]), ephemeral=False)

class CarCardSchemeView(discord.ui.View):
    def __init__(self):
        super().__init__(timeout=60)
        self.add_item(CarCardSchemeSelect())

class PCMainPanelView(discord.ui.View):
    """`.pc`（無參數）叫出的主面板：建立／啟用／查看／編輯／刪除 五顆按鈕。
    persistent view（timeout=None＋固定 custom_id，在 on_ready 註冊），bot 重啟後舊面板照樣能按。
    按鈕「誰按算誰的」：每顆按鈕都只操作按的人自己的角色卡，選單一律 ephemeral 只有本人看得到。"""
    def __init__(self):
        super().__init__(timeout=None)

    async def _send_pc_select(self, interaction: discord.Interaction, mode, title, need_cards_hint):
        """啟用／查看／編輯／刪除 共用：撈按按鈕那個人的角色卡，跳 ephemeral 分頁選單。"""
        guild_id, channel_id, user_id = interaction.guild.id, interaction.channel.id, interaction.user.id
        cards = pc_card_manager.get_all(guild_id, user_id)
        if not cards:
            await interaction.response.send_message(
                embed=discord.Embed(title="📋 你的角色卡", description=need_cards_hint, color=0x00aaff),
                ephemeral=True,
            )
            return
        view = PCPagedSelectView(mode, _InteractionMessageShim(interaction), guild_id, user_id, list(cards.items()), title, channel_id=channel_id)
        await interaction.response.send_message(embed=view.make_embed(), view=view, ephemeral=True)

    @discord.ui.button(label="🆕 建立", style=discord.ButtonStyle.primary, custom_id="pc_panel:create", row=0)
    async def create_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        await interaction.response.send_message(
            embed=discord.Embed(title="🆕 建立角色卡", description="請選擇要用哪種方式建立：", color=0x00aaff),
            view=PCCreateMethodView(),
            ephemeral=True,
        )

    @discord.ui.button(label="✅ 啟用", style=discord.ButtonStyle.success, custom_id="pc_panel:use", row=0)
    async def use_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self._send_pc_select(interaction, 'use', "🗂️ 選擇要在本頻道啟用的角色卡", "目前沒有儲存任何角色卡。按「🆕 建立」開始建立。")

    @discord.ui.button(label="📋 查看", style=discord.ButtonStyle.secondary, custom_id="pc_panel:show", row=0)
    async def show_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self._send_pc_select(interaction, 'show', "📋 選擇要查看的角色卡", "目前沒有儲存任何角色卡。按「🆕 建立」開始建立。")

    @discord.ui.button(label="✏️ 編輯", style=discord.ButtonStyle.secondary, custom_id="pc_panel:edit", row=0)
    async def edit_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self._send_pc_select(interaction, 'edit', "✏️ 選擇要編輯的角色卡", "目前沒有儲存任何角色卡，沒有可以編輯的。按「🆕 建立」開始建立。")

    @discord.ui.button(label="🗑️ 刪除", style=discord.ButtonStyle.danger, custom_id="pc_panel:del", row=0)
    async def del_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self._send_pc_select(interaction, 'del', "🗑️ 選擇要刪除的角色卡", "目前沒有儲存任何角色卡，沒有可以刪除的。")

    @discord.ui.button(label="🎲 車卡", style=discord.ButtonStyle.secondary, custom_id="pc_panel:car", row=1)
    async def car_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        await interaction.response.send_message(
            embed=discord.Embed(title="🎲 車卡", description="選擇要用哪種車卡方式：", color=0x00aaff),
            view=CarCardSchemeView(),
            ephemeral=True,
        )

    @discord.ui.button(label="🎩 代管角色卡", style=discord.ButtonStyle.secondary, custom_id="pc_panel:gm_manage", row=1)
    async def gm_manage_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        """GM 專用：不限本頻道，只要在本伺服器任一頻道登記過 GM 就能用。
        按下去先選要代管哪位玩家，再進入跟自己 `.pc` 一樣的建立流程（但存進對方帳號），或選擇要刪除對方哪張卡。"""
        if not gm_manager.is_gm_anywhere_in_guild(interaction.guild.id, interaction.user.id):
            await interaction.response.send_message("你不是本伺服器登記過的 GM，無法使用代管角色卡功能。", ephemeral=True)
            return
        await interaction.response.send_message(
            embed=discord.Embed(
                title="🎩 代管角色卡",
                description="選擇要代管哪位玩家（也可以直接打 `.pc gm @玩家` 跳過這個選單）：",
                color=0x00aaff,
            ),
            view=GMPCTargetSelectView(),
            ephemeral=True,
        )


def build_gm_pc_manage_embed(target):
    return discord.Embed(
        title=f"🎩 代管角色卡｜{target.display_name}",
        description=(
            "🆕 建立：幫這位玩家建立一張新角色卡，跟本人自己 `.pc` 一樣可以選「貼上文字」「上傳檔案」「試算表網址」，"
            "差別是會直接存進**對方**帳號底下\n"
            "📋 查看：以 ephemeral 訊息顯示這位玩家某張角色卡的完整內容（只有按的 GM 看得到）\n"
            "✏️ 編輯：修改這位玩家既有的一張角色卡，整段換貼文字重新解析（支援 Roll20 匯入碼）\n"
            "🗑️ 刪除：刪除這位玩家的一張角色卡"
        ),
        color=0x00aaff,
    )

class GMPCTargetSelect(discord.ui.UserSelect):
    """GM 代管角色卡：選擇要代管哪位玩家。每次點擊都重新檢查 GM 身分，避免面板開著時身分被收回還能用。"""
    def __init__(self):
        super().__init__(placeholder="選擇要代管的玩家…", min_values=1, max_values=1)

    async def callback(self, interaction: discord.Interaction):
        if not gm_manager.is_gm_anywhere_in_guild(interaction.guild.id, interaction.user.id):
            await interaction.response.send_message("你不是本伺服器登記過的 GM，無法使用代管角色卡功能。", ephemeral=True)
            return
        target = self.values[0]
        if target.bot:
            await interaction.response.send_message("不能對機器人代管角色卡。", ephemeral=True)
            return
        await interaction.response.send_message(embed=build_gm_pc_manage_embed(target), view=GMPCManagePanelView(target), ephemeral=True)

class GMPCTargetSelectView(discord.ui.View):
    def __init__(self):
        super().__init__(timeout=120)
        self.add_item(GMPCTargetSelect())

class GMPCManagePanelView(discord.ui.View):
    """代管特定一位玩家角色卡的操作面板：建立／刪除。跟 `.pc` 主面板一樣「誰按都要驗身分」，
    差別是驗的是「按的人是不是 GM」而不是「按的人是不是卡片本人」——同伺服器任何 GM 都能操作。
    非 persistent（5 分鐘逾時），不需要重啟後還能按，跟 PCEditConfirmView 等短期互動 View 一致。"""
    def __init__(self, target):
        super().__init__(timeout=300)
        self.target = target

    async def _check_gm(self, interaction: discord.Interaction):
        if not gm_manager.is_gm_anywhere_in_guild(interaction.guild.id, interaction.user.id):
            await interaction.response.send_message("你不是本伺服器登記過的 GM，無法使用代管角色卡功能。", ephemeral=True)
            return False
        return True

    @discord.ui.button(label="🆕 建立", style=discord.ButtonStyle.primary)
    async def create_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not await self._check_gm(interaction):
            return
        await interaction.response.send_message(
            embed=discord.Embed(title="🆕 建立角色卡", description=f"要用哪種方式幫 {self.target.mention} 建立：", color=0x00aaff),
            view=PCCreateMethodView(owner=self.target),
            ephemeral=True,
        )

    @discord.ui.button(label="📋 查看", style=discord.ButtonStyle.secondary)
    async def show_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not await self._check_gm(interaction):
            return
        guild_id = interaction.guild.id
        cards = pc_card_manager.get_all(guild_id, self.target.id)
        if not cards:
            await interaction.response.send_message(
                embed=discord.Embed(title="📋 查看角色卡", description=f"{self.target.mention} 目前沒有任何角色卡。", color=0x00aaff),
                ephemeral=True,
            )
            return
        view = PCPagedSelectView(
            'show', None, guild_id, self.target.id, list(cards.items()),
            f"📋 選擇要查看的角色卡（{self.target.display_name}）",
            actor_id=interaction.user.id,
        )
        await interaction.response.send_message(embed=view.make_embed(), view=view, ephemeral=True)

    @discord.ui.button(label="✏️ 編輯", style=discord.ButtonStyle.secondary)
    async def edit_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not await self._check_gm(interaction):
            return
        guild_id = interaction.guild.id
        cards = pc_card_manager.get_all(guild_id, self.target.id)
        if not cards:
            await interaction.response.send_message(
                embed=discord.Embed(title="✏️ 編輯角色卡", description=f"{self.target.mention} 目前沒有任何角色卡。", color=0x00aaff),
                ephemeral=True,
            )
            return
        view = PCPagedSelectView(
            'edit', _InteractionMessageShim(interaction, owner=self.target), guild_id, self.target.id, list(cards.items()),
            f"✏️ 選擇要編輯的角色卡（{self.target.display_name}）",
            actor_id=interaction.user.id,
        )
        await interaction.response.send_message(embed=view.make_embed(), view=view, ephemeral=True)

    @discord.ui.button(label="🗑️ 刪除", style=discord.ButtonStyle.danger)
    async def del_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not await self._check_gm(interaction):
            return
        guild_id = interaction.guild.id
        cards = pc_card_manager.get_all(guild_id, self.target.id)
        if not cards:
            await interaction.response.send_message(
                embed=discord.Embed(title="🗑️ 刪除角色卡", description=f"{self.target.mention} 目前沒有任何角色卡。", color=0x00aaff),
                ephemeral=True,
            )
            return
        view = PCPagedSelectView(
            'del', None, guild_id, self.target.id, list(cards.items()),
            f"🗑️ 選擇要刪除的角色卡（{self.target.display_name}）",
            actor_id=interaction.user.id,
        )
        await interaction.response.send_message(embed=view.make_embed(), view=view, ephemeral=True)


class PCSkillSelect(discord.ui.Select):
    """`.cc 技能名稱` 部分比對到多個技能時，讓玩家選擇要檢定哪一個，選完直接擲骰。"""
    def __init__(self, author_id, message, bonus_dice, target_type, matches):
        self.author_id = author_id
        self.message = message
        self.bonus_dice = bonus_dice
        self.target_type = target_type
        self.value_map = {name: value for name, value in matches}
        options = [
            discord.SelectOption(label=f"{name}（{value}%）"[:100], value=name[:100])
            for name, value in matches[:25]
        ]
        super().__init__(placeholder="選擇要檢定的技能…", options=options, min_values=1, max_values=1)

    async def callback(self, interaction: discord.Interaction):
        if interaction.user.id != self.author_id:
            await interaction.response.send_message("這不是你叫出來的選單喔，請自己輸入 `.cc 技能名稱`。", ephemeral=True)
            return
        name = self.values[0]
        value = self.value_map[name]
        crit_range, fumble_range = get_effective_range(self.message)
        final_roll, level, bonus_desc, all_rolls = coc_check(value, self.bonus_dice, crit_range, fumble_range)
        title = "COC 七版檢定"
        if self.bonus_dice > 0:
            title += f" (+{self.bonus_dice}獎勵骰)"
        elif self.bonus_dice < 0:
            title += f" ({-self.bonus_dice}懲罰骰)"
        line = f"{name} ({value}%)\n{bonus_desc} → 最終擲骰 {final_roll} → **{level}**"
        maybe_record_growth(self.message, name, value, level, self.bonus_dice, self.target_type)
        embed = discord.Embed(title=title, description=line, color=0x00aaff)
        embed.set_footer(text=interaction.user.display_name, icon_url=interaction.user.display_avatar.url)
        # 選單本身只有本人看得到，但擲骰結果要讓大家看到，所以另外發一則公開訊息
        await interaction.response.edit_message(content="✅ 已完成檢定，結果公佈在頻道中。", embed=None, view=None)
        await self.message.channel.send(embed=embed)

class PCSkillSelectView(discord.ui.View):
    def __init__(self, author_id, message, bonus_dice, target_type, matches):
        super().__init__(timeout=60)
        self.add_item(PCSkillSelect(author_id, message, bonus_dice, target_type, matches))

def build_pc_skill_lookup(card):
    """把角色卡的技能列表/戰鬥列表/技能三個區塊，加上屬性（力量、敏捷、意志、體質、外貌、教育、體型、智力）、
    幸運（LUK）、靈感、目前 SAN（SAN／理智），合併成 {名稱: 數值} 方便查詢（非數字的值會被忽略）。
    同名時技能列表/戰鬥列表/技能會蓋過屬性，維持原本以技能為主的查詢優先權。
    SAN 併進來是為了讓 `.cc san`／`.cc 理智` 能像 `.cc 鬥毆` 一樣用卡上目前 SAN 當技能值檢定（不扣理智），
    但成功不算成長（見 NON_GROWABLE_SKILLS）。"""
    lookup = {}
    attrs = card.get('attributes') or {}
    for name, value in attrs.items():
        if isinstance(value, int):
            lookup[name] = value
    luck = card.get('luck')
    if isinstance(luck, int):
        for key in ('LUK', 'luk', '幸運'):
            lookup[key] = luck
    idea = card.get('idea')
    if isinstance(idea, int):
        lookup['靈感'] = idea
    san_cur = card.get('san_cur')
    if isinstance(san_cur, int):
        for key in ('SAN', 'san', '理智'):
            lookup[key] = san_cur
    for group in (card.get('skills'), card.get('combat'), card.get('extra_skills')):
        if not group:
            continue
        for name, value in group:
            if isinstance(value, int):
                lookup[name] = value
    return lookup

def find_pc_skill_entry(card, skill_name):
    """在角色卡的技能列表／戰鬥列表／技能三個區塊裡找符合名稱的技能（先完全相符，找不到再忽略空白/符號比對，
    且忽略符號比對時必須唯一符合才算數，避免誤改到別的技能）。
    回傳 (所在的list, 該技能在list裡的索引, 技能名稱, 目前數值)；找不到回傳 None。"""
    for key in ('skills', 'combat', 'extra_skills'):
        group = card.get(key)
        if not group:
            continue
        for idx, (name, value) in enumerate(group):
            if name == skill_name:
                return group, idx, name, value
    target_norm = _normalize_for_match(skill_name)
    if not target_norm:
        return None
    matches = []
    for key in ('skills', 'combat', 'extra_skills'):
        group = card.get(key)
        if not group:
            continue
        for idx, (name, value) in enumerate(group):
            if _normalize_for_match(name) == target_norm:
                matches.append((group, idx, name, value))
    if len(matches) == 1:
        return matches[0]
    return None

# ---------- 角色卡欄位調整（.pc adj，用於團務中屬性/LUK/SAN/HP/MP/技能 增減） ----------
# 值 -> (種類, 屬性名稱或None)；種類對應 card 裡實際存放的位置
_PC_ADJ_FIELD_MAP = {}
for _label in _PC_ATTR_LABELS:
    _PC_ADJ_FIELD_MAP[_label] = ('attr', _label)
for _key in ('LUK', 'luk', '幸運', 'luck'):
    _PC_ADJ_FIELD_MAP[_key] = ('luck', None)
for _key in ('SAN', 'san', '理智'):
    _PC_ADJ_FIELD_MAP[_key] = ('san', None)
for _key in ('HP', 'hp'):
    _PC_ADJ_FIELD_MAP[_key] = ('hp', None)
for _key in ('MP', 'mp'):
    _PC_ADJ_FIELD_MAP[_key] = ('mp', None)
_PC_ADJ_FIELD_MAP['靈感'] = ('idea', None)

def resolve_pc_adj_field(field_raw):
    """把使用者輸入的欄位名稱對應到 card 裡實際存放的位置，找不到回傳 None。"""
    return _PC_ADJ_FIELD_MAP.get(field_raw) or _PC_ADJ_FIELD_MAP.get(field_raw.upper()) or _PC_ADJ_FIELD_MAP.get(field_raw.lower())

def get_pc_field_value(card, kind, attr_name):
    if kind == 'attr':
        return card.get('attributes', {}).get(attr_name)
    if kind == 'luck':
        return card.get('luck')
    if kind == 'san':
        return card.get('san_cur')
    if kind == 'hp':
        return card.get('hp_cur')
    if kind == 'mp':
        return card.get('mp_cur')
    if kind == 'idea':
        return card.get('idea')
    return None

def set_pc_field_value(card, kind, attr_name, value):
    if kind == 'attr':
        card.setdefault('attributes', {})[attr_name] = value
    elif kind == 'luck':
        card['luck'] = value
    elif kind == 'san':
        card['san_cur'] = value
    elif kind == 'hp':
        card['hp_cur'] = value
    elif kind == 'mp':
        card['mp_cur'] = value
    elif kind == 'idea':
        card['idea'] = value

def get_cthulhu_mythos_value(card):
    """從角色卡技能裡找「克蘇魯神話」的值，找不到視為 0（用於算 SAN 上限：99-克蘇魯神話）。"""
    lookup = build_pc_skill_lookup(card)
    if '克蘇魯神話' in lookup:
        return lookup['克蘇魯神話']
    target = _normalize_for_match('克蘇魯神話')
    for name, value in lookup.items():
        if _normalize_for_match(name) == target:
            return value
    return 0

def apply_pc_field_adjustment(card, kind, attr_name, delta_or_set, is_relative):
    """調整 card 上一個欄位的數值：is_relative 時用加減（可正可負），否則直接設成該值。
    數值下限鎖 0；HP／MP 另外鎖上限，不會超過角色卡上的 hp_max／mp_max；
    SAN 上限鎖 99-克蘇魯神話技能值（沒有該技能視為 0，也就是上限 99），理智恢復不會超過這個數字。
    回傳 (舊值, 新值)。"""
    old_val = get_pc_field_value(card, kind, attr_name)
    if old_val is None:
        old_val = 0
    new_val = old_val + delta_or_set if is_relative else delta_or_set
    new_val = max(0, new_val)
    if kind == 'hp' and card.get('hp_max') is not None:
        new_val = min(new_val, card['hp_max'])
    elif kind == 'mp' and card.get('mp_max') is not None:
        new_val = min(new_val, card['mp_max'])
    elif kind == 'san':
        max_san = 99 - get_cthulhu_mythos_value(card)
        new_val = min(new_val, max_san)
    set_pc_field_value(card, kind, attr_name, new_val)
    return old_val, new_val

# ---------- 抽籤表 (MongoDB) ----------
class TableManager:
    def __init__(self, connection_string=None, db_name='dicebot_db'):
        self.data = defaultdict(dict)
        self.client = None
        if not connection_string:
            print("⚠️ 警告：未設定 MONGO_URI，資料將無法持久保存！")
            return
        try:
            self.client = MongoClient(connection_string)
            self.db = self.client[db_name]
            self.collection = self.db['draw_tables']
            self.load()
            print("✅ 抽籤表資料庫連線成功")
        except Exception as e:
            print(f"❌ 資料庫連線失敗: {e}")
            self.client = None

    def load(self):
        if not self.client: return
        try:
            self.data = defaultdict(dict)
            for doc in self.collection.find():
                guild_id = int(doc['guild_id'])
                self.data[guild_id] = doc['tables']
        except Exception as e:
            print(f"⚠️ 載入資料失敗: {e}")

    def save(self, guild_id):
        if not self.client: return
        try:
            self.collection.replace_one(
                {'guild_id': str(guild_id)},
                {
                    'guild_id': str(guild_id),
                    'tables': self.data[guild_id]
                },
                upsert=True
            )
        except Exception as e:
            print(f"⚠️ 雲端存檔失敗: {e}")

    def add_table(self, guild_id, name, items):
        self.data[guild_id][name] = items
        self.save(guild_id)

    def get_table(self, guild_id, name):
        return self.data[guild_id].get(name)

    def list_tables(self, guild_id):
        return list(self.data[guild_id].items())

    def del_table(self, guild_id, name):
        if name in self.data[guild_id]:
            del self.data[guild_id][name]
            self.save(guild_id)
            return True
        return False

    def clear_tables(self, guild_id):
        self.data[guild_id] = {}
        self.save(guild_id)

uri = os.getenv("MONGO_URI")
table_manager = TableManager(connection_string=uri)

# ---------- Discord Bot ----------
intents = discord.Intents.default()
intents.message_content = True
intents.members = True  # 需要讀取完整成員名單（.drgm addgm 用名字/ID指定他人才找得到人），
                         # 這是「特權 Intent」，還必須在 Discord Developer Portal 手動開啟，見下方說明
bot = commands.Bot(command_prefix='.', intents=intents, help_command=None)

def effective_channel_id(channel_id):
    """討論串（Thread）視同母頻道：把討論串的 id 換成母頻道的 id。
    所有以 channel_id 為 key 的長期狀態（角色卡啟用、成長紀錄、GM 登記、大成功範圍指定、
    瘋狂檢定暫存）都經過這層正規化，讓「在頻道裡開的卡／開始的紀錄／登記的 GM」
    在該頻道底下的討論串一樣生效，反過來在討論串裡做的操作也會記回母頻道。
    找不到頻道（例如已封存、不在快取裡的討論串）就原樣回傳，行為退回舊版（各自獨立）。
    注意：先攻／追逐／戰技等「戰鬥現場」狀態刻意不經過這層——討論串裡開打就是獨立的一場。"""
    ch = bot.get_channel(channel_id)
    if isinstance(ch, discord.Thread) and ch.parent_id:
        return ch.parent_id
    return channel_id

gm_manager = GMManager()
cmd_manager = CmdManager()
crit_range_manager = CritRangeManager()
active_gm_manager = ActiveGMManager()
growth_channel_whitelist = GrowthChannelWhitelist()
growth_manager = GrowthManager()
pc_card_manager = PCCardManager()
pc_active_manager = PCActiveManager()
npc_card_manager = NpcCardManager()

# 「等待貼上角色卡」的暫存狀態：{(guild_id, channel_id, user_id): {'alias': str或None, 'expire': timestamp}}
# 用 .pc set 觸發後，同頻道同一人的下一則非指令訊息就會被當成角色卡文字解析。
pc_pending = {}
PC_PENDING_TIMEOUT = 120  # 秒

# 「先攻順序」暫存狀態，每個頻道一份：{(guild_id, channel_id): {'entries': {名字: {...}}}}
# 每個條目用 'kind' 分三種（可以混用，詳見 format_init_embed 上方的說明）：
#   {'kind': 'dex', 'dex': int, 'skill': int或None}                — 面板「➕ 登記 NPC」或「⚔️ 敏捷作為先攻」直接登記
#   {'kind': 'roll_check', 'roll': int, 'level': str}              — 面板「🎲 擲骰檢定作為先攻」後接 .cc 技能檢定
#   {'kind': 'roll_generic', 'roll': int}                          — 面板「🎲 擲骰檢定作為先攻」後接通用骰子 xdy+z／xdy
# 先攻名單持久化：每次變動就整份寫回 JSON 檔，bot 更新程式／重啟後名單不會消失。
# 名單只會在這三種情況被刪掉：GM 按「🧹 清空」、GM 按「🏁 結束戰鬥」、條目被移除到整份變空。
# （init_pending 是 60 秒內等擲骰的暫時狀態，不需要也不適合持久化。）
INIT_SESSIONS_FILE = 'init_sessions_data.json'

def _load_init_sessions():
    """啟動時載回上次的先攻名單。JSON 的 key 是 "guild_id:channel_id" 字串，載回時轉回 tuple。"""
    if not os.path.exists(INIT_SESSIONS_FILE):
        return {}
    try:
        with open(INIT_SESSIONS_FILE, 'r', encoding='utf-8') as f:
            raw = json.load(f)
        return {tuple(int(x) for x in k.split(':')): v for k, v in raw.items()}
    except Exception as e:
        print(f"⚠️ 讀取 {INIT_SESSIONS_FILE} 失敗，將以空白先攻名單啟動：{e}")
        return {}

init_sessions = _load_init_sessions()

def init_sessions_save():
    """先攻名單有任何變動就呼叫這個把整份寫回檔案。"""
    try:
        with open(INIT_SESSIONS_FILE, 'w', encoding='utf-8') as f:
            json.dump({f"{k[0]}:{k[1]}": v for k, v in init_sessions.items()}, f, ensure_ascii=False, indent=2)
    except Exception as e:
        print(f"⚠️ 寫入 {INIT_SESSIONS_FILE} 失敗（名單仍在記憶體中正常運作）：{e}")


# 面板「🎲 擲骰檢定作為先攻」的暫存狀態：{(guild_id, channel_id, user_id): {'name': str, 'expire': timestamp}}
# 設定後，這個人在本頻道的下一次公開擲骰（.cc 技能檢定或通用骰子）會被攔截登記進先攻名單。
init_pending = {}
INIT_PENDING_TIMEOUT = 60  # 秒

class InitPanelTracker(JsonStore):
    """記錄每個頻道「最新一份 `.init` 面板」的訊息 ID：
    重打 `.init` 發出新面板時，順手把上一份面板的按鈕拿掉（使其失效），
    避免頻道裡同時存在多份可以按的面板。存成 JSON 檔是為了 bot 重啟後
    也還找得到重啟前發的舊面板來替換（persistent view 重啟後仍可按）。
    資料結構：{"guild_id:channel_id": message_id}"""
    def __init__(self, filename='init_panel_data.json'):
        super().__init__(filename)

    def get_panel(self, guild_id, channel_id):
        return self.data.get(f"{guild_id}:{channel_id}")

    def set_panel(self, guild_id, channel_id, message_id):
        self.data[f"{guild_id}:{channel_id}"] = message_id
        self.save()

init_panel_tracker = InitPanelTracker()


# 「追逐」暫存狀態，每個頻道一份：
# {(guild_id, channel_id): {'length': int, 'obstacles': {位置: 說明}, 'participants': {名字: {'role': 'pursuer'或'evader', 'position': int, 'target': 名字或None}}}}
# 簡化模型：同一場追逐共用一條「區位軌道」跟同一組障礙設定，但每個人的位置各自獨立記錄，
# 藉此支援多名追逐者/逃跑者分頭跑（各自進度不同步），實務上仍建議分頭差異太大時另開一場（面板「🎲 隨機產生賽道」）。
chase_sessions = {}

class ChasePanelTracker(JsonStore):
    """記錄每個頻道『最新一份 `.chase` 面板』的訊息 ID，機制跟 InitPanelTracker 一樣：
    重打 `.chase` 發新面板時，把上一份面板的按鈕拿掉；bot 重啟後 persistent view 仍可按，
    這份紀錄讓「按鈕動作完成後刷新面板本體」也能在重啟後找得到目標訊息。
    資料結構：{"guild_id:channel_id": message_id}"""
    def __init__(self, filename='chase_panel_data.json'):
        super().__init__(filename)

    def get_panel(self, guild_id, channel_id):
        return self.data.get(f"{guild_id}:{channel_id}")

    def set_panel(self, guild_id, channel_id, message_id):
        self.data[f"{guild_id}:{channel_id}"] = message_id
        self.save()

chase_panel_tracker = ChasePanelTracker()

# ---------- 等待防禦方回應的對抗判定（.melee／.cc 對抗／追逐攻擊共用） ----------
class _IdOnlyMessageShim:
    """只提供 guild.id／channel.id 的假 message。get_effective_range／get_channel_gm 這類
    函式其實只吃這兩個 id，但簽章是吃 message；重啟後我們手上只剩存下來的 id，用這個替身接。"""
    class _Obj:
        def __init__(self, _id):
            self.id = _id

    def __init__(self, guild_id, channel_id):
        self.guild = self._Obj(guild_id)
        self.channel = self._Obj(channel_id)


class MeleePendingStore(JsonStore):
    """等待防禦方回應的對抗判定，以「對抗訊息的 message_id」為 key 存下結算需要的全部欄位。

    這份持久化是為了讓 MeleeResponseView／CCOpposedView 能做成 persistent view：
    按鈕永不失效，連 bot 重啟前發出的舊對抗訊息都還能按【反擊】【閃避】。
    （原本狀態存在 view 實例裡、逾時後靠 `.反擊`／`.閃避` 文字指令補救；文字指令已移除，
    按鈕成為唯一的回應方式，所以狀態一定要能跨重啟存活，否則會出現無法結算的死局。）
    """
    def __init__(self, filename='melee_pending_data.json'):
        super().__init__(filename)  # key: str(message_id) -> state dict

    def put(self, message_id, state):
        self.data[str(message_id)] = state
        self.save()

    def get(self, message_id):
        return self.data.get(str(message_id))

    def pop(self, message_id):
        state = self.data.pop(str(message_id), None)
        if state is not None:
            self.save()
        return state

melee_pending_store = MeleePendingStore()

# 「一次性損失超過5點SAN，等待下一次智力檢定」的暫存狀態：
# {(guild_id, channel_id, user_id): {'alias': str或None, 'loss': int, 'link': str, 'expire': timestamp}}
# 在 .sc 造成單次損失超過5點SAN後設置，該使用者在本頻道下一次 .cc 智力 檢定會被消耗掉這個狀態，
# 若智力檢定成功，角色陷入瘋狂。
pending_madness_check = {}
MADNESS_CHECK_TIMEOUT = 1800  # 秒（30分鐘內要完成下一步智力檢定，逾時作廢）

# ---------- 團務收尾 .save ----------
SAVE_SKIP_WORDS = {'無', '没有', '沒有', '跳過', 'skip', 'x', '-', '無.', '無。'}

def format_save_summary(answers, author):
    """把團務收尾表單填的內容組成最終貼文，結尾附上『拉線』分隔線。"""
    today = time.strftime('%Y-%m-%d')
    lines = [
        f"📅 日期：{today}",
        f"👥 出席角色：{answers.get('attendees', '')}",
        "",
        "📖 劇情摘要：",
        answers.get('summary', ''),
    ]
    todo = (answers.get('todo') or '').strip()
    if todo and todo not in SAVE_SKIP_WORDS:
        lines += ["", "※ 下次開團必做事項：", todo]
    lines += ["", f"🗓️ 下次團務時間：{answers.get('next_time', '')}"]
    lines += ["", "－" * 20]  # 拉線：宣告本次團務收尾
    embed = discord.Embed(title="📋 團務收尾", description="\n".join(lines), color=0x00aaff)
    embed.set_footer(text=f"由 {author.display_name} 收尾", icon_url=author.display_avatar.url)
    return embed

class SaveWizardModal(discord.ui.Modal, title="📋 團務收尾"):
    """一次跳出表單填四個欄位，填完送出才會發文，不會在頻道裡一來一往洗版。"""
    attendees = discord.ui.TextInput(label="出席角色", placeholder="小明, 小華, 小剛", required=True, max_length=200)
    summary = discord.ui.TextInput(label="本次劇情摘要", style=discord.TextStyle.paragraph, required=True, max_length=1000)
    todo = discord.ui.TextInput(label="※ 下次開團必做事項（沒有可留空）", style=discord.TextStyle.paragraph, required=False, max_length=500)
    next_time = discord.ui.TextInput(label="下次團務時間", placeholder="下週六晚上八點", required=True, max_length=100)

    async def on_submit(self, interaction: discord.Interaction):
        answers = {
            'attendees': str(self.attendees.value).strip(),
            'summary': str(self.summary.value).strip(),
            'todo': str(self.todo.value).strip(),
            'next_time': str(self.next_time.value).strip(),
        }
        await interaction.response.send_message(embed=format_save_summary(answers, interaction.user))

class SaveStartView(discord.ui.View):
    """`.save` 先發這個按鈕，按下去才彈出表單（Discord 規定表單一定要由互動觸發，不能純文字指令直接跳出）。"""
    def __init__(self, author_id):
        super().__init__(timeout=180)
        self.author_id = author_id

    @discord.ui.button(label="📝 開始填寫團務收尾", style=discord.ButtonStyle.primary)
    async def start_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.author_id:
            await interaction.response.send_message("這不是你叫出來的按鈕喔，請自己輸入 `.save`。", ephemeral=True)
            return
        await interaction.response.send_modal(SaveWizardModal())

def is_gm(guild_id, channel_id, user_id):
    return user_id in gm_manager.get_gm_users(guild_id, channel_id)

def get_channel_gm(message):
    """
    決定目前頻道對應哪一位 GM，完全依照這個頻道自己的登記名單判斷，
    不再涉及 Discord 頻道權限或分類（category）判斷：
    1. 若這個頻道剛好只登記了一位 GM，直接視為該頻道的 GM。
    2. 若登記了兩位（以上），且已用 `.drgm ran bind` 指定其中一位，採用該指定。
    3. 其餘情況（沒有人登記，或多位但尚未指定）視為無法判斷。
    回傳 (gm_user_id, source)：
      source 為 'single'（唯一登記，自動套用）、'active'（多位登記中被指定的那位）
      或 None（無法判斷）。
    """
    guild_id = message.guild.id
    channel_id = message.channel.id

    gms = gm_manager.get_gm_users(guild_id, channel_id)

    if len(gms) == 1:
        return gms[0], 'single'

    if len(gms) > 1:
        active = active_gm_manager.get_active(guild_id, channel_id)
        if active is not None and active in gms:
            return active, 'active'

    return None, None

def get_effective_range(message):
    """
    決定目前頻道應套用哪位 GM 的大成功/大失敗範圍。
    找不到明確的 GM（本頻道沒登記唯一 GM 或未指定，或該 GM 未設定範圍）時，
    回傳 (None, None)，coc_check 會退回預設規則。
    """
    guild_id = message.guild.id
    gm_id, _source = get_channel_gm(message)
    if gm_id is None:
        return None, None
    return crit_range_manager.get_range(guild_id, gm_id)

# ---------- 其他功能 ----------
def get_alias(guild_id, channel_id, user_id):
    for gm in gm_manager.get_gms(guild_id, channel_id):
        if gm['user_id'] == user_id:
            return gm['alias']
    return None

async def send_private_embed(ctx_or_msg, user, embed):
    """把已經組好的 embed 私訊給 user，私訊被拒或失敗時在原頻道提示。"""
    try:
        dm = await user.create_dm()
        await dm.send(embed=embed)
        return True
    except discord.Forbidden:
        await ctx_or_msg.channel.send(f"⚠️ 無法私訊給 {user.display_name}，請對方在 Discord 設定中開啟「允許伺服器成員直接訊息」。")
        return False
    except Exception as e:
        await ctx_or_msg.channel.send(f"⚠️ 私訊失敗：{e}")
        return False

# ---------- 獨立路由函式 ----------
def record_growth_result(guild_id, channel_id, user_id, skill_name, skill_value, level, link=None):
    """成長紀錄的核心：直接吃 id 不吃 message，讓「CC 對抗判定的防禦方」這種
    用按鈕回應、沒有自己訊息的檢定也能記錄。channel_id 由 growth_manager 內部做
    討論串→母頻道正規化，所以傳討論串 id 進來也沒問題。
    規則跟一般檢定一致：只記錄「成功、大成功、大失敗」，普通「失敗」不記錄；
    沒填技能名稱時改累計次數並保留訊息連結（沒有連結可留就整筆略過）。"""
    if level == '失敗':
        return
    if not growth_manager.is_active(guild_id, channel_id, user_id):
        return
    # 白名單累加閘門在 growth_manager.record_check／record_unnamed_check 內部處理
    # （頻道中途被移出白名單後停止累加，已記錄的保留），這裡不再重複判斷。
    if skill_name:
        growth_manager.record_check(guild_id, channel_id, user_id, skill_name, skill_value, level)
    elif link:
        growth_manager.record_unnamed_check(guild_id, channel_id, user_id, link)

def maybe_record_growth(message, skill_name, skill_value, level, bonus_dice, target_type):
    """若發話者在本頻道有進行中的 .start～.end 紀錄，就記錄這次檢定結果（用於結團成長清單）。
    規則：
    - 只計算 target_type == 'channel' 的公開檢定，暗骰（dr/ddr/dddr）不計算。
      （這個參數指的是「公開骰 vs 暗骰」，跟頻道／討論串無關；討論串支援由
      growth_manager 內部的討論串→母頻道 key 正規化處理。）
    - 只計算 bonus_dice == 0 的一般檢定，帶獎勵骰／懲罰骰（cc1/cc2/ccn1/ccn2）不計算。
    - 只記錄「成功、大成功、大失敗」的結果，普通的「失敗」不記錄。
    - 有填技能名稱：記錄到具名技能清單。沒填技能名稱：另外累計次數並保留訊息連結，
      方便事後回頭點開連結辨認這次到底是什麼技能。
    沒有進行中的紀錄時完全不影響原有功能。"""
    if target_type != 'channel' or bonus_dice != 0:
        return
    record_growth_result(
        message.guild.id, message.channel.id, message.author.id,
        skill_name, skill_value, level, link=message.jump_url,
    )

def growth_names_for_direct_values(message, skill_names, skill_values):
    """「.cc 80 鬥毆」這種『先打數值、再打技能名』的直接指定寫法，決定每一格成長要用什麼名稱記。
    只有當『指定的數值 == 本頻道啟用角色卡上該技能的實際值』時，才算「真的用這張卡的技能擲的」，
    回傳該技能的正式名稱（＝照常計入具名成長）；被蓋成別的數值時視同臨時修正，不列入成長。
    回傳與輸入等長的清單，每一格為：
      - 非空字串：計入該技能的具名成長（用卡上的正式技能名）
      - ""       ：純數字沒填名稱（例如「.cc 80」），維持原本「未具名計次」的行為
      - None     ：有填名稱但數值和卡值不符／查無此技能，完全不列入成長（比照帶 +/- 修正的排除）
    沒填名稱、沒啟用角色卡、卡上查無該技能、或名稱同時符合多個技能而無法確定時，都不計入具名成長。"""
    guild_id, channel_id, user_id = message.guild.id, message.channel.id, message.author.id
    skill_lookup = None  # 延後到真的遇到具名格才載入角色卡；全是純數字時完全不載入
    result = []
    for name, value in zip(skill_names, skill_values):
        if not name:
            result.append("")            # 純數字（例如「.cc 80」）：沿用原本的未具名計次
            continue
        if skill_lookup is None:
            active_alias = pc_active_manager.get_active(guild_id, channel_id, user_id)
            card = pc_card_manager.get_card(guild_id, user_id, active_alias) if active_alias else None
            skill_lookup = build_pc_skill_lookup(card) if card else {}
        matches = fuzzy_match_skill(skill_lookup, name)
        if len(matches) == 1 and matches[0][1] == value:
            result.append(matches[0][0])  # 指定值＝卡值：照常計入該技能成長（用卡上的正式名稱）
        else:
            result.append(None)           # 蓋成別的數值／查無此技能：不列入成長
    return result

def maybe_trigger_madness_check(message, skill_name, skill_value, level, final_roll):
    """若該使用者在本頻道有「單次損失超過5點SAN、等待下一步智力檢定」的暫存狀態，且這次檢定是智力檢定，
    就消耗掉這個狀態：若檢定成功（含大成功/極限成功/困難成功/一般成功），角色陷入瘋狂，
    若本頻道有進行中的 .start～.end 紀錄，也一併記錄到 .end 報告。
    回傳要附加在該行檢定結果後面的提示文字；不是智力檢定或沒有暫存狀態時回傳空字串。"""
    if skill_name not in ('智力', 'INT', 'int'):
        return ""
    guild_id, channel_id, user_id = message.guild.id, message.channel.id, message.author.id
    # 討論串視同母頻道：.sc 在母頻道超額損失後，到討論串接著 .cc 智力 一樣接得上（反之亦然）
    key = (guild_id, effective_channel_id(channel_id), user_id)
    pending = pending_madness_check.get(key)
    if not pending:
        return ""
    if time.time() >= pending['expire']:
        del pending_madness_check[key]
        return ""
    del pending_madness_check[key]
    if is_growable_success(level):
        extra = "\n💀 智力檢定成功，角色陷入瘋狂！"
        if growth_manager.is_active(guild_id, channel_id, user_id):
            growth_manager.record_madness(
                guild_id, channel_id, user_id,
                pending.get('alias'), pending.get('loss'), skill_value, final_roll, level, message.jump_url,
            )
            extra += "\n📈 已記錄至本頻道的成長清單（`.end` 查看）。"
        return extra
    return "\n🌫️ 智力檢定未成功，暫時逃過瘋狂。"

def _try_parse_int_list(s):
    try:
        return [int(x.strip()) for x in s.split(',')]
    except (ValueError, AttributeError):
        return None

async def handle_coc_roll(message, args, target_type, bonus_dice=0, forced_repeat=None):
    """forced_repeat：由 `.N cc ...`（多重擲骰前綴，見 _dot_multi）帶進來的重複次數，
    有給時直接套用（不論這次是純數值還是技能名稱查角色卡），蓋掉底下各自的次數判斷邏輯。"""
    if not args:
        await send_result(message, "❌ 缺少技能值", title="COC 檢定錯誤", color=0xff0000, target_type=target_type)
        return
    parts = args.split(maxsplit=1)
    skill_values_part = parts[0]
    skill_names_part = parts[1] if len(parts) > 1 else ""
    skill_values = _try_parse_int_list(skill_values_part)
    repeat_times = max(min(forced_repeat, 30), 1) if forced_repeat is not None else 1
    annotation = ""

    if skill_values is not None:
        skill_names = [x.strip() for x in skill_names_part.split(',')] if skill_names_part else []
        while len(skill_names) < len(skill_values):
            skill_names.append("")
        skill_mods = [0] * len(skill_values)
        # 直接指定數值（例如「.cc 80 鬥毆」）：只有指定值＝角色卡上該技能的值時才計入成長，
        # 被蓋成別的數值時不列入（詳見 growth_names_for_direct_values）。
        growth_names = growth_names_for_direct_values(message, skill_names, skill_values)
    else:
        # 沒給數值（例如「.cc 偵查」或「.cc 偵查,聆聽」）→ 從本頻道目前啟用的角色卡自動抓技能值
        # 技能名稱結尾可接 +N/-N 臨時修正（例如「.cc 敏捷+50」＝敏捷值加 50 後檢定，常見於持械備射先攻）
        # 要連續判定同一個技能請用 `.N cc 技能名`（見 _dot_multi 的 forced_repeat），
        # 例如 .5 cc 鬥毆；技能名稱後面不再吃獨立數字當次數。
        name_tokens = [t.strip() for t in re.split(r'[,\s]+', args.strip()) if t.strip()]
        if not name_tokens:
            await send_result(message, "技能值必須為數字，多個技能用逗號分隔", title="COC 檢定錯誤", color=0xff0000, target_type=target_type)
            return
        annotation = ""

        guild_id, channel_id, user_id = message.guild.id, message.channel.id, message.author.id
        # 角色卡改成「用到才載入」：像「.cc 55+50」這種純數字帶修正的寫法，沒有角色卡也能用
        active_alias = None
        skill_lookup = None

        async def _load_card_lookup():
            nonlocal active_alias, skill_lookup
            active_alias = pc_active_manager.get_active(guild_id, channel_id, user_id)
            if not active_alias:
                await send_result(message, "本頻道尚未啟用角色卡，請先用 `.pc` 叫出面板，按【啟用】選擇要使用的角色卡（面板的【查看】可以看你有哪些角色卡）。", title="COC 檢定錯誤", color=0xff0000, target_type=target_type)
                return False
            card = pc_card_manager.get_card(guild_id, user_id, active_alias)
            if not card:
                pc_active_manager.clear_active(guild_id, channel_id, user_id)
                await send_result(message, f"啟用中的角色卡「{active_alias}」已經不存在了，請用 `.pc` 面板的【啟用】重新選一張。", title="COC 檢定錯誤", color=0xff0000, target_type=target_type)
                return False
            skill_lookup = build_pc_skill_lookup(card)
            return True

        skill_values, skill_names, skill_mods, missing = [], [], [], []
        for name in name_tokens:
            base, mod = name, 0
            mod_m = re.match(r'^(.+?)([+-]\d+)$', name)
            if mod_m:
                base, mod = mod_m.group(1), int(mod_m.group(2))
            # 英文屬性縮寫別名（str/dex/pow/con/app/edu/siz/int，大小寫不拘）→ 翻成角色卡上的中文屬性名稱
            attr_alias = _ROLL20_ATTR_MAP.get(base.lower())
            if attr_alias:
                base = attr_alias
            # 純數字（含帶修正）→ 直接當技能值用，不需要角色卡；例如「55+50」或混寫「.cc 50,偵查」
            if base.isdigit():
                skill_values.append(int(base) + mod)
                skill_names.append(name if mod else "")
                skill_mods.append(mod)
                continue
            if skill_lookup is None:
                if not await _load_card_lookup():
                    return
            if base in skill_lookup:
                skill_values.append(skill_lookup[base] + mod)
                skill_names.append(f"{base}{mod:+d}" if mod else base)
                skill_mods.append(mod)
                continue
            matches = fuzzy_match_skill(skill_lookup, base)
            if len(matches) == 1:
                mn, mv = matches[0]
                skill_values.append(mv + mod)
                skill_names.append(f"{mn}{mod:+d}" if mod else mn)
                skill_mods.append(mod)
            elif len(matches) > 1:
                if mod:
                    await send_result(message, f"「{base}」在角色卡「{active_alias}」裡符合多個技能，帶 +/- 修正時請把技能名稱打完整（例如 `.cc 敏捷+50`）。", title="COC 檢定錯誤", color=0xff0000, target_type=target_type)
                    return
                embed = discord.Embed(
                    title="🔎 找到多個符合的技能",
                    description=f"「{name}」在角色卡「{active_alias}」裡符合多個技能，請選擇要檢定哪一個：",
                    color=0x00aaff,
                )
                view = PCSkillSelectView(message.author.id, message, bonus_dice, target_type, matches)
                await send_ephemeral_menu(message, embed, view)
                return
            else:
                missing.append(base)
        if missing:
            await send_result(message, f"在角色卡「{active_alias}」裡找不到技能：{'、'.join(missing)}", title="COC 檢定錯誤", color=0xff0000, target_type=target_type)
            return
        # 這條分支的成長歸屬維持原狀：從角色卡查到的技能記具名成長，純數字（skill_name 為空）記未具名計次。
        growth_names = list(skill_names)

    crit_range, fumble_range = get_effective_range(message)
    output_lines = []
    init_note = None
    team_note = None
    for i in range(repeat_times):
        for sv, sn, smod, gn in zip(skill_values, skill_names, skill_mods, growth_names):
            final_roll, level, bonus_desc, all_rolls = coc_check(sv, bonus_dice, crit_range, fumble_range)
            line = f"{sn} ({sv}%)" if sn else f"技能值 {sv}"
            if repeat_times > 1:
                line = f"第{i+1}次：{line}"
            line += f"\n{bonus_desc} → 最終擲骰 {final_roll} → **{level}**"
            line += maybe_trigger_madness_check(message, sn, sv, level, final_roll)
            output_lines.append(line)
            # smod != 0：帶 +/- 臨時修正的檢定不記入成長（比照獎勵骰/懲罰骰）。
            # gn is None：有填技能名稱但指定值蓋掉了角色卡的技能值（例如卡上鬥毆 50、卻打 .cc 80 鬥毆），
            #             同樣不列入成長。gn 為空字串＝純數字未具名計次，gn 有字＝計入該技能成長。
            if smod == 0 and gn is not None:
                maybe_record_growth(message, gn, sv, level, bonus_dice, target_type)
            if init_note is None and repeat_times == 1 and len(skill_values) == 1 and bonus_dice == 0:
                init_note = maybe_capture_init_roll(message, target_type, final_roll, level)
            if team_note is None and repeat_times == 1 and len(skill_values) == 1 and bonus_dice == 0:
                team_note = await maybe_capture_team_roll(message, target_type, sn, sv, final_roll, level)
    title = f"多重 COC 檢定（{repeat_times}次）" if repeat_times > 1 else "COC 七版檢定"
    if bonus_dice > 0:
        title += f" (+{bonus_dice}獎勵骰)"
    elif bonus_dice < 0:
        title += f" ({-bonus_dice}懲罰骰)"
    content = "\n\n".join(output_lines)
    if annotation:
        content = f"📝 {annotation}\n\n{content}"
    if init_note:
        content += init_note
    if team_note:
        content += team_note
    await send_result(message, content, title=title, target_type=target_type)

# ---------- 近戰對抗判定（.melee） ----------
# 依 CoC 第六版戰鬥規則整理：攻防雙方比較成功等級，等級高者獲勝；
# 平手時，對方選反擊則攻擊方獲勝，對方選迴避則迴避方獲勝；雙方都大失敗則無事發生。
MELEE_RANK = {"大失敗": 0, "失敗": 1, "一般成功": 2, "困難成功": 3, "極限成功": 4, "大成功": 5}
# 攻擊方擲出這兩種等級＝攻擊本身沒成功，直接視為沒打中，不發動防禦方的反擊／閃避判定。
MELEE_ATTACKER_FAIL_LEVELS = ("失敗", "大失敗")

def resolve_melee_outcome(attacker_level, defender_level, defender_choice):
    """defender_choice 為 'fight_back'（反擊）、'dodge'（閃避）或 'custom'（自訂）。
    回傳 'no_effect'（雙方都大失敗）、'attacker_hits'（攻擊方命中）、'defender_wins'（反擊命中／成功閃避）、
    'tie'（自訂平手，不自動判定，交給 GM 自己裁定）。"""
    a, d = MELEE_RANK[attacker_level], MELEE_RANK[defender_level]
    if a == 0 and d == 0:
        return "no_effect"
    if a > d:
        return "attacker_hits"
    if d > a:
        return "defender_wins"
    if defender_choice == "custom":
        return "tie"
    return "attacker_hits" if defender_choice == "fight_back" else "defender_wins"

def _melee_lookup_skill(guild_id, channel_id, user_id, skill_aliases):
    """依序嘗試 skill_aliases 裡的技能名稱，在該使用者本頻道啟用中的角色卡找數值（需唯一符合）。
    回傳 (技能顯示名稱, 數值)；沒有啟用角色卡或找不到就回傳 None。"""
    alias = pc_active_manager.get_active(guild_id, channel_id, user_id)
    if not alias:
        return None
    card = pc_card_manager.get_card(guild_id, user_id, alias)
    if not card:
        return None
    skill_lookup = build_pc_skill_lookup(card)
    for name in skill_aliases:
        matches = fuzzy_match_skill(skill_lookup, name)
        if len(matches) == 1:
            return matches[0]
    return None

def _melee_lookup_build(guild_id, channel_id, user_id):
    """抓該使用者本頻道啟用中角色卡的「體格（Build）」數值，戰技的體格比較用。
    沒有啟用角色卡、卡已不存在、或卡上沒填體格都回傳 None（呼叫端自行決定要不要套懲罰）。"""
    alias = pc_active_manager.get_active(guild_id, channel_id, user_id)
    if not alias:
        return None
    card = pc_card_manager.get_card(guild_id, user_id, alias)
    if not card:
        return None
    return card.get('build')

# 面板「📏 體格判定」的本頻道暫存：{(guild_id, channel_id, user_id): int}。
# 只給沒有體格資料（沒開卡或卡上沒填）的人用，不寫回角色卡；角色卡有值時一律優先用卡上的。
melee_build_temp = {}

def _melee_effective_build(guild_id, channel_id, user_id):
    """戰技實際採用的體格：角色卡優先，卡上沒有才退回「📏 體格判定」的本頻道暫存，都沒有回 None。"""
    card_build = _melee_lookup_build(guild_id, channel_id, user_id)
    if card_build is not None:
        return card_build
    return melee_build_temp.get((guild_id, channel_id, user_id))

def _melee_display_name(guild_id, channel_id, user):
    """戰技對抗顯示用的名稱：優先用本頻道啟用中的角色卡名稱，沒有啟用角色卡才退回 Discord 顯示名稱。"""
    alias = pc_active_manager.get_active(guild_id, channel_id, user.id)
    return alias if alias else user.display_name

def _melee_result_embed(atk_display_name, atk_skill_name, atk_value, atk_level, atk_roll, atk_bonus_desc, tail_lines, atk_note=None):
    lines = [
        f"⚔️ **{atk_display_name}** 的攻擊（{atk_skill_name or '技能值'} {atk_value}%）",
    ]
    if atk_note:
        lines.append(f"📝 {atk_note}")
    lines.append(f"{atk_bonus_desc} → 擲骰 {atk_roll} → **{atk_level}**")
    lines.append("")
    lines.extend(tail_lines)
    return discord.Embed(title="⚔️ 戰技結果", description="\n".join(lines), color=0x00aaff)

# ---------- 防禦方回應的共用結算 ----------
# .melee 戰技、.cc 對抗檢定、追逐面板的攻擊三個入口共用同一套「反擊／閃避」結算流程。
# 三者的按鈕都是 persistent view（timeout=None＋固定 custom_id，並在 on_ready 註冊），
# 結算需要的狀態存在 melee_pending_store，以對抗訊息的 message_id 為 key，因此
# 按鈕永不失效、bot 重啟後也還能按。
def _melee_partial_message(state):
    """用存下來的 channel_id／message_id 取回對抗訊息，用來把按鈕改成停用。
    頻道抓不到（bot 被踢出、頻道被刪、狀態缺 message_id）就回 None，結算照樣進行。"""
    channel = bot.get_channel(state.get('channel_id'))
    if channel is None or not state.get('message_id'):
        return None
    try:
        return channel.get_partial_message(state['message_id'])
    except AttributeError:
        return None


def _melee_new_state(kind, guild_id, channel_id, attacker, defender, atk_skill_name, atk_value,
                     atk_level, atk_roll, atk_bonus_desc, atk_display_name, def_display_name, atk_note=None):
    """組出一筆待結算狀態。只存 id 與顯示名稱、不存 Member 物件，才寫得進 JSON、跨重啟還原得回來。
    kind 為 'melee'（戰技／追逐攻擊）或 'cc'（.cc 對抗檢定），決定結果文案與是否記成長。"""
    return {
        'kind': kind,
        'guild_id': guild_id,
        'channel_id': channel_id,
        'attacker_id': attacker.id,
        'defender_id': defender.id,
        'atk_skill_name': atk_skill_name,
        'atk_value': atk_value,
        'atk_level': atk_level,
        'atk_roll': atk_roll,
        'atk_bonus_desc': atk_bonus_desc,
        'atk_display_name': atk_display_name,
        'def_display_name': def_display_name,
        'atk_note': atk_note,
    }


def _melee_register_pending(sent, state):
    """對抗訊息送出後才拿得到 message_id，這裡補進狀態並寫檔。"""
    state['message_id'] = sent.id
    melee_pending_store.put(sent.id, state)


def _melee_default_skill_aliases(state, choice):
    """按鈕沒帶技能名稱時，要拿哪些技能名稱依序去查防禦方的角色卡。
    戰技的反擊是「打啥抓啥」：優先用攻擊方這次實際用的技能名稱，查不到才退回「鬥毆」「格鬥」；
    .cc 對抗的反擊固定用「鬥毆」「格鬥」，免得被攻擊方的技能名稱帶偏。
    兩者的閃避都固定依序試「閃避」「迴避」，與攻擊方用什麼技能無關。"""
    if choice == 'dodge':
        return ("閃避", "迴避")
    if state['kind'] == 'melee' and state.get('atk_skill_name'):
        return (state['atk_skill_name'], "鬥毆", "格鬥")
    return ("鬥毆", "格鬥")


def _melee_build_tail(state, choice, def_skill_name, def_value, def_roll, def_level, def_bonus_desc):
    """戰技（含追逐攻擊）的結果尾段，回傳 (outcome, 行列表)。"""
    outcome = resolve_melee_outcome(state['atk_level'], def_level, choice)
    choice_label = "反擊" if choice == 'fight_back' else "閃避"
    def_display_name = state['def_display_name']
    tail = [
        f"🛡️ **{def_display_name}** 選擇【{choice_label}】（{def_skill_name or '技能值'} {def_value}%）",
        f"{def_bonus_desc} → 擲骰 {def_roll} → **{def_level}**",
        "",
    ]
    if outcome == "no_effect":
        tail.append("💨 雙方都大失敗，這次交手沒有造成任何影響。")
    elif outcome == "attacker_hits":
        tail.append(f"🩸 **{state['atk_display_name']} 命中！**")
        if state['atk_level'] in ("極限成功", "大成功"):
            tail.append("（自己回合主動攻擊且達到極限/大成功：傷害取最大值；貫穿武器再多投一次傷害骰疊加。）")
    else:  # defender_wins
        if choice == 'fight_back':
            tail.append(f"🩸 **{def_display_name} 反擊命中！**（反擊不適用極限/大成功的最大傷害加成）")
        else:
            tail.append(f"🍃 **{def_display_name} 成功閃避，沒有受到傷害。**")
    return outcome, tail


def _cc_build_tail(state, choice, def_skill_name, def_value, def_roll, def_level, def_bonus_desc):
    """.cc 對抗檢定的結果尾段。多一個【自訂】選項，平手時不自動裁定勝負。"""
    outcome = resolve_melee_outcome(state['atk_level'], def_level, choice)
    choice_label = {"fight_back": "反擊", "dodge": "閃避", "custom": "自訂"}[choice]
    def_display_name = state['def_display_name']
    tail = [
        f"🛡️ **{def_display_name}** 選擇【{choice_label}】（{def_skill_name or '技能值'} {def_value}%）",
        f"{def_bonus_desc} → 擲骰 {def_roll} → **{def_level}**",
        "",
    ]
    if outcome == "no_effect":
        tail.append("💨 雙方都大失敗，這次對抗沒有造成任何影響。")
    elif outcome == "tie":
        tail.append("⚖️ **雙方成功等級相同，平手。**（自訂判定不自動裁定勝負，交給 GM 自行判斷）")
    elif outcome == "attacker_hits":
        tail.append(f"✅ **{state['atk_display_name']} 的檢定生效！**")
    else:  # defender_wins
        if choice == 'fight_back':
            tail.append(f"🗡️ **{def_display_name} 反擊成功！**（成功等級高於攻擊方，逆轉了結果）")
        elif choice == 'dodge':
            tail.append(f"🍃 **{def_display_name} 成功閃避，沒有受到影響。**")
        else:
            tail.append(f"🛠️ **{def_display_name} 的對抗判定成功！**（成功等級高於攻擊方，逆轉了結果）")
    return outcome, tail


async def _melee_disable_buttons(state):
    """結算完把原對抗訊息的按鈕改成停用（保留在畫面上，只是按不下去）。"""
    pm = _melee_partial_message(state)
    if pm is None:
        return
    view = CCOpposedView() if state['kind'] == 'cc' else MeleeResponseView()
    for child in view.children:
        child.disabled = True
    try:
        await pm.edit(view=view)
    except discord.HTTPException:
        pass


async def _melee_finish(interaction, state, choice, def_skill_name, def_value):
    """取得防禦方的技能值之後的共用結算。先把待結算狀態取走——pop 同時扮演
    「這場還沒結算過」的鎖，擋掉連點兩下或按鈕與表單重複送出的情況。"""
    if melee_pending_store.pop(state.get('message_id')) is None:
        await interaction.response.send_message("這場對抗已經結算過了。", ephemeral=True)
        return
    guild_id, channel_id = state['guild_id'], state['channel_id']
    crit_range, fumble_range = get_effective_range(_IdOnlyMessageShim(guild_id, channel_id))
    def_roll, def_level, def_bonus_desc, _ = coc_check(def_value, 0, crit_range, fumble_range)

    if state['kind'] == 'cc':
        # 防禦方的對抗檢定也記入成長清單（防禦方沒有獎懲骰；沒填技能名稱時用對抗訊息本身當連結）
        pm = _melee_partial_message(state)
        record_growth_result(
            guild_id, channel_id, state['defender_id'],
            def_skill_name, def_value, def_level,
            link=pm.jump_url if pm else None,
        )
        _, tail = _cc_build_tail(state, choice, def_skill_name, def_value, def_roll, def_level, def_bonus_desc)
    else:
        _, tail = _melee_build_tail(state, choice, def_skill_name, def_value, def_roll, def_level, def_bonus_desc)

    embed = _melee_result_embed(
        state['atk_display_name'], state['atk_skill_name'], state['atk_value'],
        state['atk_level'], state['atk_roll'], state['atk_bonus_desc'], tail,
        atk_note=state.get('atk_note'),
    )
    if state['kind'] == 'cc':
        embed.title = "🎲 CC 對抗結果"
    await interaction.response.send_message(embed=embed)
    await _melee_disable_buttons(state)


class _MeleeDefenseViewBase(discord.ui.View):
    """反擊／閃避按鈕的共用底層。是 persistent view：實例不帶任何狀態，
    按下按鈕時才用 interaction.message.id 去 melee_pending_store 撈出這場對抗的資料，
    所以同一個實例可以服務所有頻道的所有對抗，重啟後也接得回去。"""
    SKILL_MODAL = None

    def __init__(self):
        super().__init__(timeout=None)

    async def _pending(self, interaction):
        """取出這則訊息對應的待結算狀態；已結算或不是防禦方本人就回 None（並已回覆使用者）。"""
        state = melee_pending_store.get(interaction.message.id)
        if state is None:
            await interaction.response.send_message("這場對抗已經結算過了。", ephemeral=True)
            return None
        if interaction.user.id != state['defender_id']:
            await interaction.response.send_message("這不是你的行動，請等防禦方本人操作。", ephemeral=True)
            return None
        return state

    async def _choose(self, interaction, choice):
        """先試著從防禦方啟用中的角色卡自動抓技能值，抓不到才跳表單讓本人手動填。"""
        state = await self._pending(interaction)
        if state is None:
            return
        found = _melee_lookup_skill(
            state['guild_id'], state['channel_id'], state['defender_id'],
            _melee_default_skill_aliases(state, choice),
        )
        if found:
            name, value = found
            await _melee_finish(interaction, state, choice, name, value)
        else:
            await interaction.response.send_modal(self.SKILL_MODAL(state, choice))


class MeleeSkillModal(discord.ui.Modal, title="輸入技能值"):
    """防禦方沒開角色卡、或角色卡上找不到對應技能時，跳出這個視窗讓本人手動輸入
    要用來反擊／閃避的技能值，送出後直接進行判定。"""
    def __init__(self, state, choice):
        super().__init__()
        self.state = state
        self.choice = choice
        skill_hint = _melee_default_skill_aliases(state, choice)[0]
        self.value_input = discord.ui.TextInput(label=f"{skill_hint}技能值", placeholder="例如 55", max_length=5)
        self.add_item(self.value_input)

    async def on_submit(self, interaction: discord.Interaction):
        raw = str(self.value_input.value).strip()
        if not raw.isdigit():
            await interaction.response.send_message("技能值必須是數字。", ephemeral=True)
            return
        skill_name = _melee_default_skill_aliases(self.state, self.choice)[0]
        await _melee_finish(interaction, self.state, self.choice, skill_name, int(raw))


class MeleeResponseView(_MeleeDefenseViewBase):
    """近戰對抗：攻擊方擲骰後發這則訊息 @防禦方，讓本人選【反擊】或【閃避】。
    按鈕不會過期，防禦方隔幾天回來按也還能結算。"""
    SKILL_MODAL = MeleeSkillModal

    @discord.ui.button(label="🗡️ 反擊", style=discord.ButtonStyle.danger, custom_id="melee_def:fight_back")
    async def fight_back_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self._choose(interaction, 'fight_back')

    @discord.ui.button(label="🍃 閃避", style=discord.ButtonStyle.primary, custom_id="melee_def:dodge")
    async def dodge_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self._choose(interaction, 'dodge')


# ---------- 戰技體格（Build）補值流程 ----------
def _melee_build_line(atk_name, atk_build, def_name, def_build, build_penalty):
    """戰技訊息裡顯示的體格比較行。"""
    return f"體格比較：{atk_name} {atk_build} vs {def_name} {def_build}" + (
        f" → 攻擊方加 {build_penalty} 顆懲罰骰" if build_penalty else " → 不加懲罰骰"
    )

def _melee_build_block_embed(atk_name, atk_build, def_name, def_build, build_diff):
    """對方體格大 3 以上 → 戰技直接無效的公告 embed。"""
    return discord.Embed(
        title="⚔️ 戰技無效",
        description=(
            f"**{atk_name}**（體格 {atk_build}）想對 **{def_name}**（體格 {def_build}）發動戰技，\n"
            f"但對方體格大了 **{build_diff}**（≧3）——體格差距太大，戰技直接無效，不進行擲骰。"
        ),
        color=0x999999,
    )

async def _melee_roll_and_launch(message, attacker, defender, atk_skill_name, atk_value, atk_display_name, def_display_name, build_line, build_penalty, interaction=None, atk_note=None):
    """體格確定後的共用流程：擲攻擊骰（套體格懲罰骰）→ 攻擊方失敗直接收場，
    否則發出反擊／閃避的對抗訊息。由戰技面板表單、體格補值表單／跳過按鈕呼叫；
    interaction 有給的話用它回覆（按鈕／表單的正常回應管道），沒有就直接發頻道訊息。
    message 只拿來取 guild／channel 脈絡（面板流程會傳面板那則訊息），攻擊方一律用 attacker。"""
    crit_range, fumble_range = get_effective_range(message)
    atk_roll, atk_level, atk_bonus_desc, _ = coc_check(atk_value, -build_penalty, crit_range, fumble_range)
    note_line = f"📝 {atk_note}\n" if atk_note else ""

    async def _send(embed, view=None):
        if interaction is not None:
            if view is not None:
                await interaction.response.send_message(embed=embed, view=view)
            else:
                await interaction.response.send_message(embed=embed)
            return await interaction.original_response()
        if view is not None:
            return await message.channel.send(embed=embed, view=view)
        return await message.channel.send(embed=embed)

    if atk_level in MELEE_ATTACKER_FAIL_LEVELS:
        # 攻擊方自己就沒成功，不需要防禦方反擊／閃避，直接判定沒打中。
        embed = discord.Embed(
            title="⚔️ 戰技",
            description=(
                f"**{atk_display_name}** 對 **{def_display_name}** 發動近戰攻擊！\n"
                f"（{atk_skill_name or '技能值'} {atk_value}%）\n"
                f"{note_line}"
                f"{build_line}\n"
                f"{atk_bonus_desc} → 擲骰 {atk_roll} → **{atk_level}**\n\n"
                f"💨 攻擊方失敗，攻擊沒有命中，不會觸發 {def_display_name} 的反擊／閃避判定。"
            ),
            color=0x999999,
        )
        await _send(embed)
        return

    view = MeleeResponseView()
    embed = discord.Embed(
        title="⚔️ 戰技",
        description=(
            f"**{atk_display_name}** 對 **{def_display_name}** 發動近戰攻擊！\n"
            f"（{atk_skill_name or '技能值'} {atk_value}%）\n"
            f"{note_line}"
            f"{build_line}\n"
            f"{atk_bonus_desc} → 擲骰 {atk_roll} → **{atk_level}**\n\n"
            f"{defender.mention} 請選擇要【反擊】還是【閃避】。\n"
            f"按鈕不會過期，晚一點再回來按也可以。"
        ),
        color=0x00aaff,
    )
    sent = await _send(embed, view)
    _melee_register_pending(sent, _melee_new_state(
        'melee', message.guild.id, message.channel.id, attacker, defender,
        atk_skill_name, atk_value, atk_level, atk_roll, atk_bonus_desc,
        atk_display_name, def_display_name, atk_note=atk_note,
    ))

class MeleeBuildModal(discord.ui.Modal, title="填寫體格"):
    """補上體格（Build），可填負數（例如 -2）。
    只缺防禦方體格時只會有一欄（防禦方本人或 GM 填）；缺攻擊方時會有兩欄，已知的一方預填可直接沿用。
    送出後照 CoC 7e 戰技規則判定：差 1／2 → 懲罰骰，差 3 以上 → 戰技無效。"""
    def __init__(self, prompt_view):
        super().__init__()
        self.prompt_view = prompt_view
        self.atk_input = None
        if not prompt_view.defender_only:
            self.atk_input = discord.ui.TextInput(
                label=(f"攻擊方 {prompt_view.atk_display_name} 的體格")[:45],
                placeholder="例如 1 或 -2",
                default=str(prompt_view.atk_build) if prompt_view.atk_build is not None else None,
                max_length=4,
            )
            self.add_item(self.atk_input)
        self.def_input = discord.ui.TextInput(
            label=(f"防禦方 {prompt_view.def_display_name} 的體格")[:45],
            placeholder="例如 1 或 -2",
            default=str(prompt_view.def_build) if prompt_view.def_build is not None else None,
            max_length=4,
        )
        self.add_item(self.def_input)

    async def on_submit(self, interaction: discord.Interaction):
        pv = self.prompt_view
        if pv.done:
            await interaction.response.send_message("這次戰技已經處理完了。", ephemeral=True)
            return

        def _parse(raw):
            raw = str(raw).strip()
            try:
                return int(raw)
            except ValueError:
                return None

        atk_build = pv.atk_build if self.atk_input is None else _parse(self.atk_input.value)
        def_build = _parse(self.def_input.value)
        if atk_build is None or def_build is None:
            await interaction.response.send_message("體格必須是整數（可為負數），例如 1 或 -2。", ephemeral=True)
            return

        pv.done = True
        pv.stop()
        await pv.finish_buttons()
        # 防禦方的體格順手寫進本頻道暫存（不動角色卡），下次對同一人發戰技就不用再問
        melee_build_temp[(pv.message.guild.id, pv.message.channel.id, pv.defender.id)] = def_build
        build_diff = def_build - atk_build
        if build_diff >= 3:
            await interaction.response.send_message(embed=_melee_build_block_embed(pv.atk_display_name, atk_build, pv.def_display_name, def_build, build_diff))
            return
        build_penalty = build_diff if build_diff > 0 else 0
        build_line = _melee_build_line(pv.atk_display_name, atk_build, pv.def_display_name, def_build, build_penalty)
        await _melee_roll_and_launch(pv.message, pv.attacker, pv.defender, pv.atk_skill_name, pv.atk_value, pv.atk_display_name, pv.def_display_name, build_line, build_penalty, interaction=interaction, atk_note=pv.atk_note)

class MeleeBuildPromptView(discord.ui.View):
    """`.melee` 抓不到體格時的補值介面。
    只缺防禦方體格（defender_only）→ 由防禦方本人或 GM 按「📝 填寫體格」跳表單補值（表單只有本人看得到）；
    缺攻擊方體格 → 由發起人或 GM 填，兩欄表單，已知的一方預填。
    也可以按「⏭️ 跳過體格比較」不套懲罰直接擲骰；逾時（180 秒）本次判定作廢，不會擲骰。"""
    def __init__(self, message, attacker, defender, atk_skill_name, atk_value, atk_display_name, def_display_name, atk_build, def_build, atk_note=None):
        super().__init__(timeout=180)
        self.message = message
        self.attacker = attacker
        self.defender = defender
        self.atk_skill_name = atk_skill_name
        self.atk_value = atk_value
        self.atk_display_name = atk_display_name
        self.def_display_name = def_display_name
        self.atk_build = atk_build
        self.def_build = def_build
        self.atk_note = atk_note
        self.defender_only = atk_build is not None and def_build is None
        self.done = False
        self.sent_message = None

    def _allowed(self, user_id):
        if is_gm(self.message.guild.id, self.message.channel.id, user_id):
            return True
        if self.defender_only:
            return user_id == self.defender.id
        return user_id == self.attacker.id

    def _denied_text(self):
        who = "防禦方本人" if self.defender_only else "發起人"
        return f"只有{who}或本頻道 GM 可以操作這顆按鈕。"

    async def finish_buttons(self):
        for child in self.children:
            child.disabled = True
        if self.sent_message:
            try:
                await self.sent_message.edit(view=self)
            except discord.HTTPException:
                pass

    @discord.ui.button(label="📝 填寫體格", style=discord.ButtonStyle.primary)
    async def fill_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if self.done:
            await interaction.response.send_message("這次戰技已經處理完了。", ephemeral=True)
            return
        if not self._allowed(interaction.user.id):
            await interaction.response.send_message(self._denied_text(), ephemeral=True)
            return
        await interaction.response.send_modal(MeleeBuildModal(self))

    @discord.ui.button(label="⏭️ 跳過體格比較", style=discord.ButtonStyle.secondary)
    async def skip_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if self.done:
            await interaction.response.send_message("這次戰技已經處理完了。", ephemeral=True)
            return
        if not self._allowed(interaction.user.id):
            await interaction.response.send_message(self._denied_text(), ephemeral=True)
            return
        self.done = True
        self.stop()
        await self.finish_buttons()
        build_line = "體格比較：已跳過，未套用體格懲罰（需要的話請 KP 手動處理）"
        await _melee_roll_and_launch(self.message, self.attacker, self.defender, self.atk_skill_name, self.atk_value, self.atk_display_name, self.def_display_name, build_line, 0, interaction=interaction, atk_note=self.atk_note)

    async def on_timeout(self):
        # 逾時 → 本次判定作廢：按鈕失效、標註作廢，不擲骰、不發任何結算。
        if self.done:
            return
        self.done = True
        await self.finish_buttons()
        if self.sent_message:
            try:
                embed = self.sent_message.embeds[0] if self.sent_message.embeds else discord.Embed(color=0x999999)
                embed.color = 0x999999
                embed.description = (embed.description or "") + "\n\n⏳ **已逾時，本次判定作廢。** 需要的話請重新輸入 `.melee`。"
                await self.sent_message.edit(embed=embed, view=self)
            except discord.HTTPException:
                pass

# ---------- 戰技面板（.melee） ----------
async def _melee_start(message, attacker, defender, atk_skill_name, atk_value, atk_display_name, atk_build, interaction, atk_note=None):
    """戰技判定的共同入口（面板表單送出後呼叫）：抓防禦方體格（角色卡優先、暫存備援）→
    雙方齊了就比較體格並開骰；缺體格就發補值提示（逾時本次判定作廢）。回覆一律走 interaction。"""
    guild_id, channel_id = message.guild.id, message.channel.id
    def_display_name = _melee_display_name(guild_id, channel_id, defender)
    def_build = _melee_effective_build(guild_id, channel_id, defender.id)

    if atk_build is not None and def_build is not None:
        build_diff = def_build - atk_build
        if build_diff >= 3:
            await interaction.response.send_message(embed=_melee_build_block_embed(atk_display_name, atk_build, def_display_name, def_build, build_diff))
            return
        build_penalty = build_diff if build_diff > 0 else 0  # 大1／大2 → 1／2 顆懲罰骰
        build_line = _melee_build_line(atk_display_name, atk_build, def_display_name, def_build, build_penalty)
        await _melee_roll_and_launch(message, attacker, defender, atk_skill_name, atk_value, atk_display_name, def_display_name, build_line, build_penalty, interaction=interaction, atk_note=atk_note)
        return

    prompt_view = MeleeBuildPromptView(message, attacker, defender, atk_skill_name, atk_value, atk_display_name, def_display_name, atk_build, def_build, atk_note=atk_note)
    if prompt_view.defender_only:
        embed = discord.Embed(
            title="⚔️ 戰技：需要防禦方體格",
            description=(
                f"**{atk_display_name}**（體格 {atk_build}）想對 **{def_display_name}** 發動戰技（{atk_skill_name or '技能值'} {atk_value}%），\n"
                f"但抓不到 **{def_display_name}** 的體格（沒開角色卡或卡上沒填）。\n\n"
                f"{defender.mention} 請按「📝 填寫體格」填入你的體格（表單只有你自己看得到，GM 也可代填），\n"
                f"或按「⏭️ 跳過體格比較」不套懲罰直接擲骰。180 秒沒操作本次判定作廢。"
            ),
            color=0xffaa00,
        )
    else:
        missing = []
        if atk_build is None:
            missing.append(f"攻擊方 {atk_display_name}")
        if def_build is None:
            missing.append(f"防禦方 {def_display_name}")
        embed = discord.Embed(
            title="⚔️ 戰技：需要體格資料",
            description=(
                f"**{atk_display_name}** 想對 **{def_display_name}** 發動戰技（{atk_skill_name or '技能值'} {atk_value}%），\n"
                f"但抓不到 **{'、'.join(missing)}** 的體格（沒開角色卡或卡上沒填）。\n\n"
                f"請 **發起人或 GM** 按「📝 填寫體格」補上數值（可填負數），或按「⏭️ 跳過體格比較」直接擲骰。\n"
                f"180 秒沒操作本次判定作廢。"
            ),
            color=0xffaa00,
        )
    await interaction.response.send_message(embed=embed, view=prompt_view)
    try:
        prompt_view.sent_message = await interaction.original_response()
    except discord.HTTPException:
        pass

class MeleeManeuverModal(discord.ui.Modal, title="戰技判定"):
    """面板「🗡️ 戰技判定」選完對象後的表單。三欄都可留空：
    技能留空 → 抓按按鈕者角色卡的「鬥毆→格鬥」；NPC 名稱有填 → 以 NPC 名義出手（技能請直接給數值）；
    體格留空 → 自動抓角色卡→「📏 體格判定」暫存，都沒有就走補值提示。"""
    def __init__(self, panel_message, defender):
        super().__init__()
        self.panel_message = panel_message
        self.defender = defender
        self.skill_input = discord.ui.TextInput(
            label="技能名稱或數值（留空抓你卡上的鬥毆→格鬥）",
            placeholder="例如 格鬥、55；留空自動抓",
            required=False,
            max_length=30,
        )
        self.name_input = discord.ui.TextInput(
            label="攻擊方名稱（替 NPC 出手才填）",
            placeholder="例如 邪教徒Ａ；留空＝你自己的角色",
            required=False,
            max_length=30,
        )
        self.build_input = discord.ui.TextInput(
            label="攻擊方體格（留空自動抓，可負數）",
            placeholder="例如 1 或 -2",
            required=False,
            max_length=4,
        )
        self.note_input = discord.ui.TextInput(
            label="備註（選填，會顯示在戰技結果裡）",
            placeholder="例如 偷襲、砍向後頸",
            required=False,
            max_length=100,
        )
        self.add_item(self.skill_input)
        self.add_item(self.name_input)
        self.add_item(self.build_input)
        self.add_item(self.note_input)

    async def on_submit(self, interaction: discord.Interaction):
        guild_id, channel_id, user_id = interaction.guild_id, interaction.channel_id, interaction.user.id
        raw_skill = str(self.skill_input.value or '').strip()
        npc_name = str(self.name_input.value or '').strip() or None
        raw_build = str(self.build_input.value or '').strip()

        # 攻擊方技能
        if raw_skill.isdigit():
            atk_skill_name, atk_value = ("鬥毆" if npc_name else ""), int(raw_skill)
        elif raw_skill:
            found = _melee_lookup_skill(guild_id, channel_id, user_id, (raw_skill,))
            if not found:
                await interaction.response.send_message(
                    f"在你本頻道啟用中的角色卡找不到技能「{raw_skill}」（或沒開角色卡／符合多筆）。\n"
                    f"請改打完整技能名稱，或直接填數值；替 NPC 出手請直接給數值。",
                    ephemeral=True,
                )
                return
            atk_skill_name, atk_value = found
        else:
            found = _melee_lookup_skill(guild_id, channel_id, user_id, ("鬥毆", "格鬥"))
            if not found:
                await interaction.response.send_message(
                    "技能留空會自動抓你角色卡的「鬥毆→格鬥」，但你本頻道沒有啟用角色卡（或卡上沒這兩項技能）。\n"
                    "請在表單裡直接填技能名稱或數值。",
                    ephemeral=True,
                )
                return
            atk_skill_name, atk_value = found

        # 攻擊方體格：表單優先 → NPC 沒填就走補值提示 → 自己出手抓角色卡→體格判定暫存
        if raw_build:
            try:
                atk_build = int(raw_build)
            except ValueError:
                await interaction.response.send_message("體格必須是整數（可為負數），例如 1 或 -2。", ephemeral=True)
                return
        elif npc_name:
            atk_build = None
        else:
            atk_build = _melee_effective_build(guild_id, channel_id, user_id)

        atk_display_name = npc_name or _melee_display_name(guild_id, channel_id, interaction.user)
        atk_note = str(self.note_input.value or '').strip() or None
        await _melee_start(self.panel_message, interaction.user, self.defender, atk_skill_name, atk_value, atk_display_name, atk_build, interaction, atk_note=atk_note)

class MeleeTargetSelect(discord.ui.UserSelect):
    """面板「🗡️ 戰技判定」的成員選單：@成員選對抗對象，選完接著跳戰技表單。
    對方在本頻道啟用中的角色卡（名稱／體格）會在後續流程自動搜尋帶入。"""
    def __init__(self, panel_message):
        super().__init__(placeholder="選擇對抗對象（@成員）", min_values=1, max_values=1)
        self.panel_message = panel_message

    async def callback(self, interaction: discord.Interaction):
        target = self.values[0]
        if target.bot:
            await interaction.response.send_message("不能對機器人發動戰技。", ephemeral=True)
            return
        if target.id == interaction.user.id:
            await interaction.response.send_message("不能對自己發動戰技。", ephemeral=True)
            return
        await interaction.response.send_modal(MeleeManeuverModal(self.panel_message, target))

class MeleeTargetSelectView(discord.ui.View):
    def __init__(self, panel_message):
        super().__init__(timeout=180)
        self.add_item(MeleeTargetSelect(panel_message))

class MeleeSelfBuildModal(discord.ui.Modal, title="體格判定"):
    """面板「📏 體格判定」：沒有體格資料（沒開卡或卡上沒填）的人把自己的體格登記到本頻道暫存。
    不會寫回角色卡；角色卡之後補上體格的話一律優先用卡上的值。"""
    def __init__(self, current_temp=None):
        super().__init__()
        self.build_input = discord.ui.TextInput(
            label="你的體格（可負數）",
            placeholder="例如 1 或 -2",
            default=str(current_temp) if current_temp is not None else None,
            max_length=4,
        )
        self.add_item(self.build_input)

    async def on_submit(self, interaction: discord.Interaction):
        raw = str(self.build_input.value).strip()
        try:
            value = int(raw)
        except ValueError:
            await interaction.response.send_message("體格必須是整數（可為負數），例如 1 或 -2。", ephemeral=True)
            return
        melee_build_temp[(interaction.guild_id, interaction.channel_id, interaction.user.id)] = value
        await interaction.response.send_message(
            f"已記錄你在本頻道的體格 **{value}**（僅暫存，不會寫回角色卡；角色卡有體格時會優先用卡上的值）。",
            ephemeral=True,
        )

class MeleePanelView(discord.ui.View):
    """`.melee` 叫出的戰技面板。這是 persistent view（timeout=None＋每顆按鈕都有 custom_id，
    並在 on_ready 註冊）：面板永不失效，bot 重啟後舊面板的按鈕都還能按（頻道脈絡按下時
    從 interaction 現場取得，同一個 view 實例服務所有頻道）。"""
    def __init__(self):
        super().__init__(timeout=None)

    @discord.ui.button(label="🗡️ 戰技判定", style=discord.ButtonStyle.primary, row=0, custom_id="melee_panel:maneuver")
    async def maneuver_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        view = MeleeTargetSelectView(interaction.message)
        await interaction.response.send_message("請選擇對抗對象（選完會跳表單填技能）：", view=view, ephemeral=True)

    @discord.ui.button(label="📏 體格判定", style=discord.ButtonStyle.secondary, row=0, custom_id="melee_panel:build")
    async def build_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        guild_id, channel_id, user_id = interaction.guild_id, interaction.channel_id, interaction.user.id
        card_build = _melee_lookup_build(guild_id, channel_id, user_id)
        if card_build is not None:
            await interaction.response.send_message(
                f"你啟用中的角色卡已有體格 **{card_build}**，戰技會直接用卡上的值，不需要另外填。",
                ephemeral=True,
            )
            return
        current_temp = melee_build_temp.get((guild_id, channel_id, user_id))
        await interaction.response.send_modal(MeleeSelfBuildModal(current_temp))

# ---------- CC 對抗檢定（.cc 技能 @對方） ----------
# 跟 .melee 共用同一套結算邏輯（resolve_melee_outcome、_melee_finish、melee_pending_store），
# 差別在於 CC 是泛用技能檢定，不是固定的鬥毆/閃避，所以多一顆【自訂】按鈕讓防禦方
# 自己指定技能名稱與數值，而且平手時不自動裁定勝負。
class CCSkillModal(discord.ui.Modal, title="輸入技能值"):
    """防禦方沒開角色卡、或角色卡上找不到要用的技能時，跳出這個視窗讓本人手動輸入
    要用來反擊／閃避的技能值，送出後直接進行判定。"""
    def __init__(self, state, choice):
        super().__init__()
        self.state = state
        self.choice = choice
        choice_label = "反擊" if choice == 'fight_back' else "閃避"
        skill_hint = _melee_default_skill_aliases(state, choice)[0]
        self.value_input = discord.ui.TextInput(label=f"{choice_label}用的「{skill_hint}」技能值", placeholder="例如 55", max_length=5)
        self.add_item(self.value_input)

    async def on_submit(self, interaction: discord.Interaction):
        raw = str(self.value_input.value).strip()
        if not raw.isdigit():
            await interaction.response.send_message("技能值必須是數字。", ephemeral=True)
            return
        skill_name = _melee_default_skill_aliases(self.state, self.choice)[0]
        await _melee_finish(interaction, self.state, self.choice, skill_name, int(raw))


class CCCustomSkillModal(discord.ui.Modal, title="自訂技能"):
    """【自訂】按鈕：不管角色卡上找不找得到攻擊方那個技能，都讓防禦方自己打技能名稱＋技能值，
    送出後直接以「對抗判定」結算；平手時不自動判誰贏，只回報平手，交給 GM 自行裁定。"""
    def __init__(self, state):
        super().__init__()
        self.state = state
        self.name_input = discord.ui.TextInput(label="技能名稱", placeholder="例如 鬥毆", max_length=30)
        self.value_input = discord.ui.TextInput(label="技能值", placeholder="例如 55", max_length=5)
        self.add_item(self.name_input)
        self.add_item(self.value_input)

    async def on_submit(self, interaction: discord.Interaction):
        raw = str(self.value_input.value).strip()
        if not raw.isdigit():
            await interaction.response.send_message("技能值必須是數字。", ephemeral=True)
            return
        name = str(self.name_input.value).strip()
        await _melee_finish(interaction, self.state, 'custom', name, int(raw))


class CCOpposedView(_MeleeDefenseViewBase):
    """.cc 技能 @對方：CC 檢定的對抗版本。攻擊方擲骰後發這則訊息 @防禦方，
    讓本人選【反擊】【閃避】或【自訂】。反擊的成功等級要高於攻擊方才算成功，
    打平的話反擊算失敗、閃避算成功（沿用 resolve_melee_outcome 的判定）。
    按鈕不會過期，防禦方隔幾天回來按也還能結算。"""
    SKILL_MODAL = CCSkillModal

    @discord.ui.button(label="🗡️ 反擊", style=discord.ButtonStyle.danger, custom_id="cc_def:fight_back")
    async def fight_back_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self._choose(interaction, 'fight_back')

    @discord.ui.button(label="🍃 閃避", style=discord.ButtonStyle.primary, custom_id="cc_def:dodge")
    async def dodge_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self._choose(interaction, 'dodge')

    @discord.ui.button(label="🛠️ 自訂", style=discord.ButtonStyle.secondary, custom_id="cc_def:custom")
    async def custom_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        state = await self._pending(interaction)
        if state is None:
            return
        await interaction.response.send_modal(CCCustomSkillModal(state))


_CC_NOTE_SEP_RE = re.compile(r'[#｜|]')

def _split_cc_skill_and_note(skill_text):
    """把「技能(＋數值) # 備註」用 #／｜／| 分隔開來，回傳 (技能部分, 備註)。
    找不到分隔符號時備註回傳空字串，交給呼叫端自己再視情況嘗試自動拆分。"""
    m = _CC_NOTE_SEP_RE.search(skill_text)
    if m:
        return skill_text[:m.start()].strip(), skill_text[m.end():].strip()
    return skill_text.strip(), ""

async def handle_cc_opposed(message, skill_text, bonus_dice, defender):
    """.cc 技能 @對方（或 .ccn／.cc1／.cc2 等後綴一樣適用）：CC 檢定的對抗版本。
    攻擊方先擲一次骰，接著發訊息 @防禦方，提醒本人可以選擇【反擊】或【閃避】；
    反擊要嚴格高於攻擊方的成功等級才算成功，打平算反擊失敗、閃避成功。

    備註功能：技能／數值後面可以用 #／｜／| 隔開一段備註文字（例如「.cc 鬥毆#打敵人A @小明」），
    備註會直接顯示在對抗結果裡，不影響技能判定。
    沒有加分隔符號、備註直接黏在技能名稱或數值後面時（例如「鬥毆打敵人A」「50 打敵人A」），
    也會自動嘗試拆開：數值開頭的話，數值後面所有文字一律當備註；技能名稱開頭的話，
    用角色卡技能表做「最長比對」抓出實際的技能名稱，其餘文字當備註。"""
    skill_text = skill_text.strip()
    if not skill_text:
        await message.channel.send(embed=discord.Embed(
            title="❌ 缺少技能",
            description="請補上要檢定的技能名稱或數值，例如 `.cc 偵查 @小明` 或 `.cc 55 @小明`。",
            color=0xff0000,
        ))
        return

    guild_id, channel_id, user_id = message.guild.id, message.channel.id, message.author.id
    skill_part, note = _split_cc_skill_and_note(skill_text)
    if not skill_part:
        await message.channel.send(embed=discord.Embed(
            title="❌ 缺少技能",
            description="請補上要檢定的技能名稱或數值，例如 `.cc 偵查 @小明` 或 `.cc 55 @小明`。",
            color=0xff0000,
        ))
        return

    tokens = skill_part.split()
    # 單一英文屬性縮寫別名（str/dex/pow/con/app/edu/siz/int，大小寫不拘）→ 翻成中文屬性名稱
    if len(tokens) == 1:
        attr_alias = _ROLL20_ATTR_MAP.get(tokens[0].lower())
        if attr_alias:
            skill_part = attr_alias
            tokens = [attr_alias]
    m_lead_num = re.match(r'^(\d+)\s*(.+)$', skill_part)
    if len(tokens) >= 2 and tokens[-1].isdigit():
        # 手動指定「技能名稱 數值」，不需要先開角色卡
        atk_skill_name, atk_value = ' '.join(tokens[:-1]), int(tokens[-1])
    elif skill_part.isdigit():
        atk_skill_name, atk_value = "", int(skill_part)
    elif m_lead_num and not note:
        # 數值開頭、後面直接接文字，且沒用分隔符號（例如「50 打敵人A」「50打敵人A」）
        # → 數值後面全部當備註，不當技能名稱處理
        atk_skill_name, atk_value = "", int(m_lead_num.group(1))
        note = m_lead_num.group(2).strip()
    else:
        active_alias = pc_active_manager.get_active(guild_id, channel_id, user_id)
        if not active_alias:
            await message.channel.send(embed=discord.Embed(
                title="❌ 本頻道尚未啟用角色卡",
                description="請先用 `.pc` 叫出面板按【啟用】，或直接打技能數值，例如 `.cc 55 @小明`。",
                color=0xff0000,
            ))
            return
        card = pc_card_manager.get_card(guild_id, user_id, active_alias)
        if not card:
            pc_active_manager.clear_active(guild_id, channel_id, user_id)
            await message.channel.send(embed=discord.Embed(title="⚠️ 啟用中的角色卡已不存在，請用 `.pc` 面板的【啟用】重新選一張。", color=0xffaa00))
            return
        skill_lookup = build_pc_skill_lookup(card)
        matches = fuzzy_match_skill(skill_lookup, skill_part)
        if len(matches) == 1:
            atk_skill_name, atk_value = matches[0]
        elif len(matches) > 1:
            names = "、".join(n for n, _ in matches)
            await message.channel.send(embed=discord.Embed(title="❌ 符合多個技能", description=f"「{skill_part}」在角色卡「{active_alias}」裡符合多個技能：{names}，請打完整名稱，或用 `#` 隔開備註（例如 `.cc 鬥毆#備註 @小明`）。", color=0xff0000))
            return
        elif not note:
            # 完全比對不到，且沒用分隔符號 → 嘗試用「最長比對」自動從前面抓出技能名稱，
            # 剩下的文字當備註（例如「鬥毆打敵人A」自動拆成 技能=鬥毆／備註=打敵人A）。
            prefix_match = None
            for name, value in skill_lookup.items():
                if name and skill_part.startswith(name):
                    if prefix_match is None or len(name) > len(prefix_match[0]):
                        prefix_match = (name, value)
            if prefix_match:
                atk_skill_name, atk_value = prefix_match
                note = skill_part[len(atk_skill_name):].strip()
            else:
                await message.channel.send(embed=discord.Embed(title="❌ 找不到技能", description=f"在角色卡「{active_alias}」裡找不到技能「{skill_part}」。想加備註的話可以用 `#` 隔開，例如 `.cc 鬥毆#備註 @小明`。", color=0xff0000))
                return
        else:
            await message.channel.send(embed=discord.Embed(title="❌ 找不到技能", description=f"在角色卡「{active_alias}」裡找不到技能「{skill_part}」。", color=0xff0000))
            return

    atk_display_name = _melee_display_name(guild_id, channel_id, message.author)
    def_display_name = _melee_display_name(guild_id, channel_id, defender)
    crit_range, fumble_range = get_effective_range(message)
    atk_roll, atk_level, atk_bonus_desc, _ = coc_check(atk_value, bonus_dice, crit_range, fumble_range)
    # 攻擊方的對抗檢定一樣記入成長清單（帶獎懲骰時 maybe_record_growth 會自動略過，規則跟一般 .cc 相同）
    maybe_record_growth(message, atk_skill_name, atk_value, atk_level, bonus_dice, 'channel')
    note_line = f"\n📝 {note}" if note else ""

    if atk_level in MELEE_ATTACKER_FAIL_LEVELS:
        # 攻擊方自己就沒成功，不需要防禦方反擊／閃避，直接判定檢定沒過。
        embed = discord.Embed(
            title="🎲 CC 對抗檢定",
            description=(
                f"**{atk_display_name}** 對 **{def_display_name}** 發起了 **{atk_skill_name or '技能值'} {atk_value}%** 的檢定！{note_line}\n"
                f"{atk_bonus_desc} → 擲骰 {atk_roll} → **{atk_level}**\n\n"
                f"💨 攻擊方失敗，不會觸發 {def_display_name} 的反擊／閃避判定。"
            ),
            color=0x999999,
        )
        await message.channel.send(embed=embed)
        return

    view = CCOpposedView()
    embed = discord.Embed(
        title="🎲 CC 對抗檢定",
        description=(
            f"**{atk_display_name}** 對 **{def_display_name}** 發起了 **{atk_skill_name or '技能值'} {atk_value}%** 的檢定！{note_line}\n"
            f"{atk_bonus_desc} → 擲骰 {atk_roll} → **{atk_level}**\n\n"
            f"{defender.mention} 請選擇要【反擊】【閃避】還是【自訂】。\n"
            f"反擊骰值要高於攻擊方的成功等級才會成功，打平的話反擊算失敗；自訂可以自己打技能名稱＋技能值，固定算對抗判定（打平只會回報平手，不自動判誰贏，交給 GM 自行裁定）。\n"
            f"按鈕不會過期，晚一點再回來按也可以。"
        ),
        color=0x00aaff,
    )
    sent = await message.channel.send(embed=embed, view=view)
    _melee_register_pending(sent, _melee_new_state(
        'cc', guild_id, channel_id, message.author, defender,
        atk_skill_name, atk_value, atk_level, atk_roll, atk_bonus_desc,
        atk_display_name, def_display_name, atk_note=note,
    ))

async def handle_pbta_roll(message, args, target_type):
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
        content = f"MOVE：{move_name}\n骰子結果：{r1}+{r2} + {mod} = {total}\n判定結果：{result}"
    else:
        content = f"骰子結果：{r1}+{r2} + {mod} = {total}\n判定結果：{result}"
    await send_result(message, content, title="🎲 PBTA 擲骰", target_type=target_type)

def _is_plain_int(s):
    return re.fullmatch(r'-?\d+', s or '') is not None

SC_USAGE = "格式錯誤，請使用：\n`.sc 成功損失/失敗損失`　→ 自動抓本頻道啟用中角色卡的目前 SAN（例如 `.sc 1/1d6`）\n`.sc 目前SAN 成功損失/失敗損失`　→ 手動指定目前 SAN，不會更動角色卡（例如 `.sc 50 1/1d6`）"

async def handle_sc_roll(message, args, target_type):
    parts = args.split()
    manual_san = None
    success_loss = fail_loss = None

    if len(parts) == 1 and '/' in parts[0]:
        success_loss, fail_loss = parts[0].split('/', 1)
    elif len(parts) == 2 and _is_plain_int(parts[0]) and '/' in parts[1]:
        manual_san = int(parts[0])
        success_loss, fail_loss = parts[1].split('/', 1)
    elif len(parts) == 2 and not _is_plain_int(parts[0]):
        success_loss, fail_loss = parts[0], parts[1]
    elif len(parts) == 3 and _is_plain_int(parts[0]):
        manual_san = int(parts[0])
        success_loss, fail_loss = parts[1], parts[2]
    else:
        await send_result(message, SC_USAGE, title="SAN 檢定錯誤", color=0xff0000, target_type=target_type)
        return

    guild_id, channel_id, user_id = message.guild.id, message.channel.id, message.author.id
    card = None
    alias = None

    if manual_san is not None:
        current_san = manual_san
    else:
        # 自動模式：從本頻道啟用中的角色卡抓「目前 SAN」（SAN：目前／(不定性瘋狂線) 左邊那個數字）
        active_alias = pc_active_manager.get_active(guild_id, channel_id, user_id)
        if not active_alias:
            await send_result(message, "本頻道尚未啟用角色卡，請先用 `.pc` 叫出面板按【啟用】，或改用 `.sc 目前SAN 成功損失/失敗損失` 手動指定目前 SAN。", title="SAN 檢定錯誤", color=0xff0000, target_type=target_type)
            return
        card = pc_card_manager.get_card(guild_id, user_id, active_alias)
        if not card:
            pc_active_manager.clear_active(guild_id, channel_id, user_id)
            await send_result(message, f"啟用中的角色卡「{active_alias}」已經不存在了，請用 `.pc` 面板的【啟用】重新選一張。", title="SAN 檢定錯誤", color=0xff0000, target_type=target_type)
            return
        if card.get('san_cur') is None:
            await send_result(message, f"角色卡「{active_alias}」沒有紀錄目前 SAN 數值，請改用 `.sc 目前SAN 成功損失/失敗損失` 手動指定。", title="SAN 檢定錯誤", color=0xff0000, target_type=target_type)
            return
        alias = active_alias
        current_san = card['san_cur']

    roll = random.randint(1, 100)
    success = roll <= current_san
    if success:
        loss = roll_dice_expr(success_loss)
        result_text = f"理智檢定成功！損失 {loss} 點 SAN。"
    else:
        loss = roll_dice_expr(fail_loss)
        result_text = f"理智檢定失敗！損失 {loss} 點 SAN。"
    new_san = max(0, current_san - loss)
    content = f"目前 SAN：{current_san}\n擲骰結果：{roll}\n結果：{result_text}\n剩餘 SAN：{new_san}"

    if loss > 5:
        content += "\n⚠️ 單次損失超過 5 點 SAN！請接著進行下一步的**智力檢定**（例如 `.cc 智力`），若檢定成功，角色將陷入瘋狂。"
        pending_madness_check[(guild_id, effective_channel_id(channel_id), user_id)] = {
            'alias': alias,
            'loss': loss,
            'link': message.jump_url,
            'expire': time.time() + MADNESS_CHECK_TIMEOUT,
        }

    if card is not None:
        # 角色卡的「(不定性瘋狂線)」欄位存在 san_max 裡；剛跌破這條線才提醒一次
        threshold = card.get('san_max')
        if threshold is not None and new_san <= threshold and current_san > threshold:
            content += f"\n⚠️ 理智已降至不定性瘋狂線（{threshold}）或以下，角色陷入不定性瘋狂！"
        if new_san <= 0 and current_san > 0:
            content += "\n☠️ 理智已降至 0！"
        card['san_cur'] = new_san
        pc_card_manager.save_card(guild_id, user_id, alias, card)
        content += f"\n📋 已更新角色卡「{alias}」的 SAN 數值。"
        if growth_manager.is_active(guild_id, channel_id, user_id):
            growth_manager.record_san_loss(guild_id, channel_id, user_id, alias, roll, success, loss, new_san, message.jump_url)
            content += "\n📈 已記錄至本頻道的成長清單（`.end` 查看）。"

    color = 0x00aa00 if success else 0xaa0000
    await send_result(message, content, title="🧠 SAN 檢定", color=color, target_type=target_type)

async def handle_int_roll(message, args, target_type):
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
    if not expr:
        await send_result(message, "請提供表達式，例如：`5+3*2` 或 `(1D100+5)/2`", title="計算錯誤", color=0xff0000, target_type=target_type)
        return
    expr = remove_discord_emoji(expr)
    result, replaced = safe_compute_with_dice(expr)
    if result is not None:
        content = f"{expr}\n= {result}" if replaced != expr else f"{expr} = {result}"
        await send_result(message, content, title="📐 計算結果", target_type=target_type)
    else:
        await send_result(message, "表達式錯誤，請檢查算式", title="計算錯誤", color=0xff0000, target_type=target_type)

async def send_result(message, content, title=None, color=0x00aaff, target_type='channel'):
    embed = discord.Embed(title=title, description=content, color=color)
    embed.set_footer(text=message.author.display_name, icon_url=message.author.display_avatar.url)
    if target_type == 'channel':
        await message.channel.send(embed=embed)
    elif target_type == 'self':
        await send_private_embed(message, message.author, embed)
        await message.add_reaction('📬')
    elif target_type == 'gm':
        # 直接發給「這個頻道」登記的所有 GM，名單本身就是頻道專屬的，不需要再判斷權限
        guild_id = message.guild.id
        channel_id = message.channel.id
        gms = gm_manager.get_gm_users(guild_id, channel_id)

        if gms:
            alias = get_alias(guild_id, channel_id, message.author.id)
            dm_embed = embed.copy()
            if alias:
                # 發話者本人也登記為 GM 且有化名時，私訊裡的署名改用化名而非本名
                dm_embed.set_footer(text=alias)

            # 用 set 合併「頻道所有 GM」跟「自己」，避免發話者剛好也是本頻道 GM 時收到兩份重複訊息
            recipients = set(gms)
            recipients.add(message.author.id)
            for uid in recipients:
                user_obj = await resolve_member_by_id(message.guild, uid)
                if user_obj:
                    await send_private_embed(message, user_obj, dm_embed)
            await message.add_reaction('📬')
        else:
            await message.channel.send(embed=discord.Embed(title="⚠️ 本頻道未設定 GM", description="請使用 `.drgm addgm` 在本頻道登記 GM。", color=0xffaa00))
    elif target_type == 'gm_only':
        guild_id = message.guild.id
        channel_id = message.channel.id
        gms = gm_manager.get_gm_users(guild_id, channel_id)
        recipients_ids = set(gms)
        recipients_ids.discard(message.author.id)  # gm_only 一律不發給自己，不管自己是不是本頻道登記的 GM

        if not gms:
            await message.channel.send(embed=discord.Embed(title="⚠️ 本頻道未設定 GM", description="請使用 `.drgm addgm` 在本頻道登記 GM。", color=0xffaa00))
        elif not recipients_ids:
            # 本頻道唯一登記的 GM 就是發話者自己，dddr（僅 GM 可見）沒有其他人能收到
            await message.channel.send(embed=discord.Embed(title="❌ 觸發失敗", description="你是本頻道唯一登記的 GM，使用 `dddr`（僅 GM 可見）將導致沒有其他 GM 能接收此訊息。", color=0xff0000))
        else:
            alias = get_alias(guild_id, channel_id, message.author.id)
            dm_embed = embed.copy()
            dm_embed.title = f"{dm_embed.title}（僅 GM 可見）" if dm_embed.title else "僅 GM 可見"
            if alias:
                dm_embed.set_footer(text=alias)

            success_count = 0
            for uid in recipients_ids:
                user_obj = await resolve_member_by_id(message.guild, uid)
                if user_obj:
                    if await send_private_embed(message, user_obj, dm_embed):
                        success_count += 1
            if success_count > 0:
                await message.add_reaction('🔒')
            else:
                await message.channel.send(embed=discord.Embed(title="❌ 私訊失敗", description="無法私訊給本頻道任何 GM，請檢查對方的隱私設定。", color=0xff0000))

async def handle_roll(message, roll_expr, target_type='channel'):
    roll_expr = remove_discord_emoji(roll_expr)
    lower_expr = roll_expr.lower().strip()

    cc_match = re.match(r'^(cc|cc[12]|ccn[12]?|coc[12]?)(?:\s+(.*))?$', lower_expr, re.I)
    if cc_match:
        cmd_part = cc_match.group(1).lower()
        args = cc_match.group(2) or ""
        bonus_dice = cc_bonus_dice(cmd_part)
        await handle_coc_roll(message, args, target_type, bonus_dice)
        return

    sc_match = re.match(r'^sc\s+(.+)$', lower_expr, re.I)
    if sc_match:
        await handle_sc_roll(message, sc_match.group(1), target_type)
        return

    int_match = re.match(r'^int\s+(\d+)\s+(\d+)$', lower_expr)
    if int_match:
        await handle_int_roll(message, f"{int_match.group(1)} {int_match.group(2)}", target_type)
        return

    calc_match = re.match(r'^calc\s+(.+)$', lower_expr)
    if calc_match:
        await handle_calc_roll(message, calc_match.group(1), target_type)
        return

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

PC_CARD_TEMPLATE = (
    "角色名稱：XXX\n"
    "HP：10／10 MP：10／10\n"
    "SAN：50／(15) LUK：50\n"
    "力量：50 敏捷：50 意志：50\n"
    "體質：50 外貌：50 教育：50\n"
    "體型：50 智力：50 靈感：50\n"
    "體格：0　DB：0　MOV：8\n"
    "[技能列表]\n"
    "偵查：25\n"
    "聆聽：20\n"
    "[戰鬥列表]\n"
    "鬥毆：25\n"
    "[技能]\n"
    "拉丁文-語言：25"
)

def format_pc_card_as_editable_text(card):
    """把角色卡 dict 轉成跟 `.pc set` 貼上格式一樣的純文字，缺的數值標成 `?`，
    給編輯用的 Modal 當預填內容；使用者送出後會照原本 parse_pc_card_text 的規則重新解析一次
    （`?` 這種非數字內容會被規則直接忽略，等於維持「沒抓到」的狀態，不會誤存成奇怪的值）。"""
    def g(v):
        return v if v is not None else '?'
    attrs = card.get('attributes', {})
    def a(k):
        return attrs.get(k, '?')

    lines = [
        f"角色名稱：{card.get('name') or '?'}",
        f"HP：{g(card['hp_cur'])}／{g(card['hp_max'])} MP：{g(card['mp_cur'])}／{g(card['mp_max'])}",
        f"SAN：{g(card['san_cur'])}／({g(card['san_max'])}) LUK：{g(card['luck'])}",
        f"力量：{a('力量')} 敏捷：{a('敏捷')} 意志：{a('意志')}",
        f"體質：{a('體質')} 外貌：{a('外貌')} 教育：{a('教育')}",
        f"體型：{a('體型')} 智力：{a('智力')} 靈感：{g(card['idea'])}",
        f"體格：{g(card['build'])} DB：{g(card['db'])} MOV：{g(card['mov'])}",
    ]

    def add_section(header, items):
        if not items:
            return
        lines.append(f"[{header}]")
        for name, val in items:
            lines.append(f"{name}：{val}")

    add_section('技能列表', card.get('skills'))
    add_section('戰鬥列表', card.get('combat'))
    add_section('技能', card.get('extra_skills'))

    return "\n".join(lines)

class PcCardEditModal(discord.ui.Modal, title="✏️ 編輯角色卡"):
    """跟 `.save` 的跳出視窗同一套做法：一按按鈕就跳表單，填完送出才處理，不會在頻道裡一來一往洗版。
    Discord 一個 Modal 最多只能放 5 個欄位，角色卡欄位太多塞不下，所以用「一大塊可編輯文字」取代，
    送出後照 `.pc set` 貼文字一樣的規則重新解析。"""
    def __init__(self, message, card, alias_hint, stub_view=None):
        super().__init__()
        self.message = message
        self.original_card = card
        self.alias_hint = alias_hint
        self.stub_view = stub_view
        default_text = format_pc_card_as_editable_text(card)
        if len(default_text) > 4000:  # Modal 文字欄位上限是 4000 字，正常角色卡不會超過，這裡只是保險
            default_text = default_text[:4000]
        self.card_text = discord.ui.TextInput(
            label="角色卡內容（可貼 Roll20 匯入碼／? 代表待補值）",
            style=discord.TextStyle.paragraph,
            default=default_text,
            required=True,
            max_length=4000,
        )
        self.add_item(self.card_text)

    async def on_submit(self, interaction: discord.Interaction):
        # ephemeral defer：後續 followup（成功卡片內容或錯誤訊息）都只有本人看得到
        await interaction.response.defer(ephemeral=True)
        clean_text = remove_discord_emoji(str(self.card_text.value)).strip()
        new_card = None
        if _looks_like_roll20_json_text(clean_text):
            try:
                # strict=False：理由同 handle_pc_paste，Roll20 匯出的 JSON 常見未跳脫的實體換行
                parsed = json.loads(clean_text, strict=False)
            except (ValueError, TypeError):
                parsed = None
            if isinstance(parsed, list) and parsed and isinstance(parsed[0], dict):
                new_card = build_card_from_roll20(parsed[0])
                # Roll20 匯入碼本來就不含 MOV／體格／DB／長瘋線，編輯時直接沿用原本角色卡上已有的數值，
                # 不用像新建時再跳一次表單補值（原卡沒有的話就維持 None，一樣可以之後再手動 .pc adj 補上）。
                for key in ('mov', 'build', 'db', 'san_max'):
                    if new_card.get(key) is None:
                        new_card[key] = self.original_card.get(key)
            else:
                await interaction.followup.send(
                    "看起來像 Roll20 匯入碼，但無法解析內容，請確認貼的是完整的 JSON"
                    "（長得像 `[{\"character_name\":...}]`），或改貼文字團簡表格式。",
                    ephemeral=True,
                )
                return
        if new_card is None:
            new_card = parse_pc_card_text(clean_text)
        ok = await _finalize_pc_card_save(self.message, new_card, self.alias_hint, interaction=interaction)
        if ok and self.stub_view:
            await self.stub_view.close_stub()

class Roll20MissingFieldsModal(discord.ui.Modal, title="🧮 補上 Roll20 匯入碼沒有的數值"):
    """Roll20 版角色 JSON 不含 MOV／體格／DB／長瘋線 這幾個欄位，這裡先用角色卡上已有的
    STR／DEX／SIZ 幫忙算出建議值填進欄位，使用者可以直接用或自己改，
    送出後才會進到跟 `.pc set` 貼文字一樣的「是否有誤」最終確認流程。
    靈感（idea）不在這裡問，一律直接帶入智力的數值，在 build_card_from_roll20 就自動補好了。"""
    def __init__(self, message, card, alias_hint, stub_view=None, default_age=None, default_san_max=None):
        super().__init__()
        self.message = message
        self.card = card
        self.alias_hint = alias_hint
        self.stub_view = stub_view
        attrs = card.get('attributes') or {}
        sug_build, sug_db = _calc_build_db(attrs.get('力量'), attrs.get('體型'))
        self._base_mov_no_age = _calc_mov(attrs.get('力量'), attrs.get('敏捷'), attrs.get('體型'), None)
        sug_mov = _calc_mov(attrs.get('力量'), attrs.get('敏捷'), attrs.get('體型'), default_age)
        self.age_input = discord.ui.TextInput(
            label="年齡（用來抓 MOV 年齡修正，不會存進角色卡）",
            default=str(default_age) if default_age is not None else '',
            required=False, max_length=10,
        )
        self.mov_input = discord.ui.TextInput(
            label="MOV（移動速度）",
            default=str(sug_mov) if sug_mov is not None else '',
            required=False, max_length=10,
        )
        self.build_input = discord.ui.TextInput(
            label="體格（Build）",
            default=str(sug_build) if sug_build is not None else '',
            required=False, max_length=10,
        )
        self.db_input = discord.ui.TextInput(
            label="DB／傷害加成（例如 0／+1D4／+1D6）",
            default=sug_db or '',
            required=False, max_length=10,
        )
        self.san_max_input = discord.ui.TextInput(
            label="長瘋線（不定性瘋狂線，SAN／(這個數字)）",
            default=str(default_san_max) if default_san_max is not None else '',
            required=False, max_length=10,
        )
        self.add_item(self.age_input)
        self.add_item(self.mov_input)
        self.add_item(self.build_input)
        self.add_item(self.db_input)
        self.add_item(self.san_max_input)

    async def on_submit(self, interaction: discord.Interaction):
        await interaction.response.defer(ephemeral=True)
        age_txt = str(self.age_input.value).strip()
        mov_txt = str(self.mov_input.value).strip()
        build_txt = str(self.build_input.value).strip()
        db_txt = str(self.db_input.value).strip()
        san_max_txt = str(self.san_max_input.value).strip()
        age_val = _safe_int(age_txt) if age_txt else None
        mov_val = _safe_int(mov_txt) if mov_txt else None
        # 填了年齡、且 MOV 欄位還是視窗一開始「沒套年齡修正」的原始建議值（代表沒被手動改過），
        # 就順手用剛填的年齡重新算一次，避免使用者填了年齡卻忘記同步調整 MOV。
        if age_val is not None and mov_val == self._base_mov_no_age:
            attrs = self.card.get('attributes') or {}
            recalculated = _calc_mov(attrs.get('力量'), attrs.get('敏捷'), attrs.get('體型'), age_val)
            if recalculated is not None:
                mov_val = recalculated
        self.card['mov'] = mov_val
        self.card['build'] = _safe_int(build_txt) if build_txt else None
        self.card['db'] = db_txt or None
        self.card['san_max'] = _safe_int(san_max_txt) if san_max_txt else None
        await interaction.followup.send("已補上數值，接著請至下方訊息確認角色卡內容。", ephemeral=True)
        if self.stub_view:
            await self.stub_view.close_stub("📝 已補上 MOV／體格／DB／長瘋線，請至下方訊息確認角色卡內容。")
        await save_new_pc_card(self.message, self.card, self.alias_hint)

class Roll20FillMissingView(discord.ui.View):
    """Roll20 匯入碼一定不含 MOV／體格／DB／靈感，先發這則「存根」讓使用者按按鈕跳表單補值，
    填完才會走進原本 `.pc set` 那套「是否有誤」確認流程。"""
    def __init__(self, message, card, alias_hint, default_age=None, default_san_max=None):
        super().__init__(timeout=300)
        self.message = message
        self.card = card
        self.alias_hint = alias_hint
        self.default_age = default_age
        self.default_san_max = default_san_max
        self.author_id = message.author.id
        self.sent_message = None
        self.done = False

    async def close_stub(self, note):
        self.done = True
        self.stop()
        if self.sent_message:
            try:
                await self.sent_message.edit(content=note, view=None)
            except discord.HTTPException:
                pass

    @discord.ui.button(label="🧮 補上缺少的數值", style=discord.ButtonStyle.primary)
    async def fill_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.author_id:
            await interaction.response.send_message("這不是你的角色卡匯入，請自己用 `.pc` 面板的【建立】。", ephemeral=True)
            return
        await interaction.response.send_modal(
            Roll20MissingFieldsModal(
                self.message, self.card, self.alias_hint, stub_view=self,
                default_age=self.default_age, default_san_max=self.default_san_max,
            )
        )

    async def on_timeout(self):
        if self.done:
            return
        for child in self.children:
            child.disabled = True
        if self.sent_message:
            try:
                await self.sent_message.edit(content="⌛ 確認逾時，尚未建立角色卡，請重新用 `.pc` 面板的【建立】。", view=self)
            except discord.HTTPException:
                pass

class PcCardRevealView(discord.ui.View):
    """`.pc set`／`.pc url` 解析完角色卡後，先在頻道發這則「存根」：
    只有一顆按鈕，卡片內容完全不出現在公開訊息裡。
    本人按下按鈕後，才用 ephemeral 訊息（只有本人看得到）顯示完整預覽＋確認/編輯按鈕。
    （Discord 限制：ephemeral 只能回覆「互動」，貼卡的純文字訊息不算互動，所以需要這一步。）"""
    def __init__(self, message, card, alias_hint, preview):
        super().__init__(timeout=300)
        self.message = message
        self.card = card
        self.alias_hint = alias_hint
        self.preview = preview
        self.author_id = message.author.id
        self.sent_message = None  # 存根訊息本體，完成/逾時要編輯它
        self.done = False

    async def close_stub(self, note="✅ 角色卡確認完成。"):
        """確認流程走完（存檔成功）後把存根收掉，按鈕移除。"""
        self.done = True
        self.stop()
        if self.sent_message:
            try:
                await self.sent_message.edit(content=note, view=None)
            except discord.HTTPException:
                pass

    @discord.ui.button(label="🔍 查看並確認角色卡（只有你看得到）", style=discord.ButtonStyle.primary)
    async def reveal_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.author_id:
            await interaction.response.send_message("這不是你的角色卡確認，請自己用 `.pc` 面板的【建立】。", ephemeral=True)
            return
        confirm_view = PcCardConfirmView(self.message, self.card, self.alias_hint, stub_view=self)
        await interaction.response.send_message(
            content="建立角色卡前先確認一下——這張角色卡是否有誤？",
            embed=self.preview,
            view=confirm_view,
            ephemeral=True,
        )

    async def on_timeout(self):
        if self.done:
            return
        for child in self.children:
            child.disabled = True
        if self.sent_message:
            try:
                await self.sent_message.edit(content="⌛ 確認逾時，尚未建立角色卡，請重新用 `.pc` 面板的【建立】。", view=self)
            except discord.HTTPException:
                pass

class PcCardConfirmView(discord.ui.View):
    """建立角色卡前先問一句「是否有誤」：
    按「否」＝沒問題，照原本邏輯直接存檔；按「是」＝跳出 PcCardEditModal 讓你直接改文字再送出。
    這個 View 現在是掛在 ephemeral 訊息上（卡片內容只有本人看得到）；
    stub_view 是頻道裡那則公開存根（PcCardRevealView），確認完成後要順手把它收掉。"""
    def __init__(self, message, card, alias_hint, stub_view=None):
        super().__init__(timeout=300)
        self.message = message
        self.card = card
        self.alias_hint = alias_hint
        self.author_id = message.author.id
        self.stub_view = stub_view
        self.sent_message = None  # （非 ephemeral 流程用）訊息送出後由呼叫端補上，逾時要編輯這則訊息用

    async def _check_author(self, interaction):
        if interaction.user.id != self.author_id:
            await interaction.response.send_message("這不是你叫出來的角色卡確認，請自己用 `.pc` 面板的【建立】。", ephemeral=True)
            return False
        return True

    def _disable_all(self):
        for child in self.children:
            child.disabled = True

    @discord.ui.button(label="✅ 沒有錯，建立角色卡", style=discord.ButtonStyle.success)
    async def confirm_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not await self._check_author(interaction):
            return
        self.stop()
        self._disable_all()
        await interaction.response.edit_message(view=self)
        ok = await _finalize_pc_card_save(self.message, self.card, self.alias_hint, interaction=interaction)
        if ok and self.stub_view:
            await self.stub_view.close_stub()

    @discord.ui.button(label="✏️ 有錯，我要編輯", style=discord.ButtonStyle.danger)
    async def edit_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not await self._check_author(interaction):
            return
        self.stop()
        self._disable_all()
        await interaction.response.send_modal(PcCardEditModal(self.message, self.card, self.alias_hint, stub_view=self.stub_view))
        try:
            await interaction.message.edit(view=self)
        except discord.HTTPException:
            pass

    async def on_timeout(self):
        self._disable_all()
        if self.sent_message:
            try:
                await self.sent_message.edit(content="⌛ 確認逾時，尚未建立角色卡，請重新用 `.pc` 面板的【建立】。", view=self)
            except discord.HTTPException:
                pass

async def _finalize_pc_card_save(message, card, alias_hint, interaction=None):
    """實際檢查＋寫入角色卡的收尾邏輯（原本 save_new_pc_card 的內容搬過來）。
    interaction 有值代表是從確認按鈕／編輯 Modal 送出的，用 ephemeral followup 回覆
    （卡片數值只有本人看得到）；沒有值代表還沒經過確認流程，直接用頻道發文。"""
    if interaction:
        async def send(**kwargs):
            return await interaction.followup.send(ephemeral=True, **kwargs)
    else:
        send = message.channel.send

    if not pc_card_has_content(card):
        await send(embed=discord.Embed(
            title="❌ 無法解析角色卡",
            description=(
                "這段文字看起來不是可辨識的角色卡格式，請確認有包含「角色名稱：」「HP：」等欄位。\n"
                "建議直接用戳卡工具產生角色卡文字後貼上，或參考以下格式範本：\n"
                f"```\n{PC_CARD_TEMPLATE}\n```\n"
                "若要重新開始，請再次輸入 `.pc`。"
            ),
            color=0xff0000,
        ))
        return False
    owner = pc_owner(message)  # GM 代管時是被代管的玩家，否則就是操作者本人
    is_gm_mode = owner.id != message.author.id
    guild_id, user_id = message.guild.id, owner.id

    if alias_hint:
        alias = alias_hint  # 編輯模式：覆蓋原本這個代稱，不管新內容的角色名稱是什麼
    else:
        if not card['name']:
            await send(embed=discord.Embed(
                title="❌ 無法辨識角色名稱",
                description=(
                    "這段文字裡沒有找到「角色名稱：」欄位，請確認格式後重新用 `.pc` 面板的【建立】→【貼上文字】。\n"
                    "建議直接用戳卡工具產生角色卡文字後貼上，或參考以下格式範本：\n"
                    f"```\n{PC_CARD_TEMPLATE}\n```"
                ),
                color=0xff0000,
            ))
            return False
        alias = card['name']
        if pc_card_manager.get_card(guild_id, user_id, alias):
            update_hint = f"請 {owner.mention} 自己用 `.pc` 面板的【編輯】選這張卡，或先用【代管角色卡】的【刪除】清掉再重建。" if is_gm_mode else "請用 `.pc` 面板的【編輯】選這張卡。"
            await send(embed=discord.Embed(
                title="❌ 角色名稱已存在",
                description=f"角色名稱「{alias}」已經存過角色卡了，不能重複儲存。\n如果要更新內容，{update_hint}",
                color=0xff0000,
            ))
            return False

    pc_card_manager.save_card(guild_id, user_id, alias, card)
    embed = format_pc_card_embed(card, alias, owner)
    embed.title = f"✅ 已儲存角色卡｜{card.get('name') or alias}"
    await send(embed=embed)
    if interaction:
        # 卡片數值走 ephemeral，只公開一行「建好了」讓 GM／全桌知道，不洩漏內容
        if is_gm_mode:
            await message.channel.send(f"📇 {message.author.display_name}（GM）已為 {owner.mention} 代管建立/更新角色卡「{card.get('name') or alias}」。")
        else:
            await message.channel.send(f"📇 {message.author.display_name} 已建立/更新角色卡「{card.get('name') or alias}」。")
    return True

async def save_new_pc_card(message, card, alias_hint):
    """把剛解析好的角色卡 dict 拿去問使用者「是否有誤」，確認後才真正寫入
    （.pc set 貼文字、.pc url 匯入試算表、直接貼 Roll20 JSON 都共用這段收尾邏輯）。
    回傳是否成功送出確認訊息（實際存檔與否要看使用者後續按哪個按鈕）。"""
    if not pc_card_has_content(card):
        await message.channel.send(embed=discord.Embed(
            title="❌ 無法解析角色卡",
            description=(
                "這段文字看起來不是可辨識的角色卡格式，請確認有包含「角色名稱：」「HP：」等欄位。\n"
                "建議直接用戳卡工具產生角色卡文字後貼上，或參考以下格式範本：\n"
                f"```\n{PC_CARD_TEMPLATE}\n```\n"
                "若要重新開始，請再次輸入 `.pc`。"
            ),
            color=0xff0000,
        ))
        return False
    owner = pc_owner(message)  # GM 代管時是被代管的玩家，否則就是操作者本人
    is_gm_mode = owner.id != message.author.id
    guild_id, user_id = message.guild.id, owner.id

    if alias_hint:
        alias = alias_hint
    else:
        if not card['name']:
            await message.channel.send(embed=discord.Embed(
                title="❌ 無法辨識角色名稱",
                description=(
                    "這段文字裡沒有找到「角色名稱：」欄位，請確認格式後重新用 `.pc` 面板的【建立】→【貼上文字】。\n"
                    "建議直接用戳卡工具產生角色卡文字後貼上，或參考以下格式範本：\n"
                    f"```\n{PC_CARD_TEMPLATE}\n```"
                ),
                color=0xff0000,
            ))
            return False
        alias = card['name']
        if pc_card_manager.get_card(guild_id, user_id, alias):
            update_hint = f"請 {owner.mention} 自己用 `.pc` 面板的【編輯】選這張卡，或先用【代管角色卡】的【刪除】清掉再重建。" if is_gm_mode else "請用 `.pc` 面板的【編輯】選這張卡。"
            await message.channel.send(embed=discord.Embed(
                title="❌ 角色名稱已存在",
                description=f"角色名稱「{alias}」已經存過角色卡了，不能重複儲存。\n如果要更新內容，{update_hint}",
                color=0xff0000,
            ))
            return False

    preview = format_pc_card_embed(card, alias, owner)
    preview.title = f"📝 請確認角色卡內容｜{card.get('name') or alias}"
    # 卡片內容不公開：頻道裡只發一則不含數值的存根，本人（或代管的 GM）按按鈕後才以 ephemeral 顯示完整預覽＋確認
    view = PcCardRevealView(message, card, alias_hint, preview)
    stub_content = (
        f"📝 已解析要給 {owner.mention} 的角色卡，請 {pc_actor_hint(message)} 按下方按鈕查看內容並確認（內容只有你看得到）。"
        if is_gm_mode else
        f"📝 已解析 {owner.mention} 的角色卡，請{pc_actor_hint(message)}按下方按鈕查看內容並確認（內容只有你看得到）。"
    )
    sent = await message.channel.send(
        content=stub_content,
        view=view,
    )
    view.sent_message = sent
    return True

PC_ATTACHMENT_EXTENSIONS = ('.txt', '.json')
PC_ATTACHMENT_MAX_SIZE = 2 * 1024 * 1024  # 2MB，角色卡文字用不到這麼多，抓大一點上限避免誤擋正常檔案

async def read_pc_attachment_text(attachment: discord.Attachment):
    """讀取 `.pc set` 等待貼上狀態時使用者附加的角色卡檔案（.txt／.json，內容通常是 Roll20 匯入碼或 DC 文字團簡表）。
    回傳 (文字內容, 錯誤訊息)：成功時錯誤訊息為 None；失敗（副檔名不符/太大/編碼錯誤/下載失敗）時文字為 None。"""
    filename_lower = attachment.filename.lower()
    if not filename_lower.endswith(PC_ATTACHMENT_EXTENSIONS):
        return None, f"檔案「{attachment.filename}」副檔名不支援，請上傳 `.txt` 或 `.json` 檔案。"
    if attachment.size > PC_ATTACHMENT_MAX_SIZE:
        return None, f"檔案「{attachment.filename}」太大了（{attachment.size} bytes），角色卡文字應該用不到這麼多，請確認檔案內容是否正確。"
    try:
        raw_bytes = await attachment.read()
    except discord.HTTPException:
        return None, f"讀取檔案「{attachment.filename}」失敗，請重新上傳一次試試。"
    for encoding in ('utf-8-sig', 'utf-8'):
        try:
            return raw_bytes.decode(encoding), None
        except UnicodeDecodeError:
            continue
    return None, f"檔案「{attachment.filename}」不是有效的 UTF-8 文字檔，請確認編碼後重新上傳。"

async def handle_pc_paste(message, raw_text, alias_hint):
    clean_text = remove_discord_emoji(raw_text).strip()
    if _looks_like_roll20_json_text(clean_text):
        try:
            # strict=False：Roll20 匯出的 JSON 常常在字串值裡直接放實體換行（例如法術/背景故事欄位），
            # 標準 JSON 規定字串內的控制字元要跳脫成 \n，但 Roll20 沒有跳脫，嚴格模式會直接解析失敗。
            parsed = json.loads(clean_text, strict=False)
        except (ValueError, TypeError):
            parsed = None
        if isinstance(parsed, list) and parsed and isinstance(parsed[0], dict):
            card = build_card_from_roll20(parsed[0])
            default_age = _safe_int(parsed[0].get('age'))
            default_san_max = _safe_int(parsed[0].get('san_start'))
            missing = [label for key, label in (('mov', 'MOV'), ('build', '體格'), ('db', 'DB'), ('san_max', '長瘋線')) if card.get(key) is None]
            if missing:
                view = Roll20FillMissingView(message, card, alias_hint, default_age=default_age, default_san_max=default_san_max)
                sent = await message.channel.send(
                    content=(
                        f"📥 已解析 {pc_owner(message).mention} 的 Roll20 匯入碼，"
                        f"不過裡面沒有「{'、'.join(missing)}」，Roll20 匯入碼本來就不含這幾項（靈感已經自動帶入智力數值，不用再填）。\n"
                        f"請{pc_actor_hint(message)}按下方按鈕補上數值（會順便問年齡算 MOV 年齡修正，其他也已依角色卡上的力量/敏捷/體型幫忙算好建議值，可以直接用或自己改）。"
                    ),
                    view=view,
                )
                view.sent_message = sent
            else:
                await save_new_pc_card(message, card, alias_hint)
            return
    card = parse_pc_card_text(clean_text)
    await save_new_pc_card(message, card, alias_hint)

# ---------- 從 Google 試算表網址匯入角色卡（.pc url／.pc 面板「建立」→ 網址） ----------
PC_SHEET_ID_RE = re.compile(r'/spreadsheets/d/([a-zA-Z0-9_-]+)')

async def run_pc_sheet_import(message, sheet_url, send_progress=True):
    """`.pc url 連結` 跟 `.pc` 面板「建立 → Google 試算表網址」共用的匯入流程。
    message 可以是真的 Discord 訊息，也可以是 _InteractionMessageShim（從按鈕/表單互動包出來的替身），
    只要有 .guild／.author／.channel 就能用。呼叫前請先確認 sheet_url 過得了 PC_SHEET_ID_RE。"""
    id_match = PC_SHEET_ID_RE.search(sheet_url)
    if not id_match:
        await message.channel.send(embed=discord.Embed(title="❌ 無法辨識試算表連結", description="請確認貼的是完整的 Google 試算表網址。", color=0xff0000))
        return
    spreadsheet_id = id_match.group(1)

    progress = None
    if send_progress:
        progress = await message.channel.send(embed=discord.Embed(title="🔄 正在讀取試算表…", description="請稍候，這可能需要幾秒鐘。", color=0x00aaff))

    card = None
    dc_text = None
    roll20_data = None
    # 先試 HKTRPG／rollbot 版：「人物卡」分頁裡內建的 .char add 快速匯入碼
    hktrpg_csv = await fetch_google_sheet_csv(spreadsheet_id, '人物卡')
    if hktrpg_csv:
        found = find_hktrpg_char_add(hktrpg_csv)
        if found:
            card = build_card_from_hktrpg(*found)

    # 找不到就試「跑團網站指令」分頁：先找 Roll20 版角色 JSON，再找戳卡版 DC 文字團簡表
    # （只抓這一個分頁的 CSV，不下載整份試算表，避免佔用太多運算資源）
    if card is None:
        dc_csv = await fetch_google_sheet_csv(spreadsheet_id, '跑團網站指令')
        if dc_csv:
            roll20_data = find_roll20_character_json(dc_csv)
            if roll20_data:
                card = build_card_from_roll20(roll20_data)
            else:
                dc_text = find_dc_summary_block(dc_csv)

    if progress:
        try:
            await progress.delete()
        except discord.HTTPException:
            pass

    if card is None and dc_text is None:
        await message.channel.send(embed=discord.Embed(
            title="❌ 無法從試算表匯入角色卡",
            description=(
                "試過「人物卡」分頁的 HKTRPG 快速匯入碼，跟「跑團網站指令」分頁的 Roll20 角色 JSON／DC 文字團簡表，都沒有找到可辨識的資料。\n"
                "請確認：\n"
                "1. 試算表已設定成「知道連結的人皆可檢視」\n"
                "2. 用的是戳卡版、Roll20 版或 HKTRPG／rollbot 版的自動角色卡模板\n\n"
                "如果你的匯入碼放在別的分頁，我沒辦法自動找整份試算表（會太吃資源），"
                "麻煩你手動打開試算表，把 Roll20 角色 JSON 那一格（長得像 `[{\"character_name\":...}]`）整段複製起來，"
                "改用 `.pc` 面板的【建立】→【貼上文字】貼給我，我一樣看得懂這種格式；戳卡版的文字角色卡也是走同一個入口。"
            ),
            color=0xff0000,
        ))
        return

    if card is not None:
        missing = [label for key, label in (('mov', 'MOV'), ('build', '體格'), ('db', 'DB'), ('san_max', '長瘋線')) if card.get(key) is None]
        if missing:
            default_age = _safe_int(roll20_data.get('age')) if roll20_data else None
            default_san_max = _safe_int(roll20_data.get('san_start')) if roll20_data else None
            view = Roll20FillMissingView(message, card, None, default_age=default_age, default_san_max=default_san_max)
            sent = await message.channel.send(
                content=(
                    f"📥 已從試算表解析出 {pc_owner(message).mention} 的角色卡，"
                    f"不過裡面沒有「{'、'.join(missing)}」，Roll20 匯入碼本來就不含這幾項（靈感已經自動帶入智力數值，不用再填）。\n"
                    f"請{pc_actor_hint(message)}按下方按鈕補上數值（會順便問年齡算 MOV 年齡修正，其他也已依角色卡上的力量/敏捷/體型幫忙算好建議值，可以直接用或自己改）。"
                ),
                view=view,
            )
            view.sent_message = sent
        else:
            await save_new_pc_card(message, card, None)
    else:
        await handle_pc_paste(message, dc_text, None)

async def fetch_google_sheet_csv(spreadsheet_id, sheet_name):
    """用分頁名稱抓「知道連結的人皆可檢視」試算表的 CSV 內容，不需要 API 金鑰、也不用管 gid。
    抓不到（未公開分享／該名稱的分頁不存在／逾時）一律回傳 None，呼叫端自行判斷要不要試下一種格式。"""
    url = f"https://docs.google.com/spreadsheets/d/{spreadsheet_id}/gviz/tq?tqx=out:csv&sheet={urlquote(sheet_name)}"
    try:
        async with aiohttp.ClientSession() as session:
            async with session.get(url, timeout=aiohttp.ClientTimeout(total=10)) as resp:
                if resp.status != 200:
                    return None
                text = await resp.text()
                if not text or text.lstrip().startswith('<'):
                    # 抓不到分頁或沒有公開權限時，Google 會回傳 HTML 錯誤頁而不是 CSV
                    return None
                return text
    except Exception:
        return None

def _iter_csv_cells(csv_text):
    """把 CSV 文字逐一拆成儲存格內容，忽略座標，只需要抓內容比對用。"""
    reader = csv.reader(StringIO(csv_text))
    for row in reader:
        for cell in row:
            if cell:
                yield cell

def find_dc_summary_block(csv_text):
    """在「跑團網站指令」分頁的 CSV 裡找『DC 文字團簡表』那一格（完整的「角色名稱：...」文字區塊），
    格式跟 .pc set 貼上文字完全相容，找到就直接回傳整格文字。"""
    for cell in _iter_csv_cells(csv_text):
        if re.match(r'^角色名稱\s*[:：]', cell.strip()):
            return cell
    return None

def _looks_like_roll20_json_text(text):
    """粗略判斷一段文字是不是 Roll20 版角色 JSON：兩種常見命名都認——
    有的模板用 `character_name`，有的模板（例如某些自架角色卡工具匯出的格式）只用 `name`。
    單純出現 `name` 太容易誤判，所以「只用 name」時額外要求同時出現 str／dex／pow 這幾個
    角色卡才會有的屬性欄位，降低把無關 JSON 誤認成角色卡的機率。"""
    if not text.startswith('['):
        return False
    if '"character_name"' in text:
        return True
    return '"name"' in text and '"str"' in text and '"dex"' in text and '"pow"' in text

def find_roll20_character_json(csv_text):
    """在已經抓到手的 CSV 文字裡找 Roll20 版角色 JSON 匯入碼
    （長得像 `[{"character_name":"...", "str":"50", ...}]` 或
    `[{"name":"...", "str":"50", ...}]` 的一整格內容）。
    只掃這一格 CSV、不額外發送任何網路請求，找不到就回傳 None。"""
    for cell in _iter_csv_cells(csv_text):
        cell = cell.strip()
        if not _looks_like_roll20_json_text(cell):
            continue
        try:
            parsed = json.loads(cell, strict=False)
        except (ValueError, TypeError):
            continue
        if isinstance(parsed, list) and parsed and isinstance(parsed[0], dict):
            return parsed[0]
    return None

_HKTRPG_CHAR_ADD_RE = re.compile(r'\.char add name\[([^\]]*)\]~state\[([^\]]*)\]~roll\[([^\]]*)\]~notes\[', re.S)

def find_hktrpg_char_add(csv_text):
    """在 CSV 裡找 HKTRPG／rollbot 版內建的『.char add』快速匯入碼，回傳 (name, state, roll) 三段原始文字。"""
    m = _HKTRPG_CHAR_ADD_RE.search(csv_text)
    if not m:
        return None
    return m.group(1), m.group(2), m.group(3)

def _safe_int(s):
    try:
        return int(re.sub(r'[^\-0-9]', '', s))
    except (ValueError, TypeError):
        return None

def build_card_from_hktrpg(name_str, state_str, roll_str):
    """把 HKTRPG／rollbot 版的 `.char add name[...]~state[...]~roll[...]` 快速匯入碼，
    轉成跟 parse_pc_card_text 輸出相同結構的角色卡 dict，才能沿用既有的儲存/顯示邏輯。
    roll[] 裡帶 {變數} 公式參照（例如 `CC {SAN}`）的欄位是動態值、不是固定數字，直接略過不記錄。"""
    data = {
        'name': name_str.strip() or None,
        'hp_cur': None, 'hp_max': None,
        'mp_cur': None, 'mp_max': None,
        'san_cur': None, 'san_max': None,
        'luck': None, 'idea': None,
        'attributes': {},
        'build': None, 'db': None, 'mov': None,
        'skills': [], 'combat': [], 'extra_skills': [],
    }

    def _pairs(s):
        for part in s.split(';'):
            part = part.strip()
            if not part or ':' not in part:
                continue
            k, v = part.split(':', 1)
            yield k.strip(), v.strip()

    for key, val in _pairs(state_str):
        if key == 'HP' and '/' in val:
            data['hp_cur'], data['hp_max'] = _safe_int(val.split('/', 1)[0]), _safe_int(val.split('/', 1)[1])
        elif key == 'MP' and '/' in val:
            data['mp_cur'], data['mp_max'] = _safe_int(val.split('/', 1)[0]), _safe_int(val.split('/', 1)[1])
        elif key == 'SAN' and '/' in val:
            data['san_cur'], data['san_max'] = _safe_int(val.split('/', 1)[0]), _safe_int(val.split('/', 1)[1])
        elif key == '體格':
            data['build'] = _safe_int(val)
        elif key == 'DB':
            data['db'] = val
        elif key == 'MOV':
            data['mov'] = _safe_int(val)
        # 職業／特徵／護甲目前的角色卡結構沒有對應欄位，先略過不記錄

    for key, val in _pairs(roll_str):
        if '{' in val:
            continue  # 公式參照（例如 CC {SAN}），不是固定數值，略過
        m = re.match(r'^CC\s+(-?\d+)', val, re.I)
        if not m:
            continue  # 武器傷害這類非 CC<= 檢定的列略過
        num = int(m.group(1))
        if key in _PC_ATTR_LABELS:
            data['attributes'][key] = num
        elif key in ('幸運', 'LUK', 'luck'):
            data['luck'] = num
        elif key == '靈感':
            data['idea'] = num
        elif key.lower() == '1d100':
            continue
        else:
            data['skills'].append((key, num))
    return data

# Roll20 版角色 JSON 的欄位名稱 -> 中文技能名稱對照表
# （對照來源：同一分頁裡 CCFOLIA 匯入碼 commands 欄位列出的中文技能清單）
_ROLL20_SKILL_MAP = {
    'psychology': '心理學', 'credit_rating': '信用評級', 'persuade': '勸說',
    'fast_talk': '話術', 'intimidate': '恐嚇', 'charm': '取悅', 'navigate': '領航',
    'jump': '跳躍', 'climb': '攀爬', 'swim': '游泳', 'drive_auto': '駕駛-汽車',
    'ride': '騎術', 'stealth': '隱匿行動', 'track': '追蹤', 'disguise': '喬裝',
    'locksmith': '鎖匠', 'sleight_of_hand': '巧手', 'language_own': '母語',
    'accounting': '會計', 'law': '法律', 'occult': '神祕學', 'history': '歷史',
    'natural_world': '博物學', 'anthropology': '人類學', 'archaeology': '考古學',
    'compute_use': '電腦使用', 'acting': '表演', 'mech_repair': '機械維修',
    'elec_repair': '電器維修', 'op_hv_machine': '重機械操作', 'spot_hidden': '偵查',
    'listen': '聆聽', 'library_use': '圖書館使用', 'appraise': '估價',
    'cthulhu_mythos': '克蘇魯神話', 'first_aid': '急救', 'medicine': '醫學',
    'pharmacy': '藥學', 'psychoanalysis': '精神分析',
}
_ROLL20_COMBAT_MAP = {
    'dodge': '閃避', 'fighting_brawl': '鬥毆', 'throw': '投擲',
    'firearms_handgun': '手槍', 'firearms_rifle': '步槍/霰彈',
    'submachine_gun': '衝鋒槍', 'machine_gun': '機槍',
}
_ROLL20_ATTR_MAP = {
    'str': '力量', 'dex': '敏捷', 'pow': '意志', 'con': '體質',
    'app': '外貌', 'edu': '教育', 'siz': '體型', 'int': '智力',
}

def _calc_build_db(str_val, siz_val):
    """依 CoC 7e 的 STR+SIZ 對照表算「體格」跟「傷害加成(DB)」，缺任一數值就回 (None, None)。
    僅供 Roll20 匯入碼補值時當「建議值」，使用者仍可在跳出的視窗裡自己改。"""
    if str_val is None or siz_val is None:
        return None, None
    total = str_val + siz_val
    if total <= 64:
        return -2, '-2'
    elif total <= 84:
        return -1, '-1'
    elif total <= 124:
        return 0, '0'
    elif total <= 164:
        return 1, '+1D4'
    elif total <= 204:
        return 2, '+1D6'
    elif total <= 284:
        return 3, '+2D6'
    elif total <= 364:
        return 4, '+3D6'
    elif total <= 444:
        return 5, '+4D6'
    else:
        extra = (total - 445) // 80 + 1
        return 5 + extra, f'+{4 + extra}D6'

def _calc_mov(str_val, dex_val, siz_val, age=None):
    """依 CoC 7e 規則算 MOV，缺力量/敏捷/體型任一就回 None。
    有給年齡的話，再套用官方年齡修正（40 歲起每級距 -1，最多到 80 歲以上 -5）。"""
    if str_val is None or dex_val is None or siz_val is None:
        return None
    if str_val < siz_val and dex_val < siz_val:
        mov = 7
    elif str_val > siz_val and dex_val > siz_val:
        mov = 9
    else:
        mov = 8
    if age is not None:
        if age >= 80:
            mov -= 5
        elif age >= 70:
            mov -= 4
        elif age >= 60:
            mov -= 3
        elif age >= 50:
            mov -= 2
        elif age >= 40:
            mov -= 1
    return mov

def _calc_idea(int_val):
    """靈感通常＝智力×5，缺智力就回 None。"""
    return int_val * 5 if int_val is not None else None

def build_card_from_roll20(data):
    """把 Roll20 版角色 JSON（`.char add` 的另一種匯入碼格式）
    轉成跟 parse_pc_card_text 輸出相同結構的角色卡 dict。
    這份 JSON 只有單一數值（沒有分現在值／最大值），一律視為角色剛建立時的滿值，
    所以 HP／MP／SAN 的目前值跟最大值先填一樣的數字，之後可以再用 `.pc set` 調整。"""
    card = {
        'name': (data.get('character_name') or data.get('name') or '').strip() or None,
        'hp_cur': None, 'hp_max': None,
        'mp_cur': None, 'mp_max': None,
        'san_cur': None, 'san_max': None,
        'luck': None, 'idea': None,
        'attributes': {},
        'build': None, 'db': None, 'mov': None,
        'skills': [], 'combat': [], 'extra_skills': [],
    }

    for key, label in _ROLL20_ATTR_MAP.items():
        num = _safe_int(data.get(key))
        if num is not None:
            card['attributes'][label] = num

    hp = _safe_int(data.get('hp'))
    if hp is not None:
        card['hp_cur'] = card['hp_max'] = hp
    mp = _safe_int(data.get('mp'))
    if mp is not None:
        card['mp_cur'] = card['mp_max'] = mp
    san_cur = _safe_int(data.get('san'))
    san_start = _safe_int(data.get('san_start'))
    if san_cur is not None or san_start is not None:
        card['san_cur'] = san_cur if san_cur is not None else san_start
    # san_max（長瘋線／不定性瘋狂線）Roll20 匯入碼裡的 san_start 只是初始 SAN，不是長瘋線，
    # 一律留空，改在補值視窗詢問使用者實際的長瘋線數值。
    luck = _safe_int(data.get('luck'))
    if luck is not None:
        card['luck'] = luck
    # 靈感一律直接帶入智力（不做智力×5的換算），有智力就自動補上，不用另外詢問
    if card['idea'] is None:
        card['idea'] = card['attributes'].get('智力')

    for key, label in _ROLL20_SKILL_MAP.items():
        num = _safe_int(data.get(key))
        if num is not None:
            card['skills'].append((label, num))

    for key, label in _ROLL20_COMBAT_MAP.items():
        num = _safe_int(data.get(key))
        if num is not None:
            card['combat'].append((label, num))

    # 自訂技能：Roll20 表格裡凡是「技能名稱＋技能值」成對出現的欄位（駕駛-其他、第二外語、
    # 生存-XX、領航-其他、藝術/工藝-XX 等），命名習慣都是 `xxx_name`（填技能名稱）配對 `xxx` 或
    # `xxx01`（填數值）。這裡不用預先列出每一種可能的 xxx，直接通用掃描所有 `_name` 結尾的欄位，
    # 只要「使用者真的有填名稱」+「對應數值欄位是數字」就保留，避免因為漏列某個自訂技能類型而被跳過。
    for key in data:
        if not key.endswith('_name') or key == 'character_name':
            continue
        name = (data.get(key) or '').strip()
        name = name.rstrip('：:').strip()  # 有些模板會把冒號一起存進名稱欄位，例如「生存：」，去掉尾巴比較好看
        if not name or name.isdigit():
            continue  # 沒填名稱，或者剛好是純數字（不像技能名稱），略過避免誤記
        prefix = key[:-len('_name')]
        num = _safe_int(data.get(prefix))
        if num is None:
            num = _safe_int(data.get(prefix + '01'))
        if num is not None:
            card['extra_skills'].append((name, num))

    return card

# ---------- 點命令處理 ----------
async def resolve_member_by_id(guild, user_id):
    """
    依 ID 找成員：先查本地快取（get_member，免 API 呼叫），
    快取沒有的話改用 fetch_member 直接跟 Discord API 查詢單一成員。
    fetch_member 是單筆查詢，不受 Members Intent 限制，即使快取不完整也能用 @提及或數字ID 找到人；
    但用「名字/暱稱文字」比對整批成員這件事，仍然需要 Members Intent 開啟才能取得完整成員清單。
    """
    member = guild.get_member(user_id)
    if member is not None:
        return member
    try:
        return await guild.fetch_member(user_id)
    except discord.NotFound:
        return None
    except discord.HTTPException:
        return None

async def resolve_target_by_text(guild, user_input):
    """依提及（<@id>）、純數字 ID，或使用者名稱/暱稱字串尋找伺服器成員，找不到回傳 None。"""
    mention_match = re.search(r'<@!?(\d+)>', user_input)
    if mention_match:
        return await resolve_member_by_id(guild, int(mention_match.group(1)))
    if user_input.isdigit():
        return await resolve_member_by_id(guild, int(user_input))
    clean_name = user_input.lstrip('@')
    target = discord.utils.get(guild.members, name=clean_name)
    if target:
        return target
    target = discord.utils.get(guild.members, display_name=clean_name)
    if target:
        return target
    lower_name = clean_name.lower()
    for member in guild.members:
        if member.name.lower() == lower_name or (member.nick and member.nick.lower() == lower_name):
            return member
    return None

# ---------- 先攻（.init）輔助函式 ----------
# 一份先攻名單裡的每個條目，用 'kind' 分三種：
#   'dex'         — 直接比 DEX 數值（面板「➕ 登記 NPC」，或「⚔️ 敏捷作為先攻」自動從角色卡抓敏捷／手動輸入），不需要先擲骰
#   'roll_check'  — 用 .cc 技能檢定 擲出來的（「🎲 擲骰檢定作為先攻」後接 .cc 敏捷 之類），有成功等級
#   'roll_generic'— 用通用骰子 xdy+z／xdy 擲出來的（「🎲 擲骰檢定作為先攻」後接普通骰子指令，支援小數，例如 1d20+3.16），只有數字沒有等級
# 三種可以同時出現在同一份名單裡；同種之間互相比較，種類之間則按「roll_check → dex → roll_generic」
# 分組列出（技能檢定的成功等級最直觀所以排最前面，通用骰子只是純數字最不具參考性所以排最後）。
# 正常情況建議整場先攻只用同一種方式登記，混用時看得懂但不會是嚴謹的統一比較。
#
# 最終排序（由上到下依序比較）：
#   1. tie_breaker（GM 用面板「↕️ 調整順序」把名字由快到慢列一遍換算而來，越前面越大；預設 0）——
#      這是「手動指定順序」，不要求數值相同才能調，指定的人一律排到未指定的人前面，
#      指定的人彼此之間照列出的順序排；沒被指定的人之間，才照下面的種類/數值/加入順序排。
#   2. 種類分組（roll_check → dex → roll_generic）與同種類內的數值高低
#   3. 加入名單的順序（GM 不特別調整的話，先登記的人排前面——這就是「你排」）
_INIT_LEVEL_RANK = {"大成功": 5, "極限成功": 4, "困難成功": 3, "一般成功": 2, "失敗": 1, "大失敗": 0}
_INIT_KIND_GROUP = {'roll_check': 0, 'dex': 1, 'roll_generic': 2}

def _init_effective_dex(e):
    """'dex' 條目的有效敏捷：持械備射／施法準備（CoC 7e 規則）先攻視為 DEX +50。"""
    return e['dex'] + (50 if e.get('ready') else 0)

def _init_natural_key(e):
    """同一種類條目「規則本身」決定的排序依據，不含 tie_breaker／加入順序這兩層人為/預設的最終比較。"""
    kind = e['kind']
    if kind == 'dex':
        return (-_init_effective_dex(e), -(e['skill'] if e['skill'] is not None else -1))
    elif kind == 'roll_check':
        return (-_INIT_LEVEL_RANK.get(e['level'], -1), e['roll'])
    else:  # 'roll_generic'
        return (-e['roll'],)

def _init_sort_key_factory(entries):
    order_index = {name: i for i, name in enumerate(entries.keys())}

    def key(item):
        name, e = item
        return (
            -e.get('tie_breaker', 0),
            _INIT_KIND_GROUP[e['kind']],
            _init_natural_key(e),
            order_index[name],
        )
    return key

def _init_entry_text(e):
    if e['kind'] == 'dex':
        skill_text = f"，戰鬥技能 {e['skill']}" if e['skill'] is not None else ""
        if e.get('ready'):
            return f"DEX {e['dex']} 🔫 持械備射／施法準備 +50 → **{_init_effective_dex(e)}**{skill_text}"
        return f"DEX {e['dex']}{skill_text}"
    elif e['kind'] == 'roll_check':
        return f"{e['level']}（擲 {e['roll']}）"
    else:
        return f"擲出 {e['roll']}"

def format_init_embed(session):
    entries = session['entries']
    if not entries:
        desc = (
            "目前沒有登記任何參戰者。\n"
            "玩家：按「⚔️ 敏捷作為先攻」（有角色卡自動抓，沒有就跳表單手動填）或「🎲 擲骰檢定作為先攻」把自己加進來（每個人要加入都要自己按一次）。\n"
            "GM：按「➕ 登記 NPC」批量登記怪物／NPC。"
        )
        return discord.Embed(title="⚔️ 先攻順序", description=desc, color=0x00aaff)

    sort_key = _init_sort_key_factory(entries)
    ordered = sorted(entries.items(), key=sort_key)
    turn_name = session.get('turn_name')
    n = len(ordered)

    def _speed_tag(i):
        """名單有兩人以上時，第一位標「最快」、最後一位標「最慢」。"""
        if n < 2:
            return ""
        if i == 1:
            return "（⚡ 最快）"
        if i == n:
            return "（🐢 最慢）"
        return ""

    lines = [
        f"{'▶ ' if name == turn_name else ''}**{i}. {name}**{_speed_tag(i)} — {_init_entry_text(e)}"
        for i, (name, e) in enumerate(ordered, 1)
    ]

    tie_notes = []
    for i in range(len(ordered) - 1):
        name_a, a = ordered[i]
        name_b, b = ordered[i + 1]
        if a['kind'] != b['kind']:
            continue
        if _init_natural_key(a) == _init_natural_key(b) and a.get('tie_breaker', 0) == b.get('tie_breaker', 0):
            tie_notes.append(f"「{name_a}」與「{name_b}」數值完全同分，目前用加入順序排列，GM 可用面板的「↕️ 調整順序」指定先後。")

    desc = "\n".join(lines)
    if tie_notes:
        desc += "\n\n⚠️ " + "\n⚠️ ".join(tie_notes)
    round_no = session.get('round')
    title = f"⚔️ 先攻順序（第 {round_no} 輪）" if round_no else "⚔️ 先攻順序"
    return discord.Embed(title=title, description=desc, color=0x00aaff)

def join_init_with_own_pc_card(guild_id, channel_id, user_id):
    """讓玩家用自己在本頻道啟用中的角色卡，把「自己」的敏捷值登記/更新進先攻名單。
    不會去抓其他人的角色卡——每個人要登記都得自己打一次 `.init`。
    已經登記過的話只更新 dex 數值本身，保留 GM 手動設定過的戰鬥技能/tie_breaker。
    回傳 (alias, dex) 成功時；沒有啟用角色卡、或角色卡沒有敏捷值時回傳 (None, None)。"""
    alias = pc_active_manager.get_active(guild_id, channel_id, user_id)
    if not alias:
        return None, None
    card = pc_card_manager.get_card(guild_id, user_id, alias)
    if not card:
        return None, None
    dex = card.get('attributes', {}).get('敏捷')
    if not isinstance(dex, int):
        return None, None
    key = (guild_id, channel_id)
    session = init_sessions.setdefault(key, {'entries': {}})
    existing = session['entries'].get(alias)
    if existing and existing.get('kind') == 'dex':
        existing['dex'] = dex
        existing['user_id'] = user_id
    else:
        session['entries'][alias] = {'kind': 'dex', 'dex': dex, 'skill': None, 'user_id': user_id}
    init_sessions_save()
    return alias, dex

class InitRollNameModal(discord.ui.Modal, title="🎲 填寫角色資訊"):
    """面板「🎲 擲骰檢定作為先攻」在這個人本頻道沒有啟用角色卡時，用這個表單問清楚
    角色名稱跟職業，填完送出才真正進入『等待你擲骰』狀態，
    登記進先攻名單時會顯示成「名稱（職業）」。"""
    char_name = discord.ui.TextInput(label="角色名稱", required=True, max_length=50)
    occupation = discord.ui.TextInput(label="職業（可留空）", required=False, max_length=50)

    def __init__(self, guild_id, channel_id, user_id):
        super().__init__()
        self.guild_id = guild_id
        self.channel_id = channel_id
        self.user_id = user_id

    async def on_submit(self, interaction: discord.Interaction):
        name = str(self.char_name.value).strip()
        occ = str(self.occupation.value).strip()
        display_name = f"{name}（{occ}）" if occ else name
        init_pending[(self.guild_id, self.channel_id, self.user_id)] = {
            'name': display_name, 'expire': time.time() + INIT_PENDING_TIMEOUT,
        }
        await interaction.response.send_message(embed=discord.Embed(
            title="🎲 等待你的先攻擲骰",
            description=f"角色：「{display_name}」\n請在 {INIT_PENDING_TIMEOUT} 秒內於本頻道擲骰——`.cc 敏捷`（或任何技能檢定）或通用骰子 `xdy+z`／`xdy` 都行，下一次擲骰結果會自動登記成先攻。",
            color=0x00aaff,
        ), ephemeral=True)

class InitManualDexModal(discord.ui.Modal, title="🖊 手動輸入敏捷"):
    """面板「⚔️ 敏捷作為先攻」在這個人本頻道沒有啟用角色卡（或角色卡沒有敏捷值）時，
    自動改跳這張表單，讓玩家自己直接打敏捷數值登記先攻，一樣不用擲骰、也不用先建角色卡。
    跟角色卡登記一樣是 'dex' 種類（依數值大小排序），只是數值來源改成手動輸入。
    已經用同一個角色名稱登記過的話，再送一次會直接覆蓋成新的數值（更新用）。"""
    char_name = discord.ui.TextInput(label="角色名稱（留空則用你的 Discord 顯示名稱）", required=False, max_length=50)
    dex_value = discord.ui.TextInput(label="敏捷數值", placeholder="例如 65", required=True, max_length=5)
    skill_value = discord.ui.TextInput(label="戰鬥技能數值（可留空，同分時用來比較）", required=False, max_length=5)

    def __init__(self, guild_id, channel_id, user_id, default_name):
        super().__init__()
        self.guild_id = guild_id
        self.channel_id = channel_id
        self.user_id = user_id
        self.char_name.default = default_name

    async def on_submit(self, interaction: discord.Interaction):
        dex_raw = str(self.dex_value.value).strip()
        if not dex_raw.isdigit():
            await interaction.response.send_message("敏捷數值必須是數字。", ephemeral=True)
            return
        skill_raw = str(self.skill_value.value).strip()
        if skill_raw and not skill_raw.isdigit():
            await interaction.response.send_message("戰鬥技能數值必須是數字（可以留空）。", ephemeral=True)
            return
        name = str(self.char_name.value).strip() or interaction.user.display_name
        key = (self.guild_id, self.channel_id)
        session = init_sessions.setdefault(key, {'entries': {}})
        existing = session['entries'].get(name)
        entry = {
            'kind': 'dex',
            'dex': int(dex_raw),
            'skill': int(skill_raw) if skill_raw else None,
            'user_id': self.user_id,
        }
        if existing and existing.get('kind') == 'dex' and existing.get('ready'):
            entry['ready'] = True  # 更新同一個名字時保留原本的持械備射標記
        session['entries'][name] = entry
        init_sessions_save()
        embed = format_init_embed(session)
        await interaction.response.send_message(
            content=f"✅ 已用手動輸入的敏捷 {dex_raw} 登記/更新「{name}」的先攻。", embed=embed
        )

class InitDelSelect(discord.ui.Select):
    """面板「🗑️ 移除」跳出的選單：直接勾選要移除的參戰者，可一次多選。
    選項的 value 用索引而不是名字本身，避免名字超過 Discord 100 字元上限被截斷後對不回去。"""
    def __init__(self, author_id, guild_id, channel_id, names):
        self.author_id = author_id
        self.guild_id = guild_id
        self.channel_id = channel_id
        self.names = names  # 只放前 25 個（Discord 選單上限）
        options = [discord.SelectOption(label=name[:100], value=str(i)) for i, name in enumerate(names)]
        super().__init__(placeholder="選擇要移除的參戰者（可多選）…", options=options, min_values=1, max_values=len(options))

    async def callback(self, interaction: discord.Interaction):
        if interaction.user.id != self.author_id:
            await interaction.response.send_message("這不是你叫出來的選單喔，請自己按面板上的「🗑️ 移除」。", ephemeral=True)
            return
        session = init_sessions.get((self.guild_id, self.channel_id))
        removed = []
        for idx_str in self.values:
            name = self.names[int(idx_str)]
            if session and session['entries'].pop(name, None) is not None:
                removed.append(name)
        if session and not session['entries']:
            init_sessions.pop((self.guild_id, self.channel_id), None)
            session = None
        init_sessions_save()
        title = f"✅ 已移除：{'、'.join(removed)}" if removed else "⚠️ 選到的條目已經不在名單上了"
        await interaction.response.edit_message(
            embed=discord.Embed(title=title, color=0x00aaff),
            view=None,
        )
        # 移除後把最新的先攻名單再貼一次（名單清空就顯示空名單提示）
        await interaction.followup.send(embed=format_init_embed(session or {'entries': {}}))

class InitDelSelectView(discord.ui.View):
    def __init__(self, author_id, guild_id, channel_id, names):
        super().__init__(timeout=120)
        self.select = InitDelSelect(author_id, guild_id, channel_id, names)
        self.add_item(self.select)

    async def on_timeout(self):
        self.select.disabled = True


class InitNpcAddModal(discord.ui.Modal, title="➕ 登記 NPC"):
    """面板「➕ 登記 NPC」跳出的表單：一行一隻批量登記。
    格式：`名字 DEX 鬥毆技能值 是否持有槍械 槍械技能值`——鬥毆技能值／是否持有槍械／槍械技能值都可以留空不填，
    留空的話後面的欄位也可以直接省略（例如只打「食屍鬼 65」或「食屍鬼 65 40」都合法）。
    是否持有槍械打「是」或「有」代表持械備射／施法準備，先攻 DEX +50；
    比較同分順序用的技能值：持有槍械時優先用「槍械技能值」，沒填才退回用「鬥毆技能值」。"""
    lines = discord.ui.TextInput(
        label="一行一隻：名字 DEX 鬥毆技能值 是否持有槍械 槍械技能值",
        style=discord.TextStyle.paragraph,
        placeholder="食屍鬼 65 40\n槍手甲 40 30 是 60\n瘋狂教授 50",
        required=True,
        max_length=1000,
    )

    def __init__(self, guild_id, channel_id):
        super().__init__()
        self.guild_id = guild_id
        self.channel_id = channel_id

    async def on_submit(self, interaction: discord.Interaction):
        key = (self.guild_id, self.channel_id)
        session = init_sessions.setdefault(key, {'entries': {}})
        added, bad = [], []
        for raw in str(self.lines.value).splitlines():
            line = raw.strip()
            if not line:
                continue
            m = re.match(
                r'^(\S+)\s+(\d+)(?:\s+(\d+))?(?:\s+(是|有|否|無|y|Y|n|N|yes|Yes|no|No))?(?:\s+(\d+))?$',
                line,
            )
            if not m:
                bad.append(raw)
                continue
            name = m.group(1)
            dex = int(m.group(2))
            brawl_raw = m.group(3)
            gun_flag_raw = m.group(4) or ''
            gun_raw = m.group(5)
            has_gun = gun_flag_raw in ('是', '有', 'y', 'Y', 'yes', 'Yes')

            skill = None
            if has_gun and gun_raw:
                skill = int(gun_raw)
            elif brawl_raw:
                skill = int(brawl_raw)
            elif gun_raw:
                skill = int(gun_raw)

            entry = {'kind': 'dex', 'dex': dex, 'skill': skill}
            if has_gun:
                entry['ready'] = True
            session['entries'][name] = entry
            added.append(name)
        if not session['entries']:
            init_sessions.pop(key, None)
        init_sessions_save()
        embed = format_init_embed(init_sessions.get(key) or {'entries': {}})
        notes = []
        if added:
            notes.append(f"✅ 已登記：{'、'.join(added)}")
        if bad:
            notes.append(
                "⚠️ 這幾行看不懂已跳過（格式：`名字 DEX 鬥毆技能值 是否持有槍械 槍械技能值`，後三個都可留空）：\n"
                + "\n".join(f"`{b}`" for b in bad)
            )
        content = "\n".join(notes) if notes else None
        await interaction.response.send_message(content=content, embed=embed)

class InitRankModal(discord.ui.Modal, title="↕️ 調整順序"):
    """面板「↕️ 調整順序」跳出的表單：把名字**由快到慢**一行一個列出來（第一行最快、
    最後一行最慢），不用再打數字。內部會照列出的順序換算成 tie_breaker（越前面越大）。
    不要求數值同分才能調整：只要列進來的名字，一律排到沒被列進來的人前面（照列出的順序），
    沒被列進來的人之間，才照原本的種類/數值/加入順序排。每次送出都是整份重設
    （先清掉上次的調整再套用這次的順序），所以要調整時把想指定順序的名字一次列齊即可。"""
    lines = discord.ui.TextInput(
        label="由快到慢一行一個名字（第一行最快）",
        style=discord.TextStyle.paragraph,
        placeholder="小明\n食屍鬼\n瘋狂教授",
        required=True,
        max_length=500,
    )

    def __init__(self, guild_id, channel_id):
        super().__init__()
        self.guild_id = guild_id
        self.channel_id = channel_id

    async def on_submit(self, interaction: discord.Interaction):
        session = init_sessions.get((self.guild_id, self.channel_id))
        names, bad, seen = [], [], set()
        for raw in str(self.lines.value).splitlines():
            name = raw.strip()
            if not name:
                continue
            if not session or name not in session['entries']:
                bad.append(raw)
                continue
            if name in seen:  # 重複列到同一個名字，以第一次出現的位置為準
                continue
            seen.add(name)
            names.append(name)
        if names:
            # 整份重設：先清掉所有舊的順序調整，再照這次列出的順序指定（越前面 tie_breaker 越大）
            for e in session['entries'].values():
                e.pop('tie_breaker', None)
            for idx, name in enumerate(names):
                session['entries'][name]['tie_breaker'] = len(names) - idx
            init_sessions_save()
        embed = format_init_embed(session or {'entries': {}})
        notes = []
        if names:
            notes.append(f"✅ 已依序調整：{' → '.join(names)}（這幾位會排在其他人前面，不需要數值同分也能調整）")
        if bad:
            notes.append("⚠️ 名單裡沒有這些名字，已跳過：\n" + "\n".join(f"`{b}`" for b in bad))
        await interaction.response.send_message(content="\n".join(notes) if notes else None, embed=embed)

class InitClearConfirmView(discord.ui.View):
    """面板「🧹 清空」的二次確認（ephemeral，只有按的 GM 看得到）。"""
    def __init__(self, guild_id, channel_id, author_id):
        super().__init__(timeout=60)
        self.guild_id = guild_id
        self.channel_id = channel_id
        self.author_id = author_id

    @discord.ui.button(label="⚠️ 確認清空", style=discord.ButtonStyle.danger)
    async def confirm_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        init_sessions.pop((self.guild_id, self.channel_id), None)
        init_sessions_save()
        for k in [k for k in init_pending if k[0] == self.guild_id and k[1] == self.channel_id]:
            init_pending.pop(k, None)
        await interaction.response.edit_message(content="✅ 已清空先攻順序。", view=None)
        await interaction.followup.send(embed=discord.Embed(title="✅ 已清空先攻順序", color=0x00aaff))

    @discord.ui.button(label="取消", style=discord.ButtonStyle.secondary)
    async def cancel_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        await interaction.response.edit_message(content="已取消，先攻名單原封不動。", view=None)

class InitEndCombatConfirmView(discord.ui.View):
    """面板「🏁 結束戰鬥」的二次確認（ephemeral，只有按的 GM 看得到）。
    確認後公開宣告戰鬥結束（附輪數），並把先攻名單、回合指標、等待中的擲骰登記一併清空。"""
    def __init__(self, guild_id, channel_id, author_id):
        super().__init__(timeout=60)
        self.guild_id = guild_id
        self.channel_id = channel_id
        self.author_id = author_id

    @discord.ui.button(label="🏁 確認結束戰鬥", style=discord.ButtonStyle.success)
    async def confirm_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        key = (self.guild_id, self.channel_id)
        session = init_sessions.pop(key, None)
        init_sessions_save()
        for k in [k for k in init_pending if k[0] == self.guild_id and k[1] == self.channel_id]:
            init_pending.pop(k, None)
        round_no = (session or {}).get('round')
        desc = f"本場共進行 **{round_no}** 輪。" if round_no else ""
        desc += "先攻名單已清空，辛苦各位了！"
        await interaction.response.edit_message(content="✅ 已結束戰鬥。", view=None)
        await interaction.followup.send(embed=discord.Embed(title="🏁 戰鬥結束！", description=desc, color=0x00aa00))

    @discord.ui.button(label="取消", style=discord.ButtonStyle.secondary)
    async def cancel_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        await interaction.response.edit_message(content="已取消，戰鬥繼續。", view=None)

class InitPanelView(discord.ui.View):
    """`.init` 叫出的操作面板：第一排是玩家自助按鈕（人人可按、只作用在自己身上），
    第二排是 GM 專用按鈕（按下去當場驗權限，非 GM 會被 ephemeral 訊息擋掉）。
    這是 persistent view（timeout=None＋每顆按鈕都有 custom_id，並在 on_ready 註冊）：
    面板永不失效，連 bot 重啟後舊面板的按鈕都還能按（頻道對應到哪個先攻名單
    是按下按鈕時從 interaction 現場取得的，所以同一個 view 實例可以服務所有頻道）。"""
    def __init__(self):
        super().__init__(timeout=None)

    @staticmethod
    def _key(interaction):
        return (interaction.guild_id, interaction.channel_id)

    async def _refresh(self, interaction):
        """把面板本體的名單 embed 更新成最新狀態。"""
        session = init_sessions.get(self._key(interaction)) or {'entries': {}}
        await interaction.response.edit_message(embed=format_init_embed(session), view=self)

    async def _gm_gate(self, interaction):
        if not is_gm(interaction.guild_id, interaction.channel_id, interaction.user.id):
            await interaction.response.send_message("這顆是 GM 專用按鈕。請先用 `.drgm addgm` 登記為本頻道 GM。", ephemeral=True)
            return False
        return True

    # ---------- 第一排：玩家自助 ----------
    @discord.ui.button(label="⚔️ 敏捷作為先攻", style=discord.ButtonStyle.primary, row=0, custom_id="init_panel:join")
    async def join_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        """優先抓你在本頻道啟用中的角色卡敏捷值直接登記；沒有角色卡（或角色卡沒填敏捷值）
        就跳表單讓你自己手動打敏捷數值，兩種情況都不用擲骰。"""
        guild_id, channel_id = self._key(interaction)
        alias, dex = join_init_with_own_pc_card(guild_id, channel_id, interaction.user.id)
        if alias is None:
            await interaction.response.send_modal(
                InitManualDexModal(guild_id, channel_id, interaction.user.id, interaction.user.display_name)
            )
            return
        await self._refresh(interaction)
        await interaction.followup.send(f"✅ 已用「{alias}」的 DEX {dex} 登記/更新你的先攻。", ephemeral=True)

    @discord.ui.button(label="🎲 擲骰檢定作為先攻", style=discord.ButtonStyle.primary, row=0, custom_id="init_panel:roll")
    async def roll_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        uid = interaction.user.id
        guild_id, channel_id = self._key(interaction)
        alias = pc_active_manager.get_active(guild_id, channel_id, uid)
        if not alias:
            # 沒有啟用中的角色卡 → 直接跳表單問名字/職業，填完才進入等待擲骰狀態
            await interaction.response.send_modal(InitRollNameModal(guild_id, channel_id, uid))
            return
        init_pending[(guild_id, channel_id, uid)] = {'name': alias, 'expire': time.time() + INIT_PENDING_TIMEOUT}
        await interaction.response.send_message(embed=discord.Embed(
            title="🎲 等待你的先攻擲骰",
            description=f"角色：「{alias}」\n請在 {INIT_PENDING_TIMEOUT} 秒內於本頻道擲骰——`.cc 敏捷`（或任何技能檢定）或通用骰子 `xdy+z`／`xdy` 都行，下一次擲骰結果會自動登記成先攻。",
            color=0x00aaff,
        ), ephemeral=True)

    @discord.ui.button(label="🔫 持械／施法 +50", style=discord.ButtonStyle.secondary, row=0, custom_id="init_panel:gun")
    async def gun_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        uid = interaction.user.id
        guild_id, channel_id = self._key(interaction)
        session = init_sessions.setdefault((guild_id, channel_id), {'entries': {}})
        alias = pc_active_manager.get_active(guild_id, channel_id, uid)
        entry = session['entries'].get(alias) if alias else None
        if entry is None:
            # 還沒在名單上 → 先照「敏捷作為先攻」按鈕的角色卡登記方式登記，再直接標記
            alias, dex = join_init_with_own_pc_card(guild_id, channel_id, uid)
            if alias is None:
                if not session['entries']:
                    init_sessions.pop((guild_id, channel_id), None)
                await interaction.response.send_message(
                    "本頻道沒有你啟用中的角色卡（或角色卡沒有敏捷值），無法自助標記。"
                    "可以先按「⚔️ 敏捷作為先攻」手動填敏捷登記後再標記；"
                    "NPC 請 GM 用「➕ 登記 NPC」時在該行填上「是否持有槍械＝是」；用「擲骰檢定作為先攻」登記的不適用 +50。",
                    ephemeral=True,
                )
                return
            entry = session['entries'][alias]
        if entry.get('kind') != 'dex':
            await interaction.response.send_message(
                f"「{alias}」是用擲骰結果登記的先攻，持械備射／施法準備的 DEX +50 只適用「以 DEX 數值登記」的條目。",
                ephemeral=True,
            )
            return
        entry['ready'] = not entry.get('ready', False)
        init_sessions_save()
        state = "已標記 🔫 持械備射／施法準備（先攻 DEX +50）" if entry['ready'] else "已取消持械備射／施法準備標記"
        await self._refresh(interaction)
        await interaction.followup.send(f"✅ {state}：「{alias}」", ephemeral=True)

    @discord.ui.button(label="📋 查看先攻表", style=discord.ButtonStyle.secondary, row=0, custom_id="init_panel:list")
    async def list_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        """人人可按：把最新的先攻名單公開貼一份在頻道最下面（戰鬥中面板常被訊息洗上去，
        這顆讓大家不用往回捲），同時把面板本體的名單也刷新成最新狀態。"""
        session = init_sessions.get(self._key(interaction)) or {'entries': {}}
        await interaction.response.send_message(embed=format_init_embed(session))
        if interaction.message:
            try:
                await interaction.message.edit(embed=format_init_embed(session), view=self)
            except Exception:
                pass

    # ---------- 第二排：GM 專用 ----------
    @discord.ui.button(label="➕ 登記 NPC", style=discord.ButtonStyle.secondary, row=1, custom_id="init_panel:npc")
    async def npc_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not await self._gm_gate(interaction):
            return
        await interaction.response.send_modal(InitNpcAddModal(interaction.guild_id, interaction.channel_id))

    @discord.ui.button(label="🗑️ 移除", style=discord.ButtonStyle.secondary, row=1, custom_id="init_panel:del")
    async def del_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not await self._gm_gate(interaction):
            return
        session = init_sessions.get(self._key(interaction))
        if not session or not session['entries']:
            await interaction.response.send_message("先攻名單是空的，沒有東西可以移除。", ephemeral=True)
            return
        names = list(session['entries'].keys())
        desc = "從下面的選單勾選要移除的參戰者（可多選）。"
        if len(names) > 25:
            desc += "\n⚠️ 名單超過 25 個，選單只顯示前 25 個，請分批移除。"
            names = names[:25]
        await interaction.response.send_message(
            embed=discord.Embed(title="🗑️ 移除先攻條目", description=desc, color=0x00aaff),
            view=InitDelSelectView(interaction.user.id, interaction.guild_id, interaction.channel_id, names),
            ephemeral=True,
        )

    @discord.ui.button(label="↕️ 調整順序", style=discord.ButtonStyle.secondary, row=1, custom_id="init_panel:rank")
    async def rank_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not await self._gm_gate(interaction):
            return
        session = init_sessions.get(self._key(interaction))
        if not session or not session['entries']:
            await interaction.response.send_message("先攻名單是空的，沒有東西可以調整。", ephemeral=True)
            return
        await interaction.response.send_modal(InitRankModal(interaction.guild_id, interaction.channel_id))

    @discord.ui.button(label="🧹 清空", style=discord.ButtonStyle.danger, row=1, custom_id="init_panel:clear")
    async def clear_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not await self._gm_gate(interaction):
            return
        await interaction.response.send_message(
            "確定要清空整份先攻名單嗎？",
            view=InitClearConfirmView(interaction.guild_id, interaction.channel_id, interaction.user.id),
            ephemeral=True,
        )

    @discord.ui.button(label="🏁 結束戰鬥", style=discord.ButtonStyle.success, row=1, custom_id="init_panel:end_combat")
    async def end_combat_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not await self._gm_gate(interaction):
            return
        session = init_sessions.get(self._key(interaction))
        if not session or not session['entries']:
            await interaction.response.send_message("目前沒有進行中的戰鬥（先攻名單是空的）。", ephemeral=True)
            return
        await interaction.response.send_message(
            "確定要結束這場戰鬥嗎？會公開宣告戰鬥結束並清空先攻名單。",
            view=InitEndCombatConfirmView(interaction.guild_id, interaction.channel_id, interaction.user.id),
            ephemeral=True,
        )

    @discord.ui.button(label="🔄 重置輪數", style=discord.ButtonStyle.secondary, row=2, custom_id="init_panel:reset_round")
    async def reset_round_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        """（GM 專用）保留目前的先攻名單，只把輪數計數與回合指標歸零：
        適合同一批參戰者接著打下一場的情況——名單、敏捷值、持械 +50 狀態都原封不動，
        下一次 `.pass` 會重新宣告「第 1 輪開始」並從名單第 1 位點名。
        row=1 已放滿 5 顆按鈕（Discord 每排上限），所以放在第 3 排。"""
        if not await self._gm_gate(interaction):
            return
        session = init_sessions.get(self._key(interaction))
        if not session or not session['entries']:
            await interaction.response.send_message("目前沒有先攻名單，沒有輪數可以重置。", ephemeral=True)
            return
        old_round = session.get('round') or 0
        session['round'] = 0
        session['turn_name'] = None
        init_sessions_save()
        await self._refresh(interaction)
        desc = (f"上一場進行到第 **{old_round}** 輪。\n" if old_round else "")
        desc += "先攻名單原封不動，輪數與回合指標已歸零；下一次 `.pass` 會從**第 1 輪**、名單第 1 位重新開始。"
        await interaction.followup.send(embed=discord.Embed(title="🔄 已重置輪數（保留先攻名單）", description=desc, color=0x00aaff))

def maybe_capture_init_roll(message, target_type, roll_value, level=None):
    """如果這個人剛才用 `.init roll [名字]` 表示『下一次擲骰就是我的先攻』，
    這裡負責把這次擲骰結果（.cc 技能檢定或通用骰子都行）登記進先攻名單。
    沒有在等待中，或不是公開檢定（暗骰不算），就什麼都不做、回傳 None。
    有登記成功的話，回傳一段可以直接接在原本擲骰結果後面的提示文字。"""
    if target_type != 'channel':
        return None
    guild_id, channel_id, user_id = message.guild.id, message.channel.id, message.author.id
    pending_key = (guild_id, channel_id, user_id)
    pending = init_pending.get(pending_key)
    if not pending or pending['expire'] < time.time():
        init_pending.pop(pending_key, None)
        return None
    if roll_value is None:
        return None
    init_pending.pop(pending_key, None)
    session_key = (guild_id, channel_id)
    session = init_sessions.setdefault(session_key, {'entries': {}})
    name = pending['name']
    if level is not None:
        session['entries'][name] = {'kind': 'roll_check', 'roll': roll_value, 'level': level, 'user_id': user_id}
    else:
        session['entries'][name] = {'kind': 'roll_generic', 'roll': roll_value, 'user_id': user_id}
    init_sessions_save()
    return f"\n\n⚔️ 已登記「{name}」的先攻：{_init_entry_text(session['entries'][name])}"


_CHASE_ROLE_LABEL = {'pursuer': '追逐者', 'evader': '逃跑者'}

def _chase_compute_actions(participants):
    """規則書的『行動次數』：MOV 最低的人每回合 1 個行動，MOV 比他高多少，每回合就多幾個行動。
    只有『有填 MOV』的人才會被計入比較跟顯示；沒填 MOV 的人維持預設 1 次行動、不特別標註。
    回傳 {名字: 行動次數}，只包含有填 MOV 的人。"""
    movs = {name: p['mov'] for name, p in participants.items() if p.get('mov') is not None}
    if not movs:
        return {}
    min_mov = min(movs.values())
    return {name: 1 + (mov - min_mov) for name, mov in movs.items()}

# ---------- 速度檢定（追逐開始前，決定要不要正式進入追逐） ----------
_CHASE_SPEED_DELTA = {'大成功': 1, '成功': 0, '失敗': -1}
_CHASE_SPEED_ALIASES = {
    '大成功': '大成功', '大成': '大成功', '極限成功': '大成功', 'crit': '大成功', 'critical': '大成功',
    '成功': '成功', '一般成功': '成功', '普通成功': '成功', 'success': '成功', '成': '成功',
    '失敗': '失敗', '失敗了': '失敗', 'fail': '失敗', 'failure': '失敗', '失': '失敗',
}

def _parse_chase_speed_result(text):
    """把速度檢定表單裡的自由文字（大成功／成功／失敗，或常見同義詞）正規化成三選一，看不懂回傳 None。"""
    key = text.strip()
    return _CHASE_SPEED_ALIASES.get(key)

def _chase_evaluate_pursuit_outcomes(participants):
    """速度檢定／MOV 異動後重新判定每個『追逐者－目標』配對的結果：
    只有兩邊都填了 MOV 才能比較；目標 MOV > 追逐者 MOV → 這個追逐者被甩開（'escaped'），
    否則正式進入追逐（'started'）。結果直接寫回各追逐者的 'chase_outcome' 欄位，供面板顯示。"""
    for p in participants.values():
        if p['role'] != 'pursuer':
            continue
        target = participants.get(p.get('target'))
        if p.get('mov') is None or not target or target.get('mov') is None:
            p.pop('chase_outcome', None)
            continue
        p['chase_outcome'] = 'escaped' if target['mov'] > p['mov'] else 'started'

def _chase_start_round(session):
    """開新回合：把每個人『本回合剩餘行動點』重置為規則書算出來的行動次數
    （沒填 MOV 的人預設 1 次，跟 format_chase_embed 顯示邏輯一致）。回傳 (回合數, action_counts)。"""
    participants = session['participants']
    action_counts = _chase_compute_actions(participants)
    for name, p in participants.items():
        p['actions_left'] = action_counts.get(name, 1)
    session['round'] = session.get('round', 0) + 1
    return session['round'], action_counts

def _chase_resolve_member(guild, guild_id, name):
    """把追逐參戰者名字解析成真正的 Discord 成員（攻擊時當防禦方一定要能 @提及本人做出反擊／閃避的反應）。
    只有『剛好對到一張角色卡、且擁有者還在伺服器裡』才算數；NPC、找不到、同名多筆都回傳 None。"""
    if not guild:
        return None
    matches = pc_card_manager.find_card_by_alias_in_guild(guild_id, name)
    if len(matches) != 1:
        return None
    try:
        return guild.get_member(int(matches[0][0]))
    except (TypeError, ValueError):
        return None

def _chase_is_owned_by(guild_id, user_id, name):
    """判斷某個追逐參戰者名字是不是這位玩家自己的角色：角色卡名稱剛好唯一對到這個名字、
    而且擁有者就是他（不限是不是『目前在本頻道啟用中』的卡，只要是他建立的角色卡就算，
    涵蓋『他開啟的角色卡』跟『他建立的角色』兩種說法）。NPC（沒有對應角色卡）一律不算任何玩家的。"""
    matches = pc_card_manager.find_card_by_alias_in_guild(guild_id, name)
    return len(matches) == 1 and str(matches[0][0]) == str(user_id)

def _chase_owned_names(guild_id, user_id, participants):
    """列出這場追逐裡，目前屬於這位玩家自己的參戰者名字（順序跟 participants 一致）。"""
    return [name for name in participants if _chase_is_owned_by(guild_id, user_id, name)]

def _chase_resolve_attacker_skill(guild_id, actor_name, skill_text):
    """解析追逐『攻擊』動作的攻擊方技能：純數字直接當技能值；不是數字就跨玩家搜尋角色卡
    （用追逐參戰者名字，不限本人操作面板，方便 GM 幫任何人動作）找同名技能。
    回傳 (技能顯示名稱, 數值)，解析失敗回傳 (None, None)。"""
    skill_text = skill_text.strip()
    if skill_text.isdigit():
        return "", int(skill_text)
    matches = pc_card_manager.find_card_by_alias_in_guild(guild_id, actor_name)
    if len(matches) != 1:
        return None, None
    skill_lookup = build_pc_skill_lookup(matches[0][2])
    found = fuzzy_match_skill(skill_lookup, skill_text)
    return found[0] if len(found) == 1 else (None, None)

async def _chase_start_attack(interaction, atk_display_name, atk_skill_name, atk_value, defender, bonus_dice=0, range_note=""):
    """追逐面板『攻擊』動作觸發的近戰／跨節點射擊判定，跟 `.melee` 共用同一套反擊／閃避機制
    （MeleeResponseView／melee_pending_store），只是攻擊方擲骰改用傳入的 bonus_dice（跨節點時是懲罰骰）。"""
    crit_range, fumble_range = get_effective_range(interaction)
    atk_roll, atk_level, atk_bonus_desc, _ = coc_check(atk_value, bonus_dice, crit_range, fumble_range)
    def_display_name = _melee_display_name(interaction.guild_id, interaction.channel_id, defender)
    head = f"**{atk_display_name}** 對 **{def_display_name}** 發動攻擊！{range_note}\n（{atk_skill_name or '技能值'} {atk_value}%）\n{atk_bonus_desc} → 擲骰 {atk_roll} → **{atk_level}**\n\n"
    if atk_level in MELEE_ATTACKER_FAIL_LEVELS:
        await interaction.channel.send(embed=discord.Embed(
            title="⚔️ 追逐中的攻擊",
            description=head + f"💨 攻擊方失敗，攻擊沒有命中，不會觸發 {def_display_name} 的反擊／閃避判定。",
            color=0x999999,
        ))
        return
    view = MeleeResponseView()
    embed = discord.Embed(
        title="⚔️ 追逐中的攻擊",
        description=head + (
            f"{defender.mention} 請選擇要【反擊】還是【閃避】。\n"
            f"按鈕不會過期，晚一點再回來按也可以。"
        ),
        color=0x00aaff,
    )
    sent = await interaction.channel.send(embed=embed, view=view)
    _melee_register_pending(sent, _melee_new_state(
        'melee', interaction.guild_id, interaction.channel_id, interaction.user, defender,
        atk_skill_name, atk_value, atk_level, atk_roll, atk_bonus_desc,
        atk_display_name, def_display_name,
    ))

_CHASE_RANDOM_SKILL_POOL = [
    '跳躍', '游泳', '攀爬', '話術', '恐嚇', '潛行', '偵查', '聆聽',
    '心理學', '鬥毆', '敏捷', '力量', '駕駛-汽車', '閃避',
]
# 常見障礙的參考HP（規則書範例），隨機產生障礙時依難度從對應的區間挑一個
_CHASE_OBSTACLE_HP_TABLE = {
    '一般': [5, 10],       # 房門或薄木頭柵欄 5HP、標準後門 10HP
    '困難': [15, 25],      # 堅固的家用前門 15HP、九吋磚牆 25HP
    '極端': [50, 100],     # 大樹 50HP、水泥橋墩 100HP
}
_CHASE_HAZARD_CONSEQUENCE = {
    '一般': ('1D3-1', '輕微'),
    '困難': ('1D6', '中度'),
    '極端': ('1D10', '重度'),
}

def _chase_d100_tier(roll):
    """規則書原文的區位危害/障礙表：01-59 淨空、60-84 一般、85-95 困難（原文「艱難」）、96-100 極端。"""
    if roll <= 59:
        return None
    elif roll <= 84:
        return '一般'
    elif roll <= 95:
        return '困難'
    else:
        return '極端'

def _generate_random_chase_encounters(length):
    """完全照規則書的 d100 表隨機產生每個區位的內容：
    每個區位擲一次 1D100 決定「淨空／一般／困難／極端」，有危害/障礙的區位再隨機決定
    這次是『障礙』（擋路，給對應難度的參考HP）還是『危害』（不擋路但失敗會受傷，給對應難度的傷害骰）。
    回傳 (obstacles, hazards) 兩個 dict：
      obstacles[pos] = {'note': str, 'hp': int, 'max_hp': int}
      hazards[pos]   = str（多行說明文字）"""
    obstacles, hazards = {}, {}
    for pos in range(1, length + 1):
        tier = _chase_d100_tier(random.randint(1, 100))
        if tier is None:
            continue
        if random.random() < 0.6:  # 危害比障礙常見一些
            skill_count = random.randint(2, 4)
            skills = random.sample(_CHASE_RANDOM_SKILL_POOL, min(skill_count, len(_CHASE_RANDOM_SKILL_POOL)))
            hp_dice, severity = _CHASE_HAZARD_CONSEQUENCE[tier]
            hazards[pos] = (
                f"{tier}難度 危害\n"
                f"可能檢定：{' '.join(skills)}\n"
                f"失敗：{hp_dice} {severity}事故傷害，及失去（1D3）點行動點"
            )
        else:
            hp = random.choice(_CHASE_OBSTACLE_HP_TABLE[tier])
            obstacles[pos] = {'note': f"{tier}難度 障礙，需要開鎖/破壞/繞過才能通過", 'hp': hp, 'max_hp': hp}
    return obstacles, hazards

def format_chase_embed(session):
    """依「區位」分類列出：每個位置各自成一個區塊，寫「這個位置有誰、有什麼障礙／危害」，
    只列出「有內容」的位置（沒人也沒障礙／危害的位置直接跳過，不用每格都列）。
    全部用文字標示，不用 emoji，降低視覺噪音也方便文字閱讀器/複製貼上。"""
    length = session['length']
    obstacles = session['obstacles']
    hazards = session.get('hazards', {})
    participants = session['participants']

    desc_lines = [f"賽道長度：{length} 個區位"]

    if not participants and not obstacles and not hazards:
        desc_lines.append("\n目前沒有參戰者、也沒有障礙／危害，用面板的「✏️ 編輯參戰者」「⚠️ 障礙／危害設置」設置。")
        return discord.Embed(title="追逐進行中", description="\n".join(desc_lines), color=0x00aaff)

    pos_participants = defaultdict(list)
    for name, p in participants.items():
        pos_participants[p['position']].append((name, p))

    action_counts = _chase_compute_actions(participants)
    all_positions = sorted(set(pos_participants) | set(obstacles) | set(hazards))

    desc_lines.append("")
    desc_lines.append("**依區位列出（只列出有人或有障礙／危害的位置）：**")
    if not all_positions:
        desc_lines.append("目前沒有人在賽道上。")

    for pos in all_positions:
        desc_lines.append(f"\n【位置 {pos}／{length}】")

        people = pos_participants.get(pos, [])
        if people:
            for name, p in sorted(people, key=lambda kv: kv[1]['role'] != 'pursuer'):
                role_label = _CHASE_ROLE_LABEL[p['role']]
                bits = [role_label]
                if p.get('mov') is not None:
                    if 'actions_left' in p:
                        bits.append(f"MOV {p['mov']}，本回合剩餘 {p['actions_left']}／{action_counts.get(name, 1)} 點行動")
                    else:
                        bits.append(f"MOV {p['mov']}，本回合 {action_counts.get(name, 1)} 次行動")
                if p.get('speed_result'):
                    bits.append(f"速度檢定：{p['speed_result']}")
                if p['role'] == 'pursuer':
                    target = p.get('target')
                    if target and target in participants:
                        gap = participants[target]['position'] - pos
                        bits.append(f"追「{target}」距離 {abs(gap)}{'（已超過目標！）' if gap < 0 else ''}")
                    else:
                        bits.append("尚未指定目標")
                    if p.get('chase_outcome') == 'escaped':
                        bits.append("⚠️ 已被目標甩開，追逐結束")
                    elif p.get('chase_outcome') == 'started':
                        bits.append("✅ 已正式進入追逐")
                desc_lines.append(f"- {name}（{'，'.join(bits)}）")
        else:
            desc_lines.append("- （目前沒有人在這個位置）")

        if pos in obstacles:
            ob = obstacles[pos]
            hp_text = f"，HP {ob['hp']}/{ob['max_hp']}" if ob.get('hp') is not None else ""
            note_lines = str(ob['note']).split('\n')
            desc_lines.append(f"- 障礙：{note_lines[0]}{hp_text}")
            for extra_line in note_lines[1:]:
                desc_lines.append(f"　{extra_line}")

        if pos in hazards:
            note_lines = str(hazards[pos]).split('\n')
            desc_lines.append(f"- 危害：{note_lines[0]}")
            for extra_line in note_lines[1:]:
                desc_lines.append(f"　{extra_line}")

    return discord.Embed(title="追逐進行中", description="\n".join(desc_lines), color=0x00aaff)

def _format_chase_obstacles_text(obstacles):
    """把障礙資料轉成 Modal 用的『一行一個』文字，格式：位置:說明[:HP]（沒設HP就不加這一段）。
    說明本身如果是多行，先壓成單行（用「／」接起來），避免預填進 Modal 後原封不動送出時被誤判。"""
    lines = []
    for pos, ob in sorted(obstacles.items()):
        note = str(ob['note']).replace(chr(10), '／')
        if ob.get('hp') is not None:
            lines.append(f"{pos}:{note}:{ob['hp']}")
        else:
            lines.append(f"{pos}:{note}")
    return "\n".join(lines)

def _format_chase_hazards_text(hazards):
    """把危害資料轉成 Modal 用的『一行一個』文字，格式：位置:說明（危害沒有HP可打，純文字說明）。"""
    return "\n".join(f"{pos}:{str(note).replace(chr(10), '／')}" for pos, note in sorted(hazards.items()))

def _chase_empty_embed():
    return discord.Embed(
        title="🏃 追逐",
        description="本頻道目前沒有進行中的追逐。GM 可以按下面的「🎲 隨機產生賽道」開始一場。",
        color=0x00aaff,
    )

def _parse_chase_participant_line(line, role, guild_id, length_val, errors, pulled_from_card):
    """把一行『名字 位置 [目標] [MOV]』文字（空格分隔，右側欄位可省略）轉成 (名字, 參戰者資料)。
    共用於「參戰者細節表單」：位置省略預設1，MOV 省略時改用名字查角色卡自動帶入（找不到就留空）。"""
    parts = line.split()
    if not parts:
        return None, None
    name = parts[0]

    pos = 1
    if len(parts) >= 2:
        if parts[1].isdigit():
            pos = max(1, min(length_val, int(parts[1])))
        else:
            errors.append(f"「{line}」的起始位置看不懂，已用預設值 1")

    target = None
    mov = None
    if role == 'pursuer':
        if len(parts) >= 3:
            target = parts[2]
        if len(parts) >= 4:
            if parts[3].isdigit():
                mov = int(parts[3])
            else:
                errors.append(f"「{line}」的 MOV 看不懂，已忽略")
    else:
        if len(parts) >= 3:
            if parts[2].isdigit():
                mov = int(parts[2])
            else:
                errors.append(f"「{line}」的 MOV 看不懂，已忽略")

    if mov is None:
        matches = pc_card_manager.find_card_by_alias_in_guild(guild_id, name)
        if len(matches) == 1 and matches[0][2].get('mov') is not None:
            mov = matches[0][2]['mov']
            pulled_from_card.append(f"「{name}」自動帶入角色卡的 MOV {mov}")

    return name, {'role': role, 'position': pos, 'target': target, 'mov': mov}

class ChaseSpeedCheckModal(discord.ui.Modal, title="🚦 速度檢定"):
    """追逐開始前的『要不要追得到／甩不甩得掉』檢定：GM 場外自己骰（徒步骰體質、開車骰汽車駕駛），
    在這裡把每個人的結果（大成功／成功／失敗）打進去，程式負責算 MOV±1 跟比較兩邊的結果。
    表單預填目前所有參戰者名字，GM 只要在後面補結果就好；沒填 MOV 的人不會被調整（會在結果裡註明）。"""
    def __init__(self, guild_id, channel_id, session, allowed_names=None):
        super().__init__()
        self.guild_id = guild_id
        self.channel_id = channel_id
        self.allowed_names = allowed_names  # None＝GM，不限制；否則只能填這份名單裡的名字（自己的角色）
        names = allowed_names if allowed_names is not None else list(session['participants'])
        default_text = "\n".join(f"{name} " for name in names)
        self.results = discord.ui.TextInput(
            label="每人一行：名字 大成功／成功／失敗",
            style=discord.TextStyle.paragraph,
            default=default_text or None,
            required=True, max_length=1500,
            placeholder="阿明 成功\n邪教徒A 大成功\n邪教徒B 失敗",
        )
        self.add_item(self.results)

    async def on_submit(self, interaction: discord.Interaction):
        key = (self.guild_id, self.channel_id)
        session = chase_sessions.get(key)
        if not session:
            await interaction.response.send_message(
                embed=discord.Embed(title="❌ 追逐已經結束或不存在", description="請先按「🎲 隨機產生賽道」開始一場追逐。", color=0xff0000),
                ephemeral=True,
            )
            return
        participants = session['participants']
        errors, applied = [], []
        for line in str(self.results.value).splitlines():
            line = line.strip()
            if not line:
                continue
            parts = line.split(None, 1)
            name = parts[0]
            p = participants.get(name)
            if not p:
                errors.append(f"「{name}」不在目前的參戰者名單裡，已跳過")
                continue
            if self.allowed_names is not None and name not in self.allowed_names:
                errors.append(f"「{name}」不是你自己的角色，已跳過（只能填自己開的角色卡或建立的角色）")
                continue
            result = _parse_chase_speed_result(parts[1]) if len(parts) >= 2 else None
            if not result:
                errors.append(f"「{name}」的檢定結果看不懂（要是「大成功」／「成功」／「失敗」），已跳過")
                continue
            p['speed_result'] = result
            if p.get('mov') is None:
                errors.append(f"「{name}」沒有設定 MOV，結果已記錄但不會調整 MOV")
                continue
            old_mov = p['mov']
            p['mov'] = max(0, old_mov + _CHASE_SPEED_DELTA[result])
            applied.append(f"{name}：{result}，MOV {old_mov} → {p['mov']}")

        _chase_evaluate_pursuit_outcomes(participants)

        verdict_lines = []
        for name, p in participants.items():
            if p['role'] != 'pursuer' or not p.get('target'):
                continue
            target = participants.get(p['target'])
            if not target:
                continue
            if p.get('chase_outcome') == 'escaped':
                verdict_lines.append(f"「{p['target']}」MOV {target['mov']} ＞「{name}」MOV {p['mov']} → {name} 被甩開，追逐結束")
            elif p.get('chase_outcome') == 'started':
                verdict_lines.append(f"「{name}」MOV {p['mov']} ≧「{p['target']}」MOV {target['mov']} → 正式進入追逐")

        desc_lines = ["**檢定結果：**"] + (applied or ["（沒有套用任何結果）"])
        if verdict_lines:
            desc_lines.append("\n**追／逃判定：**")
            desc_lines.extend(verdict_lines)
        embed = discord.Embed(title="🚦 速度檢定結果", description="\n".join(desc_lines), color=0x00aaff)
        if errors:
            embed.add_field(name="⚠️ 有些內容跳過了", value="\n".join(errors)[:1024], inline=False)
        await interaction.response.send_message(embed=embed)
        await interaction.channel.send(embed=format_chase_embed(session))
        await _chase_refresh_panel(interaction.channel, self.guild_id, self.channel_id)

class ChaseHazardModal(discord.ui.Modal, title="⚠️ 設置障礙／危害"):
    """只調整這場追逐的障礙／危害內容，不影響賽道長度跟參戰者。格式維持原本的「一行一筆」，
    欄位用「:」分隔，位置可以省略（預設1）：障礙格式「位置:說明[:HP]」，危害格式「位置:說明」。
    送出後這兩項會被表單內容整個覆蓋（單一位置想清掉，把那一行從表單裡刪掉再送出就好）。"""
    def __init__(self, guild_id, channel_id, session):
        super().__init__()
        self.guild_id = guild_id
        self.channel_id = channel_id
        self.length_val = session['length']
        self.obstacles = discord.ui.TextInput(
            label="障礙：擋路，沒過檢定不能通過（可留空；位置:說明[:HP]）",
            style=discord.TextStyle.paragraph,
            default=_format_chase_obstacles_text(session['obstacles']),
            required=False, max_length=1000,
            placeholder="3:上鎖的門:10\n5:斷橋，需要跳過",
        )
        self.hazards = discord.ui.TextInput(
            label="危害：不擋路，沒過檢定會受傷（可留空；位置:說明）",
            style=discord.TextStyle.paragraph,
            default=_format_chase_hazards_text(session.get('hazards', {})),
            required=False, max_length=1000,
            placeholder="2:困難難度 危害／可能檢定：跳躍 游泳／失敗：1D6 中度事故傷害",
        )
        self.add_item(self.obstacles)
        self.add_item(self.hazards)

    async def on_submit(self, interaction: discord.Interaction):
        key = (self.guild_id, self.channel_id)
        session = chase_sessions.get(key)
        if not session:
            await interaction.response.send_message(
                embed=discord.Embed(title="❌ 追逐已經結束或不存在", description="請先按「🎲 隨機產生賽道」開始一場追逐。", color=0xff0000),
                ephemeral=True,
            )
            return
        length_val = session['length']
        errors = []
        new_obstacles = {}
        for line in str(self.obstacles.value).splitlines():
            line = line.strip()
            if not line:
                continue
            if ':' not in line:
                errors.append(f"障礙「{line}」格式看不懂（要是「位置:說明[:HP]」），已跳過")
                continue
            pos_str, rest = line.split(':', 1)
            pos_str = pos_str.strip()
            if not pos_str.isdigit() or not (1 <= int(pos_str) <= length_val):
                errors.append(f"障礙「{line}」位置不在 1~{length_val} 範圍內，已跳過")
                continue
            hp = None
            if ':' in rest:
                maybe_note, maybe_hp = rest.rsplit(':', 1)
                if maybe_hp.strip().isdigit():
                    rest, hp = maybe_note, int(maybe_hp.strip())
            note = rest.strip()
            if note:
                new_obstacles[int(pos_str)] = {'note': note, 'hp': hp, 'max_hp': hp}

        new_hazards = {}
        for line in str(self.hazards.value).splitlines():
            line = line.strip()
            if not line:
                continue
            if ':' not in line:
                errors.append(f"危害「{line}」格式看不懂（要是「位置:說明」），已跳過")
                continue
            pos_str, note = (p.strip() for p in line.split(':', 1))
            if not pos_str.isdigit() or not (1 <= int(pos_str) <= length_val):
                errors.append(f"危害「{line}」位置不在 1~{length_val} 範圍內，已跳過")
                continue
            if note:
                new_hazards[int(pos_str)] = note

        session['obstacles'] = new_obstacles
        session['hazards'] = new_hazards
        embed = format_chase_embed(session)
        if errors:
            embed.add_field(name="⚠️ 有些內容跳過或修正了", value="\n".join(errors)[:1024], inline=False)
        await interaction.response.send_message(embed=embed)
        await _chase_refresh_panel(interaction.channel, self.guild_id, self.channel_id)

class ChaseParticipantDetailModal(discord.ui.Modal, title="🏃 填寫參戰者細節"):
    """加入參戰者的最後一步：兩個欄位，一行一個，空格分隔，格式跟以前一樣
    （逃跑者「名字 位置 MOV」／追逐者「名字 位置 目標 MOV」，右側欄位都可省略）。
    差別是勾過角色卡選單的名字會預先幫你填好（只要接著補位置/MOV/目標）；
    沒開卡的人（NPC）也可以直接在同一個欄位裡自己手打新的一行，格式相同，兩者可以並存。
    送出後是『新增或更新』：只會動到這次表單裡出現的名字，其他既有參戰者不受影響。"""
    def __init__(self, guild_id, channel_id, evader_names, pursuer_names):
        super().__init__()
        self.guild_id = guild_id
        self.channel_id = channel_id
        self.evaders = discord.ui.TextInput(
            label="逃跑者（一行一個：名字 位置 MOV，右側可留空）",
            style=discord.TextStyle.paragraph,
            default="\n".join(evader_names) if evader_names else None,
            required=False, max_length=1000,
            placeholder="阿明 3 8\n阿華",
        )
        self.pursuers = discord.ui.TextInput(
            label="追逐者（一行一個：名字 位置 目標 MOV，右側可留空）",
            style=discord.TextStyle.paragraph,
            default="\n".join(pursuer_names) if pursuer_names else None,
            required=False, max_length=1000,
            placeholder="邪教徒A 1 阿明 9（規則書建議逃跑者站追逐者前方2個節點，直接切入高潮）\n邪教徒B",
        )
        self.add_item(self.evaders)
        self.add_item(self.pursuers)

    async def on_submit(self, interaction: discord.Interaction):
        key = (self.guild_id, self.channel_id)
        session = chase_sessions.get(key)
        if not session:
            await interaction.response.send_message(
                embed=discord.Embed(title="❌ 追逐已經結束或不存在", description="請先按「🎲 隨機產生賽道」開始一場追逐。", color=0xff0000),
                ephemeral=True,
            )
            return
        length_val = session['length']
        errors, pulled_from_card, touched = [], [], []

        for line in str(self.evaders.value).splitlines():
            line = line.strip()
            if not line:
                continue
            name, entry = _parse_chase_participant_line(line, 'evader', self.guild_id, length_val, errors, pulled_from_card)
            if name:
                session['participants'][name] = entry
                touched.append(name)

        for line in str(self.pursuers.value).splitlines():
            line = line.strip()
            if not line:
                continue
            name, entry = _parse_chase_participant_line(line, 'pursuer', self.guild_id, length_val, errors, pulled_from_card)
            if name:
                session['participants'][name] = entry
                touched.append(name)

        # 追逐者指定的目標如果不在名單裡（打錯字、還沒加逃跑者），先設為未指定，不硬塞錯的名字
        for name, p in session['participants'].items():
            if p['role'] == 'pursuer' and p.get('target') and p['target'] not in session['participants']:
                errors.append(f"「{name}」指定的目標「{p['target']}」不在名單裡，先設為未指定，之後可以再編輯補上")
                p['target'] = None

        embed = format_chase_embed(session)
        if touched:
            embed.set_footer(text=f"這次新增／更新：{'、'.join(touched)}")
        if pulled_from_card:
            embed.add_field(name="🔗 自動帶入角色卡的資料", value="\n".join(pulled_from_card)[:1024], inline=False)
        if errors:
            embed.add_field(name="⚠️ 有些內容跳過或修正了", value="\n".join(errors)[:1024], inline=False)
        await interaction.response.send_message(embed=embed)
        await _chase_refresh_panel(interaction.channel, self.guild_id, self.channel_id)

class ChaseParticipantSkipView(discord.ui.View):
    """本頻道沒有人開角色卡時走這條路：跳過選單，一顆按鈕直接開細節表單讓 GM 手動輸入（NPC 或玩家皆可）。"""
    def __init__(self, guild_id, channel_id):
        super().__init__(timeout=300)
        self.guild_id = guild_id
        self.channel_id = channel_id

    @discord.ui.button(label="📝 手動輸入參戰者", style=discord.ButtonStyle.primary)
    async def open_modal(self, interaction: discord.Interaction, button: discord.ui.Button):
        await interaction.response.send_modal(ChaseParticipantDetailModal(self.guild_id, self.channel_id, [], []))

class ChaseParticipantEvaderSelect(discord.ui.Select):
    """勾選這次要加入的『逃跑者』候選人，選項來自本頻道目前有開角色卡的人。"""
    def __init__(self, author_id, names, descriptions):
        self.author_id = author_id
        options = [
            discord.SelectOption(label=n[:100], value=str(i), description=(d[:100] if d else None))
            for i, (n, d) in enumerate(zip(names, descriptions))
        ]
        super().__init__(placeholder="勾選這次要加入的逃跑者（開卡玩家專用，可留空／可多選）", min_values=0, max_values=len(options), options=options, row=0)

    async def callback(self, interaction: discord.Interaction):
        if interaction.user.id != self.author_id:
            await interaction.response.send_message("這不是你叫出來的選單喔。", ephemeral=True)
            return
        self.view.selected_evader_idx = [int(v) for v in self.values]
        await interaction.response.defer()

class ChaseParticipantPursuerSelect(discord.ui.Select):
    """勾選這次要加入的『追逐者』候選人，選項來自本頻道目前有開角色卡的人（跟逃跑者選單共用同一份名單）。"""
    def __init__(self, author_id, names, descriptions):
        self.author_id = author_id
        options = [
            discord.SelectOption(label=n[:100], value=str(i), description=(d[:100] if d else None))
            for i, (n, d) in enumerate(zip(names, descriptions))
        ]
        super().__init__(placeholder="勾選這次要加入的追逐者（開卡玩家專用，可留空／可多選）", min_values=0, max_values=len(options), options=options, row=1)

    async def callback(self, interaction: discord.Interaction):
        if interaction.user.id != self.author_id:
            await interaction.response.send_message("這不是你叫出來的選單喔。", ephemeral=True)
            return
        self.view.selected_pursuer_idx = [int(v) for v in self.values]
        await interaction.response.defer()

class ChaseParticipantSelectView(discord.ui.View):
    """先讓 GM 從『頻道內有開卡的人』分別勾選這次要加入的逃跑者／追逐者（各自一個下拉選單，互不影響，
    一次選完不用重複開），按下確認後才進到下一步的細節表單填位置/MOV/目標；
    沒開卡的人（NPC）不在選單裡，到下一步的表單再手動加一行就好。"""
    def __init__(self, author_id, guild_id, channel_id, names, descriptions):
        super().__init__(timeout=300)
        self.author_id = author_id
        self.guild_id = guild_id
        self.channel_id = channel_id
        self.names = names
        self.selected_evader_idx = []
        self.selected_pursuer_idx = []
        self.add_item(ChaseParticipantEvaderSelect(author_id, names, descriptions))
        self.add_item(ChaseParticipantPursuerSelect(author_id, names, descriptions))
        self.sent_message = None

    @discord.ui.button(label="✅ 確認選擇，下一步填細節", style=discord.ButtonStyle.primary, row=2)
    async def confirm_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.author_id:
            await interaction.response.send_message("這不是你叫出來的選單喔。", ephemeral=True)
            return
        evader_names = [self.names[i] for i in self.selected_evader_idx]
        pursuer_names = [self.names[i] for i in self.selected_pursuer_idx]
        for child in self.children:
            child.disabled = True
        if self.sent_message:
            try:
                await self.sent_message.edit(view=self)
            except discord.HTTPException:
                pass
        await interaction.response.send_modal(
            ChaseParticipantDetailModal(self.guild_id, self.channel_id, evader_names, pursuer_names)
        )

    async def on_timeout(self):
        for child in self.children:
            child.disabled = True
        if self.sent_message:
            try:
                await self.sent_message.edit(view=self)
            except discord.HTTPException:
                pass

async def _chase_launch_participant_step(interaction, guild_id, channel_id):
    """跳出『加入參戰者』這一步：頻道內有人開角色卡的話給勾選選單，沒有就直接給一顆按鈕開手動表單。
    這是呼叫它當下那個互動（按鈕或表單送出）唯一的回應，呼叫前不能已經呼叫過 interaction.response。"""
    active = pc_active_manager.get_all_active_in_channel(guild_id, channel_id)[:25]
    names, descriptions = [], []
    guild = interaction.guild
    for user_id, alias in active:
        member = guild.get_member(user_id) if guild else None
        names.append(alias)
        descriptions.append(f"@{member.display_name}" if member else None)
    if names:
        view = ChaseParticipantSelectView(interaction.user.id, guild_id, channel_id, names, descriptions)
        await interaction.response.send_message(
            embed=discord.Embed(
                title="🏃 加入參戰者",
                description=(
                    "從下面選單勾選這次要加入的逃跑者／追逐者（開卡玩家專用，可留空、可多選）。\n"
                    "沒開卡的人（NPC）不用選，直接按「✅ 確認選擇」，下一步的表單裡再手動加一行就好。"
                ),
                color=0x00aaff,
            ),
            view=view, ephemeral=True,
        )
        view.sent_message = await interaction.original_response()
    else:
        view = ChaseParticipantSkipView(guild_id, channel_id)
        await interaction.response.send_message(
            embed=discord.Embed(
                title="🏃 加入參戰者",
                description="本頻道目前沒有人開角色卡，按下面的按鈕直接跳表單手動輸入參戰者（NPC 或玩家都可以）。",
                color=0x00aaff,
            ),
            view=view, ephemeral=True,
        )

class ChaseRandomLengthModal(discord.ui.Modal, title="🎲 隨機產生賽道"):
    """輸入賽道長度，照官方 1D100 表隨機產生整條賽道的障礙／危害。如果本頻道已經有進行中的追逐，
    只會覆蓋賽道長度／障礙／危害，既有參戰者會保留（位置超出新賽道長度會自動夾回範圍內）。
    送出後接著會進到『加入參戰者』那一步（可以直接跳過，之後再用面板的「✏️ 編輯參戰者」補）。"""
    length = discord.ui.TextInput(label="賽道長度（區位數量）", placeholder="8", required=True, max_length=10)

    def __init__(self, guild_id, channel_id):
        super().__init__()
        self.guild_id = guild_id
        self.channel_id = channel_id

    async def on_submit(self, interaction: discord.Interaction):
        text = str(self.length.value).strip()
        if not text.isdigit() or int(text) < 2:
            await interaction.response.send_message("❌ 賽道長度要填數字，而且至少要 2。", ephemeral=True)
            return
        length_val = int(text)
        obstacles, hazards = _generate_random_chase_encounters(length_val)
        key = (self.guild_id, self.channel_id)
        old = chase_sessions.get(key)
        participants = {}
        if old:
            participants = old['participants']
            for p in participants.values():
                p['position'] = max(1, min(length_val, p['position']))
        chase_sessions[key] = {'length': length_val, 'obstacles': obstacles, 'hazards': hazards, 'participants': participants}
        await interaction.channel.send(
            embed=format_chase_embed(chase_sessions[key]).set_footer(
                text="每個區位都是照1D100 表（01-59淨空/60-84一般/85-95困難/96-100極端）隨機決定的。"
            )
        )
        await _chase_refresh_panel(interaction.channel, self.guild_id, self.channel_id)
        await _chase_launch_participant_step(interaction, self.guild_id, self.channel_id)

async def _chase_refresh_panel(channel, guild_id, channel_id):
    """把追逐面板本體的狀態 embed 刷新成最新資料；找不到面板訊息（被刪掉／還沒發過）就算了，
    不影響呼叫端原本的操作結果。"""
    panel_id = chase_panel_tracker.get_panel(guild_id, channel_id)
    if not panel_id:
        return
    try:
        msg = await channel.fetch_message(panel_id)
    except (discord.NotFound, discord.Forbidden, discord.HTTPException):
        return
    session = chase_sessions.get((guild_id, channel_id))
    embed = format_chase_embed(session) if session else _chase_empty_embed()
    try:
        await msg.edit(embed=embed, view=ChasePanelView())
    except discord.HTTPException:
        pass

class ChasePanelView(discord.ui.View):
    """`.chase`／`.ch` 叫出的追逐操作面板：查看／編輯參戰者／隨機產生賽道／移動／障礙危害設置／結束，
    全部改用按鈕，不再支援文字子指令。persistent view（timeout=None＋每顆按鈕都有 custom_id，並在
    on_ready 註冊）：面板永不失效，連 bot 重啟後舊面板的按鈕都還能按（頻道對應到哪場追逐是按下按鈕時
    從 interaction 現場取得的，所以同一個 view 實例可以服務所有頻道）。"""
    def __init__(self):
        super().__init__(timeout=None)

    @staticmethod
    def _key(interaction):
        return (interaction.guild_id, interaction.channel_id)

    async def _gm_gate(self, interaction):
        if not is_gm(interaction.guild_id, interaction.channel_id, interaction.user.id):
            await interaction.response.send_message("這顆是 GM 專用按鈕。請先用 `.drgm addgm` 登記為本頻道 GM。", ephemeral=True)
            return False
        return True

    async def _require_session(self, interaction):
        session = chase_sessions.get(self._key(interaction))
        if not session:
            await interaction.response.send_message(
                embed=discord.Embed(title="❌ 本頻道目前沒有進行中的追逐", description="請先按「🎲 隨機產生賽道」開始一場追逐。", color=0xff0000),
                ephemeral=True,
            )
            return None
        return session

    # ---------- 第一排 ----------
    @discord.ui.button(label="🔄 查看", style=discord.ButtonStyle.secondary, row=0, custom_id="chase_panel:view")
    async def view_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        """人人可按：把面板本體的狀態 embed 刷新成最新資料。"""
        session = chase_sessions.get(self._key(interaction))
        embed = format_chase_embed(session) if session else _chase_empty_embed()
        await interaction.response.edit_message(embed=embed, view=self)

    @discord.ui.button(label="✏️ 編輯參戰者", style=discord.ButtonStyle.primary, row=0, custom_id="chase_panel:edit")
    async def edit_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not await self._gm_gate(interaction):
            return
        session = await self._require_session(interaction)
        if not session:
            return
        await _chase_launch_participant_step(interaction, interaction.guild_id, interaction.channel_id)

    @discord.ui.button(label="🎲 隨機產生賽道", style=discord.ButtonStyle.primary, row=0, custom_id="chase_panel:random")
    async def random_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not await self._gm_gate(interaction):
            return
        await interaction.response.send_modal(ChaseRandomLengthModal(interaction.guild_id, interaction.channel_id))

    # ---------- 第二排 ----------
    @discord.ui.button(label="🏃 移動", style=discord.ButtonStyle.secondary, row=1, custom_id="chase_panel:move")
    async def move_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not await self._gm_gate(interaction):
            return
        session = await self._require_session(interaction)
        if not session:
            return
        if not session['participants']:
            await interaction.response.send_message(
                embed=discord.Embed(title="❌ 目前沒有參戰者", description="請先按「✏️ 編輯參戰者」加入。", color=0xff0000),
                ephemeral=True,
            )
            return
        view = ChaseMoveView(interaction.user.id, interaction.guild_id, interaction.channel_id, session['participants'])
        await interaction.response.send_message(
            embed=discord.Embed(title="🏃 移動參戰者", description="選擇要移動的參戰者（可多選），選完會跳出輸入視窗填要移動到的位置。", color=0x00aaff),
            view=view, ephemeral=True,
        )
        view.sent_message = await interaction.original_response()

    @discord.ui.button(label="⚠️ 障礙／危害設置", style=discord.ButtonStyle.secondary, row=1, custom_id="chase_panel:hazard")
    async def hazard_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not await self._gm_gate(interaction):
            return
        session = await self._require_session(interaction)
        if not session:
            return
        await interaction.response.send_modal(ChaseHazardModal(interaction.guild_id, interaction.channel_id, session))

    # ---------- 第三排：速度檢定／回合行動 ----------
    @discord.ui.button(label="🚦 速度檢定", style=discord.ButtonStyle.secondary, row=2, custom_id="chase_panel:speed")
    async def speed_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        """開始追逐前用：自己場外骰體質（徒步）或汽車駕駛（開車），把結果打進表單，程式負責算 MOV±1，
        並判定每個追逐者是被目標甩開、還是正式進入追逐。GM 可以填任何人；玩家只能填自己開的角色卡或建立的角色。"""
        session = await self._require_session(interaction)
        if not session:
            return
        if not session['participants']:
            await interaction.response.send_message(
                embed=discord.Embed(title="❌ 目前沒有參戰者", description="請先請 GM 按「✏️ 編輯參戰者」加入。", color=0xff0000),
                ephemeral=True,
            )
            return
        if is_gm(interaction.guild_id, interaction.channel_id, interaction.user.id):
            await interaction.response.send_modal(ChaseSpeedCheckModal(interaction.guild_id, interaction.channel_id, session))
            return
        owned = _chase_owned_names(interaction.guild_id, interaction.user.id, session['participants'])
        if not owned:
            await interaction.response.send_message(
                embed=discord.Embed(title="❌ 這場追逐裡沒有你自己的角色", description="只能操作你開啟的角色卡，或你自己建立的角色（名字要跟追逐參戰者一致）。", color=0xff0000),
                ephemeral=True,
            )
            return
        await interaction.response.send_modal(ChaseSpeedCheckModal(interaction.guild_id, interaction.channel_id, session, allowed_names=owned))

    @discord.ui.button(label="🔄 開始新回合", style=discord.ButtonStyle.primary, row=2, custom_id="chase_panel:round")
    async def round_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        """把每個人『本回合剩餘行動點』重置成規則書算出來的行動次數，開始（或進到下一個）回合。
        誰先動請看 `.init` 面板的敏捷排序（先攻機制沿用 `.init`，這裡只管行動點數）。"""
        if not await self._gm_gate(interaction):
            return
        session = await self._require_session(interaction)
        if not session:
            return
        if not session['participants']:
            await interaction.response.send_message(
                embed=discord.Embed(title="❌ 目前沒有參戰者", description="請先按「✏️ 編輯參戰者」加入。", color=0xff0000),
                ephemeral=True,
            )
            return
        round_no, action_counts = _chase_start_round(session)
        lines = [f"{name}：{session['participants'][name]['actions_left']} 點" for name in session['participants']]
        await interaction.response.edit_message(embed=format_chase_embed(session), view=self)
        await interaction.followup.send(embed=discord.Embed(
            title=f"🔄 第 {round_no} 回合開始",
            description="誰先動請看 `.init` 面板的敏捷排序。\n本回合各參戰者可用行動點數：\n" + "\n".join(lines),
            color=0x00aaff,
        ))

    @discord.ui.button(label="⚡ 行動", style=discord.ButtonStyle.primary, row=2, custom_id="chase_panel:action")
    async def action_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        """輪到誰的回合就花他的行動點數：前進／攻擊／其他（開鎖、施法、發動汽車等）。
        GM 可以幫任何人動作；玩家只能選自己開的角色卡或建立的角色。要先按過「🔄 開始新回合」才有點數可花。"""
        session = await self._require_session(interaction)
        if not session:
            return
        is_gm_user = is_gm(interaction.guild_id, interaction.channel_id, interaction.user.id)
        allowed_names = None if is_gm_user else _chase_owned_names(interaction.guild_id, interaction.user.id, session['participants'])
        pool = session['participants'] if allowed_names is None else {n: p for n, p in session['participants'].items() if n in allowed_names}
        available = [n for n, p in pool.items() if p.get('actions_left', 0) > 0]
        if not available:
            if allowed_names is not None and not allowed_names:
                await interaction.response.send_message(
                    embed=discord.Embed(title="❌ 這場追逐裡沒有你自己的角色", description="只能操作你開啟的角色卡，或你自己建立的角色（名字要跟追逐參戰者一致）。", color=0xff0000),
                    ephemeral=True,
                )
                return
            await interaction.response.send_message(
                embed=discord.Embed(title="❌ 目前沒有人還有行動點數", description="請先請 GM 按「🔄 開始新回合」重置本回合的行動點數。", color=0xff0000),
                ephemeral=True,
            )
            return
        await interaction.response.send_message(
            embed=discord.Embed(title="⚡ 選擇要動作的參戰者", color=0x00aaff),
            view=ChaseActionActorView(interaction.user.id, interaction.guild_id, interaction.channel_id, session['participants'], allowed_names=allowed_names),
            ephemeral=True,
        )

    @discord.ui.button(label="🏁 結束追逐", style=discord.ButtonStyle.danger, row=2, custom_id="chase_panel:end")
    async def end_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not await self._gm_gate(interaction):
            return
        session = chase_sessions.pop(self._key(interaction), None)
        if not session:
            await interaction.response.send_message("本頻道目前沒有進行中的追逐。", ephemeral=True)
            return
        await interaction.response.edit_message(embed=_chase_empty_embed(), view=self)
        await interaction.followup.send(embed=discord.Embed(title="✅ 追逐已結束", color=0x00aaff))


# ---------- . 指令各自的 handler（由 handle_dot_command 依序分派） ----------
async def _dot_help(message, cmd, cmd_lower):
    """.help 說明選單；`.help reload` 重新讀取 help.md（改完文案不用重開機器人）。
    有處理回傳 True，沒輪到自己回傳 False 讓分派器往下找。"""
    if re.match(r'^help(?![a-z])', cmd_lower):
        if cmd_lower[4:].strip() in ('reload', 'r'):
            count, problem = reload_help_sections()
            if not count:
                embed = discord.Embed(title="❌ 說明檔載入失敗", description=problem, color=0xff0000)
            elif problem:
                embed = discord.Embed(title=f"⚠️ 已載入 {count} 個說明分類，但有問題", description=problem, color=0xffaa00)
            else:
                labels = "、".join(HELP_SECTIONS)
                embed = discord.Embed(title=f"✅ 已重新載入 {count} 個說明分類", description=labels, color=0x00aaff)
            await message.channel.send(embed=embed)
            return True
        await send_help_embed(message)
        return True
    return False

async def _dot_init(message, cmd, cmd_lower):
    """.init 先攻面板：顯示目前先攻名單＋操作按鈕。
    第一排（人人可按）：敏捷作為先攻（優先抓角色卡，沒有就跳表單手動填）／擲骰檢定作為先攻／持械施法+50；
    第二排（GM 專用）：登記 NPC／移除／調整順序／清空。
    舊的文字子指令（add/roll/gun/del/rank/clear/list）已全部改為面板按鈕。"""
    m = re.match(r'^init(?:\s+(.*))?$', cmd, re.I | re.S)
    if not m:
        return False
    guild_id, channel_id = message.guild.id, message.channel.id
    rest = (m.group(1) or '').strip()
    content = None
    if rest:
        content = "ℹ️ `.init` 的文字子指令已改成下面的按鈕面板，直接點按鈕操作即可。"
    session = init_sessions.get((guild_id, channel_id)) or {'entries': {}}
    # 發新面板前，先讓本頻道上一份面板失效（拿掉按鈕、標註已被取代），避免同時多份可按
    old_panel_id = init_panel_tracker.get_panel(guild_id, channel_id)
    if old_panel_id:
        try:
            old_msg = await message.channel.fetch_message(old_panel_id)
            await old_msg.edit(content="ℹ️ 此面板已由新的 `.init` 面板取代。", view=None)
        except (discord.NotFound, discord.Forbidden, discord.HTTPException):
            pass  # 舊面板被刪掉／沒權限就算了，不影響發新面板
    # persistent view：面板永不失效（timeout=None），guild/channel 是按按鈕時從 interaction 取得
    sent = await message.channel.send(content=content, embed=format_init_embed(session), view=InitPanelView())
    init_panel_tracker.set_panel(guild_id, channel_id, sent.id)
    return True

async def _dot_pass(message, cmd, cmd_lower):
    """.pass 結束回合並提醒下一位（限目前行動者本人或 GM）。回合指標記在先攻 session 裡：
    - 名單存在但戰鬥還沒開始（沒有指標）→ 第一次 `.pass` 宣告「第 1 輪開始」並點名第 1 位；
    - 之後每次 `.pass` 把指標往下移一位並 @提醒（自助登記的條目有記 user_id 才會真的 ping，NPC 只顯示名字）；
    - 走完一圈自動進入下一輪；目前行動者在 `.init` 名單上會有 ▶ 標記。
    名單中途變動（目前行動者被移除）時，指標會回到該輪第 1 位重新點名。"""
    if not re.match(r'^pass(?![a-z])', cmd_lower):
        return False
    guild_id, channel_id = message.guild.id, message.channel.id
    key = (guild_id, channel_id)
    session = init_sessions.get(key)
    if not session or not session['entries']:
        await message.channel.send(embed=discord.Embed(
            title="❌ 沒有先攻名單",
            description="本頻道還沒有任何先攻資料，先用 `.init` 面板登記參戰者。",
            color=0xff0000,
        ))
        return True

    # 權限：GM 永遠可以推進；非 GM 只有在「目前行動者是自己」（條目的 user_id 是自己）時才行。
    # 開戰第一下、NPC 的回合、目前行動者被移除的修復，這幾種情況都沒有「本人」可言 → 只有 GM 能推。
    user_id = message.author.id
    allowed = is_gm(guild_id, channel_id, user_id)
    if not allowed:
        cur_entry = session['entries'].get(session.get('turn_name') or '')
        allowed = cur_entry is not None and cur_entry.get('user_id') == user_id
    if not allowed:
        await message.channel.send(embed=discord.Embed(
            title="❌ 現在不是你的回合",
            description="只有**目前行動者本人**或**本頻道登記的 GM** 才能用 `.pass` 推進回合。\n"
                        "（開戰的第一下 `.pass`、NPC 的回合，都由 GM 來推。）",
            color=0xff0000,
        ))
        return True

    ordered = sorted(session['entries'].items(), key=_init_sort_key_factory(session['entries']))
    names = [n for n, _ in ordered]
    turn_name = session.get('turn_name')
    round_no = session.get('round') or 0

    notes = []
    if turn_name not in names:
        # 還沒開始（或目前行動者已被移出名單）→ 從本輪第 1 位開始
        next_idx = 0
        if round_no == 0:
            round_no = 1
            notes.append("⚔️ 戰鬥開始，**第 1 輪**！")
        elif turn_name is not None:
            notes.append(f"⚠️ 「{turn_name}」已不在名單上，指標回到本輪第 1 位。")
    else:
        cur_idx = names.index(turn_name)
        notes.append(f"✅ 「{turn_name}」結束行動。")
        next_idx = cur_idx + 1
        if next_idx >= len(names):
            next_idx = 0
            round_no += 1
            notes.append(f"🔄 本輪結束，進入**第 {round_no} 輪**！")

    next_name, next_entry = ordered[next_idx]
    session['turn_name'] = next_name
    session['round'] = round_no
    init_sessions_save()

    uid = next_entry.get('user_id')
    content = f"<@{uid}>" if uid else None
    embed = discord.Embed(
        title=f"⏭️ 輪到：{next_name}",
        description="\n".join(notes + [
            f"順位：第 {next_idx + 1}／{len(names)} 位（第 {round_no} 輪）",
            f"條目：{_init_entry_text(next_entry)}",
        ]),
        color=0x00aaff,
    )
    await message.channel.send(content=content, embed=embed)
    return True

class ChaseMoveModal(discord.ui.Modal, title="🏃 移動參戰者"):
    """面板「🏃 移動」勾完參戰者後跳出的表單：填一個目的地，同時套用到所有被選中的參戰者。
    支援絕對位置（純數字，例如 `5`）與相對位置（帶正負號，例如 `+1`／`-2`），
    每個人各自用「自己目前的位置」去加減，算完統一夾在 1～賽道長度之間，不會衝出賽道。"""
    dest_input = discord.ui.TextInput(
        label="移動到（絕對位置如 5／相對位置如 +1、-2）",
        placeholder="輸入 5 → 直接移到位置5；輸入 +1／-2 → 往前1格／退後2格",
        required=True, max_length=10,
    )

    def __init__(self, guild_id, channel_id, names, select_view=None):
        super().__init__()
        self.guild_id = guild_id
        self.channel_id = channel_id
        self.names = names  # 被勾選、要移動的參戰者名字
        self.select_view = select_view  # 用來在送出後把第一段下拉選單設成失效

    async def on_submit(self, interaction: discord.Interaction):
        key = (self.guild_id, self.channel_id)
        session = chase_sessions.get(key)
        if not session:
            await interaction.response.send_message(
                embed=discord.Embed(title="❌ 追逐已經結束或不存在", description="請重新按面板的「🏃 移動」。", color=0xff0000),
                ephemeral=True,
            )
            return

        raw = str(self.dest_input.value).strip()
        m = re.match(r'^([+-]?\d+)$', raw)
        if not m:
            await interaction.response.send_message(
                embed=discord.Embed(title="❌ 格式錯誤", description="請輸入絕對位置（例如 `5`）或相對位置（例如 `+1`／`-2`）。", color=0xff0000),
                ephemeral=True,
            )
            return

        value = int(m.group(1))
        is_relative = raw[0] in '+-'
        length = session['length']
        participants = session['participants']

        moved_lines, skipped = [], []
        for name in self.names:
            p = participants.get(name)
            if not p:
                skipped.append(name)
                continue
            old_pos = p['position']
            new_pos = old_pos + value if is_relative else value
            new_pos = max(1, min(length, new_pos))  # 邊界判定：不能衝出賽道或變成負數
            p['position'] = new_pos
            moved_lines.append(f"{name}：{old_pos} → {new_pos}")

        # 收尾：把第一段下拉選單設成失效，避免同一份選單被重複使用
        if self.select_view:
            self.select_view.select.disabled = True
            if self.select_view.sent_message:
                try:
                    await self.select_view.sent_message.edit(view=self.select_view)
                except discord.HTTPException:
                    pass

        result_desc = "\n".join(moved_lines) if moved_lines else "沒有成功移動任何人。"
        if skipped:
            result_desc += f"\n（找不到：{'、'.join(skipped)}，可能追逐設置已被更新）"
        await interaction.response.send_message(
            embed=discord.Embed(title="✅ 移動成功", description=result_desc, color=0x00aaff),
            ephemeral=True,
        )
        # 更新後的追逐狀態表公開發到頻道，讓大家都看得到最新位置，順便刷新面板本體
        await interaction.channel.send(embed=format_chase_embed(session))
        await _chase_refresh_panel(interaction.channel, self.guild_id, self.channel_id)

class ChaseMoveSelect(discord.ui.Select):
    """面板「🏃 移動」的第一段：勾選要移動的參戰者（可多選），選項說明顯示各自目前的位置。
    跟 InitDelSelect 一樣用索引當 value，避免名字太長被 Discord 截斷後對不回去。"""
    def __init__(self, author_id, guild_id, channel_id, participants):
        self.author_id = author_id
        self.guild_id = guild_id
        self.channel_id = channel_id
        self.names = list(participants.keys())[:25]  # Discord 選單上限 25 個選項
        options = [
            discord.SelectOption(label=name[:100], value=str(i), description=f"目前位置：{participants[name]['position']}")
            for i, name in enumerate(self.names)
        ]
        super().__init__(placeholder="選擇要移動的參戰者（可多選）…", options=options, min_values=1, max_values=len(options))

    async def callback(self, interaction: discord.Interaction):
        if interaction.user.id != self.author_id:
            await interaction.response.send_message("這不是你叫出來的選單喔，請自己按面板的「🏃 移動」。", ephemeral=True)
            return
        selected_names = [self.names[int(idx)] for idx in self.values]
        await interaction.response.send_modal(
            ChaseMoveModal(self.guild_id, self.channel_id, selected_names, select_view=self.view)
        )

class ChaseMoveView(discord.ui.View):
    def __init__(self, author_id, guild_id, channel_id, participants):
        super().__init__(timeout=180)
        self.select = ChaseMoveSelect(author_id, guild_id, channel_id, participants)
        self.add_item(self.select)
        self.sent_message = None  # 送出後由呼叫端補上，逾時或選完要編輯這則訊息

    async def on_timeout(self):
        self.select.disabled = True
        if self.sent_message:
            try:
                await self.sent_message.edit(view=self)
            except discord.HTTPException:
                pass

class ChaseAttackSkillModal(discord.ui.Modal, title="⚔️ 攻擊技能"):
    """『攻擊』動作最後一步：輸入攻擊方要用的技能名稱或數值
    （純數字＝直接當技能值；不是數字就跨玩家搜尋角色卡找同名技能，NPC 沒有角色卡的話請直接打數值）。"""
    skill_input = discord.ui.TextInput(label="攻擊方技能名稱或數值", placeholder="例如：格鬥，或直接打 55", max_length=20)

    def __init__(self, guild_id, channel_id, actor_name, target_name):
        super().__init__()
        self.guild_id = guild_id
        self.channel_id = channel_id
        self.actor_name = actor_name
        self.target_name = target_name

    async def on_submit(self, interaction: discord.Interaction):
        key = (self.guild_id, self.channel_id)
        session = chase_sessions.get(key)
        if not session:
            await interaction.response.send_message(embed=discord.Embed(title="❌ 追逐已經結束或不存在", color=0xff0000), ephemeral=True)
            return
        participants = session['participants']
        actor, target = participants.get(self.actor_name), participants.get(self.target_name)
        if not actor or not target:
            await interaction.response.send_message(embed=discord.Embed(title="❌ 參戰者資料已更新，請重新操作", color=0xff0000), ephemeral=True)
            return
        if actor.get('actions_left', 0) <= 0:
            await interaction.response.send_message(embed=discord.Embed(title="❌ 這個人本回合的行動點數已經用完了", color=0xff0000), ephemeral=True)
            return
        defender = _chase_resolve_member(interaction.guild, self.guild_id, self.target_name)
        if not defender:
            await interaction.response.send_message(
                embed=discord.Embed(
                    title="❌ 無法鎖定防禦方",
                    description=f"「{self.target_name}」沒有對到唯一一位還在伺服器裡、有開角色卡的成員，無法用面板攻擊（可能是 NPC 或同名多筆）。\n請改用 `.melee`／`.cc` 手動指定 @對方。",
                    color=0xff0000,
                ),
                ephemeral=True,
            )
            return
        atk_skill_name, atk_value = _chase_resolve_attacker_skill(self.guild_id, self.actor_name, str(self.skill_input.value))
        if atk_value is None:
            await interaction.response.send_message(
                embed=discord.Embed(title="❌ 看不懂這個技能", description=f"請打數字，或「{self.actor_name}」角色卡上剛好符合、唯一的技能名稱。", color=0xff0000),
                ephemeral=True,
            )
            return

        distance = abs(actor['position'] - target['position'])
        bonus_dice = -min(distance, 3) if distance > 0 else 0
        range_note = f"（跨 {distance} 個節點射擊，懲罰骰 {abs(bonus_dice)}）" if distance > 0 else ""

        actor['actions_left'] -= 1
        await interaction.response.send_message(
            embed=discord.Embed(title="✅ 已發動攻擊", description=f"「{self.actor_name}」對「{self.target_name}」發動攻擊，消耗 1 點行動（剩餘 {actor['actions_left']}）。", color=0x00aaff),
            ephemeral=True,
        )
        await _chase_start_attack(interaction, self.actor_name, atk_skill_name, atk_value, defender, bonus_dice=bonus_dice, range_note=range_note)
        await _chase_refresh_panel(interaction.channel, self.guild_id, self.channel_id)

class ChaseAttackTargetSelect(discord.ui.Select):
    """『攻擊』動作第一步：選要打誰（面板上其他參戰者，不含自己）。同節點＝近戰，不同節點會依距離套用懲罰骰。
    跟 ChaseMoveSelect 一樣用索引當 value，避免名字太長被截斷後對不回去。"""
    def __init__(self, author_id, guild_id, channel_id, actor_name, participants):
        self.author_id = author_id
        self.guild_id = guild_id
        self.channel_id = channel_id
        self.actor_name = actor_name
        self.names = [n for n in participants if n != actor_name][:25]
        options = [
            discord.SelectOption(
                label=n[:100], value=str(i),
                description=f"位置 {participants[n]['position']}｜{_CHASE_ROLE_LABEL[participants[n]['role']]}",
            )
            for i, n in enumerate(self.names)
        ]
        super().__init__(placeholder="選擇攻擊目標…", options=options, min_values=1, max_values=1)

    async def callback(self, interaction: discord.Interaction):
        if interaction.user.id != self.author_id:
            await interaction.response.send_message("這不是你叫出來的選單喔。", ephemeral=True)
            return
        target_name = self.names[int(self.values[0])]
        await interaction.response.send_modal(
            ChaseAttackSkillModal(self.guild_id, self.channel_id, self.actor_name, target_name)
        )

class ChaseAttackTargetView(discord.ui.View):
    def __init__(self, author_id, guild_id, channel_id, actor_name, participants):
        super().__init__(timeout=120)
        self.add_item(ChaseAttackTargetSelect(author_id, guild_id, channel_id, actor_name, participants))

class ChaseActionTypeView(discord.ui.View):
    """選好『這回合誰要動作』之後的第二步：前進／攻擊／其他，各花費 1 點行動點數。"""
    def __init__(self, author_id, guild_id, channel_id, actor_name):
        super().__init__(timeout=120)
        self.author_id = author_id
        self.guild_id = guild_id
        self.channel_id = channel_id
        self.actor_name = actor_name

    async def _check(self, interaction):
        """共用檢查：權限／追逐是否還在／這個人是否還有行動點數。通過回傳 (session, actor)，
        沒通過會自己回覆錯誤訊息並回傳 (None, None)。"""
        if interaction.user.id != self.author_id:
            await interaction.response.send_message("這不是你叫出來的選單喔。", ephemeral=True)
            return None, None
        session = chase_sessions.get((self.guild_id, self.channel_id))
        actor = session['participants'].get(self.actor_name) if session else None
        if not session or not actor:
            await interaction.response.send_message(embed=discord.Embed(title="❌ 追逐或這名參戰者已經不存在了", color=0xff0000), ephemeral=True)
            return None, None
        if actor.get('actions_left', 0) <= 0:
            await interaction.response.send_message(embed=discord.Embed(title="❌ 這個人本回合的行動點數已經用完了", color=0xff0000), ephemeral=True)
            return None, None
        return session, actor

    @discord.ui.button(label="➡️ 前進", style=discord.ButtonStyle.primary)
    async def move_forward(self, interaction: discord.Interaction, button: discord.ui.Button):
        session, actor = await self._check(interaction)
        if not actor:
            return
        old_pos = actor['position']
        actor['position'] = min(session['length'], old_pos + 1)
        actor['actions_left'] -= 1
        for child in self.children:
            child.disabled = True
        await interaction.response.edit_message(
            embed=discord.Embed(title="✅ 前進", description=f"「{self.actor_name}」{old_pos} → {actor['position']}，剩餘 {actor['actions_left']} 點行動。", color=0x00aaff),
            view=self,
        )
        await interaction.channel.send(embed=format_chase_embed(session))
        await _chase_refresh_panel(interaction.channel, self.guild_id, self.channel_id)

    @discord.ui.button(label="⚔️ 攻擊", style=discord.ButtonStyle.danger)
    async def attack(self, interaction: discord.Interaction, button: discord.ui.Button):
        session, actor = await self._check(interaction)
        if not actor:
            return
        if len(session['participants']) <= 1:
            await interaction.response.send_message(embed=discord.Embed(title="❌ 沒有其他參戰者可以攻擊", color=0xff0000), ephemeral=True)
            return
        view = ChaseAttackTargetView(self.author_id, self.guild_id, self.channel_id, self.actor_name, session['participants'])
        await interaction.response.send_message(
            embed=discord.Embed(title="⚔️ 選擇攻擊目標", description="同節點＝近戰；不同節點會依距離套用懲罰骰（跨節點射擊）。", color=0x00aaff),
            view=view, ephemeral=True,
        )

    @discord.ui.button(label="🔧 其他", style=discord.ButtonStyle.secondary)
    async def other_action(self, interaction: discord.Interaction, button: discord.ui.Button):
        session, actor = await self._check(interaction)
        if not actor:
            return
        actor['actions_left'] -= 1
        for child in self.children:
            child.disabled = True
        await interaction.response.edit_message(
            embed=discord.Embed(title="✅ 其他行動", description=f"「{self.actor_name}」花費 1 點行動點數做其他動作（開鎖／施法／發動汽車等），剩餘 {actor['actions_left']} 點。", color=0x00aaff),
            view=self,
        )
        await _chase_refresh_panel(interaction.channel, self.guild_id, self.channel_id)

class ChaseActionActorSelect(discord.ui.Select):
    """『⚡ 行動』第一步：選這次要花行動點數的人，只列出本回合還有剩餘點數的人。
    allowed_names 不是 None 時（玩家自己按的，不是 GM）再進一步限制只能選名單內（自己）的角色。"""
    def __init__(self, author_id, guild_id, channel_id, participants, allowed_names=None):
        self.author_id = author_id
        self.guild_id = guild_id
        self.channel_id = channel_id
        pool = participants if allowed_names is None else {n: p for n, p in participants.items() if n in allowed_names}
        self.names = [n for n, p in pool.items() if p.get('actions_left', 0) > 0][:25]
        options = [
            discord.SelectOption(
                label=n[:100], value=str(i),
                description=f"位置 {participants[n]['position']}｜剩餘 {participants[n]['actions_left']} 點行動",
            )
            for i, n in enumerate(self.names)
        ]
        super().__init__(placeholder="選擇這次要動作的參戰者…", options=options, min_values=1, max_values=1)

    async def callback(self, interaction: discord.Interaction):
        if interaction.user.id != self.author_id:
            await interaction.response.send_message("這不是你叫出來的選單喔。", ephemeral=True)
            return
        actor_name = self.names[int(self.values[0])]
        await interaction.response.edit_message(
            embed=discord.Embed(title=f"⚡「{actor_name}」的行動", description="選擇要做的事，每項花費 1 點行動點數。", color=0x00aaff),
            view=ChaseActionTypeView(self.author_id, self.guild_id, self.channel_id, actor_name),
        )

class ChaseActionActorView(discord.ui.View):
    def __init__(self, author_id, guild_id, channel_id, participants, allowed_names=None):
        super().__init__(timeout=120)
        self.add_item(ChaseActionActorSelect(author_id, guild_id, channel_id, participants, allowed_names=allowed_names))

async def _dot_chase(message, cmd, cmd_lower):
    """.chase 追逐面板：顯示目前狀態＋操作面板（查看／編輯參戰者／隨機產生賽道／移動／障礙危害設置／結束）。
    全部改成按鈕操作，不再支援文字子指令（.chase edit／move／random／damage／end 都已移除）。
    面板是 persistent view，永不失效；重打 `.chase` 會讓上一份面板失效，避免同時多份可按。"""
    m = re.match(r'^(?:chase|ch)(?:\s+(.*))?$', cmd, re.I | re.S)
    if not m:
        return False
    guild_id, channel_id = message.guild.id, message.channel.id
    rest = (m.group(1) or '').strip()
    content_text = None
    if rest:
        content_text = "ℹ️ `.chase` 的文字子指令已經全部改成下面的按鈕面板，直接點按鈕操作即可。"
    session = chase_sessions.get((guild_id, channel_id))
    embed = format_chase_embed(session) if session else _chase_empty_embed()
    # 發新面板前，先讓本頻道上一份面板失效（拿掉按鈕、標註已被取代），避免同時多份可按
    old_panel_id = chase_panel_tracker.get_panel(guild_id, channel_id)
    if old_panel_id:
        try:
            old_msg = await message.channel.fetch_message(old_panel_id)
            await old_msg.edit(content="ℹ️ 此面板已由新的 `.chase` 面板取代。", view=None)
        except (discord.NotFound, discord.Forbidden, discord.HTTPException):
            pass  # 舊面板被刪掉／沒權限就算了，不影響發新面板
    # persistent view：面板永不失效（timeout=None），guild/channel 是按按鈕時從 interaction 取得
    sent = await message.channel.send(content=content_text, embed=embed, view=ChasePanelView())
    chase_panel_tracker.set_panel(guild_id, channel_id, sent.id)
    return True

class EphemeralRevealView(discord.ui.View):
    """在頻道發一則公開存根訊息（按鈕本體不含任何內容），本人按下按鈕後才用 ephemeral 訊息
    （只有本人看得到，Discord 會顯示「只有您才能看到這個」）顯示完整內容。
    用於 .start／.end 這類單人行動，讓其他人在頻道裡只看得到一顆按鈕、看不到實際內容。"""
    def __init__(self, author_id, embed, button_label="🔍 查看內容（只有你看得到）", timeout=180):
        super().__init__(timeout=timeout)
        self.author_id = author_id
        self.embed = embed
        self.message = None
        self.reveal_button.label = button_label

    @discord.ui.button(label="🔍 查看內容（只有你看得到）", style=discord.ButtonStyle.primary)
    async def reveal_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.author_id:
            await interaction.response.send_message("這不是你叫出來的內容，請自己輸入對應指令。", ephemeral=True)
            return
        await interaction.response.send_message(embed=self.embed, ephemeral=True)

    async def on_timeout(self):
        for child in self.children:
            child.disabled = True
        if self.message:
            try:
                await self.message.edit(view=self)
            except discord.HTTPException:
                pass

async def send_ephemeral_reveal(message, embed, stub_text=None, button_label="🔍 查看內容（只有你看得到）"):
    """發一則公開存根訊息＋按鈕；本人按下後用 ephemeral 顯示 embed 內容，其他人只看得到按鈕，看不到內容。"""
    if stub_text is None:
        stub_text = f"{message.author.mention} 有一則只有本人看得到的通知，請按下方按鈕查看。"
    view = EphemeralRevealView(message.author.id, embed, button_label=button_label)
    sent = await message.channel.send(content=stub_text, view=view)
    view.message = sent
    return view

class EphemeralMenuRevealView(discord.ui.View):
    """在頻道發一則公開存根訊息（按鈕本體不含任何選單），本人按下按鈕後才用 ephemeral 訊息
    （只有本人看得到）顯示實際的互動選單（embed＋discord.ui.View，例如角色卡選單）。
    用於 .pc 等會跳出選單的指令，讓其他人在頻道裡只看得到一顆按鈕、看不到選單內容或選項，
    選單本身的互動（下拉選單、按鈕）在 ephemeral 訊息裡照常運作。"""
    def __init__(self, author_id, embed, menu_view, button_label="🔍 開啟選單（只有你看得到）", timeout=180):
        super().__init__(timeout=timeout)
        self.author_id = author_id
        self.embed = embed
        self.menu_view = menu_view
        self.message = None
        self.reveal_button.label = button_label

    @discord.ui.button(label="🔍 開啟選單（只有你看得到）", style=discord.ButtonStyle.primary)
    async def reveal_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.author_id:
            await interaction.response.send_message("這不是你叫出來的選單，請自己輸入對應指令。", ephemeral=True)
            return
        await interaction.response.send_message(embed=self.embed, view=self.menu_view, ephemeral=True)

    async def on_timeout(self):
        for child in self.children:
            child.disabled = True
        if self.message:
            try:
                await self.message.edit(view=self)
            except discord.HTTPException:
                pass

async def send_ephemeral_menu(message, embed, menu_view, stub_text=None, button_label="🔍 開啟選單（只有你看得到）"):
    """發一則公開存根訊息＋按鈕；本人按下後用 ephemeral 顯示實際選單（embed＋view），
    其他人在頻道裡只看得到一顆按鈕，看不到選單內容或選項。"""
    if stub_text is None:
        stub_text = f"{message.author.mention} 有一份只有本人看得到的選單，請按下方按鈕開啟。"
    reveal_view = EphemeralMenuRevealView(message.author.id, embed, menu_view, button_label=button_label)
    sent = await message.channel.send(content=stub_text, view=reveal_view)
    reveal_view.message = sent
    return reveal_view

# ---------- .drgm rec 討論串多選面板 ----------
def _rec_active_threads(channel):
    """回傳母頻道底下目前『活躍（未封存）』的討論串清單。channel 不是文字頻道時回空清單。
    只用快取裡的 channel.threads（同步、免 await）：活躍討論串一定在快取，封存的本來就不列進『加入選單』。"""
    threads = getattr(channel, 'threads', None)
    if not threads:
        return []
    return list(threads)


class RecAddSelect(discord.ui.Select):
    """把『本頻道＋活躍且尚未加入的討論串』列成多選，勾選送出後一次全部加入白名單。
    value 用頻道 id 字串；頂部固定放一個『本頻道』選項（value = 母頻道 id）。"""
    def __init__(self, gm_user_id, parent_channel, candidates):
        self.gm_user_id = gm_user_id
        guild_id = parent_channel.guild.id
        options = []
        # 頂部固定放「本頻道（母頻道）」，除非它已在這位 GM 的白名單裡
        if not growth_channel_whitelist.is_allowed_by(guild_id, gm_user_id, parent_channel.id):
            options.append(discord.SelectOption(
                label=f"本頻道（{parent_channel.name}）"[:100],
                value=str(parent_channel.id),
                description="母頻道本身",
            ))
        for th in candidates:
            options.append(discord.SelectOption(label=th.name[:100], value=str(th.id), description="討論串"))
        # 沒有任何可加項時放一個佔位（選了也不做事）
        if not options:
            options = [discord.SelectOption(label="（沒有可加入的頻道／討論串）", value="__none__")]
        super().__init__(placeholder="勾選要加入白名單的頻道／討論串…", options=options[:25],
                         min_values=1, max_values=len(options), custom_id="rec_add_select")

    async def callback(self, interaction: discord.Interaction):
        if interaction.user.id != self.gm_user_id:
            await interaction.response.send_message("這不是你叫出來的面板，請自己打 `.drgm rec`。", ephemeral=True)
            return
        guild_id = interaction.guild.id
        added, dup = [], []
        for val in self.values:
            if val == "__none__":
                continue
            cid = int(val)
            if growth_channel_whitelist.add(guild_id, self.gm_user_id, cid):
                added.append(cid)
            else:
                dup.append(cid)
        lines = []
        if added:
            lines.append("✅ 已加入：" + "、".join(_rec_label(cid) for cid in added))
        if dup:
            lines.append("⚠️ 原本就在清單：" + "、".join(_rec_label(cid) for cid in dup))
        if not lines:
            lines.append("沒有選擇任何項目。")
        await interaction.response.edit_message(
            embed=discord.Embed(title="📋 成長紀錄白名單｜加入", description="\n".join(lines), color=0x00aaff),
            view=None,
        )


class RecDelSelect(discord.ui.Select):
    """列出這位 GM 白名單裡的『全部』項目（含已封存／找不到的），勾選送出後一次移除。"""
    def __init__(self, gm_user_id, guild_id, channel_ids):
        self.gm_user_id = gm_user_id
        options = []
        for cid in channel_ids[:25]:
            ch = bot.get_channel(cid)
            if ch is None:
                label, desc = f"已刪除或封存（{cid}）", "找不到頻道，仍可移除"
            else:
                kind = "討論串" if isinstance(ch, discord.Thread) else "頻道"
                archived = getattr(ch, 'archived', False)
                label = ch.name
                desc = f"{kind}{'｜已封存' if archived else ''}"
            options.append(discord.SelectOption(label=label[:100], value=str(cid), description=desc[:100]))
        if not options:
            options = [discord.SelectOption(label="（白名單是空的）", value="__none__")]
        super().__init__(placeholder="勾選要移出白名單的項目…", options=options,
                         min_values=1, max_values=len(options), custom_id="rec_del_select")

    async def callback(self, interaction: discord.Interaction):
        if interaction.user.id != self.gm_user_id:
            await interaction.response.send_message("這不是你叫出來的面板，請自己打 `.drgm rec`。", ephemeral=True)
            return
        guild_id = interaction.guild.id
        removed = []
        for val in self.values:
            if val == "__none__":
                continue
            cid = int(val)
            if growth_channel_whitelist.remove(guild_id, self.gm_user_id, cid):
                removed.append(cid)
        desc = ("✅ 已移出：" + "、".join(_rec_label(cid) for cid in removed) +
                "\n已記錄的紀錄會保留，只是不再累加。") if removed else "沒有移除任何項目。"
        await interaction.response.edit_message(
            embed=discord.Embed(title="📋 成長紀錄白名單｜移除", description=desc, color=0x00aaff),
            view=None,
        )


def _rec_label(cid):
    """把頻道 id 轉成好讀的標籤：抓得到就用 mention，抓不到就顯示 id。"""
    ch = bot.get_channel(cid)
    return ch.mention if ch is not None else f"`{cid}`"


def _rec_whitelist_lines(guild_id, gm_user_id):
    """把某 GM 目前的白名單列成文字（給面板 embed 直接顯示）。空的話回一句說明。"""
    chans = growth_channel_whitelist.get_channels(guild_id, gm_user_id)
    if not chans:
        return "（你目前的白名單是空的）"
    lines = []
    for cid in chans:
        ch = bot.get_channel(cid)
        if ch is None:
            lines.append(f"• `{cid}`（已封存或已刪除，仍在記錄）")
        else:
            kind = "討論串" if isinstance(ch, discord.Thread) else "頻道"
            archived = "｜已封存" if getattr(ch, 'archived', False) else ""
            lines.append(f"• {ch.mention}（{kind}{archived}）")
    return "目前白名單：\n" + "\n".join(lines)


async def _rec_send_whitelist(interaction, gm_user_id):
    """【查看清單】按鈕共用：用 ephemeral（只有按的人看得到）顯示這位 GM 目前的完整白名單。"""
    desc = _rec_whitelist_lines(interaction.guild.id, gm_user_id)
    if not growth_channel_whitelist.get_channels(interaction.guild.id, gm_user_id):
        desc += ("\n\nℹ️ 你目前沒有設定任何白名單頻道。你登記為 GM 的頻道會走「自動模式」："
                 "玩家自己啟用角色卡或 `.start` 就會記錄他本人的檢定。\n"
                 "一旦你在下面加入第一個頻道，你登記為 GM 的頻道就改走白名單——只記你加入的頻道，其餘不記。")
    await interaction.response.send_message(
        embed=discord.Embed(title="📋 成長紀錄白名單", description=desc, color=0x00aaff),
        ephemeral=True,
    )


def _rec_panel_embed(guild_id, gm_user_id, in_thread, here):
    """組面板 embed：標題＋操作說明＋目前白名單清單。母頻道與討論串的說明不同。"""
    if in_thread:
        desc = (
            f"這是討論串 {here.mention}。用下面的按鈕把「這條討論串」加入／移出成長紀錄白名單。\n\n"
        )
    else:
        desc = (
            "用下面的按鈕操作成長紀錄白名單（只有你看得到操作結果）：\n"
            "➕ 加入：把本頻道或它目前的討論串加進白名單（可複選）\n"
            "➖ 移除：把項目移出白名單（含已封存／已刪除的也列得出來）\n"
            "※ 之後才新建的討論串請進該討論串打 `.drgm rec`。\n\n"
        )
    desc += _rec_whitelist_lines(guild_id, gm_user_id)
    if not growth_channel_whitelist.get_channels(guild_id, gm_user_id):
        desc += ("\n\nℹ️ 你目前沒有設定任何白名單頻道。你登記為 GM 的頻道會走「自動模式」："
                 "玩家自己啟用角色卡或 `.start` 就會記錄他本人的檢定。\n"
                 "一旦你在下面加入第一個頻道，你登記為 GM 的頻道就改走白名單——只記你加入的頻道，其餘不記。")
    return discord.Embed(title="📋 成長紀錄白名單", description=desc, color=0x00aaff)


class RecThreadPanelView(discord.ui.View):
    """在討論串裡打 `.drgm rec` 跳出的面板：只針對「這條討論串」加入／移出，不用打任何子指令。
    只有叫出面板的 GM 能操作。"""
    def __init__(self, gm_user_id, thread):
        super().__init__(timeout=180)
        self.gm_user_id = gm_user_id
        self.thread = thread

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if interaction.user.id != self.gm_user_id:
            await interaction.response.send_message("這不是你叫出來的面板，請自己打 `.drgm rec`。", ephemeral=True)
            return False
        return True

    def _refresh_embed(self):
        return _rec_panel_embed(self.thread.guild.id, self.gm_user_id, True, self.thread)

    @discord.ui.button(label="➕ 加入這條討論串", style=discord.ButtonStyle.success)
    async def add_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        guild_id = interaction.guild.id
        ok = growth_channel_whitelist.add(guild_id, self.gm_user_id, self.thread.id)
        note = "✅ 已把這條討論串加入白名單。" if ok else "⚠️ 這條討論串原本就在你的白名單裡。"
        embed = self._refresh_embed()
        embed.description = note + "\n\n" + embed.description
        await interaction.response.edit_message(embed=embed, view=self)

    @discord.ui.button(label="➖ 移出這條討論串", style=discord.ButtonStyle.danger)
    async def del_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        guild_id = interaction.guild.id
        ok = growth_channel_whitelist.remove(guild_id, self.gm_user_id, self.thread.id)
        note = ("✅ 已把這條討論串移出白名單；已記錄的保留，之後不再累加。" if ok
                else "⚠️ 這條討論串原本就不在你的白名單裡。")
        embed = self._refresh_embed()
        embed.description = note + "\n\n" + embed.description
        await interaction.response.edit_message(embed=embed, view=self)

    @discord.ui.button(label="📋 查看清單", style=discord.ButtonStyle.secondary)
    async def show_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        await _rec_send_whitelist(interaction, self.gm_user_id)


class RecPanelView(discord.ui.View):
    """`.drgm rec`（在母頻道）跳出的面板：先給【加入】【移除】兩顆按鈕，
    點哪顆才展開對應的多選選單（避免一次塞兩個下拉式太擠）。只有叫出面板的 GM 能操作。"""
    def __init__(self, gm_user_id, parent_channel):
        super().__init__(timeout=180)
        self.gm_user_id = gm_user_id
        self.parent_channel = parent_channel

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if interaction.user.id != self.gm_user_id:
            await interaction.response.send_message("這不是你叫出來的面板，請自己打 `.drgm rec`。", ephemeral=True)
            return False
        return True

    @discord.ui.button(label="➕ 加入頻道／討論串", style=discord.ButtonStyle.success)
    async def add_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        guild_id = interaction.guild.id
        # 只列『尚未加入』的活躍討論串
        candidates = [th for th in _rec_active_threads(self.parent_channel)
                      if not growth_channel_whitelist.is_allowed_by(guild_id, self.gm_user_id, th.id)]
        view = discord.ui.View(timeout=180)
        view.add_item(RecAddSelect(self.gm_user_id, self.parent_channel, candidates))
        await interaction.response.edit_message(
            embed=discord.Embed(
                title="➕ 加入成長紀錄白名單",
                description="勾選要加入的頻道／討論串（可複選），送出後生效。\n只列出目前活躍、且還沒加入的討論串；之後才新建的討論串請進該串打 `.drgm rec`。",
                color=0x00aaff,
            ),
            view=view,
        )

    @discord.ui.button(label="📋 查看清單", style=discord.ButtonStyle.secondary)
    async def show_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        await _rec_send_whitelist(interaction, self.gm_user_id)

    @discord.ui.button(label="➖ 移除", style=discord.ButtonStyle.danger)
    async def del_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        guild_id = interaction.guild.id
        chans = growth_channel_whitelist.get_channels(guild_id, self.gm_user_id)
        view = discord.ui.View(timeout=180)
        view.add_item(RecDelSelect(self.gm_user_id, guild_id, chans))
        await interaction.response.edit_message(
            embed=discord.Embed(
                title="➖ 移出成長紀錄白名單",
                description="勾選要移出的項目（含已封存／已刪除的也會列出，可直接移除）。",
                color=0x00aaff,
            ),
            view=view,
        )


class StartGrowthSharedView(discord.ui.View):
    """.start 面板：跟 EphemeralRevealView 不同，這顆按鈕不限本人，頻道裡任何人都能按。
    每次有人按下，就針對「按的人」自己開始（或重開）他在本頻道的成長紀錄，並用 ephemeral
    （只有按的人看得到）回覆成長紀錄狀態 + 他目前在本頻道啟用的角色卡。"""
    def __init__(self, guild_id, channel_id, timeout=3600 * 12):
        super().__init__(timeout=timeout)
        self.guild_id = guild_id
        self.channel_id = channel_id
        self.message = None

    @discord.ui.button(label="📈 開始我的成長紀錄（只有你看得到）", style=discord.ButtonStyle.primary)
    async def start_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        guild_id, channel_id, user_id = self.guild_id, self.channel_id, interaction.user.id
        # 頻道閘門：嚴格模式（本頻道 GM 設了白名單）下不在白名單／沒開卡會被擋；
        # 自動模式（沒 GM／GM 沒設白名單）一律放行。被擋時說明原因（只有本人看得到）。
        allowed, reason = growth_channel_gate(guild_id, channel_id)
        if not allowed:
            await interaction.response.send_message(
                embed=discord.Embed(title="🚫 本頻道暫不記錄成長", description=reason, color=0xffaa00),
                ephemeral=True,
            )
            return
        already_active = growth_manager.is_active(guild_id, channel_id, user_id)
        growth_manager.start_session(guild_id, channel_id, user_id)
        desc = "已開始記錄你在**本頻道**的技能檢定。之後用 `.cc 技能值 技能名稱` 檢定時會自動記錄，結束時用 `.end` 查看成長清單。\n（只記錄你自己的檢定，且只在這個頻道生效）"
        if already_active:
            desc = "⚠️ 偵測到你在本頻道已經有一份進行中的紀錄，已捨棄舊紀錄、重新開始一份新的。\n\n" + desc
        embeds = [discord.Embed(title="📈 已開始記錄成長清單", description=desc, color=0x00aaff)]

        alias = pc_active_manager.get_active(guild_id, channel_id, user_id)
        card = pc_card_manager.get_card(guild_id, user_id, alias) if alias else None
        if card:
            embeds.append(format_pc_card_embed(card, alias, interaction.user))
        else:
            embeds.append(discord.Embed(
                title="📇 尚未啟用角色卡",
                description="本頻道目前沒有幫你啟用角色卡，請用 `.pc` 叫出面板按【啟用】。",
                color=0xffaa00,
            ))
        await interaction.response.send_message(embeds=embeds, ephemeral=True)

    async def on_timeout(self):
        for child in self.children:
            child.disabled = True
        if self.message:
            try:
                await self.message.edit(view=self)
            except discord.HTTPException:
                pass

async def _dot_start(message, cmd, cmd_lower):
    """.start 開啟成長紀錄面板。有處理回傳 True，沒輪到自己回傳 False 讓分派器往下找。
    頻道裡任何人都能按同一顆按鈕，各自開始「自己」的成長紀錄，並用 ephemeral 看到自己的
    成長紀錄狀態＋目前啟用的角色卡（只有按的人看得到，彼此看不到對方的內容）。"""
    if re.match(r'^start(\s|$)', cmd, re.I):
        guild_id, channel_id = message.guild.id, message.channel.id
        view = StartGrowthSharedView(guild_id, channel_id)
        sent = await message.channel.send(
            content="📈 成長紀錄面板已建立，任何人都可以按下方按鈕開始「自己」在本頻道的成長紀錄，並查看自己目前啟用的角色卡（只有按的人看得到）。",
            view=view,
        )
        view.message = sent
        return True
    return False

def build_growth_end_embed(session):
    """把 growth_manager.end_session() 回傳的 session dict 組成「結團成長清單」embed（不含 footer，呼叫端自行加上）。"""
    skills = session.get('skills', {})
    unnamed = session.get('unnamed') or {'count': 0, 'links': []}
    san_loss = session.get('san_loss') or {'total': 0, 'entries': []}
    adjustments = session.get('adjustments') or []
    madness = session.get('madness') or {'entries': []}
    if not skills and not unnamed['count'] and not san_loss['entries'] and not adjustments and not madness['entries']:
        return discord.Embed(title="📈 結團成長清單", description="這段期間沒有任何符合條件的 `.cc` 檢定紀錄（暗骰、獎勵/懲罰骰不列入計算）。", color=0x00aaff)
    lines = []
    for name in sorted(skills.keys()):
        info = skills[name]
        if name in NON_GROWABLE_SKILLS:
            grow_text = "屬性／固定技能，無法透過檢定成長"
        else:
            grow_text = "該技能可成長" if info['success'] else "該技能不可成長"
        lines.append(
            f"**{name}**（最後使用技能值 {info['last_skill_value']}%）\n"
            f"成功過 {info['total']} 次｜大成功 {info['crit_count']}｜大失敗 {info['fumble_count']}，{grow_text}"
        )
    embed = discord.Embed(
        title="📈 結團成長清單",
        description="\n\n".join(lines) if lines else "這段期間沒有任何有填寫技能名稱的檢定。",
        color=0x00aaff,
    )
    if unnamed['count']:
        max_show = 15
        shown = unnamed['links'][-max_show:]
        value = "\n".join(f"{i+1}. [連結]({link})" for i, link in enumerate(shown))
        if unnamed['count'] > len(shown):
            value += f"\n（僅顯示最近 {max_show} 筆，共 {unnamed['count']} 次）"
        embed.add_field(name=f"📎 未填寫技能名稱的檢定（共 {unnamed['count']} 次）", value=value, inline=False)
    if san_loss['entries']:
        max_show = 15
        entries = san_loss['entries']
        shown = entries[-max_show:]
        san_lines = []
        for e in shown:
            mark = "✅ 成功" if e['success'] else "❌ 失敗"
            san_lines.append(f"擲骰 {e['roll']}｜{mark}｜損失 {e['loss']}｜剩餘 SAN {e['new_san']}")
        value = "\n".join(san_lines)
        if len(entries) > len(shown):
            value += f"\n（僅顯示最近 {max_show} 筆，共 {len(entries)} 次）"
        embed.add_field(name=f"🧠 理智檢定損失（共損失 {san_loss['total']} 點）", value=value, inline=False)
    if madness['entries']:
        max_show = 15
        entries = madness['entries']
        shown = entries[-max_show:]
        madness_lines = []
        for e in shown:
            alias_desc = e['alias'] or "（未指定角色）"
            madness_lines.append(
                f"{alias_desc}｜單次損失 {e['san_loss']} 點 SAN 後智力檢定｜"
                f"智力 {e['int_value']}％｜擲骰 {e['roll']}｜**{e['level']}** → 陷入瘋狂"
            )
        value = "\n".join(madness_lines)
        if len(entries) > len(shown):
            value += f"\n（僅顯示最近 {max_show} 筆，共 {len(entries)} 次）"
        embed.add_field(name=f"💀 陷入瘋狂（共 {len(entries)} 次）", value=value, inline=False)
    if adjustments:
        max_show = 15
        shown = adjustments[-max_show:]
        adj_lines = []
        for a in shown:
            delta_desc = f"（{'+' if a['num'] >= 0 else ''}{a['num']}）" if a['is_relative'] else "（直接設定）"
            adj_lines.append(f"{a['alias']}／{a['field']}：{a['old']} → {a['new']} {delta_desc}")
        value = "\n".join(adj_lines)
        if len(adjustments) > len(shown):
            value += f"\n（僅顯示最近 {max_show} 筆，共 {len(adjustments)} 次）"
        embed.add_field(name=f"🛠️ 角色卡欄位／技能調整（共 {len(adjustments)} 次）", value=value, inline=False)
    return embed

class EndGrowthSharedView(discord.ui.View):
    """.end 面板：跟 StartGrowthSharedView 同一套模式，頻道裡任何人都能按這顆按鈕，
    各自結束「自己」在本頻道的成長紀錄，並用 ephemeral（只有按的人看得到）顯示結團成長清單。"""
    def __init__(self, guild_id, channel_id, timeout=3600 * 12):
        super().__init__(timeout=timeout)
        self.guild_id = guild_id
        self.channel_id = channel_id
        self.message = None

    @discord.ui.button(label="📈 結束我的成長紀錄（只有你看得到）", style=discord.ButtonStyle.primary)
    async def end_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        guild_id, channel_id, user_id = self.guild_id, self.channel_id, interaction.user.id
        session = growth_manager.end_session(guild_id, channel_id, user_id)
        if session is None:
            embed = discord.Embed(title="❌ 沒有進行中的紀錄", description="請先按上方（或另一則）成長紀錄面板開始記錄。", color=0xff0000)
        else:
            embed = build_growth_end_embed(session)
        embed.set_footer(text=interaction.user.display_name, icon_url=interaction.user.display_avatar.url)
        await interaction.response.send_message(embed=embed, ephemeral=True)

    async def on_timeout(self):
        for child in self.children:
            child.disabled = True
        if self.message:
            try:
                await self.message.edit(view=self)
            except discord.HTTPException:
                pass

async def _dot_end(message, cmd, cmd_lower):
    """.end 開啟成長紀錄結算面板。有處理回傳 True，沒輪到自己回傳 False 讓分派器往下找。
    頻道裡任何人都能按同一顆按鈕，各自結束「自己」的成長紀錄，並用 ephemeral 看到自己的
    結團成長清單（只有按的人看得到，彼此看不到對方的內容）。"""
    if re.match(r'^end(\s|$)', cmd, re.I):
        guild_id, channel_id = message.guild.id, message.channel.id
        view = EndGrowthSharedView(guild_id, channel_id)
        sent = await message.channel.send(
            content="📈 成長紀錄結算面板已建立，任何人都可以按下方按鈕結束「自己」在本頻道的成長紀錄並查看清單（只有按的人看得到）。",
            view=view,
        )
        view.message = sent
        return True
    return False

async def _dot_rts(message, cmd, cmd_lower):
    """.rts 抽籤表管理。有處理回傳 True，沒輪到自己回傳 False 讓分派器往下找。"""
    # (?![a-z]) 這類判斷是為了避免吃掉別的字（例如自訂指令 .rtsxxx），數字/中文/冒號仍可直接相連
    if re.match(r'^rts(?![a-z])', cmd_lower):
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
    return False

async def _dot_multi(message, cmd, cmd_lower):
    """`.N 指令` 多重擲骰／多重 CoC 檢定。有處理回傳 True，沒輪到自己回傳 False 讓分派器往下找。"""
    multi_match = re.match(r'^(\d+)\s+(.+)$', cmd)
    if multi_match:
        times = int(multi_match.group(1))
        rest = multi_match.group(2).strip()
        cc_match = re.match(r'^(cc(?:[12]?|n[12]?)?)(?:\s+(.*))?$', rest, re.I)
        if cc_match:
            cmd_part = cc_match.group(1).lower()
            args = cc_match.group(2) or ""
            bonus_dice = cc_bonus_dice(cmd_part)
            if not args.strip():
                await message.channel.send(embed=discord.Embed(title="❌ 缺少技能值", color=0xff0000))
                return True
            # 對抗檢定（帶 @對方）需要防禦方按按鈕回應，是一個要等對方互動的流程，
            # 沒辦法批次重複 N 次，所以直接擋下來給明確提示，而不是讓 @提及被誤判成技能名稱
            # 一路查下去噴出「找不到技能」這種不知所云的錯誤。
            defender = next((u for u in message.mentions if not u.bot and u.id != message.author.id), None)
            if defender:
                await message.channel.send(embed=discord.Embed(
                    title="❌ 對抗檢定不支援 `.N cc` 這種重複前綴",
                    description="對抗檢定要等對方按按鈕回應，沒辦法一次批次跑 N 次。請直接打 `.cc 技能 @對方`，要幾次就重複打幾次。",
                    color=0xff0000,
                ))
                return True
            # 直接交給 handle_coc_roll 處理，並用 forced_repeat 帶入次數：
            # 這樣「.N cc 數值」（純數值）跟「.N cc 技能名」（已啟用角色卡自動抓值）
            # 都走同一套邏輯，例如 .5 cc 鬥毆 就能像 .10 cc 20 一樣正常運作，
            # 不用再打 `cc 鬥毆 3` 這種把次數塞在技能名稱後面的寫法。
            await handle_coc_roll(message, args, 'channel', bonus_dice, forced_repeat=times)
            return True
        else:
            results = multi_roll(times, rest)
            if results:
                embed = discord.Embed(title=f"多重擲骰：{rest} ({times}次)", color=0x00aaff)
                desc = ""
                for i, line in enumerate(results, 1):
                    desc += f"{i}: {line}\n"
                embed.description = desc
                embed.set_footer(text=message.author.display_name, icon_url=message.author.display_avatar.url)
                await message.channel.send(embed=embed)
            else:
                await message.channel.send(embed=discord.Embed(title="❌ 多重擲骰失敗", description=rest, color=0xff0000))
            return True
    return False

async def _dot_int(message, cmd, cmd_lower):
    """.int 隨機整數。有處理回傳 True，沒輪到自己回傳 False 讓分派器往下找。"""
    if re.match(r'^int(?![a-z])', cmd_lower):
        parts = cmd.split()
        if len(parts) == 3:
            await handle_int_roll(message, f"{parts[1]} {parts[2]}", 'channel')
        else:
            await message.channel.send(embed=discord.Embed(title="❌ 格式錯誤", description="格式：`.int 最小 最大`", color=0xff0000))
        return True
    return False

async def _dot_calc(message, cmd, cmd_lower):
    """.calc 計算。有處理回傳 True，沒輪到自己回傳 False 讓分派器往下找。"""
    if re.match(r'^calc(?![a-z])', cmd_lower):
        expr = cmd[4:].strip()
        await handle_calc_roll(message, expr, 'channel')
        return True
    return False

async def _dot_cc(message, cmd, cmd_lower):
    """.cc／.coc CoC 檢定（含獎懲骰後綴）。帶 @對方時走「CC 對抗檢定」，提醒對方可以反擊或閃避。
    有處理回傳 True，沒輪到自己回傳 False 讓分派器往下找。"""
    if re.match(r'^(?:coc|cc(?:n[12]?|[12])?)(?![a-z])', cmd_lower):
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
                if cmd_lower.startswith('coc'):
                    rest = cmd[3:].strip()
                else:
                    rest = cmd[2:].strip()

        defender = next((u for u in message.mentions if not u.bot and u.id != message.author.id), None)
        if defender:
            skill_text = re.sub(r'<@!?\d+>', '', rest).strip()
            await handle_cc_opposed(message, skill_text, bonus_dice, defender)
        else:
            await handle_coc_roll(message, rest, 'channel', bonus_dice)
        return True
    return False

async def _dot_melee(message, cmd, cmd_lower):
    """.melee：叫出戰技面板（persistent view，永不失效）。舊的 `.melee 技能 @對方` 文字參數語法已移除，
    帶參數也一律回面板並提示改用按鈕。有處理回傳 True，沒輪到自己回傳 False 讓分派器往下找。"""
    melee_top_match = re.match(r'^melee(?:\s+(.*))?$', cmd, re.I | re.S)
    if not melee_top_match:
        return False
    rest = (melee_top_match.group(1) or '').strip()
    desc = (
        "🗡️ **戰技判定**：人人可按，按的人就是攻擊方。先用成員選單選對抗對象（會自動搜尋對方在本頻道啟用中的角色卡），"
        "再跳表單填技能名稱或數值——留空自動抓你角色卡的「鬥毆→格鬥」；替 NPC 出手可另填 NPC 名稱＋數值＋體格。\n"
        "體格照 CoC 7e 戰技規則自動比較：對方體格大 1／2 → 攻擊方加 1／2 顆懲罰骰；大 3 以上戰技直接無效。\n\n"
        "📏 **體格判定**：**沒有體格資料**（沒開角色卡或卡上沒填）**才需要按**——把自己的體格暫存在本頻道（不會寫回角色卡，角色卡有值時優先用卡上的）。\n\n"
        "防禦方收到對抗訊息後按【反擊】或【閃避】回應。面板與對抗按鈕都不會失效，隔一段時間再回來按也可以。"
    )
    if rest:
        desc = "ℹ️ `.melee 技能 @對方` 的文字參數語法已移除，請改用下面的面板按鈕。\n\n" + desc
    embed = discord.Embed(title="🗡️ 戰技面板", description=desc, color=0x00aaff)
    await message.channel.send(embed=embed, view=MeleePanelView())
    return True

# ---------- 快打模式（.hp／.mp／.san／.luk 快速增減）與介面模式（.DATA 面板） ----------
_QUICK_ADJ_DICE_RE = re.compile(r'^([+-])\s*(\d*[dD]\d+)$')
_QUICK_ADJ_PLAIN_RE = re.compile(r'^([+-]?)(\d+)$')

def _parse_quick_delta(value_raw):
    """解析快打指令／面板自訂調整的數值：
    `+5`／`-2` → 相對增減；`10` → 直接設成該值；`+1d6`／`-1d6` → 先擲骰，骰出的點數再相對增減（`.san -1d6` 用法）。
    回傳 (num, is_relative, roll_note, error)；error 有值時其餘欄位無效，呼叫端應直接回報錯誤。"""
    value_raw = value_raw.strip()
    dice_m = _QUICK_ADJ_DICE_RE.match(value_raw)
    if dice_m:
        sign, dice_expr = dice_m.groups()
        dice_res = parse_dice_expression(dice_expr.upper())
        if not dice_res or dice_res.total is None:
            return None, None, None, f"看不懂骰子式「{dice_expr}」。"
        rolled = dice_res.total
        num = rolled if sign == '+' else -rolled
        roll_note = f"🎲 擲骰 {dice_expr}：{rolled}[{', '.join(map(str, dice_res.rolls))}]"
        return num, True, roll_note, None
    plain_m = _QUICK_ADJ_PLAIN_RE.match(value_raw)
    if not plain_m:
        return None, None, None, f"看不懂「{value_raw}」，請用 `+5`／`-2`（相對增減）、`10`（直接設定）或 `-1d6`（先擲骰再扣）這幾種格式。"
    sign, num_str = plain_m.groups()
    is_relative = bool(sign)
    num = int(sign + num_str) if sign else int(num_str)
    return num, is_relative, None, None

def _lookup_active_card(guild_id, channel_id, user_id):
    """回傳 (active_alias, card, error_embed)；成功時 error_embed 為 None，失敗時 active_alias／card 為 None。"""
    active_alias = pc_active_manager.get_active(guild_id, channel_id, user_id)
    if not active_alias:
        return None, None, discord.Embed(title="❌ 尚未啟用角色卡", description="請先用 `.pc` 叫出面板，按【啟用】選擇本頻道要使用的角色卡。", color=0xff0000)
    card = pc_card_manager.get_card(guild_id, user_id, active_alias)
    if not card:
        pc_active_manager.clear_active(guild_id, channel_id, user_id)
        return None, None, discord.Embed(title="⚠️ 啟用中的角色卡已不存在", description=f"角色名稱「{active_alias}」已被刪除，請用 `.pc` 面板的【啟用】重新選一張。", color=0xffaa00)
    return active_alias, card, None

def _apply_stat_delta(guild_id, channel_id, user_id, active_alias, card, kind, num, is_relative):
    """套用 HP／MP／SAN／LUK 欄位調整、存卡、記錄成長清單，回傳 (舊值, 新值, 附加提醒文字清單)。"""
    old_val, new_val = apply_pc_field_adjustment(card, kind, None, num, is_relative)
    pc_card_manager.save_card(guild_id, user_id, active_alias, card)
    if growth_manager.is_active(guild_id, channel_id, user_id):
        growth_manager.record_adjustment(guild_id, channel_id, user_id, active_alias, kind.upper(), old_val, new_val, is_relative, num)

    notes = []
    requested = (old_val + num) if is_relative else num
    if kind == 'hp' and card.get('hp_max') is not None and new_val >= card['hp_max'] and requested > card['hp_max']:
        notes.append(f"📌 已達 HP 上限（{card['hp_max']}），鎖在上限值。")
    elif kind == 'mp' and card.get('mp_max') is not None and new_val >= card['mp_max'] and requested > card['mp_max']:
        notes.append(f"📌 已達 MP 上限（{card['mp_max']}），鎖在上限值。")
    if kind == 'san':
        threshold = card.get('san_max')
        if threshold is not None and new_val <= threshold and old_val > threshold:
            notes.append(f"⚠️ 理智已降至不定性瘋狂線（{threshold}）或以下，角色陷入不定性瘋狂！")
        cap_san = 99 - get_cthulhu_mythos_value(card)
        if requested > cap_san and new_val == cap_san:
            notes.append(f"📌 理智恢復已達上限（99-克蘇魯神話 {99 - cap_san} = {cap_san}），鎖在上限值。")
    if kind == 'hp' and new_val <= 0 and old_val > 0:
        notes.append("💀 HP 已降至 0，角色重傷瀕死，請 KP 裁定。")
    return old_val, new_val, notes

_QUICK_STAT_FIELDS = {
    'hp': ('hp', '❤️', 'HP'),
    'mp': ('mp', '🔵', 'MP'),
    'san': ('san', '🧠', 'SAN'),
    'luk': ('luck', '🍀', 'LUK'),
    'luck': ('luck', '🍀', 'LUK'),
}

async def _dot_quick_stat(message, cmd, cmd_lower):
    """快打模式：`.hp -2` 直接對目前啟用角色卡的 HP 做增減；`.san -1d6` 會先擲一顆骰子再扣對應點數。
    也支援 `.mp`／`.luk`（`.luck` 同義）。有處理回傳 True，沒輪到自己回傳 False 讓分派器往下找。"""
    m = re.match(r'^(hp|mp|san|luk|luck)\s+(\S.*)$', cmd, re.I)
    if not m:
        return False
    key = m.group(1).lower()
    value_raw = m.group(2).strip()
    kind, emoji, title_name = _QUICK_STAT_FIELDS[key]
    guild_id, channel_id, user_id = message.guild.id, message.channel.id, message.author.id

    active_alias, card, error_embed = _lookup_active_card(guild_id, channel_id, user_id)
    if error_embed:
        await message.channel.send(embed=error_embed)
        return True

    num, is_relative, roll_note, err = _parse_quick_delta(value_raw)
    if err:
        await message.channel.send(embed=discord.Embed(title="❌ 格式錯誤", description=err, color=0xff0000))
        return True

    old_val, new_val, notes = _apply_stat_delta(guild_id, channel_id, user_id, active_alias, card, kind, num, is_relative)

    delta_desc = f"（{'+' if num >= 0 else ''}{num}）" if is_relative else "（直接設定）"
    lines = []
    if roll_note:
        lines.append(roll_note)
    lines.append(f"**{title_name}**：{old_val} → {new_val} {delta_desc}")
    lines.extend(notes)

    embed = discord.Embed(title=f"{emoji} 「{active_alias}」的 {title_name} 已調整", description="\n".join(lines), color=0x00aaff)
    embed.set_footer(text=message.author.display_name, icon_url=message.author.display_avatar.url)
    await message.channel.send(embed=embed)
    return True

# ---------- 介面模式（.DATA 面板） ----------
_DATA_PANEL_FIELDS = ('hp', 'mp', 'san', 'luck')
_DATA_PANEL_TITLE = {'hp': 'HP', 'mp': 'MP', 'san': 'SAN', 'luck': 'LUK'}
_DATA_PANEL_EMOJI = {'hp': '❤️', 'mp': '🔵', 'san': '🧠', 'luck': '🍀'}

class DataStatAdjustModal(discord.ui.Modal):
    """`.DATA` 面板按下 HP／MP／SAN／LUK 其中一顆後跳出的表單，只填這一項的調整量。
    格式跟快打指令一樣：`+5`／`-2`（相對增減）、`10`（直接設定）、`-1d6`（先擲骰再扣，SAN／HP 常用）。"""
    def __init__(self, panel_view, kind):
        super().__init__(title=f"調整 {_DATA_PANEL_TITLE[kind]}")
        self.panel_view = panel_view
        self.kind = kind
        self.value_input = discord.ui.TextInput(
            label=f"{_DATA_PANEL_TITLE[kind]} 調整量",
            placeholder="例如 -5、+3、20（直接設定）、-1d6（先擲骰再扣）",
            required=True,
            max_length=10,
        )
        self.add_item(self.value_input)

    async def on_submit(self, interaction: discord.Interaction):
        pv = self.panel_view
        if not pv._allowed(interaction.user.id):
            await interaction.response.send_message("這不是你的角色卡面板，請自行 `.DATA` 叫出你自己的。", ephemeral=True)
            return
        active_alias, card, error_embed = _lookup_active_card(pv.guild_id, pv.channel_id, pv.owner_id)
        if error_embed:
            await interaction.response.send_message(embed=error_embed, ephemeral=True)
            return

        raw = str(self.value_input.value or '').strip()
        num, is_relative, roll_note, err = _parse_quick_delta(raw)
        if err:
            await interaction.response.send_message(f"❌ {err}", ephemeral=True)
            return

        old_val, new_val, notes = _apply_stat_delta(pv.guild_id, pv.channel_id, pv.owner_id, active_alias, card, self.kind, num, is_relative)
        delta_desc = f"（{'+' if num >= 0 else ''}{num}）" if is_relative else "（直接設定）"
        lines = []
        if roll_note:
            lines.append(roll_note)
        lines.append(f"**{_DATA_PANEL_TITLE[self.kind]}**：{old_val} → {new_val} {delta_desc}")
        lines.extend(notes)

        embed = format_pc_quick_status(card, active_alias, interaction.user)
        embed.add_field(name="🔧 最近調整", value="\n".join(lines), inline=False)
        try:
            await interaction.response.edit_message(embed=embed, view=pv)
        except discord.HTTPException:
            await interaction.response.send_message(embed=embed, view=pv)

class DataStatButton(discord.ui.Button):
    """`.DATA` 面板的單顆按鈕（HP／MP／SAN／LUK 各一顆），按下去跳出小表單輸入調整量。"""
    def __init__(self, kind):
        super().__init__(label=f"{_DATA_PANEL_EMOJI[kind]} {_DATA_PANEL_TITLE[kind]}", style=discord.ButtonStyle.secondary, row=0)
        self.kind = kind

    async def callback(self, interaction: discord.Interaction):
        if not self.view._allowed(interaction.user.id):
            await interaction.response.send_message("這不是你的角色卡面板，請自行 `.DATA` 叫出你自己的。", ephemeral=True)
            return
        await interaction.response.send_modal(DataStatAdjustModal(self.view, self.kind))

def _calc_indefinite_madness_threshold(san_cur):
    """不定性瘋狂線標準值：SAN－(SAN／5)，無條件捨去（對應 KP 慣用試算表寫法 INT(SAN-SAN/5)）。"""
    return int(san_cur - san_cur / 5)

class RecalcMadnessThresholdButton(discord.ui.Button):
    """`.DATA` 面板的「重算瘋狂線」按鈕：以目前 SAN 重新算出不定性瘋狂線（SAN－SAN/5，無條件捨去），
    直接覆蓋角色卡的 san_max。要不要按、什麼時候按（安穩睡過一覺後／團務結束後）由 KP／玩家自行判斷，
    按鈕本身不限制時機。"""
    def __init__(self):
        super().__init__(label="🌀 重算瘋狂線", style=discord.ButtonStyle.secondary, row=1)

    async def callback(self, interaction: discord.Interaction):
        pv = self.view
        if not pv._allowed(interaction.user.id):
            await interaction.response.send_message("這不是你的角色卡面板，請自行 `.DATA` 叫出你自己的。", ephemeral=True)
            return
        active_alias, card, error_embed = _lookup_active_card(pv.guild_id, pv.channel_id, pv.owner_id)
        if error_embed:
            await interaction.response.send_message(embed=error_embed, ephemeral=True)
            return
        san_cur = card.get('san_cur')
        if san_cur is None:
            await interaction.response.send_message("角色卡沒有紀錄目前 SAN 數值，無法重算瘋狂線。", ephemeral=True)
            return

        old_threshold = card.get('san_max')
        new_threshold = _calc_indefinite_madness_threshold(san_cur)
        card['san_max'] = new_threshold
        pc_card_manager.save_card(pv.guild_id, pv.owner_id, active_alias, card)

        old_desc = str(old_threshold) if old_threshold is not None else "（未設定）"
        lines = [f"**長瘋線（不定性瘋狂線）**：{old_desc} → {new_threshold}　（以目前 SAN {san_cur} 算出：INT({san_cur}－{san_cur}/5)，已寫回角色卡）"]

        embed = format_pc_quick_status(card, active_alias, interaction.user)
        embed.add_field(name="🌀 最近調整", value="\n".join(lines), inline=False)
        try:
            await interaction.response.edit_message(embed=embed, view=pv)
        except discord.HTTPException:
            await interaction.response.send_message(embed=embed, view=pv)

class DataPanelView(discord.ui.View):
    """`.DATA` 叫出的角色狀態面板：HP／MP／SAN／LUK 各一顆按鈕，
    按下去跳出小表單輸入調整量（支援 `+5`／`-2`／`10`／`-1d6` 這幾種格式），送出後就地更新卡片顯示。
    另有「重算瘋狂線」按鈕：以目前 SAN 重算不定性瘋狂線（SAN－SAN/5，無條件捨去），適合在安穩睡過一覺
    後或團務收尾時按下，實際時機由 KP／玩家自行判斷。
    只有面板擁有者本人或本頻道 GM 能操作按鈕。"""
    def __init__(self, guild_id, channel_id, owner_id):
        super().__init__(timeout=1800)
        self.guild_id = guild_id
        self.channel_id = channel_id
        self.owner_id = owner_id
        self.message = None
        for kind in _DATA_PANEL_FIELDS:
            self.add_item(DataStatButton(kind))
        self.add_item(RecalcMadnessThresholdButton())

    def _allowed(self, user_id):
        return user_id == self.owner_id or is_gm(self.guild_id, self.channel_id, user_id)

    async def on_timeout(self):
        for child in self.children:
            child.disabled = True
        if self.message:
            try:
                await self.message.edit(view=self)
            except discord.HTTPException:
                pass

async def _dot_data(message, cmd, cmd_lower):
    """.data／.DATA 角色狀態面板：顯示目前啟用角色卡的 HP／MP／SAN／LUK，並附上 HP／MP／SAN／LUK 四顆按鈕（介面模式）。
    有處理回傳 True，沒輪到自己回傳 False 讓分派器往下找。"""
    if re.match(r'^data(\s|$)', cmd, re.I):
        guild_id, channel_id, user_id = message.guild.id, message.channel.id, message.author.id
        active_alias, card, error_embed = _lookup_active_card(guild_id, channel_id, user_id)
        if error_embed:
            await message.channel.send(embed=error_embed)
            return True
        embed = format_pc_quick_status(card, active_alias, message.author)
        view = DataPanelView(guild_id, channel_id, user_id)
        view.message = await message.channel.send(embed=embed, view=view)
        return True
    return False

async def _dot_pc(message, cmd, cmd_lower):
    """.pc 角色卡管理。有處理回傳 True，沒輪到自己回傳 False 讓分派器往下找。"""
    if re.match(r'^pc(\s|$)', cmd, re.I):
        rest = cmd[2:].strip()
        guild_id, channel_id, user_id = message.guild.id, message.channel.id, message.author.id

        adj_match = re.match(r'^adj(?:\s+(.*))?$', rest, re.I)
        if adj_match:
            adj_args = (adj_match.group(1) or '').strip()
            usage = "格式：`.pc adj 欄位 +/-數值`（相對增減）或 `.pc adj 欄位 數值`（直接設成該值）\n欄位可以是屬性（力量、敏捷、意志、體質、外貌、教育、體型、智力）、LUK／幸運、SAN、HP、MP、靈感，也可以是角色卡上任何一個技能名稱（例如 偵查、鬥毆），可以一次調整多個，例如：\n`.pc adj san -5` 或 `.pc adj 力量 -3 幸運 +2` 或 `.pc adj 偵查 +5`"
            if not adj_args:
                await message.channel.send(embed=discord.Embed(title="❌ 用法錯誤", description=usage, color=0xff0000))
                return True
            active_alias = pc_active_manager.get_active(guild_id, channel_id, user_id)
            if not active_alias:
                await message.channel.send(embed=discord.Embed(title="❌ 尚未啟用角色卡", description="請先用 `.pc` 叫出面板，按【啟用】選擇本頻道要使用的角色卡。", color=0xff0000))
                return True
            card = pc_card_manager.get_card(guild_id, user_id, active_alias)
            if not card:
                pc_active_manager.clear_active(guild_id, channel_id, user_id)
                await message.channel.send(embed=discord.Embed(title="⚠️ 啟用中的角色卡已不存在", description=f"角色名稱「{active_alias}」已被刪除，請用 `.pc` 面板的【啟用】重新選一張。", color=0xffaa00))
                return True

            tokens = adj_args.split()
            if len(tokens) % 2 != 0:
                await message.channel.send(embed=discord.Embed(title="❌ 用法錯誤", description=usage, color=0xff0000))
                return True

            lines, errors, changed = [], [], False
            adj_records = []  # 供成長清單記錄用：[(欄位顯示名稱, 舊值, 新值, is_relative, num), ...]
            for i in range(0, len(tokens), 2):
                field_raw, value_raw = tokens[i], tokens[i + 1]
                info = resolve_pc_adj_field(field_raw)
                skill_entry = None if info else find_pc_skill_entry(card, field_raw)
                if not info and not skill_entry:
                    errors.append(f"找不到欄位或技能「{field_raw}」")
                    continue
                m = re.match(r'^([+-]\d+)$', value_raw)
                is_relative = bool(m)
                if not re.match(r'^[+-]?\d+$', value_raw):
                    errors.append(f"「{field_raw} {value_raw}」數值格式錯誤")
                    continue
                num = int(value_raw)

                if info:
                    kind, attr_name = info
                    old_val, new_val = apply_pc_field_adjustment(card, kind, attr_name, num, is_relative)
                    changed = True
                    delta_desc = f"（{'+' if num >= 0 else ''}{num}）" if is_relative else "（直接設定）"
                    line = f"**{field_raw}**：{old_val} → {new_val} {delta_desc}"
                    if kind == 'hp' and card.get('hp_max') is not None and new_val >= card['hp_max'] and (old_val + num if is_relative else num) > card['hp_max']:
                        line += f"\n📌 已達 HP 上限（{card['hp_max']}），鎖在上限值。"
                    elif kind == 'mp' and card.get('mp_max') is not None and new_val >= card['mp_max'] and (old_val + num if is_relative else num) > card['mp_max']:
                        line += f"\n📌 已達 MP 上限（{card['mp_max']}），鎖在上限值。"
                    if kind == 'san':
                        threshold = card.get('san_max')
                        if threshold is not None and new_val <= threshold and old_val > threshold:
                            line += f"\n⚠️ 理智已降至不定性瘋狂線（{threshold}）或以下，角色陷入不定性瘋狂！"
                        requested_san = old_val + num if is_relative else num
                        cap_san = 99 - get_cthulhu_mythos_value(card)
                        if requested_san > cap_san and new_val == cap_san:
                            line += f"\n📌 理智恢復已達上限（99-克蘇魯神話 {99 - cap_san} = {cap_san}），鎖在上限值。"
                    lines.append(line)
                    adj_records.append((field_raw, old_val, new_val, is_relative, num))
                else:
                    group, idx, skill_name, old_val = skill_entry
                    if not isinstance(old_val, int):
                        errors.append(f"「{skill_name}」目前的數值不是數字，無法調整")
                        continue
                    new_val = old_val + num if is_relative else num
                    new_val = max(0, new_val)
                    group[idx] = (skill_name, new_val)
                    changed = True
                    delta_desc = f"（{'+' if num >= 0 else ''}{num}）" if is_relative else "（直接設定）"
                    line = f"**{skill_name}**：{old_val} → {new_val} {delta_desc}"
                    lines.append(line)
                    adj_records.append((skill_name, old_val, new_val, is_relative, num))

            if changed:
                pc_card_manager.save_card(guild_id, user_id, active_alias, card)
                if adj_records and growth_manager.is_active(guild_id, channel_id, user_id):
                    for rec_field, rec_old, rec_new, rec_is_relative, rec_num in adj_records:
                        growth_manager.record_adjustment(
                            guild_id, channel_id, user_id, active_alias,
                            rec_field, rec_old, rec_new, rec_is_relative, rec_num,
                        )
            embed = discord.Embed(
                title=f"🛠️ 已調整角色卡「{active_alias}」" if changed else "❌ 沒有任何欄位被調整",
                description="\n".join(lines) if lines else None,
                color=0x00aaff if changed else 0xff0000,
            )
            if errors:
                embed.add_field(name="⚠️ 部分欄位失敗", value="\n".join(errors), inline=False)
            await message.channel.send(embed=embed)
            return True

        gm_match = re.match(r'^gm(?:\s+(.*))?$', rest, re.I)
        if gm_match:
            # GM 代管角色卡：同伺服器內只要在任一頻道登記過 GM 就能用，不限本頻道。
            if not gm_manager.is_gm_anywhere_in_guild(guild_id, user_id):
                await message.channel.send(embed=discord.Embed(title="❌ 沒有權限", description="你不是本伺服器登記過的 GM，無法使用代管角色卡功能。", color=0xff0000))
                return True
            target = next((u for u in message.mentions if not u.bot), None)
            if target:
                await message.channel.send(embed=build_gm_pc_manage_embed(target), view=GMPCManagePanelView(target))
            else:
                await message.channel.send(
                    embed=discord.Embed(title="🎩 代管角色卡", description="請選擇要代管哪位玩家（也可以直接打 `.pc gm @玩家` 跳過這個選單）：", color=0x00aaff),
                    view=GMPCTargetSelectView(),
                )
            return True

        # `.pc` 以及 `.pc` 後面接任何內容（除了上面的 adj／gm）→ 一律叫出角色卡主面板。
        # 建立／啟用／查看／編輯／刪除全部在面板上（建立支援貼上文字／上傳檔案／試算表網址三種），
        # 原本的 `.pc set`／`.pc url`／`.pc show`／`.pc edit`／`.pc del`／`.pc 角色名稱` 文字子指令已移除。
        legacy_note = ""
        if rest:
            legacy_note = f"\n\n（`.pc {rest}` 這種文字指令已改成面板操作，請直接按下面的按鈕。）"
        await message.channel.send(
            embed=discord.Embed(
                title="🗂️ 角色卡面板",
                description=(
                    "按下面的按鈕操作，誰按算誰的（只會動到你自己的角色卡，選單只有你看得到）：\n"
                    "🆕 建立：選「貼上文字」「上傳檔案」或「貼上試算表網址」\n"
                    "✅ 啟用：選一張卡在**本頻道**啟用（換頻道要重新啟用）\n"
                    "📋 查看／✏️ 編輯／🗑️ 刪除：跳選單選要操作的角色卡\n"
                    "🎩 代管角色卡：GM 專用，可以幫其他玩家建立/查看/編輯/刪除角色卡\n"
                    "欄位微調可以直接打字，例如 `.pc adj san -5`"
                    + legacy_note
                ),
                color=0x00aaff,
            ),
            view=PCMainPanelView(),
        )
        return True
    return False

async def _dot_npc(message, cmd, cmd_lower):
    """`.npc` GM 專用的 NPC／怪物簡易卡：建立/編輯/刪除/查看/列表、快速調 HP、直接用卡上技能檢定。
    刻意做成純文字指令（跟 `.cmd`／`.rts` 同風格），不像 `.pc` 那樣有面板——這種卡片本來就只是
    GM 戰前隨手記兩三個數值用的，不需要匯入/驗證那一整套。
    有處理回傳 True，沒輪到自己回傳 False 讓分派器往下找。"""
    if not re.match(r'^npc(?![a-z])', cmd_lower):
        return False
    guild_id = message.guild.id

    def _is_gm():
        return gm_manager.is_gm_anywhere_in_guild(guild_id, message.author.id)

    def _gm_only_error():
        return discord.Embed(title="❌ 僅限 GM 使用", description="請先在任一頻道用 `.drgm addgm` 登記為 GM。", color=0xff0000)

    async def _send_npc_panel():
        await message.channel.send(
            embed=discord.Embed(
                title="🧾 NPC 卡",
                description=(
                    "點下面按鈕：新增/覆蓋、局部更新、查看、刪除，或開啟網頁表單。\n"
                    "「查看」「刪除」會跳出選單直接選 NPC，不用打名稱。\n"
                    "`.npc hp 名稱 +5`／`-1d6`／`10`　快速調整 HP（用法同 `.hp`）\n"
                    "`.npc cc 名稱 技能[,技能2]`　用卡上技能值檢定（支援 cc1/cc2/ccn1/ccn2 後綴）"
                ),
                color=0x00aaff,
            ),
            view=NpcFormView(guild_id),
        )

    parts = cmd[3:].strip().split(maxsplit=1)
    if not parts:
        await _send_npc_panel()
        return True
    sub_raw = parts[0]
    sub = sub_raw.lower()
    rest = parts[1] if len(parts) > 1 else ""

    if sub in ('add', 'edit'):
        await message.channel.send(embed=discord.Embed(
            title="ℹ️ 已改用按鈕表單",
            description="新增/覆蓋、局部更新 NPC 現在請直接打 `.npc`，跳出面板後點按鈕填表單。",
            color=0x00aaff,
        ))
        return True

    if sub == 'del':
        if not _is_gm():
            await message.channel.send(embed=_gm_only_error())
            return True
        name = rest.strip()
        if not name:
            await message.channel.send(embed=discord.Embed(title="❌ 請提供名稱", color=0xff0000))
            return True
        if npc_card_manager.delete(guild_id, name):
            await message.channel.send(embed=discord.Embed(title="✅ 已刪除 NPC 卡", description=name, color=0x00aaff))
        else:
            await message.channel.send(embed=discord.Embed(title="❌ 找不到 NPC", description=name, color=0xff0000))
        return True

    if sub in ('show', 'list'):
        name = rest.strip()
        if sub == 'list' or not name:
            names = npc_card_manager.list_names(guild_id)
            desc = "、".join(names) if names else "目前沒有任何 NPC 卡，請 GM 打 `.npc` 開啟面板建立。"
            await message.channel.send(embed=discord.Embed(title="📋 NPC／怪物卡列表", description=desc, color=0x00aaff))
            return True
        card = npc_card_manager.get(guild_id, name)
        if not card:
            await message.channel.send(embed=discord.Embed(title="❌ 找不到 NPC", description=name, color=0xff0000))
        else:
            await message.channel.send(embed=discord.Embed(title=f"🗒️ {name}", description=_format_npc_card(card), color=0x00aaff))
        return True

    if sub == 'form':
        await _send_npc_panel()
        return True

    if sub == 'hp':
        if not _is_gm():
            await message.channel.send(embed=_gm_only_error())
            return True
        tokens = rest.split(maxsplit=1)
        if len(tokens) < 2:
            await message.channel.send(embed=discord.Embed(title="❌ 用法", description="`.npc hp npc名稱 +5` / `.npc hp npc名稱 -1d6` / `.npc hp npc名稱 10`", color=0xff0000))
            return True
        name, value_raw = tokens[0], tokens[1]
        if not npc_card_manager.get(guild_id, name):
            await message.channel.send(embed=discord.Embed(title="❌ 找不到 NPC", description=name, color=0xff0000))
            return True
        num, is_relative, roll_note, error = _parse_quick_delta(value_raw)
        if error:
            await message.channel.send(embed=discord.Embed(title="❌ 無法解析", description=error, color=0xff0000))
            return True
        old, new = npc_card_manager.adjust_hp(guild_id, name, num, is_relative)
        desc = f"{roll_note}\n" if roll_note else ""
        desc += f"HP {old} → {new}"
        if new <= 0 and old > 0:
            desc += "\n💀 HP 已降至 0 以下。"
        await message.channel.send(embed=discord.Embed(title=f"❤️ {name}", description=desc, color=(0xff5555 if new <= 0 else 0x00aaff)))
        return True

    cc_sub_match = re.match(r'^(?:coc|cc(?:n[12]?|[12])?)$', sub)
    if cc_sub_match:
        bonus_dice = cc_bonus_dice(sub)
        tokens = rest.split(maxsplit=1)
        if len(tokens) < 2:
            await message.channel.send(embed=discord.Embed(title="❌ 用法", description="`.npc cc 名稱 技能[,技能2,...]`", color=0xff0000))
            return True
        name, skill_text = tokens[0], tokens[1]
        card = npc_card_manager.get(guild_id, name)
        if not card:
            await message.channel.send(embed=discord.Embed(title="❌ 找不到 NPC", description=name, color=0xff0000))
            return True
        skill_lookup = card.get('skills') or {}
        skill_names_req = [s.strip() for s in skill_text.split(',') if s.strip()]
        if not skill_names_req:
            await message.channel.send(embed=discord.Embed(title="❌ 請提供技能名稱", color=0xff0000))
            return True
        crit_range, fumble_range = get_effective_range(message)
        lines, missing = [], []
        for sn in skill_names_req:
            if sn in skill_lookup:
                matched_name, sv = sn, skill_lookup[sn]
            else:
                matches = fuzzy_match_skill(skill_lookup, sn)
                if len(matches) == 1:
                    matched_name, sv = matches[0]
                elif len(matches) > 1:
                    await message.channel.send(embed=discord.Embed(
                        title="🔎 找到多個符合的技能",
                        description=f"「{sn}」在「{name}」卡上符合多個：{'、'.join(m[0] for m in matches)}，請打完整名稱。",
                        color=0x00aaff,
                    ))
                    return True
                else:
                    missing.append(sn)
                    continue
            final_roll, level, bonus_desc, _ = coc_check(sv, bonus_dice, crit_range, fumble_range)
            lines.append(f"{matched_name} ({sv}%)\n{bonus_desc} → 最終擲骰 {final_roll} → **{level}**")
        if missing:
            await message.channel.send(embed=discord.Embed(title="❌ 找不到技能", description=f"「{name}」卡上沒有：{'、'.join(missing)}", color=0xff0000))
            if not lines:
                return True
        title = f"🗡️ {name} CoC 檢定"
        if bonus_dice > 0:
            title += f"（+{bonus_dice}獎勵骰）"
        elif bonus_dice < 0:
            title += f"（{-bonus_dice}懲罰骰）"
        embed = discord.Embed(title=title, description="\n\n".join(lines), color=0x00aaff)
        embed.set_footer(text=message.author.display_name, icon_url=message.author.display_avatar.url)
        await message.channel.send(embed=embed)
        return True

    await message.channel.send(embed=discord.Embed(title="❌ 未知子指令", description="可用：add, edit, del, show, list, hp, cc（可加 1/2/n1/n2 後綴）", color=0xff0000))
    return True

async def _dot_pbta(message, cmd, cmd_lower):
    """.p／.pbta PBTA 檢定。有處理回傳 True，沒輪到自己回傳 False 讓分派器往下找。"""
    if re.match(r'^(?:pbta|p)(?![a-z])', cmd_lower):
        # 修正：pbta 要切掉 4 個字元（原本 cmd[3:] 會把尾巴的 'a' 留在參數裡導致解析失敗）
        rest = cmd[4:].strip() if cmd_lower.startswith('pbta') else cmd[1:].strip()
        await handle_pbta_roll(message, rest, 'channel')
        return True
    return False

async def _dot_sc(message, cmd, cmd_lower):
    """.sc 理智檢定。有處理回傳 True，沒輪到自己回傳 False 讓分派器往下找。"""
    if re.match(r'^sc(?![a-z])', cmd_lower):
        await handle_sc_roll(message, cmd[2:].strip(), 'channel')
        return True
    return False

async def _dot_dp(message, cmd, cmd_lower):
    """.dp 成長檢定。有處理回傳 True，沒輪到自己回傳 False 讓分派器往下找。"""
    if re.match(r'^dp(?![a-z])', cmd_lower) or cmd.startswith('成長檢定') or cmd.startswith('幕間成長'):
        args = cmd[2:].strip() if cmd_lower.startswith('dp') else cmd[4:].strip()
        await development_check(message, args)
        return True
    return False

async def _dot_save(message, cmd, cmd_lower):
    """.save 團務收尾。有處理回傳 True，沒輪到自己回傳 False 讓分派器往下找。"""
    if re.match(r'^save(\s|$)', cmd, re.I):
        guild_id, channel_id, user_id = message.guild.id, message.channel.id, message.author.id

        if not is_gm(guild_id, channel_id, user_id):
            await message.channel.send(embed=discord.Embed(
                title="❌ 只有本頻道登記的 GM 才能使用",
                description="請先用 `.drgm addgm` 登記為本頻道 GM。",
                color=0xff0000,
            ))
            return True

        await message.channel.send(
            embed=discord.Embed(title="📋 團務收尾", description="按下面的按鈕，會跳出表單讓你一次填完，不會佔頻道版面。", color=0x00aaff),
            view=SaveStartView(user_id),
        )
        return True
    return False

async def _dot_drgm(message, cmd, cmd_lower):
    """.drgm GM 管理。有處理回傳 True，沒輪到自己回傳 False 讓分派器往下找。"""
    if re.match(r'^drgm(?![a-z])', cmd_lower):
        parts = cmd[4:].strip().split()
        if not parts:
            await message.channel.send(embed=discord.Embed(title="❌ 用法", description="`.drgm addgm [使用者] [化名]` / `.drgm show` / `.drgm del 編號` / `.drgm clear` / `.drgm ran ...` / `.drgm rec`\n若不指定使用者，則新增自己為本頻道的 GM。\n`.drgm rec` 開面板設定哪些頻道可以記錄成長（母頻道可複選討論串，討論串內針對自己）。", color=0xff0000))
            return True
        sub = parts[0].lower()
        guild_id = message.guild.id
        channel_id = message.channel.id

        if sub == 'addgm':
            existing_gms = gm_manager.get_gm_users(guild_id, channel_id)
            # 權限：本頻道已經有登記的 GM 時，只有本頻道的 GM 才能再新增其他 GM；
            # 本頻道還沒有任何 GM 時（開團第一次登記），開放讓任何人自行登記自己，
            # 否則永遠不會有第一位 GM 能夠登記進來。
            if existing_gms and not is_gm(guild_id, channel_id, message.author.id):
                await message.channel.send(embed=discord.Embed(title="❌ 權限不足", description="本頻道已經登記過 GM，只有本頻道的 GM 才能新增其他 GM。", color=0xff0000))
                return True

            target = None
            alias = None

            user_input = None
            if len(parts) == 1:
                target = message.author
            elif len(parts) == 2:
                user_input = parts[1]
                target = await resolve_target_by_text(message.guild, user_input)
                if target:
                    alias = None
                else:
                    target = message.author
                    alias = user_input
            else:
                user_input = parts[1]
                alias = ' '.join(parts[2:])
                target = await resolve_target_by_text(message.guild, user_input)

            if not target:
                await message.channel.send(embed=discord.Embed(title="❌ 無法識別使用者", description=f"找不到使用者：`{user_input}`", color=0xff0000))
                return True

            if target.id in existing_gms:
                await message.channel.send(embed=discord.Embed(title="⚠️ 已是本頻道的 GM", description=f"{target.display_name} 在本頻道已經是 GM 了。", color=0xffaa00))
                return True

            gm_manager.add_gm(guild_id, channel_id, target.id, alias)
            desc = f"{target.display_name} 已加入**本頻道**的 GM 名單。" + (f" 化名：{alias}" if alias else "") + "\n（登記只在這個頻道生效，其他頻道不受影響）"
            await message.channel.send(embed=discord.Embed(title="✅ 已新增本頻道 GM", description=desc, color=0x00aaff))

        elif sub == 'show':
            gms = gm_manager.get_gms(guild_id, channel_id)
            if not gms:
                await message.channel.send(embed=discord.Embed(title="📋 本頻道 GM 列表", description="本頻道目前沒有 GM。", color=0x00aaff))
            else:
                desc = "\n".join([f"{i+1}. {gm['alias']} (<@{gm['user_id']}>)" for i, gm in enumerate(gms)])
                embed = discord.Embed(title="📋 本頻道 GM 列表", description=desc, color=0x00aaff)
                await message.channel.send(embed=embed)

        elif sub == 'del':
            if not is_gm(guild_id, channel_id, message.author.id):
                await message.channel.send(embed=discord.Embed(title="❌ 權限不足", description="只有本頻道登記的 GM 可以移除 GM 登記。", color=0xff0000))
                return True
            if len(parts) < 2 or not parts[1].isdigit():
                await message.channel.send(embed=discord.Embed(title="❌ 請提供編號", description="使用 `.drgm show` 查看本頻道的編號", color=0xff0000))
                return True
            idx = int(parts[1]) - 1
            if gm_manager.remove_gm(guild_id, channel_id, idx):
                await message.channel.send(embed=discord.Embed(title="✅ 已從本頻道移除 GM", color=0x00aaff))
            else:
                await message.channel.send(embed=discord.Embed(title="❌ 編號無效", color=0xff0000))

        elif sub == 'clear':
            if not is_gm(guild_id, channel_id, message.author.id):
                await message.channel.send(embed=discord.Embed(title="❌ 權限不足", description="只有本頻道登記的 GM 可以清空本頻道的 GM 列表。", color=0xff0000))
                return True
            gm_manager.clear_gms(guild_id, channel_id)
            await message.channel.send(embed=discord.Embed(title="✅ 已清空本頻道的 GM 列表", color=0x00aaff))

        elif sub == 'ran':
            if not is_gm(guild_id, channel_id, message.author.id):
                await message.channel.send(embed=discord.Embed(title="❌ 權限不足", description="只有本頻道登記的 GM 可以設定大成功／大失敗範圍。請先用 `.drgm addgm` 登記。", color=0xff0000))
                return True

            rest_parts = parts[1:]

            if not rest_parts or rest_parts[0].lower() == 'show':
                lines = []
                my_crit, my_fumble = crit_range_manager.get_range(guild_id, message.author.id)
                if not my_crit:
                    lines.append("你（自己）的設定：目前使用預設規則")
                else:
                    crit_str = format_range(my_crit)
                    fumble_str = format_range(my_fumble)
                    lines.append(f"你（自己）的設定 大成功/大失敗：{crit_str}/{fumble_str}")

                gm_id, source = get_channel_gm(message)
                if gm_id is None:
                    gms = gm_manager.get_gms(guild_id, channel_id)
                    if not gms:
                        lines.append("本頻道：尚未登記任何 GM，套用預設規則")
                    else:
                        gm_list_str = "、".join([f"{i+1}={gm['alias']}" for i, gm in enumerate(gms)])
                        lines.append(
                            f"本頻道登記了多位 GM（{gm_list_str}），尚未指定要套用哪一位，套用預設規則\n"
                            "請用 `.drgm ran bind [編號/化名]` 指定"
                        )
                else:
                    ch_alias = get_alias(guild_id, channel_id, gm_id) or f"<@{gm_id}>"
                    ch_crit, ch_fumble = crit_range_manager.get_range(guild_id, gm_id)
                    source_label = "本頻道唯一登記" if source == 'single' else "已指定套用"
                    if not ch_crit:
                        lines.append(f"本頻道：{source_label} → GM「{ch_alias}」，但該 GM 尚未設定範圍，套用預設規則")
                    else:
                        crit_str = format_range(ch_crit)
                        fumble_str = format_range(ch_fumble)
                        lines.append(f"本頻道：{source_label} → GM「{ch_alias}」，大成功/大失敗：{crit_str}/{fumble_str}")

                await message.channel.send(embed=discord.Embed(title="📋 大成功／大失敗範圍設定", description="\n".join(lines), color=0x00aaff))
                return True

            if rest_parts[0].lower() == 'clear':
                crit_range_manager.clear_range(guild_id, message.author.id)
                await message.channel.send(embed=discord.Embed(title="✅ 已清除你自己的大成功／大失敗設定", color=0x00aaff))
                return True

            if rest_parts[0].lower() == 'bind':
                gms = gm_manager.get_gms(guild_id, channel_id)
                if not gms:
                    await message.channel.send(embed=discord.Embed(title="❌ 本頻道尚未登記任何 GM", description="請先用 `.drgm addgm` 登記。", color=0xff0000))
                    return True
                target_gm_id = None
                if len(rest_parts) < 2:
                    target_gm_id = message.author.id if message.author.id in [g['user_id'] for g in gms] else None
                else:
                    token = rest_parts[1]
                    if token.isdigit():
                        idx = int(token) - 1
                        if 0 <= idx < len(gms):
                            target_gm_id = gms[idx]['user_id']
                    else:
                        for gm in gms:
                            if gm['alias'] == token:
                                target_gm_id = gm['user_id']
                                break
                if target_gm_id is None:
                    await message.channel.send(embed=discord.Embed(title="❌ 找不到該 GM", description="請用 `.drgm show` 查看本頻道的編號或化名，例如：`.drgm ran bind 2`（只能從本頻道自己的名單裡指定）", color=0xff0000))
                    return True
                active_gm_manager.set_active(guild_id, channel_id, target_gm_id)
                alias = get_alias(guild_id, channel_id, target_gm_id) or f"<@{target_gm_id}>"
                await message.channel.send(embed=discord.Embed(title="✅ 已指定本頻道套用對象", description=f"本頻道現在套用 GM「{alias}」的大成功／大失敗設定。", color=0x00aaff))
                return True

            if rest_parts[0].lower() == 'unbind':
                if active_gm_manager.clear_active(guild_id, channel_id):
                    await message.channel.send(embed=discord.Embed(title="✅ 已解除本頻道的指定", description="本頻道恢復套用預設規則（若只剩一位登記 GM，會自動改套用他）。", color=0x00aaff))
                else:
                    await message.channel.send(embed=discord.Embed(title="⚠️ 本頻道原本就沒有指定", color=0xffaa00))
                return True

            range_text = ''.join(rest_parts)
            slash_parts = range_text.split('/')
            if len(slash_parts) != 2:
                await message.channel.send(embed=discord.Embed(
                    title="❌ 格式錯誤",
                    description="請使用：`.drgm ran 大成功/大失敗`\n例如：`.drgm ran 1/96-100`（大成功=1，大失敗=96-100）\n或：`.drgm ran 1-5/100`（大成功=1-5，大失敗=100）\n\n`.drgm ran show` 查看設定\n`.drgm ran clear` 清除自己的設定\n\n本頻道如果只登記了一位 GM，會自動套用他的設定；登記了多位時，需要用 `.drgm ran bind [編號/化名]` 指定要套用哪一位，`.drgm ran unbind` 可解除指定。",
                    color=0xff0000
                ))
                return True

            crit_range = parse_range(slash_parts[0])
            fumble_range = parse_range(slash_parts[1])
            if not crit_range or not fumble_range:
                await message.channel.send(embed=discord.Embed(title="❌ 範圍格式錯誤", description="範圍請用數字，例如 `1` 或 `96-100`", color=0xff0000))
                return True

            crit_range_manager.set_range(guild_id, message.author.id, crit_range, fumble_range)
            crit_str = format_range(crit_range)
            fumble_str = format_range(fumble_range)
            await message.channel.send(embed=discord.Embed(
                title="✅ 已更新你自己的大成功／大失敗範圍",
                description=f"大成功/大失敗：{crit_str}/{fumble_str}\n提醒：如果你在這個頻道有登記為 GM，且本頻道只有你一位登記的 GM，會自動套用；如果本頻道登記了多位，需要用 `.drgm ran bind` 指定套用你。",
                color=0x00aaff
            ))

        elif sub == 'rec':
            # 成長紀錄頻道白名單（每位 GM 各自一份）。只走面板，不再有 add/del/show/clear 文字子指令。
            # 母頻道：面板可複選「本頻道＋目前的討論串」加入／移除。
            # 討論串：面板只針對「這條討論串」加入／移出。
            # 兩者都把目前白名單直接列在面板上。存原始 channel_id（討論串各自算，不隨母頻道）。
            if not is_gm(guild_id, channel_id, message.author.id):
                await message.channel.send(embed=discord.Embed(title="❌ 權限不足", description="只有本頻道登記的 GM 可以設定成長紀錄白名單。請先用 `.drgm addgm` 登記。", color=0xff0000))
                return True
            here = message.channel
            if isinstance(here, discord.Thread):
                embed = _rec_panel_embed(guild_id, message.author.id, True, here)
                await message.channel.send(embed=embed, view=RecThreadPanelView(message.author.id, here))
            elif isinstance(here, discord.TextChannel):
                embed = _rec_panel_embed(guild_id, message.author.id, False, here)
                await message.channel.send(embed=embed, view=RecPanelView(message.author.id, here))
            else:
                # 語音文字頻道等其他型別：沒有討論串概念，就當單一頻道用面板的移除清單也能操作
                embed = _rec_panel_embed(guild_id, message.author.id, False, here)
                await message.channel.send(embed=embed, view=RecPanelView(message.author.id, here))
            return True

        else:
            await message.channel.send(embed=discord.Embed(title="❌ 未知子指令", description="可用：addgm, show, del, clear, ran, rec", color=0xff0000))
        return True
    return False

async def _dot_cmdmgr(message, cmd, cmd_lower):
    """.cmd 自訂指令管理。有處理回傳 True，沒輪到自己回傳 False 讓分派器往下找。"""
    if re.match(r'^cmd(?![a-z])', cmd_lower):
        parts = cmd[3:].strip().split(maxsplit=1)
        if not parts:
            await message.channel.send(embed=discord.Embed(title="❌ 用法", description="`.cmd add 關鍵字 回應` / `.cmd edit 關鍵字 新回應` / `.cmd del 關鍵字` / `.cmd list` / `.cmd clear`", color=0xff0000))
            return True
        sub = parts[0].lower()
        guild_id = message.guild.id
        if sub == 'add':
            if len(parts) < 2:
                await message.channel.send(embed=discord.Embed(title="❌ 請提供 關鍵字 和 回應內容", color=0xff0000))
                return True
            rest = parts[1].split(maxsplit=1)
            if len(rest) < 2:
                await message.channel.send(embed=discord.Embed(title="❌ 請提供 關鍵字 和 回應內容", color=0xff0000))
                return True
            keyword = rest[0].lower()
            response = rest[1]
            cmd_manager.add_cmd(guild_id, keyword, response)
            await message.channel.send(embed=discord.Embed(title="✅ 已新增自訂指令", description=f"`.{keyword}`", color=0x00aaff))
        elif sub == 'edit':
            if len(parts) < 2:
                await message.channel.send(embed=discord.Embed(title="❌ 請提供 關鍵字 和 新回應", color=0xff0000))
                return True
            rest = parts[1].split(maxsplit=1)
            if len(rest) < 2:
                await message.channel.send(embed=discord.Embed(title="❌ 請提供 關鍵字 和 新回應", color=0xff0000))
                return True
            keyword = rest[0].lower()
            new_response = rest[1]
            if cmd_manager.edit_cmd(guild_id, keyword, new_response):
                await message.channel.send(embed=discord.Embed(title="✅ 已編輯自訂指令", description=f"`.{keyword}`", color=0x00aaff))
            else:
                await message.channel.send(embed=discord.Embed(title="❌ 找不到該指令", color=0xff0000))
        elif sub == 'del':
            if len(parts) < 2:
                await message.channel.send(embed=discord.Embed(title="❌ 請提供關鍵字", color=0xff0000))
                return True
            keyword = parts[1].strip().lower()
            if cmd_manager.del_cmd(guild_id, keyword):
                await message.channel.send(embed=discord.Embed(title="✅ 已刪除自訂指令", description=f"`.{keyword}`", color=0x00aaff))
            else:
                await message.channel.send(embed=discord.Embed(title="❌ 找不到該指令", color=0xff0000))
        elif sub in ('show', 'list'):
            cmds = cmd_manager.list_cmds(guild_id)
            if not cmds:
                await message.channel.send(embed=discord.Embed(title="📋 自訂指令列表", description="目前沒有任何自訂指令。", color=0x00aaff))
            else:
                desc = "\n".join([f"`.{k}` → {v}" for k, v in cmds])
                embed = discord.Embed(title="📋 自訂指令列表", description=desc, color=0x00aaff)
                await message.channel.send(embed=embed)
        elif sub == 'clear':
            cmd_manager.clear_cmds(guild_id)
            await message.channel.send(embed=discord.Embed(title="✅ 已清空所有自訂指令", color=0x00aaff))
        else:
            await message.channel.send(embed=discord.Embed(title="❌ 未知子指令", description="可用：add, edit, del, show（或 list）, clear", color=0xff0000))
        return True
    return False

# ---------- 團隊檢定（.team）----------
# 流程：GM 打 .team → 成員多選挑參與者 → 被選到的人各自打自己的 .cc（各擲各的技能／數值）
#       → bot 攔截登記每個人的骰值＋成功等級 → GM 按【結算】列出全部、算骰值平均、依規則判定總結果。
# 判定規則見 judge_team_result（大成功/大失敗優先；兩極端同時出現或普通成功失敗平手 → 待 GM 抉擇）。
# 狀態純記憶體、非持久化：機器人重啟會清掉進行中的團隊檢定（跟先攻預約、瘋狂暫存一樣屬於當場短期流程）。
TEAM_CHECK_TIMEOUT = 1800  # 秒：面板與擲骰預約的存活時間（30 分鐘）

# key=(guild_id, effective_channel_id, user_id) → {'expire': ts}；某位參與者「下一次公開單一 .cc」會被登記
team_pending = {}
# key=(guild_id, effective_channel_id) → session dict（見 _team_new_session）
team_sessions = {}

def _team_new_session(gm_id, channel_id, expected_ids, check_skill='', check_difficulty=''):
    return {
        'gm_id': gm_id,
        'channel_id': channel_id,     # 原始頻道 id（討論串就是討論串本身）
        'expected': list(expected_ids),
        'entries': {},                # user_id -> {'display','skill_name','skill_value','roll','level'}
        'check_skill': check_skill,       # GM 填的技能名稱（選填，純顯示用，不強制玩家一定要打這個技能）
        'check_difficulty': check_difficulty,  # GM 填的難度（選填，純顯示用）
        'panel_channel_id': None,
        'panel_message_id': None,
        'expire': time.time() + TEAM_CHECK_TIMEOUT,
    }

_TEAM_NONCRIT_SUCCESS = {"極限成功", "困難成功", "一般成功"}
_TEAM_NONCRIT_FAIL = {"失敗"}

def judge_team_result(levels):
    """把多個成功等級合議成一個總判定。回傳 (verdict, reason)。
    verdict ∈ {'大成功','大失敗','成功','失敗','待GM抉擇'}；空清單回傳 ('待GM抉擇','沒有任何人擲骰')。
    規則：
      1. 同時出現大成功與大失敗 → 待GM抉擇
      2. 只出現大失敗（沒有大成功）→ 大失敗
      3. 只出現大成功（沒有大失敗）→ 大成功
      4. 兩種極端都沒有 → 普通成功／失敗多數決：成功多→成功，失敗多→失敗，平手→待GM抉擇
    骰值平均只作顯示，不參與勝負判定。"""
    if not levels:
        return '待GM抉擇', '沒有任何人擲骰'
    has_cs = '大成功' in levels
    has_cf = '大失敗' in levels
    if has_cs and has_cf:
        return '待GM抉擇', '同時出現大成功與大失敗，交給 GM 裁定'
    if has_cf:
        return '大失敗', '出現大失敗'
    if has_cs:
        return '大成功', '出現大成功'
    succ = sum(1 for lv in levels if lv in _TEAM_NONCRIT_SUCCESS)
    fail = sum(1 for lv in levels if lv in _TEAM_NONCRIT_FAIL)
    if succ > fail:
        return '成功', f'成功 {succ} 人 ＞ 失敗 {fail} 人，多數成功'
    if fail > succ:
        return '失敗', f'失敗 {fail} 人 ＞ 成功 {succ} 人，多數失敗'
    return '待GM抉擇', f'成功 {succ} 人 ＝ 失敗 {fail} 人，平手交給 GM 裁定'

_TEAM_VERDICT_COLOR = {
    '大成功': 0x00aa00, '成功': 0x00aa00,
    '失敗': 0xaa0000, '大失敗': 0xaa0000,
    '待GM抉擇': 0xffaa00,
}

def _team_entry_line(e):
    if e['skill_name']:
        head = f"{e['skill_name']}（{e['skill_value']}%）"
    else:
        head = f"技能值 {e['skill_value']}"
    return f"• {e['display']}：{head} 擲出 **{e['roll']}** → **{e['level']}**"

def _team_check_header(session):
    """把 GM 填的技能名稱／難度組成一行提示字串；兩者都沒填就回傳空字串。"""
    skill = (session.get('check_skill') or '').strip()
    diff = (session.get('check_difficulty') or '').strip()
    if not skill and not diff:
        return ''
    parts = []
    if skill:
        parts.append(f"技能：**{skill}**")
    if diff:
        parts.append(f"難度：**{diff}**")
    return "📋 " + "　".join(parts) + "\n\n"

def build_team_status_embed(session, guild):
    """進行中的團隊檢定面板：列出已擲／未擲名單。"""
    entries = session['entries']
    rolled = [_team_entry_line(entries[uid]) for uid in session['expected'] if uid in entries]
    pending_names = []
    for uid in session['expected']:
        if uid in entries:
            continue
        m = guild.get_member(uid) if guild else None
        pending_names.append(m.mention if m else f"<@{uid}>")
    desc = _team_check_header(session)
    desc += (
        "被選到的人請各自打自己的 `.cc`（例如 `.cc 偵查` 或 `.cc 50`），系統會自動登記你的骰值與成功等級。\n"
        "（暗骰、帶獎勵／懲罰骰、一次多個技能的檢定不會被登記，請打單一的公開檢定。）\n\n"
    )
    desc += "**已擲骰：**\n" + ("\n".join(rolled) if rolled else "（還沒有人擲）") + "\n\n"
    desc += "**尚未擲骰：**\n" + ("、".join(pending_names) if pending_names else "（全員到齊！GM 可按【結算】）")
    return discord.Embed(title="👥 團隊檢定進行中", description=desc, color=0x00aaff)

def build_team_settlement_embed(session):
    entries = session['entries']
    order = [uid for uid in session['expected'] if uid in entries]
    order += [uid for uid in entries if uid not in session['expected']]  # 防呆，理論上不會有
    levels = [entries[uid]['level'] for uid in order]
    verdict, reason = judge_team_result(levels)
    lines = [_team_entry_line(entries[uid]) for uid in order]
    rolls = [entries[uid]['roll'] for uid in order]
    avg = round(sum(rolls) / len(rolls), 1) if rolls else 0
    missing = [uid for uid in session['expected'] if uid not in entries]
    desc = _team_check_header(session)
    desc += "\n".join(lines) if lines else "（沒有任何人擲骰）"
    desc += f"\n\n🎲 骰值平均：**{avg}**（僅供參考，不影響判定）"
    desc += f"\n\n🏁 團隊檢定總判定：**{verdict}**\n（{reason}）"
    if missing:
        miss = "、".join(f"<@{uid}>" for uid in missing)
        desc += f"\n\n⚠️ 尚有未擲骰：{miss}（未計入判定）"
    return discord.Embed(title="👥 團隊檢定結算", description=desc, color=_TEAM_VERDICT_COLOR.get(verdict, 0x00aaff))

async def _team_update_panel(guild, session):
    """把面板訊息 edit 成最新的已擲／未擲名單；訊息不在了就靜默略過。"""
    ch_id = session.get('panel_channel_id')
    msg_id = session.get('panel_message_id')
    if not ch_id or not msg_id:
        return
    ch = bot.get_channel(ch_id)
    if ch is None:
        return
    try:
        msg = await ch.fetch_message(msg_id)
        await msg.edit(embed=build_team_status_embed(session, guild), view=TeamCheckPanelView())
    except (discord.NotFound, discord.Forbidden, discord.HTTPException):
        pass

async def maybe_capture_team_roll(message, target_type, skill_name, skill_value, roll_value, level):
    """若發話者是某場進行中團隊檢定的參與者、且還沒登記過，就把這次 .cc 檢定的骰值＋等級登記進去。
    只吃公開檢定（暗骰不算）與帶成功等級的檢定；有登記成功時回傳可接在擲骰結果後的提示字串，
    並順手更新面板，否則回傳 None。呼叫端只在單一、不帶獎懲骰的檢定時才會呼叫（與先攻攔截同一個閘門）。"""
    if target_type != 'channel' or roll_value is None or level is None:
        return None
    guild_id, channel_id, user_id = message.guild.id, message.channel.id, message.author.id
    eff = effective_channel_id(channel_id)
    pending_key = (guild_id, eff, user_id)
    pending = team_pending.get(pending_key)
    if not pending or pending['expire'] < time.time():
        team_pending.pop(pending_key, None)
        return None
    session = team_sessions.get((guild_id, eff))
    if not session or session['expire'] < time.time() or user_id not in session['expected']:
        team_pending.pop(pending_key, None)
        return None
    # 只登記第一次擲骰（跟先攻一致）；登記後就從預約名單移除，之後的 .cc 不再被吃。
    team_pending.pop(pending_key, None)
    session['entries'][user_id] = {
        'display': message.author.display_name,
        'skill_name': skill_name or '',
        'skill_value': skill_value,
        'roll': roll_value,
        'level': level,
    }
    remaining = [uid for uid in session['expected'] if uid not in session['entries']]
    await _team_update_panel(message.guild, session)
    sk = skill_name or f"技能值 {skill_value}"
    note = f"\n\n👥 已登記你的團隊檢定：{sk} 擲出 {roll_value} → {level}"
    note += "（全員到齊，GM 可按【結算】）" if not remaining else f"（還有 {len(remaining)} 人未擲）"
    return note

class TeamCheckSkillDifficultyModal(discord.ui.Modal, title="👥 團隊檢定設定"):
    """成員選好之後跳出的表單：GM 填這次團隊檢定要用的技能名稱／難度（兩者都選填，純顯示用，
    不會強制玩家一定要打這個技能——玩家仍各自打自己的 .cc，有角色卡就抓卡上數值，沒有就手動打數字）。"""
    skill_input = discord.ui.TextInput(
        label="技能名稱（選填）", placeholder="例如 偵查、聆聽（留空則不顯示）",
        required=False, max_length=30,
    )
    difficulty_input = discord.ui.TextInput(
        label="難度（選填）", placeholder="例如 一般／困難／極限（留空則不顯示）",
        required=False, max_length=10,
    )

    def __init__(self, member_ids, setup_message):
        super().__init__()
        self.member_ids = member_ids       # 被選中的參與者 id 清單
        self.setup_message = setup_message  # 原本那則選人面板訊息，送出後要把它換成進行中面板

    async def on_submit(self, interaction: discord.Interaction):
        guild_id, channel_id, user_id = interaction.guild.id, interaction.channel.id, interaction.user.id
        if not is_gm(guild_id, channel_id, user_id):
            await interaction.response.send_message("只有本頻道登記的 GM 才能發起團隊檢定。", ephemeral=True)
            return
        eff = effective_channel_id(channel_id)
        skill = str(self.skill_input.value).strip()
        difficulty = str(self.difficulty_input.value).strip()
        session = _team_new_session(user_id, channel_id, self.member_ids, check_skill=skill, check_difficulty=difficulty)
        team_sessions[(guild_id, eff)] = session
        expire = session['expire']
        for mid in self.member_ids:
            team_pending[(guild_id, eff, mid)] = {'expire': expire}
        embed = build_team_status_embed(session, interaction.guild)
        try:
            await self.setup_message.edit(embed=embed, view=TeamCheckPanelView())
            session['panel_channel_id'] = self.setup_message.channel.id
            session['panel_message_id'] = self.setup_message.id
        except (discord.HTTPException, discord.NotFound):
            pass
        await interaction.response.send_message("✅ 團隊檢定已開始，請通知參與者各自打 `.cc`。", ephemeral=True)

class TeamCheckMemberSelect(discord.ui.UserSelect):
    """GM 挑選要參與團隊檢定的人（可多選）。每次點擊都重新驗 GM 身分。"""
    def __init__(self):
        super().__init__(placeholder="選擇要參與團隊檢定的人（可多選）…", min_values=1, max_values=25)

    async def callback(self, interaction: discord.Interaction):
        guild_id, channel_id, user_id = interaction.guild.id, interaction.channel.id, interaction.user.id
        if not is_gm(guild_id, channel_id, user_id):
            await interaction.response.send_message("只有本頻道登記的 GM 才能發起團隊檢定。", ephemeral=True)
            return
        members = [u for u in self.values if not u.bot]
        if not members:
            await interaction.response.send_message("請至少選一位（非機器人）玩家。", ephemeral=True)
            return
        await interaction.response.send_modal(
            TeamCheckSkillDifficultyModal([m.id for m in members], interaction.message)
        )

class TeamCheckSetupView(discord.ui.View):
    def __init__(self):
        super().__init__(timeout=TEAM_CHECK_TIMEOUT)
        self.add_item(TeamCheckMemberSelect())

class TeamCheckPanelView(discord.ui.View):
    """進行中團隊檢定的操作面板：GM 按【結算】做總判定，或【取消】終止。非 persistent（逾時作廢）。"""
    def __init__(self):
        super().__init__(timeout=TEAM_CHECK_TIMEOUT)

    async def _get_session(self, interaction):
        guild_id, channel_id = interaction.guild.id, interaction.channel.id
        eff = effective_channel_id(channel_id)
        session = team_sessions.get((guild_id, eff))
        if not session or session['expire'] < time.time():
            team_sessions.pop((guild_id, eff), None)
            await interaction.response.send_message("這場團隊檢定已經結束或逾時了，請重新 `.team`。", ephemeral=True)
            return None, eff
        if not is_gm(guild_id, channel_id, interaction.user.id):
            await interaction.response.send_message("只有本頻道登記的 GM 才能操作團隊檢定面板。", ephemeral=True)
            return None, eff
        return session, eff

    @discord.ui.button(label="📊 結算", style=discord.ButtonStyle.primary)
    async def settle_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        session, eff = await self._get_session(interaction)
        if session is None:
            return
        if not session['entries']:
            await interaction.response.send_message("目前還沒有任何人擲骰，沒得結算。等大家打完 `.cc` 再按。", ephemeral=True)
            return
        embed = build_team_settlement_embed(session)
        guild_id = interaction.guild.id
        for uid in session['expected']:
            team_pending.pop((guild_id, eff, uid), None)
        team_sessions.pop((guild_id, eff), None)
        await interaction.response.edit_message(embed=embed, view=None)

    @discord.ui.button(label="🗑️ 取消", style=discord.ButtonStyle.secondary)
    async def cancel_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        session, eff = await self._get_session(interaction)
        if session is None:
            return
        guild_id = interaction.guild.id
        for uid in session['expected']:
            team_pending.pop((guild_id, eff, uid), None)
        team_sessions.pop((guild_id, eff), None)
        await interaction.response.edit_message(
            embed=discord.Embed(title="👥 團隊檢定已取消", description="這場團隊檢定已由 GM 取消。", color=0x999999),
            view=None,
        )

async def _dot_team(message, cmd, cmd_lower):
    """.team 團隊檢定（GM 專用）：叫出成員多選面板，被選到的人各自打 .cc，GM 按【結算】做總判定。
    有處理回傳 True，沒輪到自己回傳 False 讓分派器往下找。"""
    if not re.match(r'^team(?![a-z])', cmd_lower):
        return False
    guild_id, channel_id, user_id = message.guild.id, message.channel.id, message.author.id
    if not is_gm(guild_id, channel_id, user_id):
        await message.channel.send(embed=discord.Embed(
            title="❌ 只有 GM 能發起團隊檢定",
            description="`.team` 只有本頻道登記的 GM 能使用。請先用 `.drgm addgm` 登記 GM。",
            color=0xff0000,
        ))
        return True
    eff = effective_channel_id(channel_id)
    existing = team_sessions.get((guild_id, eff))
    if existing and existing['expire'] >= time.time():
        await message.channel.send(embed=discord.Embed(
            title="⚠️ 本頻道已有進行中的團隊檢定",
            description="請先用面板上的【結算】或【取消】結束目前這場，再開新的。",
            color=0xffaa00,
        ))
        return True
    embed = discord.Embed(
        title="👥 團隊檢定",
        description=(
            "選擇要參與這場團隊檢定的人（可多選）。選好之後會跳出視窗讓你填這次要用的技能名稱／難度"
            "（兩者都選填，純顯示用）。接著被選到的人各自打自己的 `.cc`（有角色卡就直接 `.cc 技能名稱` 抓卡上數值，"
            "沒有角色卡打數字也行，例如 `.cc 50`），系統會自動登記骰值與成功等級，GM 再按【結算】做總判定。\n\n"
            "**總判定規則**：出現大成功／大失敗優先（兩者同時出現 → 待 GM 抉擇）；"
            "都沒有極端時，看普通成功與失敗的人數多數決，平手也交給 GM 抉擇。"
        ),
        color=0x00aaff,
    )
    await message.channel.send(embed=embed, view=TeamCheckSetupView())
    return True

# 依判斷順序排列的 . 指令路由表；順序有意義（例如 .data/.pc 要在 .p 之前，
# 免得被 PBTA 的 p 前綴吃掉），新增指令時插在對的位置即可。
_DOT_COMMAND_HANDLERS = (
    _dot_help,
    _dot_init,
    _dot_pass,
    _dot_chase,
    _dot_start,
    _dot_end,
    _dot_rts,
    _dot_multi,
    _dot_int,
    _dot_calc,
    _dot_cc,
    _dot_melee,
    _dot_team,
    _dot_data,
    _dot_quick_stat,
    _dot_pc,
    _dot_npc,
    _dot_pbta,
    _dot_sc,
    _dot_dp,
    _dot_save,
    _dot_drgm,
    _dot_cmdmgr,
)

async def handle_dot_command(message, cmd):
    # cmd_lower 只用來判斷「打的是哪個指令」，不分大小寫；cmd 本身維持原始大小寫，
    # 是因為後面切字串取參數（角色名稱、備註文字等）不該被強制轉小寫。
    cmd_lower = cmd.lower()
    for handler in _DOT_COMMAND_HANDLERS:
        if await handler(message, cmd, cmd_lower):
            return True

    # 全部沒接手 → 最後查伺服器自訂指令（.cmd add 建立的關鍵字）
    if cmd in cmd_manager.data.get(message.guild.id, {}):
        response = cmd_manager.get_cmd(message.guild.id, cmd)
        if response:
            await message.channel.send(response)
            return True

    return True

# ---------- 說明選單 ----------
# key -> (顯示名稱, 詳細內容)；.help 會列成下拉選單，選了哪個分類才顯示哪個分類的內容
# ---------- 說明選單 .help ----------
# 說明文案不寫在程式裡，而是放在 help.md 這一個檔案，開機時讀進來。
# 要改說明只要改那個檔案，不用動這支程式。格式：
#
#     （檔案開頭、第一個 ## 之前的內容會被忽略，可以拿來寫給自己看的筆記）
#
#     ## 🎲 我要擲骰            ← 以 ## 開頭的一行 = 一個分類，這行文字就是選單標籤
#
#     這裡是第一層內容          ← 選單點下去直接看到，只放九成情況會用到的操作
#
#     --- 更多 ---              ← 這行是分隔線，有寫才會出現【更多】按鈕
#
#     這裡是「更多」的內容      ← 邊角規則與細部行為
#
#     ## ⚔️ 戰鬥                ← 下一個分類
#     ...
#
# 分類順序就是檔案裡的順序；`.help` 預設顯示第一個分類。
# 新增／刪除／重新排序分類都只要改這個檔案，程式不用改。
HELP_FILE = os.getenv('DICE_BOT_HELP_FILE', 'help.md')
HELP_SECTION_RE = re.compile(r'^##[ \t]+(.+?)[ \t]*$', re.M)
HELP_MORE_SEPARATOR = '--- 更多 ---'
HELP_EMBED_LIMIT = 4000   # Discord embed description 上限 4096，留一點給程式碼區塊的符號

HELP_SECTIONS = {}        # label -> (第一層內容, 更多內容或 None)；順序即檔案順序（dict 保序）
HELP_LOAD_ERROR = None    # 讀檔失敗或有警告時的說明字串，`.help` 會顯示出來


def _split_help_layers(body):
    """把一個分類的內容切成 (第一層, 更多或 None)。"""
    body = body.strip('\n')
    if HELP_MORE_SEPARATOR in body:
        first, more = body.split(HELP_MORE_SEPARATOR, 1)
        more = more.strip('\n')
        return first.strip('\n'), (more or None)
    return body, None


def parse_help_document(text):
    """把整份 help.md 切成 {標籤: (第一層, 更多)}，回傳 (sections, 警告列表)。"""
    text = text.replace('\r\n', '\n')
    matches = list(HELP_SECTION_RE.finditer(text))
    sections, warnings = {}, []
    for idx, m in enumerate(matches):
        label = m.group(1).strip()
        body_end = matches[idx + 1].start() if idx + 1 < len(matches) else len(text)
        content, more = _split_help_layers(text[m.end():body_end])
        if not content.strip():
            warnings.append(f"分類「{label}」沒有內容，已略過。")
            continue
        if label in sections:
            warnings.append(f"分類「{label}」重複出現，只會保留最後一個。")
        for layer_name, layer in (("第一層", content), ("更多", more)):
            if layer and len(layer) > HELP_EMBED_LIMIT:
                warnings.append(f"分類「{label}」的{layer_name}超過 {HELP_EMBED_LIMIT} 字，顯示時會被截斷。")
        sections[label] = (content, more)
    return sections, warnings


def reload_help_sections():
    """重新讀取 help.md。回傳 (載入的分類數, 錯誤或警告訊息或 None)。
    on_ready 會呼叫一次，`.help reload` 也會呼叫——改完文案不用重開機器人。
    讀檔失敗時不讓 bot 掛掉，只把問題記在 HELP_LOAD_ERROR 讓 `.help` 顯示出來。"""
    global HELP_SECTIONS, HELP_LOAD_ERROR
    try:
        with open(HELP_FILE, 'r', encoding='utf-8') as f:
            text = f.read()
    except FileNotFoundError:
        HELP_SECTIONS, HELP_LOAD_ERROR = {}, (
            f"找不到說明檔 `{HELP_FILE}`。\n"
            f"請把它放在 `dice_bot.py` 旁邊，再用 `.help reload` 重新載入。"
        )
        return 0, HELP_LOAD_ERROR
    except Exception as e:
        HELP_SECTIONS, HELP_LOAD_ERROR = {}, f"讀取 `{HELP_FILE}` 失敗：{e}"
        return 0, HELP_LOAD_ERROR

    sections, warnings = parse_help_document(text)
    HELP_SECTIONS = sections
    if not sections:
        HELP_LOAD_ERROR = (
            f"`{HELP_FILE}` 裡沒有找到任何分類。\n"
            f"每個分類要以 `## 分類名稱` 這樣的一行開頭。"
        )
    else:
        HELP_LOAD_ERROR = "\n".join(warnings) if warnings else None
    return len(sections), HELP_LOAD_ERROR


def help_default_key():
    """`.help` 預設顯示的分類＝檔案裡的第一個分類。"""
    return next(iter(HELP_SECTIONS), None)


def _help_clip(text):
    """手改文案可能不小心寫太長，這裡確保不會超過 Discord 上限而整則訊息發不出去。"""
    if len(text) <= HELP_EMBED_LIMIT:
        return text
    return text[:HELP_EMBED_LIMIT - 20].rstrip() + "\n…（內容過長，已截斷）"


def _help_page_lookup(embed):
    """從 embed 標題反推現在顯示的是哪一個分類、是不是「更多」那一層。
    HelpView 是 persistent view，同一個註冊實例要服務所有訊息，
    所以「目前在哪一頁」不能存在 view 實例裡，改成每次從畫面上讀回來。"""
    raw_title = embed.title or ""
    label = raw_title.replace("（更多）", "").strip()
    if label in HELP_SECTIONS:
        return label, "（更多）" in raw_title
    return help_default_key(), False


def render_help(label, more=False):
    """回傳 (embed, view)。內容用程式碼區塊包起來，讓文案裡的對齊排版不會被 Markdown 吃掉。"""
    if not HELP_SECTIONS:
        embed = discord.Embed(
            title="⚠️ 說明檔尚未載入",
            description=HELP_LOAD_ERROR or "說明內容目前是空的。",
            color=0xffaa00,
        )
        return embed, None
    if label not in HELP_SECTIONS:
        label = help_default_key()
    content, more_content = HELP_SECTIONS[label]
    if more and more_content:
        embed = discord.Embed(title=f"{label}（更多）", description=f"```\n{_help_clip(more_content)}\n```", color=0x00aaff)
        return embed, HelpView(more_enabled=True, more_label="◂ 返回")
    embed = discord.Embed(title=label, description=f"```\n{_help_clip(content)}\n```", color=0x00aaff)
    return embed, HelpView(more_enabled=bool(more_content))


class HelpSelect(discord.ui.Select):
    """分類選單。選項來自 help.md 裡的 `## 分類名稱`，所以多寫一個分類就多一個選項。
    選項的 value 直接用分類名稱，這樣重新排序檔案內容時，已經發出去的舊選單也不會指錯頁。"""
    def __init__(self):
        options = [
            discord.SelectOption(label=label[:100], value=label[:100])
            for label in HELP_SECTIONS
        ] or [discord.SelectOption(label="（尚未載入說明檔）", value="__none__")]
        super().__init__(placeholder="選擇想看的說明分類…", options=options[:25], min_values=1, max_values=1, custom_id="help:section")

    async def callback(self, interaction: discord.Interaction):
        embed, view = render_help(self.values[0])
        embed.set_footer(text=interaction.user.display_name, icon_url=interaction.user.display_avatar.url)
        await interaction.response.edit_message(embed=embed, view=view)


class HelpMoreButton(discord.ui.Button):
    """在「第一層」與「更多」之間切換。沒有寫 `--- 更多 ---` 的分類會被送成停用狀態。"""
    def __init__(self, label="▸ 更多"):
        super().__init__(label=label, style=discord.ButtonStyle.secondary, custom_id="help:more")

    async def callback(self, interaction: discord.Interaction):
        if interaction.message.embeds:
            key, showing_more = _help_page_lookup(interaction.message.embeds[0])
        else:
            key, showing_more = help_default_key(), False
        embed, view = render_help(key, more=not showing_more)
        embed.set_footer(text=interaction.user.display_name, icon_url=interaction.user.display_avatar.url)
        await interaction.response.edit_message(embed=embed, view=view)


class HelpView(discord.ui.View):
    """說明選單。persistent view（timeout=None＋固定 custom_id，並在 on_ready 註冊）：
    不會讀到一半失效，bot 重啟後舊訊息的選單也還能用。
    說明內容人人可看，所以不做「只有叫出來的人能操作」的限制。
    注意：`.help reload` 之後才發出的訊息才會用到新的分類清單；已經發在頻道裡的舊訊息
    選單選項是當時產生的，重新輸入 `.help` 即可拿到最新版。"""
    def __init__(self, more_enabled=True, more_label="▸ 更多"):
        super().__init__(timeout=None)
        self.add_item(HelpSelect())
        button = HelpMoreButton(more_label)
        button.disabled = not more_enabled
        self.add_item(button)


async def send_help_embed(message):
    """`.help` 直接顯示第一個分類（快速上手），不再先送一則「請從下面的選單選擇分類」的空白提示——
    使用者打開說明時想的是「我要做某件事」，第一眼就該看到可以照著做的步驟。"""
    embed, view = render_help(help_default_key())
    embed.set_footer(text=message.author.display_name, icon_url=message.author.display_avatar.url)
    await message.channel.send(embed=embed, view=view)


def is_valid_table_name(name: str) -> bool:
    """檢查抽籤表名稱是否有效：至少一個字元，且只包含字母、數字、底線或中文字"""
    if not name:
        return False
    # 允許英文大小寫、數字、底線、中文字符（Unicode 範圍 \u4e00-\u9fff）
    return bool(re.fullmatch(r'[\w\u4e00-\u9fff]+', name))

@bot.event
async def on_ready():
    # 註冊 persistent view：`.init` 面板的按鈕永不失效，連 bot 重啟前發出的舊面板都能繼續按
    # （on_ready 可能因斷線重連被觸發多次，用旗標確保只註冊一次）
    if not getattr(bot, '_init_panel_view_registered', False):
        bot.add_view(InitPanelView())
        bot._init_panel_view_registered = True
    # 同上，`.chase` 追逐面板也是 persistent view，一併註冊
    if not getattr(bot, '_chase_panel_view_registered', False):
        bot.add_view(ChasePanelView())
        bot._chase_panel_view_registered = True
    # 同上，`.melee` 戰技面板也是 persistent view，一併註冊
    if not getattr(bot, '_melee_panel_view_registered', False):
        bot.add_view(MeleePanelView())
        bot._melee_panel_view_registered = True
    # 同上，`.pc` 角色卡主面板也是 persistent view，一併註冊
    if not getattr(bot, '_pc_panel_view_registered', False):
        bot.add_view(PCMainPanelView())
        bot._pc_panel_view_registered = True
    # 對抗判定的【反擊】【閃避】【自訂】按鈕同樣是 persistent view：註冊之後，
    # bot 重啟前發出的舊對抗訊息也還能按下去結算（狀態存在 melee_pending_store）。
    # 文字版的 `.反擊`／`.閃避` 已移除，按鈕是唯一的回應方式，所以這兩個註冊不能漏。
    if not getattr(bot, '_melee_defense_views_registered', False):
        bot.add_view(MeleeResponseView())
        bot.add_view(CCOpposedView())
        bot._melee_defense_views_registered = True
    # 說明文案放在 help.md，開機時讀進來；要註冊 HelpView 之前一定要先載入，
    # 因為選單選項是照載入結果產生的。
    count, problem = reload_help_sections()
    print(f"📖 已載入 {count} 個說明分類" + (f"（{problem}）" if problem else ""))
    if not getattr(bot, '_help_view_registered', False):
        bot.add_view(HelpView())
        bot._help_view_registered = True
    print(f'✅ 已登入：{bot.user}')

@bot.event
async def on_message(message):
    if message.author.bot:
        return
    content = message.content.strip()

    # 角色卡等待貼上狀態：.pc set 之後，同頻道同一人下一則「非指令」訊息會被當成角色卡文字解析，
    # 可以直接貼文字，也可以改附加 .txt／.json 檔案（有附件時優先吃附件內容，忽略訊息文字本身）。
    # 純附件、沒有文字的訊息 content 會是空字串，所以這段要放在「content 是空字串就 return」之前處理。
    if message.guild:
        pending_key = (message.guild.id, message.channel.id, message.author.id)
        pending = pc_pending.get(pending_key)
        if pending:
            if time.time() >= pending['expire']:
                del pc_pending[pending_key]
            elif message.attachments or (content and not content.startswith('.') and not content.startswith('!')):
                raw_card_text = None
                if message.attachments:
                    raw_card_text, attach_error = await read_pc_attachment_text(message.attachments[0])
                    if attach_error:
                        del pc_pending[pending_key]
                        await message.channel.send(embed=discord.Embed(title="❌ 無法讀取檔案", description=attach_error, color=0xff0000))
                        return
                else:
                    raw_card_text = content
                del pc_pending[pending_key]
                # 這則貼上的角色卡原文含完整數值，屬於單人行動，刪掉頻道裡的公開訊息，
                # 只留下之後由 handle_pc_paste／save_new_pc_card 產生的按鈕存根＋ephemeral 預覽（本人才看得到）。
                try:
                    await message.delete()
                except (discord.Forbidden, discord.NotFound, discord.HTTPException):
                    pass
                target_message = message
                owner_id = pending.get('owner_id')
                if owner_id and owner_id != message.author.id:
                    owner_member = message.guild.get_member(owner_id) or message.author
                    target_message = _MessageOwnerShim(message, owner_member)
                await handle_pc_paste(target_message, raw_card_text, pending.get('alias'))
                return

    if not content:
        return

    # 私訊（DM）沒有 guild，後續大量功能都依賴 message.guild.id，直接忽略避免崩潰
    if message.guild is None:
        return

    # 把「xdy+db」換成本頻道啟用角色卡的 DB 值（.calc 指令不支援這個功能）
    if not re.match(r'^\.calc\b', content, re.I):
        substituted, db_error = substitute_db_token(content, message)
        if db_error:
            await message.channel.send(embed=discord.Embed(title="❌ 無法代入 DB", description=db_error, color=0xff0000))
            return
        content = substituted

    clean_content = remove_discord_emoji(content)

    # 抽籤表功能：!名稱（只允許有效名稱）
    if clean_content.startswith('!'):
        table_name = clean_content[1:].strip()
        if is_valid_table_name(table_name):
            items = table_manager.get_table(message.guild.id, table_name)
            if items:
                idx = random.randint(0, len(items)-1)
                embed = discord.Embed(title="🎲", description=f"**{items[idx]}**", color=0x00aaff)
                embed.set_footer(text=f"#{idx+1} | {message.author.display_name}", icon_url=message.author.display_avatar.url)
                await message.channel.send(embed=embed)
            else:
                await message.channel.send(embed=discord.Embed(title="❌", description=f"沒有 `{table_name}` 抽籤表", color=0xff0000))
        # 無效名稱則完全忽略（不回應）
        return

    lower_content = clean_content.lower()
    if lower_content == 'help':
        await send_help_embed(message)
        return

    if lower_content.startswith('dddr '):
        expr = content[5:].strip()
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

    cc_match = re.match(r'^(cc(?:[12]?|n[12]?)?)(?:\s+(.*))?$', clean_content, re.I)
    if cc_match:
        cmd_part = cc_match.group(1).lower()
        args = cc_match.group(2) or ""
        fake_cmd = f".{cmd_part} {args}".strip()
        await handle_dot_command(message, fake_cmd[1:])
        return

    p_match = re.match(r'^\.p(?:\s+(2d6[+-]?\d*)?(?:\s+(.*))?)?$', clean_content, re.I)
    if p_match:
        dice_part = p_match.group(1) if p_match.group(1) else "2d6"
        move_name = p_match.group(2) if p_match.group(2) else ""
        await handle_pbta_roll(message, f"{dice_part} {move_name}".strip(), 'channel')
        return

    if content.startswith('.'):
        if re.match(r'^\.\s*\w', content):
            cmd = content[1:].strip()
            await handle_dot_command(message, cmd)
            return
        return

    if re.search(r'https?://', clean_content):
        return

    if not looks_like_dice_or_math(clean_content):
        await bot.process_commands(message)
        return

    # 拆分骰子指令與說明文字（如 "1d6 忠誠" → dice_part="1d6", label="忠誠"）
    dice_part, label = split_dice_and_label(clean_content)

    dice_res = parse_dice_expression(dice_part)
    if dice_res is not None:
        dice_res.text = label if label else None
        content = dice_res.format()
        init_note = maybe_capture_init_roll(message, 'channel', dice_res.total)
        if init_note:
            content += init_note
        await send_result(message, content, title="🎲 擲骰結果", target_type='channel')
        return

    multi = parse_multi_dice(dice_part)
    if multi:
        total, details = multi
        header = f"{dice_part}： {label}" if label else dice_part
        content = f"{header}\n{details}"
        init_note = maybe_capture_init_roll(message, 'channel', total)
        if init_note:
            content += init_note
        await send_result(message, content, title="🎲 多重骰組相加", target_type='channel')
        return

    dice_pattern = re.compile(r'^([0-9]+[DBU][0-9]+[Ss]?(?:\s+[0-9]+)?|D66[sn]?)', re.I)
    match = dice_pattern.match(dice_part)
    if match:
        inner_dice = match.group(1)
        dice_res = parse_dice_expression(inner_dice)
        if dice_res:
            dice_res.text = label if label else None
            content = dice_res.format()
            init_note = maybe_capture_init_roll(message, 'channel', dice_res.total)
            if init_note:
                content += init_note
            await send_result(message, content, title="🎲 擲骰結果", target_type='channel')
        else:
            await message.channel.send(embed=discord.Embed(title="❌ 無法解析骰子指令", description=inner_dice, color=0xff0000))
        return

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