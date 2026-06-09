#!/usr/bin/env python3
"""
netkeiba.com レース結果スクレイパー + 学習適応仮説判定
使い方: python3 netkeiba_scraper.py race_id [race_id ...]
例:     python3 netkeiba_scraper.py 202509030111 202509030112

学習適応仮説フラグ条件（前走ベース）
  条件1: 前走のコーナー通過順位が途中で下がった（後退あり）
  条件2: 前走の上がり3Fが前走メンバー内3位以内
"""

import argparse
import csv
import re
import sys
import time
import concurrent.futures
from datetime import datetime
from typing import Dict, List, Optional

import requests
from bs4 import BeautifulSoup

HEADERS = {
    "User-Agent": "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
                  "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36",
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
    "Accept-Language": "ja,en-US;q=0.9,en;q=0.8",
    "Accept-Encoding": "gzip, deflate, br",
}

def _make_session() -> requests.Session:
    """netkeiba.com でクッキーを取得してセッションを確立"""
    s = requests.Session()
    s.headers.update(HEADERS)
    try:
        s.get("https://www.netkeiba.com/", timeout=10)
    except Exception:
        pass
    return s

_SESSION = _make_session()

# 場名 → 場コード
VENUE_NAMES: Dict[str, str] = {
    "sapporo":  "01", "hakodate": "02", "fukushima": "03",
    "niigata":  "04", "nakayama": "05", "tokyo":     "06",
    "chukyo":   "07", "kyoto":    "08", "hanshin":   "09",
    "kokura":   "10",
}


# ── HTTP / パース ────────────────────────────────────────────

_REQUEST_INTERVAL = 2.0  # リクエスト間の最小待機秒数（クラス変数として上書き可）

def get_soup(url: str) -> Optional[BeautifulSoup]:
    time.sleep(_REQUEST_INTERVAL)
    try:
        resp = _SESSION.get(url, headers={"Referer": "https://db.netkeiba.com/"}, timeout=20)
        if resp.status_code != 200:
            return None
        resp.encoding = "euc-jp"
        return BeautifulSoup(resp.text, "html.parser")
    except requests.RequestException as e:
        print(f"[WARN] fetch failed: {url}  ({e})", file=sys.stderr)
        return None


def build_col_map(table) -> dict:
    """テーブルのヘッダー行からカラム名→インデックスマップを作成"""
    header_row = table.find("tr", class_="txt_c") or table.find("tr")
    return {
        th.get_text(separator="", strip=True): i
        for i, th in enumerate(header_row.find_all("th"))
    }


def cell_text(tds: list, idx: int) -> str:
    if idx < 0 or idx >= len(tds):
        return ""
    td = tds[idx]
    for el in [td.find("span"), td.find("a")]:
        if el:
            return el.get_text(strip=True)
    return td.get_text(strip=True)


def _extract_race_surface(soup) -> str:
    """Extract race surface (芝/ダート/障害) from db.netkeiba race page."""
    for cls_name in ["data_intro", "racedata", "race_data", "race-data"]:
        el = soup.find(class_=cls_name)
        if el:
            t = el.get_text(" ", strip=True)
            if "障害" in t:
                return "障害"
            if re.search(r"芝\s*[右左直]?\s*\d{3,4}", t):
                return "芝"
            if "ダート" in t:
                return "ダート"
    page_text = soup.get_text(" ", strip=True)
    m = re.search(r"(障害|芝|ダート)\s*[右左直]?\s*\d{3,4}\s*m", page_text[:5000])
    if m:
        return m.group(1)
    return ""


def parse_fukusho_payouts(soup) -> Dict[str, int]:
    """払い戻しテーブルから 複勝 {馬番: 配当(円)} を返す"""
    payouts: Dict[str, int] = {}
    for tbl in soup.find_all("table", class_="pay_table_01"):
        for tr in tbl.find_all("tr"):
            th = tr.find("th")
            if th and "複勝" in th.get_text():
                tds = tr.find_all("td")
                if len(tds) >= 2:
                    nums = list(tds[0].stripped_strings)
                    amts = list(tds[1].stripped_strings)
                    for n, a in zip(nums, amts):
                        try:
                            payouts[n.strip()] = int(a.replace(",", ""))
                        except ValueError:
                            pass
    return payouts


# ── レース結果取得 ────────────────────────────────────────────

def fetch_race_result(race_id: str) -> tuple:
    """
    Returns: (race_title, race_date, results)
    race_date: "YYYY/MM/DD"
    results: [{"着順", "馬番", "馬名", "horse_id", "コーナー通過順", "上がり3F",
               "単勝オッズ", "複勝配当"}, ...]
    """
    soup = get_soup(f"https://db.netkeiba.com/race/{race_id}/")
    if soup is None:
        raise ConnectionError(f"ページ取得失敗: race_id={race_id}")

    # レース名（空でない最初の h1）
    race_title = next(
        (h.get_text(strip=True) for h in soup.find_all("h1") if h.get_text(strip=True)),
        race_id,
    )

    # 開催日（ページタイトルから）
    race_date = ""
    title_tag = soup.find("title")
    if title_tag:
        m = re.search(r"(\d{4})年(\d{1,2})月(\d{1,2})日", title_tag.text)
        if m:
            race_date = f"{m.group(1)}/{int(m.group(2)):02d}/{int(m.group(3)):02d}"

    table = soup.find("table", class_="race_table_01")
    if table is None:
        raise ValueError(f"結果テーブルが見つかりません: race_id={race_id}")

    col = build_col_map(table)

    def ci(*keys):
        for k in keys:
            if k in col:
                return col[k]
        raise KeyError(keys)

    idx_pos    = ci("着順")
    idx_umaban = ci("馬番")
    idx_name   = ci("馬名")
    idx_corner = ci("通過")
    idx_last3f = ci("上り", "後3F")
    idx_odds   = ci("単勝")

    surface = _extract_race_surface(soup)
    fukusho = parse_fukusho_payouts(soup)

    results = []
    for tr in table.find_all("tr")[1:]:
        tds = tr.find_all("td")
        if not tds or idx_name >= len(tds):
            continue
        name_td = tds[idx_name]
        a = name_td.find("a")
        name = a.get_text(strip=True) if a else name_td.get_text(strip=True)
        if not name:
            continue

        horse_id = None
        if a and a.get("href"):
            m = re.search(r"/horse/(\d+)", a["href"])
            if m:
                horse_id = m.group(1)

        umaban = cell_text(tds, idx_umaban)
        results.append({
            "着順":          cell_text(tds, idx_pos),
            "馬番":          umaban,
            "馬名":          name,
            "horse_id":     horse_id,
            "コーナー通過順": cell_text(tds, idx_corner),
            "上がり3F":      cell_text(tds, idx_last3f),
            "単勝オッズ":    cell_text(tds, idx_odds),
            "複勝配当":      fukusho.get(umaban, 0),
            "馬場":          surface,
        })

    return race_title, race_date, results


# ── 前走データ取得 ────────────────────────────────────────────

def get_prev_races_info(horse_id: str, before_date: str, n: int = 2) -> List[dict]:
    """
    horse_id の直近 n 走のデータ（before_date より前、新しい順）を返す。
    各エントリ: {"race_id", "date", "corner_order", "last3f", "rank"}
    """
    if not horse_id:
        return []

    soup = get_soup(f"https://db.netkeiba.com/horse/result/{horse_id}/")
    if soup is None:
        return []

    table = soup.find("table", class_="db_h_race_results")
    if table is None:
        return []

    col = build_col_map(table)
    if any(k not in col for k in ("日付", "レース名", "通過", "上り")):
        return []

    idx_rank = next((col[k] for k in ("着順", "着") if k in col), -1)
    cutoff   = datetime.strptime(before_date, "%Y/%m/%d")
    found: List[dict] = []

    for tr in table.find_all("tr")[1:]:
        if len(found) >= n:
            break
        tds = tr.find_all("td")
        if not tds:
            continue

        date_str = tds[col["日付"]].get_text(strip=True)
        try:
            race_date = datetime.strptime(date_str, "%Y/%m/%d")
        except ValueError:
            continue
        if race_date >= cutoff:
            continue

        race_a = tds[col["レース名"]].find("a")
        if not race_a or not race_a.get("href"):
            continue
        m = re.search(r"/race/(\d{12})", race_a["href"])
        if not m:
            continue

        corner_td = tds[col["通過"]]
        corner    = corner_td.get_text(strip=True)

        last3f_td = tds[col["上り"]]
        span      = last3f_td.find("span")
        last3f    = span.get_text(strip=True) if span else last3f_td.get_text(strip=True)

        rank = ""
        if 0 <= idx_rank < len(tds):
            rank = tds[idx_rank].get_text(strip=True)

        found.append({
            "race_id":      m.group(1),
            "date":         date_str,
            "corner_order": corner,
            "last3f":       last3f,
            "rank":         rank,
        })

    return found


def get_prev_race_info(horse_id: str, before_date: str) -> Optional[dict]:
    """後方互換ラッパー: 前走データを 1 件返す"""
    r = get_prev_races_info(horse_id, before_date, n=1)
    return r[0] if r else None


def get_race_last3f_values(race_id: str) -> List[float]:
    """レースの全馬の上がり3Fリストを返す（ランク計算用）"""
    soup = get_soup(f"https://db.netkeiba.com/race/{race_id}/")
    if soup is None:
        return []

    table = soup.find("table", class_="race_table_01")
    if table is None:
        return []

    col = build_col_map(table)
    idx = next((col[k] for k in ("上り", "後3F") if k in col), None)
    if idx is None:
        return []

    vals = []
    for tr in table.find_all("tr")[1:]:
        tds = tr.find_all("td")
        if idx >= len(tds):
            continue
        td = tds[idx]
        span = td.find("span")
        text = span.get_text(strip=True) if span else td.get_text(strip=True)
        try:
            vals.append(float(text))
        except ValueError:
            pass
    return vals


# ── 学習適応仮説 判定 ─────────────────────────────────────────

def check_corner_drop(corner_str: str) -> bool:
    """コーナー通過順位が途中で下がる（位置番号が増加 = 後退）かチェック"""
    if not corner_str:
        return False
    nums = [int(p) for p in corner_str.split("-") if p.strip().isdigit()]
    if len(nums) < 2:
        return False
    return any(nums[i] > nums[i - 1] for i in range(1, len(nums)))


def last3f_rank(val: float, all_vals: List[float]) -> int:
    """上がり3Fのランク（競争ランキング方式: 小さいほど上位）"""
    return 1 + sum(1 for v in all_vals if v < val)


def add_hypothesis_flags(results: List[dict], race_date: str) -> List[dict]:
    """各馬の前走・2走前データを取得し、学習適応仮説フラグを付与（OR条件）"""

    # Step 1: 前走・2走前情報を並行取得
    prev_data: Dict[str, List[dict]] = {}

    def _fetch_prev(horse_id):
        return horse_id, get_prev_races_info(horse_id, race_date, n=2)

    print("前走データ取得中 ...", file=sys.stderr)
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as ex:
        futs = {ex.submit(_fetch_prev, r["horse_id"]): r for r in results if r["horse_id"]}
        for f in concurrent.futures.as_completed(futs):
            hid, data = f.result()
            prev_data[hid] = data

    # Step 2: 前走・2走前のユニークなレースについて上がり3Fを並行取得
    unique_prev_races = {d["race_id"] for lst in prev_data.values() for d in lst}
    last3f_cache: Dict[str, List[float]] = {}

    def _fetch_vals(rid):
        return rid, get_race_last3f_values(rid)

    print(f"前走レース {len(unique_prev_races)} 件の上がり3F取得中 ...", file=sys.stderr)
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as ex:
        for rid, vals in ex.map(_fetch_vals, unique_prev_races):
            last3f_cache[rid] = vals

    # Step 3: 条件チェック（パターン1 OR パターン2）
    for r in results:
        hid       = r["horse_id"]
        prev_list = prev_data.get(hid, []) if hid else []
        prev      = prev_list[0] if len(prev_list) > 0 else None
        prev2     = prev_list[1] if len(prev_list) > 1 else None

        r["前走日付"] = prev["date"] if prev else "---"

        # パターン1: 前走コーナー下がり + 前走上がり3位以内
        cond1 = check_corner_drop(prev["corner_order"]) if prev else False
        cond2 = False
        if prev:
            try:
                val = float(prev["last3f"])
                all_vals = last3f_cache.get(prev["race_id"], [])
                if all_vals:
                    cond2 = last3f_rank(val, all_vals) <= 3
            except (ValueError, TypeError):
                pass
        pattern1 = cond1 and cond2

        # パターン2: 2走前コーナー下がり + 2走前上がり3位以内 + 前走6着以下
        pattern2 = False
        if prev2:
            p2c1 = check_corner_drop(prev2["corner_order"])
            p2c2 = False
            try:
                val2  = float(prev2["last3f"])
                vals2 = last3f_cache.get(prev2["race_id"], [])
                if vals2:
                    p2c2 = last3f_rank(val2, vals2) <= 3
            except (ValueError, TypeError):
                pass
            p2c3 = False
            if prev:
                try:
                    p2c3 = int(prev["rank"]) >= 6
                except (ValueError, TypeError):
                    pass
            pattern2 = p2c1 and p2c2 and p2c3

        r["条件1"] = cond1
        r["条件2"] = cond2
        r["仮説フラグ"] = pattern1 or pattern2

    return results


# ── 回収率 ───────────────────────────────────────────────────

def calc_recovery(results: list, flagged: bool, bet_type: str = "単勝") -> dict:
    """単勝または複勝の回収率を計算"""
    target = [r for r in results if r.get("仮説フラグ") == flagged]
    invested = len(target) * 100
    if invested == 0:
        return {"count": 0, "invested": 0, "returned": 0, "rate": 0.0}

    returned = 0
    if bet_type == "単勝":
        winner = next((r for r in results if r["着順"] == "1"), None)
        if winner and winner.get("仮説フラグ") == flagged:
            try:
                returned = round(float(winner["単勝オッズ"]) * 100)
            except (ValueError, TypeError):
                pass
    else:  # 複勝
        for r in target:
            try:
                returned += int(r.get("複勝配当", 0))
            except (ValueError, TypeError):
                pass

    return {
        "count":    len(target),
        "invested": invested,
        "returned": returned,
        "rate":     returned / invested * 100,
    }


# ── 表示 ─────────────────────────────────────────────────────

def print_results(race_title: str, results: list) -> None:
    has_flags = "仮説フラグ" in results[0] if results else False

    print(f"\n{race_title}")
    sep = "=" * 72

    if has_flags:
        fmt = "{:<4}  {:<16}  {:<15}  {:>8}  {:>8}  {}"
        header = fmt.format("着順", "馬名", "コーナー通過", "上がり3F", "単勝", "フラグ")
    else:
        fmt = "{:<4}  {:<16}  {:<15}  {:>8}  {:>8}"
        header = fmt.format("着順", "馬名", "コーナー通過", "上がり3F", "単勝")

    print(sep)
    print(header)
    print("-" * 72)

    for r in results:
        if has_flags:
            cond1 = "○" if r.get("条件1") else "×"
            cond2 = "○" if r.get("条件2") else "×"
            flag_col = f"★  [条1:{cond1} 条2:{cond2}]" if r.get("仮説フラグ") else f"   [条1:{cond1} 条2:{cond2}]"
            print(fmt.format(
                r["着順"], r["馬名"], r["コーナー通過順"],
                r["上がり3F"], r["単勝オッズ"], flag_col,
            ))
        else:
            print(fmt.format(
                r["着順"], r["馬名"], r["コーナー通過順"],
                r["上がり3F"], r["単勝オッズ"],
            ))

    if has_flags:
        print()
        print("【学習適応仮説】前走ベース判定")
        print("  条件1: 前走のコーナー通過順位が途中で下がった（後退あり）")
        print("  条件2: 前走の上がり3Fが前走メンバー内3位以内")
        print()

        def fmt_row(label, tan, fuku):
            if tan["count"] == 0:
                return f"{label}: 対象なし"
            return (
                f"{label}: {tan['count']}頭 / "
                f"単勝 {tan['rate']:.1f}% / 複勝 {fuku['rate']:.1f}%  "
                f"(投資{tan['invested']}円)"
            )

        print(fmt_row("フラグあり",
                      calc_recovery(results, True,  "単勝"),
                      calc_recovery(results, True,  "複勝")))
        print(fmt_row("フラグなし",
                      calc_recovery(results, False, "単勝"),
                      calc_recovery(results, False, "複勝")))


# ── 累計集計 ─────────────────────────────────────────────────

def print_aggregate_summary(all_stats: list) -> None:
    """複数レースの累計回収率サマリーを表示（単勝・複勝）"""
    totals = {k: {"count": 0, "invested": 0, "returned": 0}
              for k in ("on_tan", "off_tan", "on_fuku", "off_fuku")}
    for s in all_stats:
        for key in ("count", "invested", "returned"):
            totals["on_tan"][key]   += s["on_tan"][key]
            totals["off_tan"][key]  += s["off_tan"][key]
            totals["on_fuku"][key]  += s["on_fuku"][key]
            totals["off_fuku"][key] += s["off_fuku"][key]

    def rate(d):
        return d["returned"] / d["invested"] * 100 if d["invested"] > 0 else 0.0

    def side(d):
        if d["invested"] == 0:
            return f"{'---':>5}  {'---':>8}  {'---':>8}  {'---':>7}"
        return (
            f"{d['count']:>5}  "
            f"{d['invested']:>7,}円  "
            f"{d['returned']:>7,}円  "
            f"{rate(d):>6.1f}%"
        )

    n = len(all_stats)
    print()
    print("=" * 74)
    print(f"【累計集計】{n} レース")
    print("=" * 74)
    print(f"{'':10}  {'フラグあり':^38}  {'フラグなし':^38}")
    print(f"{'':10}  {'頭数':>5}  {'投資':>8}  {'回収':>8}  {'回収率':>6}  {'頭数':>5}  {'投資':>8}  {'回収':>8}  {'回収率':>6}")
    print("-" * 74)
    print(f"{'単勝':<10}  {side(totals['on_tan'])}  {side(totals['off_tan'])}")
    print(f"{'複勝':<10}  {side(totals['on_fuku'])}  {side(totals['off_fuku'])}")

    # レース別サマリー
    print()
    print("  レース別内訳:")
    hdr = f"  {'race_id':<14}  {'レース名':<22}  {'あり単勝':>7}  {'なし単勝':>7}  {'あり複勝':>7}  {'なし複勝':>7}"
    print(hdr)
    print("  " + "-" * (len(hdr) - 2))
    for s in all_stats:
        def r_str(d):
            return f"{rate(d):.0f}%" if d["invested"] > 0 else "---"
        print(
            f"  {s['race_id']:<14}  {s['title'][:22]:<22}  "
            f"{r_str(s['on_tan']):>7}  {r_str(s['off_tan']):>7}  "
            f"{r_str(s['on_fuku']):>7}  {r_str(s['off_fuku']):>7}"
        )


# ── race_id 自動生成（2025年阪神・後方互換） ───────────────────

def generate_hanshin_2025_candidates() -> List[str]:
    """2025年阪神(venue=09)の race_id 候補を全列挙（実在は未確認）"""
    return [
        f"202509{kai:02d}{day:02d}{race:02d}"
        for kai  in range(1, 6)   # 第1〜5回
        for day  in range(1, 9)   # 1〜8日目
        for race in range(1, 13)  # 1〜12R
    ]


def probe_race_exists(race_id: str) -> bool:
    """レースページが存在するか軽量チェック（HTML 全解析なし）"""
    time.sleep(_REQUEST_INTERVAL)
    try:
        resp = _SESSION.get(
            f"https://db.netkeiba.com/race/{race_id}/",
            headers={"Referer": "https://db.netkeiba.com/"},
            timeout=15,
        )
        return resp.status_code == 200 and b"race_table_01" in resp.content
    except requests.RequestException:
        return False


def collect_hanshin_2025_ids(target: int = 30) -> List[str]:
    """2025年阪神開催から有効な race_id を target 件収集（後方互換）"""
    candidates = generate_hanshin_2025_candidates()
    valid: List[str] = []
    batch = 12

    print(f"2025年阪神の race_id を探索中（目標 {target} 件）...", file=sys.stderr)
    for start in range(0, len(candidates), batch):
        if len(valid) >= target:
            break
        chunk = candidates[start: start + batch]
        with concurrent.futures.ThreadPoolExecutor(max_workers=batch) as ex:
            flags = list(ex.map(probe_race_exists, chunk))
        found = [c for c, ok in zip(chunk, flags) if ok]
        valid.extend(found)
        if found:
            print(
                f"  {chunk[0]}〜{chunk[-1]}: {len(found)} 件有効"
                f"（累計 {len(valid)} 件）",
                file=sys.stderr,
            )

    result = sorted(valid)[:target]
    print(f"収集完了: {len(result)} 件", file=sys.stderr)
    return result


# ── 複数場 race_id 自動収集 ───────────────────────────────────

def _resolve_venue_codes(venue_list: List[str]) -> List[str]:
    """'hanshin' → '09'、'09' → '09' に正規化"""
    codes = []
    for v in venue_list:
        v = v.strip()
        if v in VENUE_NAMES:
            codes.append(VENUE_NAMES[v])
        elif re.fullmatch(r"\d{2}", v):
            codes.append(v)
        else:
            print(f"[WARN] 不明な場コード: {v} (スキップ)", file=sys.stderr)
    return codes


def generate_multi_venue_candidates(year: int, venue_codes: List[str]) -> List[str]:
    """複数場の race_id 候補を day 単位でラウンドロビン生成"""
    per_venue = [
        [
            f"{year}{code}{kai:02d}{day:02d}{race:02d}"
            for kai  in range(1, 7)
            for day  in range(1, 9)
            for race in range(1, 13)
        ]
        for code in venue_codes
    ]
    candidates: List[str] = []
    batch = 12
    max_len = max(len(v) for v in per_venue)
    for start in range(0, max_len, batch):
        for vlist in per_venue:
            candidates.extend(vlist[start: start + batch])
    return candidates


def collect_multi_venue_ids(year: int, venue_codes: List[str], target: int = 100) -> List[str]:
    """複数場から有効な race_id を target 件収集"""
    candidates = generate_multi_venue_candidates(year, venue_codes)
    valid: List[str] = []
    batch = 12 * len(venue_codes)

    venue_str = "+".join(venue_codes)
    print(f"{year}年 [{venue_str}] の race_id 探索中（目標 {target} 件）...", file=sys.stderr)

    for start in range(0, len(candidates), batch):
        if len(valid) >= target:
            break
        chunk = candidates[start: start + batch]
        with concurrent.futures.ThreadPoolExecutor(max_workers=min(len(chunk), 3)) as ex:
            flags = list(ex.map(probe_race_exists, chunk))
        found = [c for c, ok in zip(chunk, flags) if ok]
        valid.extend(found)
        if found:
            print(
                f"  {chunk[0]}〜{chunk[-1]}: {len(found)} 件有効（累計 {len(valid)} 件）",
                file=sys.stderr,
            )
        time.sleep(10.0)  # バッチ間インターバル（レートリミット対策）

    result = sorted(valid)[:target]
    print(f"収集完了: {len(result)} 件", file=sys.stderr)
    return result


# ── CSV 保存 ──────────────────────────────────────────────────

def save_to_csv(all_race_data: list, filepath: str) -> None:
    """全レースデータを CSV に保存（Excel 対応 UTF-8 BOM）"""
    fieldnames = [
        "race_id", "race_title", "race_date",
        "着順", "馬番", "馬名", "コーナー通過順", "上がり3F", "単勝オッズ", "複勝配当",
        "条件1", "条件2", "仮説フラグ", "馬場",
    ]
    total = 0
    with open(filepath, "w", newline="", encoding="utf-8-sig") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        for race_id, title, date, results in all_race_data:
            for r in results:
                writer.writerow({
                    "race_id":    race_id,
                    "race_title": title,
                    "race_date":  date,
                    "着順":        r.get("着順", ""),
                    "馬番":        r.get("馬番", ""),
                    "馬名":        r.get("馬名", ""),
                    "コーナー通過順": r.get("コーナー通過順", ""),
                    "上がり3F":    r.get("上がり3F", ""),
                    "単勝オッズ":  r.get("単勝オッズ", ""),
                    "複勝配当":    r.get("複勝配当", 0),
                    "条件1":      r.get("条件1", ""),
                    "条件2":      r.get("条件2", ""),
                    "仮説フラグ":  r.get("仮説フラグ", ""),
                    "馬場":        r.get("馬場", ""),
                })
                total += 1
    print(f"CSV 保存完了: {filepath}  ({total} 行)", file=sys.stderr)


# ── エントリーポイント ─────────────────────────────────────────

if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="netkeiba レース結果スクレイパー + 学習適応仮説判定",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=(
            "使用例:\n"
            "  %(prog)s 202509030111                             # 単一レース\n"
            "  %(prog)s 202509030111 202509030112               # 複数レース\n"
            "  %(prog)s --hanshin2025 --count 30 --csv h25.csv  # 2025阪神（後方互換）\n"
            "  %(prog)s --year 2026 --venues 09,06,05,08 --count 100 --csv 2026.csv\n"
            "  %(prog)s --year 2026 --venues hanshin,tokyo,nakayama,kyoto --count 100\n"
        ),
    )
    parser.add_argument(
        "race_ids", nargs="*", metavar="RACE_ID",
        help="処理する race_id（複数可）",
    )
    parser.add_argument(
        "--hanshin2025", action="store_true",
        help="2025年阪神開催の race_id を自動収集（後方互換）",
    )
    parser.add_argument(
        "--year", type=int, default=None, metavar="YYYY",
        help="自動収集する年（例: 2026）",
    )
    parser.add_argument(
        "--venues", default="09,06,05,08", metavar="CODES",
        help="場コード カンマ区切り（例: 09,06,05,08 または hanshin,tokyo,nakayama,kyoto）",
    )
    parser.add_argument(
        "--count", type=int, default=30, metavar="N",
        help="自動収集レース数（default: 30）",
    )
    parser.add_argument(
        "--csv", metavar="FILE",
        help="結果を CSV ファイルに保存",
    )
    args = parser.parse_args()

    # race_id リストを確定
    auto_modes = sum(bool(x) for x in [args.hanshin2025, args.year])
    if auto_modes > 1 or (auto_modes and args.race_ids):
        parser.error("--hanshin2025 / --year / race_id は排他指定です")

    if args.hanshin2025:
        race_ids = collect_hanshin_2025_ids(args.count)
    elif args.year:
        codes = _resolve_venue_codes(args.venues.split(","))
        if not codes:
            parser.error("有効な場コードが指定されていません")
        race_ids = collect_multi_venue_ids(args.year, codes, args.count)
    elif args.race_ids:
        race_ids = args.race_ids
    else:
        race_ids = ["202509030111"]

    all_stats: list = []
    all_race_data: list = []

    for i, race_id in enumerate(race_ids, 1):
        print(f"\n[{i}/{len(race_ids)}] {race_id} 処理中 ...", file=sys.stderr)
        try:
            title, date, data = fetch_race_result(race_id)
            data = add_hypothesis_flags(data, date)
            print_results(title, data)
            sys.stdout.flush()
            all_stats.append({
                "race_id":  race_id,
                "title":    title,
                "on_tan":   calc_recovery(data, True,  "単勝"),
                "off_tan":  calc_recovery(data, False, "単勝"),
                "on_fuku":  calc_recovery(data, True,  "複勝"),
                "off_fuku": calc_recovery(data, False, "複勝"),
            })
            all_race_data.append((race_id, title, date, data))
        except Exception as e:
            print(f"[ERROR] {race_id}: {e}", file=sys.stderr)

    if len(race_ids) > 1 and all_stats:
        print_aggregate_summary(all_stats)

    if args.csv and all_race_data:
        save_to_csv(all_race_data, args.csv)
