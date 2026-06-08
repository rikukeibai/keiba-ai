#!/usr/bin/env python3
"""
来週末の全レース出走予定馬に学習適応仮説フラグを判定して表示
過去の回収率実績は指定 CSV から自動計算

使い方:
  python3 yosou.py                              # 来週末, 2026_multi.csv 参照
  python3 yosou.py --dates 20260613 20260614    # 日付を直接指定
  python3 yosou.py --hist nikatsu_300.csv       # 参照 CSV を変更
  python3 yosou.py --log yosou_log.csv          # ログ出力先を変更
"""

import argparse
import concurrent.futures
import csv
import html as _html
import os
import re
import sys
import threading
from collections import defaultdict
from datetime import date, timedelta
from typing import Dict, List, Optional, Tuple

import requests
from bs4 import BeautifulSoup
from flask import Flask, Response, redirect

from netkeiba_scraper import (
    HEADERS,
    check_corner_drop,
    get_prev_race_info,
    get_race_last3f_values,
    last3f_rank,
)

DEFAULT_HIST = "2026_multi.csv"
DEFAULT_LOG  = "yosou_log.csv"

CLASS_ORDER = [
    "G1", "G2", "G3", "リステッド",
    "3勝クラス", "2勝クラス", "1勝クラス", "未勝利", "その他",
]

VENUE_MAP = {
    "01": "札幌", "02": "函館", "03": "福島", "04": "新潟",
    "05": "中山", "06": "東京", "07": "中京", "08": "京都",
    "09": "阪神", "10": "小倉",
}


# ── 共通ユーティリティ ────────────────────────────────────────

def classify(title: str) -> str:
    if re.search(r"\(GIII\)", title): return "G3"
    if re.search(r"\(GII\)",  title): return "G2"
    if re.search(r"\(GI\)",   title): return "G1"
    if "(L)" in title:                return "リステッド"
    if "3勝" in title: return "3勝クラス"
    if "2勝" in title: return "2勝クラス"
    if "1勝" in title: return "1勝クラス"
    if "未勝利" in title: return "未勝利"
    return "その他"


def race_label(race_id: str) -> str:
    """race_id から '阪神11R' 形式の文字列を作成"""
    venue = VENUE_MAP.get(race_id[4:6], race_id[4:6])
    r_num = int(race_id[10:12])
    return f"{venue}{r_num}R"


# ── 過去実績データ読み込み ────────────────────────────────────

def load_hist_rates(csv_path: str) -> Tuple[Dict[str, Dict], int]:
    """
    CSV からクラス別回収率を集計して返す。
    Returns: (rates_by_class, total_races)
    rates_by_class[cls] = {races, on_tan, off_tan, on_fuku, off_fuku}  (% string or "---")
    """
    try:
        with open(csv_path, encoding="utf-8-sig") as f:
            rows = list(csv.DictReader(f))
    except FileNotFoundError:
        print(f"[WARN] 過去データが見つかりません: {csv_path}", file=sys.stderr)
        return {}, 0

    race_groups: Dict[str, list] = defaultdict(list)
    for r in rows:
        race_groups[r["race_id"]].append(r)

    acc = defaultdict(lambda: {k: 0 for k in (
        "races",
        "on_tan_i",  "on_tan_r",
        "off_tan_i", "off_tan_r",
        "on_fk_i",   "on_fk_r",
        "off_fk_i",  "off_fk_r",
    )})

    has_fuku_col = "複勝配当" in (rows[0] if rows else {})

    for race_id, horses in race_groups.items():
        cls = classify(horses[0]["race_title"])
        d   = acc[cls]
        d["races"] += 1
        winner = next((h for h in horses if h.get("着順") == "1"), None)

        for flag_str, pfx in [("True", "on"), ("False", "off")]:
            grp = [h for h in horses if h.get("仮説フラグ") == flag_str]
            if not grp:
                continue
            inv = len(grp) * 100
            d[f"{pfx}_tan_i"] += inv
            if winner and winner.get("仮説フラグ") == flag_str:
                try:
                    d[f"{pfx}_tan_r"] += round(float(winner["単勝オッズ"]) * 100)
                except (ValueError, TypeError):
                    pass
            if has_fuku_col:
                d[f"{pfx}_fk_i"] += inv
                for h in grp:
                    try:
                        d[f"{pfx}_fk_r"] += int(h.get("複勝配当", 0) or 0)
                    except (ValueError, TypeError):
                        pass

    def pct(ret, inv):
        return f"{ret / inv * 100:.1f}%" if inv else "---"

    rates = {}
    for cls, d in acc.items():
        rates[cls] = {
            "races":   d["races"],
            "on_tan":  pct(d["on_tan_r"],  d["on_tan_i"]),
            "off_tan": pct(d["off_tan_r"], d["off_tan_i"]),
            "on_fk":   pct(d["on_fk_r"],   d["on_fk_i"]),
            "off_fk":  pct(d["off_fk_r"],  d["off_fk_i"]),
        }
    return rates, len(race_groups)


# ── スケジュール取得 ──────────────────────────────────────────

def next_weekend_dates() -> List[str]:
    """今日から最も近い土曜＋日曜の YYYYMMDD リストを返す"""
    today = date.today()
    days_to_sat = (5 - today.weekday()) % 7
    if days_to_sat == 0 and today.weekday() != 5:
        # 日曜 → 来週土曜へ
        days_to_sat = 6
    sat = today + timedelta(days=days_to_sat)
    sun = sat + timedelta(days=1)
    return [sat.strftime("%Y%m%d"), sun.strftime("%Y%m%d")]


def fetch_race_ids_for_date(date_str: str) -> List[str]:
    """
    YYYYMMDD の日付に対応する race_id リストを取得。
    R01 をプローブしてページ内の日付と照合 → 一致した venue/kai/day の R01-R12 を返す。
    ※ 出馬表は通常レース前日〜木曜に公開される。未公開時は空リストを返す。
    """
    year     = date_str[:4]
    target   = f"{date_str[:4]}/{date_str[4:6]}/{date_str[6:8]}"
    # 開催が多い主場に絞る（全場対応させる場合は ALL_VENUES に変更可）
    venues   = ["01", "02", "03", "04", "05", "06", "07", "08", "09", "10"]
    r01_cands = [
        f"{year}{v}{k:02d}{d:02d}01"
        for v in venues
        for k in range(1, 7)
        for d in range(1, 9)
    ]

    def probe_r01(race_id: str) -> Optional[str]:
        """R01 をフェッチして日付が target なら prefix(10桁)を返す"""
        try:
            resp = requests.get(
                f"https://db.netkeiba.com/race/{race_id}/",
                headers=HEADERS, timeout=8,
            )
            if resp.status_code != 200:
                return None
            resp.encoding = "euc-jp"
            m = re.search(r"(\d{4})年(\d{1,2})月(\d{1,2})日", resp.text)
            if not m:
                return None
            d = f"{m.group(1)}/{int(m.group(2)):02d}/{int(m.group(3)):02d}"
            return race_id[:10] if d == target else None
        except requests.RequestException:
            return None

    print(f"  {date_str} の開催スケジュールをプローブ中 ...", file=sys.stderr)
    with concurrent.futures.ThreadPoolExecutor(max_workers=20) as ex:
        prefixes = {p for p in ex.map(probe_r01, r01_cands) if p}

    if not prefixes:
        print(f"  {date_str}: 出馬表未公開（木曜以降に再実行してください）", file=sys.stderr)
        return []

    # 一致した venue/kai/day の R01-R12 をプローブして出馬表があるか確認
    full_cands = [f"{p}{r:02d}" for p in sorted(prefixes) for r in range(1, 13)]

    def probe_exists(race_id: str) -> Optional[str]:
        try:
            resp = requests.get(
                f"https://db.netkeiba.com/race/{race_id}/",
                headers=HEADERS, timeout=8,
            )
            if resp.status_code == 200 and b"race_table_01" in resp.content:
                return race_id
        except requests.RequestException:
            pass
        return None

    with concurrent.futures.ThreadPoolExecutor(max_workers=16) as ex:
        valid = [r for r in ex.map(probe_exists, full_cands) if r]

    print(f"  {date_str}: {len(valid)} レース確認", file=sys.stderr)
    return sorted(valid)


# ── 出馬表取得 ────────────────────────────────────────────────

def fetch_shutuba(race_id: str) -> Optional[Tuple[str, str, List[Dict]]]:
    """
    db.netkeiba.com から出馬表を取得。
    Returns: (race_title, race_date "YYYY/MM/DD", horses) or None
    horses: [{"馬番", "馬名", "horse_id", ...}, ...]
    """
    try:
        resp = requests.get(
            f"https://db.netkeiba.com/race/{race_id}/",
            headers=HEADERS,
            timeout=15,
        )
    except requests.RequestException as e:
        print(f"[WARN] shutuba 取得失敗 {race_id}: {e}", file=sys.stderr)
        return None

    if resp.status_code != 200:
        return None

    resp.encoding = "euc-jp"
    soup = BeautifulSoup(resp.text, "html.parser")

    # レース名
    race_title = next(
        (h.get_text(strip=True) for h in soup.find_all("h1") if h.get_text(strip=True)),
        race_id,
    )

    # 開催日
    race_date = ""
    title_tag = soup.find("title")
    if title_tag:
        m = re.search(r"(\d{4})年(\d{1,2})月(\d{1,2})日", title_tag.text)
        if m:
            race_date = f"{m.group(1)}/{int(m.group(2)):02d}/{int(m.group(3)):02d}"

    # 出走馬テーブル
    table = soup.find("table", class_="race_table_01")
    if not table:
        return None

    # ヘッダーから 馬番・馬名 列インデックスを取得
    header_row = table.find("tr", class_="txt_c") or table.find("tr")
    col: Dict[str, int] = {}
    if header_row:
        for i, th in enumerate(header_row.find_all("th")):
            col[th.get_text(separator="", strip=True)] = i

    idx_umaban = col.get("馬番", -1)
    idx_name   = next((col[k] for k in ("馬名", "馬　名") if k in col), -1)

    horses = []
    seen: set = set()

    for tr in table.find_all("tr")[1:]:
        tds = tr.find_all("td")
        if not tds:
            continue

        # 馬名セルから horse_id を抽出
        horse_a = None
        if 0 <= idx_name < len(tds):
            horse_a = tds[idx_name].find("a", href=re.compile(r"/horse/\d+"))
        if horse_a is None:
            for td in tds:
                horse_a = td.find("a", href=re.compile(r"/horse/\d+"))
                if horse_a:
                    break
        if horse_a is None:
            continue

        m = re.search(r"/horse/(\d+)", horse_a["href"])
        if not m:
            continue
        horse_id = m.group(1)
        if horse_id in seen:
            continue
        seen.add(horse_id)

        name = horse_a.get_text(strip=True)
        if not name:
            continue

        # 馬番
        umaban = ""
        if 0 <= idx_umaban < len(tds):
            umaban = tds[idx_umaban].get_text(strip=True)
        if not umaban:
            # フォールバック: 小さい整数のセルを探す
            for td in tds[:6]:
                t = td.get_text(strip=True)
                if t.isdigit() and 1 <= int(t) <= 18:
                    umaban = t
                    break

        horses.append({
            "馬番":          umaban,
            "馬名":          name,
            "horse_id":     horse_id,
            "前走日付":      "---",
            "前走コーナー順": "---",
            "前走3F順位":    "---",
            "条件1":        False,
            "条件2":        False,
            "仮説フラグ":    False,
        })

    return race_title, race_date, horses


# ── 仮説フラグ付与（表示用データも収集） ─────────────────────

def add_prediction_flags(horses: List[Dict], race_date: str) -> List[Dict]:
    """前走データを取得し、条件1・2・仮説フラグと表示用データを付与"""
    if not race_date:
        return horses

    # Step1: 前走情報を並行取得
    prev_data: Dict[str, Optional[Dict]] = {}

    def _fetch_prev(horse_id):
        return horse_id, get_prev_race_info(horse_id, race_date)

    print("  前走データ取得中 ...", file=sys.stderr)
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as ex:
        futs = {ex.submit(_fetch_prev, h["horse_id"]): h
                for h in horses if h.get("horse_id")}
        for f in concurrent.futures.as_completed(futs):
            hid, data = f.result()
            prev_data[hid] = data

    # Step2: 前走レースの上がり3Fリストを並行取得
    unique_prev = {d["race_id"] for d in prev_data.values() if d}
    last3f_cache: Dict[str, List[float]] = {}

    def _fetch_vals(rid):
        return rid, get_race_last3f_values(rid)

    if unique_prev:
        print(f"  前走レース {len(unique_prev)} 件の上がり3F取得中 ...", file=sys.stderr)
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as ex:
        for rid, vals in ex.map(_fetch_vals, unique_prev):
            last3f_cache[rid] = vals

    # Step3: 条件判定・情報付与
    for h in horses:
        hid  = h.get("horse_id")
        prev = prev_data.get(hid) if hid else None

        if not prev:
            continue

        h["前走日付"]      = prev["date"]
        h["前走コーナー順"] = prev["corner_order"] or "---"

        cond1 = check_corner_drop(prev["corner_order"])

        cond2      = False
        rank_str   = "---"
        try:
            val      = float(prev["last3f"])
            all_vals = last3f_cache.get(prev["race_id"], [])
            if all_vals:
                rank     = last3f_rank(val, all_vals)
                rank_str = str(rank)
                cond2    = rank <= 3
        except (ValueError, TypeError):
            pass

        h["前走3F順位"] = rank_str
        h["条件1"]     = cond1
        h["条件2"]     = cond2
        h["仮説フラグ"] = cond1 and cond2

    return horses


# ── 表示 ─────────────────────────────────────────────────────

def fmt_hist(rates: Dict[str, Dict], cls: str) -> str:
    """クラス別過去実績を1行で整形"""
    r = rates.get(cls)
    if not r:
        return "(過去データなし)"
    fuku_part = ""
    if r["on_fk"] != "---" or r["off_fk"] != "---":
        fuku_part = f"  複勝: あり {r['on_fk']} / なし {r['off_fk']}"
    return (
        f"{r['races']}R実績  "
        f"単勝: あり {r['on_tan']} / なし {r['off_tan']}"
        f"{fuku_part}"
    )


def print_report(
    races_by_class: Dict[str, List[Dict]],
    hist_rates: Dict[str, Dict],
    dates: List[str],
    hist_csv: str,
    total_hist: int,
) -> None:
    """クラス別にレース・馬情報を表示"""
    date_label = "  ".join(
        f"{d[:4]}/{d[4:6]}/{d[6:8]}" for d in dates
    )

    print()
    print("=" * 70)
    print(f"  学習適応仮説 予想レポート  {date_label}")
    print(f"  参照データ: {hist_csv}  ({total_hist} レース)")
    print("=" * 70)

    flagged_all: List[Dict] = []

    for cls in CLASS_ORDER:
        race_list = races_by_class.get(cls)
        if not race_list:
            continue

        print()
        print(f"▌ {cls}  ({len(race_list)} レース)")
        print(f"  過去実績: {fmt_hist(hist_rates, cls)}")
        print("  " + "─" * 66)

        horse_hdr = f"  {'馬番':>3}  {'馬名':<16}  {'前走コーナー順':<14}  {'3F順':>4}  {'条1':>3}  {'条2':>3}  フラグ"
        print(horse_hdr)

        for race in race_list:
            rdate = race["race_date"]
            label = race_label(race["race_id"])
            print(f"\n    [{label}] {race['race_title']}  {rdate}")
            print("    " + "-" * 62)

            for h in sorted(race["horses"], key=lambda x: x.get("馬番", "99") or "99"):
                c1   = "○" if h["条件1"]    else "×"
                c2   = "○" if h["条件2"]    else "×"
                flag = "★★★" if h["仮説フラグ"] else ""
                print(
                    f"  {h['馬番']:>4}  {h['馬名']:<16}  "
                    f"{h['前走コーナー順']:<14}  {h['前走3F順位']:>4}位  "
                    f"{c1:>3}  {c2:>3}  {flag}"
                )
                if h["仮説フラグ"]:
                    flagged_all.append({
                        "cls":    cls,
                        "label":  label,
                        "title":  race["race_title"],
                        "date":   rdate,
                        "horse":  h,
                        "race_id": race["race_id"],
                    })

    # ── フラグあり馬 一覧 ───────────────────────────────────
    print()
    print("=" * 70)
    print(f"  ★ フラグあり馬  合計 {len(flagged_all)} 頭")
    print("=" * 70)

    if not flagged_all:
        print("  (該当馬なし)")
    else:
        for item in flagged_all:
            h    = item["horse"]
            hist = hist_rates.get(item["cls"])
            hist_str = ""
            if hist:
                hist_str = f"  [過去単勝あり{hist['on_tan']}]"
            print(
                f"\n  ★ {item['label']}  {item['title']}  ({item['cls']})  {item['date']}"
            )
            print(
                f"     馬番{h['馬番']}  {h['馬名']}"
                f"  前走: コーナー後退○ / 上がり3F {h['前走3F順位']}位○"
                f"  (前走日: {h['前走日付']}){hist_str}"
            )

    print()


# ── CSV ログ保存 ──────────────────────────────────────────────

def save_log(races_by_class: Dict[str, List[Dict]], filepath: str) -> None:
    """予想結果を CSV に保存"""
    today_str = date.today().strftime("%Y/%m/%d")
    fieldnames = [
        "予想日", "開催日", "race_id", "レース名", "クラス",
        "馬番", "馬名",
        "前走日付", "前走コーナー順", "前走3F順位",
        "条件1", "条件2", "仮説フラグ",
    ]
    rows = []
    for cls, race_list in races_by_class.items():
        for race in race_list:
            for h in race["horses"]:
                rows.append({
                    "予想日":    today_str,
                    "開催日":    race["race_date"],
                    "race_id":  race["race_id"],
                    "レース名":  race["race_title"],
                    "クラス":    cls,
                    "馬番":      h.get("馬番", ""),
                    "馬名":      h.get("馬名", ""),
                    "前走日付":      h.get("前走日付", ""),
                    "前走コーナー順": h.get("前走コーナー順", ""),
                    "前走3F順位":    h.get("前走3F順位", ""),
                    "条件1":    h.get("条件1", ""),
                    "条件2":    h.get("条件2", ""),
                    "仮説フラグ": h.get("仮説フラグ", ""),
                })

    with open(filepath, "w", newline="", encoding="utf-8-sig") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)

    print(f"ログ保存完了: {filepath}  ({len(rows)} 行)", file=sys.stderr)


# ── HTML レポート生成 ─────────────────────────────────────────

def generate_html_report(
    races_by_class: Dict[str, List[Dict]],
    hist_rates: Dict[str, Dict],
    dates: List[str],
    hist_csv: str,
    total_hist: int,
    filepath: Optional[str] = "yosou_result.html",
) -> str:
    """予想結果を keiba-ai-v2 デザインの HTML ファイルとして出力"""

    # ── ヘルパー ────────────────────────────────────────────
    def esc(s) -> str:
        return _html.escape(str(s) if s is not None else "")

    def rate_cls(s: str) -> str:
        """回収率文字列から CSS クラスを返す"""
        if s in ("---", ""):
            return "rate-na"
        try:
            v = float(s.rstrip("%"))
            return "rate-hi" if v >= 100 else "rate-mid" if v >= 80 else "rate-lo"
        except ValueError:
            return "rate-na"

    def fmt_date_jp(d: str) -> str:
        """YYYYMMDD → YYYY/MM/DD(曜)"""
        wdays = "月火水木金土日"
        dt = date(int(d[:4]), int(d[4:6]), int(d[6:8]))
        return f"{d[:4]}/{d[4:6]}/{d[6:8]}({wdays[dt.weekday()]})"

    today_str  = date.today().strftime("%Y/%m/%d")
    date_label = "・".join(fmt_date_jp(d) for d in dates)

    total_races   = sum(len(v) for v in races_by_class.values())
    total_horses  = sum(len(r["horses"]) for v in races_by_class.values() for r in v)
    total_flagged = sum(
        sum(1 for h in r["horses"] if h["仮説フラグ"])
        for v in races_by_class.values() for r in v
    )
    flag_pct = f"{total_flagged / total_horses * 100:.1f}" if total_horses else "0"

    # ── フラグあり馬リスト（表示順） ─────────────────────
    flagged_all = []
    for cls in CLASS_ORDER:
        for race in races_by_class.get(cls, []):
            for h in race["horses"]:
                if h["仮説フラグ"]:
                    flagged_all.append({"cls": cls, "race": race, "horse": h})

    # ── CSS ────────────────────────────────────────────────
    css = (
        "*{box-sizing:border-box;margin:0;padding:0;"
        "font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif}"
        "body{background:#f5f5f0;padding:0;color:#1a1a18;font-size:13px;line-height:1.5}"
        "nav{background:#fff;border-bottom:1px solid #e8e8e4;padding:0 16px;"
        "position:sticky;top:0;z-index:100}"
        ".nav-inner{max-width:980px;margin:0 auto;display:flex;align-items:center;"
        "height:44px;gap:12px}"
        ".nav-brand{font-size:13px;font-weight:600;color:#534AB7}"
        ".nav-links{display:flex;gap:4px;margin-left:auto}"
        ".nav-link{padding:5px 12px;border-radius:6px;text-decoration:none;"
        "font-size:13px;color:#555;white-space:nowrap}"
        ".nav-link:hover{background:#f5f5f0;color:#1a1a18}"
        ".nav-link.active{background:#EEEDFE;color:#534AB7;font-weight:500}"
        ".nav-update{background:#534AB7!important;color:#fff!important;font-weight:500}"
        ".nav-update:hover{background:#3C3489!important}"
        ".app{max-width:980px;margin:0 auto;padding:20px 16px}"
        "h1{font-size:18px;font-weight:500;margin-bottom:4px}"
        "h2{font-size:14px;font-weight:600;margin-bottom:12px;color:#534AB7}"
        ".subtitle{font-size:12px;color:#888;margin-bottom:20px}"
        ".ver-badge{display:inline-block;font-size:10px;padding:2px 8px;"
        "background:#EEEDFE;color:#534AB7;border-radius:6px;margin-left:8px;vertical-align:middle}"
        ".metrics{display:grid;grid-template-columns:repeat(4,1fr);gap:10px;margin-bottom:20px}"
        ".metric{background:#fff;border:1px solid #e8e8e4;border-radius:10px;padding:12px 14px}"
        ".metric-label{font-size:11px;color:#888;margin-bottom:4px}"
        ".metric-val{font-size:22px;font-weight:500}"
        ".metric-sub{font-size:11px;color:#aaa;margin-top:2px}"
        ".card{background:#fff;border:1px solid #e8e8e4;border-radius:12px;padding:16px 20px;margin-bottom:12px}"
        ".rate-badge{font-size:11px;font-weight:500;padding:2px 8px;border-radius:6px;"
        "display:inline-block;margin-right:4px;white-space:nowrap}"
        ".rate-hi{background:#E1F5EE;color:#0F6E56}"
        ".rate-mid{background:#FFF8E1;color:#B07800}"
        ".rate-lo{background:#FDECEA;color:#C13A2A}"
        ".rate-na{background:#f1efe8;color:#aaa}"
        ".flag-badge{font-size:11px;font-weight:500;padding:3px 9px;border-radius:8px;"
        "display:inline-block;white-space:nowrap}"
        ".flag-on{background:#E1F5EE;color:#0F6E56}"
        ".flag-off{background:#f1efe8;color:#bbb}"
        ".rank-circle{width:26px;height:26px;border-radius:50%;display:inline-flex;"
        "align-items:center;justify-content:center;font-size:11px;font-weight:500;"
        "background:#EEEDFE;color:#3C3489;flex-shrink:0}"
        ".class-section{margin-bottom:20px}"
        ".class-header{display:flex;align-items:center;flex-wrap:wrap;gap:8px;margin-bottom:8px}"
        ".class-name{font-size:15px;font-weight:600}"
        ".race-cnt{font-size:12px;color:#888;background:#f5f5f0;padding:2px 8px;border-radius:8px}"
        ".flagged-cnt{font-size:12px;font-weight:600;color:#0F6E56}"
        ".hist-block{font-size:11px;color:#888;display:flex;align-items:center;"
        "gap:6px;flex-wrap:wrap;margin-left:4px}"
        ".race-card{background:#fff;border:1px solid #e8e8e4;border-radius:10px;"
        "margin-bottom:8px;overflow:hidden}"
        ".race-head{padding:9px 14px;border-bottom:1px solid #f0f0ec;display:flex;"
        "align-items:center;gap:10px;background:#fafaf7}"
        ".race-venue{font-size:12px;font-weight:700;color:#534AB7}"
        ".race-title{font-size:13px;font-weight:500}"
        ".race-date{font-size:11px;color:#888;margin-left:auto}"
        ".htable{width:100%;border-collapse:collapse}"
        ".htable th{font-size:11px;color:#888;font-weight:500;padding:6px 10px;"
        "text-align:left;border-bottom:1px solid #f0f0ec;background:#fafaf7;white-space:nowrap}"
        ".htable td{padding:7px 10px;border-bottom:1px solid #f5f5f0;vertical-align:middle}"
        ".htable tr:last-child td{border-bottom:none}"
        ".htable tr.flagged-row{background:#F7FFFC}"
        ".htable tr.flagged-row td{border-bottom-color:#e4f5ee}"
        ".cond-ok{color:#0F6E56;font-weight:600}"
        ".cond-ng{color:#ddd}"
        ".mono{font-family:ui-monospace,monospace;font-size:12px}"
        ".divider{border:none;border-top:1px solid #e8e8e4;margin:20px 0}"
        ".flag-pickup{margin-bottom:20px}"
        ".pickup-list{display:grid;gap:8px}"
        ".pickup-item{background:#fff;border:1px solid #d9efe6;border-radius:10px;"
        "padding:14px 18px;display:grid;grid-template-columns:auto 1fr auto;gap:14px;align-items:start}"
        ".pickup-badge{background:#0F6E56;color:#fff;font-size:11px;font-weight:600;"
        "padding:4px 10px;border-radius:8px;white-space:nowrap}"
        ".pickup-race{font-size:11px;color:#888;margin-bottom:3px}"
        ".pickup-horse{font-size:15px;font-weight:600;margin-bottom:4px}"
        ".pickup-detail{font-size:11px;color:#555;line-height:1.8}"
        ".pickup-hist{text-align:right;min-width:120px}"
        ".pickup-hist-label{font-size:10px;color:#aaa;margin-bottom:6px}"
        ".empty-note{text-align:center;padding:32px 16px;color:#aaa;font-size:12px;"
        "background:#fff;border:1px solid #e8e8e4;border-radius:10px}"
        ".info-box{padding:14px 18px;background:#f5f5f0;border-radius:8px;font-size:12px;"
        "color:#555;line-height:2;margin-top:16px}"
        ".info-box strong{color:#1a1a18}"
        "@media(max-width:640px){"
        ".metrics{grid-template-columns:repeat(2,1fr)}"
        ".pickup-item{grid-template-columns:1fr}"
        ".pickup-hist{text-align:left}}"
    )

    # ── 内部ビルダー ────────────────────────────────────────
    def hist_badges(cls: str) -> str:
        r = hist_rates.get(cls)
        if not r:
            return '<span style="font-size:11px;color:#aaa">(過去データなし)</span>'
        parts = [f'<span style="color:#aaa">{r["races"]}R実績:</span>']
        for label, key in [("あり単勝", "on_tan"), ("なし単勝", "off_tan")]:
            val = r.get(key, "---")
            parts.append(f'<span class="rate-badge {rate_cls(val)}">{label} {val}</span>')
        on_fk = r.get("on_fk", "---")
        if on_fk != "---":
            for label, key in [("あり複勝", "on_fk"), ("なし複勝", "off_fk")]:
                val = r.get(key, "---")
                parts.append(f'<span class="rate-badge {rate_cls(val)}">{label} {val}</span>')
        return f'<span class="hist-block">{"".join(parts)}</span>'

    def horse_table(horses: List[Dict]) -> str:
        rows = ""
        for h in sorted(horses, key=lambda x: x.get("馬番", "99") or "99"):
            flagged  = h["仮説フラグ"]
            row_cls  = ' class="flagged-row"' if flagged else ""
            c1 = '<span class="cond-ok">○</span>' if h["条件1"] else '<span class="cond-ng">×</span>'
            c2 = '<span class="cond-ok">○</span>' if h["条件2"] else '<span class="cond-ng">×</span>'
            badge = ('<span class="flag-badge flag-on">★ あり</span>'
                     if flagged else '<span class="flag-badge flag-off">なし</span>')
            num    = esc(h.get("馬番", "-") or "-")
            name   = esc(h.get("馬名", "-"))
            corner = esc(h.get("前走コーナー順", "---") or "---")
            r3f    = h.get("前走3F順位", "---") or "---"
            r3f_d  = esc(f"{r3f}位" if r3f not in ("---", "") else "---")
            nstyle = ' style="font-weight:600"' if flagged else ""
            rows += (
                f"<tr{row_cls}>"
                f"<td><span class=\"rank-circle\">{num}</span></td>"
                f"<td{nstyle}>{name}</td>"
                f"<td class=\"mono\">{corner}</td>"
                f"<td style=\"text-align:center\">{r3f_d}</td>"
                f"<td style=\"text-align:center\">{c1}</td>"
                f"<td style=\"text-align:center\">{c2}</td>"
                f"<td>{badge}</td>"
                f"</tr>"
            )
        return (
            '<div style="overflow-x:auto">'
            '<table class="htable">'
            "<thead><tr>"
            "<th>馬番</th><th>馬名</th><th>前走コーナー順</th>"
            "<th style=\"text-align:center\">前走3F</th>"
            "<th style=\"text-align:center\">条1</th>"
            "<th style=\"text-align:center\">条2</th>"
            "<th>フラグ</th>"
            "</tr></thead>"
            f"<tbody>{rows}</tbody>"
            "</table></div>"
        )

    def race_card(race: Dict) -> str:
        label = esc(race_label(race["race_id"]))
        title = esc(race["race_title"])
        rdate = esc(race["race_date"])
        return (
            '<div class="race-card">'
            '<div class="race-head">'
            f'<span class="race-venue">{label}</span>'
            f'<span class="race-title">{title}</span>'
            f'<span class="race-date">{rdate}</span>'
            "</div>"
            f"{horse_table(race['horses'])}"
            "</div>"
        )

    # ── フラグあり馬 ピックアップ ────────────────────────
    if flagged_all:
        items = ""
        for item in flagged_all:
            h     = item["horse"]
            cls   = item["cls"]
            race  = item["race"]
            lbl   = esc(race_label(race["race_id"]))
            title = esc(race["race_title"])
            rdate = esc(race["race_date"])
            corner = esc(h.get("前走コーナー順", "---") or "---")
            r3f    = esc(h.get("前走3F順位",   "---") or "---")
            prev_d = esc(h.get("前走日付",     "---") or "---")
            num    = esc(h.get("馬番", "-") or "-")
            name   = esc(h.get("馬名", "-"))
            hist   = hist_rates.get(cls)
            hist_html = ""
            if hist:
                on_t  = hist.get("on_tan",  "---")
                off_t = hist.get("off_tan", "---")
                hist_html = (
                    '<div class="pickup-hist">'
                    '<div class="pickup-hist-label">過去実績</div>'
                    f'<span class="rate-badge {rate_cls(on_t)}">あり単勝 {esc(on_t)}</span><br>'
                    f'<span style="font-size:10px;color:#888">vs なし {esc(off_t)}</span>'
                    "</div>"
                )
            items += (
                '<div class="pickup-item">'
                f'<div><span class="pickup-badge">★ {esc(cls)}</span></div>'
                "<div>"
                f'<div class="pickup-race">{lbl}&nbsp;&nbsp;{title}&nbsp;&nbsp;{rdate}</div>'
                f'<div class="pickup-horse">馬番{num}番&nbsp;&nbsp;{name}</div>'
                f'<div class="pickup-detail">'
                f"前走コーナー後退:&nbsp;{corner}&nbsp;&nbsp;"
                f"前走上がり3F:&nbsp;{r3f}位&nbsp;&nbsp;"
                f"前走日:&nbsp;{prev_d}"
                "</div>"
                "</div>"
                f"{hist_html}"
                "</div>"
            )
        pickup_section = (
            '<div class="flag-pickup">'
            f'<h2>★ フラグあり馬 ピックアップ&nbsp;（{total_flagged} 頭）</h2>'
            f'<div class="pickup-list">{items}</div>'
            "</div>"
        )
    else:
        pickup_section = (
            '<div class="flag-pickup">'
            '<h2>★ フラグあり馬 ピックアップ</h2>'
            '<div class="empty-note">フラグあり馬は見つかりませんでした</div>'
            "</div>"
        )

    # ── クラス別詳細 ────────────────────────────────────
    class_html = ""
    for cls in CLASS_ORDER:
        race_list = races_by_class.get(cls)
        if not race_list:
            continue
        flagged_n = sum(
            sum(1 for h in r["horses"] if h["仮説フラグ"]) for r in race_list
        )
        flagged_note = (
            f'<span class="flagged-cnt">★ {flagged_n}頭</span>' if flagged_n else ""
        )
        cards = "".join(race_card(r) for r in race_list)
        class_html += (
            '<div class="class-section">'
            '<div class="class-header">'
            f'<span class="class-name">{esc(cls)}</span>'
            f'<span class="race-cnt">{len(race_list)} レース</span>'
            f"{flagged_note}"
            f"{hist_badges(cls)}"
            "</div>"
            f"{cards}"
            "</div>"
        )

    if not class_html:
        class_html = '<div class="empty-note">レースデータがありません</div>'

    # ── 完全 HTML ──────────────────────────────────────
    html = f"""<!DOCTYPE html>
<html lang="ja">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>予想レポート {esc(date_label)}</title>
<style>{css}</style>
</head>
<body>
<nav>
  <div class="nav-inner">
    <span class="nav-brand">学習適応仮説</span>
    <div class="nav-links">
      <a href="/" class="nav-link active">予想</a>
      <a href="/history" class="nav-link">過去結果</a>
      <a href="/about" class="nav-link">説明</a>
      <a href="/update" class="nav-link nav-update">更新</a>
    </div>
  </div>
</nav>
<div class="app">

<h1>学習適応仮説 予想レポート<span class="ver-badge">{today_str} 生成</span></h1>
<p class="subtitle">対象: {esc(date_label)}&nbsp;&nbsp;参照データ: {esc(hist_csv)}（{total_hist} レース）</p>

<div class="metrics">
  <div class="metric">
    <div class="metric-label">対象レース</div>
    <div class="metric-val">{total_races}</div>
    <div class="metric-sub">{"・".join(d[:4]+"/"+d[4:6]+"/"+d[6:8] for d in dates)}</div>
  </div>
  <div class="metric">
    <div class="metric-label">出走頭数</div>
    <div class="metric-val">{total_horses}</div>
  </div>
  <div class="metric">
    <div class="metric-label">フラグあり</div>
    <div class="metric-val" style="color:#0F6E56">{total_flagged}</div>
    <div class="metric-sub">全体の {flag_pct}%</div>
  </div>
  <div class="metric">
    <div class="metric-label">参照レース数</div>
    <div class="metric-val" style="color:#534AB7">{total_hist}</div>
    <div class="metric-sub">{esc(hist_csv)}</div>
  </div>
</div>

{pickup_section}

<hr class="divider">

<h2>クラス別 詳細</h2>
{class_html}

<div class="info-box">
  <strong>判定ルール&nbsp;</strong>
  条件1: 前走コーナー通過順位が途中で下がっている（例 2‑3‑5‑6 → ○ / 5‑4‑3‑2 → ×）&nbsp;&nbsp;
  条件2: 前走上がり3F が前走メンバー内3位以内&nbsp;&nbsp;→ 両方満たす馬に「学習フラグあり」を付与<br>
  回収率の色分け:&nbsp;
  <span class="rate-badge rate-hi">100%以上</span>
  <span class="rate-badge rate-mid">80〜99%</span>
  <span class="rate-badge rate-lo">80%未満</span>
</div>

</div>
</body>
</html>"""

    if filepath:
        with open(filepath, "w", encoding="utf-8") as f:
            f.write(html)
        print(f"HTML レポート生成完了: {filepath}", file=sys.stderr)
    return html


# ── 説明ページ生成 ───────────────────────────────────────────

def build_about_page() -> str:
    """説明ページの HTML を生成"""

    css = (
        "*{box-sizing:border-box;margin:0;padding:0;"
        "font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif}"
        "body{background:#f5f5f0;padding:0;color:#1a1a18;font-size:14px;line-height:1.7}"
        "nav{background:#fff;border-bottom:1px solid #e8e8e4;padding:0 16px;"
        "position:sticky;top:0;z-index:100}"
        ".nav-inner{max-width:860px;margin:0 auto;display:flex;align-items:center;"
        "height:44px;gap:12px}"
        ".nav-brand{font-size:13px;font-weight:600;color:#534AB7}"
        ".nav-links{display:flex;gap:4px;margin-left:auto}"
        ".nav-link{padding:5px 12px;border-radius:6px;text-decoration:none;"
        "font-size:13px;color:#555;white-space:nowrap}"
        ".nav-link:hover{background:#f5f5f0;color:#1a1a18}"
        ".nav-link.active{background:#EEEDFE;color:#534AB7;font-weight:500}"
        ".nav-update{background:#534AB7!important;color:#fff!important;font-weight:500}"
        ".nav-update:hover{background:#3C3489!important}"
        ".app{max-width:860px;margin:0 auto;padding:40px 16px 60px}"
        # hero
        ".hero{margin-bottom:48px}"
        ".hero-label{font-size:11px;font-weight:600;letter-spacing:.08em;"
        "color:#534AB7;text-transform:uppercase;margin-bottom:10px}"
        ".hero-title{font-size:28px;font-weight:600;line-height:1.3;margin-bottom:14px}"
        ".hero-sub{font-size:15px;color:#555;max-width:560px;line-height:1.8}"
        # sections
        ".section{margin-bottom:40px}"
        ".section-num{display:inline-block;width:28px;height:28px;border-radius:50%;"
        "background:#534AB7;color:#fff;font-size:12px;font-weight:700;"
        "text-align:center;line-height:28px;flex-shrink:0;margin-top:3px}"
        ".section-head{display:flex;align-items:flex-start;gap:12px;margin-bottom:16px}"
        ".section-title{font-size:18px;font-weight:600;line-height:1.4}"
        ".section-body{padding-left:40px}"
        ".section-body p{color:#333;margin-bottom:12px}"
        ".section-body p:last-child{margin-bottom:0}"
        # card inside section
        ".inner-card{background:#fff;border:1px solid #e8e8e4;border-radius:12px;"
        "padding:20px 24px;margin-bottom:16px}"
        ".inner-card:last-child{margin-bottom:0}"
        ".inner-card-title{font-size:13px;font-weight:600;color:#534AB7;margin-bottom:10px}"
        # hypothesis box
        ".hypo-box{background:#F4F3FE;border:1px solid #c9c5e8;border-radius:12px;"
        "padding:20px 24px;margin-bottom:16px}"
        ".hypo-cond{display:flex;align-items:flex-start;gap:10px;margin-bottom:10px}"
        ".hypo-cond:last-child{margin-bottom:0}"
        ".cond-num{display:inline-block;width:22px;height:22px;border-radius:50%;"
        "background:#534AB7;color:#fff;font-size:11px;font-weight:700;"
        "text-align:center;line-height:22px;flex-shrink:0;margin-top:2px}"
        ".cond-text{font-size:14px;color:#1a1a18;line-height:1.6}"
        ".cond-text strong{color:#534AB7}"
        # why box
        ".why-item{display:flex;gap:14px;margin-bottom:14px;align-items:flex-start}"
        ".why-item:last-child{margin-bottom:0}"
        ".why-icon{font-size:18px;flex-shrink:0;width:26px;text-align:center;margin-top:1px}"
        ".why-text{font-size:14px;color:#333;line-height:1.7}"
        ".why-text strong{color:#1a1a18;font-weight:600}"
        # disclaimer
        ".disclaimer{background:#fff;border:1px solid #e8e8e4;border-radius:12px;"
        "padding:20px 24px}"
        ".disclaimer-title{font-size:12px;font-weight:600;color:#888;letter-spacing:.06em;"
        "text-transform:uppercase;margin-bottom:12px}"
        ".disclaimer p{font-size:13px;color:#666;line-height:1.8;margin-bottom:8px}"
        ".disclaimer p:last-child{margin-bottom:0}"
        # divider
        ".divider{border:none;border-top:1px solid #e8e8e4;margin:40px 0}"
        # tag
        ".tag{display:inline-block;font-size:11px;font-weight:500;padding:3px 9px;"
        "border-radius:6px;background:#EEEDFE;color:#534AB7;margin-right:6px;margin-bottom:6px}"
        ".tag-green{background:#E1F5EE;color:#0F6E56}"
        ".rate-badge{font-size:11px;font-weight:500;padding:2px 8px;border-radius:6px;"
        "display:inline-block;margin-right:4px}"
        ".rate-hi{background:#E1F5EE;color:#0F6E56}"
        "@media(max-width:640px){.hero-title{font-size:22px}.section-body{padding-left:0}"
        ".section-head{flex-wrap:wrap}}"
    )

    return f"""<!DOCTYPE html>
<html lang="ja">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>説明 — 学習適応仮説 予想AI</title>
<style>{css}</style>
</head>
<body>

<nav>
  <div class="nav-inner">
    <span class="nav-brand">学習適応仮説</span>
    <div class="nav-links">
      <a href="/" class="nav-link">予想</a>
      <a href="/history" class="nav-link">過去結果</a>
      <a href="/about" class="nav-link active">説明</a>
      <a href="/update" class="nav-link nav-update">更新</a>
    </div>
  </div>
</nav>

<div class="app">

  <!-- ヒーロー -->
  <div class="hero">
    <div class="hero-label">About this tool</div>
    <h1 class="hero-title">競馬の暗黙知を<br>数値化する試み</h1>
    <p class="hero-sub">
      このツールは「記号創発システム論」という認知科学の理論を競馬に応用し、
      馬が<strong>「競馬を覚えた」瞬間</strong>を統計的に捉えようとする実験的な予想システムです。
    </p>
  </div>

  <!-- 1. この予想AIとは -->
  <div class="section">
    <div class="section-head">
      <span class="section-num">1</span>
      <h2 class="section-title">この予想AIとは何か</h2>
    </div>
    <div class="section-body">
      <div class="inner-card">
        <div class="inner-card-title">記号創発システム論から生まれた</div>
        <p>
          記号創発システム論とは、言語や概念が環境との相互作用を通じて自律的に生まれる
          プロセスを記述する理論です。競走馬もまたレースを経験するなかで
          「どう走ればよいか」という暗黙的な知識を身につけると考えます。
        </p>
        <p>
          このツールはその「学習の瞬間」を、レース結果のデータから検出しようとするものです。
        </p>
      </div>
      <div class="inner-card">
        <div class="inner-card-title">競馬の暗黙知を数値化する</div>
        <p>
          熟練した調教師や騎手は「この馬はそろそろ走る」という直感を持ちます。
          その直感の一部は言語化・数値化できる可能性があります。
          前走のコーナー通過順と上がり3Fタイムはその候補です。
        </p>
        <span class="tag">記号創発システム論</span>
        <span class="tag">暗黙知</span>
        <span class="tag tag-green">データ駆動</span>
      </div>
    </div>
  </div>

  <hr class="divider">

  <!-- 2. 学習適応仮説とは -->
  <div class="section">
    <div class="section-head">
      <span class="section-num">2</span>
      <h2 class="section-title">学習適応仮説とは</h2>
    </div>
    <div class="section-body">
      <p style="margin-bottom:16px;color:#555">
        以下の2条件を<strong>両方</strong>満たす馬を「学習フラグあり」と判定します。
        これらの馬は<em>競馬を覚えた可能性が高く</em>、次走で好走しやすいと仮説を立てています。
      </p>
      <div class="hypo-box">
        <div class="hypo-cond">
          <span class="cond-num">1</span>
          <div class="cond-text">
            <strong>前走のコーナー通過順位が途中で下がった</strong><br>
            例：2→3→5→6（後退あり） ✓　／　5→4→3→2（前進のみ） ✗
          </div>
        </div>
        <div class="hypo-cond">
          <span class="cond-num">2</span>
          <div class="cond-text">
            <strong>前走の上がり3Fが前走メンバー内3位以内だった</strong><br>
            同じレースに出走した馬の中で、最後の600mが速かった馬
          </div>
        </div>
      </div>
      <p style="color:#555;font-size:13px">
        ※ 判定はすべて<strong>前走</strong>のデータに基づきます。
        出馬表が公開されたタイミング（通常レース前日〜木曜）に取得・更新されます。
      </p>
    </div>
  </div>

  <hr class="divider">

  <!-- 3. なぜこの条件なのか -->
  <div class="section">
    <div class="section-head">
      <span class="section-num">3</span>
      <h2 class="section-title">なぜこの条件なのか</h2>
    </div>
    <div class="section-body">
      <div class="inner-card">
        <div class="why-item">
          <div class="why-icon">📉</div>
          <div class="why-text">
            <strong>単に順位を下げた馬は弱い可能性がある</strong><br>
            コーナーで後退するだけでは、単なる実力不足や不利を示しているだけかもしれません。
            それだけでは何も言えません。
          </div>
        </div>
        <div class="why-item">
          <div class="why-icon">⚡</div>
          <div class="why-text">
            <strong>しかし上がりが速ければ末脚を温存した証拠</strong><br>
            一方で上がり3Fがメンバー内3位以内なら、後退は「負け」ではなく
            「末脚のためにエネルギーを溜めた」行動だった可能性があります。
          </div>
        </div>
        <div class="why-item">
          <div class="why-icon">🧠</div>
          <div class="why-text">
            <strong>これが暗黙知として機能する</strong><br>
            競走馬はレースを繰り返すなかで「前半に位置を下げて末脚を爆発させる」
            という走り方を覚えます。この行動パターンが確立された馬は、次走で
            同じ戦略をより洗練された形で実行できると考えます。
            これが「競馬を覚えた」状態であり、本仮説が検出しようとする現象です。
          </div>
        </div>
      </div>
    </div>
  </div>

  <hr class="divider">

  <!-- 4. 免責事項 -->
  <div class="section">
    <div class="section-head">
      <span class="section-num">4</span>
      <h2 class="section-title">免責事項</h2>
    </div>
    <div class="section-body">
      <div class="disclaimer">
        <div class="disclaimer-title">Disclaimer</div>
        <p>
          本ツールは<strong>研究・学習目的</strong>で作成されたものです。
          競馬の予想結果を保証するものではありません。
        </p>
        <p>
          馬券の購入・投資判断はご自身の判断と責任のもとで行ってください。
          本ツールの利用によって生じたいかなる損失についても、開発者は責任を負いません。
        </p>
        <p>
          競馬はギャンブルです。ご利用は適切な範囲でお願いします。
        </p>
      </div>
    </div>
  </div>

</div>
</body>
</html>"""


# ── 過去結果ページ生成 ────────────────────────────────────────

def build_history_page(csv_path: str = DEFAULT_HIST) -> str:
    """過去結果ページの HTML を生成（クラス別回収率 + レース一覧）"""
    import csv as _csv_mod
    from collections import defaultdict as _dd

    e = _html.escape

    def pct(r: int, i: int) -> str:
        return f"{r / i * 100:.1f}%" if i else "---"

    def rc(s: str) -> str:
        if s == "---": return "rate-na"
        try:
            v = float(s.rstrip("%"))
            return "rate-hi" if v >= 100 else "rate-mid" if v >= 80 else "rate-lo"
        except ValueError:
            return "rate-na"

    # ── データ読み込み ───────────────────────────────────
    try:
        with open(csv_path, encoding="utf-8-sig") as f:
            rows = list(_csv_mod.DictReader(f))
    except FileNotFoundError:
        return _error_page(f"データファイルが見つかりません: {csv_path}")
    if not rows:
        return _error_page("データがありません")

    has_fuku = "複勝配当" in rows[0]

    race_groups: Dict[str, list] = _dd(list)
    for r in rows:
        race_groups[r["race_id"]].append(r)

    # ── クラス別集計 ─────────────────────────────────────
    class_stats: Dict[str, dict] = {}
    class_races:  Dict[str, list] = _dd(list)

    for race_id, horses in sorted(race_groups.items()):
        cls = classify(horses[0]["race_title"])
        if cls not in class_stats:
            class_stats[cls] = dict(
                on_tan_i=0, on_tan_r=0, off_tan_i=0, off_tan_r=0,
                on_fk_i=0,  on_fk_r=0,  off_fk_i=0,  off_fk_r=0,
                on_count=0, off_count=0, race_count=0, tan_hits_on=0,
            )
        d = class_stats[cls]
        d["race_count"] += 1

        winner  = next((h for h in horses if h.get("着順") == "1"), None)
        on_grp  = [h for h in horses if h.get("仮説フラグ") == "True"]
        off_grp = [h for h in horses if h.get("仮説フラグ") == "False"]
        d["on_count"]  += len(on_grp)
        d["off_count"] += len(off_grp)

        tan_hit_on = bool(winner and winner.get("仮説フラグ") == "True")
        if tan_hit_on:
            d["tan_hits_on"] += 1

        for grp, pfx, flag_str in [(on_grp, "on", "True"), (off_grp, "off", "False")]:
            if not grp:
                continue
            inv = len(grp) * 100
            d[f"{pfx}_tan_i"] += inv
            if winner and winner.get("仮説フラグ") == flag_str:
                try:
                    d[f"{pfx}_tan_r"] += round(float(winner["単勝オッズ"]) * 100)
                except (ValueError, TypeError):
                    pass
            if has_fuku:
                d[f"{pfx}_fk_i"] += inv
                for h in grp:
                    try:
                        d[f"{pfx}_fk_r"] += int(h.get("複勝配当", 0) or 0)
                    except (ValueError, TypeError):
                        pass

        def _sort_key(h: dict) -> int:
            o = h.get("着順", "99")
            return int(o) if str(o).isdigit() else 99

        class_races[cls].append({
            "race_id":    race_id,
            "race_title": horses[0]["race_title"],
            "race_date":  horses[0]["race_date"],
            "on_count":   len(on_grp),
            "tan_hit_on": tan_hit_on,
            "horses":     sorted(horses, key=_sort_key),
        })

    # ── 集計サマリー ─────────────────────────────────────
    total_races    = len(race_groups)
    total_horses   = len(rows)
    total_on       = sum(d["on_count"]     for d in class_stats.values())
    total_tan_hits = sum(d["tan_hits_on"]  for d in class_stats.values())
    on_pct = f"{total_on / total_horses * 100:.1f}" if total_horses else "0"

    # ── 全クラス合算回収率 ─────────────────────────────
    all_on_ti = sum(d["on_tan_i"]  for d in class_stats.values())
    all_on_tr = sum(d["on_tan_r"]  for d in class_stats.values())
    all_off_ti = sum(d["off_tan_i"] for d in class_stats.values())
    all_off_tr = sum(d["off_tan_r"] for d in class_stats.values())
    global_on_tan  = pct(all_on_tr,  all_on_ti)
    global_off_tan = pct(all_off_tr, all_off_ti)

    # ── CSS ─────────────────────────────────────────────
    css = (
        "*{box-sizing:border-box;margin:0;padding:0;"
        "font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif}"
        "body{background:#f5f5f0;padding:0;color:#1a1a18;font-size:13px;line-height:1.5}"
        "nav{background:#fff;border-bottom:1px solid #e8e8e4;padding:0 16px;"
        "position:sticky;top:0;z-index:100}"
        ".nav-inner{max-width:980px;margin:0 auto;display:flex;align-items:center;"
        "height:44px;gap:12px}"
        ".nav-brand{font-size:13px;font-weight:600;color:#534AB7}"
        ".nav-links{display:flex;gap:4px;margin-left:auto}"
        ".nav-link{padding:5px 12px;border-radius:6px;text-decoration:none;"
        "font-size:13px;color:#555;white-space:nowrap}"
        ".nav-link:hover{background:#f5f5f0;color:#1a1a18}"
        ".nav-link.active{background:#EEEDFE;color:#534AB7;font-weight:500}"
        ".nav-update{background:#534AB7!important;color:#fff!important;font-weight:500}"
        ".nav-update:hover{background:#3C3489!important}"
        ".app{max-width:980px;margin:0 auto;padding:20px 16px}"
        "h1{font-size:18px;font-weight:500;margin-bottom:4px}"
        "h2{font-size:14px;font-weight:600;margin-bottom:12px;color:#534AB7}"
        ".subtitle{font-size:12px;color:#888;margin-bottom:20px}"
        ".ver-badge{display:inline-block;font-size:10px;padding:2px 8px;"
        "background:#EEEDFE;color:#534AB7;border-radius:6px;margin-left:8px;vertical-align:middle}"
        ".metrics{display:grid;grid-template-columns:repeat(4,1fr);gap:10px;margin-bottom:20px}"
        ".metric{background:#fff;border:1px solid #e8e8e4;border-radius:10px;padding:12px 14px}"
        ".metric-label{font-size:11px;color:#888;margin-bottom:4px}"
        ".metric-val{font-size:22px;font-weight:500}"
        ".metric-sub{font-size:11px;color:#aaa;margin-top:2px}"
        ".card{background:#fff;border:1px solid #e8e8e4;border-radius:12px;"
        "padding:16px 20px;margin-bottom:16px}"
        ".rate-badge{font-size:11px;font-weight:500;padding:2px 8px;border-radius:6px;"
        "display:inline-block;margin-right:4px;white-space:nowrap}"
        ".rate-hi{background:#E1F5EE;color:#0F6E56}"
        ".rate-mid{background:#FFF8E1;color:#B07800}"
        ".rate-lo{background:#FDECEA;color:#C13A2A}"
        ".rate-na{background:#f1efe8;color:#aaa}"
        ".divider{border:none;border-top:1px solid #e8e8e4;margin:20px 0}"
        ".class-section{margin-bottom:20px}"
        ".class-header{display:flex;align-items:center;flex-wrap:wrap;gap:8px;margin-bottom:8px}"
        ".class-name{font-size:15px;font-weight:600}"
        ".race-cnt{font-size:12px;color:#888;background:#f5f5f0;padding:2px 8px;border-radius:8px}"
        # stat table
        ".stbl{width:100%;border-collapse:collapse}"
        ".stbl th{font-size:11px;color:#888;font-weight:500;padding:7px 12px;"
        "border-bottom:2px solid #e8e8e4;white-space:nowrap;background:#fafaf7}"
        ".stbl th.r,.stbl td.r{text-align:right}"
        ".stbl td{padding:8px 12px;border-bottom:1px solid #f5f5f0;vertical-align:middle}"
        ".stbl tr:last-child td{border-bottom:none}"
        ".stbl tr:hover td{background:#fafaf8}"
        ".stbl tr.total-row td{border-top:2px solid #e8e8e4;font-weight:600;"
        "background:#fafaf7}"
        ".stbl .grp-hi{background:#e9f8f0;font-size:10px;padding:1px 6px;"
        "border-radius:4px;color:#0F6E56;font-weight:600}"
        ".stbl .grp-lo{background:#f5f5f0;font-size:10px;padding:1px 6px;"
        "border-radius:4px;color:#888}"
        # accordion
        "details{background:#fff;border:1px solid #e8e8e4;border-radius:10px;"
        "margin-bottom:6px;overflow:hidden}"
        "details[open]{border-color:#c9c5e8}"
        "summary{padding:10px 14px;cursor:pointer;list-style:none;display:flex;"
        "align-items:center;gap:10px;user-select:none;background:#fafaf7}"
        "summary::-webkit-details-marker{display:none}"
        "details[open]>summary{background:#F4F3FE;border-bottom:1px solid #e8e8e4}"
        "summary:hover{background:#f0eff9}"
        ".chevron{font-size:10px;color:#bbb;transition:transform .15s;flex-shrink:0;"
        "margin-right:2px}"
        "details[open] .chevron{transform:rotate(90deg)}"
        ".rv{font-size:12px;font-weight:700;color:#534AB7}"
        ".rt{font-size:13px;font-weight:500}"
        ".rd{font-size:11px;color:#888}"
        ".rmeta{display:flex;align-items:center;gap:6px;margin-left:auto;flex-wrap:wrap}"
        ".on-badge{font-size:11px;font-weight:600;padding:2px 8px;border-radius:6px;"
        "background:#E1F5EE;color:#0F6E56}"
        ".win-flag{font-size:11px;font-weight:600;padding:2px 8px;border-radius:6px;"
        "background:#FFF8E1;color:#B07800}"
        # result horse table
        ".htable{width:100%;border-collapse:collapse}"
        ".htable th{font-size:11px;color:#888;font-weight:500;padding:6px 10px;"
        "text-align:left;border-bottom:1px solid #f0f0ec;background:#fafaf7;white-space:nowrap}"
        ".htable th.r,.htable td.r{text-align:right}"
        ".htable td{padding:7px 10px;border-bottom:1px solid #f5f5f0;vertical-align:middle}"
        ".htable tr:last-child td{border-bottom:none}"
        ".rank-circle{width:24px;height:24px;border-radius:50%;display:inline-flex;"
        "align-items:center;justify-content:center;font-size:11px;font-weight:600;"
        "background:#EEEDFE;color:#3C3489;flex-shrink:0}"
        ".rank-win{background:#FFE082;color:#7A5800}"
        ".mono{font-family:ui-monospace,monospace;font-size:12px}"
        ".flag-badge{font-size:11px;font-weight:500;padding:2px 8px;border-radius:8px;"
        "display:inline-block;white-space:nowrap}"
        ".flag-on{background:#E1F5EE;color:#0F6E56}"
        ".flag-off{background:#f1efe8;color:#bbb}"
        ".tr-win{background:#FFFBEB}"
        ".tr-flag{background:#F7FFFC}"
        ".tr-winflag{background:#DFFBEE}"
        ".empty-note{text-align:center;padding:32px;color:#aaa;font-size:12px;"
        "background:#fff;border:1px solid #e8e8e4;border-radius:10px}"
        "@media(max-width:640px){.metrics{grid-template-columns:repeat(2,1fr)}"
        ".rmeta{display:none}"
        ".stbl th:nth-child(n+4),.stbl td:nth-child(n+4){display:none}}"
    )

    # ── クラス別集計テーブル ─────────────────────────────
    stat_rows = ""
    tot = dict(on_ti=0, on_tr=0, off_ti=0, off_tr=0,
               on_fi=0, on_fr=0, off_fi=0, off_fr=0,
               on_c=0, off_c=0)

    for cls in CLASS_ORDER:
        d = class_stats.get(cls)
        if not d:
            continue
        on_t  = pct(d["on_tan_r"],  d["on_tan_i"])
        off_t = pct(d["off_tan_r"], d["off_tan_i"])
        on_f  = pct(d["on_fk_r"],   d["on_fk_i"])  if has_fuku else "---"
        off_f = pct(d["off_fk_r"],  d["off_fk_i"]) if has_fuku else "---"
        stat_rows += (
            f'<tr>'
            f'<td>{e(cls)}</td>'
            f'<td class="r">{d["race_count"]}</td>'
            f'<td class="r">{d["on_count"]}</td>'
            f'<td class="r"><span class="rate-badge {rc(on_t)}">{on_t}</span></td>'
            f'<td class="r"><span class="rate-badge {rc(on_f)}">{on_f}</span></td>'
            f'<td class="r">{d["off_count"]}</td>'
            f'<td class="r"><span class="rate-badge {rc(off_t)}">{off_t}</span></td>'
            f'<td class="r"><span class="rate-badge {rc(off_f)}">{off_f}</span></td>'
            f'</tr>'
        )
        tot["on_c"]  += d["on_count"]
        tot["off_c"] += d["off_count"]
        for k in ("on_ti","on_tr","off_ti","off_tr"):
            tot[k] += d[f"{k.replace('ti','tan_i').replace('tr','tan_r')}"]
        if has_fuku:
            for k in ("on_fi","on_fr","off_fi","off_fr"):
                tot[k] += d[f"{k.replace('fi','fk_i').replace('fr','fk_r')}"]

    tot_on_t  = pct(tot["on_tr"],  tot["on_ti"])
    tot_off_t = pct(tot["off_tr"], tot["off_ti"])
    tot_on_f  = pct(tot["on_fr"],  tot["on_fi"]) if has_fuku else "---"
    tot_off_f = pct(tot["off_fr"], tot["off_fi"]) if has_fuku else "---"
    stat_rows += (
        f'<tr class="total-row">'
        f'<td>合計</td>'
        f'<td class="r">{total_races}</td>'
        f'<td class="r">{tot["on_c"]}</td>'
        f'<td class="r"><span class="rate-badge {rc(tot_on_t)}">{tot_on_t}</span></td>'
        f'<td class="r"><span class="rate-badge {rc(tot_on_f)}">{tot_on_f}</span></td>'
        f'<td class="r">{tot["off_c"]}</td>'
        f'<td class="r"><span class="rate-badge {rc(tot_off_t)}">{tot_off_t}</span></td>'
        f'<td class="r"><span class="rate-badge {rc(tot_off_f)}">{tot_off_f}</span></td>'
        f'</tr>'
    )

    stat_table = (
        '<div class="card">'
        '<h2>クラス別 回収率集計</h2>'
        '<div style="overflow-x:auto">'
        '<table class="stbl">'
        '<thead><tr>'
        '<th>クラス</th><th class="r">R数</th>'
        '<th class="r" colspan="3" style="text-align:center;background:#e9f8f0;color:#0F6E56">'
        '━━ フラグあり ━━</th>'
        '<th class="r" colspan="3" style="text-align:center;background:#f5f5f0;color:#888">'
        '━━ フラグなし ━━</th>'
        '</tr>'
        '<tr>'
        '<th></th><th></th>'
        '<th class="r">頭数</th><th class="r">単勝回収率</th><th class="r">複勝回収率</th>'
        '<th class="r">頭数</th><th class="r">単勝回収率</th><th class="r">複勝回収率</th>'
        '</tr></thead>'
        f'<tbody>{stat_rows}</tbody>'
        '</table></div></div>'
    )

    # ── レース一覧（クラス別アコーディオン） ──────────────
    def result_horse_table(horses: list) -> str:
        rows = ""
        for h in horses:
            flag   = h.get("仮説フラグ") == "True"
            rank_s = h.get("着順", "")
            win    = rank_s == "1"
            if win and flag:
                tr_cls = ' class="tr-winflag"'
            elif win:
                tr_cls = ' class="tr-win"'
            elif flag:
                tr_cls = ' class="tr-flag"'
            else:
                tr_cls = ""
            rk_cls  = "rank-win" if win else "rank-circle"
            badge   = ('<span class="flag-badge flag-on">★ あり</span>'
                       if flag else '<span class="flag-badge flag-off">なし</span>')
            num     = e(h.get("馬番", "-") or "-")
            name    = e(h.get("馬名",   "-"))
            corner  = e(h.get("コーナー通過順", "---") or "---")
            f3      = e(h.get("上がり3F",  "---") or "---")
            odds    = e(h.get("単勝オッズ", "---") or "---")
            fuku    = e(h.get("複勝配当", "---") or "---") if has_fuku else ""
            nstyle  = ' style="font-weight:600"' if (win or flag) else ""
            fuku_td = f'<td class="r mono">{fuku}</td>' if has_fuku else ""
            rows += (
                f'<tr{tr_cls}>'
                f'<td><span class="{rk_cls}">{e(rank_s) or "-"}</span></td>'
                f'<td class="r">{num}</td>'
                f'<td{nstyle}>{name}</td>'
                f'<td class="mono">{corner}</td>'
                f'<td class="r mono">{f3}</td>'
                f'<td class="r mono">{odds}</td>'
                f'{fuku_td}'
                f'<td>{badge}</td>'
                f'</tr>'
            )
        fuku_th = '<th class="r">複勝配当</th>' if has_fuku else ""
        return (
            '<div style="overflow-x:auto">'
            '<table class="htable">'
            '<thead><tr>'
            '<th>着順</th><th class="r">馬番</th><th>馬名</th>'
            '<th>コーナー</th><th class="r">上がり3F</th>'
            f'<th class="r">単勝オッズ</th>{fuku_th}<th>フラグ</th>'
            '</tr></thead>'
            f'<tbody>{rows}</tbody>'
            '</table></div>'
        )

    race_list_html = ""
    for cls in CLASS_ORDER:
        races = class_races.get(cls)
        if not races:
            continue
        d = class_stats[cls]
        on_t  = pct(d["on_tan_r"],  d["on_tan_i"])
        off_t = pct(d["off_tan_r"], d["off_tan_i"])
        on_f  = pct(d["on_fk_r"],   d["on_fk_i"])  if has_fuku else "---"

        rate_badges = (
            f'<span class="rate-badge {rc(on_t)}" style="font-size:11px">あり単勝 {on_t}</span>'
            f'<span class="rate-badge {rc(on_f)}" style="font-size:11px">あり複勝 {on_f}</span>'
            f'<span class="rate-badge rate-na" style="font-size:11px">なし単勝 {off_t}</span>'
        )

        race_details = ""
        for race in races:
            lbl   = e(race_label(race["race_id"]))
            title = e(race["race_title"])
            rdate = e(race["race_date"])
            on_n  = race["on_count"]
            hit   = race["tan_hit_on"]

            on_html  = (f'<span class="on-badge">★ {on_n}頭</span>' if on_n else "")
            win_html = ('<span class="win-flag">★ 単勝的中</span>' if hit else "")

            race_details += (
                f'<details>'
                f'<summary>'
                f'<span class="chevron">▶</span>'
                f'<span class="rv">{lbl}</span>'
                f'<span class="rt">{title}</span>'
                f'<div class="rmeta">{on_html}{win_html}'
                f'<span class="rd">{rdate}</span></div>'
                f'</summary>'
                f'{result_horse_table(race["horses"])}'
                f'</details>'
            )

        race_list_html += (
            f'<div class="class-section">'
            f'<div class="class-header">'
            f'<span class="class-name">{e(cls)}</span>'
            f'<span class="race-cnt">{len(races)} レース</span>'
            f'{rate_badges}'
            f'</div>'
            f'{race_details}'
            f'</div>'
        )

    if not race_list_html:
        race_list_html = '<div class="empty-note">データがありません</div>'

    # ── 完全 HTML ────────────────────────────────────────
    today_str = date.today().strftime("%Y/%m/%d")
    return f"""<!DOCTYPE html>
<html lang="ja">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>過去結果 — {e(csv_path)}</title>
<style>{css}</style>
</head>
<body>
<nav>
  <div class="nav-inner">
    <span class="nav-brand">学習適応仮説</span>
    <div class="nav-links">
      <a href="/" class="nav-link">予想</a>
      <a href="/history" class="nav-link active">過去結果</a>
      <a href="/about" class="nav-link">説明</a>
      <a href="/update" class="nav-link nav-update">更新</a>
    </div>
  </div>
</nav>
<div class="app">

<h1>過去結果<span class="ver-badge">{e(csv_path)}</span></h1>
<p class="subtitle">{today_str} 閲覧&nbsp;&nbsp;全クラス 単勝回収率: フラグあり
<span class="rate-badge {rc(global_on_tan)}">{global_on_tan}</span>
/ フラグなし <span class="rate-badge {rc(global_off_tan)}">{global_off_tan}</span></p>

<div class="metrics">
  <div class="metric">
    <div class="metric-label">集計レース数</div>
    <div class="metric-val">{total_races}</div>
  </div>
  <div class="metric">
    <div class="metric-label">出走頭数</div>
    <div class="metric-val">{total_horses}</div>
  </div>
  <div class="metric">
    <div class="metric-label">フラグあり</div>
    <div class="metric-val" style="color:#0F6E56">{total_on}</div>
    <div class="metric-sub">全体の {on_pct}%</div>
  </div>
  <div class="metric">
    <div class="metric-label">単勝的中（あり）</div>
    <div class="metric-val" style="color:#534AB7">{total_tan_hits}</div>
    <div class="metric-sub">{total_races} レース中</div>
  </div>
</div>

{stat_table}

<hr class="divider">

<h2>レース一覧</h2>
{race_list_html}

</div>
</body>
</html>"""


# ── Flask アプリ ──────────────────────────────────────────────

app = Flask(__name__)

_html_cache    = ""
_last_updated  = ""
_update_status = "idle"   # "idle" | "running" | "done" | "error"
_update_error  = ""
_update_lock   = threading.Lock()


def _do_update(hist_csv: str, dates: List[str]) -> None:
    """バックグラウンドで出馬表を取得して予想HTMLを更新する"""
    global _html_cache, _last_updated, _update_status, _update_error
    try:
        print(f"[update] 対象日付: {dates}", file=sys.stderr)
        hist_rates, total_hist = load_hist_rates(hist_csv)
        print(f"[update] 過去実績: {total_hist} レース", file=sys.stderr)

        all_race_ids: List[str] = []
        for d in dates:
            all_race_ids.extend(fetch_race_ids_for_date(d))

        if not all_race_ids:
            _update_status = "error"
            _update_error  = "出馬表未公開（木曜以降に再実行してください）"
            print(f"[update] {_update_error}", file=sys.stderr)
            return

        races_by_class: Dict[str, List[Dict]] = defaultdict(list)
        n = len(all_race_ids)
        for i, race_id in enumerate(all_race_ids, 1):
            print(f"[update] [{i}/{n}] {race_id} ({race_label(race_id)})", file=sys.stderr)
            sys.stderr.flush()
            result = fetch_shutuba(race_id)
            if result is None:
                continue
            race_title, race_date, horses = result
            if not horses:
                continue
            horses = add_prediction_flags(horses, race_date)
            cls    = classify(race_title)
            races_by_class[cls].append({
                "race_id":    race_id,
                "race_title": race_title,
                "race_date":  race_date,
                "horses":     horses,
            })

        save_log(races_by_class, "yosou_log.csv")

        _html_cache   = generate_html_report(
            races_by_class, hist_rates, dates, hist_csv, total_hist,
            filepath=None,
        )
        _last_updated  = date.today().strftime("%Y/%m/%d %H:%M")
        _update_status = "done"
        print("[update] 完了", file=sys.stderr)

    except Exception as e:
        _update_status = "error"
        _update_error  = str(e)
        print(f"[update] エラー: {e}", file=sys.stderr)


def _updating_page() -> str:
    return """<!DOCTYPE html>
<html lang="ja">
<head>
<meta charset="UTF-8">
<meta http-equiv="refresh" content="10; url=/">
<title>更新中...</title>
<style>
*{box-sizing:border-box;margin:0;padding:0}
body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif;
background:#f5f5f0;display:flex;align-items:center;justify-content:center;
min-height:100vh;color:#1a1a18}
.box{text-align:center;background:#fff;border:1px solid #e8e8e4;
border-radius:12px;padding:48px 64px}
h2{color:#534AB7;font-size:18px;font-weight:500;margin-bottom:10px}
p{color:#888;font-size:13px;line-height:1.8}
.spinner{width:44px;height:44px;border:3px solid #EEEDFE;border-top-color:#534AB7;
border-radius:50%;animation:spin .8s linear infinite;margin:0 auto 24px}
@keyframes spin{to{transform:rotate(360deg)}}
</style>
</head>
<body>
<div class="box">
  <div class="spinner"></div>
  <h2>データ取得中...</h2>
  <p>netkeibaから出馬表を取得しています。<br>このページは10秒ごとに自動更新されます。</p>
</div>
</body>
</html>"""


def _nodata_page() -> str:
    return """<!DOCTYPE html>
<html lang="ja">
<head>
<meta charset="UTF-8">
<title>学習適応仮説 予想</title>
<style>
*{box-sizing:border-box;margin:0;padding:0}
body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif;
background:#f5f5f0;display:flex;align-items:center;justify-content:center;
min-height:100vh;color:#1a1a18}
.box{text-align:center;background:#fff;border:1px solid #e8e8e4;
border-radius:12px;padding:48px 64px}
h2{font-size:18px;font-weight:500;margin-bottom:10px}
p{color:#888;font-size:13px;line-height:1.8;margin-bottom:28px}
a.btn{display:inline-block;padding:10px 28px;background:#534AB7;color:#fff;
border-radius:8px;text-decoration:none;font-size:14px;font-weight:500}
a.btn:hover{background:#3C3489}
</style>
</head>
<body>
<div class="box">
  <h2>学習適応仮説 予想レポート</h2>
  <p>まだデータがありません。<br>下のボタンで最新の出馬表を取得してください。</p>
  <a class="btn" href="/update">データを取得する</a>
</div>
</body>
</html>"""


def _error_page(msg: str) -> str:
    safe = _html.escape(msg)
    return f"""<!DOCTYPE html>
<html lang="ja">
<head>
<meta charset="UTF-8">
<title>エラー</title>
<style>
*{{box-sizing:border-box;margin:0;padding:0}}
body{{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif;
background:#f5f5f0;display:flex;align-items:center;justify-content:center;
min-height:100vh;color:#1a1a18}}
.box{{text-align:center;background:#fff;border:1px solid #e8e8e4;
border-radius:12px;padding:48px 64px;max-width:480px}}
h2{{font-size:18px;font-weight:500;color:#C13A2A;margin-bottom:10px}}
p{{color:#888;font-size:12px;line-height:1.8;margin-bottom:24px}}
.msg{{background:#FDECEA;border-radius:8px;padding:12px 16px;font-size:12px;
color:#C13A2A;margin-bottom:24px;text-align:left}}
a.btn{{display:inline-block;padding:10px 28px;background:#534AB7;color:#fff;
border-radius:8px;text-decoration:none;font-size:14px;font-weight:500}}
</style>
</head>
<body>
<div class="box">
  <h2>取得エラー</h2>
  <div class="msg">{safe}</div>
  <p>木曜日以降に出馬表が公開されると取得できます。</p>
  <a class="btn" href="/update">再取得する</a>
</div>
</body>
</html>"""


@app.route("/")
def index() -> Response:
    if _update_status == "running":
        return Response(_updating_page(), mimetype="text/html")
    if _update_status == "error":
        return Response(_error_page(_update_error), mimetype="text/html")
    if not _html_cache:
        return Response(_nodata_page(), mimetype="text/html")
    return Response(_html_cache, mimetype="text/html")


@app.route("/history")
def history() -> Response:
    csv_path = os.environ.get("HIST_CSV", DEFAULT_HIST)
    return Response(build_history_page(csv_path), mimetype="text/html")


@app.route("/about")
def about() -> Response:
    return Response(build_about_page(), mimetype="text/html")


@app.route("/update")
def trigger_update() -> Response:
    global _update_status, _update_error
    with _update_lock:
        if _update_status == "running":
            return redirect("/")
        _update_status = "running"
        _update_error  = ""
    hist_csv = os.environ.get("HIST_CSV", DEFAULT_HIST)
    dates    = next_weekend_dates()
    t = threading.Thread(target=_do_update, args=(hist_csv, dates), daemon=True)
    t.start()
    return redirect("/")


# ── CLI エントリーポイント（直接実行時） ──────────────────────

def main() -> None:
    """CLI 用: python yosou.py --cli [--dates ...] [--hist ...] [--log ...]"""
    parser = argparse.ArgumentParser(
        description="来週末の全レースに学習適応仮説フラグを判定して表示",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=(
            "使用例:\n"
            "  %(prog)s --cli                         # 来週末（自動）\n"
            "  %(prog)s --cli --dates 20260613 20260614\n"
            "  %(prog)s --cli --hist nikatsu_300.csv\n"
        ),
    )
    parser.add_argument("--cli",   action="store_true", help="CLI モードで実行（Flask を起動しない）")
    parser.add_argument("--dates", nargs="+", metavar="YYYYMMDD",
                        help="対象日付（省略時: 最も近い土日）")
    parser.add_argument("--hist",  default=DEFAULT_HIST, metavar="FILE",
                        help=f"過去実績 CSV (default: {DEFAULT_HIST})")
    parser.add_argument("--log",   default=DEFAULT_LOG,  metavar="FILE",
                        help=f"ログ出力先 (default: {DEFAULT_LOG})")
    parser.add_argument("--html",  default="yosou_result.html", metavar="FILE",
                        help="HTML レポート出力先 (default: yosou_result.html)")
    args = parser.parse_args()

    if not args.cli:
        # CLI フラグなし → Flask 起動
        port = int(os.environ.get("PORT", 5000))
        print(f"Flask サーバー起動: http://0.0.0.0:{port}", file=sys.stderr)
        app.run(host="0.0.0.0", port=port, debug=False)
        return

    dates = args.dates if args.dates else next_weekend_dates()
    print(f"対象日付: {', '.join(dates)}", file=sys.stderr)

    hist_rates, total_hist = load_hist_rates(args.hist)
    print(f"  {total_hist} レース分のデータを読み込みました", file=sys.stderr)

    all_race_ids: List[str] = []
    print("レース一覧を取得中 ...", file=sys.stderr)
    for d in dates:
        all_race_ids.extend(fetch_race_ids_for_date(d))

    if not all_race_ids:
        print("エラー: レース情報を取得できませんでした", file=sys.stderr)
        sys.exit(1)

    print(f"対象レース: {len(all_race_ids)} レース", file=sys.stderr)

    races_by_class: Dict[str, List[Dict]] = defaultdict(list)
    total_horses = 0

    for i, race_id in enumerate(all_race_ids, 1):
        print(f"\n[{i}/{len(all_race_ids)}] {race_id} ({race_label(race_id)}) 処理中 ...",
              file=sys.stderr)
        result = fetch_shutuba(race_id)
        if result is None:
            print("  スキップ（出馬表取得失敗）", file=sys.stderr)
            continue
        race_title, race_date, horses = result
        if not horses:
            print("  スキップ（出走馬なし）", file=sys.stderr)
            continue
        print(f"  {race_title}  ({race_date})  {len(horses)}頭", file=sys.stderr)
        horses = add_prediction_flags(horses, race_date)
        cls    = classify(race_title)
        flagged_n = sum(1 for h in horses if h["仮説フラグ"])
        print(f"  フラグあり: {flagged_n}頭 / {len(horses)}頭", file=sys.stderr)
        sys.stderr.flush()
        races_by_class[cls].append({
            "race_id":    race_id,
            "race_title": race_title,
            "race_date":  race_date,
            "horses":     horses,
        })
        total_horses += len(horses)

    print(f"\n取得完了: {sum(len(v) for v in races_by_class.values())} レース / "
          f"{total_horses} 頭", file=sys.stderr)

    print_report(races_by_class, hist_rates, dates, args.hist, total_hist)
    save_log(races_by_class, args.log)
    generate_html_report(
        races_by_class, hist_rates, dates, args.hist, total_hist,
        filepath=args.html,
    )


if __name__ == "__main__":
    main()

def main() -> None:
    parser = argparse.ArgumentParser(
        description="来週末の全レースに学習適応仮説フラグを判定して表示",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=(
            "使用例:\n"
            "  %(prog)s                              # 来週末（自動）\n"
            "  %(prog)s --dates 20260613 20260614    # 日付指定\n"
            "  %(prog)s --hist nikatsu_300.csv       # 参照 CSV を変更\n"
        ),
    )
    parser.add_argument(
        "--dates", nargs="+", metavar="YYYYMMDD",
        help="対象日付（省略時: 最も近い土日）",
    )
    parser.add_argument(
        "--hist", default=DEFAULT_HIST, metavar="FILE",
        help=f"過去実績 CSV (default: {DEFAULT_HIST})",
    )
    parser.add_argument(
        "--log", default=DEFAULT_LOG, metavar="FILE",
        help=f"ログ出力先 (default: {DEFAULT_LOG})",
    )
    parser.add_argument(
        "--html", default="yosou_result.html", metavar="FILE",
        help="HTML レポート出力先 (default: yosou_result.html)",
    )
    args = parser.parse_args()

    # 対象日付の決定
    dates = args.dates if args.dates else next_weekend_dates()
    print(f"対象日付: {', '.join(dates)}", file=sys.stderr)

    # 過去実績データ読み込み
    print(f"過去実績を読み込み中: {args.hist}", file=sys.stderr)
    hist_rates, total_hist = load_hist_rates(args.hist)
    print(f"  {total_hist} レース分のデータを読み込みました", file=sys.stderr)

    # race_id を日付ごとに取得
    all_race_ids: List[str] = []
    print("レース一覧を取得中 ...", file=sys.stderr)
    for d in dates:
        all_race_ids.extend(fetch_race_ids_for_date(d))

    if not all_race_ids:
        print("エラー: レース情報を取得できませんでした", file=sys.stderr)
        sys.exit(1)

    print(f"対象レース: {len(all_race_ids)} レース", file=sys.stderr)

    # 出馬表取得 & フラグ判定
    races_by_class: Dict[str, List[Dict]] = defaultdict(list)
    total_horses = 0

    for i, race_id in enumerate(all_race_ids, 1):
        print(f"\n[{i}/{len(all_race_ids)}] {race_id} ({race_label(race_id)}) 処理中 ...",
              file=sys.stderr)
        result = fetch_shutuba(race_id)
        if result is None:
            print(f"  スキップ（出馬表取得失敗）", file=sys.stderr)
            continue

        race_title, race_date, horses = result
        if not horses:
            print(f"  スキップ（出走馬なし）", file=sys.stderr)
            continue

        print(f"  {race_title}  ({race_date})  {len(horses)}頭", file=sys.stderr)

        horses = add_prediction_flags(horses, race_date)
        cls    = classify(race_title)

        flagged_n = sum(1 for h in horses if h["仮説フラグ"])
        print(
            f"  フラグあり: {flagged_n}頭 / {len(horses)}頭",
            file=sys.stderr,
        )
        sys.stderr.flush()

        races_by_class[cls].append({
            "race_id":    race_id,
            "race_title": race_title,
            "race_date":  race_date,
            "horses":     horses,
        })
        total_horses += len(horses)

    print(f"\n取得完了: {sum(len(v) for v in races_by_class.values())} レース / {total_horses} 頭",
          file=sys.stderr)

    # 表示
    print_report(races_by_class, hist_rates, dates, args.hist, total_hist)

    # CSV 保存
    save_log(races_by_class, args.log)

    # HTML 生成
    generate_html_report(
        races_by_class, hist_rates, dates, args.hist, total_hist,
        filepath=args.html,
    )


if __name__ == "__main__":
    main()
