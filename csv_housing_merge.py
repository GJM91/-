# -*- coding: utf-8 -*-
"""
주택관리번호 기준 CSV 병합 도구 (1:다 매칭)
================================================================
두 개의 CSV 파일을 "주택관리번호"를 기준으로 매칭하여,
한쪽 파일(추가 파일)의 내용을 다른 파일(기준 파일)에 붙여넣습니다.

  · 기준 파일(왼쪽)  : 결과의 뼈대가 되는 파일
  · 추가 파일(오른쪽): 기준 파일에 내용을 가져올 파일

[1:다 매칭이란?]
  기준 파일의 주택관리번호 하나에 대해, 추가 파일에 같은 번호를 가진
  행이 여러 개 있을 수 있습니다. 이 경우 결과에서 기준 행이 매칭된
  개수만큼 복제되어(행이 늘어나) 각 추가 행과 짝지어집니다.
  (SQL 의 LEFT JOIN 과 동일한 동작)

[사용법]
  · 파이썬 3 가 설치된 PC 에서 실행하면 팝업 창이 뜹니다.
      python csv_housing_merge.py
  · 별도 라이브러리 설치가 필요 없습니다(표준 라이브러리 tkinter/csv 사용).
  · 한글 CSV(cp949/euc-kr) 와 UTF-8 모두 자동 인식합니다.

작성: 정보시스템 감리 실무용 유틸리티
"""

import os
import csv
import tkinter as tk
from tkinter import ttk, filedialog, messagebox

# ─────────────────────────────────────────────────────────────
# 기본 설정
# ─────────────────────────────────────────────────────────────
# 주택관리번호로 추정되는 컬럼명 후보 (자동 선택에 사용)
KEY_CANDIDATES = ["주택관리번호", "주택 관리번호", "관리번호", "주택관리 번호"]

# CSV 인코딩 자동 인식 시 시도할 순서 (한글 CSV 는 cp949 가 많음)
ENCODING_CANDIDATES = ["utf-8-sig", "cp949", "euc-kr", "utf-8"]


# ─────────────────────────────────────────────────────────────
# CSV 입출력 유틸리티
# ─────────────────────────────────────────────────────────────
def read_csv(path):
    """CSV 파일을 읽어 (헤더 리스트, 행 리스트[dict]) 를 반환한다.

    인코딩을 자동으로 판별한다. 실패 시 마지막 인코딩으로
    깨진 문자를 대체(replace)하여 읽는다.
    """
    last_err = None
    for enc in ENCODING_CANDIDATES:
        try:
            with open(path, "r", encoding=enc, newline="") as f:
                reader = csv.DictReader(f)
                rows = list(reader)
                headers = reader.fieldnames or []
                # 헤더 공백 제거
                headers = [(h or "").strip() for h in headers]
                cleaned = []
                for r in rows:
                    cleaned.append({(k or "").strip(): v for k, v in r.items()})
                return headers, cleaned
        except (UnicodeDecodeError, UnicodeError) as e:
            last_err = e
            continue
    # 모두 실패하면 마지막 인코딩으로 강제 읽기
    with open(path, "r", encoding=ENCODING_CANDIDATES[-1], errors="replace", newline="") as f:
        reader = csv.DictReader(f)
        rows = list(reader)
        headers = [(h or "").strip() for h in (reader.fieldnames or [])]
        cleaned = [{(k or "").strip(): v for k, v in r.items()} for r in rows]
    return headers, cleaned


def write_csv(path, headers, rows):
    """결과를 UTF-8(BOM) 로 저장한다. (엑셀에서 한글이 깨지지 않도록)"""
    with open(path, "w", encoding="utf-8-sig", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=headers, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(rows)


def normalize_key(value):
    """주택관리번호 값을 매칭용으로 정규화한다.

    앞뒤 공백 제거, 내부 공백 제거. (숫자/문자열 표기 차이를 줄임)
    """
    if value is None:
        return ""
    return str(value).strip().replace(" ", "")


def guess_key_column(headers):
    """헤더 목록에서 주택관리번호로 보이는 컬럼을 추정한다."""
    # 1) 정확히 일치
    for cand in KEY_CANDIDATES:
        if cand in headers:
            return cand
    # 2) '관리번호' 포함
    for h in headers:
        if "관리번호" in h:
            return h
    # 3) '주택' + '번호' 포함
    for h in headers:
        if "주택" in h and "번호" in h:
            return h
    return headers[0] if headers else ""


# ─────────────────────────────────────────────────────────────
# 핵심 병합 로직 (1:다 매칭)
# ─────────────────────────────────────────────────────────────
def merge_one_to_many(base_headers, base_rows, base_key,
                      add_headers, add_rows, add_key,
                      add_cols, keep_unmatched=True,
                      prefix=""):
    """기준 파일에 추가 파일의 내용을 1:다 로 붙인다.

    Parameters
    ----------
    base_*      : 기준 파일의 헤더/행/키 컬럼
    add_*       : 추가 파일의 헤더/행/키 컬럼
    add_cols    : 추가 파일에서 가져올 컬럼 목록
    keep_unmatched : 매칭되는 추가 행이 없어도 기준 행을 남길지 여부
    prefix      : 가져온 컬럼명 앞에 붙일 접두어(컬럼명 충돌 방지)

    Returns
    -------
    (결과 헤더, 결과 행 리스트, 통계 dict)
    """
    # 추가 파일을 키별로 인덱싱 (키 -> 행 리스트)
    index = {}
    for r in add_rows:
        k = normalize_key(r.get(add_key))
        if k == "":
            continue
        index.setdefault(k, []).append(r)

    # 결과 헤더 = 기준 헤더 + (접두어 붙인) 추가 컬럼
    out_add_cols = [prefix + c for c in add_cols]
    # 기준 헤더와 겹치는 이름은 접두어로 자동 회피
    result_headers = list(base_headers)
    for c in out_add_cols:
        # 이미 있으면 뒤에 _2, _3 … 붙여 유일하게
        name = c
        n = 2
        while name in result_headers:
            name = f"{c}_{n}"
            n += 1
        result_headers.append(name)
    # out_add_cols 를 최종 이름으로 갱신 (충돌 회피 반영)
    final_add_names = result_headers[len(base_headers):]

    result_rows = []
    matched_base = 0
    total_matched_rows = 0
    unmatched_base = 0

    for br in base_rows:
        k = normalize_key(br.get(base_key))
        matches = index.get(k, []) if k != "" else []

        if matches:
            matched_base += 1
            for ar in matches:
                total_matched_rows += 1
                new_row = dict(br)  # 기준 행 복제
                for src_col, out_name in zip(add_cols, final_add_names):
                    new_row[out_name] = ar.get(src_col, "")
                result_rows.append(new_row)
        else:
            unmatched_base += 1
            if keep_unmatched:
                new_row = dict(br)
                for out_name in final_add_names:
                    new_row[out_name] = ""
                result_rows.append(new_row)

    stats = {
        "기준_행수": len(base_rows),
        "추가_행수": len(add_rows),
        "매칭된_기준행": matched_base,
        "매칭안된_기준행": unmatched_base,
        "생성된_결과행": len(result_rows),
        "추가파일_고유키수": len(index),
    }
    return result_headers, result_rows, stats


# ─────────────────────────────────────────────────────────────
# GUI (팝업)
# ─────────────────────────────────────────────────────────────
class MergeApp:
    def __init__(self, root):
        self.root = root
        self.root.title("주택관리번호 CSV 병합 (1:다 매칭)")
        self.root.geometry("640x560")

        self.base_path = tk.StringVar()
        self.add_path = tk.StringVar()
        self.base_headers = []
        self.base_rows = []
        self.add_headers = []
        self.add_rows = []

        self._build_ui()

    def _build_ui(self):
        pad = {"padx": 8, "pady": 4}

        # ── 1) 기준 파일 ────────────────────────────────
        f1 = ttk.LabelFrame(self.root, text="① 기준 파일 (내용을 붙일 대상)")
        f1.pack(fill="x", **pad)
        ttk.Entry(f1, textvariable=self.base_path).pack(
            side="left", fill="x", expand=True, padx=6, pady=6)
        ttk.Button(f1, text="찾아보기…",
                   command=self.load_base).pack(side="left", padx=6)

        row1 = ttk.Frame(self.root)
        row1.pack(fill="x", **pad)
        ttk.Label(row1, text="기준 파일 주택관리번호 컬럼:").pack(side="left")
        self.base_key_cb = ttk.Combobox(row1, state="readonly", width=28)
        self.base_key_cb.pack(side="left", padx=6)

        # ── 2) 추가 파일 ────────────────────────────────
        f2 = ttk.LabelFrame(self.root, text="② 추가 파일 (여기서 내용을 가져옴)")
        f2.pack(fill="x", **pad)
        ttk.Entry(f2, textvariable=self.add_path).pack(
            side="left", fill="x", expand=True, padx=6, pady=6)
        ttk.Button(f2, text="찾아보기…",
                   command=self.load_add).pack(side="left", padx=6)

        row2 = ttk.Frame(self.root)
        row2.pack(fill="x", **pad)
        ttk.Label(row2, text="추가 파일 주택관리번호 컬럼:").pack(side="left")
        self.add_key_cb = ttk.Combobox(row2, state="readonly", width=28)
        self.add_key_cb.pack(side="left", padx=6)

        # ── 3) 가져올 컬럼 선택 ──────────────────────────
        f3 = ttk.LabelFrame(self.root, text="③ 추가 파일에서 가져올 컬럼 (여러 개 선택 가능)")
        f3.pack(fill="both", expand=True, **pad)
        listwrap = ttk.Frame(f3)
        listwrap.pack(fill="both", expand=True, padx=6, pady=6)
        self.cols_list = tk.Listbox(listwrap, selectmode="extended", height=8)
        self.cols_list.pack(side="left", fill="both", expand=True)
        sb = ttk.Scrollbar(listwrap, orient="vertical",
                           command=self.cols_list.yview)
        sb.pack(side="left", fill="y")
        self.cols_list.config(yscrollcommand=sb.set)

        btns = ttk.Frame(f3)
        btns.pack(fill="x", padx=6)
        ttk.Button(btns, text="전체 선택",
                   command=lambda: self.cols_list.select_set(0, "end")
                   ).pack(side="left")
        ttk.Button(btns, text="선택 해제",
                   command=lambda: self.cols_list.select_clear(0, "end")
                   ).pack(side="left", padx=6)

        # ── 4) 옵션 ─────────────────────────────────────
        f4 = ttk.Frame(self.root)
        f4.pack(fill="x", **pad)
        self.keep_unmatched = tk.BooleanVar(value=True)
        ttk.Checkbutton(f4, text="매칭되는 추가 행이 없어도 기준 행 유지",
                        variable=self.keep_unmatched).pack(side="left")

        # ── 5) 실행 ─────────────────────────────────────
        ttk.Button(self.root, text="병합 실행 후 저장…",
                   command=self.run_merge).pack(pady=10)

    # ── 파일 로드 ────────────────────────────────────────
    def _pick_and_load(self, path_var, key_cb, is_base):
        path = filedialog.askopenfilename(
            title="CSV 파일 선택",
            filetypes=[("CSV 파일", "*.csv"), ("모든 파일", "*.*")])
        if not path:
            return
        try:
            headers, rows = read_csv(path)
        except Exception as e:
            messagebox.showerror("읽기 오류", f"CSV 를 읽지 못했습니다.\n\n{e}")
            return
        if not headers:
            messagebox.showwarning("경고", "헤더(첫 줄)를 찾을 수 없습니다.")
            return

        path_var.set(path)
        key_cb["values"] = headers
        key_cb.set(guess_key_column(headers))

        if is_base:
            self.base_headers, self.base_rows = headers, rows
        else:
            self.add_headers, self.add_rows = headers, rows
            # 추가 파일 컬럼 목록 갱신
            self.cols_list.delete(0, "end")
            for h in headers:
                self.cols_list.insert("end", h)

        messagebox.showinfo(
            "불러오기 완료",
            f"파일: {os.path.basename(path)}\n"
            f"컬럼 수: {len(headers)}\n"
            f"행 수: {len(rows)}")

    def load_base(self):
        self._pick_and_load(self.base_path, self.base_key_cb, is_base=True)

    def load_add(self):
        self._pick_and_load(self.add_path, self.add_key_cb, is_base=False)

    # ── 실행 ─────────────────────────────────────────────
    def run_merge(self):
        if not self.base_rows:
            messagebox.showwarning("확인", "① 기준 파일을 먼저 선택하세요.")
            return
        if not self.add_rows:
            messagebox.showwarning("확인", "② 추가 파일을 먼저 선택하세요.")
            return

        base_key = self.base_key_cb.get()
        add_key = self.add_key_cb.get()
        if not base_key or not add_key:
            messagebox.showwarning("확인", "양쪽 파일의 주택관리번호 컬럼을 지정하세요.")
            return

        sel = self.cols_list.curselection()
        if not sel:
            messagebox.showwarning(
                "확인", "③ 추가 파일에서 가져올 컬럼을 하나 이상 선택하세요.")
            return
        add_cols = [self.cols_list.get(i) for i in sel]

        headers, rows, stats = merge_one_to_many(
            self.base_headers, self.base_rows, base_key,
            self.add_headers, self.add_rows, add_key,
            add_cols, keep_unmatched=self.keep_unmatched.get())

        # 저장 위치 선택
        out_path = filedialog.asksaveasfilename(
            title="결과 저장",
            defaultextension=".csv",
            initialfile="병합결과.csv",
            filetypes=[("CSV 파일", "*.csv")])
        if not out_path:
            return
        try:
            write_csv(out_path, headers, rows)
        except Exception as e:
            messagebox.showerror("저장 오류", f"결과를 저장하지 못했습니다.\n\n{e}")
            return

        # 결과 요약 팝업
        msg = (
            "병합이 완료되었습니다.\n\n"
            f"· 기준 파일 행수      : {stats['기준_행수']:,}\n"
            f"· 추가 파일 행수      : {stats['추가_행수']:,}\n"
            f"· 매칭된 기준 행      : {stats['매칭된_기준행']:,}\n"
            f"· 매칭 안된 기준 행   : {stats['매칭안된_기준행']:,}\n"
            f"· 생성된 결과 행      : {stats['생성된_결과행']:,}\n\n"
            f"저장 위치:\n{out_path}"
        )
        messagebox.showinfo("완료", msg)


def main():
    root = tk.Tk()
    MergeApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
