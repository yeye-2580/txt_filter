import json
import os
import re
import subprocess
import sys
import threading
import shutil
import time
import csv
import warnings
import datetime
import glob
import queue
import tkinter as tk
from tkinter import filedialog, messagebox, Listbox, BooleanVar
import customtkinter as ctk
import pandas as pd
import dask.dataframe as dd
import chardet
warnings.filterwarnings("ignore")
# ---------------------------------------------------------------------------
# 상수 정의
# ---------------------------------------------------------------------------
ENCODING_MAP = {
    "ANSI":       "cp949",
    "UTF-8":      "utf-8",
    "UTF-8(BOM)": "utf-8-sig",
    "UTF-16 LE":  "utf-16-le",
    "UTF-16 BE":  "utf-16-be",
    "EUC-KR":     "euc-kr",
    "ISO-8859-1": "iso-8859-1",
    "LATIN1":     "latin1",
}
REVERSE_ENCODING_MAP = {v.lower(): k for k, v in ENCODING_MAP.items()}
EXCEL_MAX_ROWS = 1_048_576
# pandas 버전별 bad-line 처리 파라미터 분기
_PD_VERSION = tuple(int(x) for x in pd.__version__.split(".")[:2])
CSV_BADLINE_KWARGS = (
    {"on_bad_lines": "skip"}
    if _PD_VERSION >= (1, 3)
    else {"error_bad_lines": False, "warn_bad_lines": False}
)
ctk.set_appearance_mode("light")
ctk.set_default_color_theme("green")
def _open_file_cross_platform(path: str) -> None:
    """OS별 파일 열기."""
    if sys.platform == "win32":
        os.startfile(path)
    elif sys.platform == "darwin":
        subprocess.run(["open", path], check=False)
    else:
        subprocess.run(["xdg-open", path], check=False)
# ===========================================================================
# 메인 애플리케이션
# ===========================================================================
class FilterPivotApp(ctk.CTk):
    # -----------------------------------------------------------------------
    # 초기화
    # -----------------------------------------------------------------------
    def __init__(self):
        super().__init__()
        self.title("txtGL Filter 3.313 by seokelee@deloitte.com")
        self.configure(fg_color="white")
        # 파일 / 상태
        self.df_path: str | None = None
        self.delimiter        = tk.StringVar(value="|")
        self.header_row       = tk.IntVar(value=0)
        self.headers: list[str] = []
        self.encoding_var     = tk.StringVar()
        self.encoding         = "utf-8"
        self.parquet_exists   = False
        # 분석 모드
        self.selected_analysis  = "Pivot"
        self.blocksize_var      = tk.StringVar(value="64MB")
        # UI 위젯 참조 (create_widgets 전 None 초기화)
        self.delete_blank_button  = None
        self.patch_parquet_button = None
        self.main_frame           = None
        self.pivot_frame          = None
        self.filter_frame         = None
        self._reorder_selected_index = None
        self.header_edit_button   = None
        # 결과 파일 경로
        self.filter_result_parts: list[str] = []
        self.pivot_result_file   = ""
        self.filter_result_file  = ""
        self.filter_status_message = ""
        self.pivot_status_message  = ""
        # 헤더 표시 매핑
        self.original_headers: list[str]        = []
        self.header_display_map: dict[str, str]  = {}
        self.display_to_original_map: dict[str, str] = {}
        # UI 상태 머신
        self.busy     = False
        self.ui_state = "initial"   # initial / raw_selected / parquet_ready
        self._ui_queue: queue.Queue = queue.Queue()
        # 창 높이 debounce 핸들
        self._height_job = None
        # 다중 필터
        self.max_filters             = 5
        self.active_filter_count_var = tk.IntVar(value=1)
        self.current_filter_index    = tk.IntVar(value=1)
        self.filter_columns          = [""] * self.max_filters
        self.filter_keyword_texts    = [""] * self.max_filters
        # Parquet 파라미터 캐시 (메인스레드에서 읽어 백그라운드로 전달)
        # ⑬ 주석: _start_parquet_generation()에서 버튼 클릭 시점에 캐싱하므로
        #          blocksize_var 등 UI 값이 항상 정확히 반영됨
        self._parquet_delimiter      = "|"
        self._parquet_header_row     = 0
        self._parquet_encoding       = "utf-8"
        self._parquet_blocksize      = 16_777_216
        self._parquet_blocksize_label = "64MB"
        self.last_parquet_npartitions = "N/A"
        self.create_widgets()
        self.after(50, self._process_ui_queue)
        self.refresh_ui_state("initial")
    # -----------------------------------------------------------------------
    # 스레드 안전 UI 헬퍼
    # -----------------------------------------------------------------------
    def _process_ui_queue(self):
        """백그라운드에서 요청한 UI 작업을 메인스레드에서 처리."""
        try:
            while True:
                func, args, kwargs = self._ui_queue.get_nowait()
                try:
                    func(*args, **kwargs)
                except Exception as e:
                    print(f"[UI Queue 처리 오류] {type(e).__name__}: {e}")
        except queue.Empty:
            pass
        try:
            self.after(50, self._process_ui_queue)
        except Exception:
            pass
    def ui_call(self, func, *args, **kwargs):
        """메인스레드면 즉시 실행, 백그라운드면 큐에 등록."""
        if threading.current_thread() is threading.main_thread():
            return func(*args, **kwargs)
        try:
            self._ui_queue.put((func, args, kwargs))
        except Exception as e:
            print(f"[UI Queue 등록 오류] {type(e).__name__}: {e}")
        return None
    def update_parquet_status(self, message: str):
        def _update():
            try:
                self.status_label.configure(text=message)
            except Exception as e:
                print(f"[Parquet 상태 표시 오류] {type(e).__name__}: {e}")
        self.ui_call(_update)
    def update_analysis_status(self, message: str, progress=None, save=True):
        def _update():
            try:
                self.progress_label.configure(text=message)
                if progress is not None:
                    self.progress_bar.set(progress)
                try:
                    self.update_idletasks()
                except Exception:
                    pass
                # 진행 중 상태 메시지는 탭 전환 후 복원에서 제외
                _exclude = [
                    "파일 저장 중", "로딩 중", "Filtering 중", "피벗 집계 중",
                    "Wide 포맷", "데이터 로딩", "키워드 미입력", "삭제 대상 행 추출",
                    "삭제 행 txt 저장", "새 Parquet 생성", "Parquet 생성 중", "예외 분석 중",
                    "임시 Parquet", "기존 Parquet와 병합", "Parquet 교체",
                    "수정 파일 읽는 중", "원시파일에서 불일치",
                ]
                if save and hasattr(self, "selected_analysis"):
                    if any(ex in message for ex in _exclude):
                        return
                    if self.selected_analysis == "Filter":
                        self.filter_status_message = message
                    elif self.selected_analysis == "Pivot":
                        self.pivot_status_message = message
            except Exception as e:
                print(f"[분석 상태 표시 오류] {type(e).__name__}: {e}")
        self.ui_call(_update)
    def update_status(self, message, progress=None, save=True):
        """기존 호출부 호환용."""
        self.update_analysis_status(message, progress, save)
    def _configure_state(self, widget, state):
        try:
            if widget is not None:
                widget.configure(state=state)
        except Exception:
            pass
    def _disable_all_controls(self):
        targets = [
            self.raw_file_button, self.parquet_folder_button,
            self.merge_button,
            getattr(self, "manual_button", None),
            self.generate_button, self.delete_button,
            self.delete_blank_button, self.patch_parquet_button,
            self.header_edit_button,
            self.log_button, self.reset_button,
            self.delimiter_menu, self.encoding_menu, self.blocksize_option,
            self.header_preview,
            self.analysis_tab, self.run_button,
            self.filter_count_menu, self.filter_toggle,
            self.filter_col_select, self.additional_filter_checkbox,
            self.additional_col_select, self.keyword_input,
            self.index_listbox, self.column_listbox,
            self.value_menu, self.agg_menu,
            self.open_result_button, self.delete_result_button,
        ]
        for w in targets:
            self._configure_state(w, "disabled")
    def refresh_ui_state(self, state=None):
        if state is not None:
            self.ui_state = state
        if getattr(self, "busy", False):
            self._disable_all_controls()
            return
        self._disable_all_controls()
        base_btns = [self.raw_file_button, self.parquet_folder_button, self.merge_button]
        if hasattr(self, "manual_button"):
            base_btns.append(self.manual_button)
        for w in base_btns:
            self._configure_state(w, "normal")
        if self.ui_state == "initial":
            self._configure_state(self.header_preview, "normal")
            self.update_result_buttons()
            return
        if self.ui_state == "raw_selected":
            for w in [self.generate_button, self.delimiter_menu, self.encoding_menu,
                      self.blocksize_option, self.reset_button, self.header_preview]:
                self._configure_state(w, "normal")
            self.update_result_buttons()
            return
        if self.ui_state == "parquet_ready":
            for w in [self.delete_button, self.delete_blank_button,
                      self.patch_parquet_button,
                      self.header_edit_button,
                      self.log_button, self.reset_button,
                      self.analysis_tab, self.run_button]:
                self._configure_state(w, "normal")
            for w in [self.generate_button, self.delimiter_menu, self.encoding_menu,
                      self.blocksize_option, self.header_preview]:
                self._configure_state(w, "disabled")
            if self.selected_analysis == "Filter":
                for w in [self.filter_count_menu, self.filter_toggle,
                          self.filter_col_select, self.additional_filter_checkbox,
                          self.keyword_input]:
                    self._configure_state(w, "normal")
                self.toggle_additional_filter()
            elif self.selected_analysis == "Pivot":
                for w in [self.index_listbox, self.column_listbox,
                          self.value_menu, self.agg_menu]:
                    self._configure_state(w, "normal")
            self.update_result_buttons()
    def begin_busy(self, parquet_message=None, analysis_message=None, analysis_progress=None):
        self.busy = True
        self.refresh_ui_state()
        if parquet_message:
            self.update_parquet_status(parquet_message)
        if analysis_message:
            self.update_analysis_status(analysis_message, analysis_progress)
    def end_busy(self, state=None):
        self.busy = False
        if state:
            self.refresh_ui_state(state)
        else:
            self.refresh_ui_state()
    # -----------------------------------------------------------------------
    # UI 구성
    # -----------------------------------------------------------------------
    def create_widgets(self):
        self.main_frame = ctk.CTkFrame(self, fg_color="#f0f0f0")
        self.main_frame.pack(fill="both", expand=True, padx=20, pady=10)
        # ── 파일 섹션 ──────────────────────────────────────────────────────
        file_section = ctk.CTkFrame(self.main_frame, fg_color="#e8e8e8")
        file_section.pack(fill="x", pady=(0, 10))
        top_row = ctk.CTkFrame(file_section, fg_color="#e8e8e8")
        top_row.pack(fill="x", padx=10, pady=(10, 5))
        ctk.CTkLabel(top_row, text="분석할 파일 선택 및 분석모드 설정",
                     font=("맑은 고딕", 14, "bold")).pack(side="left")
        # status_label: top_row 오른쪽 배치 → pq_frame 버튼들과 공간 충돌 없음
        self.status_label = ctk.CTkLabel(
            top_row, text="분석 준비 전: 파일을 먼저 선택하세요.",
            font=("맑은 고딕", 12), anchor="e", text_color="#444444")
        self.status_label.pack(side="right", padx=(10, 5))
        ctrl = ctk.CTkFrame(file_section, fg_color="#e8e8e8")
        ctrl.pack(fill="x", padx=10, pady=5)
        self.raw_file_button = ctk.CTkButton(
            ctrl, text="📜 원시파일 선택", command=self.select_raw_file)
        self.raw_file_button.pack(side="left", padx=5)
        self.parquet_folder_button = ctk.CTkButton(
            ctrl, text="📁 Parquet 폴더 선택", command=self.select_parquet_folder)
        self.parquet_folder_button.pack(side="left", padx=5)
        self.merge_button = ctk.CTkButton(
            ctrl, text="➕ 원시파일 병합", command=self.merge_raw_files)
        self.merge_button.pack(side="left", padx=5)
        ctk.CTkLabel(ctrl, text="구분자:").pack(side="left", padx=(10, 5))
        self.delimiter_menu = ctk.CTkOptionMenu(
            ctrl, values=["|", ",", "\t", ";"], variable=self.delimiter, width=70)
        self.delimiter_menu.pack(side="left", padx=(0, 10))
        ctk.CTkLabel(ctrl, text="인코딩:").pack(side="left", padx=(5, 5))
        self.encoding_menu = ctk.CTkOptionMenu(
            ctrl, values=list(ENCODING_MAP.keys()),
            variable=self.encoding_var, width=100,
            command=self.update_encoding)
        self.encoding_menu.pack(side="left", padx=(0, 10))
        ctk.CTkLabel(ctrl, text="블록사이즈:").pack(side="left", padx=(5, 5))
        self.blocksize_option = ctk.CTkOptionMenu(
            ctrl, values=["16MB", "32MB", "64MB", "128MB", "256MB"],
            variable=self.blocksize_var, width=80,
            command=self.blocksize_warning)
        self.blocksize_option.pack(side="left", padx=(0, 10))
        self.encoding_label = ctk.CTkLabel(ctrl, text="식별된인코딩: 미확인", width=120)
        self.encoding_label.pack(side="left", padx=5)
        self.manual_button = ctk.CTkButton(
            ctrl, text="📘 설명서", command=self.show_manual_window, width=110)
        self.manual_button.pack(side="right", padx=(5, 5))
        # ── Parquet 관리 행 ────────────────────────────────────────────────
        pq_frame = ctk.CTkFrame(file_section, fg_color="#e8e8e8")
        pq_frame.pack(fill="x", padx=10, pady=(0, 5))
        self.generate_button = ctk.CTkButton(
            pq_frame, text="⭕ Parquet 생성",
            command=self.show_parquet_confirm_dialog, state="disabled")
        self.generate_button.pack(side="left", padx=5)
        self.delete_button = ctk.CTkButton(
            pq_frame, text="❌ Parquet 삭제",
            command=self.delete_parquet, state="disabled")
        self.delete_button.pack(side="left", padx=5)
        self.delete_blank_button = ctk.CTkButton(
            pq_frame, text="🧹 빈행데이터 삭제",
            command=self.show_blank_delete_dialog, state="disabled")
        self.delete_blank_button.pack(side="left", padx=5)
        self.patch_parquet_button = ctk.CTkButton(
            pq_frame, text="🩹 예외행 보완",
            command=self.show_patch_parquet_dialog, state="disabled")
        self.patch_parquet_button.pack(side="left", padx=5)
        self.header_edit_button = ctk.CTkButton(
            pq_frame, text="📝 헤더표시수정",
            command=self.show_header_display_editor, state="disabled")
        self.header_edit_button.pack(side="left", padx=5)
        self.log_button = ctk.CTkButton(
            pq_frame, text="⏹️ Parquet log",
            command=self.show_parquet_log, state="disabled")
        self.log_button.pack(side="left", padx=5)
        self.reset_button = ctk.CTkButton(
            pq_frame, text="🔄 초기화", command=self.reset_ui, width=110)
        self.reset_button.pack(side="right", padx=(5, 5))
        # ── 헤더 미리보기 ──────────────────────────────────────────────────
        preview_frame = tk.Frame(file_section, bg="#f0f0f0")
        preview_frame.pack(fill="x", padx=10, pady=5)
        self.header_preview = Listbox(preview_frame, height=5, bg="#f0f0f0",
                                      xscrollcommand=True)
        self.header_preview.pack(side="left", fill="x", expand=True)
        self.header_preview.bind("<<ListboxSelect>>", self.select_header_row)
        # ── 모드 탭 / 동적 프레임 / 액션 ─────────────────────────────────
        self.mode_frame = ctk.CTkFrame(self.main_frame, fg_color="#dcdcdc")
        self.analysis_tab = ctk.CTkSegmentedButton(
            self.mode_frame, values=["Filter", "Pivot"], command=self.switch_mode)
        self.analysis_tab.configure(state="disabled")
        self.analysis_tab.pack(fill="x", pady=5)
        self.dynamic_frame = ctk.CTkFrame(self.main_frame, fg_color="#dcdcdc")
        self.create_pivot_widgets()
        self.create_filter_widgets()
        self.action_frame = ctk.CTkFrame(self.main_frame, fg_color="#e0e0e0")
        left_af = ctk.CTkFrame(self.action_frame, fg_color="transparent")
        left_af.pack(side="left", padx=10, fill="x", expand=True)
        self.run_button = ctk.CTkButton(
            left_af, text="▶️ 분석 실행", command=self.run_analysis, state="disabled")
        self.run_button.pack(side="left", padx=(0, 5))
        self.progress_bar = ctk.CTkProgressBar(left_af, width=250)
        self.progress_bar.set(0)
        self.progress_bar.pack(side="left", padx=(5, 5))
        self.progress_label = ctk.CTkLabel(left_af, text="", font=("맑은 고딕", 11))
        self.progress_label.pack(side="left", padx=(5, 5))
        right_af = ctk.CTkFrame(self.action_frame, fg_color="transparent")
        right_af.pack(side="right", padx=10)
        self.result_file_label = ctk.CTkLabel(
            right_af, text="", font=("맑은 고딕", 10), anchor="e", width=240)
        self.result_file_label.pack(side="left", padx=(5, 5))
        self.open_result_button = ctk.CTkButton(
            right_af, text="📂 분석파일 실행",
            command=self.open_result_file, state="disabled", width=120)
        self.open_result_button.pack(side="left", padx=5)
        self.delete_result_button = ctk.CTkButton(
            right_af, text="❌ 분석파일 삭제",
            command=self.delete_result_file, state="disabled", width=120)
        self.delete_result_button.pack(side="left", padx=5)
        # 초기엔 모드/동적/액션 프레임 숨김
        self.mode_frame.pack_forget()
        self.dynamic_frame.pack_forget()
        self.action_frame.pack_forget()
        self.update_idletasks()
        self.geometry(f"1450x{self.winfo_reqheight()}")
    def blocksize_warning(self, value):
        self.blocksize_var.set(value)
        # ⑪ 이미 메인 스레드이므로 after(0) 불필요 → 직접 호출
        if value in ["128MB", "256MB"]:
            messagebox.showwarning(
                "성능 경고", f"{value} 선택 시 기초파일 생성 시간이 길어질 수 있습니다.")
    # -----------------------------------------------------------------------
    # 설명서 창
    # -----------------------------------------------------------------------
    def show_manual_window(self):
        manual_text = """txtGL Filter v3 사용 안내 - FREEWARE
============================================================
코드 및 아래 설명서는 CHATGPT 및 CLAUDE로 만들었습니다.
1. 프로그램 개요
------------------------------------------------------------
txtGL Filter는 SAP 원장, 쿼리, 기타 테이블 형식의 대용량 데이터를 Parquet 형식으로 변환한 후
Filter 또는 Pivot 분석을 수행하는 프로그램입니다.
Excel로 열기 어려운 대용량 txt/csv/xls/xlsx 파일을 압축·분석할 수 있습니다.
2. 설치 및 실행 방법
------------------------------------------------------------
1) zip 파일 압축 해제
2) exe 파일 오른쪽 클릭 → [속성] → [보안] → [차단 해제] 체크 → 실행
3. 지원 파일 형식
------------------------------------------------------------
txt / csv / xls(인식 안되면 확장자 txt로 변경 후 시도) / xlsx
4. 기본 사용 순서
------------------------------------------------------------
1) 원본 데이터 수령
2) [원시파일병합] → 여러 파일을 하나의 txt로 병합
3) [원본파일선택] → 헤더행 선택, 인코딩·구분자 자동 인식
4) [PARQUET 생성] → 완전성검토 선택 가능
5) [PARQUET log] 확인
6) [PIVOT] 실행하여 Parquet 검증
7) 필요 시 [빈행데이터 삭제] 실행
8) 필요 시 PARQUET 생성시 완전성검토 → [예외행 보완] 실행 → 열 개수 불일치 행 보완
9) 필요 시 [헤더표시변경] 실행
10) Filter 또는 Pivot 분석 실행 → csv 저장
5. 주요 기능
------------------------------------------------------------
[PARQUET 생성] txt/csv/xls/xlsx → Parquet 압축 폴더 변환
[Filter] 최대 5개 필터 동시 적용, 결과 csv 저장
[추가 필터링] 키워드 포함 행과 동일 전표번호 전표 전체 추출
[Pivot] 행/열 기준 집계 (합계/개수)
[원시파일 병합] 여러 파일 → 하나의 txt
[빈행데이터 삭제] 특정 헤더 기준 빈 행 삭제
[예외행 보완] 구분자/줄바꿈 포함으로 열 개수 불일치 처리된 행을
   Excel에서 수기로 수정 후 기존 Parquet에 추가 보완
[헤더표시변경] 화면 표시 및 결과 파일 헤더명만 변경
6. 예외행 보완 사용법
------------------------------------------------------------
① Parquet 생성 시 [완전성 검토 추가] 체크 → anomaly_lines.txt 생성
② [예외행 보완] 버튼 클릭
③ STEP 1: [열 개수 불일치] 행만 추출 → txt 저장
④ 저장된 txt를 Excel에서 열어 구분자/줄바꿈 문제 수동 수정
   (적요 등 필드 내 구분자·줄바꿈 제거 또는 열 수 맞춤)
⑤ 수정 후 txt/csv로 저장
⑥ STEP 2: 수정 파일 선택 → 기존 Parquet에 자동 병합
7. 사용 시 주의사항
------------------------------------------------------------
- Parquet 생성은 파일 크기에 따라 장시간 소요 (15GB → 1시간+)
- Parquet 생성 후 반드시 log 확인
- 완전성검토 시 anomaly 파일 별도 저장
- 추가 필터링은 처리 시간이 크게 증가할 수 있음
8. 변경 Log
------------------------------------------------------------
[v3.16]  구분자 인식 오류 수정, 중복 헤더 오류 수정, 다중 필터 추가
[v3.211] xlsx/xls 병합 지원, 빈행 삭제, 헤더 표시명 변경, UI 상태관리 개선
[v3.313] 구분자 오인식 정리(탭 구분자)
         예외행(anomaly) 보완 병합 기능 추가 (STEP1 추출 + STEP2 Parquet 병합)
         기타 코드 정리(by Claude)
"""
        win = tk.Toplevel(self)
        win.title("txtGL Filter v3 사용 안내")
        win.geometry("900x700")
        win.minsize(700, 500)
        frm = tk.Frame(win)
        frm.pack(fill="both", expand=True, padx=10, pady=10)
        frm.rowconfigure(0, weight=1)
        frm.columnconfigure(0, weight=1)
        txt = tk.Text(frm, wrap="word", font=("맑은 고딕", 10))
        txt.insert("1.0", manual_text)
        txt.configure(state="disabled")
        txt.grid(row=0, column=0, sticky="nsew")
        sb = tk.Scrollbar(frm, orient="vertical", command=txt.yview)
        sb.grid(row=0, column=1, sticky="ns")
        txt.configure(yscrollcommand=sb.set)
        ctk.CTkButton(win, text="닫기", command=win.destroy, width=120).pack(pady=(0, 10))
    # -----------------------------------------------------------------------
    # 인코딩 감지 / 구분자 감지
    # -----------------------------------------------------------------------
    def _detect_encoding_for_merge(self, path: str) -> str:
        try:
            with open(path, "rb") as f:
                raw = f.read(100_000)
            det = chardet.detect(raw)
            enc = (det.get("encoding") or "utf-8").lower()
            if enc in ("euc-kr", "ks_c_5601-1987", "x-windows-949"):
                return "cp949"
            if enc in ("ascii", "iso-8859-1", "windows-1252", "latin1"):
                return "utf-8"
            return enc
        except Exception:
            return "utf-8"
    def _detect_delimiter(self, sample_lines: list) -> str:
        """
        구분자 자동 감지.
    
        기존 단순 출현 횟수 방식은 적요에 콤마/세미콜론이 많은 경우 오탐 가능.
        개선 방식:
        - 후보 구분자별로 샘플 행을 파싱
        - 열 수가 2개 이상이고
        - 행별 열 수가 가장 일관적인 구분자를 우선 선택
        - 동점이면 평균 열 수가 큰 구분자를 선택
        """
        candidates = ["|", "\t", ",", ";"]
        best_delim = "|"
        best_score = None
    
        lines = [line.rstrip("\r\n") for line in sample_lines if str(line).strip()]
        if not lines:
            return "|"
    
        for delim in candidates:
            try:
                lengths = []
                for line in lines:
                    row = next(csv.reader([line], **self._csv_reader_kwargs(delim)))
                    lengths.append(len(row))
    
                if not lengths:
                    continue
    
                avg_len = sum(lengths) / len(lengths)
                max_len = max(lengths)
                min_len = min(lengths)
                spread = max_len - min_len
    
                # 구분자로서 의미 없으면 제외
                if max_len <= 1:
                    continue
    
                # score가 낮을수록 좋음
                # 1순위: 열 수 일관성
                # 2순위: 평균 열 수 많음
                score = (spread, -avg_len)
    
                if best_score is None or score < best_score:
                    best_score = score
                    best_delim = delim
    
            except Exception:
                continue
    
        return best_delim
    def _normalize_delimiter(self, value) -> str:
        if value in ("\t", "\\t", "TAB", "Tab", "tab", "탭"):
            return "\t"
        return str(value) if value else "|"
    def _csv_reader_kwargs(self, delimiter: str) -> dict:
        """
        csv.reader 공통 옵션.
    
        정확성 기준:
        - 탭(\t), 세로바(|): SAP/GL 원장 추출 파일 성격상 quotechar를 사용하지 않음.
          단독 큰따옴표(")를 quote 시작으로 오인하지 않기 위함.
        - 콤마(,), 세미콜론(;): 일반 CSV 규칙을 적용하여 quote로 감싼 필드 내 구분자/줄바꿈을 허용.
        """
        delimiter = self._normalize_delimiter(delimiter)
    
        if delimiter in ("\t", "|"):
            return {
                "delimiter": delimiter,
                "quoting": csv.QUOTE_NONE,
                "escapechar": "\\",
                "strict": False,
            }
    
        return {
            "delimiter": delimiter,
            "quotechar": '"',
            "doublequote": True,
            "strict": False,
        }
    def _csv_writer_kwargs(self, delimiter: str) -> dict:
        """
        csv.writer 공통 옵션.
    
        - 탭(\t), 세로바(|): QUOTE_NONE
        - 콤마(,), 세미콜론(;): QUOTE_MINIMAL
    
        주의:
        - QUOTE_NONE 상태에서 필드 안에 실제 구분자(| 또는 탭)가 있으면 escapechar로 escape될 수 있음.
        - 원장 분석 목적상 필드 내부 구분자는 원본 데이터 품질 이슈로 보는 것이 안전함.
        """
        delimiter = self._normalize_delimiter(delimiter)
    
        base = {
            "delimiter": delimiter,
            "lineterminator": "\n",
        }
    
        if delimiter in ("\t", "|"):
            base.update({
                "quoting": csv.QUOTE_NONE,
                "escapechar": "\\",
            })
        else:
            base.update({
                "quotechar": '"',
                "quoting": csv.QUOTE_MINIMAL,
                "doublequote": True,
            })
    
        return base
    def _dask_read_csv_kwargs(self, delimiter: str) -> dict:
        """
        Dask/Pandas read_csv 공통 quote 옵션.
    
        - 탭(\t), 세로바(|): quote 해석을 끔.
          단독 큰따옴표(")를 일반 문자로 처리.
        - 콤마(,), 세미콜론(;): quotechar='"' 규칙 유지.
        """
        delimiter = self._normalize_delimiter(delimiter)
    
        if delimiter in ("\t", "|"):
            return {
                "quoting": csv.QUOTE_NONE,
                "escapechar": "\\",
            }
    
        return {
            "quotechar": '"',
            "doublequote": True,
        }
    def _parse_csv_line(self, line: str, delimiter: str) -> list:
        """한 줄을 안전하게 파싱 (헤더 읽기 전용)."""
        line = line.rstrip("\r\n")
        delimiter = self._normalize_delimiter(delimiter)
        try:
            return next(csv.reader([line], **self._csv_reader_kwargs(delimiter)))
        except Exception:
            return line.split(delimiter)
    # -----------------------------------------------------------------------
    # 파일 읽기 유틸 (병합·미리보기용)
    # -----------------------------------------------------------------------
    def _read_preview_lines_for_any_file(self, path: str, max_lines=10,
                                          force_delimiter: str | None = None) -> list:
        """
        파일 미리보기 (논리 레코드 단위).
        force_delimiter 지정 시 self.delimiter.get() 대신 해당 구분자 사용.
        """
        ext = os.path.splitext(path)[1].lower()
        # ③ force_delimiter 파라미터 추가: _patch_parquet_from_file 등에서
        #    _parquet_delimiter를 직접 전달하여 UI 구분자와 불일치 방지
        delimiter = self._normalize_delimiter(
            force_delimiter if force_delimiter is not None else self.delimiter.get())
        preview_lines = []
        if ext in (".txt", ".csv"):
            enc = self._detect_encoding_for_merge(path)
            try:
                with open(path, "r", encoding=enc, errors="replace", newline="") as f:
                    reader = csv.reader(f, **self._csv_reader_kwargs(delimiter))
                    for i, row in enumerate(reader):
                        if i >= max_lines:
                            break
                        preview_lines.append(
                            delimiter.join("" if v is None else str(v) for v in row))
            except Exception:
                with open(path, "r", encoding=enc, errors="replace") as f:
                    for _ in range(max_lines):
                        line = f.readline()
                        if not line:
                            break
                        preview_lines.append(line.rstrip("\r\n"))
        elif ext == ".xlsx":
            try:
                from openpyxl import load_workbook
                wb = load_workbook(filename=path, read_only=True, data_only=True)
                ws = wb.active
                for i, row in enumerate(ws.iter_rows(values_only=True)):
                    if i >= max_lines:
                        break
                    values = ["" if v is None else str(v) for v in row]
                    preview_lines.append(delimiter.join(values))
                wb.close()
            except Exception:
                df_p = pd.read_excel(path, header=None, nrows=max_lines, dtype=str).fillna("")
                for _, row in df_p.iterrows():
                    preview_lines.append(delimiter.join(str(v) for v in row))
        elif ext == ".xls":
            df_p = pd.read_excel(path, header=None, nrows=max_lines, dtype=str).fillna("")
            for _, row in df_p.iterrows():
                preview_lines.append(delimiter.join(str(v) for v in row))
        return preview_lines
    def _iter_rows_from_any_file(self, path: str, delimiter: str, base_encoding=None):
        """파일 종류 무관 행 단위 스트리밍 (병합용)."""
        ext = os.path.splitext(path)[1].lower()
        delimiter = self._normalize_delimiter(delimiter)
        if ext in (".txt", ".csv"):
            enc = base_encoding or self._detect_encoding_for_merge(path)
            # ⑤ errors="replace": 인코딩 오류 한 글자에서 전체 중단 방지
            with open(path, "r", encoding=enc, errors="replace", newline="") as f:
                reader = csv.reader(f, **self._csv_reader_kwargs(delimiter))
                for row in reader:
                    if row is None:
                        continue
                    if not row or not any(str(v).strip() for v in row):
                        continue
                    yield [str(v).strip() if v is not None else "" for v in row]
        elif ext == ".xlsx":
            from openpyxl import load_workbook
            wb = None
            try:
                wb = load_workbook(filename=path, read_only=True, data_only=True)
                ws = wb.active
                for row in ws.iter_rows(values_only=True):
                    if row is None:
                        continue
                    values = ["" if v is None else str(v).strip() for v in row]
                    if not any(values):
                        continue
                    yield values
            finally:
                if wb is not None:
                    try:
                        wb.close()
                    except Exception:
                        pass
        elif ext == ".xls":
            df = pd.read_excel(path, header=None, dtype=str).fillna("")
            for row in df.itertuples(index=False, name=None):
                values = [str(v).strip() if v is not None else "" for v in row]
                if not any(values):
                    continue
                yield values
    def _align_row_to_header(self, row_dict: dict, standard_header: list) -> list:
        return [row_dict.get(col, "") for col in standard_header]
    def _normalize_row_length(self, row: list, target_len: int) -> list:
        row = list(row)
        if len(row) < target_len:
            row.extend([""] * (target_len - len(row)))
        elif len(row) > target_len:
            row = row[:target_len]
        return row
    def _make_unique_headers(self, headers: list) -> list:
        """중복 헤더 처리 (빈 헤더 → 컬럼N)."""
        seen: dict = {}
        unique = []
        for i, h in enumerate(headers):
            base = h.strip() if h.strip() else f"컬럼{i}"
            if base not in seen:
                seen[base] = 0
                unique.append(base)
            else:
                seen[base] += 1
                unique.append(f"{base}_{seen[base]}")
        return unique
    # -----------------------------------------------------------------------
    # 원시파일 병합
    # -----------------------------------------------------------------------
    def merge_raw_files(self):
        valid_ext = (".txt", ".csv", ".xlsx", ".xls")
        paths = filedialog.askopenfilenames(
            title="통합할 파일들 선택",
            filetypes=[
                ("지원 파일", "*.txt;*.csv;*.xlsx;*.xls"),
                ("텍스트 파일", "*.txt"), ("CSV 파일", "*.csv"),
                ("Excel 파일", "*.xlsx;*.xls"),
            ],
        )
        if not paths:
            return
        paths = [p for p in paths if os.path.splitext(p)[1].lower() in valid_ext]
        if not paths:
            messagebox.showwarning("파일 없음", "선택한 파일 중 지원되는 형식이 없습니다.")
            return
        delimiter = self._normalize_delimiter(self.delimiter.get())
        selected_header_cols = None
        base_encoding = None
        try:
            use_custom_header = messagebox.askyesno(
                "헤더 선택",
                "병합 파일의 헤더 행을 직접 선택하시겠습니까?\n\n"
                "예: 여러 파일의 헤더가 동일하거나 순서가 다를 경우,\n"
                "기준이 될 파일에서 헤더 행을 한 번 선택하여\n"
                "모든 파일을 해당 헤더 순서에 맞춰 병합합니다.",
            )
            if use_custom_header:
                header_file = filedialog.askopenfilename(
                    title="헤더를 선택할 기준 파일 선택",
                    filetypes=[("지원 파일", "*.txt;*.csv;*.xlsx;*.xls")],
                )
                if not header_file:
                    messagebox.showinfo("취소", "헤더 선택이 취소되어 병합도 중단됩니다.")
                    return
                if os.path.splitext(header_file)[1].lower() not in valid_ext:
                    messagebox.showerror("형식 오류", "헤더 기준 파일은 txt/csv/xlsx/xls만 지원합니다.")
                    return
                base_encoding = (self._detect_encoding_for_merge(header_file)
                                 if os.path.splitext(header_file)[1].lower() in (".txt", ".csv")
                                 else "utf-8")
                preview_lines = self._read_preview_lines_for_any_file(header_file, max_lines=10)
                if not preview_lines:
                    messagebox.showerror("오류", "기준 파일에서 미리볼 행을 찾을 수 없습니다.")
                    return
                header_index_var = tk.IntVar(value=-1)
                top = tk.Toplevel(self)
                top.title("헤더 행 선택 (더블클릭)")
                top.geometry("900x320")
                top.grab_set()
                tk.Label(
                    top,
                    text=f"기준 파일: {os.path.basename(header_file)}\n"
                         "아래 목록에서 헤더에 해당하는 행을 더블클릭하여 선택하세요.",
                    anchor="w", justify="left",
                ).pack(fill="x", padx=10, pady=5)
                lb = tk.Listbox(top, height=min(10, len(preview_lines)))
                lb.pack(fill="both", expand=True, padx=10, pady=5)
                for idx, line in enumerate(preview_lines):
                    lb.insert("end", f"{idx}: {line}")
                def on_header_dbl(event):
                    sel = lb.curselection()
                    if sel:
                        header_index_var.set(sel[0])
                        top.destroy()
                def on_cancel():
                    header_index_var.set(-1)
                    top.destroy()
                lb.bind("<Double-Button-1>", on_header_dbl)
                tk.Button(top, text="취소", command=on_cancel).pack(pady=5)
                self.wait_window(top)
                if header_index_var.get() < 0:
                    messagebox.showinfo("취소", "헤더가 선택되지 않아 병합을 중단합니다.")
                    return
                selected_idx = header_index_var.get()
                for i, row in enumerate(
                        self._iter_rows_from_any_file(header_file, delimiter, base_encoding)):
                    if i == selected_idx:
                        selected_header_cols = [str(c).strip() for c in row]
                        break
                if not selected_header_cols:
                    raise ValueError("기준 헤더 행을 읽지 못했습니다.")
            else:
                first_file = paths[0]
                base_encoding = (self._detect_encoding_for_merge(first_file)
                                 if os.path.splitext(first_file)[1].lower() in (".txt", ".csv")
                                 else "utf-8")
                first_iter = self._iter_rows_from_any_file(first_file, delimiter, base_encoding)
                try:
                    selected_header_cols = [str(c).strip() for c in next(first_iter)]
                except StopIteration:
                    raise ValueError("첫 번째 파일에서 헤더를 읽을 수 없습니다.")
            selected_header_cols = self._make_unique_headers(selected_header_cols)
            standard_header_len  = len(selected_header_cols)
            first_name   = os.path.splitext(os.path.basename(paths[0]))[0]
            timestamp    = datetime.datetime.now().strftime("%y%m%d_%H%M%S")
            default_name = f"병합_{first_name}_{timestamp}.txt"
            save_path = filedialog.asksaveasfilename(
                defaultextension=".txt",
                title="저장 위치 및 파일명 선택",
                initialfile=default_name,
                filetypes=[("텍스트 파일", "*.txt"), ("CSV 파일", "*.csv"),
                           ("모든 파일", "*.*")],
            )
            if not save_path:
                return
        except Exception as e:
            messagebox.showerror("오류", f"병합 준비 실패:\n{e}")
            return
        self.begin_busy(parquet_message="📄 원시파일 병합 준비 중...")
        output_encoding = base_encoding or "utf-8"
        def _do_merge():
            skipped_files = []
            detail_errors = []
            total_written = 0
            # 진행도: 파일 수 기반 (파일 크기 합산 없이 단순 카운터)
            n_files = len(paths)
            try:
                with open(save_path, "w", encoding=output_encoding, newline="") as outfile:
                    writer = csv.writer(outfile, **self._csv_writer_kwargs(delimiter))
                    writer.writerow(selected_header_cols)
                    total_written += 1
                    for f_idx, fpath in enumerate(paths):
                        fname = os.path.basename(fpath)
                        # 0.05 ~ 0.90 구간을 파일 수로 균등 분할
                        self.update_parquet_status(
                            f"📄 원시파일 병합 중... ({f_idx + 1}/{n_files}) {fname}"
                        )
                        try:
                            ext = os.path.splitext(fpath)[1].lower()
                            file_enc = base_encoding if ext in (".txt", ".csv") else None
                            row_iter = self._iter_rows_from_any_file(fpath, delimiter, file_enc)
                            try:
                                file_header_raw = next(row_iter)
                            except StopIteration:
                                continue
                            file_header    = self._make_unique_headers(
                                [str(c).strip() for c in file_header_raw])
                            header_idx_map = {col: i for i, col in enumerate(file_header)}
                            for row in row_iter:
                                if not any(str(v).strip() for v in row):
                                    continue
                                row = self._normalize_row_length(row, len(file_header))
                                row_dict    = {cn: row[i] if i < len(row) else ""
                                               for cn, i in header_idx_map.items()}
                                aligned_row = self._align_row_to_header(
                                    row_dict, selected_header_cols)
                                aligned_row = self._normalize_row_length(
                                    aligned_row, standard_header_len)
                                writer.writerow(
                                    ["" if v is None else str(v) for v in aligned_row])
                                total_written += 1
                        except Exception as e:
                            skipped_files.append(os.path.basename(fpath))
                            detail_errors.append(f"{os.path.basename(fpath)}: {e}")
                msg_lines = [
                    f"{len(paths)}개 파일 병합 완료:",
                    save_path, "",
                    f"📌 기준 헤더 열 수: {len(selected_header_cols):,}",
                    f"📊 기록된 총 행 수(헤더 포함): {total_written:,}",
                ]
                if skipped_files:
                    msg_lines += ["", "⚠️ 처리 중 오류가 발생한 파일:"]
                    msg_lines += [f" - {n}" for n in skipped_files]
                if detail_errors:
                    msg_lines += ["", "상세 오류:"]
                    msg_lines += [f" - {err}" for err in detail_errors[:10]]
                def _on_done():
                    self.update_parquet_status(
                        f"✅ 원시파일 병합 완료: {os.path.basename(save_path)} "
                        f"({total_written:,}행)"
                    )
                    self.end_busy()
                    messagebox.showinfo("완료", "\n".join(msg_lines))
                self.ui_call(_on_done)
            except Exception as e:
                def _on_err(err=e):
                    self.update_parquet_status("❌ 병합 실패")
                    self.end_busy()
                    messagebox.showerror("오류", f"파일 병합 실패:\n{err}")
                self.ui_call(_on_err)
        threading.Thread(target=_do_merge, daemon=True).start()
    # -----------------------------------------------------------------------
    # 빈행 삭제
    # -----------------------------------------------------------------------
    def show_blank_delete_dialog(self):
        if not self.parquet_exists or not self.df_path:
            messagebox.showwarning("경고", "먼저 Parquet 파일을 준비하세요.")
            return
        if not self.headers:
            messagebox.showwarning("경고", "헤더 정보를 불러오지 못했습니다.")
            return
        dialog = ctk.CTkToplevel(self)
        dialog.title("빈행데이터 삭제")
        dialog.geometry("520x300")
        dialog.resizable(False, False)
        dialog.grab_set()
        outer = ctk.CTkFrame(dialog, fg_color="transparent")
        outer.pack(fill="both", expand=True, padx=20, pady=20)
        ctk.CTkLabel(outer, text="빈행데이터 삭제",
                     font=("맑은 고딕", 15, "bold"), anchor="w").pack(fill="x", pady=(0, 12))
        ctk.CTkLabel(
            outer,
            text="선택한 헤더 열에서 빈값/공백/NaN/__BLANK__ 로 식별되는 행만\n"
                 "현재 Parquet에서 삭제합니다.\n삭제된 행은 별도 txt 파일로 저장됩니다.",
            justify="left", anchor="w", font=("맑은 고딕", 11),
        ).pack(fill="x", pady=(0, 15))
        form_frame = ctk.CTkFrame(outer, fg_color="#f4f4f4", corner_radius=8)
        form_frame.pack(fill="x", pady=(0, 15))
        ctk.CTkLabel(form_frame, text="삭제 기준 헤더",
                     font=("맑은 고딕", 11, "bold"), anchor="w", width=110
                     ).grid(row=0, column=0, padx=(15, 10), pady=15, sticky="w")
        selected_col_var = tk.StringVar(value=self.headers[0] if self.headers else "")
        ctk.CTkOptionMenu(form_frame, values=self.headers,
                          variable=selected_col_var, width=300
                          ).grid(row=0, column=1, padx=(0, 15), pady=15, sticky="ew")
        form_frame.grid_columnconfigure(1, weight=1)
        ctk.CTkLabel(outer, text="※ 삭제 후 기존 Parquet는 새 결과로 교체됩니다.",
                     text_color="gray", font=("맑은 고딕", 10), anchor="w"
                     ).pack(fill="x", pady=(0, 18))
        btn_frame = ctk.CTkFrame(outer, fg_color="transparent")
        btn_frame.pack(fill="x")
        def on_confirm():
            sel_disp = selected_col_var.get().strip()
            if not sel_disp:
                messagebox.showwarning("경고", "헤더를 선택하세요.")
                return
            sel_orig = self._original_header(sel_disp)
            if not messagebox.askyesno(
                "삭제 확인",
                f"[{sel_disp}] 열이 빈값인 행을 현재 Parquet에서 삭제합니다.\n\n"
                "삭제된 행은 txt 파일로 별도 저장됩니다.\n계속 진행할까요?",
            ):
                return
            dialog.destroy()
            self.delete_blank_rows_from_parquet(sel_orig)
        ctk.CTkButton(btn_frame, text="삭제 실행", width=140,
                      command=on_confirm).pack(side="right", padx=(10, 0))
        ctk.CTkButton(btn_frame, text="취소", width=140,
                      fg_color="#d9534f", hover_color="#c9302c",
                      command=dialog.destroy).pack(side="right")
    def delete_blank_rows_from_parquet(self, target_column: str):
        if self.busy:
            return
        self.begin_busy(analysis_message=f"🧹 빈행 삭제 중... ({target_column})",
                        analysis_progress=0.2)
        start_time = time.time()
        def task():
            temp_parquet_path   = None
            backup_parquet_path = None
            try:
                parquet_path = self.df_path + ".parquet"
                if not os.path.exists(parquet_path):
                    raise FileNotFoundError("Parquet 경로를 찾을 수 없습니다.")
                ddf = dd.read_parquet(parquet_path)
                if target_column not in ddf.columns:
                    raise KeyError(f"선택한 헤더가 Parquet에 존재하지 않습니다: {target_column}")
                before_rows = self._count_parquet_rows_from_metadata(parquet_path) or 0
                self.update_analysis_status("📄 삭제 대상 행 추출 중...", 0.35)
                def _removed_only(df, col):
                    s = df[col].fillna("").astype(str).str.strip()
                    return df[s.eq("") | s.eq("__BLANK__")]
                removed_df   = ddf.map_partitions(
                    _removed_only, target_column, meta=ddf._meta).compute()
                deleted_rows = len(removed_df)
                after_rows   = before_rows - deleted_rows
                if deleted_rows <= 0:
                    def no_target():
                        self.update_analysis_status("ℹ️ 삭제 대상 없음", 1.0)
                        self.end_busy("parquet_ready")
                        messagebox.showinfo("완료",
                            f"[{target_column}] 열에서 삭제할 빈행 데이터가 없습니다.")
                    self.ui_call(no_target)
                    return
                self.update_analysis_status("📝 삭제 행 txt 저장 중...", 0.5)
                base_name   = os.path.splitext(os.path.basename(self.df_path))[0]
                timestamp   = datetime.datetime.now().strftime("%y%m%d_%H%M%S")
                safe_col    = re.sub(r"[^\w가-힣]", "", target_column)[:40] or "column"
                deleted_txt = os.path.join(
                    os.path.dirname(self.df_path),
                    f"{base_name}_deleted_blank_rows_{safe_col}_{timestamp}.txt")
                with open(deleted_txt, "w", encoding="utf-8") as fout:
                    fout.write("📄 빈행데이터 삭제 로그\n")
                    fout.write(f"원본 파일: {os.path.basename(self.df_path)}\n")
                    fout.write(f"삭제 기준 헤더: {target_column}\n")
                    fout.write(f"삭제 행 수: {deleted_rows:,}\n")
                    fout.write(f"생성 시각: {datetime.datetime.now()}\n")
                    fout.write("-" * 100 + "\n")
                    fout.write("\t".join(str(c) for c in removed_df.columns) + "\n")
                    fout.write("-" * 100 + "\n")
                    for _, row in removed_df.iterrows():
                        vals = [
                            "" if pd.isna(row[c]) else str(row[c]).replace("\n", " ")
                            for c in removed_df.columns
                        ]
                        fout.write("\t".join(vals) + "\n")
                self.update_analysis_status("📦 새 Parquet 생성 중...", 0.7)
                def _keep_non_blank(df, col):
                    s = df[col].fillna("").astype(str).str.strip()
                    return df[~(s.eq("") | s.eq("__BLANK__"))]
                filtered_ddf      = ddf.map_partitions(
                    _keep_non_blank, target_column, meta=ddf._meta)
                temp_parquet_path = parquet_path + ".__tmp_blank_delete__"
                if os.path.exists(temp_parquet_path):
                    shutil.rmtree(temp_parquet_path, ignore_errors=True)
                filtered_ddf.to_parquet(temp_parquet_path, compression="snappy",
                                        write_index=False)
                backup_parquet_path = parquet_path + ".__bak_blank_delete__"
                if os.path.exists(backup_parquet_path):
                    shutil.rmtree(backup_parquet_path, ignore_errors=True)
                os.replace(parquet_path, backup_parquet_path)
                os.replace(temp_parquet_path, parquet_path)
                shutil.rmtree(backup_parquet_path, ignore_errors=True)
                backup_parquet_path = None
                try:
                    self.last_parquet_npartitions = filtered_ddf.npartitions
                    self._append_parquet_summary_log(
                        after_rows, parquet_path,
                        getattr(self, "_parquet_blocksize_label", self.blocksize_var.get()))
                except Exception as log_e:
                    print(f"[Parquet 로그 재작성 실패] {log_e}")
                elapsed = time.time() - start_time
                def on_done():
                    self.update_analysis_status(
                        f"✅ 빈행 {deleted_rows:,}건 삭제 완료 / ⏱ {elapsed:.2f}초", 1.0)
                    self.load_file_from_parquet()
                    self.end_busy("parquet_ready")
                    messagebox.showinfo(
                        "완료",
                        f"[{target_column}] 열 기준 빈행 삭제가 완료되었습니다.\n\n"
                        f"삭제 전 행 수: {before_rows:,}\n"
                        f"삭제 후 행 수: {after_rows:,}\n"
                        f"삭제된 행 수: {deleted_rows:,}\n"
                        f"삭제행 txt 저장: {deleted_txt}\n"
                        f"소요 시간: {elapsed:.2f}초",
                    )
                self.ui_call(on_done)
            except Exception as e:
                try:
                    parquet_path = self.df_path + ".parquet"
                    for tmp in [temp_parquet_path, backup_parquet_path]:
                        if tmp and os.path.exists(tmp):
                            shutil.rmtree(tmp, ignore_errors=True)
                    if (backup_parquet_path and os.path.exists(backup_parquet_path)
                            and not os.path.exists(parquet_path)):
                        os.replace(backup_parquet_path, parquet_path)
                except Exception as rb_e:
                    print(f"[롤백 실패] {rb_e}")
                def on_error(err=e):
                    self.update_analysis_status("❌ 빈행 삭제 실패", 0.0)
                    self.end_busy("parquet_ready")
                    messagebox.showerror("빈행 삭제 오류", f"{type(err).__name__}: {err}")
                self.ui_call(on_error)
        threading.Thread(target=task, daemon=True).start()
    # -----------------------------------------------------------------------
    # anomaly 보완 병합 (신규)
    # -----------------------------------------------------------------------
    def show_patch_parquet_dialog(self):
        """
        anomaly [열 개수 불일치] 행을 사용자가 Excel에서 전처리한 후
        기존 Parquet에 병합 추가하는 워크플로 안내 + 실행 다이얼로그.
        ⑧ Parquet 폴더 직접 선택 시 _parquet_delimiter가 기본값일 수 있음을 안내.
        """
        if not self.parquet_exists or not self.df_path:
            messagebox.showwarning("경고", "먼저 Parquet 파일을 준비하세요.")
            return
        dialog = ctk.CTkToplevel(self)
        dialog.title("🩹 예외행 보완")
        dialog.resizable(False, False)
        dialog.grab_set()
        outer = ctk.CTkFrame(dialog, fg_color="transparent")
        outer.pack(fill="both", expand=True, padx=20, pady=20)
        ctk.CTkLabel(outer, text="🩹 예외행 보완",
                     font=("맑은 고딕", 15, "bold"), anchor="w").pack(fill="x", pady=(0, 10))
        n_cols    = len(self.original_headers)
        delimiter = self._parquet_delimiter
        # ⑧ Parquet 폴더 직접 선택 시 구분자 확인 안내
        folder_warn = ""
        if not (self.df_path and os.path.exists(self.df_path)):
            folder_warn = "\n⚠️ Parquet 폴더 직접 선택 시 구분자를 수동으로 확인하세요."
        guide = (
            "【사용 순서】\n\n"
            "① [STEP 1] 버튼으로 열 개수 불일치 행 추출 → csv 저장\n"
            "② 저장된 csv를 Excel에서 열어 구분자/줄바꿈 문제 수동 수정\n"
            "   (적요 등 필드 내 구분자·줄바꿈 제거 또는 열 수 맞춤)\n"
            f"   ※ 열 개수를 기준 헤더({n_cols}개)와 동일하게 맞춰야 함\n"
            "③ 수정한 파일을 csv로 저장\n"
            "④ [STEP 2] 버튼으로 수정 파일 선택 → 기존 Parquet에 병합 추가\n\n"
            f"📌 기준 헤더 열 수: {n_cols}개\n"
            f"📌 구분자: [{delimiter}]\n"
            f"📌 인코딩: {self._parquet_encoding}"
            + folder_warn
        )
        # wraplength=580: 창 폭(640) 안에서 텍스트 자동 줄바꿈 → 고정 높이 불필요
        ctk.CTkLabel(outer, text=guide, justify="left", anchor="w",
                     font=("맑은 고딕", 11), wraplength=580).pack(fill="x", pady=(0, 15))
        sep = ctk.CTkFrame(outer, height=2, fg_color="#cccccc")
        sep.pack(fill="x", pady=(0, 15))
        btn_frame = ctk.CTkFrame(outer, fg_color="transparent")
        btn_frame.pack(fill="x", pady=(0, 10))
        ctk.CTkButton(
            btn_frame,
            text="📤 STEP 1: 불일치 행 추출 → csv 저장",
            width=280,
            command=lambda: self._extract_mismatch_rows_to_txt(dialog)
        ).pack(side="left", padx=(0, 10))
        ctk.CTkButton(
            btn_frame,
            text="📥 STEP 2: 수정 파일 → Parquet 병합",
            width=280,
            command=lambda: self._patch_parquet_from_file(dialog)
        ).pack(side="left")
        ctk.CTkButton(outer, text="닫기", width=120,
                      fg_color="#d9534f", hover_color="#c9302c",
                      command=dialog.destroy).pack(pady=(15, 0))
        # 위젯이 모두 배치된 후 실제 필요 높이로 창 크기 자동 결정
        dialog.update_idletasks()
        dialog.geometry(f"640x{dialog.winfo_reqheight()}")
    def _extract_mismatch_rows_to_txt(self, parent_dialog=None):
        """
        anomaly_lines.txt에서 [열 개수 불일치] 행만 추출하여
        사용자가 Excel에서 수정할 수 있는 csv 로 저장.
        ④ csv.writer로 올바르게 저장하여 Excel에서 열었을 때 깨지지 않게 함.
        anomaly 파일 없으면 원시파일에서 직접 추출 제안.
        """
        anomaly_path = os.path.splitext(self.df_path)[0] + "_anomaly_lines.txt"
        if not os.path.exists(anomaly_path):
            answer = messagebox.askyesno(
                "anomaly 파일 없음",
                "anomaly_lines.txt가 없습니다.\n\n"
                "Parquet 생성 시 [완전성 검토 추가]를 체크하면 생성됩니다.\n\n"
                "원시파일에서 직접 [열 개수 불일치] 행을 추출할까요?\n"
                "(파일 크기에 따라 시간이 소요됩니다)"
            )
            if answer:
                self._extract_mismatch_from_raw(parent_dialog)
            return
        try:
            delimiter = self._parquet_delimiter
            n_cols    = len(self.original_headers)
            # ④ parsed 열 리스트로 수집 (원문 문자열 아님)
            mismatch_rows: list[list[str]] = []
            with open(anomaly_path, "r", encoding="utf-8", errors="replace") as f:
                for line in f:
                    if not line.startswith("[열 개수 불일치]"):
                        continue
                    # "[열 개수 불일치] (기대열=N, 실제열=M) 구분자로 재결합된 원문" 형식
                    raw = re.sub(
                        r"^\[열 개수 불일치\]\s*(\(기대열=\d+,\s*실제열=\d+\)\s*)?",
                        "", line
                    ).strip()
                    # 원문을 다시 파싱하여 열 리스트로 복원
                    cols = self._parse_csv_line(raw, delimiter)
                    mismatch_rows.append(cols)
            if not mismatch_rows:
                messagebox.showinfo(
                    "불일치 행 없음",
                    "anomaly_lines.txt에 [열 개수 불일치] 행이 없습니다.\n"
                    "Parquet 데이터가 이미 완전할 수 있습니다."
                )
                return
            timestamp  = datetime.datetime.now().strftime("%y%m%d_%H%M%S")
            base       = os.path.splitext(os.path.basename(self.df_path))[0]
            default_nm = f"{base}_mismatch_rows_{timestamp}.csv"
            save_path  = filedialog.asksaveasfilename(
                defaultextension=".csv",
                title="불일치 행 저장 위치 선택",
                initialfile=default_nm,
                filetypes=[("CSV 파일", "*.csv"), ("텍스트 파일", "*.txt")],
            )
            if not save_path:
                return
            # ④ csv.writer로 정확하게 저장 (필드 내 구분자·줄바꿈 따옴표 처리)
            with open(save_path, "w", encoding="utf-8-sig", newline="") as fout:
                writer = csv.writer(fout, quotechar='"',
                                    quoting=csv.QUOTE_MINIMAL, lineterminator="\n")
                writer.writerow(self.original_headers)
                for cols in mismatch_rows:
                    # 열 수 정렬: 부족→빈칸, 초과→마지막 열에 병합
                    if len(cols) < n_cols:
                        cols = cols + [""] * (n_cols - len(cols))
                    elif len(cols) > n_cols:
                        cols = cols[:n_cols - 1] + [delimiter.join(cols[n_cols - 1:])]
                    writer.writerow(cols)
            messagebox.showinfo(
                "추출 완료",
                f"[열 개수 불일치] 행 {len(mismatch_rows):,}건이 저장되었습니다.\n\n"
                f"📁 {save_path}\n\n"
                f"【다음 단계】\n"
                f"① Excel에서 위 파일을 열어 수정\n"
                f"② 열 개수를 {n_cols}개로 맞춤\n"
                f"   (적요 등 필드 내 구분자·줄바꿈 제거)\n"
                f"③ csv 형식으로 저장\n"
                f"④ STEP 2 버튼으로 Parquet에 병합"
            )
        except Exception as e:
            messagebox.showerror("추출 오류", f"{type(e).__name__}: {e}")
    def _extract_mismatch_from_raw(self, parent_dialog=None):
        """anomaly 파일이 없을 때 원시파일에서 직접 불일치 행 추출 (백그라운드)."""
        if not self.df_path or not os.path.exists(self.df_path):
            messagebox.showerror("오류", "원시파일 경로를 찾을 수 없습니다.")
            return
        self.begin_busy(parquet_message="🔍 원시파일에서 불일치 행 추출 중...")
        delimiter      = self._parquet_delimiter
        encoding       = self._parquet_encoding
        header_row_idx = self._parquet_header_row
        n_cols         = len(self.original_headers)
        def task():
            try:
                mismatch: list[list[str]] = []
                with open(self.df_path, "r", encoding=encoding,
                          errors="replace", newline="") as fin:
                    reader  = csv.reader(fin, **self._csv_reader_kwargs(delimiter))
                    rec_idx = -1
                    for parsed in reader:
                        rec_idx += 1
                        if rec_idx <= header_row_idx:
                            continue
                        cols = [str(c).strip() for c in parsed]
                        if len(cols) != n_cols and any(cols):
                            mismatch.append(cols)
                if not mismatch:
                    def no_result():
                        self.end_busy("parquet_ready")
                        messagebox.showinfo(
                            "결과 없음",
                            "원시파일에서 [열 개수 불일치] 행이 발견되지 않았습니다.\n"
                            "Parquet 데이터가 이미 완전합니다."
                        )
                    self.ui_call(no_result)
                    return
                timestamp  = datetime.datetime.now().strftime("%y%m%d_%H%M%S")
                base       = os.path.splitext(os.path.basename(self.df_path))[0]
                default_nm = f"{base}_mismatch_rows_{timestamp}.csv"
                def do_save():
                    save_path = filedialog.asksaveasfilename(
                        defaultextension=".csv",
                        title="불일치 행 저장 위치 선택",
                        initialfile=default_nm,
                        filetypes=[("CSV 파일", "*.csv"), ("텍스트 파일", "*.txt")],
                    )
                    if not save_path:
                        self.end_busy("parquet_ready")
                        return
                    try:
                        # ④ csv.writer로 정확하게 저장
                        with open(save_path, "w", encoding="utf-8-sig", newline="") as fout:
                            writer = csv.writer(fout, quotechar='"',
                                                quoting=csv.QUOTE_MINIMAL, lineterminator="\n")
                            writer.writerow(self.original_headers)
                            for cols in mismatch:
                                if len(cols) < n_cols:
                                    cols = cols + [""] * (n_cols - len(cols))
                                elif len(cols) > n_cols:
                                    cols = cols[:n_cols - 1] + [
                                        delimiter.join(cols[n_cols - 1:])]
                                writer.writerow(cols)
                        self.end_busy("parquet_ready")
                        messagebox.showinfo(
                            "추출 완료",
                            f"불일치 행 {len(mismatch):,}건 저장 완료.\n\n"
                            f"📁 {save_path}\n\n"
                            "Excel에서 수정 후 STEP 2로 병합하세요."
                        )
                    except Exception as save_e:
                        self.end_busy("parquet_ready")
                        messagebox.showerror("저장 오류", str(save_e))
                self.ui_call(do_save)
            except Exception as e:
                def on_err(err=e):
                    self.end_busy("parquet_ready")
                    messagebox.showerror("추출 오류", str(err))
                self.ui_call(on_err)
        threading.Thread(target=task, daemon=True).start()
    def _patch_parquet_from_file(self, parent_dialog=None):
        """
        사용자가 Excel에서 수정한 파일을 읽어 기존 Parquet에 행 추가 병합.
        헤더 검증 → 열 수 검증 → 임시 Parquet 생성 → 기존과 병합 → 교체.
        """
        if not self.parquet_exists or not self.df_path:
            messagebox.showwarning("경고", "먼저 Parquet 파일을 준비하세요.")
            return
        patch_path = filedialog.askopenfilename(
            title="수정 완료된 파일 선택 (csv / txt / xlsx)",
            filetypes=[
                ("지원 파일", "*.csv;*.txt;*.xlsx"),
                ("CSV/텍스트", "*.csv;*.txt"),
                ("Excel", "*.xlsx"),
            ],
        )
        if not patch_path:
            return
        n_cols    = len(self.original_headers)
        # ③ Parquet 생성 당시 구분자(_parquet_delimiter)를 미리보기에 직접 전달
        delimiter = self._parquet_delimiter
        try:
            preview = self._read_preview_lines_for_any_file(
                patch_path, max_lines=3, force_delimiter=delimiter)
            if not preview:
                messagebox.showerror("오류", "선택한 파일에서 데이터를 읽을 수 없습니다.")
                return
            first_cols = [c.strip() for c in preview[0].split(delimiter)]
            col_count  = len(first_cols)
            if col_count != n_cols:
                if not messagebox.askyesno(
                    "열 수 불일치 경고",
                    f"선택 파일의 열 수({col_count})가\n"
                    f"기존 Parquet 헤더 열 수({n_cols})와 다릅니다.\n\n"
                    f"기존 헤더: {' | '.join(self.original_headers[:5])}"
                    f"{'...' if n_cols > 5 else ''}\n\n"
                    "계속 진행하면 누락 열은 빈칸으로 채워지거나 초과 열은 제거됩니다.\n"
                    "계속하시겠습니까?"
                ):
                    return
        except Exception as prev_e:
            messagebox.showerror("미리보기 오류", str(prev_e))
            return
        if parent_dialog:
            try:
                parent_dialog.destroy()
            except Exception:
                pass
        self.begin_busy(parquet_message="🩹 Parquet 보완 병합 중...")
        def task():
            temp_patch_parquet = None
            merged_parquet     = None
            backup_path        = None
            try:
                parquet_path = self.df_path + ".parquet"
                ext          = os.path.splitext(patch_path)[1].lower()
                self.update_analysis_status("📥 수정 파일 읽는 중...", 0.2)
                if ext in (".txt", ".csv"):
                    patch_enc = self._detect_encoding_for_merge(patch_path)
                    patch_df  = pd.read_csv(
                        patch_path,
                        sep=delimiter,
                        dtype=str,
                        encoding=patch_enc,
                        encoding_errors="replace",
                        keep_default_na=False,
                        na_filter=False,
                        **{**self._dask_read_csv_kwargs(delimiter), **CSV_BADLINE_KWARGS},
                    )
                elif ext == ".xlsx":
                    patch_df = pd.read_excel(patch_path, dtype=str, header=0).fillna("")
                else:
                    raise ValueError(f"지원하지 않는 파일 형식: {ext}")
                patch_df = patch_df.astype(str)
                # 표시명 → 원본명 역변환
                rename_back = {self._display_header(orig): orig
                               for orig in self.original_headers
                               if self._display_header(orig) != orig}
                if rename_back:
                    patch_df.rename(columns=rename_back, inplace=True)
                # 기존 Parquet 헤더 기준 열 정렬 (누락→빈값, 초과→제거)
                for col in self.original_headers:
                    if col not in patch_df.columns:
                        patch_df[col] = ""
                patch_df = patch_df[self.original_headers]
                # ⑦ 완전히 빈 행 제거 — 벡터 연산으로 성능 개선
                valid_mask = (patch_df != "").any(axis=1)
                bad_rows   = int((~valid_mask).sum())
                patch_df   = patch_df[valid_mask].reset_index(drop=True)
                patch_rows = len(patch_df)
                if patch_rows == 0:
                    def no_data():
                        self.end_busy("parquet_ready")
                        messagebox.showwarning(
                            "데이터 없음",
                            "수정 파일에 유효한 데이터 행이 없습니다.\n"
                            "열 수와 내용을 다시 확인하세요."
                        )
                    self.ui_call(no_data)
                    return
                self.update_analysis_status("📦 임시 Parquet 생성 중...", 0.45)
                temp_patch_parquet = parquet_path + ".__tmp_patch__"
                if os.path.exists(temp_patch_parquet):
                    shutil.rmtree(temp_patch_parquet, ignore_errors=True)
                patch_ddf = dd.from_pandas(patch_df, npartitions=1)
                patch_ddf.to_parquet(temp_patch_parquet,
                                     compression="snappy", write_index=False)
                self.update_analysis_status("🔀 기존 Parquet와 병합 중...", 0.65)
                existing_ddf = dd.read_parquet(parquet_path)
                new_ddf      = dd.read_parquet(temp_patch_parquet)
                merged_ddf   = dd.concat(
                    [existing_ddf, new_ddf], ignore_unknown_divisions=True)
                merged_parquet = parquet_path + ".__tmp_merged__"
                if os.path.exists(merged_parquet):
                    shutil.rmtree(merged_parquet, ignore_errors=True)
                merged_ddf.to_parquet(merged_parquet,
                                      compression="snappy", write_index=False)
                self.update_analysis_status("🔄 Parquet 교체 중...", 0.85)
                backup_path = parquet_path + ".__bak_patch__"
                if os.path.exists(backup_path):
                    shutil.rmtree(backup_path, ignore_errors=True)
                os.replace(parquet_path, backup_path)
                os.replace(merged_parquet, parquet_path)
                shutil.rmtree(backup_path, ignore_errors=True)
                backup_path = None
                shutil.rmtree(temp_patch_parquet, ignore_errors=True)
                temp_patch_parquet = None
                merged_parquet     = None
                new_total = self._count_parquet_rows_from_metadata(parquet_path)
                # ⑭ 로그: write_parquet_summary_log_simple("w") 호출 대신
                #         append 전용 함수로 분리하여 기존 검증 요약 유지
                try:
                    self._append_parquet_summary_log(
                        new_total or "N/A", parquet_path,
                        getattr(self, "_parquet_blocksize_label", self.blocksize_var.get()))
                    log_path = self.df_path + "_parquet_log.txt"
                    with open(log_path, "a", encoding="utf-8") as lg:
                        lg.write("\n📌 anomaly 보완 병합\n")
                        lg.write(f"   병합 파일: {os.path.basename(patch_path)}\n")
                        lg.write(f"   추가 행 수: {patch_rows:,}\n")
                        if bad_rows:
                            lg.write(f"   제외 행 수(빈 행): {bad_rows:,}\n")
                        lg.write(
                            f"   병합 후 총 행 수: {new_total:,}\n"
                            if isinstance(new_total, int)
                            else "   병합 후 총 행 수: N/A\n"
                        )
                        lg.write(f"   처리 시각: {datetime.datetime.now()}\n")
                except Exception as log_e:
                    print(f"[병합 로그 갱신 실패] {log_e}")
                def on_done():
                    self.load_file_from_parquet()
                    self.end_busy("parquet_ready")
                    total_text = (f"{new_total:,}" if isinstance(new_total, int) else "N/A")
                    messagebox.showinfo(
                        "병합 완료",
                        f"✅ Parquet 보완 병합이 완료되었습니다.\n\n"
                        f"📥 추가된 행 수: {patch_rows:,}건\n"
                        f"📊 병합 후 총 행 수: {total_text}건\n"
                        f"⚠️ 제외된 빈 행: {bad_rows:,}건\n\n"
                        "Parquet log에서 결과를 확인하세요."
                    )
                self.ui_call(on_done)
            except Exception as e:
                try:
                    parquet_path = self.df_path + ".parquet"
                    for tmp in [temp_patch_parquet, merged_parquet]:
                        if tmp and os.path.exists(tmp):
                            shutil.rmtree(tmp, ignore_errors=True)
                    if (backup_path and os.path.exists(backup_path)
                            and not os.path.exists(parquet_path)):
                        os.replace(backup_path, parquet_path)
                except Exception as rb_e:
                    print(f"[롤백 실패] {rb_e}")
                def on_err(err=e):
                    self.update_analysis_status("❌ 병합 실패", 0.0)
                    self.end_busy("parquet_ready")
                    messagebox.showerror("병합 오류", f"{type(err).__name__}: {err}")
                self.ui_call(on_err)
        threading.Thread(target=task, daemon=True).start()
    # -----------------------------------------------------------------------
    # Pivot UI
    # -----------------------------------------------------------------------
    def create_pivot_widgets(self):
        self.pivot_frame = ctk.CTkFrame(self.dynamic_frame, fg_color="#dcdcdc")
        ctk.CTkLabel(self.pivot_frame, text="📊 피벗 분석 설정",
                     font=("맑은 고딕", 12, "bold")).pack(pady=5)
        list_frame = ctk.CTkFrame(self.pivot_frame, fg_color="#dcdcdc")
        list_frame.pack(pady=5)
        ctk.CTkLabel(list_frame, text="행 기준 필드 (Index)",
                     font=("맑은 고딕", 11)).grid(row=0, column=0, padx=10, pady=2, sticky="w")
        ctk.CTkLabel(list_frame, text="열 기준 필드 (Columns)",
                     font=("맑은 고딕", 11)).grid(row=0, column=1, padx=10, pady=2, sticky="w")
        visible_count = 8
        idx_frm = tk.Frame(list_frame)
        idx_frm.grid(row=1, column=0, padx=10, pady=2)
        self.index_listbox = Listbox(idx_frm, selectmode="extended",
                                     height=visible_count, width=40, exportselection=False)
        self.index_listbox.pack(side="left", fill="y")
        idx_sb = tk.Scrollbar(idx_frm, orient="vertical", command=self.index_listbox.yview)
        idx_sb.pack(side="right", fill="y")
        self.index_listbox.configure(yscrollcommand=idx_sb.set)
        col_frm = tk.Frame(list_frame)
        col_frm.grid(row=1, column=1, padx=10, pady=2)
        self.column_listbox = Listbox(col_frm, selectmode="extended",
                                      height=visible_count, width=40, exportselection=False)
        self.column_listbox.pack(side="left", fill="y")
        col_sb = tk.Scrollbar(col_frm, orient="vertical", command=self.column_listbox.yview)
        col_sb.pack(side="right", fill="y")
        self.column_listbox.configure(yscrollcommand=col_sb.set)
        opt_frm = ctk.CTkFrame(list_frame, fg_color="transparent")
        opt_frm.grid(row=1, column=2, padx=10, pady=2, sticky="n")
        ctk.CTkLabel(opt_frm, text="값 필드 (Value)",
                     font=("맑은 고딕", 11)).pack(anchor="w", pady=(5, 0))
        self.value_var  = tk.StringVar()
        self.value_menu = ctk.CTkOptionMenu(opt_frm, variable=self.value_var,
                                            values=[], width=150)
        self.value_menu.pack(pady=(0, 10))
        ctk.CTkLabel(opt_frm, text="집계 방식 (Sum/Count)",
                     font=("맑은 고딕", 11)).pack(anchor="w")
        self.agg_var  = tk.StringVar(value="합계")
        self.agg_menu = ctk.CTkOptionMenu(opt_frm, variable=self.agg_var,
                                          values=["합계", "개수"], width=150)
        self.agg_menu.pack()
        ctk.CTkLabel(self.pivot_frame,
                     text="※ 추가/삭제: 더블클릭, 순서변경: 원클릭",
                     text_color="gray", font=("맑은 고딕", 10)).pack(anchor="center", pady=(5, 5))
        ctk.CTkLabel(self.pivot_frame, text="선택된 행 필드 (Index)",
                     font=("맑은 고딕", 10)).pack(anchor="center", pady=(10, 2))
        self.index_buttons_frame = ctk.CTkFrame(self.pivot_frame, fg_color="#dcdcdc", height=1)
        self.index_buttons_frame.pack(anchor="center")
        ctk.CTkLabel(self.pivot_frame, text="선택된 열 필드 (Columns)",
                     font=("맑은 고딕", 10)).pack(anchor="center", pady=(5, 2))
        self.column_buttons_frame = ctk.CTkFrame(self.pivot_frame, fg_color="#dcdcdc", height=1)
        self.column_buttons_frame.pack(anchor="center")
        self.index_listbox.bind("<Double-Button-1>", self.toggle_index_field)
        self.column_listbox.bind("<Double-Button-1>", self.toggle_column_field)
        self.selected_index_buttons:  list[str] = []
        self.selected_column_buttons: list[str] = []
    # -----------------------------------------------------------------------
    # Filter UI
    # -----------------------------------------------------------------------
    def create_filter_widgets(self):
        self.filter_frame = ctk.CTkFrame(self.dynamic_frame, fg_color="white")
        ctk.CTkLabel(self.filter_frame, text="🔍 필터링 설정",
                     font=("맑은 고딕", 12, "bold")).pack(pady=5)
        cnt_frm = ctk.CTkFrame(self.filter_frame, fg_color="white")
        cnt_frm.pack(pady=(0, 5))
        ctk.CTkLabel(cnt_frm, text="사용할 필터 개수 (최대 5개):",
                     font=("맑은 고딕", 11)).pack(side="left", padx=(0, 5))
        self.filter_count_menu = ctk.CTkOptionMenu(
            cnt_frm,
            values=[str(i) for i in range(1, self.max_filters + 1)],
            variable=self.active_filter_count_var,
            command=self.on_filter_count_change, width=80)
        self.filter_count_menu.pack(side="left")
        self.filter_toggle = ctk.CTkSegmentedButton(
            self.filter_frame,
            values=[f"필터{i}" for i in range(1, self.max_filters + 1)],
            command=self.on_filter_tab_change)
        self.filter_toggle.set("필터1")
        self.filter_toggle.pack(pady=(5, 10))
        self.filter_col_select = ctk.CTkOptionMenu(
            self.filter_frame, values=[], command=self.on_filter_column_change)
        self.filter_col_select.pack(pady=5)
        ctk.CTkLabel(self.filter_frame,
                     text="※ 키워드 입력: 엔터/콤마/탭/공백 구분 입력 또는 엑셀 붙여넣기",
                     text_color="gray", font=("맑은 고딕", 11)).pack(pady=(10, 2))
        self.keyword_input = ctk.CTkTextbox(self.filter_frame, height=100, width=1000)
        self.keyword_input.pack(pady=5)
        self.keyword_input.bind("<KeyRelease>", self.update_keyword_count)
        self.keyword_count_label = ctk.CTkLabel(
            self.filter_frame, text="입력된 키워드: 0개", text_color="gray")
        self.keyword_count_label.pack(pady=(0, 10))
        self.additional_filter_var = BooleanVar()
        self.additional_filter_checkbox = ctk.CTkCheckBox(
            self.filter_frame,
            text="추가 필터링 활성화(추가시간소요)",
            variable=self.additional_filter_var,
            command=self.toggle_additional_filter)
        self.additional_filter_checkbox.pack(pady=5)
        ctk.CTkLabel(self.filter_frame,
                     text="※ 예: 선택된 키워드가 속한 전표번호 전표 전체 추출",
                     text_color="gray", font=("맑은 고딕", 10)
                     ).pack(anchor="center", padx=10, pady=(0, 10))
        self.additional_col_select = ctk.CTkOptionMenu(self.filter_frame, values=[])
        self.additional_col_select.pack(pady=5)
        self.additional_col_select.configure(state="disabled")
    # -----------------------------------------------------------------------
    # Filter 상태 동기화
    # -----------------------------------------------------------------------
    def _sync_current_filter_from_ui(self):
        idx = self.current_filter_index.get() - 1
        if 0 <= idx < self.max_filters:
            self.filter_columns[idx]       = self._original_header(self.filter_col_select.get())
            self.filter_keyword_texts[idx] = self.keyword_input.get("1.0", "end").strip()
    def _load_filter_to_ui(self, idx: int):
        if not 0 <= idx < self.max_filters:
            return
        self.current_filter_index.set(idx + 1)
        self._refresh_filter_header_options()
        self.keyword_input.delete("1.0", "end")
        self.keyword_input.insert("1.0", self.filter_keyword_texts[idx] or "")
        self.update_keyword_count()
    def _refresh_filter_header_options(self):
        if not hasattr(self, "filter_col_select"):
            return
        headers = self.original_headers or []
        if not headers:
            self.filter_col_select.configure(values=[])
            self.filter_col_select.set("")
            return
        active_count = self.active_filter_count_var.get()
        idx          = self.current_filter_index.get() - 1
        used = {self.filter_columns[i] for i in range(active_count)
                if i != idx and self.filter_columns[i]}
        options_original = [h for h in headers if h not in used]
        current_original = (self.filter_columns[idx]
                            if 0 <= idx < self.max_filters else "")
        if (current_original and current_original in headers
                and current_original not in options_original):
            options_original.insert(0, current_original)
        if not options_original:
            options_original = headers[:]
        options_display = [self._display_header(h) for h in options_original]
        self.filter_col_select.configure(values=options_display)
        if current_original and current_original in headers:
            self.filter_col_select.set(self._display_header(current_original))
        elif options_original and 0 <= idx < self.max_filters:
            self.filter_columns[idx] = options_original[0]
            self.filter_col_select.set(self._display_header(options_original[0]))
        else:
            self.filter_col_select.set("")
    def on_filter_count_change(self, value):
        try:
            new_count = max(1, min(self.max_filters, int(value)))
        except Exception:
            new_count = 1
        self.active_filter_count_var.set(new_count)
        if self.current_filter_index.get() > new_count:
            self.current_filter_index.set(new_count)
            self.filter_toggle.set(f"필터{new_count}")
        self._refresh_filter_header_options()
        self.update_keyword_count()
    def on_filter_tab_change(self, value: str):
        try:
            idx = int("".join(ch for ch in value if ch.isdigit())) - 1
        except Exception:
            return
        if idx >= self.active_filter_count_var.get():
            self.filter_toggle.set(f"필터{self.current_filter_index.get()}")
            return
        self._sync_current_filter_from_ui()
        self._load_filter_to_ui(idx)
    def on_filter_column_change(self, selected_column: str):
        idx = self.current_filter_index.get() - 1
        if 0 <= idx < self.max_filters:
            self.filter_columns[idx] = self._original_header(selected_column)
            self._refresh_filter_header_options()
    def update_keyword_count(self, event=None):
        text = self.keyword_input.get("1.0", "end").strip()
        kws  = list(filter(None, map(str.strip, re.split(r"[\n\r\t, ]+", text))))
        self.keyword_count_label.configure(text=f"입력된 키워드: {len(kws)}개")
    def switch_mode(self, mode: str):
        self.selected_analysis = mode
    
        for w in self.dynamic_frame.winfo_children():
            w.pack_forget()
    
        if mode == "Pivot":
            self.pivot_frame.pack(fill="both", expand=True, pady=10)
            self.update_status(self.pivot_status_message, save=False)
    
        elif mode == "Filter":
            self.filter_frame.pack(fill="both", expand=True, pady=10)
            self.update_status(self.filter_status_message, save=False)
            self.after(100, self.toggle_additional_filter)
    
        self.update_result_buttons()
        self.after(50, self.adjust_window_height)
        self.refresh_ui_state()
    def toggle_additional_filter(self):
        state = ("normal"
                 if (self.additional_filter_var.get()
                     and not self.busy
                     and self.ui_state == "parquet_ready"
                     and self.selected_analysis == "Filter")
                 else "disabled")
        self.additional_col_select.configure(state=state)
    def update_encoding(self, selected_encoding: str):
        self.encoding = ENCODING_MAP.get(selected_encoding, "utf-8")
        self.encoding_label.configure(text=f"식별된인코딩: {selected_encoding}")
    # -----------------------------------------------------------------------
    # 초기화
    # -----------------------------------------------------------------------
    def reset_ui(self):
        self.parquet_exists = False
        self.headers        = []
        self.original_headers       = []
        self.header_display_map     = {}
        self.display_to_original_map = {}
        self.df_path = None
        self.index_listbox.delete(0, "end")
        self.column_listbox.delete(0, "end")
        self.value_menu.set("")
        self.value_menu.configure(values=[])
        self.filter_col_select.set("")
        self.filter_col_select.configure(values=[])
        self.keyword_input.delete("1.0", "end")
        self.additional_col_select.set("")
        self.additional_col_select.configure(values=[], state="disabled")
        self.header_preview.configure(height=5, state="normal")
        self.header_preview.delete(0, tk.END)
        self.encoding_var.set("")
        self.encoding_label.configure(text="식별된인코딩: 미확인")
        self.update_parquet_status("분석 준비 전: 파일을 먼저 선택하세요.")
        self.progress_label.configure(text="")
        self.progress_bar.set(0)
        self.dynamic_frame.pack_forget()
        self.mode_frame.pack_forget()
        self.action_frame.pack_forget()
        self.filter_result_file    = ""
        self.filter_result_parts   = []
        self.pivot_result_file     = ""
        self.filter_status_message = ""
        self.pivot_status_message  = ""
        self.result_file_label.configure(text="")
        self.active_filter_count_var.set(1)
        self.current_filter_index.set(1)
        self.filter_columns       = [""] * self.max_filters
        self.filter_keyword_texts = [""] * self.max_filters
        try:
            self.filter_count_menu.set("1")
            self.filter_toggle.set("필터1")
        except Exception:
            pass
        self.keyword_count_label.configure(text="입력된 키워드: 0개")
        self.additional_filter_var.set(False)
        self.toggle_additional_filter()
        self.selected_index_buttons  = []
        self.selected_column_buttons = []
        for w in self.index_buttons_frame.winfo_children():
            w.destroy()
        for w in self.column_buttons_frame.winfo_children():
            w.destroy()
        self.index_listbox.selection_clear(0, "end")
        self.column_listbox.selection_clear(0, "end")
        self.ui_state = "initial"
        self.busy     = False
        self.refresh_ui_state("initial")
        self.adjust_window_height()
    # -----------------------------------------------------------------------
    # Pivot 필드 선택 / 버튼 표시
    # -----------------------------------------------------------------------
    def toggle_index_field(self, event):
        self.toggle_field(event, self.index_listbox,
                          self.selected_index_buttons, self.index_buttons_frame)
    def toggle_column_field(self, event):
        self.toggle_field(event, self.column_listbox,
                          self.selected_column_buttons, self.column_buttons_frame)
    def toggle_field(self, event, listbox, selected_list, frame):
        selection = listbox.curselection()
        if not selection:
            return
        val_display  = listbox.get(selection[0])
        val_original = self._original_header(val_display)
        if val_original in selected_list:
            selected_list.remove(val_original)
        else:
            selected_list.append(val_original)
        self.update_selection_display(listbox, selected_list, frame)
        self.adjust_window_height()
    def remove_button_by_click(self, button, selected_list, frame, listbox):
        val = getattr(button, "_original_value", button.cget("text"))
        if val in selected_list:
            selected_list.remove(val)
            self.update_selection_display(listbox, selected_list, frame)
            self.adjust_window_height()
    def handle_reorder_click(self, value, selected_list, listbox, frame):
        try:
            if self._reorder_selected_index is None:
                self._reorder_selected_index = selected_list.index(value)
                self._highlight_selected_button(value, frame)
            else:
                if self._reorder_selected_index >= len(selected_list):
                    self._reorder_selected_index = None
                    return
                target_index = selected_list.index(value)
                moved = selected_list.pop(self._reorder_selected_index)
                selected_list.insert(target_index, moved)
                self._reorder_selected_index = None
                self.update_selection_display(listbox, selected_list, frame)
        except ValueError:
            self._reorder_selected_index = None
    def _highlight_selected_button(self, value, frame):
        for row_frame in frame.winfo_children():
            for widget in row_frame.winfo_children():
                orig = getattr(widget, "_original_value", "")
                widget.configure(fg_color="#aed6f1" if orig == value else "#d5f5e3")
    def update_selection_display(self, listbox, selected_list, frame):
        for w in frame.winfo_children():
            w.destroy()
        max_per_row = 6
        row_frame   = None
        for idx, val in enumerate(selected_list):
            if idx % max_per_row == 0:
                row_frame = ctk.CTkFrame(frame, fg_color="lightgray")
                row_frame.pack(anchor="w")
            disp = self._display_header(val)
            btn  = ctk.CTkButton(
                row_frame, text=f"  {idx + 1}. {disp}",
                width=200, height=26, font=("맑은 고딕", 11),
                fg_color="#d5f5e3", text_color="black",
                hover_color="#b2f0c5", corner_radius=3)
            btn._original_value = val
            btn.bind("<Button-1>",
                     lambda e, v=val: self.handle_reorder_click(v, selected_list, listbox, frame))
            btn.bind("<Double-Button-1>",
                     lambda e, b=btn: self.remove_button_by_click(b, selected_list, frame, listbox))
            btn.pack(side="left", padx=5, pady=3)
        for i in range(listbox.size()):
            item_disp = listbox.get(i)
            item_orig = self._original_header(item_disp)
            listbox.itemconfig(i, {"fg": "gray" if item_orig in selected_list else "black"})
        self.adjust_window_height()
    # -----------------------------------------------------------------------
    # 파일 선택
    # -----------------------------------------------------------------------
    def select_raw_file(self):
        if self.busy:
            return
        path = filedialog.askopenfilename(filetypes=[("Text Files", "*.txt *.csv")])
        if not path:
            return
        # ② busy 경쟁조건 수정: df_path 설정 → reset_ui() → begin_busy() 순서로 변경
        #    reset_ui() 내 busy=False 덮어쓰기 이후 begin_busy()에서 True로 확정
        self.df_path = path
        self.reset_ui()
        self.df_path = path          # reset_ui가 None으로 초기화하므로 재설정
        self.begin_busy(parquet_message="📜 원시파일 선택 중...")
        try:
            with open(self.df_path, "rb") as f:
                raw = f.read(10_000)
            detected = chardet.detect(raw)
            enc = detected.get("encoding") or "utf-8"
            if enc.lower() in ("ascii", "iso-8859-1", "windows-1252"):
                enc = "utf-8"
            elif enc.lower() == "euc-kr":
                enc = "cp949"
            gui_enc = REVERSE_ENCODING_MAP.get(enc.lower(), "UTF-8")
            self.encoding_var.set(gui_enc)
            self.encoding = ENCODING_MAP.get(gui_enc, "utf-8")
            self.encoding_label.configure(text=f"식별된인코딩: {gui_enc}")
            try:
                from itertools import islice
                with open(self.df_path, "r", encoding=self.encoding, errors="strict") as f:
                    lines = list(islice(f, 5))
            except UnicodeDecodeError:
                self.encoding = "utf-8"
                self.encoding_var.set("UTF-8")
                from itertools import islice
                with open(self.df_path, "r", encoding="utf-8", errors="replace") as f:
                    lines = list(islice(f, 5))
            nonempty_lines = [l for l in lines if l.strip()]
            detected_delim = self._detect_delimiter(nonempty_lines)
            if detected_delim:
                self.delimiter.set(detected_delim)
                try:
                    self.delimiter_menu.set(detected_delim)
                except Exception:
                    pass
            self.header_preview.configure(state="normal", height=5)
            self.header_preview.delete(0, tk.END)
            for idx, line in enumerate(lines[:5]):
                self.header_preview.insert(tk.END, f"{idx}: {line.strip()}")
            parquet_path = self.df_path + ".parquet"
            if os.path.isdir(parquet_path):
                try:
                    dd.read_parquet(parquet_path).head(1)
                    self.parquet_exists = True
                    self.busy = False
                    self.load_file_from_parquet()
                    return
                except Exception:
                    self.parquet_exists = False
                    shutil.rmtree(parquet_path, ignore_errors=True)
            self.load_analysis_state()
            self.update_parquet_status(
                "✅ 원시파일 선택 완료: 헤더 행 확인 후 Parquet 생성을 진행하세요.")
            self.end_busy("raw_selected")
        except Exception as e:
            self.update_parquet_status("❌ 원시파일 선택 오류")
            self.end_busy("initial")
            messagebox.showerror("원시파일 선택 오류", str(e))
    def select_parquet_folder(self):
        if self.busy:
            return
        folder_path = filedialog.askdirectory(title="Parquet 폴더 선택")
        if not folder_path:
            return
        self.begin_busy(parquet_message="📂 Parquet 폴더 선택 중...")
        try:
            parquet_files = glob.glob(os.path.join(folder_path, "*.parquet"))
            if not parquet_files:
                messagebox.showwarning("파일 없음", "선택한 폴더에 Parquet 파일이 없습니다.")
                self.update_parquet_status("❌ Parquet 파일 없음")
                self.end_busy()
                return
            parent_dir   = os.path.dirname(folder_path)
            pq_folder    = os.path.basename(folder_path)
            base_txt     = pq_folder.replace(".parquet", "")
            self.df_path = os.path.join(parent_dir, base_txt)
            self.parquet_exists = True
            self.update_parquet_status(f"📂 Parquet 인식 완료: {pq_folder}")
            self.load_file_from_parquet()
        except Exception as e:
            self.update_parquet_status("❌ Parquet 로딩 오류")
            self.end_busy()
            messagebox.showerror("오류", f"Parquet 파일을 불러오는 중 오류 발생:\n{e}")
    def select_header_row(self, event=None):
        selected = self.header_preview.curselection()
        if not selected or not self.df_path:
            return
        self.header_row.set(selected[0])
        with open(self.df_path, "r", encoding=self.encoding, errors="replace") as f:
            for _ in range(self.header_row.get()):
                f.readline()
            header_line = f.readline().strip()
        delimiter      = self.delimiter.get()
        raw_headers    = [h.strip() for h in self._parse_csv_line(header_line, delimiter)]
        unique_headers = self._make_unique_headers(raw_headers)
        self.original_headers   = unique_headers[:]
        self.header_display_map = {h: h for h in self.original_headers}
        self.headers            = unique_headers[:]
        self.populate_fields()
        self.update_parquet_status(
            f"✅ 헤더 행 선택됨: {self.header_row.get()}행 — Parquet 생성을 진행하세요.")
        self.refresh_ui_state("raw_selected")
    # -----------------------------------------------------------------------
    # 헤더 표시 관리
    # -----------------------------------------------------------------------
    def _display_header(self, original: str) -> str:
        return self.header_display_map.get(original, original)
    def _original_header(self, display: str) -> str:
        return self.display_to_original_map.get(display, display)
    def _rebuild_header_display_maps(self):
        if not self.original_headers:
            self.header_display_map      = {}
            self.display_to_original_map = {}
            self.headers = []
            return
        raw_display = [self.header_display_map.get(orig, orig) for orig in self.original_headers]
        unique_disp = self._make_unique_headers(raw_display)
        self.header_display_map      = dict(zip(self.original_headers, unique_disp))
        self.display_to_original_map = {disp: orig
                                        for orig, disp in self.header_display_map.items()}
        self.headers = [self.header_display_map[orig] for orig in self.original_headers]
    def _rename_df_columns_to_display(self, df: pd.DataFrame) -> pd.DataFrame:
        rename_map = {orig: self._display_header(orig)
                      for orig in df.columns if orig in self.header_display_map}
        return df.rename(columns=rename_map)
    def _rebuild_all_header_widgets(self):
        """listbox / optionmenu 등 헤더 관련 위젯 전체 갱신."""
        headers = self.headers
        for lb in [self.index_listbox, self.column_listbox]:
            lb.configure(state="normal")
            lb.delete(0, "end")
            for h in headers:
                lb.insert("end", h)
        for menu in [self.filter_col_select, self.value_menu, self.additional_col_select]:
            menu.configure(values=headers)
        self.update_selection_display(
            self.index_listbox, self.selected_index_buttons, self.index_buttons_frame)
        self.update_selection_display(
            self.column_listbox, self.selected_column_buttons, self.column_buttons_frame)
        self._refresh_filter_header_options()
    def refresh_header_display_ui(self):
        self._rebuild_header_display_maps()
        if self.headers:
            try:
                header_text = f"헤더: {' | '.join(self.headers)}"
                self.header_preview.configure(state="normal", height=1)
                self.header_preview.delete(0, tk.END)
                self.header_preview.insert(tk.END, header_text)
                self.header_preview.configure(state="disabled")
            except Exception:
                pass
        self._rebuild_all_header_widgets()
        idx = self.current_filter_index.get() - 1
        if 0 <= idx < self.max_filters and self.filter_columns[idx]:
            self.filter_col_select.set(self._display_header(self.filter_columns[idx]))
        elif self.headers:
            self.filter_col_select.set(self.headers[0])
        cur_add_orig = self._original_header(self.additional_col_select.get().strip())
        if cur_add_orig in self.original_headers:
            self.additional_col_select.set(self._display_header(cur_add_orig))
        elif self.headers:
            self.additional_col_select.set(self.headers[0])
        cur_val_orig = self._original_header(self.value_var.get().strip())
        if cur_val_orig in self.original_headers:
            self.value_var.set(self._display_header(cur_val_orig))
        elif self.headers:
            self.value_var.set(self.headers[0])
        self.refresh_ui_state()
        self.adjust_window_height()
    def show_header_display_editor(self):
        if not self.parquet_exists or not self.original_headers:
            messagebox.showwarning("경고", "먼저 Parquet 파일을 준비하세요.")
            return
        self._rebuild_header_display_maps()
        dialog = ctk.CTkToplevel(self)
        dialog.title("헤더 표시 수정")
        dialog.geometry("900x620")
        dialog.grab_set()
        outer = ctk.CTkFrame(dialog, fg_color="transparent")
        outer.pack(fill="both", expand=True, padx=20, pady=20)
        ctk.CTkLabel(outer, text="헤더 표시 수정",
                     font=("맑은 고딕", 16, "bold"), anchor="w").pack(fill="x", pady=(0, 8))
        ctk.CTkLabel(
            outer,
            text="Parquet 원본 헤더는 변경되지 않습니다.\n"
                 "여기서 수정한 값은 화면 표시와 Filter/Pivot 결과 파일 저장 시에만 적용됩니다.",
            justify="left", anchor="w", font=("맑은 고딕", 11),
        ).pack(fill="x", pady=(0, 12))
        grid_frame = ctk.CTkScrollableFrame(outer, width=820, height=430)
        grid_frame.pack(fill="both", expand=True, pady=(0, 15))
        ctk.CTkLabel(grid_frame, text="원본 헤더", font=("맑은 고딕", 11, "bold"),
                     anchor="w", width=320).grid(row=0, column=0, padx=10, pady=8, sticky="w")
        ctk.CTkLabel(grid_frame, text="표시 헤더", font=("맑은 고딕", 11, "bold"),
                     anchor="w", width=380).grid(row=0, column=1, padx=10, pady=8, sticky="w")
        entry_map: dict = {}
        for i, orig in enumerate(self.original_headers, start=1):
            disp = self._display_header(orig)
            ctk.CTkLabel(grid_frame, text=orig, anchor="w", width=320
                         ).grid(row=i, column=0, padx=10, pady=6, sticky="w")
            entry = ctk.CTkEntry(grid_frame, width=380)
            entry.insert(0, disp)
            entry.grid(row=i, column=1, padx=10, pady=6, sticky="ew")
            entry_map[orig] = entry
        grid_frame.grid_columnconfigure(1, weight=1)
        btn_frame = ctk.CTkFrame(outer, fg_color="transparent")
        btn_frame.pack(fill="x", pady=(5, 0))
        def on_restore():
            for orig, entry in entry_map.items():
                entry.delete(0, "end")
                entry.insert(0, orig)
        def on_apply():
            self.begin_busy(parquet_message="📝 헤더 표시 수정 적용 중...")
            try:
                disp_list = []
                for orig in self.original_headers:
                    raw  = entry_map[orig].get().strip()
                    name = raw if raw else orig
                    disp_list.append(name)
                unique_disp = self._make_unique_headers(disp_list)
                if unique_disp != disp_list:
                    if not messagebox.askyesno(
                        "중복 표시명",
                        "일부 표시명이 중복되어 자동으로 구분자(_N)가 추가됩니다.\n계속하시겠습니까?",
                    ):
                        self.end_busy("parquet_ready")
                        return
                self.header_display_map = dict(zip(self.original_headers, unique_disp))
                self._rebuild_header_display_maps()
                self.refresh_header_display_ui()
                self.save_analysis_state()
                self.update_parquet_status("✅ 헤더 표시 수정 완료")
                messagebox.showinfo("완료", "헤더 표시 수정이 적용되었습니다.")
                dialog.destroy()
            except Exception as e:
                messagebox.showerror("오류", f"헤더 표시 수정 실패:\n{e}")
                self.update_parquet_status("❌ 헤더 표시 수정 실패")
            finally:
                self.end_busy("parquet_ready")
        ctk.CTkButton(btn_frame, text="복구", width=120, command=on_restore).pack(side="left")
        ctk.CTkButton(btn_frame, text="취소", width=120,
                      fg_color="#d9534f", hover_color="#c9302c",
                      command=dialog.destroy).pack(side="right")
        ctk.CTkButton(btn_frame, text="적용", width=120,
                      command=on_apply).pack(side="right", padx=(0, 10))
    # -----------------------------------------------------------------------
    # Parquet log
    # -----------------------------------------------------------------------
    def show_parquet_log(self):
        import tkinter.ttk as ttv
        if not self.df_path:
            messagebox.showwarning("경고", "먼저 원시파일 또는 Parquet 폴더를 선택하세요.")
            return
        log_path     = self.df_path + "_parquet_log.txt"
        anomaly_path = os.path.splitext(self.df_path)[0] + "_anomaly_lines.txt"
        log_content = anomaly_content = ""
        anomaly_count = 0
        if os.path.exists(log_path):
            try:
                with open(log_path, "r", encoding="utf-8") as f:
                    log_content = f.read()
            except Exception as e:
                log_content = f"[오류] 로그 파일 열기 실패: {e}"
        else:
            log_content = "📂 Parquet 생성 요약 로그 파일이 존재하지 않습니다."
        if os.path.exists(anomaly_path):
            try:
                with open(anomaly_path, "r", encoding="utf-8") as f:
                    lines = f.readlines()
                    anomaly_count   = len(lines)
                    anomaly_content = "".join(lines)
            except Exception as e:
                anomaly_content = f"[오류] parquet 차이 행 파일 열기 실패: {e}"
        else:
            anomaly_content = "📂 parquet 차이 로그 파일이 존재하지 않습니다."
        anomaly_summary = (f"🧾 Parquet 제외행 리스트 "
                           f"(총 {anomaly_count:,}개의 제외행이 식별되었습니다)\n"
                           + "-" * 40 + "\n")
        full_text  = log_content.strip() + "\n\n" + anomaly_summary + anomaly_content.strip()
        line_count = full_text.count("\n") + 1
        calc_h     = min(150 + line_count * 18, 500)
        log_win = tk.Toplevel(self)
        log_win.title("Parquet Log")
        log_win.geometry(f"600x{calc_h}")
        text_frame = tk.Frame(log_win)
        text_frame.pack(fill="both", expand=True, padx=10, pady=10)
        text_frame.columnconfigure(0, weight=1)
        text_frame.rowconfigure(0, weight=1)
        tw = tk.Text(text_frame, wrap="none", font=("맑은 고딕", 10))
        tw.insert("1.0", full_text)
        tw.configure(state="disabled")
        tw.grid(row=0, column=0, sticky="nsew")
        ys = ttv.Scrollbar(text_frame, orient="vertical",   command=tw.yview)
        xs = ttv.Scrollbar(text_frame, orient="horizontal", command=tw.xview)
        tw.configure(yscrollcommand=ys.set, xscrollcommand=xs.set)
        ys.grid(row=0, column=1, sticky="ns")
        xs.grid(row=1, column=0, sticky="ew")
    # -----------------------------------------------------------------------
    # Parquet 생성 확인 다이얼로그
    # -----------------------------------------------------------------------
    def show_parquet_confirm_dialog(self):
        dialog = ctk.CTkToplevel(self)
        dialog.title("Parquet 생성 확인")
        dialog.geometry("450x180")
        dialog.resizable(False, False)
        dialog.grab_set()
        msg_frame = ctk.CTkFrame(dialog, fg_color="transparent")
        msg_frame.pack(fill="both", expand=True, padx=20, pady=20)
        ctk.CTkLabel(
            msg_frame,
            text="Parquet 파일을 생성합니다.\n"
                 "이 작업은 파일 크기에 따라 상당한 시간이 소요될 수 있습니다.\n"
                 "계속 진행하시겠습니까?",
            anchor="center", justify="center", font=("맑은 고딕", 13),
        ).pack(anchor="w")
        checkbox_var = tk.BooleanVar(value=False)
        ctk.CTkCheckBox(
            dialog,
            text="완전성 검토 추가:\n불필요하여 제외한 데이터 집계(처리 시간 증가)",
            variable=checkbox_var,
        ).pack(anchor="w", padx=15, pady=(0, 10))
        btn_frame = ctk.CTkFrame(dialog, fg_color="transparent")
        btn_frame.pack(pady=10)
        def on_confirm():
            flag = checkbox_var.get()
            dialog.destroy()
            self.after(10, lambda: self._start_parquet_generation(flag))
        ctk.CTkButton(btn_frame, text="계속 진행", width=140,
                      command=on_confirm).pack(side="left", padx=10)
        ctk.CTkButton(btn_frame, text="취소", width=140,
                      fg_color="#d9534f", hover_color="#c9302c",
                      command=dialog.destroy).pack(side="left", padx=10)
    def _start_parquet_generation(self, extract_anomaly: bool):
        """메인스레드에서 UI 값 캐싱 후 Parquet 생성 실행."""
        try:
            self._parquet_delimiter       = self._normalize_delimiter(self.delimiter.get())
            self._parquet_header_row      = int(self.header_row.get())
            self._parquet_encoding        = self.encoding
            self._parquet_blocksize       = self.parse_size(self.blocksize_var.get())
            self._parquet_blocksize_label = self.blocksize_var.get()
        except Exception as e:
            messagebox.showerror("UI 읽기 오류", f"파라미터 읽기 실패: {type(e).__name__}: {e}")
            return
        self.generate_parquet(extract_anomaly=extract_anomaly)
    def parse_size(self, size_str: str) -> int:
        try:
            s = size_str.strip().lower()
            if s.endswith("mb"):
                return int(float(s.replace("mb", "")) * 1024 * 1024)
            if s.endswith("gb"):
                return int(float(s.replace("gb", "")) * 1024 * 1024 * 1024)
            return int(s)
        except Exception:
            return 16_777_216
    def generate_parquet(self, extract_anomaly: bool = False):
        """
        Parquet 생성 단일 통합 함수.
        [v3.312] Step 3: enumerate(fin) → csv.reader 논리 레코드 순회로 교체
                 구분자/따옴표 감싼 줄바꿈 포함 멀티라인 레코드를 하나의 행으로 처리.
                 탭 구분자는 QUOTE_NONE → 멀티라인 불가 → anomaly 보완 병합으로 수동 보완.
        [v3.313] ⑥ 로그에 "(멀티라인 포함 시 물리 줄 수와 다를 수 있음)" 안내 추가.
        """
        if self.busy:
            return
        start_msg = ("📄 예외 분석 및 Parquet 생성 중..."
                     if extract_anomaly else "📄 Parquet 생성 중...")
        self.begin_busy(
            parquet_message=start_msg,
            analysis_message=start_msg,
            analysis_progress=0.1,
        )
        start_time = time.time()
        def task():
            import tempfile
            from collections import defaultdict
            temp_path    = None
            anomaly_file = None
            try:
                encoding        = self._parquet_encoding
                delimiter       = self._parquet_delimiter
                header_row_idx  = self._parquet_header_row
                blocksize_bytes = self._parquet_blocksize
                blocksize_label = self._parquet_blocksize_label
                if not self.df_path or not os.path.exists(self.df_path):
                    raise FileNotFoundError("원본 파일 경로가 유효하지 않습니다.")
                # ── 1. 헤더 읽기 ────────────────────────────────────────
                with open(self.df_path, "r", encoding=encoding,
                          errors="replace", newline="") as f:
                    for _ in range(header_row_idx):
                        f.readline()
                    header_line = f.readline()
                if not header_line:
                    raise ValueError("선택한 헤더 행을 읽을 수 없습니다.")
                raw_header = [h.strip() for h in self._parse_csv_line(header_line, delimiter)]
                if not raw_header or not any(raw_header):
                    raise ValueError("헤더가 비어 있습니다. 헤더 행 선택을 확인하세요.")
                unique_header = self._make_unique_headers(raw_header)
                n_cols        = len(raw_header)
                header_values = [str(h).strip() for h in raw_header]
                # ── 2. 임시 CSV 및 anomaly 경로 준비 ────────────────────
                temp_dir = os.path.dirname(self.df_path)
                temp_fd, temp_path = tempfile.mkstemp(suffix=".csv", dir=temp_dir)
                os.close(temp_fd)
                anomaly_path = os.path.splitext(self.df_path)[0] + "_anomaly_lines.txt"
                if not extract_anomaly and os.path.exists(anomaly_path):
                    try:
                        os.remove(anomaly_path)
                    except Exception:
                        pass
                excluded_counts  = defaultdict(int)
                valid_row_count  = 0
                total_line_count = 0   # 논리 레코드 수 (멀티라인 포함 시 물리 줄 수와 다를 수 있음)
                buffer           = []
                buf_size         = 10_000
                if extract_anomaly:
                    anomaly_file = open(anomaly_path, "w", encoding="utf-8", newline="")
                # ── 3. 원본 파일 논리 레코드 단위 검증 후 임시 CSV 작성 ──
                # 진행도: 파일 크기(bytes) 기반, 10,000 레코드마다 UI 갱신 (메모리 추가 없음)
                try:
                    _file_size = os.path.getsize(self.df_path)
                except Exception:
                    _file_size = 0
                _PROGRESS_INTERVAL = 10_000   # 갱신 주기 (레코드 수)
                _next_update       = _PROGRESS_INTERVAL
                self.update_analysis_status("📄 원본 데이터 검증 중...", 0.05)
                with open(self.df_path, "r", encoding=encoding,
                          errors="replace", newline="") as fin, \
                     open(temp_path, "w", encoding="utf-8", newline="") as vout:
                    writer     = csv.writer(vout, **self._csv_writer_kwargs(delimiter))
                    reader     = csv.reader(fin, **self._csv_reader_kwargs(delimiter))
                    record_idx = -1
                    for parsed_cols in reader:
                        total_line_count += 1
                        record_idx       += 1
                        reason            = None
                        # 10,000 레코드마다 파일 위치 기반 진행도 갱신 (0.05~0.50 구간)
                        if total_line_count >= _next_update:
                            _next_update += _PROGRESS_INTERVAL
                            try:
                                _pos   = fin.buffer.tell() if hasattr(fin, "buffer") else 0
                                _ratio = (_pos / _file_size) if _file_size > 0 else 0
                                _p     = 0.05 + 0.45 * min(_ratio, 1.0)
                            except Exception:
                                _p = 0.25
                            self.update_analysis_status(
                                f"📄 검증 중... {total_line_count:,}행 처리",
                                progress=_p, save=False)
                        if record_idx < header_row_idx:
                            reason = "[헤더 이전 행]"
                        elif record_idx == header_row_idx:
                            reason = "[헤더 행]"
                        else:
                            parsed_cols = [str(c).strip() for c in parsed_cols]
                            if not any(parsed_cols):
                                reason = "[빈 행]"
                            elif len(parsed_cols) != n_cols:
                                reason = "[열 개수 불일치]"
                            elif parsed_cols == header_values:
                                reason = "[헤더 중복 행]"
                            else:
                                writer.writerow(parsed_cols)
                                valid_row_count += 1
                        if reason:
                            excluded_counts[reason] += 1
                            if extract_anomaly and anomaly_file is not None:
                                raw_repr = delimiter.join(
                                    parsed_cols if isinstance(parsed_cols, list) else [])
                                if reason == "[열 개수 불일치]":
                                    n_actual = (len(parsed_cols)
                                                if isinstance(parsed_cols, list) else "?")
                                    detail = (f"{reason} "
                                              f"(기대열={n_cols}, 실제열={n_actual}) "
                                              f"{raw_repr}\n")
                                else:
                                    detail = f"{reason} {raw_repr}\n"
                                buffer.append(detail)
                                if len(buffer) >= buf_size:
                                    anomaly_file.writelines(buffer)
                                    buffer.clear()
                    if extract_anomaly and anomaly_file is not None and buffer:
                        anomaly_file.writelines(buffer)
                        buffer.clear()
                if anomaly_file is not None:
                    anomaly_file.close()
                    anomaly_file = None
                if valid_row_count <= 0 or not temp_path or os.path.getsize(temp_path) == 0:
                    raise ValueError(
                        "유효한 데이터가 존재하지 않아 Parquet 생성이 불가능합니다.")
                # ── 4. 검증된 임시 CSV → Dask Parquet 생성 ──────────────
                self.update_parquet_status("📦 Parquet 생성 중...")
                self.update_analysis_status("📦 Parquet 생성 중...", 0.55)
                parquet_path = self.df_path + ".parquet"
                if os.path.exists(parquet_path):
                    shutil.rmtree(parquet_path, ignore_errors=True)
                os.makedirs(parquet_path, exist_ok=True)
                ddf = dd.read_csv(
                    temp_path,
                    sep=delimiter,
                    names=unique_header,
                    header=None,
                    blocksize=blocksize_bytes,
                    dtype=str,
                    encoding="utf-8",
                    encoding_errors="replace",
                    keep_default_na=False,
                    na_filter=False,
                    **self._dask_read_csv_kwargs(delimiter),
                )
                ddf.to_parquet(parquet_path, compression="snappy", write_index=False)
                partition_count = ddf.npartitions
                row_count = (self._count_parquet_rows_from_metadata(parquet_path)
                             or valid_row_count)
                self.last_parquet_npartitions = partition_count
                self.parquet_exists = True
                # ⑭ 최초 생성 시에는 write("w") 모드로 요약 작성
                self.write_parquet_summary_log(row_count, parquet_path, blocksize_label)
                # ── 5. Parquet log에 제외행 요약 추가 ───────────────────
                try:
                    log_path = self.df_path + "_parquet_log.txt"
                    with open(log_path, "a", encoding="utf-8") as log:
                        log.write("\n📌 Parquet 생성 검증 요약\n")
                        # ⑥ 멀티라인 레코드 포함 시 물리 줄 수와 다를 수 있음을 명시
                        log.write(
                            f"📄 원본 총 논리 레코드 수: {total_line_count:,}"
                            f"  ※ 멀티라인 레코드 포함 시 실제 물리 줄 수와 다를 수 있음\n"
                        )
                        log.write(f"✅ 유효 데이터 행 수: {valid_row_count:,}\n")
                        log.write(f"🚫 제외 레코드 수: {sum(excluded_counts.values()):,}\n")
                        for k, v in excluded_counts.items():
                            log.write(f"   - {k}: {v:,}\n")
                        log.write(
                            f"🧾 상세 제외행 로그 생성 여부: {'Y' if extract_anomaly else 'N'}\n")
                        if excluded_counts.get("[열 개수 불일치]", 0) > 0:
                            log.write(
                                "   ※ [열 개수 불일치] 행은 [anomaly 보완 병합] 기능으로\n"
                                "     Excel 수정 후 Parquet에 추가 가능합니다.\n"
                            )
                except Exception as log_e:
                    print(f"[Parquet 검증 요약 로그 추가 실패] {log_e}")
                elapsed = time.time() - start_time
                def on_done():
                    self.update_analysis_status(
                        f"✅ Parquet 생성 완료 / ⏱ {elapsed:.2f}초", 1.0)
                    self.load_file_from_parquet(
                        row_count_override=row_count,
                        partition_count_override=partition_count,
                    )
                    mismatch_count = excluded_counts.get("[열 개수 불일치]", 0)
                    extra_msg = ""
                    if mismatch_count > 0:
                        extra_msg = (
                            f"\n\n⚠️ [열 개수 불일치] {mismatch_count:,}건 발견\n"
                            "[anomaly 보완 병합] 버튼으로 Excel 수정 후 Parquet에 추가할 수 있습니다."
                        )
                    messagebox.showinfo(
                        "완료",
                        f"Parquet 파일이 성공적으로 생성되었습니다.\n\n"
                        f"⏱ 생성 소요 시간: {elapsed:.2f}초\n"
                        f"🧩 파티션 수: {partition_count:,}개\n"
                        f"📊 유효 데이터 행 수: {valid_row_count:,}건\n"
                        f"🚫 제외 레코드 수: {sum(excluded_counts.values()):,}건"
                        + extra_msg,
                    )
                self.ui_call(on_done)
            except Exception as e:
                err_type, err_msg = type(e).__name__, str(e)
                def on_error():
                    self.update_analysis_status("❌ Parquet 생성 실패", 0.0)
                    self.update_parquet_status("❌ Parquet 생성 실패")
                    self.end_busy("raw_selected")
                    messagebox.showerror("Parquet 생성 오류", f"{err_type}: {err_msg}")
                self.ui_call(on_error)
            finally:
                try:
                    if anomaly_file is not None:
                        anomaly_file.close()
                except Exception:
                    pass
                try:
                    if temp_path and os.path.exists(temp_path):
                        os.remove(temp_path)
                except Exception:
                    pass
        threading.Thread(target=task, daemon=True).start()
    # -----------------------------------------------------------------------
    # Parquet 메타데이터 행 수 계산
    # -----------------------------------------------------------------------
    def _count_parquet_rows_from_metadata(self, parquet_path: str):
        try:
            import pyarrow.parquet as pq
            files = glob.glob(os.path.join(parquet_path, "**", "*.parquet"), recursive=True)
            total = 0
            for f in files:
                try:
                    pf = pq.ParquetFile(f)
                    if pf.metadata is not None:
                        total += pf.metadata.num_rows
                except Exception:
                    pass
            return total if total > 0 else None
        except Exception as e:
            print(f"[Parquet metadata 행 수 계산 실패] {type(e).__name__}: {e}")
            return None
    # -----------------------------------------------------------------------
    # Parquet 로그 함수 (⑭ 분리)
    # -----------------------------------------------------------------------
    def write_parquet_summary_log(self, row_count, parquet_path: str, blocksize_str: str):
        """
        Parquet 최초 생성 시 요약 로그를 새로 작성("w" 모드).
        기존 로그를 덮어쓰는 것이 맞는 상황에만 사용.
        """
        try:
            files = glob.glob(
                os.path.join(parquet_path, "**", "*.parquet"), recursive=True)
            partition_count = len(files)
            size_mb  = sum(os.path.getsize(f) for f in files) / (1024 * 1024)
            raw_size_mb = (os.path.getsize(self.df_path) / (1024 * 1024)
                           if self.df_path and os.path.exists(self.df_path) else 0)
            row_count_text = f"{row_count:,}" if isinstance(row_count, int) else "N/A"
            log_path = self.df_path + "_parquet_log.txt"
            with open(log_path, "w", encoding="utf-8") as log:
                log.write("📄 Parquet 생성 요약\n")
                log.write(f"📁 원본 파일: {os.path.basename(self.df_path)}\n")
                log.write(f"📦 원본 파일 크기: {raw_size_mb:.2f} MB\n")
                log.write(f"🧱 Parquet BlockSize: {blocksize_str}\n")
                log.write(f"🧩 Parquet 파티션 수: {partition_count:,}\n")
                log.write(f"📊 Parquet 행 수: {row_count_text}\n")
                log.write(f"📐 Parquet 용량: {size_mb:.2f} MB\n")
                log.write(f"🕒 생성 시각: {datetime.datetime.now()}\n")
        except Exception as e:
            print(f"[Parquet 로그 저장 실패] {e}")
    def _append_parquet_summary_log(self, row_count, parquet_path: str, blocksize_str: str):
        """
        ⑭ 빈행 삭제 / anomaly 병합 후 현재 Parquet 상태를 로그에 추가("a" 모드).
        기존 생성 검증 요약을 덮어쓰지 않음.
        """
        try:
            files = glob.glob(
                os.path.join(parquet_path, "**", "*.parquet"), recursive=True)
            partition_count = len(files)
            size_mb  = sum(os.path.getsize(f) for f in files) / (1024 * 1024)
            row_count_text = f"{row_count:,}" if isinstance(row_count, int) else "N/A"
            log_path = self.df_path + "_parquet_log.txt"
            with open(log_path, "a", encoding="utf-8") as log:
                log.write("\n📄 Parquet 상태 갱신\n")
                log.write(f"🧩 Parquet 파티션 수: {partition_count:,}\n")
                log.write(f"📊 Parquet 행 수: {row_count_text}\n")
                log.write(f"📐 Parquet 용량: {size_mb:.2f} MB\n")
                log.write(f"🕒 갱신 시각: {datetime.datetime.now()}\n")
        except Exception as e:
            print(f"[Parquet 로그 추가 실패] {e}")
    # -----------------------------------------------------------------------
    # Parquet 로드
    # -----------------------------------------------------------------------
    def load_file_from_parquet(self, row_count_override=None, partition_count_override=None):
        try:
            parquet_path = f"{self.df_path}.parquet"
            ddf = dd.read_parquet(parquet_path)
            self.original_headers = ddf.columns.tolist()
            if not self.header_display_map:
                self.header_display_map = {h: h for h in self.original_headers}
            self._rebuild_header_display_maps()
            self.populate_fields(reset_filter=False)
            header_text = f"헤더: {' | '.join(self.headers)}"
            self.header_preview.configure(state="normal", height=1)
            self.header_preview.delete(0, tk.END)
            self.header_preview.insert(tk.END, header_text)
            self.header_preview.configure(state="disabled")
            self.header_row.set(-1)
            files = glob.glob(
                os.path.join(parquet_path, "**", "*.parquet"), recursive=True)
            partition_count = (partition_count_override if partition_count_override is not None
                               else len(files))
            size_mb   = sum(os.path.getsize(f) for f in files) / (1024 * 1024)
            row_count = (row_count_override if row_count_override is not None
                         else self._count_parquet_rows_from_metadata(parquet_path))
            row_text  = f"{row_count:,}" if isinstance(row_count, int) else "N/A"
            self.parquet_exists = True
            self.load_analysis_state()
            self.analysis_tab.set("Filter")
            self.switch_mode("Filter")
            self.mode_frame.pack(fill="x", pady=(0, 10), padx=10)
            self.dynamic_frame.pack(fill="both", expand=True, padx=10, pady=5)
            self.action_frame.pack(fill="x", pady=(0, 10), padx=10)
            self.update_parquet_status(
                f"✅ Parquet 파일 준비 완료 "
                f"(행: {row_text}, 파티션: {partition_count}, 크기: {size_mb:.2f}MB)")
            self.end_busy("parquet_ready")
            self.update_result_buttons()
            self.adjust_window_height()
        except Exception as e:
            self.update_parquet_status("❌ Parquet 파일 로딩 실패")
            self.end_busy()
            messagebox.showerror(
                "오류", f"Parquet 파일을 불러오는 중 오류 발생:\n{type(e).__name__}: {e}")
    # -----------------------------------------------------------------------
    # Parquet 삭제
    # -----------------------------------------------------------------------
    def delete_parquet(self):
        if not messagebox.askokcancel("Parquet 삭제 확인",
                                      "Parquet 파일이 삭제됩니다.\n\n계속 진행할까요?"):
            return
        import stat as stat_mod
        parquet_path = f"{self.df_path}.parquet"
        log_path     = self.df_path + "_parquet_log.txt"
        anomaly_path = os.path.splitext(self.df_path)[0] + "_anomaly_lines.txt"
        state_path   = self.df_path + ".state.json"
        try:
            self.begin_busy(parquet_message="❌ Parquet 삭제 중...")
            if os.path.exists(parquet_path):
                try:
                    shutil.rmtree(parquet_path, onerror=self._handle_remove_readonly)
                except Exception as e:
                    messagebox.showwarning("Parquet 삭제 실패",
                                           f"Parquet 폴더 삭제 중 오류:\n{e}")
                    return
            for p in [log_path, anomaly_path]:
                if os.path.exists(p):
                    try:
                        os.remove(p)
                    except Exception as e:
                        print(f"[파일 삭제 실패] {e}")
            if os.path.exists(state_path):
                try:
                    os.chmod(state_path, stat_mod.S_IWRITE)
                    os.remove(state_path)
                except Exception as e:
                    print(f"[상태파일 삭제 실패] {e}")
            messagebox.showinfo("삭제 완료", f"Parquet 파일이 삭제되었습니다:\n{parquet_path}")
            self.reset_ui()
        except PermissionError as e:
            messagebox.showerror("삭제 실패", f"권한 오류:\n{e}")
        except Exception as e:
            messagebox.showerror("삭제 실패", f"오류:\n{e}")
        finally:
            if self.df_path:
                self.end_busy("raw_selected")
            else:
                self.end_busy("initial")
    def _handle_remove_readonly(self, func, path, exc):
        import stat as stat_mod
        try:
            os.chmod(path, stat_mod.S_IWRITE)
            func(path)
        except Exception as e:
            print(f"[삭제 실패: {path}] {e}")
    # -----------------------------------------------------------------------
    # populate_fields
    # -----------------------------------------------------------------------
    def populate_fields(self, reset_filter=True):
        if not self.original_headers:
            if len(self.headers) == 1 and isinstance(self.headers[0], str):
                h0 = self.headers[0]
                for sep in ["|", ",", "\t", ";"]:
                    if sep in h0:
                        self.headers = [col.strip() for col in h0.split(sep)]
                        break
            self.original_headers = list(self.headers)
        if not self.header_display_map:
            self.header_display_map = {h: h for h in self.original_headers}
        self._rebuild_header_display_maps()
        self._rebuild_all_header_widgets()
        self.value_var.set(self.headers[0] if self.headers else "")
        self.additional_col_select.set(self.headers[0] if self.headers else "")
        self.toggle_additional_filter()
        self.adjust_window_height()
        if reset_filter:
            self.filter_columns       = [""] * self.max_filters
            self.filter_keyword_texts = [""] * self.max_filters
            self.active_filter_count_var.set(1)
            self.current_filter_index.set(1)
            try:
                self.filter_count_menu.set("1")
                self.filter_toggle.set("필터1")
            except Exception:
                pass
            self.keyword_input.delete("1.0", "end")
            self.keyword_count_label.configure(text="입력된 키워드: 0개")
        self._refresh_filter_header_options()
    # -----------------------------------------------------------------------
    # 결과 버튼
    # -----------------------------------------------------------------------
    def update_result_buttons(self):
        if getattr(self, "busy", False) or self.ui_state != "parquet_ready":
            self.result_file_label.configure(text="")
            self._configure_state(self.open_result_button, "disabled")
            self._configure_state(self.delete_result_button, "disabled")
            return
        mode   = self.selected_analysis
        exists = False
        label  = ""
        if mode == "Filter":
            parts = getattr(self, "filter_result_parts", [])
            rf    = getattr(self, "filter_result_file", "")
            if parts and isinstance(parts, list):
                existing = [f for f in parts if f and os.path.exists(f)]
                if existing:
                    exists = True
                    label  = f"{os.path.basename(existing[0])} ~ part{len(parts)}.csv"
            elif rf and os.path.exists(rf):
                exists = True
                label  = os.path.basename(rf)
        elif mode == "Pivot":
            rf = getattr(self, "pivot_result_file", "")
            if rf and os.path.exists(rf):
                exists = True
                label  = os.path.basename(rf)
        if exists and label:
            short = label if len(label) <= 80 else self._shorten_filename(label)
            self.result_file_label.configure(text=f"📄 {short}")
            self._configure_state(self.open_result_button, "normal")
            self._configure_state(self.delete_result_button, "normal")
        else:
            self.result_file_label.configure(text="")
            self._configure_state(self.open_result_button, "disabled")
            self._configure_state(self.delete_result_button, "disabled")
    # -----------------------------------------------------------------------
    # 분석 실행
    # -----------------------------------------------------------------------
    def run_analysis(self):
        if not self.parquet_exists:
            messagebox.showwarning(
                "경고",
                "먼저 파일을 선택하고 Parquet 파일을 생성해야 합니다."
            )
            return
    
        # 현재 실행하는 분석 모드만 결과 경로 초기화
        # 다른 모드의 결과 파일 경로는 유지해야 함
        if self.selected_analysis == "Filter":
            self.filter_result_file = ""
            self.filter_result_parts = []
            self.filter_status_message = ""
        elif self.selected_analysis == "Pivot":
            self.pivot_result_file = ""
            self.pivot_status_message = ""
    
        self.result_file_label.configure(text="")
        self.update_result_buttons()
    
        self.begin_busy(analysis_message="📥 분석 시작", analysis_progress=0.1)
        self._sync_current_filter_from_ui()
    
        use_additional    = self.additional_filter_var.get()
        additional_column = self._original_header(self.additional_col_select.get())
        active_count      = self.active_filter_count_var.get()
    
        filter_specs = []
        for i in range(active_count):
            col  = self.filter_columns[i]
            text = (self.filter_keyword_texts[i] or "").strip()
            if col and text:
                filter_specs.append((col, text))
    
        try:
            if self.selected_analysis == "Filter":
                threading.Thread(
                    target=lambda: self.run_filtering(
                        filter_specs, use_additional, additional_column
                    ),
                    daemon=True,
                ).start()
            else:
                self.run_pivot()
    
        except Exception as e:
            self.end_busy("parquet_ready")
            messagebox.showerror("분석 실행 오류", str(e))
    # -----------------------------------------------------------------------
    # 필터링
    # -----------------------------------------------------------------------
    def run_filtering(self, filter_specs, use_additional, additional_col):
        try:
            start_time = time.time()
            self.update_analysis_status("🔍 Filtering 중...", 0.2)
            if not filter_specs:
                def handle_empty():
                    self.update_analysis_status("❗ 필터 설정 없음", 0.0)
                    self.end_busy("parquet_ready")
                    messagebox.showwarning("경고", "최소 1개의 필터(헤더+키워드)를 설정하세요.")
                self.ui_call(handle_empty)
                return
            parquet_path      = self.df_path + ".parquet"
            ddf               = dd.read_parquet(parquet_path)
            total_source_rows = self._count_parquet_rows_from_metadata(parquet_path) or "N/A"
            parsed_filters = []
            masks          = []
            for col, keyword_text in filter_specs:
                text = (keyword_text or "").strip()
                kws  = list(filter(None, map(str.strip, re.split(r"[\n\r\t, ]+", text))))
                if not kws:
                    continue
                parsed_filters.append((col, kws))
                pattern = "(?i)" + "|".join(map(re.escape, kws))
                masks.append(ddf[col].str.contains(pattern, na=False, regex=True))
            if not masks:
                def handle_no_kw():
                    self.update_analysis_status("❗ 키워드 미입력", 0.0)
                    self.end_busy("parquet_ready")
                    messagebox.showwarning("경고", "모든 필터에 키워드가 비어 있습니다.")
                self.ui_call(handle_no_kw)
                return
            from functools import reduce
            import operator
            combined_mask = reduce(operator.and_, masks)
            if use_additional:
                filtered_ddf        = ddf[combined_mask].persist()
                base_df             = filtered_ddf.compute()
                additional_keywords = set(base_df[additional_col].dropna().unique())
                def _match_add(df, col, kws):
                    return df[df[col].isin(kws)]
                additional_df = ddf.map_partitions(
                    _match_add, additional_col, additional_keywords,
                    meta=ddf._meta).compute()
                result_df = pd.concat(
                    [base_df, additional_df], ignore_index=True).drop_duplicates()
            else:
                result_df = ddf[combined_mask].compute()
            if result_df.empty:
                def handle_no_results():
                    self.update_analysis_status("❗ 필터링 결과 없음", 0.0)
                    self.end_busy("parquet_ready")
                    messagebox.showinfo("결과 없음", "필터링 결과가 없습니다.")
                self.ui_call(handle_no_results)
                return
            self.update_analysis_status("💾 파일 저장 중...", 0.9)
            self.ui_call(self._save_filter_result,
                         result_df, parsed_filters, use_additional,
                         additional_col, total_source_rows, start_time)
        except Exception as e:
            def on_error(err=e):
                self.end_busy("parquet_ready")
                messagebox.showerror("필터링 오류", str(err))
            self.ui_call(on_error)
    def _save_filter_result(self, result_df, parsed_filters, use_additional,
                            additional_col, total_source_rows, start_time):
        try:
            first_col, first_kws = (parsed_filters[0] if parsed_filters
                                    else ("필터", ["조건"]))
            base       = os.path.splitext(os.path.basename(self.df_path))[0]
            base_clean = re.sub(r"[^\w가-힣]", "", base)
            col_clean  = re.sub(r"[^\w가-힣]", "", first_col)
            kw_main    = re.sub(r"[^\w가-힣]", "", first_kws[0])[:20] if first_kws else "조건"
            kw_suffix  = kw_main
            if first_kws and len(first_kws) > 1:
                kw_suffix += f"_외{len(first_kws) - 1}건"
            if len(parsed_filters) > 1:
                kw_suffix += f"_멀티{len(parsed_filters)}필터"
            timestamp = datetime.datetime.now().strftime("%y%m%d_%H%M%S")
            filename  = f"txtGL_Filter_{base_clean}_{col_clean}_{kw_suffix}_{timestamp}.csv"
            base_dir  = os.path.dirname(self.df_path)
            save_path = filedialog.asksaveasfilename(
                defaultextension=".csv",
                filetypes=[("CSV 파일", "*.csv")],
                initialfile=filename,
                initialdir=base_dir,
            )
            if not save_path:
                self.end_busy("parquet_ready")
                return
            base_name, ext   = os.path.splitext(save_path)
            result_rows      = len(result_df)
            self.filter_result_parts = []
            df_to_save = self._rename_df_columns_to_display(result_df)
            if result_rows > EXCEL_MAX_ROWS:
                num_parts = (result_rows + EXCEL_MAX_ROWS - 1) // EXCEL_MAX_ROWS
                for i in range(num_parts):
                    part_df   = df_to_save.iloc[i * EXCEL_MAX_ROWS:(i + 1) * EXCEL_MAX_ROWS]
                    part_path = f"{base_name}_part{i + 1}{ext}"
                    part_df.to_csv(part_path, index=False, encoding="utf-8-sig")
                    self.filter_result_parts.append(part_path)
                self.filter_result_file = self.filter_result_parts[0]
            else:
                df_to_save.to_csv(save_path, index=False, encoding="utf-8-sig")
                self.filter_result_file = save_path
            self.save_analysis_state()
            elapsed     = time.time() - start_time
            elapsed_msg = f"{elapsed:.2f}초"
            self.update_analysis_status(
                f"✅ {result_rows:,}건 완료 / ⏱ {elapsed_msg}", progress=1.0, save=True)
            kw_preview = []
            for col, kws in parsed_filters:
                if not kws:
                    continue
                prev = ", ".join(kws[:5])
                if len(kws) > 5:
                    prev += f", 외 {len(kws) - 5}건"
                kw_preview.append(f"{col}: {prev}")
            kw_text = "\n".join(kw_preview) if kw_preview else "(키워드 없음)"
            info_lines = [
                f"✅ 필터링 완료: {result_rows:,}건",
                f"⏱️ 처리 시간: {elapsed_msg}",
                f"🔍 필터별 키워드:\n{kw_text}",
            ]
            if use_additional:
                info_lines.append(f"➕ 추가 필터링 열: {additional_col}")
            total_text = (f"{total_source_rows:,}"
                          if isinstance(total_source_rows, int) else str(total_source_rows))
            info_lines.append(f"📊 읽은 총 행 수: {total_text}")
            self.end_busy("parquet_ready")
            self.update_result_buttons()
            messagebox.showinfo("완료", "\n".join(info_lines))
        except Exception as e:
            self.end_busy("parquet_ready")
            messagebox.showerror("저장 오류", str(e))
    # -----------------------------------------------------------------------
    # Pivot
    # -----------------------------------------------------------------------
    @staticmethod
    def _normalize_blank_values(df: pd.DataFrame, columns: list, marker: str) -> pd.DataFrame:
        for col in columns:
            if col in df.columns:
                df[col] = (df[col].fillna(marker)
                           .replace(r'^\s*$', marker, regex=True))
        return df
    def run_pivot(self):
        start_time    = time.time()
        index_fields  = list(self.selected_index_buttons)
        column_fields = list(self.selected_column_buttons)
        value_field   = self._original_header(self.value_var.get())
        agg_func      = self.agg_var.get()
        parquet_path  = self.df_path + ".parquet"
        save_dir      = os.path.dirname(self.df_path)
        if not value_field:
            self.update_analysis_status("❗ 피벗 값 필드 선택 누락", 0.0)
            self.end_busy("parquet_ready")
            messagebox.showwarning("경고", "값 필드를 선택하세요.")
            return
        def pivot_logic():
            try:
                self.update_analysis_status("📥 데이터 로딩 중...", 0.2)
                needed_cols = list(dict.fromkeys(index_fields + column_fields + [value_field]))
                ddf = dd.read_parquet(parquet_path, columns=needed_cols)
                blank_marker = "__BLANK__"
                grp_cands    = index_fields + column_fields
                if grp_cands:
                    ddf = ddf.map_partitions(
                        FilterPivotApp._normalize_blank_values, grp_cands, blank_marker)
                if value_field in ddf.columns:
                    ddf[value_field] = (ddf[value_field]
                                        .fillna(blank_marker)
                                        .replace(r'^\s*$', blank_marker, regex=True))
                self.update_analysis_status("📊 피벗 집계 중...", 0.5)
                if agg_func == "합계":
                    def clean_numeric(df):
                        if value_field in df.columns:
                            df[value_field] = pd.to_numeric(
                                df[value_field].astype(str).str.replace(",", "", regex=False),
                                errors="coerce")
                        return df
                    ddf = ddf.map_partitions(clean_numeric)
                    ddf = ddf[ddf[value_field].notnull()]
                # Case 1: 행/열 모두 미선택
                if not index_fields and not column_fields:
                    total = (ddf[value_field].sum().compute()
                             if agg_func == "합계"
                             else ddf[value_field].fillna(blank_marker).nunique().compute())
                    disp_vf   = self._display_header(value_field)
                    result_df = pd.DataFrame(
                        [{"구분": "전체", f"{agg_func.upper()}({disp_vf})": total}])
                # Case 2: 행 기준만
                elif index_fields and not column_fields:
                    grouped = (ddf.groupby(index_fields)[value_field].sum()
                               if agg_func == "합계"
                               else ddf.groupby(index_fields)[value_field].nunique())
                    result_df = grouped.reset_index().compute()
                    disp_idx  = [self._display_header(h) for h in index_fields]
                    disp_vf   = self._display_header(value_field)
                    result_df.columns = disp_idx + [f"{agg_func.upper()}({disp_vf})"]
                # Case 3: 열 기준만
                elif not index_fields and column_fields:
                    grouped = (ddf.groupby(column_fields)[value_field].sum()
                               if agg_func == "합계"
                               else ddf.groupby(column_fields)[value_field].nunique())
                    temp_df  = grouped.reset_index().compute()
                    disp_col = [self._display_header(h) for h in column_fields]
                    disp_vf  = self._display_header(value_field)
                    agg_name = f"{agg_func.upper()}({disp_vf})"
                    temp_df.columns = disp_col + [agg_name]
                    if len(disp_col) == 1:
                        temp_df2  = temp_df.set_index(disp_col[0])
                        result_df = temp_df2[[agg_name]].T.reset_index(drop=True)
                        result_df.columns.name = None
                    else:
                        temp_df["_전체"] = "전체"
                        result_df = temp_df.pivot_table(
                            index="_전체", columns=disp_col,
                            values=agg_name, aggfunc="sum").reset_index(drop=True)
                        if isinstance(result_df.columns, pd.MultiIndex):
                            result_df.columns = [
                                " ".join(map(str, c)).strip()
                                for c in result_df.columns.values]
                # Case 4: 행 + 열 모두
                else:
                    grp_all = index_fields + column_fields
                    grouped = (ddf.groupby(grp_all)[value_field].sum()
                               if agg_func == "합계"
                               else ddf.groupby(grp_all)[value_field].nunique())
                    temp_df  = grouped.reset_index().compute()
                    disp_idx = [self._display_header(h) for h in index_fields]
                    disp_col = [self._display_header(h) for h in column_fields]
                    disp_vf  = self._display_header(value_field)
                    agg_name = f"{agg_func.upper()}({disp_vf})"
                    temp_df.columns = disp_idx + disp_col + [agg_name]
                    self.update_analysis_status("📐 Wide 포맷 변환 중...", 0.7)
                    result_df = temp_df.pivot(
                        index=disp_idx, columns=disp_col, values=agg_name).reset_index()
                    if isinstance(result_df.columns, pd.MultiIndex):
                        result_df.columns = [
                            " ".join(map(str, c)).strip()
                            for c in result_df.columns.values]
                self.update_analysis_status("💾 파일 저장 중...", 0.9)
                base      = os.path.splitext(os.path.basename(self.df_path))[0]
                timestamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
                filename  = f"txtGL_Pivot_{base}_{timestamp}.csv"
                save_path = os.path.join(save_dir, filename)
                result_df.to_csv(save_path, index=False, encoding="utf-8-sig")
                elapsed = time.time() - start_time
                def on_done():
                    self.pivot_result_file = save_path
                    self.save_analysis_state()
                    self.update_analysis_status(
                        f"✅ {result_df.shape[0]:,}행 × {result_df.shape[1]:,}열 "
                        f"/ ⏱ {elapsed:.2f}초", 1.0)
                    self.end_busy("parquet_ready")
                    self.update_result_buttons()
                    messagebox.showinfo(
                        "피벗 완료",
                        f"✅ {result_df.shape[0]:,}행 × {result_df.shape[1]:,}열\n"
                        f"⏱ 소요 시간: {elapsed:.2f}초\n"
                        f"📁 저장 위치:\n{save_path}",
                    )
                self.ui_call(on_done)
            except Exception as e:
                err_type, err_msg = type(e).__name__, str(e)
                def on_error():
                    self.end_busy("parquet_ready")
                    messagebox.showerror("피벗 오류", f"{err_type}: {err_msg}")
                self.ui_call(on_error)
        threading.Thread(target=pivot_logic, daemon=True).start()
    # -----------------------------------------------------------------------
    # 결과 파일 열기 / 삭제
    # -----------------------------------------------------------------------
    def open_result_file(self):
        mode = self.selected_analysis
        if mode == "Filter":
            parts = getattr(self, "filter_result_parts", [])
            rf    = getattr(self, "filter_result_file", "")
            if parts and isinstance(parts, list) and len(parts) > 1:
                p1 = parts[0]
                if os.path.exists(p1):
                    if messagebox.askyesno(
                        "분할 파일 실행",
                        f"🔄 분석 결과가 총 {len(parts)}개의 분할 파일로 저장되었습니다.\n\n"
                        f"{os.path.basename(p1)} ~ part{len(parts)}.csv\n\n"
                        "첫 번째 파일(part1)을 열까요?",
                    ):
                        _open_file_cross_platform(p1)
                else:
                    messagebox.showwarning("파일 없음",
                                           "첫 번째 분할 파일이 존재하지 않습니다.")
                    self.filter_result_file  = ""
                    self.filter_result_parts = []
                    self.update_result_buttons()
                    self.save_analysis_state()
                return
            if rf and os.path.exists(rf):
                _open_file_cross_platform(rf)
                return
            messagebox.showwarning("파일 없음", "필터링 결과 파일이 존재하지 않습니다.")
            self.filter_result_file  = ""
            self.filter_result_parts = []
            self.update_result_buttons()
            self.save_analysis_state()
        elif mode == "Pivot":
            rf = getattr(self, "pivot_result_file", "")
            if rf and os.path.exists(rf):
                _open_file_cross_platform(rf)
                return
            messagebox.showwarning("파일 없음", "피벗 분석 결과 파일이 존재하지 않습니다.")
            self.pivot_result_file = ""
            self.update_result_buttons()
            self.save_analysis_state()
    def delete_result_file(self):
        mode          = self.selected_analysis
        deleted_files = []
        missing_files = []
        failed_files  = []
        if mode == "Filter":
            parts   = getattr(self, "filter_result_parts", [])
            rf      = getattr(self, "filter_result_file", "")
            targets = parts if (parts and isinstance(parts, list)) else ([rf] if rf else [])
            if not targets:
                messagebox.showwarning("파일 없음", "삭제할 필터링 분석 결과 파일이 없습니다.")
                return
            for f in targets:
                if os.path.exists(f):
                    try:
                        os.remove(f)
                        deleted_files.append(f)
                    except Exception as e:
                        failed_files.append((f, str(e)))
                else:
                    missing_files.append(f)
            if not failed_files:
                self.filter_result_file  = ""
                self.filter_result_parts = []
        elif mode == "Pivot":
            rf = getattr(self, "pivot_result_file", "")
            if not rf:
                messagebox.showwarning("파일 없음", "삭제할 피벗 분석 결과 파일이 없습니다.")
                return
            if os.path.exists(rf):
                try:
                    os.remove(rf)
                    deleted_files.append(rf)
                except Exception as e:
                    failed_files.append((rf, str(e)))
            else:
                missing_files.append(rf)
            if not failed_files:
                self.pivot_result_file = ""
        else:
            messagebox.showwarning("분석 모드 없음", "선택된 분석 모드를 확인할 수 없습니다.")
            return
        if deleted_files:
            messagebox.showinfo(
                "삭제 완료",
                f"{len(deleted_files)}개 파일이 삭제되었습니다:\n\n"
                + "\n".join(os.path.basename(f) for f in deleted_files),
            )
        if failed_files:
            messagebox.showerror(
                "삭제 실패",
                "일부 파일 삭제 실패:\n\n"
                + "\n".join(f"{os.path.basename(f)}: {m}" for f, m in failed_files),
            )
            return
        if missing_files:
            messagebox.showwarning(
                "일부 파일 없음",
                f"{len(missing_files)}개 파일은 이미 존재하지 않습니다:\n\n"
                + "\n".join(os.path.basename(f) for f in missing_files),
            )
        self.update_result_buttons()
        self.save_analysis_state()
        self.update_status("", 0.0)
    # -----------------------------------------------------------------------
    # 상태 저장 / 복원
    # -----------------------------------------------------------------------
    def save_analysis_state(self):
        if not self.df_path:
            return
        state = {
            "header_display_map": self.header_display_map,
            "filter": {
                "column": (self.filter_columns[self.current_filter_index.get() - 1]
                           if 0 <= self.current_filter_index.get() - 1 < self.max_filters
                           else ""),
                "additional_enabled": self.additional_filter_var.get(),
                "additional_column":  self._original_header(self.additional_col_select.get()),
                "active_count":       self.active_filter_count_var.get(),
                "columns_multi":      self.filter_columns,
                "keyword_texts_multi": self.filter_keyword_texts,
            },
            "pivot": {
                "index":   list(self.selected_index_buttons),
                "columns": list(self.selected_column_buttons),
                "value":   self._original_header(self.value_var.get()),
                "agg":     self.agg_var.get(),
            },
            "filter_result_file":  (self.filter_result_file
                                    if isinstance(self.filter_result_file, str) else ""),
            "filter_result_parts": (self.filter_result_parts
                                    if isinstance(self.filter_result_parts, list) else []),
            "pivot_result_file":   (self.pivot_result_file
                                    if isinstance(self.pivot_result_file, str) else ""),
            "parquet_blocksize":   self.blocksize_var.get(),
            "parquet_npartitions": getattr(self, "last_parquet_npartitions", "N/A"),
        }
        state_path = self.df_path + ".state.json"
        try:
            with open(state_path, "w", encoding="utf-8") as f:
                json.dump(state, f, ensure_ascii=False, indent=4)
        except Exception as e:
            print(f"[상태 저장 실패] {e}")
    def load_analysis_state(self):
        if not self.df_path or not self.headers:
            self.toggle_additional_filter()
            return
        state_path = self.df_path + ".state.json"
        if not os.path.exists(state_path):
            self.toggle_additional_filter()
            return
        try:
            with open(state_path, "r", encoding="utf-8") as f:
                state = json.load(f)
            saved_map = state.get("header_display_map", {})
            self.header_display_map = {orig: saved_map.get(orig, orig)
                                       for orig in self.original_headers}
            self._rebuild_header_display_maps()
            fs           = state.get("filter", {})
            active_count = max(1, min(self.max_filters, fs.get("active_count", 1)))
            self.active_filter_count_var.set(active_count)
            cols_multi = fs.get("columns_multi", [])
            self.filter_columns = [""] * self.max_filters
            for i in range(min(len(cols_multi), self.max_filters)):
                if cols_multi[i] in self.original_headers:
                    self.filter_columns[i] = cols_multi[i]
            kw_multi = fs.get("keyword_texts_multi", [])
            self.filter_keyword_texts = [""] * self.max_filters
            for i in range(min(len(kw_multi), self.max_filters)):
                self.filter_keyword_texts[i] = kw_multi[i]
            self.current_filter_index.set(1)
            try:
                self.filter_count_menu.set(str(active_count))
                self.filter_toggle.set("필터1")
            except Exception:
                pass
            self.additional_filter_var.set(fs.get("additional_enabled", False))
            self.additional_col_select.configure(values=self.headers)
            add_orig = fs.get("additional_column", "")
            if add_orig in self.original_headers:
                self.additional_col_select.set(self._display_header(add_orig))
            self.toggle_additional_filter()
            self._refresh_filter_header_options()
            self.keyword_input.delete("1.0", "end")
            if self.filter_keyword_texts[0]:
                self.keyword_input.insert("1.0", self.filter_keyword_texts[0])
            self.update_keyword_count()
            ps = state.get("pivot", {})
            self.selected_index_buttons  = [v for v in ps.get("index", [])
                                            if v in self.original_headers]
            self.selected_column_buttons = [v for v in ps.get("columns", [])
                                            if v in self.original_headers]
            pv_orig = ps.get("value", "")
            self.value_var.set(self._display_header(pv_orig)
                               if pv_orig in self.original_headers
                               else (self.headers[0] if self.headers else ""))
            self.agg_var.set(ps.get("agg", "합계"))
            self.update_selection_display(
                self.index_listbox, self.selected_index_buttons, self.index_buttons_frame)
            self.update_selection_display(
                self.column_listbox, self.selected_column_buttons, self.column_buttons_frame)
            self.refresh_header_display_ui()
            self.filter_result_file  = state.get("filter_result_file", "")
            self.filter_result_parts = state.get("filter_result_parts", [])
            self.pivot_result_file   = state.get("pivot_result_file", "")
            self.update_result_buttons()
        except Exception as e:
            print(f"[상태 파일 로딩 실패] {e}")
            self.toggle_additional_filter()
    # -----------------------------------------------------------------------
    # 유틸리티
    # -----------------------------------------------------------------------
    def _shorten_filename(self, filename: str, max_length=80) -> str:
        if len(filename) <= max_length:
            return filename
        name, ext  = os.path.splitext(filename)
        prefix_len = 62
        suffix_len = max(18, max_length - prefix_len - len(ext) - 5)
        return f"{name[:prefix_len]} ... {name[-suffix_len:]}{ext}"
    def adjust_window_height(self):
        """debounce 적용 — 빈번한 호출 시 깜빡임 방지."""
        if self._height_job:
            try:
                self.after_cancel(self._height_job)
            except Exception:
                pass
        self._height_job = self.after(80, self._do_adjust_height)
    def _do_adjust_height(self):
        self._height_job = None
        try:
            self.update_idletasks()
            self.geometry(f"1450x{max(self.winfo_reqheight(), 300)}")
        except Exception:
            pass
# ===========================================================================
# 엔트리 포인트
# ===========================================================================
if __name__ == "__main__":
    app = FilterPivotApp()
    app.after(100, lambda: app.geometry(f"1450x{app.winfo_reqheight()}"))
    app.mainloop()
