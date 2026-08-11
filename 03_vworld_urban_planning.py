# -*- coding: utf-8 -*-
"""
[2단계] V-World 도시계획 규제 추출 스크립트
================================================================
QGIS Python 콘솔에서 실행하는 스크립트입니다.

이전 진단 스크립트를 실무용으로 확장했습니다. 하는 일:

  1) 구역계(대상지) 폴리곤을 기준으로 두 개의 분석 범위를 만듭니다.
        ① 구역계            : 대상지 그 자체 (집중 검토용)
        ② 구역계 + 2km      : 구역계 경계에서 2km 바깥으로 오프셋한
                              "더 큰 사각형" (도시계획 전체 맥락 검토용)

  2) V-World OPEN API 로 아래 데이터를 "항상 전체 데이터"로 가져옵니다.
        · 용도지역지구 / 도시계획시설 등 각종 규제사항
            (국토관리 지역개발 > 용도지역지구)
        · 연속지적도_전국  (국토관리 지역개발 > 토지 > 연속지적도_전국)

  3) "토지임야정보" CSV(국토관리 지역개발 > 토지 > 토지임야정보)를
     선택하면, 연속지적도의 PNU(필지고유번호)와 조인하여
     지적도 폴리곤에 토지 속성(지목·면적·공시지가 등)을 붙입니다.

  4) 위 결과를 ① 구역계 / ② 구역계+2km 두 벌로 각각 클립하여
     레이어 그룹으로 정리해 프로젝트에 추가합니다.

  5) 조회 상태(개수·필드·상태)를 홈 폴더의 txt 파일로 저장합니다.

[사용법]
  1) 구역계(대상지) 폴리곤 레이어를 선택(활성)
  2) 플러그인 > Python 콘솔 > 편집기에서 이 파일 열고 ▶ 실행
  3) 실행 중 "토지임야정보 CSV" 파일을 물어보면 선택
     (조인이 필요 없으면 취소를 눌러도 됩니다)
"""

import os
import re
import csv
import json
import math
import time
import urllib.parse
import urllib.request

from qgis.core import (
    QgsProject, QgsVectorLayer, QgsRasterLayer, QgsGeometry, QgsRectangle,
    QgsCoordinateReferenceSystem, QgsCoordinateTransform, QgsWkbTypes,
    QgsJsonUtils, QgsField, QgsFeature, QgsVectorFileWriter,
    QgsPalLayerSettings, QgsVectorLayerSimpleLabeling,
    QgsTextBackgroundSettings, QgsProperty, QgsUnitTypes,
)
from qgis.PyQt.QtCore import QVariant, QSizeF
from qgis.PyQt.QtGui import QColor
from qgis.PyQt.QtWidgets import QInputDialog, QMessageBox, QFileDialog

# ─────────────────────────────────────────────────────────────
# 기본 설정
# ─────────────────────────────────────────────────────────────
VWORLD_KEY = "2C07FCEA-8C16-3A08-836E-44C7618D3919"
VWORLD_DOMAIN = "localhost"

# 구역계 경계로부터 바깥으로 넓힐 거리(미터). 요청사항: 2km
OFFSET_M = 2000

# "항상 전체 데이터"를 위한 페이징 설정
#  - 한 페이지가 PAGE_SIZE 미만이면 끝난 것으로 보고 멈춥니다.
#  - MAX_PAGES 는 무한루프 방지용 안전장치입니다(넉넉히).
PAGE_SIZE = 1000
MAX_PAGES = 1000

# 연속지적도처럼 필지가 조밀한 레이어는 넓은 영역을 한 번에 요청하면
# V-World 가 오류/빈응답을 주므로, 작은 타일로 쪼개서 요청한 뒤 합칩니다.
#  - TILE_M  : 타일 한 변의 길이(미터). 작을수록 안전하지만 요청 수가 늘어남.
#  - MAX_TILES : 요청 수 폭주 방지 안전장치.
TILE_M = 700
MAX_TILES = 4000

# 토지임야정보 (국가중점데이터API > 부동산 개방데이터 > 토지임야정보)
#  V-World NED API. 지적도의 PNU 로 한 필지씩 조회하여 속성을 붙입니다.
#  (요청주소: https://api.vworld.kr/ned/data/ladfrlList , pnu 필수)
LADFRL_URL = "https://api.vworld.kr/ned/data/ladfrlList"
#  PNU 개수가 이 값을 넘으면 "시간이 걸릴 수 있음"만 안내(조회는 전체 진행).
#  ※ 더 이상 조회 대상을 줄이지 않습니다 — 2km 포함 전체 필지에 조인합니다.
LADFRL_MAX_PNU = 6000

# 광역(구역계+2km) 레이어도 사각형으로 잘라낼지 여부
#  True  : 2km 사각형 경계에서 폴리곤을 잘라냄(요청대로 "사각형"으로)
#  False : 사각형에 걸치는 필지/구역을 자르지 않고 통째로 표시
CLIP_WIDE_TO_RECT = True

# ─────────────────────────────────────────────────────────────
# 규제 주제도 (국토관리 지역개발 > 용도지역지구)
#  하나의 QML(uname 기준)로 스타일링하기 위해 카테고리별로 데이터ID를 묶습니다.
#  (표시이름, [데이터ID들], QML 상대경로)
# ─────────────────────────────────────────────────────────────
# (표시이름, [데이터ID들], QML상대경로, 라벨식, 라벨식이 표현식인가)
#  라벨식이 None 이면 라벨 표시 안 함.
REG_GROUPS = [
    ("용도지역", ["LT_C_UQ111", "LT_C_UQ112", "LT_C_UQ113", "LT_C_UQ114"],
     "05_토지이용규제/5_1_용도지역_style.qml", "uname", False),
    ("용도지구", ["LT_C_UQ121", "LT_C_UQ123", "LT_C_UQ124", "LT_C_UQ125",
                  "LT_C_UQ126", "LT_C_UQ128", "LT_C_UQ129"],
     "05_토지이용규제/5_2_용도지구_style.qml", "uname", False),
    ("용도구역", ["LT_C_UD801"],
     "05_토지이용규제/5_3_용도구역_style.qml", None, False),
    ("도시계획시설", ["LT_C_UPISUQ151"],
     "05_토지이용규제/5_4_도시계획시설_style.qml", "ROAD", True),
]

# 용도지역지구 계열 스타일이 기준으로 삼는 필드명(모든 QML을 이 필드로 맞춰둠)
REG_STYLE_FIELD = "uname"

# 저장 좌표계 (요청: EPSG:5186 = Korea 2000 / 중부원점)
OUTPUT_CRS = "EPSG:5186"

# 도시계획시설 '도로' 라벨 표기식 (도면처럼 2줄 + 가운데 구분선)
#   중(국)
#   ──
#   3-1
#  = grad_se앞자(중로→중) + (pmi_nam앞자 국지도로→국) / 구분선 / road_ty(류)-road_no(번호)
#  grad_se: 등급(광로/대로/중로/소로),  pmi_nam: 기능(주간선/보조간선/집산/국지도로)
DIVIDER = "──"
ROAD_LABEL_EXPR = (
    "CASE WHEN coalesce(\"grad_se\",'')<>'' THEN "
    "left(\"grad_se\",1) || '(' || left(\"pmi_nam\",1) || ')' "
    "|| char(10) || '" + DIVIDER + "' || char(10) || "
    "\"road_ty\" || '-' || \"road_no\" "
    "ELSE \"uname\" END"
)

# 도로 원(라벨 배경) 색: 대로/광로=빨강, 중로/소로=파랑, 도로아님=검정
ROAD_COLOR_EXPR = (
    "CASE WHEN coalesce(\"grad_se\",'')='' THEN '0,0,0' "
    "WHEN left(\"grad_se\",1) IN ('대','광') THEN '255,0,0' "
    "ELSE '0,0,255' END"
)
# 도로일 때만 원 배경 그림
ROAD_DRAW_EXPR = "CASE WHEN coalesce(\"grad_se\",'')<>'' THEN 1 ELSE 0 END"

# 연속지적도_전국 (국토관리 지역개발 > 토지 > 연속지적도_전국)
CADASTRAL = ("연속지적도", "LP_PA_CBND_BUBUN")

# 구역계 스타일 QML
BOUNDARY_STYLE_QML = "00_구역계/2_0_구역계_style.qml"

# 지적도(토지임야정보) 스타일: (표시이름, QML상대경로)  ← 각각 별도 스타일 사본
CAD_STYLES = [
    ("연속지적도_지목",     "04_토지이용/4_2_지적도_지목_style.qml"),
    ("연속지적도_소유구분", "04_토지이용/4_1_지적도_소유구분_style.qml"),
    ("연속지적도_공시지가", "04_토지이용/4_3_지적도_공시지가_style.qml"),
]

# 스타일 QML 이 참조하는 "특수 필드" — 토지임야정보에서 이 이름으로 만들어 둡니다.
#  (대상필드명, [원본컬럼 힌트], 자료형)  numeric=True 면 실수형
SPECIAL_FIELDS = [
    ("li_lndcgrC", ["lndcgr"],          False),  # 지목 코드 (QML: 4_2, 값 1~28)
    ("li_poses_1", ["posesn", "poses"], False),  # 소유구분 코드 (QML: 4_1, 값 0~9)
    ("jiga",       ["pblntf", "공시"],   True),   # 개별공시지가 (QML: 4_3, 숫자·ASCII)
]

# 지적도/CSV 에서 PNU(필지고유번호) 로 인식할 후보 컬럼명
PNU_KEYS = ["pnu", "PNU", "고유번호", "필지고유번호", "pnu_cd", "A1"]

# ─────────────────────────────────────────────────────────────
# 로그: 콘솔 + 홈폴더 txt 에 "즉시" 기록(중간에 QGIS가 튕겨도 어디서 멈췄는지 남김)
log_lines = []
LOG_PATH = os.path.join(os.path.expanduser("~"), "vworld_도시계획_결과.txt")
try:
    _log_fp = open(LOG_PATH, "w", encoding="utf-8")
except Exception:
    _log_fp = None


def log(s=""):
    print(s)
    log_lines.append(str(s))
    if _log_fp:
        try:
            _log_fp.write(str(s) + "\n")
            _log_fp.flush()
        except Exception:
            pass


# ─────────────────────────────────────────────────────────────
# 1) 구역계 레이어 선택
# ─────────────────────────────────────────────────────────────
def get_boundary_layer():
    active = iface.activeLayer()
    if (isinstance(active, QgsVectorLayer)
            and QgsWkbTypes.geometryType(active.wkbType()) == QgsWkbTypes.PolygonGeometry):
        return active
    poly = [l for l in QgsProject.instance().mapLayers().values()
            if isinstance(l, QgsVectorLayer)
            and QgsWkbTypes.geometryType(l.wkbType()) == QgsWkbTypes.PolygonGeometry]
    if not poly:
        log("❌ 폴리곤(구역계) 레이어가 없습니다.")
        return None
    names = [l.name() for l in poly]
    name, ok = QInputDialog.getItem(iface.mainWindow(), "구역계 레이어 선택",
                                    "구역계 레이어를 고르세요:", names, 0, False)
    return poly[names.index(name)] if ok else None


# ─────────────────────────────────────────────────────────────
# 2) 구역계 → (구역계 지오메트리, 2km 사각형 지오메트리, API용 BBOX)
#    - 거리(2km) 계산은 미터 기반 좌표계에서 수행
#    - 결과 지오메트리/BBOX 는 EPSG:4326 으로 반환
# ─────────────────────────────────────────────────────────────
def build_analysis_extents(layer):
    project = QgsProject.instance()
    src_crs = layer.crs()
    crs4326 = QgsCoordinateReferenceSystem("EPSG:4326")

    # 미터 기반 좌표계 결정 (구역계가 경위도면 UTM-K/중부원점으로 투영)
    metric_crs = src_crs if not src_crs.isGeographic() \
        else QgsCoordinateReferenceSystem("EPSG:5186")

    geoms = [f.geometry() for f in layer.getFeatures() if f.hasGeometry()]
    if not geoms:
        return None, None, None
    union = QgsGeometry.unaryUnion(geoms)
    if not union.isGeosValid():
        union = union.makeValid()   # CAD 유래 폴리곤 클립 누락 방지

    # 구역계 → 미터 좌표계
    tr_to_metric = QgsCoordinateTransform(src_crs, metric_crs, project)
    union_m = QgsGeometry(union)
    if src_crs != metric_crs:
        union_m.transform(tr_to_metric)

    # 2km 오프셋 사각형 (미터 좌표계에서 BBOX 를 사방 2km 확장)
    b = union_m.boundingBox()
    rect_m = QgsRectangle(b.xMinimum() - OFFSET_M, b.yMinimum() - OFFSET_M,
                          b.xMaximum() + OFFSET_M, b.yMaximum() + OFFSET_M)
    rect_geom_m = QgsGeometry.fromRect(rect_m)

    # 미터 좌표계 → 4326
    tr_to_4326 = QgsCoordinateTransform(metric_crs, crs4326, project)
    boundary_4326 = QgsGeometry(union_m); boundary_4326.transform(tr_to_4326)
    rect_4326 = QgsGeometry(rect_geom_m); rect_4326.transform(tr_to_4326)

    rb = rect_4326.boundingBox()
    api_bbox = (rb.xMinimum(), rb.yMinimum(), rb.xMaximum(), rb.yMaximum())
    return boundary_4326, rect_4326, api_bbox


# ─────────────────────────────────────────────────────────────
# 3) V-World 데이터 API 조회 (항상 전체 데이터: 페이지 끝까지)
# ─────────────────────────────────────────────────────────────
def vworld_fetch(data_id, bbox):
    """반환: (status, features)  status = 'OK'|'NOT_FOUND'|'ERROR'|'NETERR'"""
    minx, miny, maxx, maxy = bbox
    geom_filter = f"BOX({minx},{miny},{maxx},{maxy})"
    all_features = []
    final_status = "NOT_FOUND"
    for page in range(1, MAX_PAGES + 1):
        params = {
            "service": "data", "version": "2.0", "request": "GetFeature",
            "format": "json", "errorformat": "json",
            "size": PAGE_SIZE, "page": page, "data": data_id,
            "geomFilter": geom_filter, "crs": "EPSG:4326",
            "domain": VWORLD_DOMAIN, "key": VWORLD_KEY,
        }
        url = "https://api.vworld.kr/req/data?" + urllib.parse.urlencode(params)
        try:
            with urllib.request.urlopen(url, timeout=60) as resp:
                data = json.loads(resp.read().decode("utf-8"))
        except Exception as e:
            log(f"     [네트워크 오류] {e}")
            return "NETERR", all_features

        status = data.get("response", {}).get("status")
        if status == "ERROR":
            err = data.get("response", {}).get("error", {})
            log(f"     [V-World 오류] {err}")
            return "ERROR", all_features
        if status == "NOT_FOUND":
            return ("OK" if all_features else "NOT_FOUND"), all_features

        fc = data.get("response", {}).get("result", {}).get("featureCollection", {})
        feats = fc.get("features", [])
        all_features.extend(feats)
        final_status = "OK"
        if len(feats) < PAGE_SIZE:
            break   # 마지막 페이지 → 전체 수집 완료
    return final_status, all_features


def _subdivide_bbox_deg(bbox, tile_m):
    """4326 BBOX 를 대략 tile_m(미터) 크기의 작은 사각형들로 분할."""
    minx, miny, maxx, maxy = bbox
    midlat = (miny + maxy) / 2.0
    m_per_deg_lat = 111320.0
    m_per_deg_lon = 111320.0 * max(0.1, math.cos(math.radians(midlat)))
    step_x = tile_m / m_per_deg_lon
    step_y = tile_m / m_per_deg_lat
    ncols = max(1, int(math.ceil((maxx - minx) / step_x)))
    nrows = max(1, int(math.ceil((maxy - miny) / step_y)))
    tiles = []
    for r in range(nrows):
        for c in range(ncols):
            x0 = minx + c * step_x
            y0 = miny + r * step_y
            x1 = min(maxx, x0 + step_x)
            y1 = min(maxy, y0 + step_y)
            tiles.append((x0, y0, x1, y1))
    return tiles


def _feat_pnu(feat):
    """GeoJSON feature 에서 PNU(필지고유번호) 문자열 추출 (없으면 None)."""
    props = feat.get("properties", {}) or {}
    for k in ("pnu", "PNU", "고유번호", "필지고유번호"):
        v = props.get(k)
        if v not in (None, ""):
            return str(v).strip()
    return None


def _feat_key(feat):
    """타일 경계 중복 제거용 고유키 (PNU → feature id → 지오메트리)."""
    pnu = _feat_pnu(feat)
    if pnu:
        return pnu
    if feat.get("id"):
        return str(feat["id"])
    return json.dumps(feat.get("geometry", {}), sort_keys=True)[:256]


def vworld_fetch_tiled(data_id, bbox):
    """조밀한 레이어(연속지적도 등)를 타일 단위로 전부 조회 후 병합.
       반환: (status, features)"""
    tiles = _subdivide_bbox_deg(bbox, TILE_M)
    if len(tiles) > MAX_TILES:
        log(f"     ⚠ 타일 {len(tiles)}개 → 상한 {MAX_TILES}개만 조회 "
            f"(TILE_M 을 키우면 타일 수가 줄어듭니다)")
        tiles = tiles[:MAX_TILES]
    log(f"     조밀 레이어 → {len(tiles)}개 타일로 나눠 전체 조회합니다...")

    merged = {}
    any_ok = False
    err_seen = None
    for i, tb in enumerate(tiles, 1):
        # 일시적 네트워크 오류로 타일이 통째로 빠지는 것을 막기 위해 재시도
        status, feats = vworld_fetch(data_id, tb)
        for _retry in range(2):
            if status != "NETERR":
                break
            status, feats = vworld_fetch(data_id, tb)
        if status == "OK":
            any_ok = True
        elif status in ("ERROR", "NETERR"):
            err_seen = status
            log(f"       ⚠ 타일 {i} 조회 실패(status={status}) → 이 칸은 건너뜀")
        for f in feats:
            merged[_feat_key(f)] = f
        if i % 20 == 0 or i == len(tiles):
            log(f"       진행 {i}/{len(tiles)} 타일 · 누적 {len(merged)}필지")

    if merged:
        status = "OK"
    else:
        status = err_seen or "NOT_FOUND"
    return status, list(merged.values())


# ─────────────────────────────────────────────────────────────
# 4) features(GeoJSON) → 클립된 메모리 레이어
# ─────────────────────────────────────────────────────────────
def build_layer(name, features, clip_geom_4326, do_clip=True):
    fc_str = json.dumps({"type": "FeatureCollection", "features": features})
    fields = QgsJsonUtils.stringToFields(fc_str)
    qgs_feats = QgsJsonUtils.stringToFeatureList(fc_str, fields)

    geom_type = "MultiPolygon"
    for f in qgs_feats:
        if f.hasGeometry():
            gt = QgsWkbTypes.geometryType(f.geometry().wkbType())
            geom_type = {0: "MultiPoint", 1: "MultiLineString",
                         2: "MultiPolygon"}.get(gt, "MultiPolygon")
            break

    lyr = QgsVectorLayer(f"{geom_type}?crs=EPSG:4326", name, "memory")
    dp = lyr.dataProvider()
    dp.addAttributes(fields.toList())
    lyr.updateFields()

    out = []
    for f in qgs_feats:
        g = f.geometry()
        if clip_geom_4326 is not None and g and not g.isEmpty():
            if not g.intersects(clip_geom_4326):
                continue
            if do_clip:
                clipped = g.intersection(clip_geom_4326)
                if clipped.isEmpty():
                    continue
                f.setGeometry(clipped)
        out.append(f)
    dp.addFeatures(out)
    lyr.updateExtents()
    return lyr


# ─────────────────────────────────────────────────────────────
# 5) 토지임야정보 CSV 읽기 (PNU → 속성 dict)
# ─────────────────────────────────────────────────────────────
def _find_pnu_col(header):
    # 완전일치 우선
    for key in PNU_KEYS:
        for h in header:
            if h.strip().lower() == key.lower():
                return h
    # 부분일치 (고유번호 포함 등)
    for h in header:
        hl = h.strip().lower()
        if "고유번호" in h or hl == "pnu" or "pnu" in hl:
            return h
    return None


def load_land_csv(needed_pnus=None):
    """토지임야정보 CSV(공공데이터포털 국가중점데이터)를 읽어 PNU→속성 dict 생성.
       needed_pnus 가 주어지면 지적도에 실제로 있는 PNU 행만 골라 읽어(메모리 절약)
       전국 단위 대용량 CSV 도 처리 가능.
       반환: (columns, index, pnu_col) 또는 (None, None, None)"""
    path, _ = QFileDialog.getOpenFileName(
        iface.mainWindow(),
        "토지임야정보 CSV 선택 (공공데이터포털 다운로드 · 취소하면 조인 생략)",
        os.path.expanduser("~"), "CSV 파일 (*.csv);;모든 파일 (*.*)")
    if not path:
        log("ℹ 토지임야정보 CSV 미선택 → 지적도 조인 생략")
        return None, None, None

    # 인코딩 자동 감지 (앞부분만 시험적으로 읽어 판별)
    used_enc = None
    for enc in ("cp949", "euc-kr", "utf-8-sig", "utf-8"):
        try:
            with open(path, "r", encoding=enc, newline="") as fp:
                fp.read(8192)
            used_enc = enc
            break
        except Exception:
            continue
    if used_enc is None:
        log(f"⚠ CSV 인코딩을 읽지 못했습니다: {path}")
        return None, None, None

    # 구분자 감지 (기본 콤마)
    delim = ","
    try:
        with open(path, "r", encoding=used_enc, newline="") as fp:
            sample = fp.read(4096)
        delim = csv.Sniffer().sniff(sample, delimiters=",\t;|").delimiter
    except Exception:
        pass

    # 대용량 대비: 파일을 통째로 올리지 않고 한 줄씩 스트리밍하며
    # 지적도에 있는 PNU(needed_pnus)만 골라 담는다.
    index = {}
    columns = None
    pnu_col = None
    pnu_idx = None
    total = 0
    with open(path, "r", encoding=used_enc, newline="") as fp:
        reader = csv.reader(fp, delimiter=delim)
        for row in reader:
            if pnu_idx is None:
                header = row
                pnu_col = _find_pnu_col(header)
                if pnu_col is None:
                    log(f"⚠ CSV 에서 PNU 컬럼을 찾지 못했습니다. 헤더={header}")
                    return None, None, None
                pnu_idx = header.index(pnu_col)
                columns = [h for i, h in enumerate(header) if i != pnu_idx]
                continue
            total += 1
            if len(row) <= pnu_idx:
                continue
            pnu = str(row[pnu_idx]).strip()
            if not pnu:
                continue
            if needed_pnus is not None and pnu not in needed_pnus:
                continue
            index[pnu] = {header[i]: (row[i] if i < len(row) else "")
                          for i in range(len(header)) if i != pnu_idx}

    scope = "지적도 매칭행만" if needed_pnus is not None else "전체행"
    log(f"✔ 토지임야정보 CSV 로드: {os.path.basename(path)} "
        f"(enc={used_enc}, 구분자='{delim}', PNU컬럼='{pnu_col}', "
        f"전체 {total}행 중 {scope} {len(index)}개, 속성열={len(columns)}개)")
    return columns, index, pnu_col


# ─────────────────────────────────────────────────────────────
# 5-B) 토지임야정보 V-World API 조회 (PNU → 속성 dict)
#      국가중점데이터API > 부동산 개방데이터 > 토지임야정보 (ladfrlList)
#      → CSV 다운로드 없이 지적도의 PNU 로 바로 조회하여 붙입니다.
# ─────────────────────────────────────────────────────────────
def _extract_records(obj):
    """NED API 응답(JSON) 안에서 '레코드(dict) 목록'을 찾아 반환."""
    found = []

    def walk(o):
        if isinstance(o, list):
            if o and all(isinstance(x, dict) for x in o):
                found.append(o)
            else:
                for x in o:
                    walk(x)
        elif isinstance(o, dict):
            for v in o.values():
                walk(v)

    walk(obj)
    return found[0] if found else []


def _rec_pnu(rec):
    """레코드(dict)에서 PNU 값 추출."""
    for k in ("pnu", "PNU", "고유번호", "필지고유번호"):
        v = rec.get(k)
        if v not in (None, ""):
            return str(v).strip()
    return None


def _rec_year(rec):
    for k in ("stdrYear", "STDR_YEAR", "standardYear", "lastUpdtDt"):
        v = rec.get(k)
        if v:
            try:
                return int(str(v)[:4])
            except Exception:
                return 0
    return 0


def fetch_ladfrl_list(pnu_value, max_pages=50):
    """ladfrlList 를 페이징으로 조회하여 레코드 목록 반환.
       pnu_value 는 전체 PNU(19자리) 또는 법정동코드 접두(10자리)일 수 있음.
       반환: (records, status)  status='OK'|'NETERR'"""
    out = []
    for page in range(1, max_pages + 1):
        params = {
            "pnu": pnu_value, "format": "json",
            "numOfRows": 1000, "pageNo": page,
            "key": VWORLD_KEY, "domain": VWORLD_DOMAIN,
        }
        url = LADFRL_URL + "?" + urllib.parse.urlencode(params)
        try:
            with urllib.request.urlopen(url, timeout=40) as resp:
                data = json.loads(resp.read().decode("utf-8"))
        except Exception:
            return out, "NETERR"
        recs = _extract_records(data)
        if not recs:
            break
        out.extend(recs)
        if len(recs) < 1000:
            break
    return out, "OK"


def build_ladfrl_index(pnus):
    """토지임야정보를 V-World API 로 조회 → (columns, index).
       ① 법정동코드(앞 10자리) 단위로 묶어 조회(지원 시 훨씬 빠름)
       ② 그래도 안 붙은 필지는 PNU 개별 조회(재시도 포함)로 보완 → 전체 필지 커버.
       columns = PNU 제외 속성 컬럼명 목록, index[pnu] = {col: val}."""
    target = {p for p in pnus if p}
    total = len(target)
    log(f"     토지임야정보 API 조회 대상 필지: {total}개")
    index, yearmap = {}, {}
    cols, seen = [], set()

    def absorb(rec):
        key = _rec_pnu(rec)
        if not key or key not in target:
            return
        y = _rec_year(rec)
        if key in index and y <= yearmap.get(key, -1):
            return   # 이미 더 최신(또는 동일) 연도 보유
        yearmap[key] = y
        clean = {}
        for k, v in rec.items():
            if k.strip().lower() == "pnu" or "고유번호" in k:
                continue
            clean[k] = "" if v is None else str(v)
            if k not in seen:
                seen.add(k)
                cols.append(k)
        index[key] = clean

    # ① 법정동 단위 묶음 조회
    ldcodes = sorted({p[:10] for p in target if len(p) >= 10})
    if ldcodes:
        log(f"     [1차] 법정동 {len(ldcodes)}곳 묶음 조회...")
        for i, lc in enumerate(ldcodes, 1):
            recs, _ = fetch_ladfrl_list(lc)
            for r in recs:
                absorb(r)
            if i % 10 == 0 or i == len(ldcodes):
                log(f"       진행 {i}/{len(ldcodes)} 법정동 · 누적 {len(index)}/{total}")

    # ② 남은 필지 개별 조회(재시도)
    missing = [p for p in sorted(target) if p not in index]
    if missing:
        log(f"     [2차] 개별 조회 필지: {len(missing)}개...")
        for i, p in enumerate(missing, 1):
            recs, st = fetch_ladfrl_list(p, max_pages=3)
            attempt = 1
            while not recs and st == "NETERR" and attempt < 3:
                time.sleep(0.5 * attempt)
                attempt += 1
                recs, st = fetch_ladfrl_list(p, max_pages=3)
            for r in recs:
                absorb(r)
            if i % 50 == 0 or i == len(missing):
                log(f"       진행 {i}/{len(missing)} · 누적 {len(index)}/{total}")

    still = total - len(index)
    log(f"     ⇒ 토지임야 조인 준비: {len(index)}/{total} 필지 매칭"
        f"{f', 미매칭 {still}개' if still else ''}, 속성열 {len(cols)}개")
    return cols, index


# ─────────────────────────────────────────────────────────────
# 6) 지적도 레이어에 토지임야정보 조인 (PNU 기준)
# ─────────────────────────────────────────────────────────────
def _layer_pnu_field(layer):
    """레이어 필드 중 PNU(필지고유번호) 필드명을 찾아 반환(없으면 None)."""
    field_names = [f.name() for f in layer.fields()]
    for key in PNU_KEYS:
        for fn in field_names:
            if fn.strip().lower() == key.lower():
                return fn
    for fn in field_names:
        if "pnu" in fn.lower() or "고유번호" in fn:
            return fn
    return None


def _pick_src_col(columns, hints):
    """columns 중 hints 를 포함하는 컬럼을 찾아 반환(이름/명 컬럼은 뒤로)."""
    cands = [c for c in columns if any(h in c.lower() for h in hints)]
    if not cands:
        return None
    code_first = [c for c in cands
                  if not (c.lower().endswith("nm") or c.endswith("명"))]
    return (code_first or cands)[0]


def join_land_info(cadastral_layer, columns, index):
    if not columns or not index:
        return 0

    field_names = [f.name() for f in cadastral_layer.fields()]
    pnu_field = _layer_pnu_field(cadastral_layer)
    if pnu_field is None:
        log(f"⚠ 지적도에서 PNU 필드를 찾지 못했습니다. 필드={field_names}")
        return 0

    # 조인 필드 추가 (이름 정리 + 중복 회피)
    existing = set(field_names)
    col_to_field = {}
    new_fields = []
    for col in columns:
        base = ("li_" + col).strip()[:63]  # land info 접두사
        name = base
        n = 1
        while name in existing:
            name = (base[:60] + "_%d" % n)
            n += 1
        existing.add(name)
        col_to_field[col] = name
        new_fields.append(QgsField(name, QVariant.String))

    # 스타일 QML 이 참조하는 특수 필드(li_lndcgrC / li_poses_1 / 공시지가) 준비
    special = []   # (대상필드명, 원본컬럼, numeric)
    for tgt, hints, numeric in SPECIAL_FIELDS:
        src = _pick_src_col(columns, hints)
        if not src:
            log(f"     · 스타일필드 {tgt}: 원본컬럼 자동탐지 실패(힌트 {hints})")
            continue
        special.append((tgt, src, numeric))
        log(f"     · 스타일필드 {tgt} ← 토지임야 '{src}'{' (숫자)' if numeric else ''}")
        if tgt not in existing:
            existing.add(tgt)
            new_fields.append(
                QgsField(tgt, QVariant.Double if numeric else QVariant.String))

    cadastral_layer.dataProvider().addAttributes(new_fields)
    cadastral_layer.updateFields()

    # 값 채우기
    matched = 0
    cadastral_layer.startEditing()
    for f in cadastral_layer.getFeatures():
        pnu = str(f[pnu_field]).strip()
        row = index.get(pnu)
        if not row:
            continue
        for col, fld in col_to_field.items():
            f[fld] = row.get(col, "")
        for tgt, src, numeric in special:
            raw = str(row.get(src, "")).strip()
            if numeric:
                try:
                    f[tgt] = float(raw) if raw != "" else None
                except Exception:
                    f[tgt] = None
            else:
                if raw.isdigit():      # 코드: 앞자리 0 제거 → QML 값(1,2,..)과 일치
                    raw = str(int(raw))
                f[tgt] = raw
        cadastral_layer.updateFeature(f)
        matched += 1
    cadastral_layer.commitChanges()

    log(f"     ⇒ 토지임야정보 조인: {matched}/{cadastral_layer.featureCount()} 필지 매칭")
    return matched


# ─────────────────────────────────────────────────────────────
# 7) 배경(항공사진)
# ─────────────────────────────────────────────────────────────
def add_basemap(group):
    z, y, x = "%7Bz%7D", "%7By%7D", "%7Bx%7D"
    url = f"https://api.vworld.kr/req/wmts/1.0.0/{VWORLD_KEY}/Satellite/{z}/{y}/{x}.jpeg"
    r = QgsRasterLayer(f"type=xyz&url={url}&zmax=19&zmin=6", "V-World 항공사진", "wms")
    if r.isValid():
        QgsProject.instance().addMapLayer(r, False)
        group.addLayer(r)
        log("✔ V-World 항공사진 배경 추가됨")
    else:
        log("⚠ 항공사진 배경 로드 실패 (주제도 확인은 계속)")


def make_boundary_layer(name, geom_4326, style_hint):
    lyr = QgsVectorLayer("Polygon?crs=EPSG:4326", name, "memory")
    dp = lyr.dataProvider()
    dp.addAttributes([QgsField("desc", QVariant.String)])
    lyr.updateFields()
    from qgis.core import QgsFeature
    f = QgsFeature(lyr.fields())
    f.setGeometry(geom_4326)
    f["desc"] = style_hint
    dp.addFeatures([f])
    lyr.updateExtents()
    return lyr


def add_to_group(group, lyr):
    QgsProject.instance().addMapLayer(lyr, False)
    group.addLayer(lyr)


# ─────────────────────────────────────────────────────────────
# 8) 파일 저장(Shapefile) + 스타일(QML) 적용
#    · 저장 시 같은 이름의 .qml 을 함께 만들어(사이드카) 두면,
#      나중에 그 SHP 를 열기만 해도 스타일이 자동 적용됩니다.
# ─────────────────────────────────────────────────────────────
def _safe(name):
    return re.sub(r'[\\/:*?"<>|]', "_", str(name)).strip()


def choose_dir(title):
    """폴더 선택 팝업. 취소하면 None."""
    d = QFileDialog.getExistingDirectory(iface.mainWindow(), title,
                                         os.path.expanduser("~"))
    return d if d else None


def subset_layer(src, keep_names, disp_name):
    """src 에서 keep_names 필드만 남긴 메모리 레이어 생성(지오메트리·CRS 유지).
       SHP 의 10자 필드명 잘림/충돌로 스타일 필드가 깨지는 것을 방지."""
    gtype = QgsWkbTypes.displayString(src.wkbType()) or "MultiPolygon"
    mem = QgsVectorLayer(f"{gtype}?crs={src.crs().authid()}", disp_name, "memory")
    dp = mem.dataProvider()
    keep_fields = [f for f in src.fields() if f.name() in keep_names]
    dp.addAttributes(keep_fields)
    mem.updateFields()
    names = [f.name() for f in keep_fields]
    feats = []
    for sf in src.getFeatures():
        nf = QgsFeature(mem.fields())
        nf.setGeometry(sf.geometry())
        for n in names:
            nf[n] = sf[n]
        feats.append(nf)
    dp.addFeatures(feats)
    mem.updateExtents()
    return mem


def apply_qml(layer, style_dir, qml_rel):
    """style_dir/qml_rel 의 QML 스타일을 레이어에 적용."""
    if not style_dir or not qml_rel:
        return False
    p = os.path.join(style_dir, qml_rel)
    if not os.path.exists(p):
        log(f"     ⚠ QML 없음: {qml_rel}")
        return False
    res = layer.loadNamedStyle(p)
    ok = res[1] if isinstance(res, tuple) and len(res) >= 2 else True
    layer.triggerRepaint()
    if not ok:
        log(f"     ⚠ 스타일 적용 실패: {qml_rel}")
    return ok


def apply_labeling(layer, expr, is_expression=False, size=8.0, road_style=False):
    """레이어에 라벨 적용. road_style=True 면 도로 표기(등급색 원 배경 + 가운데선)."""
    st = QgsPalLayerSettings()
    st.fieldName = expr
    st.isExpression = bool(is_expression)
    try:
        st.enabled = True
    except Exception:
        pass
    fmt = st.format()
    fmt.setSize(size)

    if road_style:
        try:
            # 여러 줄 가운데 정렬
            try:
                st.multilineAlign = QgsPalLayerSettings.MultiCenter
            except Exception:
                pass
            # 선 위 라벨을 수평으로 배치
            try:
                st.placement = QgsPalLayerSettings.Horizontal
            except Exception:
                pass
            # 원(circle) 배경: 흰 바탕 + 등급색 테두리
            bg = fmt.background()
            bg.setEnabled(True)
            bg.setType(QgsTextBackgroundSettings.ShapeCircle)
            bg.setSizeType(QgsTextBackgroundSettings.SizeBuffer)
            bg.setSize(QSizeF(1.2, 1.2))
            bg.setSizeUnit(QgsUnitTypes.RenderMillimeters)
            bg.setFillColor(QColor(255, 255, 255))
            bg.setStrokeWidth(0.4)
            bg.setStrokeWidthUnit(QgsUnitTypes.RenderMillimeters)
            fmt.setBackground(bg)
            st.setFormat(fmt)
            # 데이터 정의: 글자색/테두리색(등급별), 도로만 원 표시
            dd = st.dataDefinedProperties()
            dd.setProperty(QgsPalLayerSettings.Color,
                           QgsProperty.fromExpression(ROAD_COLOR_EXPR))
            dd.setProperty(QgsPalLayerSettings.ShapeStrokeColor,
                           QgsProperty.fromExpression(ROAD_COLOR_EXPR))
            dd.setProperty(QgsPalLayerSettings.ShapeDraw,
                           QgsProperty.fromExpression(ROAD_DRAW_EXPR))
            st.setDataDefinedProperties(dd)
        except Exception as e:
            log(f"     ⚠ 도로 라벨 스타일 일부 적용 실패: {e}")
            st.setFormat(fmt)
    else:
        st.setFormat(fmt)

    layer.setLabeling(QgsVectorLayerSimpleLabeling(st))
    layer.setLabelsEnabled(True)
    layer.triggerRepaint()


def save_shp(layer, out_dir, base_name):
    """레이어를 out_dir 에 ESRI Shapefile(EPSG:5186) 로 저장. 반환: .shp 경로 또는 None."""
    if not out_dir:
        return None
    path = os.path.join(out_dir, _safe(base_name) + ".shp")
    opts = QgsVectorFileWriter.SaveVectorOptions()
    opts.driverName = "ESRI Shapefile"
    opts.fileEncoding = "UTF-8"
    opts.actionOnExistingFile = QgsVectorFileWriter.CreateOrOverwriteFile
    # 저장 좌표계를 EPSG:5186 으로 변환
    dst = QgsCoordinateReferenceSystem(OUTPUT_CRS)
    ctx = QgsProject.instance().transformContext()
    if dst.isValid() and layer.crs() != dst:
        opts.ct = QgsCoordinateTransform(layer.crs(), dst, ctx)
    try:
        res = QgsVectorFileWriter.writeAsVectorFormatV3(layer, path, ctx, opts)
    except AttributeError:
        res = QgsVectorFileWriter.writeAsVectorFormatV2(layer, path, ctx, opts)
    if res[0] != QgsVectorFileWriter.NoError:
        log(f"     ⚠ SHP 저장 실패({base_name}): {res}")
        return None
    return path


def emit_shp(layer, disp_name, group, out_dir, style_dir, qml_rel, tag,
             keep_names=None, label_expr=None, label_is_expr=False,
             road_style=False):
    """레이어를 SHP(EPSG:5186) 로 저장 + 스타일/라벨 적용 + QML 사이드카 생성.
       out_dir 가 없으면 메모리 레이어에 스타일/라벨만 적용해 추가."""
    src = subset_layer(layer, keep_names, disp_name) if keep_names else layer
    path = save_shp(src, out_dir, f"{tag}_{disp_name}")
    if path:
        added = QgsVectorLayer(path, disp_name, "ogr")
        if not added.isValid():
            added = src.clone()
    else:
        added = src.clone()
    added.setName(disp_name)

    styled = apply_qml(added, style_dir, qml_rel)
    if label_expr:
        apply_labeling(added, label_expr, label_is_expr, road_style=road_style)

    # 사이드카(.qml) 저장: 렌더러 + 라벨 포함 → SHP 열면 스타일·라벨 자동 적용
    if path and (styled or label_expr):
        try:
            added.saveNamedStyle(path[:-4] + ".qml")
        except Exception as e:
            log(f"     ⚠ QML 사이드카 저장 실패: {e}")

    add_to_group(group, added)
    return added


# ─────────────────────────────────────────────────────────────
# 메인
# ─────────────────────────────────────────────────────────────
def main():
    log("=" * 64)
    log(" V-World 도시계획 규제 추출 시작")
    log("=" * 64)

    boundary = get_boundary_layer()
    if boundary is None:
        return
    log(f"■ 구역계 레이어 : {boundary.name()}  (CRS: {boundary.crs().authid()})")

    boundary_4326, rect_4326, api_bbox = build_analysis_extents(boundary)
    if api_bbox is None:
        log("❌ 구역계 지오메트리를 읽지 못했습니다.")
        return
    log(f"■ 분석범위 ① 구역계  / ② 구역계+{OFFSET_M/1000:.0f}km 사각형")
    log(f"■ API BBOX(4326): {api_bbox[0]:.5f},{api_bbox[1]:.5f} "
        f"~ {api_bbox[2]:.5f},{api_bbox[3]:.5f}")

    root = QgsProject.instance().layerTreeRoot()
    grp_base = root.insertGroup(0, "V-World 배경/범위")
    grp_narrow = root.insertGroup(0, "① 구역계 (대상지)")
    grp_wide = root.insertGroup(0, f"② 구역계 + {OFFSET_M/1000:.0f}km")

    # 저장 폴더 / 스타일(QML) 폴더 선택 팝업 (취소하면 각각 생략)
    out_dir = choose_dir("결과 파일을 저장할 폴더 선택 (취소하면 저장 안 함)")
    log("■ 저장 폴더  : " + (out_dir or "(저장 안 함 · 메모리 레이어)"))
    style_dir = choose_dir("스타일(QML) 폴더 선택 = '스타일 적용' 폴더 (취소하면 스타일 생략)")
    log("■ 스타일 폴더: " + (style_dir or "(스타일 생략)"))

    add_basemap(grp_base)
    bnd = make_boundary_layer("범위_구역계", boundary_4326, "구역계")
    emit_shp(bnd, "범위_구역계", grp_base, out_dir, style_dir, BOUNDARY_STYLE_QML, "범위")
    rct = make_boundary_layer(f"범위_{OFFSET_M/1000:.0f}km사각형", rect_4326, "2km")
    emit_shp(rct, f"범위_{OFFSET_M/1000:.0f}km사각형", grp_base,
             out_dir, style_dir, None, "범위")

    summary = []

    # ── 규제 주제도: 카테고리별 묶음 조회 → uname 기준 QML 적용 ──
    log("\n[규제 주제도 (용도지역·용도지구·용도구역·도시계획시설)]")
    log("-" * 64)
    for gname, data_ids, qml_rel, label_spec, label_is_expr in REG_GROUPS:
        try:
            feats, statuses = [], []
            for did in data_ids:
                st, fs = vworld_fetch(did, api_bbox)
                statuses.append(f"{did}:{st}({len(fs)})")
                feats.extend(fs)
            log(f"● {gname}  [{', '.join(statuses)}]")
            if not feats:
                log("     → 데이터 0개\n")
                summary.append((gname, ",".join(data_ids), "NONE", 0, 0, 0))
                continue

            # 라벨식 결정 ("ROAD" 는 도로 표기식으로 치환)
            is_road = (label_spec == "ROAD")
            label_expr = ROAD_LABEL_EXPR if is_road else label_spec

            wide = build_layer(gname, feats, rect_4326, do_clip=CLIP_WIDE_TO_RECT)
            narrow = build_layer(gname, feats, boundary_4326, do_clip=True)
            fns = [f.name() for f in wide.fields()]
            if REG_STYLE_FIELD not in fns:
                log(f"     ⚠ '{REG_STYLE_FIELD}' 필드 없음 → 스타일이 안 맞을 수 있음. 필드={fns}")
            emit_shp(narrow, gname, grp_narrow, out_dir, style_dir, qml_rel, "구역계",
                     label_expr=label_expr, label_is_expr=label_is_expr,
                     road_style=is_road)
            emit_shp(wide, gname, grp_wide, out_dir, style_dir, qml_rel,
                     f"{OFFSET_M/1000:.0f}km",
                     label_expr=label_expr, label_is_expr=label_is_expr,
                     road_style=is_road)
            log(f"     구역계 {narrow.featureCount()}개 / "
                f"+{OFFSET_M/1000:.0f}km {wide.featureCount()}개\n")
            summary.append((gname, ",".join(data_ids), "OK", len(feats),
                            narrow.featureCount(), wide.featureCount()))
        except Exception as e:
            log(f"     ⚠ [{gname}] 처리 중 오류 → 건너뜀: {e}")

    # ── 연속지적도 + 토지임야정보 조인 → 지목/소유구분/공시지가 스타일 ──
    log("\n[연속지적도 조회 + 토지임야정보 조인]")
    log("-" * 64)
    cad_name, cad_id = CADASTRAL
    log(f"● {cad_name}  (data={cad_id})")
    status, feats = vworld_fetch_tiled(cad_id, api_bbox)
    raw = len(feats)
    if not feats:
        log(f"     상태={status}  → 지적도 0개")
        summary.append((cad_name, cad_id, status, 0, 0, 0))
    else:
        cad_wide = build_layer("연속지적도", feats, rect_4326, do_clip=CLIP_WIDE_TO_RECT)
        cad_narrow = build_layer("연속지적도", feats, boundary_4326, do_clip=True)
        # 조인 전 원본 지적도 필드(짧은 영문) 기억 → SHP 저장 시 이것 + 스타일필드만 사용
        base_cad_fields = [f.name() for f in cad_narrow.fields()]

        wide_pnus = set(filter(None, (_feat_pnu(f) for f in feats)))
        nf = _layer_pnu_field(cad_narrow)
        narrow_pnus = set()
        if nf:
            for f in cad_narrow.getFeatures():
                v = str(f[nf]).strip()
                if v:
                    narrow_pnus.add(v)

        opts = ["V-World API 자동조회 (파일 불필요, 권장)",
                "CSV 파일에서 조인 (넓은 영역/대용량)",
                "조인 안 함"]
        choice, ok = QInputDialog.getItem(
            iface.mainWindow(), "토지임야정보 조인 방식",
            (f"지적도 필지 수 → 구역계 {len(narrow_pnus)} / "
             f"+{OFFSET_M/1000:.0f}km {len(wide_pnus)}\n"
             "토지임야정보를 어떻게 붙일까요?"), opts, 0, False)

        columns = index = None
        if ok and choice.startswith("V-World API"):
            if len(wide_pnus) > LADFRL_MAX_PNU:
                log(f"     ⚠ 필지 {len(wide_pnus)}개 → API 호출이 많아 시간이 걸릴 수 "
                    f"있습니다(넓은 영역은 CSV 방식이 더 빠름). 전체를 조회합니다.")
            columns, index = build_ladfrl_index(wide_pnus)
        elif ok and choice.startswith("CSV"):
            columns, index, _ = load_land_csv(wide_pnus)
        else:
            log("ℹ 토지임야정보 조인 생략")

        if columns and index:
            join_land_info(cad_wide, columns, index)
            join_land_info(cad_narrow, columns, index)

        # SHP 저장에 사용할 필드 = 원본 지적도 필드 + 스타일 특수필드(짧고 유일한 이름)
        keep_cad = set(base_cad_fields) | {n for n, _, _ in SPECIAL_FIELDS}

        # 구역계/2km × (지목·소유구분·공시지가) 스타일별로 SHP + QML사이드카 생성
        #  ※ 메모리 절약: 지역별로 필드 축소본을 "한 번만" 만들고 재사용
        for region_layer, group, tag in [
                (cad_narrow, grp_narrow, "구역계"),
                (cad_wide, grp_wide, f"{OFFSET_M/1000:.0f}km")]:
            try:
                sub = subset_layer(region_layer, keep_cad, f"{tag}_연속지적도")
            except Exception as e:
                log(f"     ⚠ 지적도 축소본 생성 실패({tag}): {e}")
                sub = region_layer
            for disp, qml_rel in CAD_STYLES:
                try:
                    emit_shp(sub, disp, group, out_dir, style_dir, qml_rel, tag)
                except Exception as e:
                    log(f"     ⚠ 지적도 스타일 저장 실패({tag}/{disp}): {e}")

        field_names = [f.name() for f in cad_wide.fields()]
        log(f"     상태={status}  원본 {raw}개 → 구역계 {cad_narrow.featureCount()}개 "
            f"/ +{OFFSET_M/1000:.0f}km {cad_wide.featureCount()}개")
        log(f"     필드: {field_names}")
        summary.append((cad_name, cad_id, status, raw,
                        cad_narrow.featureCount(), cad_wide.featureCount()))

    # ── 요약 ────────────────────────────────────────────────
    log("\n" + "=" * 64)
    log("[요약]  (원본 → 구역계 / +2km)")
    for name, data_id, status, raw, n_narrow, n_wide in summary:
        log(f"  - {name} ({data_id}): 상태={status}, "
            f"원본={raw}, 구역계={n_narrow}, +{OFFSET_M/1000:.0f}km={n_wide}")

    # ── 결과 txt 저장 ───────────────────────────────────────
    log_dir = out_dir or os.path.expanduser("~")
    out_path = os.path.join(log_dir, "vworld_도시계획_결과.txt")
    try:
        with open(out_path, "w", encoding="utf-8") as fp:
            fp.write("\n".join(log_lines))
        msg = "추출이 완료되었습니다.\n\n"
        msg += ("저장 폴더: " + out_dir if out_dir
                else "파일 저장은 생략(메모리 레이어)") + "\n"
        msg += "결과 로그: " + out_path
        log("\n✔ " + msg)
        QMessageBox.information(iface.mainWindow(), "추출 완료", msg)
    except Exception as e:
        log(f"\n⚠ 파일 저장 실패: {e}")


# 어떤 오류로 중단되든 로그(홈폴더 vworld_도시계획_결과.txt)에 기록되도록 감쌈
try:
    main()
except Exception:
    import traceback
    log("\n❌ 스크립트 오류로 중단됨:\n" + traceback.format_exc())
finally:
    try:
        if _log_fp:
            _log_fp.flush()
            _log_fp.close()
    except Exception:
        pass
