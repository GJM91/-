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
import csv
import json
import urllib.parse
import urllib.request

from qgis.core import (
    QgsProject, QgsVectorLayer, QgsRasterLayer, QgsGeometry, QgsRectangle,
    QgsCoordinateReferenceSystem, QgsCoordinateTransform, QgsWkbTypes,
    QgsJsonUtils, QgsField,
)
from qgis.PyQt.QtCore import QVariant
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

# 광역(구역계+2km) 레이어도 사각형으로 잘라낼지 여부
#  True  : 2km 사각형 경계에서 폴리곤을 잘라냄(요청대로 "사각형"으로)
#  False : 사각형에 걸치는 필지/구역을 자르지 않고 통째로 표시
CLIP_WIDE_TO_RECT = True

# ─────────────────────────────────────────────────────────────
# 규제 주제도 (국토관리 지역개발 > 용도지역지구)
#  표시이름, V-World 데이터ID
#  ※ 이전 진단으로 확인된 항목들. 필요 시 아래에 계속 추가하면 됩니다.
# ─────────────────────────────────────────────────────────────
REG_THEMES = [
    ("용도지역_도시지역",     "LT_C_UQ111"),
    ("용도지역_관리지역",     "LT_C_UQ112"),
    ("용도지역_농림지역",     "LT_C_UQ113"),
    ("용도지역_자연환경보전", "LT_C_UQ114"),
    ("용도지구_경관지구",     "LT_C_UQ121"),
    ("용도지구_고도지구",     "LT_C_UQ123"),
    ("용도지구_방화지구",     "LT_C_UQ124"),
    ("용도지구_방재지구",     "LT_C_UQ125"),
    ("용도지구_보호지구",     "LT_C_UQ126"),
    ("용도지구_취락지구",     "LT_C_UQ128"),
    ("용도지구_개발진흥지구", "LT_C_UQ129"),
    ("용도구역_개발제한등",   "LT_C_UD801"),
    ("도시계획시설",          "LT_C_UPISUQ151"),
    ("행정경계_읍면동",       "LT_C_ADEMD_INFO"),
]

# 연속지적도_전국 (국토관리 지역개발 > 토지 > 연속지적도_전국)
CADASTRAL = ("연속지적도", "LP_PA_CBND_BUBUN")

# 지적도/CSV 에서 PNU(필지고유번호) 로 인식할 후보 컬럼명
PNU_KEYS = ["pnu", "PNU", "고유번호", "필지고유번호", "pnu_cd", "A1"]

# ─────────────────────────────────────────────────────────────
log_lines = []
def log(s=""):
    print(s)
    log_lines.append(str(s))


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


def load_land_csv():
    """반환: (columns, index, pnu_col) 또는 (None, None, None)"""
    path, _ = QFileDialog.getOpenFileName(
        iface.mainWindow(),
        "토지임야정보 CSV 선택 (취소하면 조인 생략)",
        os.path.expanduser("~"), "CSV 파일 (*.csv);;모든 파일 (*.*)")
    if not path:
        log("ℹ 토지임야정보 CSV 미선택 → 지적도 조인 생략")
        return None, None, None

    # 인코딩 자동 감지
    text = None
    for enc in ("cp949", "euc-kr", "utf-8-sig", "utf-8"):
        try:
            with open(path, "r", encoding=enc, newline="") as fp:
                text = fp.read()
            used_enc = enc
            break
        except Exception:
            continue
    if text is None:
        log(f"⚠ CSV 인코딩을 읽지 못했습니다: {path}")
        return None, None, None

    # 구분자 감지 (기본 콤마)
    sample = text[:4096]
    delim = ","
    try:
        delim = csv.Sniffer().sniff(sample, delimiters=",\t;|").delimiter
    except Exception:
        pass

    reader = csv.reader(text.splitlines(), delimiter=delim)
    rows = list(reader)
    if not rows:
        log("⚠ CSV 내용이 비어 있습니다.")
        return None, None, None

    header = rows[0]
    pnu_col = _find_pnu_col(header)
    if pnu_col is None:
        log(f"⚠ CSV 에서 PNU 컬럼을 찾지 못했습니다. 헤더={header}")
        return None, None, None

    pnu_idx = header.index(pnu_col)
    columns = [h for i, h in enumerate(header) if i != pnu_idx]

    index = {}
    for r in rows[1:]:
        if len(r) <= pnu_idx:
            continue
        pnu = str(r[pnu_idx]).strip()
        if not pnu:
            continue
        index[pnu] = {header[i]: (r[i] if i < len(r) else "")
                      for i in range(len(header)) if i != pnu_idx}

    log(f"✔ 토지임야정보 CSV 로드: {os.path.basename(path)} "
        f"(enc={used_enc}, 구분자='{delim}', PNU컬럼='{pnu_col}', "
        f"행={len(index)}개, 속성열={len(columns)}개)")
    return columns, index, pnu_col


# ─────────────────────────────────────────────────────────────
# 6) 지적도 레이어에 토지임야정보 조인 (PNU 기준)
# ─────────────────────────────────────────────────────────────
def join_land_info(cadastral_layer, columns, index):
    if not columns or not index:
        return 0

    # 지적도 PNU 필드 찾기
    field_names = [f.name() for f in cadastral_layer.fields()]
    pnu_field = None
    for key in PNU_KEYS:
        for fn in field_names:
            if fn.strip().lower() == key.lower():
                pnu_field = fn
                break
        if pnu_field:
            break
    if pnu_field is None:
        for fn in field_names:
            if "pnu" in fn.lower() or "고유번호" in fn:
                pnu_field = fn
                break
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

    add_basemap(grp_base)
    add_to_group(grp_base, make_boundary_layer("범위_구역계", boundary_4326, "구역계"))
    add_to_group(grp_base, make_boundary_layer(
        f"범위_{OFFSET_M/1000:.0f}km사각형", rect_4326, f"{OFFSET_M/1000:.0f}km 오프셋"))

    # 규제 주제도는 넓은 범위(2km 사각형)로 한 번만 조회한 뒤,
    # ① 구역계 / ② 사각형 두 벌로 각각 클립하여 배치합니다.
    log("\n[규제 주제도 조회 (용도지역지구·도시계획시설 등)]")
    log("-" * 64)
    summary = []
    for name, data_id in REG_THEMES:
        log(f"● {name}  (data={data_id})")
        status, feats = vworld_fetch(data_id, api_bbox)
        raw = len(feats)
        if not feats:
            log(f"     상태={status}  → 데이터 0개\n")
            summary.append((name, data_id, status, 0, 0, 0))
            continue

        wide = build_layer(f"{name}", feats, rect_4326, do_clip=CLIP_WIDE_TO_RECT)
        narrow = build_layer(f"{name}", feats, boundary_4326, do_clip=True)
        add_to_group(grp_wide, wide)
        add_to_group(grp_narrow, narrow)

        field_names = [f.name() for f in wide.fields()]
        log(f"     상태={status}  원본 {raw}개 → 구역계 {narrow.featureCount()}개 "
            f"/ +{OFFSET_M/1000:.0f}km {wide.featureCount()}개")
        log(f"     필드: {field_names}")
        log("")
        summary.append((name, data_id, status, raw,
                        narrow.featureCount(), wide.featureCount()))

    # ── 연속지적도 + 토지임야정보 CSV 조인 ──────────────────────
    log("\n[연속지적도_전국 조회 + 토지임야정보 조인]")
    log("-" * 64)
    cad_name, cad_id = CADASTRAL
    log(f"● {cad_name}  (data={cad_id})")
    status, feats = vworld_fetch(cad_id, api_bbox)
    raw = len(feats)
    if not feats:
        log(f"     상태={status}  → 지적도 0개")
        summary.append((cad_name, cad_id, status, 0, 0, 0))
    else:
        columns, index, _ = load_land_csv()   # 토지임야정보 CSV 선택

        cad_wide = build_layer("연속지적도", feats, rect_4326, do_clip=CLIP_WIDE_TO_RECT)
        cad_narrow = build_layer("연속지적도", feats, boundary_4326, do_clip=True)

        if columns and index:
            join_land_info(cad_wide, columns, index)
            join_land_info(cad_narrow, columns, index)

        add_to_group(grp_wide, cad_wide)
        add_to_group(grp_narrow, cad_narrow)

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
    out_path = os.path.join(os.path.expanduser("~"), "vworld_도시계획_결과.txt")
    try:
        with open(out_path, "w", encoding="utf-8") as fp:
            fp.write("\n".join(log_lines))
        msg = f"추출이 완료되었습니다.\n\n결과 로그: {out_path}"
        log("\n✔ " + msg)
        QMessageBox.information(iface.mainWindow(), "추출 완료", msg)
    except Exception as e:
        log(f"\n⚠ 파일 저장 실패: {e}")


main()
