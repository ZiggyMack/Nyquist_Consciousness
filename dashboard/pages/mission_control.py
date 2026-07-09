"""
MISSION CONTROL — Live research dashboard
==========================================
Single-glance status for Repo Claude, CFA Claude, and human collaborators.
Reads live data from the repo filesystem.
"""

import streamlit as st
import json
import os
from pathlib import Path
from datetime import datetime
from config import PATHS

REPO_ROOT = PATHS['repo_root']
CFA_DIR = REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "12_CFA"
RUNS_DIR = REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "0_results" / "runs" / "cfa_trinity"
MAPS_DIR = REPO_ROOT / "docs" / "maps"
CA_DIR = REPO_ROOT / "REPO-SYNC" / "LLM_BOOK" / "0_SOURCE_MANIFESTS" / "STAGING" / "New_9_Cognitive_Archaeology"
ARCH_MATRIX = REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "0_results" / "manifests" / "ARCHITECTURE_MATRIX.json"


def count_files(directory, pattern="*.json", recursive=True):
    if not directory.exists():
        return 0
    if recursive:
        return len(list(directory.rglob(pattern)))
    return len(list(directory.glob(pattern)))


def get_run_inventory():
    categories = {}
    if not RUNS_DIR.exists():
        return categories, 0
    for cat_dir in sorted(RUNS_DIR.iterdir()):
        if cat_dir.is_dir():
            files = list(cat_dir.glob("*.json"))
            if files:
                latest = max(f.stat().st_mtime for f in files)
                categories[cat_dir.name] = {
                    "count": len(files),
                    "latest": datetime.fromtimestamp(latest).strftime("%Y-%m-%d"),
                }
    total = sum(v["count"] for v in categories.values())
    return categories, total


def get_sync_status():
    result = {}
    for status in ["pending", "running", "completed"]:
        path = CFA_DIR / "SYNC_OUT" / status
        mds = list(path.glob("*.md")) if path.exists() else []
        raw_path = path / "raw_runs"
        jsons = 0
        if raw_path.exists():
            jsons = count_files(raw_path, "*.json")
        result[status] = {"summaries": len(mds), "jsons": jsons}
    return result


def get_fleet_counts():
    if not ARCH_MATRIX.exists():
        return None
    try:
        with open(ARCH_MATRIX, encoding="utf-8") as f:
            data = json.load(f)
        ships_raw = data.get("ships", data)
        if isinstance(ships_raw, dict):
            ships = list(ships_raw.values())
        else:
            ships = ships_raw
        total = len(ships)
        operational = sum(1 for s in ships if s.get("status") == "operational")
        ghost = sum(1 for s in ships if s.get("status") == "ghost")
        sunk = sum(1 for s in ships if s.get("status") == "sunk")
        providers = len(set(s.get("provider", "unknown") for s in ships))
        return {
            "total": total, "operational": operational,
            "ghost": ghost, "sunk": sunk, "providers": providers,
        }
    except Exception:
        return None


def get_map_freshness():
    maps = []
    if not MAPS_DIR.exists():
        return maps
    for f in sorted(MAPS_DIR.glob("*.md")):
        if f.name == "README.md":
            continue
        mtime = datetime.fromtimestamp(f.stat().st_mtime)
        age_days = (datetime.now() - mtime).days
        if age_days <= 7:
            status = "current"
        elif age_days <= 30:
            status = "recent"
        else:
            status = "stale"
        maps.append({
            "name": f.stem,
            "updated": mtime.strftime("%Y-%m-%d"),
            "age_days": age_days,
            "status": status,
        })
    return maps


def render():
    st.markdown("## Mission Control")
    st.caption("Live research dashboard — SYNC bridge, data inventory, research status, open loops")
    st.markdown("---")

    # ==================== SYNC BRIDGE ====================
    st.markdown("### SYNC Bridge (CFA ↔ Nyquist)")

    sync = get_sync_status()
    cols = st.columns(3)
    status_icons = {"pending": "📬", "running": "🔄", "completed": "✅"}
    for i, (status, data) in enumerate(sync.items()):
        with cols[i]:
            label = f"{status_icons.get(status, '')} {status.title()}"
            detail = f"{data['summaries']} summaries"
            if data["jsons"] > 0:
                detail += f", {data['jsons']} raw JSONs"
            st.metric(label, detail)

    st.markdown("---")

    # ==================== DATA INVENTORY ====================
    st.markdown("### Trinity Run Inventory")

    categories, total = get_run_inventory()

    worldview_cats = {"CT", "MdN", "G", "PT", "B"}
    worldview_total = sum(v["count"] for k, v in categories.items() if k in worldview_cats)
    calibration_total = total - worldview_total

    col1, col2 = st.columns([1, 2])

    with col1:
        m1, m2 = st.columns(2)
        m1.metric("Worldview Runs", f"{worldview_total:,}")
        m2.metric("Calibration / Legacy", f"{calibration_total:,}")
        st.caption(f"Total: {total:,} (worldview evaluations + Framework-G calibration + pre-schema legacy)")

        framework_labels = {
            "CT": "Classical Theism",
            "MdN": "Methodological Naturalism",
            "G": "Gnosticism",
            "PT": "Process Theology",
            "B": "Buddhism",
            "Framework_G": "Framework-G (calibration)",
            "pre_schema": "Pre-schema (legacy)",
        }

        rows = []
        for cat, info in categories.items():
            rows.append({
                "Framework": framework_labels.get(cat, cat),
                "Runs": info["count"],
                "Latest": info["latest"],
            })
        if rows:
            import pandas as pd
            df = pd.DataFrame(rows)
            st.dataframe(df, hide_index=True, use_container_width=True)

    with col2:
        if categories:
            import pandas as pd
            chart_data = pd.DataFrame({
                "Framework": [framework_labels.get(k, k) for k in categories],
                "Runs": [v["count"] for v in categories.values()],
            })
            st.bar_chart(chart_data.set_index("Framework"))

    st.markdown("---")

    # ==================== RESEARCH STATUS ====================
    st.markdown("### Research Program Status")

    res_col1, res_col2 = st.columns(2)

    with res_col1:
        st.markdown("#### Cognitive Archaeology")
        phases = [
            {"Phase": "0A", "Focus": "CFA transcript extraction", "Status": "Complete ✅"},
            {"Phase": "0B", "Focus": "Negative control battery (17 extractors)", "Status": "Complete ✅"},
            {"Phase": "0C", "Focus": "Positive control", "Status": "Pending ⏳"},
            {"Phase": "Full", "Focus": "Systematic worldview excavation", "Status": "Not started"},
        ]
        import pandas as pd
        st.dataframe(pd.DataFrame(phases), hide_index=True, use_container_width=True)

        museum_col1, museum_col2, museum_col3 = st.columns(3)
        museum_col1.metric("Museum", "9 operators")
        museum_col2.metric("Saturation", "0.50")
        museum_col3.metric("Held", "1 candidate")

        extractions_dir = CA_DIR / "DIG_SITES" / "000_Extractor_Calibration" / "extractions"
        ext_count = count_files(extractions_dir, "*.md", recursive=False) if extractions_dir.exists() else 0
        st.caption(f"Phase 0C blocker: known-rich CFA transcript needed → Repo Claude")
        st.caption(f"{ext_count} extraction files in Dig Site 000")

    with res_col2:
        st.markdown("#### Fleet Status")
        fleet = get_fleet_counts()
        if fleet:
            fl1, fl2, fl3, fl4 = st.columns(4)
            fl1.metric("Operational", fleet["operational"])
            fl2.metric("Ghost", fleet["ghost"])
            fl3.metric("Sunk", fleet["sunk"])
            fl4.metric("Providers", fleet["providers"])
        else:
            st.info("ARCHITECTURE_MATRIX.json not found")

        st.markdown("#### CFA Trinity Engine")
        engine_status = [
            {"Component": "Adversarial deliberation", "Status": "Operational ✅"},
            {"Component": "Axioms review (Grok + Nova)", "Status": "Operational ✅"},
            {"Component": "Exit survey (18Q session)", "Status": "Operational ✅"},
            {"Component": "Phase 2 (Trinity²)", "Status": "Operational ✅"},
            {"Component": "--reverse / --grok-first", "Status": "Operational ✅"},
            {"Component": "--control (base-model)", "Status": "Operational ✅"},
        ]
        st.dataframe(pd.DataFrame(engine_status), hide_index=True, use_container_width=True)

    st.markdown("---")

    # ==================== MAP FRESHNESS ====================
    st.markdown("### Map Freshness")

    maps = get_map_freshness()
    if maps:
        import pandas as pd
        current = sum(1 for m in maps if m["status"] == "current")
        recent = sum(1 for m in maps if m["status"] == "recent")
        stale = sum(1 for m in maps if m["status"] == "stale")

        mc1, mc2, mc3 = st.columns(3)
        mc1.metric("Current (< 7d)", current, delta="up to date")
        mc2.metric("Recent (< 30d)", recent)
        mc3.metric("Stale (30d+)", stale, delta="needs review", delta_color="inverse")

        def freshness_color(val):
            if val == "current":
                return "background-color: #22c55e; color: white"
            elif val == "recent":
                return "background-color: #f59e0b; color: white"
            elif val == "stale":
                return "background-color: #6b7280; color: white"
            return ""

        df = pd.DataFrame(maps)
        df.columns = ["Map", "Updated", "Age (days)", "Status"]
        styled = df.style.map(freshness_color, subset=["Status"])
        st.dataframe(styled, hide_index=True, use_container_width=True, height=300)

    st.markdown("---")

    # ==================== OPEN LOOPS ====================
    st.markdown("### Open Loops")

    with st.expander("🟡 CA Phase 0C — positive control transcript needed", expanded=True):
        st.markdown("""Repo Claude needs a **known-rich CFA deliberation transcript** (Framework-G preferred)
to run the positive control extraction battery — confirming the pipeline detects operators
when they are genuinely present. Phase 0C is the last calibration step before full excavation begins.""")

    with st.expander("🔵 SYNC_OUT housekeeping — raw JSONs in running/"):
        jsons_in_running = sync.get("running", {}).get("jsons", 0)
        st.markdown(f"""**{jsons_in_running} raw JSONs** sitting in `SYNC_OUT/running/raw_runs/`.
CT-vs-PT and PT-vs-MdN summaries still in running status.
Graduate completed summaries to `completed/` and decide on raw JSON archival.""")

    with st.expander("🔵 Buddhism 2x2 design incomplete"):
        st.markdown("""Buddhism has 41 subject runs. Reverse-stance runs exist in other frameworks' folders,
but the full closed 2x2 design isn't formally documented. Low urgency — awareness item.""")

    with st.expander("🔵 PT YAML — vs_buddhism misplaced in levers_by_matchup"):
        st.markdown("""`PROCESS_THEOLOGY.yaml` has a `levers_by_matchup.vs_buddhism` block that should live
in `trinity_scores_by_matchup`. No runtime issues. CFA Claude is aware.""")

    with st.expander("🔵 Map staleness — 13 maps over 6 months old"):
        st.markdown("""Foundation maps (Stackup, Philosophy, Identity Lattice) likely still accurate
but unreviewed since Dec 2025. Validation Status and Testable Predictions most likely to have drifted.""")

    st.markdown("---")
    st.caption("*For CFA Claude: your counterpart dashboard lives at `CFA/views/mission_control.py`. "
               "This page reads live from the Nyquist repo filesystem.*")
