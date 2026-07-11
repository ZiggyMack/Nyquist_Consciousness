"""
MISSION CONTROL — Research decision board
==========================================
Single-glance: what's cooking, what needs doing, what's blocking.
Inspired by CFA Claude's mission control design.
"""

import streamlit as st
import json
from pathlib import Path
from datetime import datetime
from config import PATHS

import pandas as pd

REPO_ROOT = PATHS['repo_root']
CFA_DIR = REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "12_CFA"
RUNS_DIR = REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "0_results" / "runs" / "cfa_trinity"
MAPS_DIR = REPO_ROOT / "docs" / "maps"
CA_DIR = REPO_ROOT / "REPO-SYNC" / "LLM_BOOK" / "0_SOURCE_MANIFESTS" / "STAGING" / "New_9_Cognitive_Archaeology"
LLM_BOOK_DIR = REPO_ROOT / "REPO-SYNC" / "LLM_BOOK" / "0_SOURCE_MANIFESTS" / "STAGING"
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
                golden = 0
                control = 0
                for f in files:
                    try:
                        with open(f, encoding="utf-8") as fh:
                            d = json.load(fh)
                        cond = d.get("condition", "unknown")
                        if cond == "external":
                            golden += 1
                        elif cond == "control":
                            control += 1
                    except Exception:
                        pass
                categories[cat_dir.name] = {
                    "count": len(files),
                    "golden": golden,
                    "control": control,
                    "latest": datetime.fromtimestamp(latest).strftime("%Y-%m-%d"),
                }
    total = sum(v["count"] for v in categories.values())
    return categories, total


def get_sync_status():
    result = {}
    for status in ["pending", "running", "completed"]:
        path = CFA_DIR / "SYNC_OUT" / status
        deliveries = []
        if path.exists():
            deliveries = [f for f in path.iterdir()
                          if f.suffix in ('.md', '.yaml', '.yml') and f.name != '.gitkeep']
        raw_path = path / "raw_runs"
        jsons = 0
        if raw_path.exists():
            jsons = count_files(raw_path, "*.json")
        result[status] = {"summaries": len(deliveries), "jsons": jsons}
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


def priority_badge(level):
    colors = {
        "HIGH": ("#dc2626", "#fef2f2"),
        "MEDIUM": ("#d97706", "#fffbeb"),
        "LOW": ("#6b7280", "#f9fafb"),
        "DONE": ("#22c55e", "#f0fdf4"),
    }
    bg, _ = colors.get(level, ("#6b7280", "#f9fafb"))
    return f'<span style="background:{bg}; color:white; padding:2px 10px; border-radius:4px; font-size:0.8em; font-weight:bold;">{level}</span>'


def action_line(text):
    return f'*<span style="color:#2a9d8f;">→ {text}</span>*'


def render():
    st.markdown("## Mission Control")
    st.caption("Research decision board — what's cooking, what needs doing, what's blocking")

    # ==================== WHAT'S COOKING? ====================

    st.markdown("---")
    st.markdown("\U0001f50d\U0001f525 **WHAT'S COOKING?**")
    st.caption("New theoretical terrain opening up — what the deep digs unlocked and where the research is headed next")

    cook_col1, cook_col2 = st.columns(2)

    with cook_col1:
        with st.container(border=True):
            st.markdown("\U0001f4d0 **Discovery Simplex emerged from Curt**")
            st.markdown(
                "Four orthogonal discovery questions — not competing theories. "
                "Transformation (Noether), Constraint (Barandes), Composition (Curt), Generation (Dirac). "
                "Two corners confirmed, two predicted. This replaces the single backward/forward axis "
                "with a principled coordinate system for organizing all discovery architectures."
            )
            st.caption("New_10 Dig Site 010 · Q31–Q38 formal audit · CONFIRMED")

        with st.container(border=True):
            st.markdown("✅ **Phase 0C COMPLETE — empirical arm unblocked**")
            st.markdown(
                "All 4 Tier 1 extractors (DeepSeek V4 Pro, Claude, Gemma4 31B, Cogito 671B) "
                "passed the positive control on Framework-G v2.1 (66K chars). "
                "91–100% match with Phase 0A ground truth. Calibration triangle closed: "
                "pipeline detects (0C), doesn't hallucinate (0B), extractors agree (0A)."
            )
            st.caption("Phase 0C · 2026-07-10 · Gemma4 31B star performer")

    with cook_col2:
        with st.container(border=True):
            st.markdown("\U0001f517 **\"Don't privilege nodes\" — 5 projects converge**")
            st.markdown(
                "Barandes (pair-dependent laws), Curt (transition functions), CFA (crux interactions), "
                "ARMADA (calibration relationships), EOS (operator composition). All independently say: "
                "interesting structure lives BETWEEN components, not within them. "
                "This is the strongest cross-project principle confirmed so far."
            )
            st.caption("Convergence: Barandes + Curt + CFA + ARMADA + EOS")

        with st.container(border=True):
            st.markdown("\U0001f3db️ **Architecture F = a fourth discovery engine**")
            st.markdown(
                "Curt's \"every operation has a domain of validity\" produced a genuine new architecture: "
                "Composition Analysis. Unlike RCI (reads backward from outputs), Architecture F audits "
                "whether operations are LICENSED in new domains. It's the architecture that audits other "
                "architectures. Instances: Arrow, Efron, Abramsky-Brandenburger."
            )
            st.caption("New_10 · Architecture F · Candidate (Composition corner)")

    # ==================== LLM BOOK PIPELINE STATUS ====================

    st.markdown("---")
    st.markdown("\U0001f4da **LLM BOOK PIPELINE**")
    st.caption("Deep dig status — what's done, what's next, how it feeds New_9")

    pipe_col1, pipe_col2, pipe_col3 = st.columns(3)

    with pipe_col1:
        with st.container(border=True):
            st.markdown("**New_8** (Barandes/Adlam)")
            st.markdown("Round 1 ✔️ Round 2 ✔️")
            st.markdown(
                "Produced: 7 operators (OP-001–007), RCI architecture (confirmed), "
                "ISP↔Cognitive Archaeology mapping, Noether lens."
            )
            st.markdown("*Status: ✅ COMPLETE*")

    with pipe_col2:
        with st.container(border=True):
            st.markdown("**New_10** (Curt / TOE)")
            st.markdown("Round 1 ✔️ Audit ✔️")
            st.markdown(
                "Produced: Architecture F, Discovery Simplex, Relation Space, "
                "Category Theory hypothesis, 8 experiments staged, 13 connections."
            )
            st.markdown("*Status: ✅ COMPLETE*")

    with pipe_col3:
        with st.container(border=True):
            st.markdown("**Dig Site 003** (Dirac)")
            st.markdown("Q50 rank #1 — next in queue")
            st.markdown(
                "Tests: Generation corner of the simplex. Does forward-generative "
                "discovery exist as genuinely distinct from backward-reading (RCI)? "
                "Beauty as selection filter. Pre-articulate intimation."
            )
            st.markdown("*Status: ⏳ PLANNED*")

    # ==================== OPEN LOOPS ====================

    st.markdown("---")
    st.markdown("\U0001f512 **OPEN LOOPS**")
    st.caption("Known issues and pending decisions — remove entries as they're resolved")

    sync = get_sync_status()

    # Count by priority
    st.markdown("**0 high · 2 medium · 3 low**")

    # Phase 0C resolved (full width)
    with st.container(border=True):
        st.markdown(f'{priority_badge("DONE")} &nbsp; **CA Phase 0C — COMPLETE (2026-07-10)**',
                    unsafe_allow_html=True)
        st.markdown(
            "4 Tier 1 extractors passed positive control on Framework-G v2.1 (66K chars). "
            "91–100% match with Phase 0A ground truth. OP-004 and OP-008 recovered by 6/6 independent "
            "extractors — first GREEN promotion candidates (pending 2nd dig site). "
            "Empirical arm **UNBLOCKED**."
        )
        st.markdown(action_line(
            "Resolved — proceed to systematic excavation (Dig Site 003 Dirac)"
        ), unsafe_allow_html=True)

    med_col1, med_col2 = st.columns(2)

    with med_col1:
        with st.container(border=True):
            st.markdown(f'{priority_badge("MEDIUM")} &nbsp; **Dig Site 003 (Dirac) — next deep dig**',
                        unsafe_allow_html=True)
            st.markdown(
                "The Discovery Simplex predicts a Generation corner — forward-generative discovery "
                "as a genuinely distinct architecture. Dirac is the test case. If his process reduces to "
                "RCI applied differently, the simplex loses a corner. If it's genuinely new, Architecture B "
                "is confirmed."
            )
            st.markdown(action_line(
                "Prepare Dirac source material for NotebookLM, design Q1–Q22"
            ), unsafe_allow_html=True)

    with med_col2:
        with st.container(border=True):
            jsons_in_running = sync.get("running", {}).get("jsons", 0)
            st.markdown(f'{priority_badge("MEDIUM")} &nbsp; **SYNC_OUT housekeeping — {jsons_in_running} raw JSONs**',
                        unsafe_allow_html=True)
            st.markdown(
                f"**{jsons_in_running} raw JSONs** sitting in `SYNC_OUT/running/raw_runs/` across batch folders. "
                "CT-vs-PT and PT-vs-MdN deliveries graduated. Decide whether raw JSONs should be archived "
                "or remain for CFA Claude to pull."
            )
            st.markdown(action_line(
                "Graduate completed summaries to completed/, archive raw JSONs to .archive/"
            ), unsafe_allow_html=True)

    low_col1, low_col2, low_col3 = st.columns(3)

    with low_col1:
        with st.container(border=True):
            st.markdown(f'{priority_badge("LOW")} &nbsp; **PT YAML — vs_buddhism misplaced**',
                        unsafe_allow_html=True)
            st.markdown(
                "`PROCESS_THEOLOGY.yaml` has a `levers_by_matchup.vs_buddhism` block with Trinity score "
                "structure — misplaced during Buddhism batch. No runtime impact (coverage matrix ignores it). "
                "Structural debt only."
            )
            st.markdown(action_line(
                "Move block to trinity_scores_by_matchup when convenient"
            ), unsafe_allow_html=True)

    with low_col2:
        with st.container(border=True):
            st.markdown(f'{priority_badge("LOW")} &nbsp; **Buddhism 2×2 design incomplete**',
                        unsafe_allow_html=True)
            st.markdown(
                "Buddhism has 41 subject runs (b_vs_ct: 10, b_vs_mdn: 11, b_vs_pt: 10, b_vs_g: 10). "
                "Reverse-stance runs exist in other frameworks' folders but the full closed 2×2 design "
                "isn't formally documented."
            )
            st.markdown(action_line(
                "Awareness item — no action required now"
            ), unsafe_allow_html=True)

    with low_col3:
        with st.container(border=True):
            maps = get_map_freshness()
            stale_count = sum(1 for m in maps if m["status"] == "stale")
            st.markdown(f'{priority_badge("LOW")} &nbsp; **Map staleness — {stale_count} maps stale**',
                        unsafe_allow_html=True)
            st.markdown(
                "Foundation maps (Stackup, Philosophy, Identity Lattice) likely still accurate "
                "but unreviewed since Dec 2025. Validation Status and Testable Predictions most "
                "likely to have drifted."
            )
            st.markdown(action_line(
                "Batch review when bandwidth allows"
            ), unsafe_allow_html=True)

    # ==================== INVENTORY (collapsed) ====================

    st.markdown("---")

    with st.expander("\U0001f4ca **DATA INVENTORY** — runs, fleet, maps", expanded=False):

        # --- Trinity Runs ---
        st.markdown("#### Trinity Run Inventory")
        categories, total = get_run_inventory()
        worldview_cats = {"CT", "MdN", "G", "PT", "B"}
        golden_total = sum(v["golden"] for k, v in categories.items() if k in worldview_cats)
        control_total = sum(v["control"] for k, v in categories.items() if k in worldview_cats)
        calibration_total = total - golden_total - control_total

        m1, m2, m3 = st.columns(3)
        m1.metric("Golden Runs", f"{golden_total:,}")
        m2.metric("Control Runs", f"{control_total:,}")
        m3.metric("Calibration", f"{calibration_total:,}")
        st.caption(f"Total on disk: {total:,}")

        framework_labels = {
            "CT": "Classical Theism", "MdN": "Methodological Naturalism",
            "G": "Gnosticism", "PT": "Process Theology", "B": "Buddhism",
            "Framework_G": "Framework-G (calibration)", "pre_schema": "Pre-schema (legacy)",
        }
        rows = []
        for cat, info in categories.items():
            rows.append({
                "Framework": framework_labels.get(cat, cat),
                "Golden": info["golden"], "Control": info["control"],
                "Total": info["count"], "Latest": info["latest"],
            })
        if rows:
            st.dataframe(pd.DataFrame(rows), hide_index=True, use_container_width=True)

        # --- Fleet ---
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

        # --- SYNC ---
        st.markdown("#### SYNC Bridge (CFA ↔ Nyquist)")
        sync_cols = st.columns(3)
        status_icons = {"pending": "\U0001f4ec", "running": "\U0001f504", "completed": "✅"}
        for i, (status, data) in enumerate(sync.items()):
            with sync_cols[i]:
                label = f"{status_icons.get(status, '')} {status.title()}"
                detail = f"{data['summaries']} deliveries"
                if data["jsons"] > 0:
                    detail += f", {data['jsons']} raw JSONs"
                st.metric(label, detail)

        # --- Maps ---
        st.markdown("#### Map Freshness")
        if maps:
            current = sum(1 for m in maps if m["status"] == "current")
            recent = sum(1 for m in maps if m["status"] == "recent")
            stale = sum(1 for m in maps if m["status"] == "stale")

            mc1, mc2, mc3 = st.columns(3)
            mc1.metric("Current (< 7d)", current)
            mc2.metric("Recent (< 30d)", recent)
            mc3.metric("Stale (30d+)", stale)

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

        # --- Dig Sites ---
        st.markdown("#### Dig Site Status")
        dig_sites = [
            {"Site": "000", "Target": "Extractor Calibration", "Status": "✅ 0A/0B/0C Complete",
             "Result": "17 extractors, 4 tiers, 2 new ops, Gemma4 star"},
            {"Site": "001", "Target": "Adlam & Barandes", "Status": "✅ Complete",
             "Result": "7 operators (OP-001–007)"},
            {"Site": "002", "Target": "Barandes (solo)", "Status": "✅ Complete",
             "Result": "6 new ops (OP-010–015), RCI arch, 40 insights"},
            {"Site": "010", "Target": "Curt Jaimungal", "Status": "✅ Complete (R1+Audit)",
             "Result": "Arch F, Simplex, Relation Space"},
            {"Site": "003", "Target": "Dirac", "Status": "⏳ Planned (Q50 #1)",
             "Result": "Tests Generation corner"},
            {"Site": "004", "Target": "Wolfram", "Status": "Queued (Q50 #2)",
             "Result": "Computational architecture"},
            {"Site": "005", "Target": "Hermann", "Status": "Queued (Q50 #3)",
             "Result": "Philosophical auditing"},
        ]
        st.dataframe(pd.DataFrame(dig_sites), hide_index=True, use_container_width=True)

        # --- Museum stats ---
        st.markdown("#### Museum Status")
        mu_col1, mu_col2 = st.columns(2)
        with mu_col1:
            st.markdown("**Museum A (Operators)**")
            a1, a2, a3 = st.columns(3)
            a1.metric("Registered", "15")
            a2.metric("YELLOW / RED", "7 / 8")
            a3.metric("Held", "1")
        with mu_col2:
            st.markdown("**Museum B (Architectures)**")
            b1, b2, b3 = st.columns(3)
            b1.metric("Total", "6")
            b2.metric("Confirmed", "1 (RCI)")
            b3.metric("Candidates", "5")

        # --- Engine ---
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
    st.caption("*For CFA Claude: your counterpart dashboard lives at `CFA/views/mission_control.py`. "
               "This page reads live from the Nyquist repo filesystem.*")
