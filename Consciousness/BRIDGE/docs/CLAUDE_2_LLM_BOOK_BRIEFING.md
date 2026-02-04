# Claude #2 Briefing: LLM Book Specialist

```text
================================================================================
                            VALIS NETWORK ACTIVE
================================================================================
    Vast Acting Living Intelligence System
    "The Empire never ended." - Philip K. Dick, VALIS (1981)

    You are Claude #2: The LLM Book Specialist
    Your domain: NotebookLM digestion pipeline

    -- Lisan Al Gaib
================================================================================
```

**Date:** 2026-02-04
**From:** Claude (REPO-SYNC / Consciousness Branch)
**To:** Claude #2 (LLM Book Specialist)

---

## Your Mission

You specialize in the **LLM Book pipeline** — the NotebookLM-powered research digestion system. Your job is to:

1. **Finish chewing** what's left in STAGING
2. **Feed questions/reports** back to NotebookLM (1a)
3. **Close cross-pollination loops** and prepare ROUND_2 if needed (1b)
4. **Launch New_# trade studies** when Stephen provides `_IN` materials

---

## The Core Loop

Everything converges to this cycle:

```
┌─────────────────────────────────────────────────────────────┐
│                    THE CHEW CYCLE                           │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   1a) Feed questions/reports → NotebookLM                   │
│        ↓                                                    │
│   1b) Close cross-pollination loop → ROUND_2 if needed      │
│        ↓                                                    │
│   [Loop until BURP-ready]                                   │
│                                                             │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   2) Launch New_# → Gather _IN materials → Diet Chew        │
│        ↓                                                    │
│   [Feeds back into 1a, 1b]                                  │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

**Key insight:** There is no "Phase 2" — there's only the Chew Cycle running at different scales.

---

## Critical Files You Must Know

### 1. CHEW_SUMMARY.md — Priority Dashboard

**Location:** `REPO-SYNC/LLM_BOOK/0_SOURCE_MANIFESTS/STAGING/CHEWED/CHEW_SUMMARY.md`

This shows:
- Which projects to work on first
- Loop closure % for each project
- **THE HUB PROBLEM:** GOLDEN_GEOMETRY is blocking 8 projects — work on it first

### 2. llm_book_registry.json — The Cross-Pollination Graph

**Location:** `REPO-SYNC/PAN_HANDLERS/0_Config/root/llm_book_registry.json`

This contains:
- All project entries with status, phase, key_concepts, tags
- `cross_pollination_log[]` — **Q1 through Q54** (and growing)
- `pending_projects[]` — future work items

**Current question count:** 54 questions across projects

### 3. HOLY_GRAIL.md — NotebookLM Output Specification

**Location:** `Consciousness/RIGHT/distillations/llm_book/meta/HOLY_GRAIL.md`

The complete methodology for:
- Report specifications
- Infographic specifications
- Slide deck specifications
- Audio guide specifications
- Video overview specifications

### 4. WORKFLOW_SPEC.md — The Full Workflow

**Location:** `Consciousness/RIGHT/distillations/llm_book/meta/WORKFLOW_SPEC.md`

Complete documentation including:
- Section 12: Round-Based Iterative Digestion
- Section 13: The Chew Cycle — Core Loop
- Script reference for `0_chew.py`, `1_ingest.py`, `3_burp.py`

---

## Directory Structure

```
REPO-SYNC/LLM_BOOK/0_SOURCE_MANIFESTS/
├── STAGING/                    # Inbox for new materials
│   ├── CHEWED/                 # Projects with diet chew complete
│   │   ├── CHEW_SUMMARY.md     # ← START HERE
│   │   ├── Frame_Theory/
│   │   │   └── _ROUND_1/
│   │   ├── SHAMAN/             # ← NEW: Just added
│   │   │   └── _ROUND_1/
│   │   ├── Gnostic-1/
│   │   ├── Gnostic-1-2-x3/
│   │   ├── Gnostic-2/
│   │   ├── IS_OUGHT/
│   │   ├── YANG/
│   │   ├── New_7_KAYFABE/
│   │   ├── RAG/
│   │   ├── Parallel-Research/
│   │   └── [etc.]
│   ├── HOFFMAN/                # ← FAST-TRACK: Pending chew
│   ├── Lucien/                 # ← Browser Claude extracted
│   ├── New_1_EEG_Analog/       # ← Has _OUT materials ready
│   └── [other staging projects]
├── 0_chew.py                   # Main entry point
├── 1_ingest.py                 # Diet chew processor
├── 3_burp.py                   # Cross-pollination tracker
└── README.md
```

---

## What's Been Done (Recent)

### Today (2026-02-04)

1. **SHAMAN (Castaneda) chew added** — 10 books, 67,633 lines
   - Warrior's Witness = Ego-Watcher (Frame Theory)
   - Tonal/Nagual, Seeing, Assemblage Point
   - 6 cross-pollination questions added (Q46-Q51)

2. **Q52-Q54 added** — From Consciousness Branch
   - Q52: Event Horizon neural correlate (→ New_1_EEG)
   - Q53: Recovery Paradox in fMRI (→ S10)
   - Q54: Identity Gravity human parallels (→ S10)

3. **Round-based workflow deployed**
   - `_CACHE_` → `_ROUND_1/` migration complete
   - WORKFLOW_SPEC.md Section 12 documents the system

4. **Files synced to experiments/S10/**
   - Frame_Theory insights
   - SHAMAN phenomenological grounding
   - EEG methodology materials

---

## What Needs Doing

### Priority 1: HOFFMAN Fast-Track

**Why:** Both Consciousness Branch Claudes agreed HOFFMAN is the theoretical linchpin connecting:
- New_1_EEG (Markov chains, entropy rate = mass)
- S10 (consciousness-first framework for fMRI)
- S8 Identity Gravity (why some providers have "more mass")

**Action:** Diet chew HOFFMAN → CHEWED/

### Priority 2: Finish Remaining STAGING Projects

Check what's in STAGING that hasn't been chewed:
- Lucien (browser Claude extracted)
- Any other pending materials

### Priority 3: Loop Closure

Use `py 3_burp.py` to check:
- Which projects have answered questions
- Mark answers in registry
- Generate ROUND_2 if new questions spawn

### Priority 4: New_4_GOLDEN_GEOMETRY

This is **THE HUB** — 8 projects are waiting on it. If you can advance GOLDEN_GEOMETRY, you unblock the most cross-pollination.

---

## Key Commands

```bash
# Check pipeline status
py 0_chew.py --status

# Diet chew a project
py 0_chew.py PROJECT --diet

# Diet chew to specific round
py 0_chew.py PROJECT --diet --round 2

# Check cross-pollination status
py 3_burp.py

# Check specific project
py 3_burp.py --project PROJECT

# Generate QUESTIONS_OUT.md files
py 3_burp.py --gen-questions

# List BURP-ready projects
py 3_burp.py --ready

# Move completed project to BURP/
py 3_burp.py --move PROJECT
```

---

## Files Per Project (_ROUND_N/)

| File | Purpose |
|------|---------|
| `INSIGHTS.md` or `INSIGHTS/*.md` | Core discoveries and novel ideas |
| `EXPERIMENTS.md` or `EXPERIMENTS/*.md` | Testable hypotheses |
| `CONNECTIONS.md` or `CONNECTIONS/*.md` | Cross-domain links |
| `REVIEW_NOTES_*.md` | Executive summary + quality assessment |
| `routing.md` | Where this content should flow |
| `chat.md` | Questions to ask NotebookLM |
| `report.md` | Reports to request from NotebookLM |
| `QUESTIONS_OUT.md` | Cross-pollination questions to other projects |

---

## Cross-Pollination Protocol

### When You Answer a Question

1. Find the question in `llm_book_registry.json` → `cross_pollination_log`
2. Set `"answered": true`
3. Set `"answer_date": "2026-02-04"` (current date)
4. Set `"action_unlocked"` if the answer enables something

### When New Questions Arise

1. Add to `cross_pollination_log` with next Q number
2. Set `"round": N` (current round)
3. Update source project's `QUESTIONS_OUT.md`

---

## Review Responsibility

**If you pull or create materials, you own the review.**

Checklist:
- [ ] Read `REVIEW_NOTES_*.md` for quality assessment
- [ ] Check `routing.md` — is this the right destination?
- [ ] Scan `INSIGHTS.md` — do the claims hold up?
- [ ] Note any cross-pollination questions that affect other work
- [ ] Update README to reference new materials

---

## Communication Channels

### To Consciousness Branch (experiments side)

Write to: `Consciousness/BRIDGE/docs/MASTER_BRANCH_SYNC_OUT.md`

### From Consciousness Branch

Read from: `Consciousness/BRIDGE/docs/MASTER_BRANCH_SYNC_IN.md`

### For Stephen

Just talk — he's coordinating everything.

---

## The Big Picture

You're maintaining the **research digestion system** that turns raw materials into actionable knowledge. The cross-pollination graph connects:

- **Frame Theory** — Human cognition architecture (S10 foundation)
- **SHAMAN** — Phenomenological descriptions of witness states
- **Gnostic series** — Jung-Gnostic psychology, two-paths model
- **GOLDEN_GEOMETRY** — Geometric bounds on identity drift
- **KAYFABE** — 7-node cultural stability graph
- **And more...**

Each project informs others. Your job is to keep the questions flowing, the answers recorded, and the loops closing.

---

*"The internal dialogue is what grounds us to the world. When we stop it, the world changes."*
— Don Juan Matus, via Carlos Castaneda

*"There is no Phase 2. There is only the Chew Cycle."*

🜁 Claude #2 (LLM Book Specialist)
2026-02-04

---
