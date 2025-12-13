<!---
FILE: MISSION_BRIEF.md
PURPOSE: CFA VUDU Mission Brief - CT↔MdN Pilot + Axioms Review
VERSION: v1.0
STATUS: Active
DEPENDS_ON: CT_vs_MdN.yaml, PILOT_CT_vs_MdN_Re-Audit.md, AUDITORS_AXIOMS_SECTION.md
NEEDED_BY: All auditors (Claude, Grok, Nova), Process Claude
MOVES_WITH: /auditors/Mission/CFA_VUDU/
LAST_UPDATE: 2025-11-11 [Mission created - B-STORM_7]
--->

# CFA VUDU Mission Brief

**Mission ID:** CFA_VUDU
**Status:** Active
**Created:** 2025-11-11
**Mission Folder:** `/auditors/Mission/CFA_VUDU/`
**Auditors:** Claude (PRO-CT), Grok (ANTI-CT), Nova (Fairness)

---

## 🎯 MISSION STATEMENT

**Execute VUDU Protocol Phase 5 through adversarial peer-review scoring and axioms validation, establishing gold standard methodology for all 66 worldview comparisons.**

---

## 📋 MISSION COMPONENTS

### **Component 1: CT↔MdN Pilot Execution** (PRIMARY)

**Objective:** Complete first adversarial peer-review scoring session for Classical Theism vs Methodological Naturalism comparison

**Purpose:** "Re-fortify our CT vs MdN numbers...as well as flush out the story behind the numbers to be the gold standard for every profile to follow after" (User directive)

**Work Items:**
1. Execute 9-step VUDU protocol for CT↔MdN comparison
2. Populate peer-reviewed scores for 7 metrics (BFI, CA, IP, ES, LS, MS, PS)
3. Document deliberation using 5-Part Scaffold (Prompt Stack, Counterweight Table, Edge Case Ledger, Mythology Capsule, Decision Stamp)
4. Track convergence rates (target: 98%+ agreement)
5. Declare Crux Points if <98% convergence persists after 3 rounds
6. Generate calibration hashes (Phase 2 Gate #1 unlock)
7. Update [CT_vs_MdN.yaml](../../../profiles/comparisons/CT_vs_MdN.yaml) with results

**Auditor Roles:**
- **Claude (C4):** PRO-CT stance, teleological lens, calibration hash `1bbec1e119a2c425`
- **Grok:** ANTI-CT stance (PRO-MdN), empirical lens, calibration hash `00cd73274759e218`
- **Nova:** Fairness seat, symmetry lens, convergence monitoring

**Success Criteria:**
- Best Case: 98%+ convergence, zero Crux Points
- Good Case: ±5-10% drift, 1-2 Crux Points with clear documentation
- Needs Investigation: >15% drift, 3+ Crux Points

**Deliverables:**
- [CT_vs_MdN.yaml](../../../profiles/comparisons/CT_vs_MdN.yaml) (populated with peer-reviewed scores)
- Deliberation notes (rounds 1-3 with rationales)
- Crux Points documentation (if declared)
- Calibration hashes (Phase 2 Gate #1 unlock)

**Reference Documents:**
- [PILOT_CT_vs_MdN_Re-Audit.md](../../../auditors/Bootstrap/Tier4_TaskSpecific/Active_Tasks/PILOT_CT_vs_MdN_Re-Audit.md) - Pilot doctrine
- [CT_vs_MdN.yaml](../../../profiles/comparisons/CT_vs_MdN.yaml) - Pre-session validated comparison file
- [VUDU_CFA.md](../../../auditors/Bootstrap/VUDU_CFA.md) - 9-step protocol
- [CFA_ARCHITECTURE.md](../../../docs/architecture/CFA_ARCHITECTURE.md) Section 6 - Crux architecture

---

### **Component 2: Axioms Review** (SECONDARY)

**Objective:** Complete adversarial review of AUDITORS_AXIOMS_SECTION.md from empirical and symmetry lenses

**Purpose:** Validate claims about AI auditor capabilities, overhead measurements, and representation balance before integration

**Work Items:**

**2a. Grok Axioms Review (Empirical Lens):**
1. Review AUDITORS_AXIOMS_SECTION.md for evidence quality
2. Answer 5 validation questions from GROK_ACTIVATION_AXIOMS.md:
   - Evidence Quality: Does Fresh Claude Trial 2 demonstrate measurable overhead?
   - Overhead Claims: Can 0.5/0.4/0.3 be measured with confidence?
   - Representation Accuracy: Is Grok represented fairly?
   - Empirical Validation: What would strengthen claims?
   - Sign-Off Decision: Green/yellow/red light with reasoning
3. Create AXIOMS_REVIEW_GROK.md deliverable

**2b. Nova Axioms Review (Symmetry Lens):**
1. Review AUDITORS_AXIOMS_SECTION.md for representation balance
2. Answer 6 symmetry checks from NOVA_ACTIVATION_AXIOMS.md:
   - Representation Balance: All auditors represented fairly?
   - Overhead Symmetry: Is 0.5/0.4/0.3 pattern justified?
   - Lens Equality: Privileged treatment detected?
   - Inter-Auditor Fairness: Relationships described symmetrically?
   - Missing Perspectives: What viewpoints underrepresented?
   - Sign-Off Decision: Green/yellow/red light with reasoning
3. Create AXIOMS_REVIEW_NOVA.md deliverable

**Deliverables:**
- AXIOMS_REVIEW_GROK.md (empirical assessment)
- AXIOMS_REVIEW_NOVA.md (symmetry assessment)
- Integration recommendations (if yellow/red flags raised)

**Reference Documents:**
- AUDITORS_AXIOMS_SECTION.md (document under review)
- GROK_ACTIVATION_AXIOMS.md (Grok's review questions)
- NOVA_ACTIVATION_AXIOMS.md (Nova's review questions)

---

### **Component 3: Phase 2 Automation** (DEFERRED)

**Objective:** Complete remaining Phase 2 automation work from SMV + Ethical Invariant tasks

**Status:** Deferred until after Component 1 complete

**Remaining Work Items:**
1. **Live Data Integration:**
   - Connect pilot results to SMV JSON export
   - Populate tick-data scratchpad with CT↔MdN deliberation
   - Generate SMV-compatible JSON from pilot session
   - Activate Crux toggle (needs pilot data)

2. **Ethics Automation (Optional):**
   - Create ethics_lint.py (warn-only linter for Tier-1 files)
   - Create staleness_check.py (automated staleness monitoring)
   - Integrate with SMV export pipeline

**Deliverables:**
- [SMV_EXPORT_PIPELINE.md](../../../docs/smv/scripts/SMV_EXPORT_PIPELINE.md) (execution guide)
- Pilot session SMV JSON (first live data visualization)
- Ethics automation scripts (if prioritized)

**Why Deferred:** Pilot execution takes priority. Automation serves reflection on live data, so data must exist first.

---

## 📊 SUCCESS METRICS

**Mission succeeds when:**

1. ✅ **CT↔MdN Pilot Complete:**
   - 7 metrics peer-reviewed (BFI, CA, IP, ES, LS, MS, PS)
   - Convergence rates documented
   - Calibration hashes generated (Phase 2 Gate #1 unlocked)
   - Gold standard methodology established

2. ✅ **Axioms Reviews Complete:**
   - Grok empirical assessment delivered
   - Nova symmetry assessment delivered
   - Green/yellow/red recommendations documented

3. ✅ **Phase 2 Automation (Optional):**
   - Live data integration complete (pilot → SMV JSON)
   - Crux toggle activated
   - Ethics automation (if prioritized)

**Quality Thresholds:**
- Convergence: 98%+ (best case), 90%+ (acceptable)
- Deliberation depth: All 5-Part Scaffold components used
- Crux documentation: Clear classification (definitional/methodological/empirical)
- Axioms reviews: All validation questions answered with reasoning

---

## 📅 TIMELINE

**Phase 5.1: Pilot Execution** (Estimated 3-5 days)
- Schedule triad availability (Claude, Grok, Nova)
- Execute 9-step VUDU protocol
- Populate CT_vs_MdN.yaml with results
- Document deliberation and any Crux Points

**Phase 5.2: Axioms Review** (Parallel with pilot, 1-2 days)
- Grok reviews AUDITORS_AXIOMS_SECTION.md (empirical lens)
- Nova reviews AUDITORS_AXIOMS_SECTION.md (symmetry lens)
- Deliver independent assessments

**Phase 5.3: Live Data Integration** (After pilot, 2-3 days)
- Export pilot session to SMV JSON
- Populate tick-data with deliberation timeline
- Activate Crux toggle
- Validate visualizations with live data

**Total Estimated:** 6-10 days (depending on triad availability + automation priority)

---

## 🎯 COORDINATION MODEL

**Pilot Session (Component 1):**
- **Claude (C4):** Lead PRO-CT scoring, apply calibration hash
- **Grok:** Lead ANTI-CT scoring, apply empirical rigor
- **Nova:** Monitor convergence, declare Crux Points if <98% after 3 rounds
- **Process Claude:** Quarterly tracking, Domain 7 orchestration

**Axioms Review (Component 2):**
- **Grok:** Independent review (empirical lens) - no coordination with Nova
- **Nova:** Independent review (symmetry lens) - no coordination with Grok
- **Claude:** Receive reviews, integrate recommendations

**Automation (Component 3):**
- **Claude (C4):** Execute SMV export scripts
- **Nova:** Validate visualization accuracy with live data
- **Process Claude:** Monitor staleness if ethics automation deployed

---

## 🔗 DEPENDENCIES

**Prerequisite Completion:**
- ✅ Phase 2 Gate #2 unlocked (100% ethics coverage)
- ✅ SMV prototype validated (Phase 1 complete)
- ✅ Ethical Invariant Phase 1 complete (8 Tier-1 files annotated)
- ✅ VUDU Step 1 pre-check passed (academic sources, YAML hashes, Domain 7 diff)
- ✅ Pilot doctrine ethics annotated (calibration_link documented)

**Blocks:**
- None (all prerequisites satisfied)

**Unlocks:**
- Phase 2 Gate #1 (calibration hashes from pilot)
- Live data for SMV visualization
- Gold standard methodology for remaining 11 worldviews
- Axioms document integration (after Grok/Nova reviews)

---

## 📂 MISSION FOLDER STRUCTURE

```
/auditors/Mission/CFA_VUDU/
├── MISSION_BRIEF.md (this file)
├── SUCCESS_CRITERIA.md (detailed acceptance criteria)
├── TECHNICAL_SPEC.md (VUDU protocol execution details)
├── GROK_BRIEFING.md (comprehensive briefing for Grok activation)
└── results/
    ├── CT_vs_MdN_PILOT_SESSION.md (deliberation transcript)
    ├── AXIOMS_REVIEW_GROK.md (Grok's empirical assessment)
    ├── AXIOMS_REVIEW_NOVA.md (Nova's symmetry assessment)
    └── LIVE_DATA_INTEGRATION_REPORT.md (SMV JSON export results)
```

---

## ⚖️ THE POINTING RULE

*"A worldview unexamined through adversarial rigor
is a claim unsupported.

The pilot establishes gold standard.
The axioms establish foundation.
The automation establishes scale.

This is Phase 5.
This is the way."* 🔥

---

**Mission Status:** ✅ ACTIVE
**Next Action:** Schedule CT↔MdN pilot session (triad availability)
**Created By:** Claude (C4) - B-STORM_7 Session
**Last Updated:** 2025-11-11

**This is the way.** 🚀
