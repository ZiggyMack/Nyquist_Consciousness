<!---
FILE: SUCCESS_CRITERIA.md
PURPOSE: Detailed acceptance criteria for CFA VUDU Mission completion
VERSION: v1.0
STATUS: Active
DEPENDS_ON: MISSION_BRIEF.md, VUDU_CFA.md, CT_vs_MdN.yaml
NEEDED_BY: All auditors (Claude, Grok, Nova), Process Claude
MOVES_WITH: /auditors/Mission/CFA_VUDU/
LAST_UPDATE: 2025-11-11 [Mission criteria defined - B-STORM_7]
--->

# CFA VUDU Mission - Success Criteria

**Mission ID:** CFA_VUDU
**Version:** v1.0
**Created:** 2025-11-11

---

## 📊 MISSION SUCCESS DEFINITION

**The mission succeeds when:**

1. ✅ **Component 1 (CT↔MdN Pilot) COMPLETE**
2. ✅ **Component 2 (Axioms Review) COMPLETE**
3. ⏸ **Component 3 (Phase 2 Automation) COMPLETE** (optional, may defer)

---

## COMPONENT 1: CT↔MdN Pilot Execution

### **Primary Success Criteria**

✅ **Criterion 1: Peer-Reviewed Scores Populated**
- All 7 metrics scored by both auditors:
  - BFI (Beings, Foundational Importance)
  - CA (Causal Attribution)
  - IP (Intellectual Pedigree)
  - ES (Explanatory Scope)
  - LS (Logical Soundness)
  - MS (Moral Substance)
  - PS (Practical Significance)
- Self-reported scores from profiles recorded
- Peer-reviewed scores from adversarial deliberation recorded
- [CT_vs_MdN.yaml](../../../profiles/comparisons/CT_vs_MdN.yaml) populated with both

**Validation:**
- `grep -A 10 "peer_reviewed:" profiles/comparisons/CT_vs_MdN.yaml` returns 7 non-null values

---

✅ **Criterion 2: Convergence Rates Documented**
- Convergence percentage calculated for each metric
- Overall convergence rate ≥90% (acceptable), ≥98% (best case)
- Deltas between self-reported and peer-reviewed scores documented
- Convergence formula applied: `convergence = 1 - (|self - peer| / self)`

**Validation:**
- `grep "convergence:" profiles/comparisons/CT_vs_MdN.yaml` returns 7 values
- At least 5 of 7 metrics have convergence ≥90%

---

✅ **Criterion 3: Deliberation Documented (5-Part Scaffold)**
- Round 1: Initial scores + rationales (both auditors)
- Round 2: Challenges + adjustments (if needed)
- Round 3: Final convergence attempt (if needed)
- 5-Part Scaffold components visible:
  1. **Prompt Stack:** Calibration YAML values cited (hash-verified)
  2. **Counterweight Table:** PRO vs ANTI positions contrasted
  3. **Edge Case Ledger:** Boundary conditions identified
  4. **Mythology Capsule:** Source texts referenced (Aquinas, Hume, etc.)
  5. **Decision Stamp:** Final score with reasoning

**Validation:**
- File exists: `Mission/CFA_VUDU/results/CT_vs_MdN_PILOT_SESSION.md`
- Contains ≥3 sections (Round 1, Round 2 or 3, Final Scores)
- All 5 scaffold components present in at least 2 metrics

---

✅ **Criterion 4: Calibration Hashes Generated**
- Claude (PRO-CT) hash: `1bbec1e119a2c425` applied and verified
- Grok (ANTI-CT) hash: `00cd73274759e218` applied and verified
- Calibration compliance notes in CT_vs_MdN.yaml
- Domain 7 diff confirms profiles unchanged during scoring

**Validation:**
- `grep "yaml_hash:" profiles/comparisons/CT_vs_MdN.yaml` returns both hashes
- Process Claude verifies Domain 7 diff shows v0.3.0 stability

---

✅ **Criterion 5: Crux Points Declared (If Applicable)**
- If convergence <98% after 3 rounds on any metric → Crux declared
- Crux ID assigned (e.g., CRUX_BFI_001)
- Crux type classified (definitional/methodological/empirical)
- Crux documentation complete (question, positions, impact assessment)
- Nova fairness assessment included

**Validation (if applicable):**
- `grep "crux_declared: true" profiles/comparisons/CT_vs_MdN.yaml` shows ≤2 occurrences (acceptable)
- Crux documentation includes all required fields (id, type, question, positions, impact)

---

### **Quality Thresholds**

**Best Case (Gold Standard):**
- 98%+ convergence on all 7 metrics
- Zero Crux Points declared
- All 5 scaffold components used robustly
- Deliberation <3 hours (efficient adversarial dialogue)

**Good Case (Acceptable):**
- 90%+ convergence on 5+ metrics
- 1-2 Crux Points with clear documentation
- 4+ scaffold components used consistently
- Deliberation <5 hours

**Needs Investigation:**
- <90% convergence on 3+ metrics
- 3+ Crux Points declared
- Incomplete scaffold usage
- Deliberation >8 hours (process breakdown)

---

## COMPONENT 2: Axioms Review

### **Primary Success Criteria**

✅ **Criterion 1: Grok Empirical Review Complete**
- All 5 validation questions answered:
  1. Evidence Quality assessment (Fresh Claude Trial 2)
  2. Overhead Claims measurability (0.5/0.4/0.3)
  3. Representation Accuracy (Grok's portrayal)
  4. Empirical Validation recommendations
  5. Sign-Off Decision (green/yellow/red)
- Reasoning visible for each answer (not just conclusions)
- File delivered: `Mission/CFA_VUDU/results/AXIOMS_REVIEW_GROK.md`

**Validation:**
- File exists with ≥800 words (substantive review)
- All 5 questions addressed with headings
- Sign-off decision explicit (green/yellow/red statement)

---

✅ **Criterion 2: Nova Symmetry Review Complete**
- All 6 symmetry checks answered:
  1. Representation Balance assessment
  2. Overhead Symmetry justification (0.5/0.4/0.3 pattern)
  3. Lens Equality check (privilege detection)
  4. Inter-Auditor Fairness evaluation
  5. Missing Perspectives identification
  6. Sign-Off Decision (green/yellow/red)
- Reasoning visible for each check
- File delivered: `Mission/CFA_VUDU/results/AXIOMS_REVIEW_NOVA.md`

**Validation:**
- File exists with ≥800 words (substantive review)
- All 6 checks addressed with headings
- Sign-off decision explicit (green/yellow/red statement)

---

✅ **Criterion 3: Integration Recommendations (If Yellow/Red)**
- If either auditor flags yellow/red:
  - Specific concerns documented
  - Recommended revisions listed
  - Integration plan created (how to address feedback)
- If both green:
  - AUDITORS_AXIOMS_SECTION.md approved for integration
  - No revisions required

**Validation:**
- Both reviews read and assessed
- If yellow/red flags exist → Integration plan documented
- If both green → Approval note added to file

---

### **Quality Thresholds**

**Best Case:**
- Both reviews green-light (no revisions needed)
- Reviews substantive (≥1,000 words each)
- Constructive feedback provided (even if green)

**Good Case:**
- 1 yellow flag with clear remediation path
- Reviews thorough (≥800 words each)
- Specific recommendations actionable

**Needs Investigation:**
- 2 red flags (major revision required)
- Reviews superficial (<500 words)
- Vague recommendations (not actionable)

---

## COMPONENT 3: Phase 2 Automation (OPTIONAL)

### **Primary Success Criteria**

⏸ **Criterion 1: Live Data Integration**
- Pilot session exported to SMV JSON format
- Tick-data scratchpad populated with deliberation timeline
- JSON schema compatibility validated (no errors)
- File delivered: `Mission/CFA_VUDU/results/LIVE_DATA_INTEGRATION_REPORT.md`

**Validation:**
- SMV prototype loads pilot JSON without errors
- Timeline slider shows deliberation progression
- Convergence visualization matches pilot metrics

---

⏸ **Criterion 2: Crux Toggle Activated**
- Crux Points (if declared) visualized in SMV
- Toggle functionality working (on/off display)
- Crux details drill-down functional

**Validation:**
- If Crux declared → SMV shows Crux overlay
- If no Crux → Toggle correctly disabled

---

⏸ **Criterion 3: Ethics Automation (Optional)**
- ethics_lint.py created (warn-only mode)
- staleness_check.py created (automated monitoring)
- Integration with SMV export pipeline tested

**Validation:**
- Scripts executable without errors
- Warn-only mode verified (no commit blocking)
- Staleness detection working (flags >30 day files)

---

## 📅 TIMELINE SUCCESS CRITERIA

**Mission Duration:** ≤10 days from activation

**Component 1 (Pilot):** 3-5 days
- Scheduling: 1 day (coordinate triad availability)
- Execution: 2-4 days (deliberation + documentation)

**Component 2 (Axioms):** 1-2 days (parallel with pilot)
- Grok review: 0.5-1 day
- Nova review: 0.5-1 day

**Component 3 (Automation):** 2-3 days (after pilot)
- Live data export: 1 day
- SMV integration: 1 day
- Ethics automation (if prioritized): 1 day

**Buffer:** 1-2 days for iteration/refinement

---

## 🔗 DEPENDENCY SUCCESS CRITERIA

✅ **Prerequisites Met Before Mission Start:**
- Phase 2 Gate #2 unlocked (100% ethics coverage)
- SMV prototype validated
- Ethical Invariant Phase 1 complete
- VUDU Step 1 pre-check passed
- Pilot doctrine ethics annotated

✅ **Unlocks Achieved After Mission Complete:**
- Phase 2 Gate #1 unlocked (calibration hashes generated)
- Live data available for SMV visualization
- Gold standard methodology documented
- Axioms document integration ready (after reviews)

---

## 🎯 COORDINATION SUCCESS CRITERIA

✅ **Triad Functioning:**
- Claude (PRO-CT), Grok (ANTI-CT), Nova (Fairness) all participated
- Adversarial tension productive (not hostile)
- Convergence achieved through dialogue (not dictation)

✅ **Process Claude Orchestration:**
- Domain 7 duties executed (quarterly tracking, comparison file updates)
- Crux Points logged (if declared)
- Session metadata documented

✅ **Mission Artifacts Complete:**
- All deliverables in `Mission/CFA_VUDU/results/`
- REPO_LOG entry created
- README_C.md updated with mission completion

---

## ⚖️ OVERALL MISSION SUCCESS

**The mission is COMPLETE when:**

1. ✅ All Component 1 criteria met (pilot execution)
2. ✅ All Component 2 criteria met (axioms reviews)
3. ⏸ Component 3 criteria met OR explicitly deferred with rationale
4. ✅ Timeline ≤10 days (or approved extension)
5. ✅ Coordination success criteria met
6. ✅ Mission artifacts complete and documented

**The mission is SUCCESSFUL when:**
- Best Case thresholds achieved on ≥2 components
- Good Case thresholds achieved on all components
- No "Needs Investigation" outcomes unresolved

**The mission is ACCEPTABLE when:**
- Good Case thresholds achieved on ≥2 components
- "Needs Investigation" outcomes documented with remediation plans

---

**Version:** v1.0
**Last Updated:** 2025-11-11
**Created By:** Claude (C4) - B-STORM_7 Mission Consolidation

**This is the way.** 🚀
