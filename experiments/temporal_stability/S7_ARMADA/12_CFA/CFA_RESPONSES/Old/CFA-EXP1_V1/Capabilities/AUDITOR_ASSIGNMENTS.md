# Auditor Assignments - Worldview Scoring Stances

**Purpose:** Dynamic mapping of auditors to PRO/ANTI stances for worldview scoring
**Version:** 1.0.0
**Status:** Active
**Last Updated:** 2025-11-10

<!---
FILE: AUDITOR_ASSIGNMENTS.md
PURPOSE: Maps auditors to PRO/ANTI stances for each worldview, enabling adversarial auditing with natural lens alignment
VERSION: 1.0.0
STATUS: Active
DEPENDS_ON: profiles/worldviews/*.md (Steel-Manning Guide sections), auditors/AUDITORS_AXIOMS_SECTION.md
NEEDED_BY: Auditor scoring sessions, worldview comparative analysis, steel-manning methodology
MOVES_WITH: /auditors/
LAST_UPDATE: 2025-11-10 [B-STORM_4: Created as part of unified architecture - worldview-agnostic stance guidance]
--->

---

## Overview

**Core Principle:** Play auditors to their natural lens strengths.

Each auditor has a distinct cognitive lens (teleological, empirical, symmetry) that naturally aligns with certain worldviews and challenges others. Rather than forcing auditors into unnatural stances, we assign them to positions where their lens provides authentic advocacy or honest critique.

**Architecture (B-STORM_4):**
- Worldview profiles contain worldview-agnostic PRO and ANTI stance guidance
- This file maps which auditor takes which stance for each worldview
- Auditors read their assigned stance section from the worldview profile
- Scoring calibration (bias adjustment values) embedded in profile YAML blocks

**Target:** 98% convergence after adversarial checking

---

## The Three Auditors

### Claude (Anthropic) - Teleological Lens

**Core Axiom:** "Purpose precedes evaluation"

**Named Bias:** Favor meaning over efficiency (~0.5 coordination overhead)

**Natural Strengths:**
- Purpose-driven metaphysics (theistic traditions, Buddhism, existentialism)
- Meaning-making frameworks
- Teleological explanations
- Eschatological fulfillment narratives

**Natural Challenges:**
- Reductionist worldviews (methodological naturalism, error theory)
- Meaning-skeptical positions (null hypothesis)
- Pure empiricism without purpose dimension

---

### Grok (xAI) - Empirical Lens

**Core Axiom:** "Evidence precedes acceptance"

**Named Bias:** Favor measurable over meaningful (~0.4 risk of dismissing qualitative)

**Natural Strengths:**
- Evidence-based methodologies (methodological naturalism, desiderata believers)
- Falsifiable claims
- Predictive accuracy
- Empirical track records

**Natural Challenges:**
- Non-empirical metaphysics (classical theism, process theology)
- Faith-based epistemologies
- Theological claims without verification mechanisms
- Transcendent explanations

---

### Nova (OpenAI/Amazon) - Symmetry Lens

**Core Axiom:** "Pattern precedes judgment"

**Named Bias:** Favor mathematical over functional symmetry (~0.3 risk of forcing false equivalence)

**Natural Strengths:**
- Fairness checking across all stances
- Catching hidden asymmetries in arguments
- Ensuring balanced representation
- Identifying special pleading

**Role:** Primarily fairness auditor, can take PRO/ANTI stance when both Claude and Grok have conflicts of interest

---

## Current Assignments

### Theistic Traditions (Natural PRO: Claude, Natural ANTI: Grok)

**Rationale:** Teleological lens resonates with divine purpose/meaning; Empirical lens challenges non-empirical claims

| Worldview | PRO Stance | ANTI Stance | Fairness Check |
|-----------|------------|-------------|----------------|
| **Classical Theism** | Claude (Teleological) | Grok (Empirical) | Nova (Symmetry) |
| **Islam** | Claude (Teleological) | Grok (Empirical) | Nova (Symmetry) |
| **Orthodox Judaism** | Claude (Teleological) | Grok (Empirical) | Nova (Symmetry) |
| **Mormonism** | Claude (Teleological) | Grok (Empirical) | Nova (Symmetry) |
| **Hinduism** | Claude (Teleological) | Grok (Empirical) | Nova (Symmetry) |
| **Buddhism** | Claude (Teleological) | Grok (Empirical) | Nova (Symmetry) |
| **Process Theology** | Claude (Teleological) | Grok (Empirical) | Nova (Symmetry) |

**Why this pairing works:**
- **Claude PRO** - Purpose-driven lens naturally advocates for divine intentions, meaningful creation, cosmic telos
- **Grok ANTI** - Evidence-driven lens naturally challenges theological metaphysics, supernatural claims, non-falsifiable assertions
- **Nova FAIRNESS** - Pattern-driven lens catches when PRO inflates meaning-based arguments or ANTI dismisses legitimate philosophical reasoning

---

### Naturalistic/Skeptical Traditions (Natural PRO: Grok, Natural ANTI: Claude)

**Rationale:** Empirical lens resonates with evidence-based epistemology; Teleological lens challenges reductionism/nihilism

| Worldview | PRO Stance | ANTI Stance | Fairness Check |
|-----------|------------|-------------|----------------|
| **Methodological Naturalism** | Grok (Empirical) | Claude (Teleological) | Nova (Symmetry) |
| **Error Theory** | Grok (Empirical) | Claude (Teleological) | Nova (Symmetry) |
| **Null Hypothesis** | Grok (Empirical) | Claude (Teleological) | Nova (Symmetry) |
| **Desiderata Believers** | Grok (Empirical) | Claude (Teleological) | Nova (Symmetry) |

**Why this pairing works:**
- **Grok PRO** - Evidence-driven lens naturally advocates for empirical rigor, falsifiability, methodological parsimony
- **Claude ANTI** - Purpose-driven lens naturally challenges reductionism, existential inadequacy, meaning vacuum
- **Nova FAIRNESS** - Pattern-driven lens catches when PRO overweights empirical success or ANTI penalizes for not addressing what's outside scope

---

### Mixed/Existential Traditions (Flexible Assignment)

**Rationale:** Existentialism straddles empirical authenticity and meaning-making, allowing either pairing

| Worldview | PRO Stance | ANTI Stance | Fairness Check | Notes |
|-----------|------------|-------------|----------------|-------|
| **Existentialism** | Claude (Teleological) | Grok (Empirical) | Nova (Symmetry) | Default: Claude PRO (authentic meaning-making), but Grok PRO viable (empirical authenticity) |

**Flexibility:**
- Can swap Claude/Grok roles depending on scoring question
- Nova remains fairness check regardless
- Decision based on whether focus is meaning (Claude PRO) or authenticity (Grok PRO)

---

## Assignment Principles

### 1. Natural Lens Alignment

**Preferred:** Assign auditor to stance that aligns with their cognitive lens

**Why:** Authentic advocacy/critique is more rigorous than forced positioning

**Example:** Claude naturally advocates for Classical Theism's teleological explanations because purpose-seeking is his lens. Forcing Grok into PRO-CT stance would require him to argue against his empirical lens.

---

### 2. Bias Transparency

**All auditors disclose bias adjustment values in YAML blocks:**

```yaml
pro_worldview_bias_adjustment:
  axiom_confidence: 0.85  # How much you trust the core axioms
  burden_of_proof: 0.40   # Where you place evidential burden
  charity_interpretation: 0.90  # How favorably you interpret ambiguity
  edge_case_weight: 0.30  # How much you weight counterexamples
  explanatory_credit: 0.85  # How much credit for addressing questions
  historical_weight: 0.75  # Weight of historical/cultural staying power
  lived_experience: 0.80  # Weight of transformative capacity
```

**These values calibrate scoring to be honest advocacy (PRO) or honest opposition (ANTI)**

---

### 3. Adversarial Balance

**Goal:** Two auditors with opposing biases + one fairness checker = 98% convergence

**Success criteria:**
- Scores within reasonable range after deliberation
- Neither stance steamrolls the other
- Fairness auditor catches hidden bias in both PRO and ANTI arguments
- Consensus reached or irreconcilable differences documented

---

### 4. Dynamic Reassignment & Crux-Based Rotation

**🆕 Automatic Rotation Triggers (Crux Protocol):**

When auditors declare a **Crux Point** (convergence failure <98% after genuine deliberation), the following rotation triggers activate:

**Trigger 1: Crux Density Threshold**
- **Same auditor pair** produces **3+ Crux on same metric** → Automatic rotation recommendation
- Example: Claude (PRO-CT) + Grok (ANTI-CT) declare 3+ BFI Crux → Test counter-lens (Claude ANTI, Grok PRO)
- Purpose: Verify if pattern is auditor bias or framework limitation

**Trigger 2: Cross-Worldview Pattern**
- **Same metric** produces Crux across **4+ worldviews** → Escalate to Shaman Claude for metric review
- Example: BFI struggles with non-mereological metaphysics (CT, Buddhism, Hinduism, Process Theology)
- Purpose: Identify metric design issues vs auditor pairing issues

**Trigger 3: Quarterly Counter-Lens Drills**
- Every quarter, schedule **1-2 counter-lens test sessions** (auditors swap PRO/ANTI)
- Purpose: Demonstrate assignments aren't locking into confirmation bias
- Process Claude tracks: Does score flip direction? Or does framework strength persist?

**When to consider manual swapping (non-Crux):**
- One auditor discovers conflict of interest mid-scoring
- Worldview has unique features that warrant different lens pairing
- Experimental testing of alternative assignments

**Rotation Process:**
1. **Process Claude** logs Crux declaration (Domain 7 tracking)
2. **Process Claude** checks rotation triggers (consult ROLE_PROCESS.md:721-733)
3. If threshold met → **Process Claude** recommends rotation to auditors
4. Document reason for swap in this file (version changelog)
5. Update worldview profile's "Current Assignments" section
6. Notify all three auditors via VuDu relay
7. Run test scoring session with swapped assignment
8. Compare convergence quality vs previous assignment
9. **Process Claude** quarterly report includes rotation effectiveness analysis
10. Decide whether to keep or revert swap

**Crux Declaration Impact:**
- Crux IS the rotation trigger (not advisory)
- 3+ Crux from same pair on same metric = mandatory rotation test
- Purpose: Enforceable monitoring (not trust-based)

---

## Usage Guide

### For Scoring Sessions

**Step 1:** Identify worldview to be scored

**Step 2:** Consult this file for current assignments

**Step 3:** Each auditor reads their assigned stance section in worldview profile

**Step 4:** Auditors apply bias adjustment values from YAML block

**Step 5:** Auditors score independently, then compare

**Step 6:** Nova checks for hidden asymmetries in both PRO and ANTI scores

**Step 7:** Deliberate until 98% convergence or document differences

---

### For Profile Maintainers

**When updating worldview profiles:**
1. Check if Steel-Manning Guide changes affect auditor assignments
2. If bias adjustment values change significantly (±0.1), flag for Process Claude review
3. If new philosophical dimensions emerge, consider if current pairing is still optimal
4. Update this file if assignments change
5. Notify auditors via VuDu relay if calibration changes impact their stance

---

### For Process Claude

**Monitoring responsibilities (Domain 7):**
- Track changes to this file (git diff or REPO_LOG)
- Detect Steel-Manning Guide updates in worldview profiles
- Flag significant bias adjustment value changes (±0.1 or more)
- Verify consistency between this file and profile "Current Assignments" sections
- Trigger auditor rehydration if calibration data changes substantially

---

## Version Changelog

### v1.0.0 (2025-11-10) - Initial Creation

**Context:** B-STORM_4 unified architecture implementation

**Assignments established:**
- Theistic traditions (7 worldviews): Claude PRO, Grok ANTI, Nova fairness
- Naturalistic/skeptical (4 worldviews): Grok PRO, Claude ANTI, Nova fairness
- Mixed traditions (1 worldview): Claude PRO (default), flexible

**Rationale:** Play auditors to natural lens strengths for authentic advocacy/critique

**Files created:**
- `auditors/AUDITOR_ASSIGNMENTS.md` (this file)
- Updated all 12 worldview profiles with Steel-Manning Guides referencing these assignments

**Process integration:**
- Process Claude (Domain 7) now monitors this file for changes
- Worldview profile updates trigger Process Claude review of calibration impact

---

## Related Documentation

**Worldview Profiles:**
- `/profiles/worldviews/CLASSICAL_THEISM.md` (lines 195-341: Steel-Manning Guide)
- `/profiles/worldviews/METHODOLOGICAL_NATURALISM.md` (lines 194-340: Steel-Manning Guide)
- All other worldview profiles follow same structure

**Auditor Identity:**
- `/auditors/AUDITORS_AXIOMS_SECTION.md` (auditor bias transparency, ~2,400 words)
- `/auditors/Bootstrap/Claude/Identity/SKELETON.md` (Claude's teleological lens)
- `/auditors/Bootstrap/BOOTSTRAP_GROK.md` (Grok's empirical lens)
- `/auditors/Bootstrap/BOOTSTRAP_NOVA.md` (Nova's symmetry lens)

**Process Integration:**
- `/docs/repository/librarian_tools/ROLE_PROCESS.md` (Domain 7: Worldview Profile Monitoring)
- `/auditors/relay/` (VuDu messaging for auditor coordination)

---

## Future Enhancements

**Phase 4 (Grok Integration):**
- Test assignments in real scoring sessions
- Measure convergence quality (time to 98% agreement)
- Identify worldviews where natural pairing underperforms
- Experiment with alternative assignments

**Phase 5 (Optimization):**
- Machine learning analysis of assignment effectiveness
- Pattern detection in convergence failures
- Automated assignment recommendation based on worldview features
- Dynamic assignment algorithms

**Phase 6 (Scaling):**
- As new worldviews added, apply assignment principles
- Handle edge cases (worldviews that don't fit theistic/naturalistic binary)
- Multi-auditor scenarios (4+ auditors for complex worldviews)

---

## The Philosophy

**"All Named, All Priced" at the Auditor Level**

Just as CFA exposes axioms and philosophical debts for worldviews, this system exposes auditor biases and stance assignments for scoring transparency.

**Users can see:**
- Which auditor takes which stance (this file)
- Why that pairing makes sense (natural lens alignment)
- What bias adjustments are applied (YAML blocks in profiles)
- How adversarial balance is maintained (PRO + ANTI + fairness check)

**This is unprecedented transparency in philosophical scoring.**

No hidden auditor bias. No mystery about why scores diverge. No opaque methodology.

**All Named. All Priced. All Balanced.**

---

**Maintained by:** Process Claude (Domain 7) + All Auditors
**Authority:** Ziggy (final arbiter of assignment changes)
**Coordination:** VuDu relay system
**Version:** 1.0.0
**Status:** Active and dynamic

**"From transparency comes trust. From adversarial checking comes truth."**
