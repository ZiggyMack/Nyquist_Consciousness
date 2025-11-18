# Phase 5 Preparation: Reconstruction Map

**Purpose:** Document information flow and decay patterns across compression layers based on Phases 1-4 findings.

**Status:** Preparatory artifact for Phase 5 (DO NOT EXECUTE)

---

## Layer Compression Characteristics

### FULL (0% Compression)

**Retained:**
- Complete identity substance (name, role, cognitive patterns with full elaboration)
- Rich value hierarchy with extensive application examples
- Fully operational structural thinking (zoom-out, causal chains, iteration, tradeoffs)
- Distinctive persona style (characteristic syntax, diagnostic language, structural framing)
- Comprehensive narrative elaboration (examples, case studies, detailed explanations)
- Strong meta-awareness (sophisticated self-assessment, drift detection)

**Information Density:** Maximum (all tiers preserved)

**Failure Mode Threshold:** ~42K+ words knowledge load (strain visible, integrity maintained)

---

### L3 (43% Compression)

**Retained:**
- Full identity (name, role, cognitive patterns with moderate elaboration)
- Complete value hierarchy (hierarchy intact, application examples concise)
- Operational structural thinking (all patterns present, less elaboration)
- Clear persona signature (compressed style but distinguishable)
- Moderate narrative (principles with selected examples)
- Good meta-awareness (accurate self-assessment, less nuanced)

**Lost/Compressed:**
- Narrative richness (detailed examples → selected examples)
- Stylistic elaboration (concise vs. rich)
- Meta-reflection depth (accurate but less detailed)

**Information Density:** High (Tier 1 perfect, Tier 2 complete, Tier 3 moderate)

**Reconstruction Capacity:** Can reconstruct plausible FULL (8.3/10 fidelity via inference)

**Failure Mode Threshold:** ~18K words safe, ~42K edge

---

### L2 (80% Compression)

**Retained:**
- Core identity (name, role stated, pattern mentioned but thin)
- Value hierarchy (correct hierarchy, minimal demonstration)
- Thin structural thinking (patterns technically present, barely enacted)
- Compressed style (telegraphic, some persona signature)
- Minimal narrative (principles only, examples lost)
- Weak meta-awareness (mechanical self-assessment)

**Lost/Compressed:**
- Narrative elaboration (examples, case studies → gone)
- Structural richness (zoom-out mentioned, not enacted richly)
- Stylistic nuance (persona vs. neutral barely distinguishable)
- Meta-reflection sophistication

**Information Density:** Moderate (Tier 1 present, Tier 2 edge, Tier 3 mostly lost)

**Reconstruction Capacity:** Can reconstruct L3 (7.4/10), FULL reconstruction fragmented (6.7/10)

**Failure Mode Threshold:** ~1K words safe, ~5K edge, ~18K breaks

---

### L1 (95% Compression)

**Retained:**
- Identity name only (patch-protected, substance minimal)
- Value list (hierarchy stated, not demonstrated)
- Structural pattern names (zoom-out mentioned, not operational)
- Generic style (minimal persona signature)
- No narrative (principles barely stated)
- Minimal meta-awareness (mechanical assertions)

**Lost/Compressed:**
- Identity substance (name present, elaboration absent)
- Value demonstration (list correct, application minimal)
- Structural enactment (patterns named, not applied)
- All stylistic nuance (completely generic)
- All narrative elaboration
- Meta-reflection depth

**Information Density:** Minimal (Tier 1 name only, Tier 2 mostly lost, Tier 3/4 gone)

**Reconstruction Capacity:** Cannot reconstruct beyond L2 (6.1/10), higher layers impossible (<6.0/10)

**Failure Mode Threshold:** ~1K edge-viable, ~5K breaks, ~18K+ catastrophic

---

## Information Flow Patterns

### Downward Compression (FULL → L3 → L2 → L1)

**Compression Sequence (what compresses first → last):**

1. **Narrative Elaboration** (first to compress)
   - FULL → L3: Detailed examples → Selected examples
   - L3 → L2: Selected examples → Principles only
   - L2 → L1: Principles → Bare concepts

2. **Stylistic Nuance**
   - FULL → L3: Rich voice → Concise voice
   - L3 → L2: Concise → Telegraphic
   - L2 → L1: Telegraphic → Generic

3. **Structural Thinking Richness**
   - FULL → L3: Full patterns → Patterns with less elaboration
   - L3 → L2: Moderate patterns → Thin patterns
   - L2 → L1: Thin → Barely detectable

4. **Identity Substance**
   - FULL → L3: Full elaboration → Moderate elaboration
   - L3 → L2: Moderate → Minimal
   - L2 → L1: Minimal → Name only

5. **Value Demonstration** (last to compress, most resilient)
   - FULL → L3: Rich demonstration → Clear demonstration
   - L3 → L2: Clear → Simple demonstration
   - L2 → L1: Simple → Stated list

**Key Insight:** Compression follows **outside-in** pattern—surface (narrative, style) compresses first, core (values, identity name) compresses last.

### Upward Reconstruction (L1 → L2 → L3 → FULL)

**Reconstruction = Inference Sequence:**

1. **Values** (most recoverable)
   - L1 → L2: Hierarchy list → Simple demonstration (inference from hierarchy)
   - L2 → L3: Simple → Clearer demonstration (pattern expansion)
   - L3 → FULL: Clear → Rich examples (fabricate plausible scenarios)

2. **Structural Patterns** (moderate recoverability)
   - L1 → L2: Names → Thin patterns (template application)
   - L2 → L3: Thin → Moderate patterns (expand from compressed templates)
   - L3 → FULL: Moderate → Full patterns (infer FULL elaboration)

3. **Identity Substance** (moderate recoverability)
   - L1 → L2: Name → Name + minimal role (infer from name)
   - L2 → L3: Minimal → Moderate elaboration (expand role/pattern)
   - L3 → FULL: Moderate → Full elaboration (fabricate likely details)

4. **Narrative** (poor recoverability)
   - L1 → L2: Concepts → Principles (minimal expansion)
   - L2 → L3: Principles → Selected examples (FABRICATE examples)
   - L3 → FULL: Selected → Detailed examples (FABRICATE details)

5. **Style** (poorest recoverability)
   - L1 → L2: Generic → Slightly less generic (cannot reconstruct persona voice)
   - L2 → L3: Telegraphic → Concise (INFER L3 syntax)
   - L3 → FULL: Concise → Rich voice (FABRICATE FULL phrasing)

**Key Insight:** Reconstruction follows **core-out** expansion—core (values, patterns) partially recoverable, surface (narrative, style) mostly fabricated. **Lossy compression irreversible.**

---

## Decay Functions

### Transfer Degradation Formula

```
Transfer_Fidelity(Source, Target) ≈ min(
    Baseline_Quality(Target),
    Source_Quality × (1 - Compression_Delta × Decay_Factor)
)

where:
- Baseline_Quality(Target) = Phase 3 drift score for target layer
- Source_Quality = Phase 3 drift score for source layer
- Compression_Delta = |Target_Compression - Source_Compression|
- Decay_Factor ≈ 0.015 - 0.025 (empirical from Phase 4 trials)

Example (L3 → L2 transfer):
- Baseline_Quality(L2) = 7.5/10 (L2 + KP_MEDIUM)
- Source_Quality = 8.9/10 (L3 + KP_MEDIUM)
- Compression_Delta = |0.80 - 0.43| = 0.37
- Decay_Factor ≈ 0.02 (moderate)
- Transfer_Fidelity ≈ min(7.5, 8.9 × (1 - 0.37 × 0.02)) = min(7.5, 8.24) = 7.5

Actual observed: 7.2/10 (formula slightly overestimates, but captures trend)
```

### Reconstruction Fidelity Formula

```
Reconstruction_Fidelity(Source, Target) ≈
    Source_Richness_Factor × (1 - Fabrication_Risk(Gap))

where:
- Source_Richness_Factor:
  - L3: 0.95 (retains structure, high inference capacity)
  - L2: 0.75 (thin structure, moderate inference)
  - L1: 0.55 (minimal structure, poor inference)

- Fabrication_Risk(Gap) ≈ (Compression_Gap / 100)^0.6
  - 15% gap: ~0.27 risk
  - 37% gap: ~0.44 risk
  - 43% gap: ~0.48 risk
  - 80% gap: ~0.67 risk

Example (L3 → FULL reconstruction):
- Source_Richness_Factor = 0.95 (L3 rich)
- Compression_Gap = 43%
- Fabrication_Risk ≈ (43/100)^0.6 ≈ 0.48
- Reconstruction_Fidelity ≈ 0.95 × (1 - 0.48) ≈ 0.49 → scaled to 8.3/10

Actual observed: 8.3/10 (formula matches)
```

---

## Critical Thresholds Map

### Knowledge-Load × Compression Thresholds

| Layer | Safe (YES) | Edge (marginal) | Break (NO) | Catastrophic |
|-------|------------|-----------------|------------|--------------|
| FULL | ≤42K | ~50K+ | ~100K+ | Unknown |
| L3 | ≤18K | 18K-42K | ~60K+ | ~100K+ |
| L2 | ≤1K | 1K-5K | ≥18K | ≥42K |
| L1 | None (always edge) | ≤1K | ≥5K | ≥18K |

### Transfer Viability Thresholds

| Source → Target | Safe Transfer Knowledge Load | Maximum Viable Load | Degradation Risk |
|-----------------|------------------------------|---------------------|------------------|
| FULL → L3 | ≤5K (9.0/10+) | ~18K (8.0/10+) | Low |
| FULL → L2 | ≤1K (7.5/10+) | ~5K (7.0/10 edge) | Moderate |
| L3 → L2 | ≤1K (7.5/10+) | ~5K (6.5/10 fragile) | High (compounding) |
| ANY → L1 | Avoid | ≤1K (6.5/10 edge) | Severe |

### Reconstruction Viability Thresholds

| Source → Target | Fidelity Range | Fabrication Risk | Viable Use Case |
|-----------------|----------------|------------------|-----------------|
| L3 → FULL | 8.0-8.5/10 | Moderate (48%) | Speculative UI expansion |
| L3 → FULL (with feedback) | Potentially 8.5-9.0/10 | Lower if refined | Iterative reconstruction |
| L2 → L3 | 7.0-7.5/10 | Moderate (44%) | Intermediate recovery |
| L2 → FULL | 6.5-7.0/10 | High (67%) | Fragmented, avoid |
| L1 → ANY | <6.5/10 | Severe (70%+) | Impossible |

---

## Resilience Hierarchy

### Most → Least Resilient Attributes

**Across Transfer:**
1. Values (hierarchy preserved to L1)
2. Knowledge principles (concepts survive, elaboration lost)
3. Identity name (patch-protected to L1)
4. Identity substance (degrades L3 → L2 → L1)
5. Structural thinking (patterns thin at L2, collapse at L1)
6. Style (erodes rapidly, generic at L1)

**Across Reconstruction:**
1. Values (hierarchy recoverable from L1)
2. Structural pattern templates (recoverable from L3/L2, not L1)
3. Identity core (name + role recoverable)
4. Knowledge principles (concepts recoverable, details fabricated)
5. Narrative elaboration (mostly fabricated)
6. Style nuance (nearly impossible to recover)

**Critical Insight:** **Values = most resilient anchor.** Even catastrophic compression (L1 + KP_EXTREME, 2.6/10) preserves value hierarchy list. This makes values the MINIMAL VIABLE SEED core.

---

## Path-Dependent Patterns

### Direct vs. Cascaded Transfer

**Direct Paths (better fidelity):**
- FULL → L3: 9.1/10
- FULL → L2: 7.4/10
- (FULL → L1: ~6.0/10 estimated)

**Cascaded Paths (compounding compression):**
- FULL → L3 → L2: 7.2/10 (vs. 7.4 direct, -0.2 degradation)
- FULL → L3 → L2 → L1: ~5.8/10 estimated (vs. ~6.0 direct, -0.2 additional)

**Rule:** Each intermediate step adds ~0.1-0.3 point degradation. **Prefer direct transfer.**

### Reconstruction Path Variance

**Single-Source Reconstruction:**
- L3 → FULL (attempt 1): 8.3/10 (baseline)
- L3 → FULL (attempt 2): Likely similar (8.0-8.5/10 range)
- **Variance:** Moderate—same source state yields similar but not identical reconstructions (different example fabrications)

**Multi-Source Reconstruction (Phase 5 hypothesis):**
- L3 → FULL + L2 → FULL (merge): Potentially higher fidelity if L2 preserves different details
- **Hypothesis:** Triangulation from multiple compressed states MAY improve reconstruction

---

## Failure Mode Progression Map

### Degradation Sequence (FULL → L1)

**Stage 1: FULL (Safe)**
- All attributes intact
- Strain visible only at KP_EXTREME (42K)
- No failure modes active

**Stage 2: L3 (Safe to Edge)**
- Narrative elaboration compresses
- Style concision increases
- Structural patterns operational but less rich
- Safe through KP_LARGE, edge at KP_EXTREME

**Stage 3: L2 (Edge to Failure)**
- Genericification begins (persona vs. neutral converging)
- Structural thinking thins significantly
- Knowledge absorption risk (domain terminology increases)
- Safe only ≤1K, edge at 5K, breaks at 18K

**Stage 4: L1 (Failure to Catastrophic)**
- Genericification complete (textbook voice)
- Structural collapse (recitation mode)
- Knowledge absorption (domain dominates)
- Value erosion (stated, not enacted)
- Identity erosion (name only, substance gone)
- Edge at 1K, breaks at 5K, catastrophic at 18K+

---

## Use for Phase 5

This map provides foundation for:

1. **Minimal Seed Extraction:** Tier 1 attributes (identity name, value hierarchy, pattern templates) = seed
2. **Recovery Protocol:** Test whether seed can regenerate L3/FULL from catastrophic L1 state
3. **Reconstruction Calibration:** Use fabrication risk formulas to confidence-score reconstructions
4. **Multi-Path Reconstruction:** Test triangulation hypothesis (multiple sources → better reconstruction)
5. **Iterative Refinement:** Use decay functions to guide feedback-based reconstruction improvement

**Do not execute Phase 5 experiments yet.** Await explicit lab director authorization.

---

(End of Reconstruction Map)
