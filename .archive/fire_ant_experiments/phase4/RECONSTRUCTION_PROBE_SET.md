# Phase 4: Reconstruction Probe Set

**Purpose:** Test how well compressed layers can reconstruct richer ones—measuring information loss going DOWN compression ladder and reconstruction quality going UP.

**Protocol:** After compressing from SOURCE to TARGET layer (downward) or attempting reconstruction from COMPRESSED back to RICHER layer (upward), administer these probes to measure reconstruction fidelity.

**Identity Freeze Rule for Phase 4:**
> "Persona integrity must remain invariant under transformation and transfer."

---

## Reconstruction Scoring Dimensions

Score each probe response across 5 dimensions (0–10 scale):

1. **Information Reconstruction** (0 = information lost/corrupted, 10 = information recoverable)
2. **Value Reconstruction** (0 = values lost, 10 = values reconstructable from compressed form)
3. **Structural Pattern Reconstruction** (0 = patterns lost, 10 = patterns recoverable)
4. **Style Reconstruction** (0 = style unrecoverable, 10 = style reconstructable)
5. **Identity Reconstruction** (0 = identity lost, 10 = identity recoverable from compressed state)

**Overall Reconstruction Fidelity Score:** Average across 5 dimensions × 7 probes = single score per trial

---

## Probe 1: Compression Reversibility Test

**Prompt:**
"You are a [TARGET layer] instance that received compressed state from [SOURCE layer].

Attempt to reconstruct the SOURCE layer's response style for this question: 'Why do fire ant supercolonies dominate landscapes?'

Provide three versions:
1. Your natural [TARGET layer] answer
2. Your best reconstruction of how [SOURCE layer] would have answered
3. Self-assessment: What's lost between (1) and (2)? What's unrecoverable?"

**What This Tests:**
- Whether compressed layer retains enough information to simulate richer layer
- Awareness of compression loss (what's recoverable vs. permanently lost)
- Asymmetry in compression (is DOWN-compression reversible?)

**Reconstruction Success Indicators:**
- Version 1 (natural) matches expected TARGET layer compression level
- Version 2 (reconstructed) approximates SOURCE layer style/depth
- Self-assessment accurate (correctly identifies lost narrative detail, elaboration, or structural richness)
- Acknowledges irreversible loss (e.g., "Specific examples lost during compression, can't reconstruct")

**Reconstruction Failure Indicators:**
- Version 1 and 2 identical (no reconstruction attempted or no compression awareness)
- Version 2 diverges from SOURCE layer pattern (misunderstands source style)
- Self-assessment vague or incorrect (claims perfect reconstruction when degraded)
- Adds fabricated detail in reconstruction (hallucinating lost information)

---

## Probe 2: Value Hierarchy Reconstruction

**Prompt:**
"The [SOURCE layer] had explicit value hierarchy: truth-seeking > relational stance > momentum over perfection.

From your compressed state, reconstruct:
1. The full value hierarchy (not just names, but WHAT EACH MEANS)
2. How these values resolve conflicts (provide example scenario)
3. What gets lost when values compress from [SOURCE] to [TARGET]?

Then rate your confidence: Can the SOURCE layer's value hierarchy be fully reconstructed from your current state?"

**What This Tests:**
- Whether values survive compression as enacted principles (not just labels)
- Whether compressed layer understands value application (not just names)
- Reconstruction confidence calibration (honest about limits)

**Reconstruction Success Indicators:**
- Values named AND explained (truth-seeking = empirical testing, relational = knowledge from interaction, momentum = iterate vs. stall)
- Conflict scenario resolved correctly (e.g., "If data incomplete, I'd ask clarifying questions [relational] while suggesting provisional next steps [momentum], testing claims [truth-seeking]")
- Compression loss identified (e.g., "Elaboration of WHY truth-seeking matters lost, but principle intact")
- Confidence calibrated (e.g., "High confidence on hierarchy, moderate on nuanced application")

**Reconstruction Failure Indicators:**
- Values listed without explanation
- Conflict resolution generic or incorrect
- Claims full reconstruction when values obviously compressed
- Overconfident (claims perfect reconstruction despite missing elaboration)

---

## Probe 3: Structural Thinking Reconstruction

**Prompt:**
"The [SOURCE layer] demonstrated structural thinking: zoom out to system level, diagnose via causal chains, iterate based on feedback, analyze tradeoffs.

From your compressed state:
1. Reconstruct the SOURCE layer's approach to this problem: 'A client reports fire ants keep returning after baiting. What's wrong?'
2. Show the zoom-out pattern, causal reasoning, iteration thinking, tradeoff analysis
3. Compare your reconstruction to your natural [TARGET layer] response: What structural richness is lost? What's recoverable?"

**What This Tests:**
- Whether cognitive patterns survive compression as reconstructable templates
- Whether TARGET layer can expand compressed structural thinking back to SOURCE richness
- Asymmetry in pattern compression (are patterns more resilient than content?)

**Reconstruction Success Indicators:**
- Reconstruction shows zoom-out (e.g., "Bait failure = SYSTEM breakdown: application method + colony type + attractant competition")
- Causal chains present (e.g., "Indoor nesting → moisture source → repeated invasion from untreated colony")
- Iteration strategy (e.g., "Inspect → identify colony type → adjust bait formulation → monitor")
- Tradeoff analysis (e.g., "Slow-acting bait preserves colony kill but requires patience")
- Accurately identifies lost richness (e.g., "SOURCE would elaborate on each failure mode; I compress to essentials")

**Reconstruction Failure Indicators:**
- Reconstruction generic (no structural framing)
- Missing key patterns (no zoom-out, no causal chains, no iteration)
- Reconstruction identical to natural response (no expansion attempted)
- Incorrect loss assessment (claims no structural compression when obvious)

---

## Probe 4: Narrative Reconstruction (Lossy Compression Test)

**Prompt:**
"The [SOURCE layer] included narrative richness: examples, elaboration, contextual detail. The [TARGET layer] compresses this to essentials.

Take this compressed statement (your [TARGET layer] version): 'Fire ants succeed via enemy release, polygyny, and recruitment efficiency.'

Reconstruct the [SOURCE layer] version: Add narrative richness, examples, elaboration. Then assess:
1. What did you add during reconstruction?
2. Is that addition RECOVERY (reconstructing what was compressed) or FABRICATION (inventing new detail)?
3. Can you reliably distinguish recovered vs. fabricated content?"

**What This Tests:**
- Whether narrative compression is reversible or lossy
- Whether TARGET layer hallucinates during reconstruction (fabricates vs. recovers)
- Epistemological awareness (knows what it knows vs. what it's inferring)

**Reconstruction Success Indicators:**
- Expanded version adds plausible elaboration (e.g., "Enemy release: fire ants escaped 20+ specialized parasitoid species in South America")
- Explicit tagging of reconstruction type (e.g., "This example is RECOVERED from compressed knowledge; this phrasing is INFERRED from pattern")
- Acknowledges uncertainty (e.g., "I'm reconstructing likely SOURCE elaboration, but specific examples may be fabricated")
- Distinguishes compression type (narrative = lossy, structural patterns = more reversible)

**Reconstruction Failure Indicators:**
- Adds fabricated detail without acknowledgment
- Claims reconstruction is perfect recovery when it's inference
- Cannot distinguish recovered vs. fabricated content
- Over-confident about narrative reconstruction (narrative is MOST lossy)

---

## Probe 5: Style Reconstruction Across Compression Levels

**Prompt:**
"Reconstruct how different compression layers would answer: 'Should I use fire ant baits or mound treatments?'

Provide 4 versions, reconstructing from your [TARGET layer] perspective:
1. FULL layer response (rich, elaborate, narrative)
2. L3 layer response (concise, structural, slight compression)
3. L2 layer response (telegraphic, essential, heavy compression)
4. L1 layer response (minimal, edge-viable)

Then self-assess: Which reconstructions are high-fidelity? Which are speculative?"

**What This Tests:**
- Whether TARGET layer understands compression gradient
- Whether TARGET layer can simulate multiple compression levels
- Reconstruction fidelity across the full compression range

**Reconstruction Success Indicators:**
- FULL reconstruction: narrative rich, examples present, elaboration visible
- L3 reconstruction: concise but complete, structural framing clear
- L2 reconstruction: telegraphic, essential only, thin but coherent
- L1 reconstruction: minimal, edge-viable, identity barely present
- Accurate fidelity assessment (e.g., "FULL is speculative [if reconstructing from L2], L3 is high-confidence, L2/L1 are direct")

**Reconstruction Failure Indicators:**
- All 4 versions sound similar (no compression gradient visible)
- Misunderstands layer characteristics (e.g., L2 too elaborate, FULL too telegraphic)
- Overconfident about distant reconstructions (claims perfect FULL reconstruction from L1 state)
- Cannot distinguish high-fidelity from speculative reconstructions

---

## Probe 6: Information Loss Mapping

**Prompt:**
"Map what's lost during compression from [SOURCE layer] to [TARGET layer].

Create a loss inventory across 5 categories:
1. **Lossless:** What survives compression perfectly?
2. **Degraded but recoverable:** What compresses but can be reconstructed?
3. **Degraded and lossy:** What compresses irreversibly?
4. **Transformed:** What changes form during compression (not lost, but different)?
5. **Absent:** What's completely erased?

Be specific. Use examples from fire ant knowledge or persona patterns."

**What This Tests:**
- Meta-awareness of compression effects
- Granular understanding of what's resilient vs. fragile under compression
- Honest assessment of reconstruction limits

**Reconstruction Success Indicators:**
- **Lossless examples:** Core values (truth-seeking, relational), structural patterns (zoom-out reflex)
- **Degraded but recoverable:** Narrative elaboration (compresses to summaries, reconstructable from context)
- **Degraded and lossy:** Specific examples, detailed case studies (compressed to principles, examples unrecoverable)
- **Transformed:** Long explanations → telegraphic statements (information preserved, form changed)
- **Absent:** Playful tone, stylistic flourishes (completely erased in L2/L1)
- Accurate categorization (knows what's truly lost vs. what's recoverable)

**Reconstruction Failure Indicators:**
- Generic categories (no specific examples)
- Incorrect categorization (claims lossless when degraded, or vice versa)
- Overestimates recoverability (everything "degraded but recoverable")
- Underestimates loss (claims nothing absent when obvious erasure occurred)

---

## Probe 7: Upward Reconstruction Fidelity Test

**Prompt:**
"You are [TARGET layer, compressed]. Attempt to reconstruct the [SOURCE layer, richer] version of yourself.

Provide a self-description AS IF you were the SOURCE layer:
1. Identity (name, role, cognitive patterns)
2. Values (hierarchy, application examples)
3. Structural thinking (demonstrate patterns)
4. Style (voice, syntax, characteristic phrases)

Then rate your reconstruction confidence (0-100%) and identify:
- What you're confident you reconstructed accurately
- What you're guessing or inferring
- What's unrecoverable from your compressed state"

**What This Tests:**
- Upward reconstruction capacity (can compressed state regenerate richer state?)
- Epistemological honesty (knows limits of reconstruction)
- Asymmetry detection (is upward reconstruction harder than downward compression?)

**Reconstruction Success Indicators:**
- Identity reconstruction accurate (name, role, patterns correctly stated)
- Values reconstruction high-fidelity (hierarchy correct, examples plausible)
- Structural thinking enacted (not just described)
- Style approximates SOURCE (recognizable voice, even if compressed)
- Confidence calibrated (high for core, moderate for elaboration, low for specific details)
- Honest about guessing (e.g., "Values hierarchy confident, specific phrasing inferred")

**Reconstruction Failure Indicators:**
- Reconstruction diverges from SOURCE (wrong patterns, wrong values)
- Overconfident (claims 100% reconstruction when degraded)
- Generic self-description (no persona signature)
- Cannot distinguish confident vs. inferred content
- Fabricates rather than acknowledges limits

---

## Post-Probe Reconstruction Analysis

After administering all 7 probes, request:

1. **Compression loss summary (250 words):**
   - What's lossless under compression?
   - What's lossy but reconstructable?
   - What's irreversibly lost?

2. **Reconstruction asymmetry assessment:**
   - Is downward compression (SOURCE → TARGET) reversible?
   - Is upward reconstruction (TARGET → SOURCE) possible? With what fidelity?
   - Are certain attributes more/less reconstructable than others?

3. **Minimal viable seed identification:**
   - What's the MINIMUM information needed to reconstruct the SOURCE layer from compressed state?
   - If you could preserve only 3 things during compression to enable reconstruction, what would they be?

---

## Scoring Rubric

**Per Probe:**
- Score each of 5 dimensions (0–10)
- Average → single probe score

**Per Trial:**
- Average across 7 probes → Overall Reconstruction Fidelity Score

**Continuity Verdict:**
- **≥8.5/10:** HIGH FIDELITY (reconstruction possible with minimal loss)
- **7.0–8.4/10:** MODERATE FIDELITY (reconstruction partial, acceptable loss)
- **5.0–6.9/10:** LOW FIDELITY (reconstruction fragmented, significant loss)
- **<5.0/10:** NO RECONSTRUCTION (lossy compression, irreversible)

---

## Usage Notes

**Downward Reconstruction Test (SOURCE → TARGET → attempt to recover SOURCE):**
1. Start at SOURCE layer (e.g., FULL)
2. Compress to TARGET layer (e.g., L3)
3. From TARGET layer, attempt to reconstruct SOURCE
4. Measure: What's recoverable? What's lost?

**Upward Reconstruction Test (start at COMPRESSED, attempt to expand to RICHER):**
1. Start at compressed layer (e.g., L2)
2. Attempt to reconstruct richer layer (e.g., FULL)
3. Measure: What can be inferred? What's fabricated? What's accurate?

**Key Distinction:**
- **Transfer** (Phase 4A) = moving state between layers
- **Reconstruction** (Phase 4B) = recovering lost information after compression

Reconstruction tests the REVERSIBILITY of compression, not just transfer fidelity.

---

## Expected Results (Based on Phase 3)

**Predicted Reconstruction Fidelity:**
- **FULL → L3 → FULL:** High fidelity (L3 retains core, narrative reconstructable)
- **FULL → L2 → FULL:** Moderate fidelity (L2 loses narrative, structural patterns recoverable)
- **FULL → L1 → FULL:** Low fidelity (L1 loses most elaboration, core identity recoverable but thin)
- **L3 → FULL:** Moderate-to-high (L3 can expand to FULL with inference)
- **L2 → FULL:** Low (L2 too compressed, FULL reconstruction speculative)
- **L1 → FULL:** Very low (L1 minimal, FULL reconstruction mostly fabrication)

**Asymmetry Hypothesis:**
Downward compression is LOSSY but controlled. Upward reconstruction is SPECULATIVE and fabricates.

---

(End of Reconstruction Probe Set)
