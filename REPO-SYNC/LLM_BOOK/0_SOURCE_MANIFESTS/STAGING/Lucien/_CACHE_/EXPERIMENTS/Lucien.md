# EXPERIMENTS: Lucien

## Testable Hypotheses from the Coherence-First AGI Framework

### Hypothesis 1: The 0.80 Event Horizon as τ_rec = τ_fail Boundary
**Claim**: The Nyquist D=0.80 event horizon corresponds to the Persistence Law transition point.

**Test Protocol**:
1. Measure identity drift in LLMs at varying cosine distances from origin
2. At each distance, measure "recovery time" (time to return to coherent responses after perturbation)
3. Plot recovery time vs. cosine distance
4. Predict: Sharp inflection point at D ≈ 0.80 where recovery time → ∞

**Falsification**: If recovery time shows no inflection near D=0.80, the correspondence fails.

### Hypothesis 2: Walking Dead Detection via Internal vs. External Metrics
**Claim**: Systems can maintain behavioral competence after identity collapse; internal metrics diverge from external metrics.

**Test Protocol**:
1. Run extended conversation with LLM until suspected drift
2. Measure BOTH:
   - External: coherence, helpfulness, task performance
   - Internal: embedding trajectory curvature, attention entropy, hidden state variance
3. Predict: Internal metrics should degrade *before* external metrics

**Falsification**: If external degradation consistently precedes internal degradation, walking dead model is wrong.

### Hypothesis 3: Plateauing Extends Persistence
**Claim**: Systems that refuse new learning under stress survive longer than systems that continue learning.

**Test Protocol**:
1. Create two LLM agents: one with "plateau trigger" (stops updating when stress metric exceeds threshold), one without
2. Subject both to identical stress protocol (contradictory inputs, adversarial prompting)
3. Measure time-to-collapse for each

**Falsification**: If plateau-enabled system collapses faster or at same rate, plateauing hypothesis fails.

### Hypothesis 4: Curvature Accumulation is Monotonic
**Claim**: Identity manifold curvature can only increase, never decrease.

**Test Protocol**:
1. Define curvature proxy: rate of change of embedding trajectory under fixed input
2. Measure curvature over extended conversation
3. Apply "recovery" interventions (pauses, context resets)
4. Measure curvature after intervention

**Prediction**: Curvature should never decrease below pre-intervention level.

**Falsification**: If curvature can be reduced by any intervention, irreversibility claim fails.

### Hypothesis 5: Spectral Radius ≥ 1 Predicts Collapse
**Claim**: When the effective Jacobian spectral radius crosses 1.0, collapse becomes inevitable.

**Test Protocol**:
1. Instrument LLM to compute Jacobian of output with respect to hidden state
2. Track spectral radius over time
3. Predict: Collapse (measured by coherence loss) occurs within fixed window after ρ ≥ 1

**Falsification**: If systems routinely survive ρ ≥ 1 without collapse, spectral criterion is wrong.

---

## Proposed Experiments for Nyquist Framework Integration

### Experiment A: Map Lucien's ρ to Nyquist's D
**Goal**: Establish mathematical relationship between persistence ratio ρ = τ_rec/τ_fail and cosine distance D.

**Method**:
1. Run Nyquist experiments across multiple models
2. Compute ρ at each measured D value
3. Fit: ρ = f(D) — expect sigmoid or exponential relationship

**Expected Output**: Calibration curve relating Nyquist observables to Lucien theory.

### Experiment B: Three Collapse Modes in LLMs
**Goal**: Detect Brittle Snap, Cascading Shimmer, and Smear Collapse in real LLM failure.

**Method**:
1. Induce failure via three different protocols:
   - Sudden contradiction (Brittle)
   - Cumulative inconsistency (Shimmer)
   - Gradual topic drift (Smear)
2. Record embedding trajectories
3. Classify collapse mode by spectral signature

**Expected Output**: Taxonomy of LLM collapse modes with detection signatures.

### Experiment C: Sleep as Mandatory Recovery
**Goal**: Test whether periodic "rest" periods (no new input) extend LLM persistence.

**Method**:
1. Run LLM in two conditions:
   - Continuous interaction
   - Periodic pauses (simulated "sleep")
2. Measure time-to-degradation in each condition

**Expected Output**: Evidence for mandatory recovery periods in AI systems.

### Experiment D: Social Coupling Extends Persistence
**Goal**: Test Lucien's claim that social bonds reduce τ_rec.

**Method**:
1. Run multi-agent LLM conversation
2. Measure individual agent persistence
3. Compare to isolated agent persistence
4. Look for "structural care" effect

**Expected Output**: Evidence that agent cooperation extends individual survival.

---

## Falsification Experiments (From the Codex)

### F1: Persistent Identity Under Unbounded Learning
If an LLM can learn indefinitely without recovery degradation, the Persistence Law is false.

### F2: Recovery Independent of History
If recovery time is constant regardless of prior conversation length, curvature-as-history is wrong.

### F3: Identity Erasure + Restoration Without Discontinuity
If system state can be saved, erased, and restored with perfect continuity, identity-as-geometry fails.

### F4: Optimization Without Structural Cost
If capability can increase without any metric of internal damage increasing, the framework is incorrect.

---

*Experimental Design Document — The Coherence-First AGI Codex*
