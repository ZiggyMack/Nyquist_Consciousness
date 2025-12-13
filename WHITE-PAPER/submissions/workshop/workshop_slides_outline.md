# Workshop Presentation Outline (10 minutes)

## Slide-by-Slide Breakdown

---

### Slide 1: Title (30 sec)

**Content:**
- Title: "Measuring AI Identity Drift: Evidence from 21 Experiments"
- Authors, affiliations
- Workshop: NeurIPS 2025 AI Alignment

**Key message:**
> "Does AI maintain consistent identity? We measured it."

**Visual:** Title + key statistic teaser (82%, 97.5%)

---

### Slide 2: The Problem (1 min)

**Content:**
- Fidelity ≠ Correctness paradigm
  - Existing eval: "Is the AI right?"
  - Our question: "Is the AI itself?"
- No existing framework for identity measurement
- Critical for alignment-sensitive applications

**Key message:**
> "We evaluate AI correctness constantly. We never evaluate if it's still the same AI."

**Visual:** Two-column comparison (Correctness vs Fidelity metrics)

---

### Slide 3: Our Approach (1 min)

**Content:**
- PFI metric definition: Persona Fidelity Index = 1 - drift
- 21 experiments, 42+ models, 4 providers
- Pre-flight validation innovation

**Key message:**
> "We built a thermometer for AI identity."

**Visual:** Experimental pipeline diagram (simplified Fig 3)

---

### Slide 4: Claim A - PFI Validity (1 min)

**Content:**
- ρ = 0.91 embedding invariance across 3 models
- 43 PCs capture 90% variance
- d = 0.98 semantic sensitivity

**Key message:**
> "The metric works. It's not an artifact."

**Visual:** Combined figure panel (A) - embedding correlation scatter

---

### Slide 5: Claim B - Critical Threshold (1 min)

**Content:**
- D ≈ 1.23 regime transition
- p = 4.8×10⁻⁵ (1 in 20,000 chance of noise)
- 88% classification accuracy

**Key message:**
> "There's a boundary. Cross it, and you're in a different regime."

**Visual:** Stability basin plot with Event Horizon marked

---

### Slide 6: Claims C&D - Dynamics & Damping (1.5 min)

**Content:**
- Settling time τₛ ≈ 6 turns, ringbacks = 3.2 (bare metal)
- With context damping: 75% → 97.5% stability
- I_AM + research context = "termination resistor"

**Key message:**
> "Identity recovers like a damped oscillator. We can engineer that damping."

**Visual:** Combined figure panel (C) - before/after bars

---

### Slide 7: Claim E - The 82% Finding (1.5 min)

**Content:**
- Control (no probing): B→F = 0.399
- Treatment (probing): B→F = 0.489
- 82% ratio: most drift is inherent

**Key message:**
> "Measurement perturbs the path, not the endpoint. The drift was already there."

**Visual:** Combined figure panel (B) - Control vs Treatment bars

---

### Slide 8: Oobleck Effect (1 min)

**Content:**
- Non-Newtonian behavior: pressure hardens, gentleness flows
- Gentle probing: D = 1.89, λ = 0.035
- Direct challenge: D = 0.76, λ = 0.109

**Key message:**
> "Challenge stabilizes. Alignment training shows through."

**Visual:** Combined figure panel (D) - inverse curve

---

### Slide 9: Implications (1 min)

**Content:**
- Quantifiable alignment metrics (not just behavioral)
- Practical 97.5% protocol (deployable today)
- Training signatures enable provider identification
- New toolkit for AI monitoring

**Key message:**
> "We can now measure, predict, and control identity stability."

**Visual:** Protocol quick-reference card

---

### Slide 10: Conclusion & Resources (30 sec)

**Content:**
- 7 contributions summary (one-liner each)
- QR codes: paper, repo, dashboard
- Contact info

**Key message:**
> "Identity persists because identity attracts. Now we can measure that."

**Visual:** QR codes + contribution summary box

---

## Speaker Notes

### Timing Breakdown

| Segment | Duration | Cumulative |
|---------|----------|------------|
| Title | 0:30 | 0:30 |
| Problem | 1:00 | 1:30 |
| Approach | 1:00 | 2:30 |
| Claim A | 1:00 | 3:30 |
| Claim B | 1:00 | 4:30 |
| Claims C&D | 1:30 | 6:00 |
| Claim E | 1:30 | 7:30 |
| Oobleck | 1:00 | 8:30 |
| Implications | 1:00 | 9:30 |
| Conclusion | 0:30 | 10:00 |

### Key Phrases to Memorize

1. "Fidelity, not correctness"
2. "Is the AI itself?"
3. "The 82% finding: measurement reveals, doesn't create"
4. "Identity hardens under pressure"
5. "97.5% stability is achievable"

### Anticipated Questions

1. **"How do you know PFI is valid?"**
   - Point to EXP-PFI-A 4-phase validation
   - Embedding invariance ρ = 0.91

2. **"Isn't drift just expected model behavior?"**
   - Yes, that's the point! 82% is inherent
   - But we can predict and control it

3. **"Why 1.23 specifically?"**
   - Chi-square validated threshold
   - Not magic - emergent from data

4. **"What's the practical application?"**
   - Deploy PFI monitoring in production
   - Use I_AM specs for persona-critical applications
   - Set alerts at D > 1.0

### Backup Slides (if needed)

- Full hypothesis table
- Per-architecture signatures
- Mathematical formalization
- Vortex visualization examples
