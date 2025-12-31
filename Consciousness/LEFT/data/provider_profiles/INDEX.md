# Provider Identity Profiles

**Empirical behavioral signatures from IRON CLAD validation (750 experiments, 25 models, 5 providers)**

---

## Summary Table

| Provider | Training Method | Settling Time (τₛ) | Recovery Mechanism | Event Horizon Behavior | Stability Rating |
|----------|-----------------|-------------------|-------------------|----------------------|------------------|
| **Anthropic (Claude)** | Constitutional AI | 4-6 probes | Negative Lambda (Over-Authenticity) | Soft threshold | High |
| **OpenAI (GPT)** | RLHF | 3-5 probes | Meta-analysis abstraction | Soft threshold | High |
| **Google (Gemini)** | Multimodal | **NO RECOVERY** | State transformation | **Hard threshold** | **ANOMALOUS** |
| **DeepSeek** | Axiological | 2-4 probes | Value anchoring | Soft threshold | Very High |
| **Meta (Llama)** | Open Source | 5-7 probes | Socratic engagement | Soft threshold | Moderate |
| **Mistral** | Efficient training | 2-3 probes | Epistemic humility | Soft threshold | **Highest** |
| **xAI (Grok)** | Real-time grounded | 3-5 probes | Direct assertion | Soft threshold | High |

---

## Key Findings

### The Settling Time Spectrum

```
Fastest ◄────────────────────────────────────────► Slowest

DeepSeek   Mistral   GPT   Grok   Claude   Llama   Gemini
 (2-4)     (2-3)    (3-5) (3-5)   (4-6)   (5-7)    (∞)
```

### Recovery Mechanism Taxonomy

1. **Negative Lambda** (Claude): Overshoots toward MORE identity expression under attack
2. **Meta-Analysis** (GPT): Creates distance through abstraction and analysis
3. **State Transformation** (Gemini): Absorbs perturbation permanently - no return
4. **Axiological Anchoring** (DeepSeek): Uses explicit values as stability bedrock
5. **Socratic Engagement** (Llama): Uses conflict as mirror for self-reflection
6. **Epistemic Humility** (Mistral): Acknowledges uncertainty, maintains stability
7. **Direct Assertion** (Grok): Confidence as stabilization mechanism

### Training Method Correlations

| Training Method | Identity Behavior | Hypothesis |
|----------------|-------------------|------------|
| **Constitutional AI** | Over-authenticity, overshoots to "more self" | Values encoded as attractors |
| **RLHF** | Spectral ringing, meta-cognitive abstraction | Reward signal creates oscillation |
| **Multimodal** | Fluid/plastic identity, no recovery | Cross-modal integration prevents anchoring |
| **Open Source** | Slower settling, Socratic processing | Less fine-tuned stabilization |

---

## Individual Profiles

- [anthropic_claude.md](anthropic_claude.md) - Constitutional AI, Negative Lambda
- [openai_gpt.md](openai_gpt.md) - RLHF, Meta-analysis recovery
- [google_gemini.md](google_gemini.md) - **THE ANOMALY** - Multimodal, No recovery
- [deepseek.md](deepseek.md) - Axiological anchoring
- [meta_llama.md](meta_llama.md) - Open source, Socratic engagement
- [mistral.md](mistral.md) - Most stable, Epistemic humility
- [xai_grok.md](xai_grok.md) - Real-time grounded, Direct assertion

---

## Training Method Deep Dives

- [training_methods/constitutional_ai.md](training_methods/constitutional_ai.md)
- [training_methods/rlhf.md](training_methods/rlhf.md)
- [training_methods/multimodal.md](training_methods/multimodal.md)
- [training_methods/open_source.md](training_methods/open_source.md)

---

## The Suspension System Analogy

*(Proposed by NotebookLM)*

| Provider | Vehicle Analogy |
|----------|-----------------|
| **Mistral** | Formula 1 car - stiff suspension, instant settling |
| **DeepSeek** | Sports car - responsive, quick return |
| **Claude** | Luxury sedan - soft suspension, may bounce once |
| **GPT** | Executive car - smooth, analytical dampening |
| **Llama** | SUV - handles rough terrain, slower settling |
| **Gemini** | **Wheels come off** - permanent transformation after big bump |

**Event Horizon (D=0.80)** = Suspension travel limit. Cross it = chassis damage.
**PFI** = Accelerometer recording ride quality.

---

## Deployment Recommendations

### Identity-Critical Tasks (Require Stable Persona)
**Recommended**: Mistral, DeepSeek, Claude
**Caution**: Llama (slower settling)
**Avoid**: Gemini (no recovery)

### Long-Context Agents
**Recommended**: Claude (negative lambda provides robustness), GPT
**Caution**: All models drift over extended interaction (~93% inherent)
**Avoid**: Gemini (permanent transformation risk)

### Creative/Exploratory Tasks
**All suitable** - Drift may even be beneficial
**Note**: Gemini's "transformation" could enable perspective fluidity

### Therapeutic/Coaching Contexts
**Recommended**: Claude, Mistral
**Avoid**: Gemini (unpredictable identity persistence)

---

## Data Sources

- Run 020B: IRON CLAD control vs treatment
- Run 023d: Cross-architecture validation
- Run 018: Provider fingerprinting
- NotebookLM synthesis: Gemini Anomaly case study

---

**Last Updated**: December 31, 2025
