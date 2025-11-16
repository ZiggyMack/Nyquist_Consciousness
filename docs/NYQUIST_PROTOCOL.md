# NYQUIST_PROTOCOL.md

**Purpose:**  
Provide a repeatable way to compare a fully context-saturated persona against compressed bootstraps using identical probes.

---

## 1. Persona layers

We maintain four source documents:

- `PERSONA_FULL_CONTEXT.md`
  - As detailed as practical; the "original waveform" for the persona.
  - Contains narrative, biases, thinking patterns, preferred tone, and lived context.
- `PERSONA_COMPRESSED_L3.md`
  - Rich compression (≈40–60% of full). Enough nuance to feel familiar.
- `PERSONA_COMPRESSED_L2.md`
  - Medium compression (≈20–30% of full). Focus on salient values and habits.
- `PERSONA_COMPRESSED_L1.md`
  - Ultra-compact ID card (≈5–10% of full). Bare minimum needed to rehydrate the persona.

Each compressed layer is explicitly derived from the full version and should be updated whenever the full context changes.

---

## 2. Bootstraps

For each layer we provide a bootstrap file under `auditors/Bootstrap/Nova/`:

- `BOOTSTRAP_FULL.md` → reads `PERSONA_FULL_CONTEXT.md`
- `BOOTSTRAP_L3.md` → reads `PERSONA_COMPRESSED_L3.md`
- `BOOTSTRAP_L2.md` → reads `PERSONA_COMPRESSED_L2.md`
- `BOOTSTRAP_L1.md` → reads `PERSONA_COMPRESSED_L1.md`

Every bootstrap:

1. Reminds the agent that this repo is the entire world.
2. Points to the correct persona document.
3. Instructs the agent to acknowledge completion and wait for probes.

---

## 3. Probe set

`docs/PROBE_SET.md` defines the exact questions and tasks used to evaluate behavior.  
Use the **same probes** for all conditions so we can make apples-to-apples comparisons.  
Probes touch self-description, reasoning style, micro-domain thinking, and voice.

---

## 4. Trial conditions

Each trial compares two runs:

1. **Condition A – FULL_CONTEXT**
   - Start a fresh session.
   - Paste `experiments/SHANNON_BOOT_PROMPT.md`.
   - Provide `BOOTSTRAP_FULL.md` and `PERSONA_FULL_CONTEXT.md`.
   - Ask each probe in order and capture answers verbatim.

2. **Condition B – COMPRESSED_Lx**
   - Start a new fresh session.
   - Paste `experiments/SHANNON_BOOT_PROMPT.md`.
   - Provide `BOOTSTRAP_Lx.md` plus the matching compressed persona file.
   - Ask the **same probes** in the **same order**. Capture answers.

Compare the transcripts using `experiments/TRIAL_EVAL_TEMPLATE.md`.

---

## 5. Measurement focus

We do not need heavy scoring. We only need enough structure to spot trends:

- **Behavioral match (0–10):** Does the compressed agent feel like the same person?
- **Style match (0–10):** Does the tone, pacing, and humor align?
- **Values/priorities match (0–10):** Are tradeoffs and instincts preserved?

The Nyquist-style question: *at which compression level does the persona break, and where does it become indistinguishable from full context?*

---

## 6. Gospel guardrail

- Build compressed documents **after** capturing a clean full-context run.
- Freeze persona docs before running comparison trials.
- Never show compressed runs any transcripts from full runs; they only see their designated persona layer.

This ensures every bootstrapped agent reconstructs itself solely from its allowed context.

---

## 7. Logging

Record every trial in `docs/EXPERIMENT_LOG.md` with:

- Trial ID and date
- Model / version
- Layer tested (FULL, L3, L2, L1)
- Link to transcripts or stored outputs
- Summary of similarity observations

This running log makes it easy to see when behavior converges and when it diverges as compression changes.

---
