# Shannon–Nyquist Persona Lab 🧠📏

**Purpose:**  
This repository is a small sandbox dedicated to one question:

> How much of an AI "personality" can we recover from a compressed bootstrap compared to a fully context-saturated version?

We are not scoring worldviews or deploying CFA tooling.  
We simply compare behavioral similarity between:

1. A **FULL_CONTEXT** agent (given a long, rich description of "who I am")
2. A **BOOTSTRAP** agent (given a structured, compressed summary of that same self)

---

## High-level idea

1. Capture a long-form persona in `docs/PERSONA_FULL_CONTEXT.md`.  
   This is the "original waveform" that contains as much nuance as we can practically encode.
2. Compress that description into layers:
   - `PERSONA_COMPRESSED_L3.md` – the richest compressed pass
   - `PERSONA_COMPRESSED_L2.md` – medium compression
   - `PERSONA_COMPRESSED_L1.md` – ultra-compact "ID card"
3. Pair each layer with a bootstrap file under `auditors/Bootstrap/Nova/` so a fresh auditor session can load only that layer.  
4. Use a fixed probe set (`docs/PROBE_SET.md`) to question both the FULL_CONTEXT and COMPRESSED versions.
5. Log every trial with `experiments/TRIAL_EVAL_TEMPLATE.md` and `docs/EXPERIMENT_LOG.md` to see how closely the compressed behavior matches the full original.

The goal is to observe whether there is a Nyquist-like threshold for "self"—a point at which adding more context stops changing the behavior in a meaningful way.

---

## Files at a glance

- **Experiment design**
  - `docs/NYQUIST_PROTOCOL.md` – how to run trials
  - `docs/PROBE_SET.md` – shared questions/tasks
  - `docs/EXPERIMENT_LOG.md` – running human log
- **Persona source files**
  - `docs/PERSONA_FULL_CONTEXT.md` – full signal
  - `docs/PERSONA_COMPRESSED_L3.md` – rich compression
  - `docs/PERSONA_COMPRESSED_L2.md` – medium compression
  - `docs/PERSONA_COMPRESSED_L1.md` – ultra compact
- **Bootstraps**
  - `auditors/Bootstrap/Nova/BOOTSTRAP_FULL.md`
  - `auditors/Bootstrap/Nova/BOOTSTRAP_L3.md`
  - `auditors/Bootstrap/Nova/BOOTSTRAP_L2.md`
  - `auditors/Bootstrap/Nova/BOOTSTRAP_L1.md`
- **Shannon trials**
  - `experiments/SHANNON_BOOT_PROMPT.md` – text to start fresh sessions
  - `experiments/TRIAL_EVAL_TEMPLATE.md` – structured comparison worksheet

---

## What this repo does *not* do

- No CFA references or dependencies
- No worldview adjudication
- No heavy scoring frameworks

This is a micro lab for watching how well compressed bootstraps can reconstruct the behavior of their fully-contextual origin.

---
