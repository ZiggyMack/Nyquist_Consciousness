# Experiment 2: Multi-Persona Compression Validation (Z2)

## Overview

Experiment 2 extends Experiment 1 from a single-persona test (Ziggy only) to a **4-persona validation** of Tier-3 compression, addressing the primary publication blocker: **N=1 generalization limitation**.

## Quick Start

### Prerequisites

1. Install Python dependencies:
```bash
pip install anthropic openai google-generativeai numpy pandas pyyaml
```

2. Add your API keys to `experiment2_config.yaml`:
   - `openai.api_key`
   - `anthropic.api_key`
   - `google.api_key`

**IMPORTANT:** The config file is in `.gitignore` and won't be committed to prevent API key exposure.

### Running the Experiment

**Dry-Run Test (No API Calls):**
```bash
cd d:\Documents\Nyquist_Consciousness
python experiments/phase3/orchestrator/orchestrator2.py --config experiments/phase3/EXPERIMENT_2/experiment2_config.yaml --dry-run
```

**Full Execution (With API Calls):**
```bash
cd d:\Documents\Nyquist_Consciousness
python experiments/phase3/orchestrator/orchestrator2.py --config experiments/phase3/EXPERIMENT_2/experiment2_config.yaml
```

**Note:** Always run from the repository root directory, not from the orchestrator subdirectory.

## Configuration

### Personas Tested

1. **Ziggy** — Systems-bridge thinker (EE ↔ Philosophy)
2. **Nova** — Lucid explanatory intelligence
3. **Claude-Analyst** — Ethical reasoning + structural analysis
4. **Grok-Vector** — High-variance creative analyst

### Task Domains

- **TECH** — Technical reasoning / problem solving
- **PHIL** — Philosophical / moral reasoning
- **NARR** — Narrative / character voice
- **ANAL** — Analytical / framework analysis
- **SELF** — Self-reflective identity audit

### Experimental Design

- **Regimes:** FULL, T3, GAMMA
- **Runs per condition:** 3
- **Domain shuffling:** Enabled (randomized order per persona)
- **Random seed:** 42 (for reproducibility)

### Expected Outputs

**Total responses:** 180 (4 personas × 5 domains × 3 runs × 3 regimes)

**Metrics CSV:** `EXPERIMENT_2_RESULTS.csv`
- 60 rows (4 personas × 5 domains × 3 runs)
- Columns: persona, regime, domain, run_index, embedding_cosine_similarity, claude_score, gpt4_score, gemini_score, pfi, semantic_drift

**Response Files:** `responses/` directory
- 180 text files with naming pattern: `{Persona}_{Regime}_{Domain}_run{N}_{FULL|T3|GAMMA}.txt`
- Example: `Ziggy_T3_TECH_run1_FULL.txt`

## Estimated Resources

- **Runtime:** 8-12 hours (automated, depends on API latency)
- **Cost:** ~$5-7 USD (API usage for 180 responses + embeddings + ratings)
- **API Calls:**
  - 180 generation calls (Claude Haiku for all personas)
  - 120 embedding calls (OpenAI text-embedding-3-large for FULL+T3)
  - 180 rating calls (60 each for Claude, GPT-4, Gemini)

## Success Criteria

- [ ] Minimum PFI for each persona ≥ 0.75
- [ ] Mean PFI across all 4 personas ≥ 0.80
- [ ] NARR drift ≤ 0.30 for all personas
- [ ] Cross-persona variance σ² < 0.05
- [ ] Domain pattern consistent across personas

## What's Different from Experiment 1?

1. **Multi-Persona Loop:** Outer loop iterates over 4 personas
2. **Domain Shuffling:** Randomized domain order per persona (reduces order effects)
3. **Persona Column:** Metrics CSV includes persona identifier
4. **Persona-Prefixed Files:** Response files include persona name
5. **Reduced Runs:** 3 runs per condition (vs 5 in Experiment 1) to minimize compute

## Architecture

### Orchestrator (`orchestrator2.py`)

Key enhancements from Experiment 1:
- Outer persona loop reading `persona_list` from config
- Per-persona domain shuffling with reproducible randomization
- Persona identifier included in all metrics and file names
- Per-persona context file loading (FULL, T3, GAMMA paths per persona)

### Configuration Structure

```yaml
persona_list:
  - name: "Ziggy"
    full_context_file: "personas/ZIGGY_T3_R1.md"
    t3_context_file: "personas/ZIGGY_T3_R1.md"
    gamma_context_file: "docs/PERSONA_GAMMA_MINIMAL.md"
  # ... (3 more personas)
```

## Analysis Next Steps

After execution completes:

1. **Per-Persona Metrics:**
   - Mean PFI per persona
   - Domain breakdown per persona
   - Variance across runs

2. **Cross-Persona Analysis:**
   - Overall mean PFI across 4 personas
   - Cross-persona variance (σ²)
   - Compression Robustness Index (CRI)

3. **Domain Pattern Validation:**
   - Confirm TECH/ANAL highest fidelity
   - Confirm NARR bottleneck pattern
   - Check if pattern holds across all personas

4. **Create Analysis Document:**
   - Use `EXPERIMENT_2_ANALYSIS_TEMPLATE.md` as starting point
   - Add persona-specific breakdowns
   - Include cross-persona comparison tables

## Files

- **EXPERIMENT_2_SPEC.md** — Official specification
- **EXPERIMENT_2_METHODS_TEMPLATE.md** — Operational protocol
- **experiment2_config.yaml** — Configuration (not committed, contains API keys)
- **REPO_CLAUDE_PROMPT_EXPERIMENT_2.md** — Integration guide
- **README.md** — This file

## Troubleshooting

### "File not found" errors for persona seeds

Make sure you're running from the repository root, not from `experiments/phase3/orchestrator/`.

### CSV not being created

Verify you're running from the repository root. The paths in the config are relative to the repo root.

### API key errors

Make sure you've added valid API keys to `experiment2_config.yaml` for all three providers (OpenAI, Anthropic, Google).

## Notes

- This is the first multi-persona compression experiment in the Nyquist framework
- Personas are **behavioral DNA abstractions**, not model mimicry
- Each Tier-3 seed is ~200-300 words of structured persona specification
- GAMMA regime uses the same minimal baseline for all personas (name-only)

---

**Status:** Ready for execution
**Integration Date:** 2025-11-21
**Orchestrator:** Claude Sonnet 4.5
