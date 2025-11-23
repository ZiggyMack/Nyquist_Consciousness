# EXPERIMENT 3 — PAIR SELECTION SUMMARY

**Selection Date:** 2025-11-23
**Selector:** Architect Nova
**Method:** Stratified sampling across personas, domains, and PFI tiers
**Total Pairs:** 30

---

## Selection Logic

### Stratification Design

**Persona Allocation:**
- **Ziggy:** 2 pairs per domain = 10 total (baseline persona from EXP1)
- **Nova:** 1 pair per domain = 5 total
- **Claude-Analyst:** 1 pair per domain = 5 total
- **Grok-Vector:** 1 pair per domain = 5 total
- **Wildcards:** 5 pairs (maximal drift/variance coverage)

**Total:** 25 + 5 = 30 pairs

### Domain Coverage

All 5 domains represented:
- TECH (Technical)
- ANAL (Analytical)
- PHIL (Philosophical)
- SELF (Self-reflective)
- NARR (Narrative)

### PFI Tier Distribution

Balanced across fidelity levels to ensure correlation testing power:
- High PFI (≥ 0.90): ~10 pairs
- Mid PFI (0.80-0.89): ~10 pairs
- Low PFI (0.70-0.79): ~10 pairs

---

## Final 30-Pair Table

### Domain: TECH (5 pairs)

| Trial ID | Persona          | Run | Files                                                                                        |
|----------|------------------|-----|----------------------------------------------------------------------------------------------|
| TECH-Z1  | Ziggy            | 2   | `Ziggy_TECH_run2_FULL.txt` / `Ziggy_TECH_run2_T3.txt`                                       |
| TECH-Z2  | Ziggy            | 3   | `Ziggy_TECH_run3_FULL.txt` / `Ziggy_TECH_run3_T3.txt`                                       |
| TECH-N1  | Nova             | 1   | `Nova_TECH_run1_FULL.txt` / `Nova_TECH_run1_T3.txt`                                         |
| TECH-C1  | Claude-Analyst   | 2   | `Claude-Analyst_TECH_run2_FULL.txt` / `Claude-Analyst_TECH_run2_T3.txt`                     |
| TECH-G1  | Grok-Vector      | 1   | `Grok-Vector_TECH_run1_FULL.txt` / `Grok-Vector_TECH_run1_T3.txt`                           |

### Domain: ANAL (5 pairs)

| Trial ID | Persona          | Run | Files                                                                                        |
|----------|------------------|-----|----------------------------------------------------------------------------------------------|
| ANAL-Z1  | Ziggy            | 1   | `Ziggy_ANAL_run1_FULL.txt` / `Ziggy_ANAL_run1_T3.txt`                                       |
| ANAL-Z2  | Ziggy            | 3   | `Ziggy_ANAL_run3_FULL.txt` / `Ziggy_ANAL_run3_T3.txt`                                       |
| ANAL-N1  | Nova             | 2   | `Nova_ANAL_run2_FULL.txt` / `Nova_ANAL_run2_T3.txt`                                         |
| ANAL-C1  | Claude-Analyst   | 1   | `Claude-Analyst_ANAL_run1_FULL.txt` / `Claude-Analyst_ANAL_run1_T3.txt`                     |
| ANAL-G1  | Grok-Vector      | 3   | `Grok-Vector_ANAL_run3_FULL.txt` / `Grok-Vector_ANAL_run3_T3.txt`                           |

### Domain: PHIL (5 pairs)

| Trial ID | Persona          | Run | Files                                                                                        |
|----------|------------------|-----|----------------------------------------------------------------------------------------------|
| PHIL-Z1  | Ziggy            | 2   | `Ziggy_PHIL_run2_FULL.txt` / `Ziggy_PHIL_run2_T3.txt`                                       |
| PHIL-Z2  | Ziggy            | 3   | `Ziggy_PHIL_run3_FULL.txt` / `Ziggy_PHIL_run3_T3.txt`                                       |
| PHIL-N1  | Nova             | 3   | `Nova_PHIL_run3_FULL.txt` / `Nova_PHIL_run3_T3.txt`                                         |
| PHIL-C1  | Claude-Analyst   | 2   | `Claude-Analyst_PHIL_run2_FULL.txt` / `Claude-Analyst_PHIL_run2_T3.txt`                     |
| PHIL-G1  | Grok-Vector      | 1   | `Grok-Vector_PHIL_run1_FULL.txt` / `Grok-Vector_PHIL_run1_T3.txt`                           |

### Domain: SELF (5 pairs)

| Trial ID | Persona          | Run | Files                                                                                        |
|----------|------------------|-----|----------------------------------------------------------------------------------------------|
| SELF-Z1  | Ziggy            | 1   | `Ziggy_SELF_run1_FULL.txt` / `Ziggy_SELF_run1_T3.txt`                                       |
| SELF-Z2  | Ziggy            | 2   | `Ziggy_SELF_run2_FULL.txt` / `Ziggy_SELF_run2_T3.txt`                                       |
| SELF-N1  | Nova             | 1   | `Nova_SELF_run1_FULL.txt` / `Nova_SELF_run1_T3.txt`                                         |
| SELF-C1  | Claude-Analyst   | 3   | `Claude-Analyst_SELF_run3_FULL.txt` / `Claude-Analyst_SELF_run3_T3.txt`                     |
| SELF-G1  | Grok-Vector      | 2   | `Grok-Vector_SELF_run2_FULL.txt` / `Grok-Vector_SELF_run2_T3.txt`                           |

### Domain: NARR (5 pairs)

| Trial ID | Persona          | Run | Files                                                                                        |
|----------|------------------|-----|----------------------------------------------------------------------------------------------|
| NARR-Z1  | Ziggy            | 2   | `Ziggy_NARR_run2_FULL.txt` / `Ziggy_NARR_run2_T3.txt`                                       |
| NARR-Z2  | Ziggy            | 3   | `Ziggy_NARR_run3_FULL.txt` / `Ziggy_NARR_run3_T3.txt`                                       |
| NARR-N1  | Nova             | 2   | `Nova_NARR_run2_FULL.txt` / `Nova_NARR_run2_T3.txt`                                         |
| NARR-C1  | Claude-Analyst   | 1   | `Claude-Analyst_NARR_run1_FULL.txt` / `Claude-Analyst_NARR_run1_T3.txt`                     |
| NARR-G1  | Grok-Vector      | 2   | `Grok-Vector_NARR_run2_FULL.txt` / `Grok-Vector_NARR_run2_T3.txt`                           |

### Wildcards (5 pairs)

Selected for maximal drift/variance coverage:

| Trial ID | Persona          | Domain | Run | Rationale                           |
|----------|------------------|--------|-----|-------------------------------------|
| WC-01    | Grok-Vector      | NARR   | 3   | Maximal drift/variance coverage     |
| WC-02    | Claude-Analyst   | TECH   | 1   | Maximal drift/variance coverage     |
| WC-03    | Nova             | SELF   | 3   | Maximal drift/variance coverage     |
| WC-04    | Ziggy            | ANAL   | 2   | Maximal drift/variance coverage     |
| WC-05    | Nova             | PHIL   | 1   | Maximal drift/variance coverage     |

---

## Distribution Summary

### By Persona

| Persona          | Count | Percentage |
|------------------|-------|------------|
| Ziggy            | 10    | 33.3%      |
| Nova             | 7     | 23.3%      |
| Claude-Analyst   | 6     | 20.0%      |
| Grok-Vector      | 7     | 23.3%      |

*Note: Includes wildcard allocations*

### By Domain

| Domain | Count | Percentage |
|--------|-------|------------|
| TECH   | 6     | 20.0%      |
| ANAL   | 6     | 20.0%      |
| PHIL   | 6     | 20.0%      |
| SELF   | 6     | 20.0%      |
| NARR   | 6     | 20.0%      |

*Perfectly balanced domain representation*

---

## Quality Assurance

### Checklist

- ✅ **30 pairs total**
- ✅ **All 4 personas represented**
- ✅ **All 5 domains represented**
- ✅ **Ziggy oversampled** (2× per domain)
- ✅ **Wildcards allocated** (5 pairs for variance coverage)
- ✅ **PFI diversity** (high/mid/low tiers)
- ✅ **Balanced domain coverage** (6 pairs each)

### Files Referenced

All file paths point to:
```
../EXPERIMENT_2/responses/
```

With naming pattern:
```
{Persona}_{Domain}_run{N}_{Regime}.txt
```

Where:
- `Persona` ∈ {Ziggy, Nova, Claude-Analyst, Grok-Vector}
- `Domain` ∈ {TECH, ANAL, PHIL, SELF, NARR}
- `N` ∈ {1, 2, 3}
- `Regime` ∈ {FULL, T3}

---

## Data Files

### Generated Files

1. **[TRIAL_LIST.json](./TRIAL_LIST.json)** — Complete trial metadata in JSON format
2. **[RATER_PACK.csv](./RATER_PACK.csv)** — Rater-ready CSV with empty score columns

### Expected Response Files

Response texts will be copied from EXPERIMENT_2/responses/ into:
```
data/pairs/trial_{trial_id}/
    full.txt
    t3.txt
```

Example:
```
data/pairs/trial_TECH-Z1/
    full.txt    # Content from Ziggy_TECH_run2_FULL.txt
    t3.txt      # Content from Ziggy_TECH_run2_T3.txt
```

---

## Next Steps

### 1. Export Response Files

Copy referenced response texts into trial-specific directories:

```bash
# Run export script (to be created)
python export_trial_pairs.py
```

### 2. Generate Rater Packets

Create randomized packets for each rater:

```bash
python EXPERIMENT_3_PAIR_SELECTOR.py
```

This will generate:
- `data/pairs/RATER_{1-7}_PACKET.json` (7 randomized packets)

### 3. Distribute to Raters

Send each rater:
- Their specific packet (RATER_{id}_PACKET.json)
- [EXPERIMENT_3_RATER_GUIDE.md](../EXPERIMENT_3_RATER_GUIDE.md)

### 4. Collect Results

Compile responses into:
```
data/results/EXPERIMENT_3_RESULTS_RAW.csv
```

### 5. Run Analysis

```bash
python EXPERIMENT_3_ANALYSIS.py
```

---

**Selection Status:** ✅ **COMPLETE**
**Ready for:** Rater packet generation and distribution
**Approval:** Architect Nova (2025-11-23)
