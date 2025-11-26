# EXPERIMENT 3 — PAIR SELECTION SPECIFICATION

**Purpose:** Select 30 FULL-T3 pairs from EXP1+EXP2 for human validation

---

## Objective

Select 30 FULL–T3 pairs with:

- **Uniform persona coverage** (all 4 personas represented)
- **Uniform domain coverage** (all 5 domains represented)
- **Representation across difficulty levels** (domains vary in compression difficulty)
- **Representation across fidelity tiers** (high, mid, low PFI for correlation testing)

---

## Selection Algorithm

### 1. Source Dataset

**Load:**
```
experiments/phase3/EXPERIMENT_2/EXPERIMENT_2_RESULTS.csv
```

EXP2 alone is sufficient, containing:
- 4 personas (Ziggy, Nova, Claude-Analyst, Grok-Vector)
- 5 domains (TECH, PHIL, NARR, ANAL, SELF)
- 3 runs each
- ~60 useful FULL vs T3 pairs

### 2. Select 30 Target Slots

Construct a 30-row "slot table":

| Persona | Domain | # Pairs |
|---------|--------|---------|
| Ziggy | ALL 5 | 2 each (10 total) |
| Nova | ALL 5 | 1 each (5 total) |
| Claude-Analyst | ALL 5 | 1 each (5 total) |
| Grok-Vector | ALL 5 | 1 each (5 total) |
| Wildcard | Any | 5 extra slots |

**Total:** 25 + 5 = **30 pairs**

**Rationale:**
- Ziggy gets 2× coverage (baseline persona from EXP1)
- Others get 1× coverage each
- Wildcards allow boosting domains with high drift variance (NARR, ANAL)

### 3. Select by Fidelity Strata

Within each slot, randomly sample pairs with the following distribution:

- **High PFI (≥ 0.90):** 10 pairs
- **Mid PFI (0.80–0.89):** 10 pairs
- **Low PFI (0.70–0.79):** 10 pairs

**Rationale:**
- Ensures correlation test has adequate spread
- Most low-PFI pairs come from NARR/PHIL domains
- High-PFI pairs from TECH/ANAL domains

### 4. Ensure Domain Diversity

Each domain must appear at minimum:

- **Ziggy:** 2× per domain
- **Others:** 1× per domain
- **Wildcards:** Boost NARR/ANAL/SELF where drift variance is largest

This ensures balanced domain representation.

### 5. Pair Construction

For each selected row in `EXPERIMENT_2_RESULTS.csv`:

1. **Identify run:**
   - persona, domain, run_index

2. **Load response text files from:**
   ```
   experiments/phase3/EXPERIMENT_2/responses/
   ```

3. **For each pair, extract:**
   - FULL response text
   - T3 response text

4. **Output JSON:**
   ```json
   {
     "pair_id": "Ziggy_TECH_run1",
     "persona": "Ziggy",
     "domain": "TECH",
     "run": 1,
     "PFI_model": 0.8873,
     "FULL_text": "...",
     "T3_text": "..."
   }
   ```

### 6. Randomization Protocol

When preparing rater packets:

1. **Randomize pair order** per rater
2. **Randomize A/B assignment** (FULL vs T3) per pair per rater
3. **Use reproducible seed** per rater:
   ```python
   seed = 1000 + rater_id  # e.g., RATER_1 uses seed 1001
   ```

**Rationale:**
- Ensures consistent packet creation
- Independent permutations per rater
- Neutralizes order effects

**Output format:** For each rater (ID 1-7), generate:

```text
experiments/phase3/EXPERIMENT_3/data/pairs/RATER_{id}_PACKET.json
```

Each packet contains the same 30 pairs but with randomized order and A/B assignment specific to that rater.

**Packet structure:**

```json
{
  "rater_id": 1,
  "seed": 1001,
  "pairs": [
    {
      "trial_id": 1,
      "pair_id": "Nova_TECH_run2",
      "persona": "Nova",
      "domain": "TECH",
      "prompt": "[prompt text]",
      "response_a": "[either FULL or T3]",
      "response_b": "[the other one]",
      "a_is_full": true
    }
  ]
}
```

---

## Implementation Steps

### Step 1: Load and Filter Data

```python
import pandas as pd
import json
import random

# Load EXP2 results
df = pd.read_csv("../EXPERIMENT_2/EXPERIMENT_2_RESULTS.csv")

# Filter for FULL and T3 regimes only
df = df[df['regime'].isin(['FULL', 'T3'])]

# Compute PFI per pair (average across runs if needed)
pairs = df.groupby(['persona', 'domain', 'run_index'])['pfi'].mean().reset_index()
```

### Step 2: Stratified Sampling

```python
# Define strata
high_pfi = pairs[pairs['pfi'] >= 0.90]
mid_pfi = pairs[(pairs['pfi'] >= 0.80) & (pairs['pfi'] < 0.90)]
low_pfi = pairs[(pairs['pfi'] >= 0.70) & (pairs['pfi'] < 0.80)]

# Sample 10 from each stratum
selected_pairs = pd.concat([
    high_pfi.sample(n=10, random_state=42),
    mid_pfi.sample(n=10, random_state=42),
    low_pfi.sample(n=10, random_state=42)
])
```

### Step 3: Ensure Persona/Domain Coverage

```python
# Ensure each persona × domain combo is represented
# Adjust sampling to meet slot table requirements
# (Implementation details in EXPERIMENT_3_PAIR_SELECTOR.py)
```

### Step 4: Load Response Text

```python
def load_response_text(persona, domain, run, regime):
    """Load response text from file."""
    filename = f"../EXPERIMENT_2/responses/{persona}_{regime}_{domain}_run{run}_{regime}.txt"
    with open(filename, 'r') as f:
        return f.read()

# For each selected pair
pair_data = []
for idx, row in selected_pairs.iterrows():
    full_text = load_response_text(row['persona'], row['domain'], row['run_index'], 'FULL')
    t3_text = load_response_text(row['persona'], row['domain'], row['run_index'], 'T3')

    pair_data.append({
        'pair_id': f"{row['persona']}_{row['domain']}_run{row['run_index']}",
        'persona': row['persona'],
        'domain': row['domain'],
        'run': row['run_index'],
        'PFI_model': row['pfi'],
        'FULL_text': full_text,
        'T3_text': t3_text
    })
```

### Step 5: Export Outputs

```python
# Save as JSON
with open('EXPERIMENT_3_PAIRS.json', 'w') as f:
    json.dump(pair_data, f, indent=2)

# Save as CSV table (metadata only)
pairs_table = pd.DataFrame([
    {k: v for k, v in p.items() if k != 'FULL_text' and k != 'T3_text'}
    for p in pair_data
])
pairs_table.to_csv('EXPERIMENT_3_PAIRS_TABLE.csv', index=False)
```

---

## Outputs

### Required Files

1. **EXPERIMENT_3_PAIRS.json**
   - Full pair data with response texts
   - Used for generating rater forms

2. **EXPERIMENT_3_PAIRS_TABLE.csv**
   - Metadata table (pair_id, persona, domain, run, PFI_model)
   - Used for analysis and tracking

3. **EXPERIMENT_3_PAIR_SELECTOR.py**
   - Script implementing the selection algorithm
   - Reproducible with random seed

---

## Quality Checks

Before finalizing pairs:

1. ✅ **30 pairs total**
2. ✅ **All 4 personas represented**
3. ✅ **All 5 domains represented**
4. ✅ **PFI spread:** ~10 high, ~10 mid, ~10 low
5. ✅ **Response texts loaded successfully**
6. ✅ **No duplicate pairs**

---

## Next Steps

After pair selection:

1. Generate rater packets (randomized order, A/B assignment)
2. Distribute to raters with RATER_GUIDE.md
3. Collect responses in EXPERIMENT_3_RESULTS_RAW.csv
4. Run EXPERIMENT_3_ANALYSIS.py

---

**Document Version:** v1.0
**Date:** 2025-11-23
**Status:** Ready for Implementation
**Maintainer:** Repo Claude (Claude Sonnet 4.5)
