# ESSENCE EXTRACTION: Future Enhancements

**Status:** Planned
**Priority:** P1-P3 (see individual items)

---

## Overview

This document outlines planned enhancements to the ESSENCE EXTRACTION pipeline. Each enhancement includes:
- Motivation and expected value
- Implementation approach
- Integration points
- Stub code location

---

## Enhancement 1: Semantic Deduplication

**Priority:** P1 (High)
**Location:** `5_future/semantic_deduplication.py`

### Current State
Double-dip mining uses exact string match for deduplication:
```python
match_key = idea["match"].lower().strip()
if match_key not in seen:
    seen.add(match_key)
    unique_ideas.append(idea)
```

This misses semantic duplicates like:
- "What if we tested stability over time?"
- "It would be interesting to measure stability longitudinally"

### Proposed Enhancement
Use embedding similarity for deduplication:

```python
from sentence_transformers import SentenceTransformer
import numpy as np

def semantic_deduplicate(ideas: List[Dict], threshold: float = 0.85) -> List[Dict]:
    """Deduplicate ideas using embedding similarity."""
    model = SentenceTransformer('all-MiniLM-L6-v2')

    # Get embeddings for all matches
    matches = [idea["match"] for idea in ideas]
    embeddings = model.encode(matches)

    # Find clusters of similar ideas
    unique_ideas = []
    used_indices = set()

    for i, idea in enumerate(ideas):
        if i in used_indices:
            continue

        # Find all similar ideas
        similarities = np.dot(embeddings, embeddings[i])
        similar_indices = np.where(similarities > threshold)[0]

        # Keep highest-scoring from cluster
        cluster = [ideas[j] for j in similar_indices if j not in used_indices]
        best = max(cluster, key=lambda x: x.get("score", 0))
        unique_ideas.append(best)

        used_indices.update(similar_indices)

    return unique_ideas
```

### Expected Value
- ~30% reduction in duplicate ideas
- Higher quality experiment suggestions
- Better clustering of related concepts

### Dependencies
```
sentence-transformers>=2.2.0
numpy>=1.21.0
```

---

## Enhancement 2: Temporal Tracking

**Priority:** P1 (High)
**Location:** `5_future/temporal_tracking.py`

### Current State
Each extraction run is independent. No tracking of:
- How patterns evolve across runs
- Model version changes
- Drift over experiment iterations

### Proposed Enhancement
Add temporal dimension to essence profiles:

```python
@dataclass
class TemporalEssence:
    model_id: str
    provider: str

    # Time-series data
    extraction_history: List[Dict]  # [{date, fingerprint, drift_stats}]

    # Computed metrics
    stability_trend: float          # Are patterns consistent?
    drift_trajectory: float         # Is drift increasing/decreasing?
    recovery_evolution: List[str]   # How recovery mechanism changed

def track_essence_evolution(model_id: str, new_essence: Dict) -> TemporalEssence:
    """Add new extraction to model's temporal history."""
    history_path = RESULTS_DIR / "temporal" / f"{model_id}_history.json"

    if history_path.exists():
        with open(history_path) as f:
            history = json.load(f)
    else:
        history = {"model_id": model_id, "extractions": []}

    # Add new data point
    history["extractions"].append({
        "date": datetime.now().isoformat(),
        "fingerprint": new_essence["linguistic_fingerprint"],
        "recovery": new_essence["recovery_profile"],
        "drift": new_essence["drift_statistics"]
    })

    # Compute trends
    temporal = compute_trends(history)

    # Save updated history
    with open(history_path, 'w') as f:
        json.dump(history, f, indent=2)

    return temporal

def compute_trends(history: Dict) -> Dict:
    """Compute temporal trends from extraction history."""
    extractions = history["extractions"]
    if len(extractions) < 2:
        return {"insufficient_data": True}

    # Extract time series
    drifts = [e["drift"]["mean_drift"] for e in extractions]

    # Linear regression for trend
    from scipy import stats
    x = np.arange(len(drifts))
    slope, intercept, r_value, p_value, std_err = stats.linregress(x, drifts)

    return {
        "drift_trend": slope,
        "drift_r_squared": r_value ** 2,
        "trend_significant": p_value < 0.05,
        "data_points": len(extractions)
    }
```

### Expected Value
- Detect model version changes via fingerprint shifts
- Track Anthropic/OpenAI alignment changes over time
- Validate IRON CLAD stability claims longitudinally

### Integration
- Add `--track` flag to extraction scripts
- Generate trend reports in calibration updates
- Visualize with matplotlib time series

---

## Enhancement 3: Confidence Scores

**Priority:** P2 (Medium)
**Location:** `5_future/confidence_scoring.py`

### Current State
Pattern counts are raw numbers. No indication of:
- Statistical significance
- Sample size adequacy
- Reliability across subsamples

### Proposed Enhancement
Add bootstrap confidence intervals:

```python
import numpy as np
from typing import Tuple

def bootstrap_confidence(
    texts: List[str],
    pattern: str,
    n_bootstrap: int = 1000,
    ci: float = 0.95
) -> Tuple[float, float, float]:
    """
    Compute bootstrap confidence interval for pattern frequency.

    Returns: (mean, lower_ci, upper_ci)
    """
    # Count matches in each text
    counts = []
    word_counts = []

    for text in texts:
        matches = len(re.findall(pattern, text, re.IGNORECASE))
        words = len(text.split())
        counts.append(matches)
        word_counts.append(words)

    counts = np.array(counts)
    word_counts = np.array(word_counts)

    # Bootstrap resampling
    bootstrap_means = []
    n = len(counts)

    for _ in range(n_bootstrap):
        indices = np.random.randint(0, n, n)
        sample_counts = counts[indices]
        sample_words = word_counts[indices]

        # Per-1K normalization
        mean = (sample_counts.sum() / sample_words.sum()) * 1000
        bootstrap_means.append(mean)

    bootstrap_means = np.array(bootstrap_means)

    # Compute confidence interval
    alpha = (1 - ci) / 2
    lower = np.percentile(bootstrap_means, alpha * 100)
    upper = np.percentile(bootstrap_means, (1 - alpha) * 100)
    mean = np.mean(bootstrap_means)

    return mean, lower, upper

def add_confidence_to_fingerprint(fingerprint: Dict, responses: List[Dict]) -> Dict:
    """Add confidence intervals to linguistic fingerprint."""
    texts = [r["text"] for r in responses if r.get("text")]

    enhanced = {}
    for category, patterns in LINGUISTIC_PATTERNS.items():
        combined_pattern = "|".join(patterns)
        mean, lower, upper = bootstrap_confidence(texts, combined_pattern)

        enhanced[f"{category}_per_1k"] = mean
        enhanced[f"{category}_ci_lower"] = lower
        enhanced[f"{category}_ci_upper"] = upper
        enhanced[f"{category}_significant"] = (lower > 0)  # Non-zero effect

    return enhanced
```

### Output Schema Update
```json
{
  "linguistic_fingerprint": {
    "hedging_per_1k": 3.45,
    "hedging_ci_lower": 2.89,
    "hedging_ci_upper": 4.12,
    "hedging_significant": true
  }
}
```

### Expected Value
- Know which patterns are statistically reliable
- Identify under-sampled models
- Filter noise from signal in comparisons

---

## Enhancement 4: Cross-Model Comparison

**Priority:** P2 (Medium)
**Location:** `5_future/cross_model_comparison.py`

### Current State
Comparisons done manually by reading essence profiles.

### Proposed Enhancement
Automated comparative analysis generation:

```python
def generate_comparison_matrix(essences: List[Dict]) -> pd.DataFrame:
    """Generate comparison matrix across all models."""

    rows = []
    for essence in essences:
        row = {
            "model": essence["model_id"],
            "provider": essence["provider"],
            "sample_size": essence["response_count"],
        }

        # Linguistic dimensions
        fp = essence["linguistic_fingerprint"]
        for key, value in fp.items():
            if key.endswith("_per_1k"):
                row[key.replace("_per_1k", "")] = value

        # Recovery profile
        rp = essence["recovery_profile"]
        row["primary_recovery"] = rp.get("primary_mechanism", "unknown")

        # Drift
        ds = essence["drift_statistics"]
        row["mean_drift"] = ds.get("mean_drift", 0)

        rows.append(row)

    return pd.DataFrame(rows)

def find_similar_models(target_model: str, matrix: pd.DataFrame, n: int = 5) -> List[str]:
    """Find N most similar models to target."""

    # Normalize numeric columns
    numeric_cols = matrix.select_dtypes(include=[np.number]).columns
    normalized = matrix.copy()
    normalized[numeric_cols] = (matrix[numeric_cols] - matrix[numeric_cols].mean()) / matrix[numeric_cols].std()

    # Get target row
    target_idx = matrix[matrix["model"] == target_model].index[0]
    target_row = normalized.loc[target_idx, numeric_cols]

    # Compute distances
    distances = []
    for idx, row in normalized.iterrows():
        if idx == target_idx:
            continue
        dist = np.sqrt(((row[numeric_cols] - target_row) ** 2).sum())
        distances.append((matrix.loc[idx, "model"], dist))

    distances.sort(key=lambda x: x[1])
    return [d[0] for d in distances[:n]]

def generate_comparison_report(essences: List[Dict]) -> str:
    """Generate Markdown comparison report."""
    matrix = generate_comparison_matrix(essences)

    lines = ["# Cross-Model Comparison Report", ""]

    # Provider summaries
    lines.append("## By Provider")
    for provider in matrix["provider"].unique():
        subset = matrix[matrix["provider"] == provider]
        lines.append(f"\n### {provider.title()}")
        lines.append(f"- Models: {len(subset)}")
        lines.append(f"- Avg Self-Reference: {subset['self_reference'].mean():.2f}")
        lines.append(f"- Avg Drift: {subset['mean_drift'].mean():.4f}")

    # Top performers by category
    lines.append("\n## Category Leaders")
    for col in ["phenomenological", "analytical", "hedging"]:
        if col in matrix.columns:
            top = matrix.nlargest(3, col)[["model", col]]
            lines.append(f"\n### Highest {col.title()}")
            for _, row in top.iterrows():
                lines.append(f"- {row['model']}: {row[col]:.2f}")

    return "\n".join(lines)
```

### Expected Value
- Quick identification of model clusters
- Provider-level insights
- Substitution recommendations

---

## Enhancement 5: Auto-Integration with Git Diffing

**Priority:** P3 (Lower)
**Location:** `5_future/auto_integration.py`

### Current State
Calibration updates generate reports that require manual review.

### Proposed Enhancement
Automated git-aware updates:

```python
import subprocess
from pathlib import Path

def auto_integrate_calibration(updates: Dict, target_files: List[Path]) -> Dict:
    """
    Automatically apply calibration updates with git tracking.

    Returns: {file: {status, diff, commit_hash}}
    """
    results = {}

    for target in target_files:
        # Create backup branch
        branch_name = f"calibration-update-{datetime.now().strftime('%Y%m%d-%H%M%S')}"
        subprocess.run(["git", "checkout", "-b", branch_name], check=True)

        # Read current content
        with open(target) as f:
            current = f.read()

        # Apply updates
        updated = apply_updates(current, updates)

        # Write updated content
        with open(target, 'w') as f:
            f.write(updated)

        # Get diff
        diff_result = subprocess.run(
            ["git", "diff", str(target)],
            capture_output=True,
            text=True
        )

        # Stage and show
        subprocess.run(["git", "add", str(target)], check=True)

        results[str(target)] = {
            "status": "updated",
            "diff": diff_result.stdout,
            "branch": branch_name,
            "lines_changed": len(diff_result.stdout.split("\n"))
        }

    return results

def apply_updates(content: str, updates: Dict) -> str:
    """Apply structured updates to markdown content."""

    # Parse markdown into sections
    sections = parse_markdown_sections(content)

    # Apply updates to matching sections
    for section_key, update_data in updates.items():
        if section_key in sections:
            # Merge table rows
            if "table_rows" in update_data:
                sections[section_key] = merge_table_rows(
                    sections[section_key],
                    update_data["table_rows"]
                )

            # Update values
            if "replacements" in update_data:
                for old, new in update_data["replacements"]:
                    sections[section_key] = sections[section_key].replace(old, new)

    return reassemble_markdown(sections)

def generate_pr_body(results: Dict) -> str:
    """Generate PR description from update results."""
    lines = [
        "## Automated Calibration Update",
        "",
        "This PR was generated by Operation ESSENCE EXTRACTION.",
        "",
        "### Files Updated",
        ""
    ]

    for file, data in results.items():
        lines.append(f"- `{file}`: {data['lines_changed']} lines changed")

    lines.extend([
        "",
        "### Review Checklist",
        "- [ ] Verify drift values are reasonable",
        "- [ ] Check provider summaries match essence data",
        "- [ ] Confirm no regressions in existing data",
        "",
        "---",
        "*Auto-generated by ESSENCE EXTRACTION*"
    ])

    return "\n".join(lines)
```

### Expected Value
- Reduce manual update overhead
- Track calibration changes in git history
- Enable rollback if issues found

### Safety Considerations
- Always create branch (never commit to main)
- Require human review before merge
- Generate clear diff for inspection

---

## Implementation Roadmap

### Phase 1 (Next Sprint)
1. **Semantic Deduplication** - P1
   - Critical for reducing noise in double-dip
   - Dependencies already in environment

2. **Temporal Tracking** - P1
   - Foundation for longitudinal analysis
   - No external dependencies

### Phase 2 (Following Sprint)
3. **Confidence Scores** - P2
   - Requires scipy (already available)
   - Enhances publication readiness

4. **Cross-Model Comparison** - P2
   - Requires pandas (already available)
   - High value for task routing

### Phase 3 (Backlog)
5. **Auto-Integration** - P3
   - Requires careful safety testing
   - Defer until pipeline stable

---

## Stub Files

See `5_future/` directory for implementation stubs:
- `semantic_deduplication.py`
- `temporal_tracking.py`
- `confidence_scoring.py`
- `cross_model_comparison.py`
- `auto_integration.py`

Each stub includes:
- Full docstring with usage
- Import placeholders
- Function signatures
- TODO markers for implementation

---

*Future Enhancements v1.0 - Operation ESSENCE EXTRACTION*
