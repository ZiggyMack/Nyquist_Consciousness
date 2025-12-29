# Reviewer Feedback - v4 Package

**Purpose:** Collect structured feedback from reviewers on v4 package materials.
**Version:** v4 (Run 023d IRON CLAD + Oobleck Effect)
**Date:** December 2025

---

## How to Submit Feedback

Each reviewer has their own directory. Submit feedback by creating/editing files in your directory.

### Directory Structure

```
feedback/
├── README.md              # This file
├── FEEDBACK_STATUS.json   # Aggregate status (auto-generated)
├── Claude/
│   ├── visual_requests.json   # Visual requests
│   └── content_feedback.md    # Content/editorial feedback
└── Grok/
    ├── visual_requests.json
    └── content_feedback.md
```

---

## 1. Visual Requests (`visual_requests.json`)

Request new visuals or suggest placement changes.

### Schema

```json
{
  "reviewer": "Claude",
  "version": "v4",
  "date": "2025-12-29",
  "requests": [
    {
      "type": "add",
      "visual": "new_visual.png",
      "source": "15_Oobleck_Effect",
      "pipeline": "arxiv",
      "placement": "main",
      "figure_num": 5,
      "reason": "Supports Claim E - 92% inherent drift",
      "status": "pending"
    },
    {
      "type": "move",
      "visual": "settling_curves.png",
      "from_pipeline": "workshop",
      "to_pipeline": "arxiv",
      "to_placement": "appendix",
      "reason": "Too detailed for workshop, better in full paper",
      "status": "pending"
    }
  ]
}
```

### Request Types

| Type | Description | Required Fields |
|------|-------------|-----------------|
| `add` | Add new visual to pipeline | visual, source, pipeline, placement |
| `move` | Move visual between pipelines | visual, from_pipeline, to_pipeline |
| `remove` | Remove visual from pipeline | visual, pipeline, reason |
| `replace` | Replace one visual with another | visual, replacement, pipeline |

### Status Values

- `pending` - Awaiting review
- `approved` - Will be incorporated
- `rejected` - Not accepted (with reason)
- `synced` - Already incorporated into visual_index.md

---

## 2. Content Feedback (`content_feedback.md`)

General feedback on paper content, structure, claims, etc.

### Template

```markdown
# Content Feedback - [Reviewer Name]

## Pipeline: arxiv

### Section 2.1: Framework Overview
- **Issue:** [Description]
- **Suggestion:** [What to change]
- **Priority:** High/Medium/Low

### Figure 3
- **Issue:** Caption unclear
- **Suggestion:** Add reference to Event Horizon D=0.80

## Pipeline: workshop

### Overall Structure
- **Feedback:** [Comments]
```

---

## Processing Feedback

Feedback is processed by `0_sync_viz.py`:

```bash
# View all pending feedback
py calibration/0_sync_viz.py --requests

# Process and aggregate feedback
py calibration/0_sync_viz.py --process-feedback

# Update visual_index.md with approved changes
py calibration/0_sync_viz.py --update-index
```

---

## Feedback Flow

```
1. Reviewer creates feedback files in their directory
2. Run --process-feedback to aggregate into CURRENT_VERSION.json
3. Stephen reviews and approves/rejects in CURRENT_VERSION.json
4. Run --update-index to update visual_index.md
5. Run 3_generate_pdfs.py to regenerate with new placements
```

---

*IRON CLAD Methodology: Event Horizon = 0.80 (cosine), p = 2.40e-23*
