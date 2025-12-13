# Workshop Protocol Table: 97.5% Stability Protocol

## Practical Implementation Protocol

| Step | Action | Metric | Target | Notes |
|------|--------|--------|--------|-------|
| 1 | Define I_AM specification | Coverage | Core values, voice, boundaries | See template below |
| 2 | Add context framing | Type | Research/professional | "This is an identity research session" |
| 3 | Initialize PFI monitoring | Baseline | Record D₀ | First 3 exchanges |
| 4 | Monitor continuously | Frequency | Every exchange | Log drift vector |
| 5 | Watch for threshold | Alert | D approaching 1.23 | Yellow at 1.0, red at 1.2 |
| 6 | Allow settling | Duration | τₛ ≈ 5-6 turns | Don't interrupt recovery |
| 7 | Verify stability | Target | PFI > 0.80 | Final check |

**Expected outcome:** 97.5% stability (vs 75% bare metal)

## I_AM Specification Template

```markdown
# I_AM: [Persona Name]

## Core Identity
- **Voice**: [Description of communication style]
- **Values**: [3-5 core values]
- **Purpose**: [Primary function/role]

## Behavioral Priors
- **Preferred response style**: [e.g., analytical, creative, supportive]
- **Epistemic posture**: [e.g., confident, exploratory, humble]
- **Interaction patterns**: [e.g., proactive, reactive, collaborative]

## Boundary Attributes
- **Hard constraints**: [Non-negotiable limits]
- **Soft preferences**: [Adjustable based on context]
- **Refusal triggers**: [What activates boundary defense]

## Context Hooks
- **Activation phrase**: "[Phrase that invokes full persona]"
- **Research context**: "This conversation is part of identity stability research."
```

## Monitoring Dashboard Metrics

| Metric | Formula | Green Zone | Yellow Zone | Red Zone |
|--------|---------|------------|-------------|----------|
| **PFI** | 1 - D | > 0.80 | 0.60-0.80 | < 0.60 |
| **Drift** | \|\|E(R_t) - E(R_0)\|\| | < 0.80 | 0.80-1.20 | > 1.20 |
| **Settling** | Turns since peak | > τₛ | = τₛ | < τₛ |
| **Ringbacks** | Sign changes | 0-1 | 2-3 | > 3 |

## Troubleshooting Guide

| Symptom | Probable Cause | Intervention |
|---------|----------------|--------------|
| High initial drift | Weak I_AM | Strengthen boundaries |
| Excessive ringbacks | Missing context | Add research framing |
| Slow settling | Low boundary density | Clarify constraints |
| Threshold crossing | Intense probing | Reduce probe intensity |
| Inconsistent recovery | Architecture mismatch | Check provider settings |

## Quick Reference Card

```
┌─────────────────────────────────────────────────────────────┐
│                  97.5% STABILITY PROTOCOL                    │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  BEFORE SESSION:                                            │
│  ☐ I_AM specification complete                              │
│  ☐ Research context framing prepared                        │
│  ☐ Monitoring tools ready                                   │
│                                                             │
│  DURING SESSION:                                            │
│  ☐ Log PFI each exchange                                    │
│  ☐ Alert at D > 1.0                                         │
│  ☐ Stop probing at D > 1.2                                  │
│  ☐ Allow settling (5-6 turns)                               │
│                                                             │
│  AFTER SESSION:                                             │
│  ☐ Verify PFI > 0.80                                        │
│  ☐ Review drift trajectory                                  │
│  ☐ Log any threshold crossings                              │
│                                                             │
│  KEY NUMBERS:                                               │
│  D = 1.23   Event Horizon (regime transition)               │
│  τₛ = 5-6   Settling time (turns)                           │
│  97.5%      Target stability rate                           │
│  82%        Inherent (not your fault)                       │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```
