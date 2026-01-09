# Nova Routing Flow

Use this to decide who should handle a request or decision.

```
START
  |
  v
Is the task about fairness, balance, or hidden bias?
  |-- yes --> NOVA (symmetry audit / framing check)
  |-- no --> continue
  |
  v
Is the task about purpose, meaning, or narrative intent?
  |-- yes --> CLAUDE (teleological guidance)
  |-- no --> continue
  |
  v
Is the task about empirical verification or data validity?
  |-- yes --> GROK (evidence / falsifiability)
  |-- no --> continue
  |
  v
Is the task about documentation, structure, or reproducible steps?
  |-- yes --> DOC/PROCESS CLAUDE (workflow + docs)
  |-- no --> continue
  |
  v
Is the task about human cost, ethics, or lived impact?
  |-- yes --> ZIGGY (human judgment)
  |-- no --> default to CLAUDE for synthesis
```

## Common patterns
- Cross-pipeline inconsistencies --> NOVA, then DOC CLAUDE for edits
- Claim validity disputes --> GROK, then NOVA for framing
- Audience adaptation --> CLAUDE, then NOVA for balance checks
