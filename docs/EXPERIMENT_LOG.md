# Shannon–Nyquist Trial Log

Use this file to record every comparison run. Add rows as trials complete.

| Trial | Date | Baseline Trial | Model / Version | Layer (FULL/L3/L2/L1) | Probe Set Version | Outcome Summary | Notes / Links |
|-------|------|----------------|-----------------|------------------------|-------------------|-----------------|---------------|
| 1A    | 2025-01-17 | 1A (self) | Claude Sonnet 4.5 | FULL | 1.0 | Baseline established | experiments/Trial_01_FULL_vs_L1_Evaluation.md |
| 1B    | 2025-01-17 | 1A | Claude Sonnet 4.5 | L1 | 1.0 | 95% compression EXCEEDS Nyquist threshold. Identity confused, personality signature lost, structural thinking collapsed. Behavioral: 6/10, Style: 4/10, Values: 7/10. Continuity: NO. | experiments/Trial_01_FULL_vs_L1_Evaluation.md |
| 2     | 2025-01-17 | 1A | Claude Sonnet 4.5 | L3 | 1.0 | 43% compression WITHIN safe threshold. Identity preserved, structural thinking intact, core values perfect. Narrative compressed, playful energy reduced. Behavioral: 9/10, Style: 8/10, Values: 10/10. Continuity: YES. | experiments/Trial_02_FULL_vs_L3_Evaluation.md |
| 3     | 2025-01-17 | 1A | Claude Sonnet 4.5 | L2 | 1.0 | 80% compression AT NYQUIST BOUNDARY. Identity clear, structural thinking preserved, core values perfect. Narrative significantly compressed, playfulness stated not enacted. Behavioral: 8/10, Style: 7/10, Values: 10/10. Continuity: YES (edge). | experiments/Trial_03_FULL_vs_L2_Evaluation.md |

**Logging tips**
- Keep transcripts or full outputs alongside the repo (or link to external storage) so you can re-read behavior later.
- When the probe set changes, reset the trial numbering or clearly annotate the switch.
- Use the "Outcome Summary" column to capture whether the compressed persona felt indistinguishable, close, or divergent relative to the full-context baseline.
- For the "Baseline Trial" column: FULL runs should reference themselves (e.g., "1" for Trial 1); compressed runs (L1/L2/L3) should reference the FULL trial they're being compared against.

