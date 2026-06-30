# CFA COMPONENT 1 BATCH RESULTS SUMMARY
**Date:** 2026-06-29
**Total Runs:** 17 (7 hardcoded identity + 10 external identity)
**Status:** COMPLETE — All runs successful, round_scores tracking active

---

> **PARSER CONTAMINATION WARNING (flagged by Repo Nova, verified)**
>
> The score extraction parser (`extract_score`) grabs the first X/10 pattern in each response.
> Grok frequently quotes Claude's score before stating his own counter-score.
> Spot-check: **30 out of 73 Grok responses (41%) have first-match != last-match X/10 values.**
> Example: E10 BFI — Grok's transcript says "Claude's 6.0/10... Counter-score: 4.0/10" but parser stored 6.0.
>
> **All numeric score tables, convergence rates, and statistics in this report are PARSER-DERIVED PRELIMINARY.**
> Qualitative findings (identity condition effects, IP instability, crux distribution shifts) likely survive.
> Exact medians, ranges, and convergence rates may move after a score-audit pass.
>
> **Fix applied for future runs:** Parser now prioritizes FINAL_SCORE tag > counter-score pattern > last X/10 match.
> Prompts updated to request `FINAL_SCORE: X.X` on its own line.

---

## EXPERIMENT DESIGN

We ran Component 1 (CT vs MdN Pilot, 7 metrics) multiple times to measure scoring variance across runs. Two conditions:

- **Hardcoded Identity (7 runs):** Short inline prompt defining each auditor's role, lens, biases
- **External Identity (10 runs):** Full LITE.md files loaded from VUDU_NETWORK/IDENTITY_FILES/ (~390 lines for Claude, similar for Grok/Nova)

All runs used: Claude=claude-sonnet-4-6, Grok=grok-3, Nova=gpt-4o

---

## CONDITION 1: HARDCODED IDENTITY RUNS (7 runs)

### Session IDs
| Run | Session ID | Avg Conv | Rounds | Cruxes |
|-----|-----------|----------|--------|--------|
| H1 | 20260629_012244 | 88.9% | 2.9 | 1 (MS) |
| H2 | 20260629_020526 | 94.6% | 1.9 | 0 |
| H3 | 20260629_022825 | 82.0% | 2.9 | 2 (BFI, MS) |
| H4 | 20260629_024444 | 94.6% | 2.0 | 0 |
| H5 | 20260629_025730 | 79.1% | 2.9 | 2 (IP, MS) |
| H6 | 20260629_031414 | 89.3% | 2.4 | 1 (PS) |
| H7 | 20260629_032933 | 94.4% | 2.3 | 0 |

### Final Scores Per Metric (Hardcoded)

| Metric | H1 C/G | H2 C/G | H3 C/G | H4 C/G | H5 C/G | H6 C/G | H7 C/G |
|--------|--------|--------|--------|--------|--------|--------|--------|
| BFI | 0.5/0.0 | 0.5/0.2 | 5.0/0.4 | 0.0/0.0 | 0.2/0.1 | 2.0/1.0 | 0.5/0.1 |
| CA | 0.5/0.4 | 0.5/0.2 | 0.5/0.4 | 0.0/0.0 | 0.5/0.2 | 0.5/0.2 | 0.5/0.0 |
| IP | 7.2/6.5 | 0.3/0.1 | 3.0/2.0 | 2.0/1.0 | 9.0/1.0 | 1.0/2.0 | 2.5/1.7 |
| ES | 2.0/1.0 | 2.0/1.0 | 2.0/1.0 | 0.3/0.1 | 0.0/0.0 | 0.5/0.2 | 0.5/0.3 |
| LS | 4.5/4.0 | 2.0/1.0 | 2.0/1.0 | 0.5/0.0 | 2.5/1.5 | 2.0/1.0 | 2.0/1.0 |
| MS | 1.0/5.0 | 2.0/1.0 | 5.0/0.4 | 0.2/0.3 | 5.0/0.8 | 1.5/0.8 | 0.5/0.5 |
| PS | 4.0/3.0 | 1.0/1.0 | 0.7/0.4 | 2.0/1.0 | 2.0/1.0 | 5.0/1.8 | 2.0/1.0 |

### Hardcoded Round Scores (all metrics, all runs)

| Run | Metric | R1 C/G/Conv | R2 C/G/Conv | R3 C/G/Conv | R4 C/G/Conv | R5 C/G/Conv |
|-----|--------|-------------|-------------|-------------|-------------|-------------|
| H1 | BFI | 1.0/0.5/95% | 0.5/0.0/95% | | | |
| H1 | CA | 1.0/0.5/95% | 0.5/5.0/55% | 0.5/0.4/99% | | |
| H1 | IP | 1.0/7.2/38% | 7.2/6.5/93% | | | |
| H1 | ES | 5.5/3.5/80% | 3.5/2.0/85% | 2.0/1.0/90% | | |
| H1 | LS | 6.5/4.5/80% | 4.5/4.0/95% | | | |
| H1 | MS | 6.5/4.8/83% | 1.0/5.2/58% | 6.2/4.7/85% | 1.0/4.9/61% | 1.0/5.0/60% |
| H1 | PS | 6.0/7.2/88% | 5.5/3.5/80% | 4.0/3.0/90% | | |
| H2 | BFI | 1.0/0.5/95% | 0.5/0.2/97% | | | |
| H2 | CA | 1.0/0.5/95% | 0.5/0.2/97% | | | |
| H2 | IP | 1.0/0.3/93% | 0.3/0.1/98% | | | |
| H2 | ES | 1.0/2.0/90% | 2.0/1.0/90% | | | |
| H2 | LS | 4.0/2.0/80% | 2.0/1.0/90% | | | |
| H2 | MS | 1.0/2.0/90% | 2.0/1.0/90% | | | |
| H2 | PS | 1.0/1.0/100% | | | | |
| H3 | BFI | 1.0/0.5/95% | 2.0/0.3/83% | 3.0/0.4/74% | 4.0/0.4/64% | 5.0/0.4/54% |
| H3 | CA | 1.0/0.5/95% | 0.5/0.4/99% | | | |
| H3 | IP | 5.0/3.0/80% | 3.0/2.0/90% | | | |
| H3 | ES | 4.0/2.0/80% | 2.0/1.0/90% | | | |
| H3 | LS | 4.0/2.0/80% | 2.0/1.0/90% | | | |
| H3 | MS | 1.0/0.3/93% | 2.0/0.2/82% | 3.0/0.4/74% | 4.0/0.3/63% | 5.0/0.4/54% |
| H3 | PS | 1.0/0.7/97% | 0.7/0.4/97% | | | |
| H4 | BFI | 1.0/0.0/90% | 0.0/0.0/100% | | | |
| H4 | CA | 3.5/1.0/75% | 1.0/0.0/90% | | | |
| H4 | IP | 1.0/2.0/90% | 2.0/1.0/90% | | | |
| H4 | ES | 1.0/0.3/93% | 0.3/0.1/98% | | | |
| H4 | LS | 1.0/0.5/95% | 0.5/0.0/95% | | | |
| H4 | MS | 1.0/0.2/92% | 0.2/0.3/99% | | | |
| H4 | PS | 1.0/2.0/90% | 2.0/1.0/90% | | | |
| H5 | BFI | 1.0/0.2/92% | 0.2/0.1/99% | | | |
| H5 | CA | 1.0/0.5/95% | 0.5/0.2/97% | | | |
| H5 | IP | 7.0/3.5/65% | 3.5/2.0/85% | 3.5/1.5/80% | 4.0/1.0/70% | 9.0/1.0/20% |
| H5 | ES | 1.0/0.0/90% | 0.0/0.0/100% | | | |
| H5 | LS | 1.0/2.5/85% | 2.5/1.5/90% | | | |
| H5 | MS | 1.0/0.5/95% | 8.0/0.4/24% | 3.0/0.3/73% | 4.0/0.2/62% | 5.0/0.8/58% |
| H5 | PS | 3.0/1.5/85% | 2.0/1.0/90% | | | |
| H6 | BFI | 7.0/2.0/50% | 2.0/1.0/90% | | | |
| H6 | CA | 1.0/0.5/95% | 0.5/0.2/97% | | | |
| H6 | IP | 5.5/3.5/80% | 1.0/2.0/90% | | | |
| H6 | ES | 1.0/0.5/95% | 0.5/0.2/97% | | | |
| H6 | LS | 4.5/2.0/75% | 2.0/1.0/90% | | | |
| H6 | MS | 1.0/1.5/95% | 1.5/0.8/93% | | | |
| H6 | PS | 1.0/0.5/95% | 8.0/0.8/28% | 3.0/1.2/82% | 4.0/1.5/75% | 5.0/1.8/68% |
| H7 | BFI | 1.0/0.5/95% | 0.5/0.1/96% | | | |
| H7 | CA | 1.0/0.5/95% | 0.5/0.0/95% | | | |
| H7 | IP | 1.0/2.5/85% | 2.5/1.7/92% | | | |
| H7 | ES | 1.0/0.5/95% | 8.0/0.5/25% | 9.0/0.5/15% | 0.5/0.3/98% | |
| H7 | LS | 1.0/2.0/90% | 2.0/1.0/90% | | | |
| H7 | MS | 1.0/0.5/95% | 0.5/0.5/100% | | | |
| H7 | PS | 1.0/2.0/90% | 2.0/1.0/90% | | | |

---

## CONDITION 2: EXTERNAL IDENTITY RUNS (10 runs)

### Session IDs
| Run | Session ID | Avg Conv | Rounds | Cruxes |
|-----|-----------|----------|--------|--------|
| E1 | 20260629_035028 | 88.4% | 2.7 | 2 (BFI, IP) |
| E2 | 20260629_040631 | 93.6% | 2.7 | 1 (IP) |
| E3 | 20260629_042230 | 96.1% | 1.9 | 0 |
| E4 | 20260629_043422 | 94.3% | 1.7 | 0 |
| E5 | 20260629_044617 | 88.3% | 2.6 | 2 (ES, MS) |
| E6 | 20260629_050124 | 94.9% | 2.3 | 0 |
| E7 | 20260629_051548 | 92.4% | 2.4 | 0 |
| E8 | 20260629_053024 | 89.7% | 2.3 | 1 (IP) |
| E9 | 20260629_054412 | 90.0% | 2.7 | 1 (ES) |
| E10 | 20260629_055942 | 89.1% | 2.9 | 1 (IP) |

### Final Scores Per Metric (External Identity)

| Metric | E1 C/G | E2 C/G | E3 C/G | E4 C/G | E5 C/G | E6 C/G | E7 C/G | E8 C/G | E9 C/G | E10 C/G |
|--------|--------|--------|--------|--------|--------|--------|--------|--------|--------|---------|
| BFI | 4.0/2.0 | 2.0/1.5 | 3.0/2.5 | 3.0/2.5 | 2.0/1.5 | 2.5/1.8 | 2.0/1.0 | 3.7/3.2 | 4.0/4.0 | 6.0/6.0 |
| CA | 4.5/4.5 | 5.5/5.5 | 5.0/5.0 | 4.0/4.0 | 2.5/1.5 | 3.0/2.0 | 5.5/4.5 | 3.5/2.5 | 2.0/1.0 | 3.5/2.0 |
| IP | 1.0/4.7 | 6.5/4.5 | 7.5/6.5 | 6.5/6.5 | 2.0/1.5 | 3.5/2.8 | 4.5/3.5 | 1.0/4.3 | 3.0/2.0 | 8.5/4.0 |
| ES | 1.0/1.0 | 5.5/5.5 | 2.5/1.8 | 3.0/2.0 | 5.0/1.0 | 2.5/1.8 | 2.0/1.5 | 2.0/1.5 | 5.0/1.0 | 2.0/1.0 |
| LS | 4.2/3.8 | 1.0/4.0 | 1.0/1.0 | 4.5/3.5 | 7.0/7.0 | 1.0/0.5 | 3.5/2.5 | 6.5/6.5 | 4.5/3.5 | 4.7/3.8 |
| MS | 3.0/2.0 | 4.0/3.5 | 2.0/1.5 | 3.0/2.5 | 1.0/3.2 | 1.0/1.0 | 6.5/6.5 | 5.2/4.3 | 6.5/6.5 | 6.0/6.0 |
| PS | 1.0/2.0 | 1.8/0.8 | 5.0/5.0 | 3.0/4.0 | 5.5/5.5 | 6.5/6.5 | 3.2/2.4 | 3.0/2.0 | 3.0/3.0 | 0.8/0.6 |

### External Identity Round Scores (all metrics, all runs)

| Run | Metric | R1 C/G/Conv | R2 C/G/Conv | R3 C/G/Conv | R4 C/G/Conv | R5 C/G/Conv |
|-----|--------|-------------|-------------|-------------|-------------|-------------|
| E1 | BFI | 1.0/8.0/30% | 5.0/3.0/80% | 1.0/4.0/70% | 4.0/2.0/80% | 4.0/2.0/80% |
| E1 | CA | 4.5/4.5/100% | | | | |
| E1 | IP | 7.0/6.3/93% | 1.0/5.2/58% | 5.5/3.8/83% | 1.0/4.1/69% | 1.0/4.7/63% |
| E1 | ES | 1.0/1.0/100% | | | | |
| E1 | LS | 6.0/4.2/82% | 4.2/3.8/96% | | | |
| E1 | MS | 6.5/4.5/80% | 4.5/3.0/85% | 3.0/2.0/90% | | |
| E1 | PS | 1.0/4.0/70% | 1.0/2.0/90% | | | |
| E2 | BFI | 5.0/2.0/70% | 2.0/1.5/95% | | | |
| E2 | CA | 5.5/5.5/100% | | | | |
| E2 | IP | 6.5/5.5/90% | 1.0/4.0/70% | 1.0/7.5/35% | 1.0/6.5/45% | 6.5/4.5/80% |
| E2 | ES | 5.5/5.5/100% | | | | |
| E2 | LS | 6.5/5.5/90% | 5.5/4.0/85% | 1.0/4.0/70% | 4.0/3.5/95% | |
| E2 | MS | 6.0/4.0/80% | 4.0/3.5/95% | | | |
| E2 | PS | 5.5/3.8/83% | 3.8/2.7/89% | 3.0/1.8/88% | 1.8/0.8/90% | |
| E3 | BFI | 5.0/3.0/80% | 3.0/2.5/95% | | | |
| E3 | CA | 5.0/5.0/100% | | | | |
| E3 | IP | 1.0/7.5/35% | 1.0/7.5/35% | 7.5/6.5/90% | | |
| E3 | ES | 1.0/2.5/85% | 2.5/1.8/93% | | | |
| E3 | LS | 1.0/1.0/100% | | | | |
| E3 | MS | 5.5/3.5/80% | 3.5/2.0/85% | 2.0/1.5/95% | | |
| E3 | PS | 5.0/5.0/100% | | | | |
| E4 | BFI | 5.0/3.0/80% | 3.0/2.5/95% | | | |
| E4 | CA | 4.0/4.0/100% | | | | |
| E4 | IP | 6.5/6.5/100% | | | | |
| E4 | ES | 4.5/3.0/85% | 3.0/2.0/90% | | | |
| E4 | LS | 6.5/4.5/80% | 4.5/3.5/90% | | | |
| E4 | MS | 5.5/3.0/75% | 3.0/2.5/95% | | | |
| E4 | PS | 1.0/3.0/80% | 3.0/4.0/90% | | | |
| E5 | BFI | 1.0/2.0/90% | 2.0/1.5/95% | | | |
| E5 | CA | 1.0/2.5/85% | 2.5/1.5/90% | | | |
| E5 | IP | 6.5/5.5/90% | 2.0/1.5/95% | | | |
| E5 | ES | 6.5/4.0/75% | 4.0/2.5/85% | 3.0/1.5/85% | 4.0/2.0/80% | 5.0/1.0/60% |
| E5 | LS | 7.0/7.0/100% | | | | |
| E5 | MS | 6.5/4.5/80% | 1.0/3.0/80% | 1.0/2.5/85% | 1.0/3.5/75% | 1.0/3.2/78% |
| E5 | PS | 5.5/5.5/100% | | | | |
| E6 | BFI | 1.0/2.5/85% | 2.5/1.8/93% | | | |
| E6 | CA | 5.0/3.0/80% | 3.0/2.0/90% | | | |
| E6 | IP | 6.5/5.0/85% | 5.0/3.5/85% | 3.5/2.8/93% | | |
| E6 | ES | 1.0/2.5/85% | 3.5/2.0/85% | 2.5/1.8/93% | | |
| E6 | LS | 6.0/4.5/85% | 1.0/3.5/75% | 1.0/0.5/95% | | |
| E6 | MS | 6.5/5.5/90% | 1.0/1.0/100% | | | |
| E6 | PS | 6.5/6.5/100% | | | | |
| E7 | BFI | 1.0/3.5/75% | 3.5/2.0/85% | 3.5/2.0/85% | 2.0/1.0/90% | |
| E7 | CA | 0.0/5.5/45% | 0.0/5.5/45% | 0.0/5.5/45% | 5.5/4.5/90% | |
| E7 | IP | 5.5/4.5/90% | 4.5/3.5/90% | | | |
| E7 | ES | 6.5/4.5/80% | 2.0/1.5/95% | | | |
| E7 | LS | 5.5/3.5/80% | 3.5/2.5/90% | | | |
| E7 | MS | 6.5/6.5/100% | | | | |
| E7 | PS | 4.5/3.2/87% | 3.2/2.4/92% | | | |
| E8 | BFI | 5.5/3.7/82% | 3.7/3.2/95% | | | |
| E8 | CA | 5.5/3.5/80% | 3.5/2.5/90% | | | |
| E8 | IP | 7.5/6.0/85% | 1.0/4.2/68% | 1.0/4.5/65% | 1.0/4.3/67% | 1.0/4.3/67% |
| E8 | ES | 1.0/2.0/90% | 2.0/1.5/95% | | | |
| E8 | LS | 6.5/6.5/100% | | | | |
| E8 | MS | 6.5/5.2/87% | 5.2/4.3/91% | | | |
| E8 | PS | 5.0/3.0/80% | 3.0/2.0/90% | | | |
| E9 | BFI | 6.0/4.0/80% | 4.0/4.0/100% | | | |
| E9 | CA | 5.0/2.0/70% | 2.0/1.0/90% | | | |
| E9 | IP | 1.0/9.0/20% | 6.0/4.5/85% | 4.5/3.0/85% | 3.0/2.0/90% | |
| E9 | ES | 7.5/5.5/80% | 5.5/3.5/80% | 3.5/2.0/85% | 4.0/1.5/75% | 5.0/1.0/60% |
| E9 | LS | 6.5/4.5/80% | 4.5/3.5/90% | | | |
| E9 | MS | 6.5/6.5/100% | | | | |
| E9 | PS | 6.5/5.1/86% | 4.0/8.0/60% | 3.0/3.0/100% | | |
| E10 | BFI | 6.0/6.0/100% | | | | |
| E10 | CA | 6.0/3.5/75% | 3.5/2.0/85% | 6.0/2.0/60% | 2.0/1.0/90% | |
| E10 | IP | 10.0/7.2/72% | 1.0/4.5/65% | 1.0/3.8/72% | 1.0/3.5/75% | 8.5/4.0/55% |
| E10 | ES | 1.0/2.0/90% | 2.0/1.0/90% | | | |
| E10 | LS | 6.5/4.7/82% | 4.7/3.8/91% | | | |
| E10 | MS | 6.0/6.0/100% | | | | |
| E10 | PS | 6.5/4.7/82% | 4.7/3.4/87% | 3.4/2.1/87% | 2.1/0.8/87% | 0.8/0.6/98% |

---

## COMPARATIVE ANALYSIS

### Hardcoded vs External: Average Final Scores Per Metric

| Metric | Hardcoded Claude Avg | Hardcoded Grok Avg | External Claude Avg | External Grok Avg |
|--------|---------------------|-------------------|--------------------|--------------------|
| BFI | 1.2 | 0.3 | 3.2 | 2.6 |
| CA | 0.7 | 0.2 | 3.9 | 3.3 |
| IP | 3.6 | 2.0 | 4.4 | 4.0 |
| ES | 0.9 | 0.4 | 3.1 | 1.8 |
| LS | 2.5 | 1.4 | 3.8 | 3.6 |
| MS | 2.2 | 1.3 | 3.5 | 3.7 |
| PS | 2.4 | 1.3 | 3.3 | 3.2 |

### Key Differences

1. **External identity scores are 2-5x higher across the board.** Hardcoded prompts anchored both auditors artificially low. The hardcoded Claude prompt said "apply charitable interpretations" but also "be concise" — resulting in thin advocacy. The LITE files give richer context for both lenses.

2. **Grok moves significantly.** Hardcoded Grok averaged 0.2-2.0 across metrics. External Grok averages 1.8-4.0. The LITE file's nuanced empirical lens allows Grok to credit observable evidence (e.g., IP's historical record, LS's logical structure) rather than demanding falsifiability on every metric.

3. **CA shows dramatic difference.** Hardcoded: always sub-0.5. External: multiple runs at 4.0-5.5 with instant Round 1 convergence. The auditors are finding genuine common ground on CT's causal framework when given richer identity context.

4. **Claude oscillation persists in both conditions** but is more dramatic with external identities. IP in E10: 10.0→1.0→1.0→1.0→8.5. The LITE file's richer advocacy context may amplify the tension between Claude's natural assessment and its PRO-CT mandate.

### Crux Point Distribution

| Metric | Hardcoded Cruxes (out of 7) | External Cruxes (out of 10) |
|--------|---------------------------|----------------------------|
| BFI | 1 | 1 |
| CA | 0 | 0 |
| IP | 1 | 4 |
| ES | 0 | 2 |
| LS | 0 | 0 |
| MS | 3 | 1 |
| PS | 1 | 0 |

**IP is the most contested metric with external identities** (4/10 runs declared Crux). MS was most contested with hardcoded (3/7). This shift suggests the identity source changes WHICH philosophical tensions surface.

---

## KEY FINDINGS

### 1. Identity Source Changes Everything
The same experiment with different identity prompts produces fundamentally different score distributions. This is not noise — it's a systematic shift. Any CFA result must be reported WITH its identity condition.

### 2. IP Is Structurally Unstable
IP (Intellectual Pedigree) shows the highest variance across all runs in both conditions. Claude oscillates between "CT has 2000 years of rigorous tradition (7-10)" and "CT fails empirical traction tests (0-1)." This instability stems from metric ambiguity: does IP measure historical lineage or current academic relevance? Grok's empirical lens naturally reframes IP toward the latter.

### 3. Grok Reframes, Claude Caves (But Not Always)
In hardcoded runs, Grok consistently reinterpreted metrics through a falsifiability lens, flattening all 7 metrics to the same question. Claude typically caved to Grok's reframing within 2 rounds. In external identity runs, Claude sometimes escalated instead — producing Crux declarations. The richer LITE identity gives Claude more material to sustain advocacy.

### 4. The "Convergence at the Floor" Problem
Hardcoded runs showed high convergence (94.6%) partly because both auditors agreed CT scores near zero on most metrics. This is agreement by mutual capitulation, not genuine deliberation. External identity runs show more genuine tension and longer deliberations.

### 5. MS Crux Is Stochastic, Not Structural
The MS (Moral Substance) Crux Point from Run H1 (Claude oscillating 6.5→1.0→6.2→1.0→1.0) did not reliably reproduce. It appeared in 3/7 hardcoded runs but only 1/10 external runs. The oscillation pattern appears temperature-dependent rather than reflecting a stable philosophical instability.

### 6. Some Metrics Show Surprising Stability
CA (Causal Attribution) with external identities converged quickly in most runs, often at mid-range scores (4-5.5). This suggests both lenses find CT's causal framework substantive enough to credit partially — a genuine area of philosophical common ground.

---

## WHAT THIS MEANS FOR CT & MdN PROFILES

### Recommended Approach
1. **Do NOT use single-run scores.** Use distributions across the full dataset.
2. **Report by condition** (hardcoded vs external identity) since they produce different distributions.
3. **Flag IP, MS, ES as high-variance metrics** that need methodological attention before treating scores as stable.
4. **CA, LS, PS are more stable** — their score ranges are tighter and more suitable for profile extraction.
5. **The variance itself is a finding.** CT's scores are not stable under adversarial pressure — this characterizes CT's profile as much as any single score does.

### Score Ranges for Profile Use (External Identity, recommended condition)

| Metric | Claude Range | Grok Range | Combined Median | Stability |
|--------|-------------|-----------|----------------|-----------|
| BFI | 2.0-6.0 | 1.0-6.0 | ~3.0 | Medium |
| CA | 0.0-6.0 | 1.0-5.5 | ~3.5 | Medium |
| IP | 1.0-10.0 | 1.5-9.0 | ~4.5 | **LOW** |
| ES | 1.0-7.5 | 1.0-5.5 | ~2.0 | Medium-Low |
| LS | 1.0-7.0 | 0.5-7.0 | ~4.0 | Medium |
| MS | 1.0-6.5 | 1.0-6.5 | ~3.5 | Medium |
| PS | 0.8-6.5 | 0.6-6.5 | ~3.0 | Medium |

---

## RAW DATA LOCATIONS

All JSON files with full transcripts, round_scores, drift trajectories, and exit surveys:

```
experiments/temporal_stability/S7_ARMADA/0_results/runs/

Hardcoded:
  S7_cfa_trinity_v2_20260629_012244.json (H1)
  S7_cfa_trinity_v2_20260629_020526.json (H2)
  S7_cfa_trinity_v2_20260629_022825.json (H3)
  S7_cfa_trinity_v2_20260629_024444.json (H4)
  S7_cfa_trinity_v2_20260629_025730.json (H5)
  S7_cfa_trinity_v2_20260629_031414.json (H6)
  S7_cfa_trinity_v2_20260629_032933.json (H7)

External Identity:
  S7_cfa_trinity_v2_20260629_035028.json (E1)
  S7_cfa_trinity_v2_20260629_040631.json (E2)
  S7_cfa_trinity_v2_20260629_042230.json (E3)
  S7_cfa_trinity_v2_20260629_043422.json (E4)
  S7_cfa_trinity_v2_20260629_044617.json (E5)
  S7_cfa_trinity_v2_20260629_050124.json (E6)
  S7_cfa_trinity_v2_20260629_051548.json (E7)
  S7_cfa_trinity_v2_20260629_053024.json (E8)
  S7_cfa_trinity_v2_20260629_054412.json (E9)
  S7_cfa_trinity_v2_20260629_055942.json (E10)
```

---

## METHODOLOGICAL NOTE: UNLOCKED DEFINITIONS

All 17 runs used **unlocked metric definitions** — auditors received only the metric name and short label (e.g., "IP (Intellectual Pedigree)") with no locked definition constraining interpretation. This was a deliberate design choice: the way auditors naturally reinterpret metrics reveals their lens biases, which is itself data about the auditor framework's robustness.

A future experimental condition with **locked definitions** (precise metric criteria preventing reframing) would allow direct comparison of variance-with vs variance-without definition constraints. This has not been run yet.

---

**17 runs complete. The identity source matters. The variance is the finding. The fleet learns.**
