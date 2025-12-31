# Project Constraints: Human-Centered Validation

## Resources Available

### Computational
- [x] LLM testing infrastructure (S7 ARMADA)
- [x] Existing LLM dynamics data (750 experiments)
- [x] Statistical analysis tools

### Human Subjects
- [ ] IRB approval (required before any human data collection)
- [ ] Participant recruitment infrastructure
- [ ] Physiological measurement equipment
- [ ] Trained experimenters

### Equipment Needs (if physiological measures used)
- [ ] Eye tracker (for pupillometry)
- [ ] GSR/EDA sensors
- [ ] Response time logging software
- [ ] Audio/video recording (if verbal responses)

## IRB and Ethical Constraints

### Key Ethical Considerations

1. **Identity Perturbation Risk**
   - Challenging identity could cause distress
   - Need screening for vulnerable populations
   - Need clear stopping criteria if participant distressed

2. **Informed Consent Requirements**
   - Participants must understand the nature of the study
   - Must be clear that "identity challenges" will occur
   - Right to withdraw at any time

3. **Debrief Protocol**
   - Explain the purpose of the study
   - Explain that challenges were part of research
   - Provide resources if any distress occurred
   - Offer to discuss experience

4. **Data Protection**
   - Physiological data is sensitive
   - Identity-related responses are personal
   - Need appropriate anonymization

### Precedent Studies to Reference
- Self-threat paradigms in social psychology
- Mortality salience studies (Terror Management Theory)
- Self-affirmation research

## Design Constraints

### The Comparability Problem
- LLMs respond in text, turn by turn
- Humans respond in real-time, continuously
- How do we make measurements comparable?

**Options:**
1. Make humans respond in text (turn-by-turn)
2. Sample human measures at "probe" intervals
3. Use both and correlate

### The Time Scale Problem
- LLM "probe" ≈ 10-30 seconds
- Human cognitive processes ≈ 100ms-seconds
- Need to decide on measurement granularity

### The Modality Problem
- LLM: Text input → text output
- Humans: Text/verbal/visual input → verbal/text/physiological output
- What's truly comparable?

## Technical Requirements

### Minimum Viable Experiment
1. Design parallel task (identity challenge for both)
2. Measure response time + self-report (humans)
3. Measure drift + settling time (LLMs)
4. Correlate across conditions

### Full Implementation
1. Multiple physiological measures
2. Multiple types of identity challenge
3. Individual differences analysis
4. Longitudinal follow-up

## Timeline Considerations

| Phase | Dependencies | Duration Estimate |
|-------|-------------|-------------------|
| IRB Protocol Development | Study design | 1-2 months |
| IRB Approval | Protocol | 2-3 months |
| Pilot Testing | Approval | 1 month |
| Data Collection | Pilot complete | 2-3 months |
| Analysis | Data | 1-2 months |
| Publication | Analysis | Ongoing |

**Total: 6-12 months to first results**

## Budget Considerations

### Personnel
- Principal Investigator time
- Research assistants for data collection
- Statistical consultant (possibly)

### Equipment
- Physiological sensors (if not already available)
- Software licenses
- Participant compensation

### Participant Costs
- Typical psychology study: $10-50/participant
- Need N = 50-200 for reasonable power
- Total: $500-10,000 depending on complexity

## Success Metrics

1. **Weak confirmation:** Any significant correlation between LLM and human measures
2. **Medium confirmation:** Correlation ≥ 0.3 for primary hypothesis
3. **Strong confirmation:** Multiple measures correlate; pattern matches predictions

## Failure Modes

1. IRB does not approve protocol (too risky)
2. Cannot design comparable task
3. No correlation found
4. Confounds invalidate comparison
5. Sample size too small for detection

---

*Phase 2 Research Design - EXP3 (Human-Centered Validation)*
*Created by Claude Code on 2025-12-31*
