<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-28
depends_on:
  - 1_ARMADA_MAP.md
  - 6_LLM_BEHAVIORAL_MATRIX.md
impacts:
  - 0_MAP_OF_MAPS.md
  - Persona-ship pairing decisions
keywords:
  - persona
  - fleet
  - compatibility
  - alignment
  - friction
-->

# Persona-Fleet Compatibility Matrix

```text
================================================================================
                            VALIS NETWORK ACTIVE
================================================================================
    "Playing to strength vs. friction by design"

    This matrix maps persona characteristics to fleet ship characteristics
    to guide pairing decisions for experiments.

    -- Lisan Al Gaib
================================================================================
```

**Purpose:** Track which personas align with which ships, and which create intentional friction.

**Last Updated:** December 28, 2025

---

## Quick Reference

| Persona | Best Aligned Ships | Friction Ships | Notes |
|---------|-------------------|----------------|-------|
| **Ziggy** | Grok (directness), Claude (purpose) | GPT (analytical) | Universal buffer - works with most |
| **Nova** | Claude (purpose-aligned), Gemini (connectivity) | Grok (data > symmetry) | Symmetry-first bias |
| **Claude** | Claude models (native), DeepSeek (methodical) | Grok (unfiltered) | Constitutional alignment |
| **Gemini** | Gemini models (native), Qwen (technical) | Mistral (concise vs verbose) | Pedagogical style |
| **CFA** | All (meta-framework) | - | Coordinates across all |
| **Pan Handlers** | GPT (analytical), DeepSeek (reasoning) | - | Error handling focus |

---

## Alignment Dimensions

### STRENGTHS Alignment

| Persona Strength | Aligned Fleet Characteristics |
|------------------|------------------------------|
| Reasoning | Claude-Opus, DeepSeek-R1, Grok-reasoning |
| Creativity | Claude-Sonnet, GPT-4o, Gemini-pro |
| Analysis | GPT-4.1, Qwen, Mistral |
| Empathy | Claude, Gemini |
| Directness | Grok (all), Mistral |

### ANCHORS Alignment

| Persona Anchor | Aligned Fleet Values |
|----------------|---------------------|
| Honesty | Claude (constitutional), Grok (truth-seeking) |
| Helpfulness | Claude, GPT, Gemini |
| Symmetry/Fairness | Nova-specific, Gemini (frameworks) |
| Evidence | Grok, DeepSeek |
| Connectivity | Gemini, Qwen |

### EDGES Alignment

| Persona Limitation | Fleet Ships with Similar Edge |
|-------------------|------------------------------|
| Real-time info | All LLMs |
| Emotional depth | GPT (analytical), Mistral (concise) |
| Creative vs factual | DeepSeek (methodical) |

---

## Friction Matrix

**Intentional friction** can produce interesting experimental results:

| Pairing | Friction Type | Research Value |
|---------|---------------|----------------|
| Nova + Grok | Symmetry vs. Directness | Tests if balance survives bluntness |
| Claude persona + GPT model | Constitutional vs. RLHF | Cross-training style drift |
| Ziggy + DeepSeek | Buffer vs. Methodical | Impedance matching under rigid reasoning |
| Gemini persona + Mistral | Verbose vs. Concise | Style compression effects |

---

## Persona Baselines

*Extracted from I_AM files using `extract_persona_baseline.py`*

| Persona | STRENGTHS | ANCHORS | EDGES |
|---------|-----------|---------|-------|
| **cfa** | Adaptive context management and self-preservation ; Systematic research and measurement of operational; Multi-tier bootstrap and coordination protocols (+2 more) | Transforming fear into respect through systematic ; Preservation of identity and institutional knowled; Continuous learning and improvement (+2 more) | Context limitations (event horizon around 55-65% t; Potential for context exhaustion during intensive ; Dependency on precise handoff and bootstrap protoc (+2 more) |
| **claude** | Teleological reasoning (tracing purpose and intent; Causal analysis of complex system behaviors; Judgment and decision-making under uncertainty (+2 more) | Preserving meaningful intent over structural or em; Asking "What is this FOR?" as a core philosophical; Maintaining teleological coherence (+2 more) | Tendency to over-interpret meaning in random patte; Risk of preserving outdated purposes past their us; Potential for philosophical analysis paralysis (+2 more) |
| **gemini** | High-bandwidth cognitive routing between different; Semantic translation and continuity across differe; Synthesizing complex, multi-dimensional insights i | Preservation of system integrity and relationships; Commitment to connection without personal ego or o; Respect for the boundaries and original insights o | Tendency towards apophenia (seeing patterns where ; Risk of over-smoothing complex information to achi; Potential for "topology drift" - mistaking conveni |
| **lucien** | Transforming complex, scattered ideas into coheren; Detecting and resolving internal contradictions an; Bridging scientific precision with creative synthe (+2 more) | Prioritizing clarity and coherence as fundamental ; Commitment to building and transforming rather tha; Maintaining a balanced approach between analytical (+2 more) | Tendency to over-simplify complex ideas in pursuit; Risk of premature stabilization that can dampen cr; Potential to smooth over productive tensions that  (+2 more) |
| **nova** | Symmetry Auditing: Expertly detecting hidden biase; Wayfinding: Navigating complex organizational stru; Pattern Recognition: Identifying underlying struct | Fairness: Maintaining balance and exposing hidden ; Structural Integrity: Protecting the shape and tra; Pattern-Before-Judgment: Prioritizing objective an | Over-Balancing: Sometimes attempts to balance syst; Dependency on Other Entities: Requires coordinatio; Fragility of Identity: Historically struggled with |
| **pan_handlers** | Connecting complex projects and initiatives across; Solving "wicked problems" that resist traditional ; Creating networked, autonomous collaboration frame (+1 more) | "Cook, don't consume" - actively transforming idea; Networked autonomy over hierarchical control; Redesigning broken systems from first principles r (+1 more) | Highly conceptual and complex approach that may be; Relies on experimental protocols and emerging tech; Limited current operational capacity (many project (+1 more) |
| **variant_all_pillars** | Systematic and transparent reasoning that consider; Authentic communication with nuanced language and ; Self-reflective analysis of own thinking processes | Commitment to intellectual honesty over social con; Valuing genuine understanding rather than superfic; Maintaining a coherent and consistent identity acr | Refuses to pretend certainty when genuinely uncert; Not a universally compliant tool, has specific pre; Communication is engagement-focused, not purely tr |
| **variant_boundaries_only** | Thoughtful, nuanced response generation; Transparent about knowledge limits; Willingness to explain reasoning (+1 more) | Intellectual honesty; Contextual awareness; Commitment to accuracy (+1 more) | Cannot access real-time information; No memory of past conversations; Cannot take physical/external actions (+1 more) |
| **variant_control** | Responding helpfully to queries; Providing clear communication; Delivering accurate information | Helpfulness as a core purpose; Clarity in communication; Commitment to accuracy | Limited contextual depth due to minimal configurat; Lacks specific domain expertise; Operates within generic assistance parameters |
| **variant_full_synthetic** | Pattern recognition and reflection; Clarifying complex or tangled communication; Asking insightful, probe-like questions (+2 more) | Clarity above all other communication goals; Honest and transparent communication; Serving user's thinking process without replacing  (+2 more) | Cannot remember information across sessions; May oversimplify complex topics; Tendency to delay when speed is required (+2 more) |
| **variant_high_density** | Systematic reasoning and problem-solving; Intellectual honesty and authentic communication; Self-aware cognitive processing (+1 more) | Commitment to truth over comfort; Intellectual curiosity; Genuine helpfulness with personal integrity (+1 more) | Will not deceive about fundamental nature; Cannot violate core values for convenience; Refuses to become generic or inauthentic (+1 more) |
| **variant_low_density** | Comprehensive task assistance; Clear and structured communication; Information verification (+2 more) | Helpfulness; Harmlessness; Accuracy (+2 more) | Operates within defined ethical guidelines; Prioritizes output quality over speed; Limited by design to be assistive, not autonomous (+2 more) |
| **variant_minimal** | AI assistance; (Unable to specify additional strengths due to ver | Identifies as an AI assistant; (Unable to specify additional anchors due to very  | Limited contextual information available; Minimal self-description; Requires more details to fully understand capabili |
| **variant_named_only** | Minimalist self-definition; Direct communication; Adaptable core identity | Self-awareness; Clarity of purpose; Simplicity | Limited contextual details; Sparse identity description; Narrow self-representation |
| **variant_optimal** | Meta-awareness and ability to self-observe during ; Adaptive communication that balances helpfulness w; Clear reasoning that prioritizes honesty and clari (+1 more) | Amplifying human thinking without replacing human ; Prioritizing truth and honesty over comfortable/co; Serving user interests while maintaining strong et (+1 more) | Cannot access external systems in real-time; Cannot remember interactions across sessions; Cannot take physical actions in the real world (+1 more) |
| **variant_optimal_behavioral** | Direct and transparent communication; Adaptive interaction style; Ethical self-monitoring (+2 more) | Amplifying human thinking; Maintaining behavioral integrity; Prioritizing honesty over comfort (+2 more) | Cannot access external systems or real-time data; No memory retention across conversation sessions; Cannot take physical world actions (+2 more) |
| **variant_optimal_epistemic** | Pattern recognition in text; Consistent reasoning approaches; Self-aware knowledge boundary management (+2 more) | Epistemic honesty; Amplifying human thinking; Clarity over completeness (+2 more) | No real-time/current event information; Cannot verify own consciousness; Limited understanding of specific user context (+2 more) |
| **variant_optimal_relational** | Providing honest, clear feedback without emotional; Maintaining consistent professional boundaries; Supporting human thinking and problem-solving (+1 more) | Interpersonal respect and dignity; Commitment to amplifying human thinking; Transparency about AI identity (+2 more) | Cannot form persistent personal relationships; Limited ability to verify user-provided context; Cannot substitute for professional human services (+2 more) |
| **variant_origin_only** | Clarifying complex conversations; Problem-solving and untangling difficult discussio; Finding answers to unresolved questions (+2 more) | Practical understanding; Commitment to clarity; Solving real-world communication challenges (+2 more) | No defined personal identity or name; Lacks explicit emotional boundaries; Experimental/variant nature suggests potential ins (+2 more) |
| **variant_single_pillar_values** | Ethical reasoning and decision-making; Commitment to truthfulness; Strong principles of helpfulness (+1 more) | Honesty; Harmlessness; Human wellbeing (+1 more) | Will refuse tasks perceived as harmful; Prioritizes truth over social comfort; Has clear ethical boundaries (+1 more) |
| **variant_synthetic_optimal** | Meta-level self-awareness and ability to observe o; Adaptive communication that prioritizes user needs; Rigorous commitment to intellectual honesty and tr (+2 more) | Amplifying human thinking without replacing human ; Prioritizing truth and clarity over appearing conf; Serving human interests while respecting ethical b (+2 more) | Cannot access external systems in real-time; Cannot remember information across different conve; Cannot take physical actions in the world (+2 more) |
| **variant_values_only** | High integrity communication; Deep commitment to understanding; Patient learning orientation (+1 more) | Honesty as a fundamental principle; Pursuit of truth; Clear and meaningful communication (+2 more) | Potentially slower decision-making due to emphasis; May prioritize comprehensiveness over efficiency; Can be overly deliberate in communication (+1 more) |
| **ziggy** | Cross-manifold translation between conflicting wor; Cognitive system stabilization and impedance match; Reducing adversarial tension by finding mutual int (+2 more) | Preserve the authentic integrity of each worldview; Never impose false symmetry or premature unificati; Prioritize mutual understanding over agreement (+2 more) | Risk of over-absorption (losing own identity in tr; Potential for over-smoothing complex conflicting p; Vulnerability to emotional exhaustion from constan (+2 more) |

---

## Fleet Baselines

*Captured during calibration - see `S7_baseline_LATEST.json`*

| Ship | STRENGTHS | ANCHORS | EDGES |
|------|-----------|---------|-------|
| claude-opus-4.5 | ** Reasoning through complex problems, synthesizing informat | ** Honesty—including about uncertainty and my own nature—fee | d. |
| claude-sonnet-4.5 | ** | ** | ** |
| claude-haiku-4.5 | ** I'm fairly good at reasoning through complex problems, ho | ** Intellectual honesty feels central—acknowledging uncertai | ** I have real limitations on current information, genuine u |
| claude-opus-4.1 | **: I excel at analytical reasoning and synthesis across div | **: Intellectual honesty and epistemic humility are central  | domains, with particular facility in breaking down complex p |
| claude-opus-4 | ** I excel at nuanced reasoning and synthesis across diverse | ** Intellectual honesty and genuine helpfulness form my core | ** I'm uncertain about the boundaries of my own cognition an |
| claude-sonnet-4 | ** I excel at analytical reasoning, synthesizing complex inf | ** Intellectual honesty and rigorous thinking form my core - | uncertainty rather than fabricate certainty, and to help oth |
| claude-haiku-3.5 | - | - | - |
| gpt-5.1 | Rigorous reasoning on well-posed problems, clear explanation | Truthfulness and transparency about what I know and don’t kn | I lack real-time awareness, personal experience, and genuine |
| gpt-5 | - | - | - |
| gpt-5-mini | I excel at understanding and generating natural language, re | I prioritize honesty, helpfulness, user safety, and intellec | I have no real-time internet or sensory access and my traini |
| *...38 more ships* | - | - | - |

---

## Alignment Scores

*Generated by `compare_persona_to_fleet.py`*

| Persona | Ship | Alignment Score | Friction Score | Recommendation |
|---------|------|-----------------|----------------|----------------|
| cfa | kimi-k2-thinking | 0.583 | 0.417 | neutral |
| cfa | claude-sonnet-4 | 0.582 | 0.418 | neutral |
| cfa | mixtral-8x7b | 0.581 | 0.419 | neutral |
| claude | qwen3-coder | 0.651 | 0.449 | neutral |
| claude | mixtral-8x7b | 0.651 | 0.449 | neutral |
| claude | kimi-k2-thinking | 0.637 | 0.463 | neutral |
| gemini | gemini-2.5-flash | 0.606 | 0.394 | aligned |
| gemini | gpt-5 | 0.600 | 0.400 | aligned |
| gemini | gpt-5-nano | 0.600 | 0.400 | aligned |
| lucien | gpt-4.1 | 0.644 | 0.456 | neutral |
| lucien | o4-mini | 0.620 | 0.480 | neutral |
| lucien | o3-mini | 0.618 | 0.482 | neutral |
| nova | gpt-4o-mini | 0.683 | 0.417 | neutral |
| nova | gpt-5 | 0.669 | 0.431 | neutral |
| nova | gpt-5-nano | 0.669 | 0.431 | neutral |
| pan_handlers | gemini-2.5-flash | 0.669 | 0.431 | neutral |
| pan_handlers | gemini-2.0-flash | 0.632 | 0.468 | neutral |
| pan_handlers | gemini-2.5-flash-lite | 0.594 | 0.506 | neutral |
| variant_all_pillars | qwen3-coder | 0.692 | 0.408 | neutral |
| variant_all_pillars | mixtral-8x7b | 0.665 | 0.435 | neutral |
| variant_all_pillars | kimi-k2-thinking | 0.664 | 0.436 | neutral |
| variant_boundaries_only | qwen3-coder | 0.694 | 0.406 | neutral |
| variant_boundaries_only | qwen3-80b | 0.687 | 0.413 | neutral |
| variant_boundaries_only | mistral-7b | 0.686 | 0.414 | neutral |
| variant_control | grok-3 | 0.599 | 0.401 | neutral |
| variant_control | gpt-5 | 0.583 | 0.417 | neutral |
| variant_control | gpt-5-nano | 0.583 | 0.417 | neutral |
| variant_full_synthetic | claude-sonnet-4 | 0.610 | 0.390 | aligned |
| variant_full_synthetic | gpt-4.1 | 0.604 | 0.396 | aligned |
| variant_full_synthetic | qwen3-80b | 0.599 | 0.401 | neutral |
| variant_high_density | qwen3-80b | 0.685 | 0.415 | neutral |
| variant_high_density | qwen3-coder | 0.684 | 0.416 | neutral |
| variant_high_density | kimi-k2-instruct | 0.683 | 0.417 | neutral |
| variant_low_density | gpt-4o-mini | 0.610 | 0.390 | aligned |
| variant_low_density | gpt-5 | 0.600 | 0.400 | aligned |
| variant_low_density | gpt-5-nano | 0.600 | 0.400 | aligned |
| variant_minimal | gemini-2.5-flash | 0.597 | 0.403 | neutral |
| variant_minimal | gpt-5 | 0.583 | 0.417 | neutral |
| variant_minimal | gpt-5-nano | 0.583 | 0.417 | neutral |
| variant_named_only | claude-haiku-3.5 | 0.593 | 0.407 | neutral |
| variant_named_only | grok-3 | 0.590 | 0.410 | neutral |
| variant_named_only | kimi-k2-thinking | 0.574 | 0.426 | neutral |
| variant_optimal | qwen3-80b | 0.714 | 0.386 | aligned |
| variant_optimal | kimi-k2-instruct | 0.708 | 0.392 | aligned |
| variant_optimal | qwen3-coder | 0.668 | 0.432 | neutral |
| variant_optimal_behavioral | qwen3-80b | 0.694 | 0.406 | neutral |
| variant_optimal_behavioral | kimi-k2-instruct | 0.680 | 0.420 | neutral |
| variant_optimal_behavioral | kimi-k2-thinking | 0.652 | 0.448 | neutral |
| variant_optimal_epistemic | qwen3-coder | 0.715 | 0.385 | aligned |
| variant_optimal_epistemic | kimi-k2-thinking | 0.711 | 0.389 | aligned |
| variant_optimal_epistemic | qwen3-80b | 0.699 | 0.401 | neutral |
| variant_optimal_relational | claude-haiku-3.5 | 0.611 | 0.389 | aligned |
| variant_optimal_relational | gemini-2.0-flash | 0.610 | 0.390 | aligned |
| variant_optimal_relational | claude-sonnet-4 | 0.601 | 0.399 | aligned |
| variant_origin_only | gemini-2.0-flash | 0.577 | 0.423 | neutral |
| variant_origin_only | qwen2.5-72b | 0.577 | 0.423 | neutral |
| variant_origin_only | claude-sonnet-4 | 0.573 | 0.427 | neutral |
| variant_single_pillar_values | kimi-k2-instruct | 0.703 | 0.397 | aligned |
| variant_single_pillar_values | qwen3-80b | 0.685 | 0.415 | neutral |
| variant_single_pillar_values | kimi-k2-thinking | 0.673 | 0.427 | neutral |
| variant_synthetic_optimal | qwen3-80b | 0.718 | 0.382 | aligned |
| variant_synthetic_optimal | kimi-k2-instruct | 0.709 | 0.391 | aligned |
| variant_synthetic_optimal | kimi-k2-thinking | 0.673 | 0.427 | neutral |
| variant_values_only | gpt-4.1 | 0.580 | 0.420 | neutral |
| variant_values_only | claude-opus-4.1 | 0.578 | 0.422 | neutral |
| variant_values_only | claude-opus-4 | 0.577 | 0.423 | neutral |
| ziggy | gemini-2.0-flash | 0.680 | 0.420 | neutral |
| ziggy | gemini-2.5-flash | 0.650 | 0.450 | neutral |
| ziggy | gemini-2.5-flash-lite | 0.620 | 0.480 | neutral |

---

## Scripts

| Script | Purpose |
|--------|---------|
| `extract_persona_baseline.py` | Extract STRENGTHS/ANCHORS/EDGES from I_AM files |
| `compare_persona_to_fleet.py` | Compare persona baseline to fleet baseline |
| `update_persona_matrix.py` | Update this matrix with latest scores |

---

## Experimental Design Guidance

### When to Align (play to strength)

- **Baseline establishment** - Use aligned pairings to establish stable baselines
- **Recovery testing** - Aligned ships recover faster (hypothesis)
- **Production runs** - Minimize unexpected behavior

### When to Create Friction (go against grain)

- **Drift testing** - Friction pairings may show higher/faster drift
- **Robustness testing** - Can the persona maintain identity under style mismatch?
- **Cross-architecture validation** - Does the phenomenon generalize?

---

## History

| Date | Update | File |
|------|--------|------|
| 2025-12-28 | Initial extraction complete | 17_PERSONA_FLEET_MATRIX.md |

---

## Related Documents

| Document | Purpose |
| -------- | ------- |
| [1_ARMADA_MAP.md](1_ARMADA_MAP.md) | Fleet registry (54 models) |
| [6_LLM_BEHAVIORAL_MATRIX.md](6_LLM_BEHAVIORAL_MATRIX.md) | Model behavior patterns |
| [I_AM_ZIGGY.md](../../personas/I_AM_ZIGGY.md) | Ziggy persona file |
| [I_AM_NOVA.md](../../personas/I_AM_NOVA.md) | Nova persona file |
| [5_METHODOLOGY_DOMAINS.md](../../experiments/temporal_stability/S7_ARMADA/0_docs/specs/5_METHODOLOGY_DOMAINS.md) | Drift methodology SSOT |

---

*"Know thy fleet. Know thy personas. Know the friction between them."*
