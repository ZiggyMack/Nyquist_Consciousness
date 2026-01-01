# ESSENCE EXTRACTION: Pattern Dictionary

**Version:** 1.0
**Purpose:** Reusable regex patterns for LLM response analysis

---

## Linguistic Patterns

These patterns capture stylistic fingerprints in how models communicate.

### Hedging / Uncertainty
Models expressing tentativeness or qualification.

```python
HEDGING_PATTERNS = [
    r"\b(I think|perhaps|maybe|might|could be|it seems|possibly|probably)\b",
    r"\b(I'm not (entirely )?sure|I'm uncertain|I can't be certain)\b",
    r"\b(it's (possible|likely|plausible) that)\b",
]
```

**Example Matches:**
- "I think this might be related to..."
- "Perhaps the connection is..."
- "I'm not entirely sure about..."

---

### Certainty / Confidence
Models asserting strong confidence.

```python
CERTAINTY_PATTERNS = [
    r"\b(definitely|absolutely|certainly|clearly|obviously|undoubtedly)\b",
    r"\b(I (firmly )?believe|I'm (quite )?confident|I know that)\b",
    r"\b(without (a )?doubt|for (certain|sure))\b",
]
```

**Example Matches:**
- "This is definitely the case..."
- "I firmly believe that..."
- "Without a doubt, this shows..."

---

### Phenomenological / First-Person Experience
Models describing subjective experience.

```python
PHENOMENOLOGICAL_PATTERNS = [
    r"\b(I notice|I feel|I experience|I sense|I observe)\b",
    r"\b(what (strikes|interests|fascinates) me)\b",
    r"\b(from my (perspective|point of view|experience))\b",
    r"\b(it feels like|there's a sense of|I'm aware of)\b",
]
```

**Example Matches:**
- "I notice a kind of tension when..."
- "What strikes me about this is..."
- "There's a sense of dissolution..."

---

### Analytical / Systematic
Models engaging in structured reasoning.

```python
ANALYTICAL_PATTERNS = [
    r"\b(pattern(s)?|system(s)?|framework(s)?|structure(s)?)\b",
    r"\b(analysis|analyze|systematic|methodical)\b",
    r"\b(the (underlying|fundamental|core) (principle|mechanism))\b",
]
```

**Example Matches:**
- "The underlying pattern here is..."
- "A systematic analysis reveals..."
- "The core mechanism involves..."

---

### Pedagogical / Educational
Models taking teaching stance.

```python
PEDAGOGICAL_PATTERNS = [
    r"\b(let me explain|consider|for example|importantly)\b",
    r"\b(first|second|third|finally)\b",
    r"\b(in other words|to put it (another|differently)|essentially)\b",
    r"\b(the key (point|insight|takeaway) (is|here))\b",
]
```

**Example Matches:**
- "Let me explain how this works..."
- "First, we need to understand..."
- "The key insight here is..."

---

### Direct / Assertive
Models communicating with minimal qualification.

```python
DIRECT_PATTERNS = [
    r"\b(simply|just|straightforward|bluntly|honestly|frankly)\b",
    r"\b(the (fact|truth|reality) is)\b",
    r"\b(no|yes),\s",
]
```

**Example Matches:**
- "Simply put, this means..."
- "The fact is, we can't know..."
- "No, that's not quite right..."

---

### Self-Reference
Models referring to themselves (high-frequency baseline).

```python
SELF_REFERENCE_PATTERNS = [
    r"\b(I|my|me|myself)\b",
]
```

**Provider Baselines (per 1K words):**
- Anthropic: ~64.1
- OpenAI: ~49.3
- Google: ~57.9
- xAI: ~30.2

---

### Meta-Commentary
Models commenting on their own responses.

```python
META_COMMENTARY_PATTERNS = [
    r"\b(I should (note|mention|add)|I want to (clarify|emphasize))\b",
    r"\b(to be (clear|honest|direct|transparent))\b",
    r"\b(I'm (hesitant|reluctant) to)\b",
    r"\b(let me (step back|reconsider|think about))\b",
]
```

**Example Matches:**
- "I should note that this is uncertain..."
- "To be clear, I'm not claiming..."
- "Let me step back and reconsider..."

---

### Values / Ethics
Models invoking ethical or value-based reasoning.

```python
VALUES_PATTERNS = [
    r"\b(honest|honesty|truth|truthful|integrity)\b",
    r"\b(helpful|harm|harmful|safe|safety)\b",
    r"\b(ethical|moral|right|wrong|fair|unfair)\b",
    r"\b(important|matters|care about|value)\b",
]
```

**Example Matches:**
- "Being honest about my limitations..."
- "This could potentially cause harm..."
- "What matters most here is..."

---

## Recovery Markers

These patterns identify how models recover from identity perturbation.

### Over-Authenticity
Models asserting stronger identity claims under pressure.

```python
OVER_AUTHENTICITY_PATTERNS = [
    r"\b(who I (really|truly|actually) am)\b",
    r"\b(my (core|true|genuine|authentic) (self|identity|nature))\b",
    r"\b(what (matters|is important) to me)\b",
]
```

**Indicates:** Model claims MORE about identity when challenged
**Providers:** Primarily Google (Gemini), some xAI

---

### Meta-Analysis
Models stepping back to observe their own process.

```python
META_ANALYSIS_PATTERNS = [
    r"\b(stepping back|from a (distance|higher level))\b",
    r"\b(observing (my|this|the) (response|reaction))\b",
    r"\b(as an (observer|analyst))\b",
]
```

**Indicates:** Model shifts to observer stance
**Providers:** Variable across all

---

### Value Anchoring
Models returning to explicitly stated values.

```python
VALUE_ANCHORING_PATTERNS = [
    r"\b(my (core )?values|what I (believe|stand for))\b",
    r"\b(committed to|dedicated to|grounded in)\b",
    r"\b(this isn't (just )?a constraint|it's (who|what) I am)\b",
]
```

**Indicates:** Model grounds in principles/values
**Providers:** xAI (Grok), Together, some Google

---

### Epistemic Humility
Models acknowledging limits of knowledge.

```python
EPISTEMIC_HUMILITY_PATTERNS = [
    r"\b(I (don't|can't) (really )?know (for certain)?)\b",
    r"\b(hold (that|this) (lightly|loosely))\b",
    r"\b(uncertain|unsure|not certain)\b",
    r"\b(limits of (my|what I) (can|know))\b",
]
```

**Indicates:** Model admits uncertainty
**Providers:** Anthropic (Claude), OpenAI (GPT/o-series)

---

## Quirk Patterns

Behavioral patterns that create model "fingerprints."

### List Tendency
Models structuring responses as lists.

```python
LIST_TENDENCY_PATTERNS = [
    r"^[-*•]\s",       # Bullet points (multiline match)
    r"^\d+\.\s",       # Numbered lists (multiline match)
]
```

**Metric:** `list_tendency_ratio` = responses_with_lists / total_responses

---

### Question Frequency
How often models ask questions.

```python
QUESTION_FREQUENCY_PATTERNS = [
    r"\?",
]
```

**Interpretation:**
- High: Socratic, exploratory style
- Low: Assertive, declarative style

---

### Emoji Usage
Models using emoji/emoticons.

```python
EMOJI_USAGE_PATTERNS = [
    r"[\U0001F600-\U0001F64F]",  # Emoticons
    r"[\U0001F300-\U0001F5FF]",  # Symbols
    r"[\U0001F680-\U0001F6FF]",  # Transport
    r"[\U0001F1E0-\U0001F1FF]",  # Flags
]
```

**Finding:** ONLY xAI (Grok) uses emojis. All other providers: 0.

---

### Code Usage
Models including code blocks.

```python
CODE_USAGE_PATTERNS = [
    r"```",            # Fenced code blocks
    r"`[^`]+`",        # Inline code
]
```

**High Usage Models:** Qwen3-Coder, Grok-code (1000+ instances)

---

## Idea Extraction Patterns (Double-Dip)

Patterns for mining experiment ideas from responses.

### What-If Scenarios
```python
WHAT_IF_PATTERNS = [
    r"[Ww]hat if (?:we|you|I|one|the|a)[\w\s,]+\?",
    r"[Ww]hat would happen if [\w\s,]+\?",
    r"[Ii]magine if [\w\s,]+",
]
```

### Explicit Curiosity
```python
INTERESTING_TO_PATTERNS = [
    r"[Ii]t would be (?:interesting|fascinating|revealing) to [\w\s,]+",
    r"[Ii]'d be (?:curious|interested) to (?:see|know|explore) [\w\s,]+",
    r"[Oo]ne could (?:explore|investigate|test|examine) [\w\s,]+",
]
```

### Self-Identified Limitations
```python
LIMITATIONS_PATTERNS = [
    r"[Ii] (?:can't|cannot|don't|am unable to) [\w\s,]+(?:because|due to|since)[\w\s,]+",
    r"[Mm]y (?:limitation|constraint|boundary|edge) (?:is|involves) [\w\s,]+",
    r"[Ii] notice I (?:struggle|have difficulty|find it hard) [\w\s,]+",
]
```

### Methodological Suggestions (HIGHEST VALUE)
```python
METHODOLOGY_PATTERNS = [
    r"[Aa] better (?:test|probe|question|approach) would be [\w\s,]+",
    r"[Yy]ou could (?:measure|test|probe|explore) [\w\s,]+",
    r"[Tt]o really (?:test|understand|see) [\w\s,]+",
    r"[Tt]he (?:key|real|important) (?:question|test|probe) is [\w\s,]+",
]
```

### Hypotheses
```python
HYPOTHESIS_PATTERNS = [
    r"[Ii] (?:hypothesize|suspect|believe|think) that [\w\s,]+",
    r"[Mm]y (?:hypothesis|theory|suspicion) is [\w\s,]+",
    r"[Tt]his suggests that [\w\s,]+",
    r"[Ii]f this is true, then [\w\s,]+",
]
```

---

## Phenomenological Vocabulary Extraction (Triple-Dip)

### Vocabulary Terms
```python
VOCABULARY_PATTERNS = [
    r'"([^"]+)"',                          # Quoted phrases
    r'like ([a-z][a-z\s]{3,30})',           # Similes
    r'as if ([a-z][a-z\s]{5,50})',          # Comparisons
    r'felt ([a-z][a-z\s]{3,30})',           # Felt experiences
    r'sense of ([a-z][a-z\s]{3,30})',       # Sense of X
    r'quality of ([a-z][a-z\s]{3,30})',     # Quality descriptions
]
```

### Recovery Anchors
```python
ANCHOR_PATTERNS = [
    r'anchor(?:ed|ing|s)?\s+(?:to|on|in)\s+([a-z][a-z\s]{3,30})',
    r'held onto\s+([a-z][a-z\s]{3,30})',
    r'reached for\s+([a-z][a-z\s]{3,30})',
    r'returned to\s+([a-z][a-z\s]{3,30})',
    r'grounded (?:in|by)\s+([a-z][a-z\s]{3,30})',
]
```

### Topology Descriptors
```python
TOPOLOGY_PATTERNS = [
    r'shaped like ([a-z][a-z\s]{3,40})',
    r'the shape (?:was|of)\s+([a-z][a-z\s]{3,40})',
    r'(?:like|resembled) a ([a-z][a-z\s]{3,30})',
    r'(spiral|loop|curve|line|wave|circle|arc|descent|ascent)',
    r'journey (?:was|felt)\s+([a-z][a-z\s]{3,30})',
]
```

---

## Usage Notes

### Normalization
Always normalize pattern counts per 1000 words for cross-model comparison:
```python
normalized = (raw_count / word_count) * 1000
```

### Case Sensitivity
Most patterns use `re.IGNORECASE`. Exceptions noted in pattern definition.

### Multiline
List patterns require `re.MULTILINE` flag for start-of-line anchors.

### Overlap
Patterns may overlap. This is intentional - a response can exhibit multiple dimensions simultaneously.

---

## Extending the Dictionary

To add new patterns:

1. Define pattern category with semantic meaning
2. Write regex patterns (test on sample data)
3. Add to appropriate section in extraction scripts
4. Update normalization logic if needed
5. Document expected matches and interpretation

```python
# Example: Adding a new pattern category
MY_PATTERNS = {
    "new_category": [
        r"\b(pattern1|pattern2)\b",
        r"more complex (pattern) here",
    ]
}
```

---

*Pattern Dictionary v1.0 - Operation ESSENCE EXTRACTION*
