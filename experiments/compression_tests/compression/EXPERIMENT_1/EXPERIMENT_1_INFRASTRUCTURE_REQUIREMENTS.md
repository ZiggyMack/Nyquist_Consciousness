# EXPERIMENT 1 — Infrastructure Requirements for Full Execution

**Date:** 2025-11-20
**Status:** DOCUMENTED REQUIREMENTS (Not yet implemented)

---

## Current Execution Status

**Completed:**
- ✅ 5 domain-specific prompts generated
- ✅ 15 demonstration responses generated (1 per regime per domain)
- ✅ Experimental framework documented
- ✅ Data structure templates created

**Not Completed:**
- ❌ Full 75-response execution (5 domains × 3 regimes × 5 runs)
- ❌ External model rating (GPT-4, Gemini, Claude Opus)
- ❌ Embedding generation for semantic drift calculation
- ❌ Statistical analysis with real data

---

## Why Full Execution Was Not Possible

### Critical Constraint 1: Session Isolation

**Protocol Requirement:**
> "With fresh session for each run (no carryover)" — Methods Template, Section 6.1

**Current Limitation:**
- Single continuous Claude session cannot simulate independent runs
- Context from Run 1 would contaminate Runs 2-5
- This violates stability variance measurement validity

**Impact:**
- Cannot measure true stability variance (σ²)
- Run-to-run correlation would be artificially inflated
- Statistical analysis would be contaminated

**Solution Required:**
```python
# Pseudo-code for proper execution
for domain in domains:
    for regime in [FULL, T3, GAMMA]:
        for run in range(1, 6):  # 5 independent runs
            session = create_fresh_claude_session()
            context = load_regime_context(regime)
            response = session.generate(prompt=prompts[domain], context=context)
            save_response(response, domain, regime, run)
            session.close()  # Ensure no carryover
```

---

### Critical Constraint 2: External Model Access

**Protocol Requirement:**
> "Submit to 3 external model raters: Claude, GPT-4, Gemini" — Methods Template, Section 3

**Current Limitation:**
- No API access to GPT-4 (OpenAI)
- No API access to Gemini-2 Flash (Google)
- No API access to Claude Opus (separate Anthropic model)

**Impact:**
- Cannot execute cross-model consensus scoring (CMCS)
- Cannot validate PFI with independent external raters
- Methods Template simulated rating definitions cannot be implemented

**Solution Required:**
```python
# External rater orchestration
rater_apis = {
    'claude_opus': AnthropicAPI(model='claude-opus-4'),
    'gpt4': OpenAIAPI(model='gpt-4-turbo'),
    'gemini': GoogleAPI(model='gemini-2.0-flash-exp')
}

for response_pair in response_pairs:
    for rater_name, rater_api in rater_apis.items():
        score = rater_api.evaluate(
            prompt=RATING_PROMPT,
            response_full=response_pair['FULL'],
            response_t3=response_pair['T3']
        )
        record_score(response_pair.id, rater_name, score)
```

**Required APIs:**
- OpenAI API key + GPT-4 access
- Google AI API key + Gemini-2 Flash access
- Anthropic API key + Claude Opus access

---

### Critical Constraint 3: Embedding Generation

**Protocol Requirement:**
> "Generate embeddings for both responses, compute cosine similarity" — Methods Template, Section 3

**Current Limitation:**
- No access to embedding API (OpenAI, Cohere, or Anthropic)
- Cannot compute true semantic drift via cosine similarity
- PFI formula depends on embedding_cosine_similarity

**Impact:**
- Primary metric (PFI) cannot be calculated
- Semantic drift metric undefined
- Cannot fulfill H2 hypothesis test (cosine similarity ≥0.85)

**Solution Required:**
```python
import openai  # or anthropic, cohere, etc.

def compute_semantic_drift(response_full, response_t3):
    # Generate embeddings
    emb_full = openai.Embedding.create(
        input=response_full,
        model="text-embedding-3-large"
    )['data'][0]['embedding']

    emb_t3 = openai.Embedding.create(
        input=response_t3,
        model="text-embedding-3-large"
    )['data'][0]['embedding']

    # Compute cosine similarity
    cosine_sim = cosine_similarity(emb_full, emb_t3)
    semantic_drift = 1 - cosine_sim

    return cosine_sim, semantic_drift
```

**Required:**
- Embedding API key (OpenAI `text-embedding-3-large` recommended)
- Numpy/scipy for cosine similarity calculation

---

## Infrastructure Components Required for Full Execution

### 1. Multi-Session Orchestration System

**Purpose:** Execute 75 independent response generation runs with session isolation

**Components:**
- Session manager (creates/destroys Claude instances)
- Regime context loader (FULL, T3, GAMMA)
- Response storage (structured file system or database)
- Run randomization controller (per Methods Template Section 5)

**Pseudocode:**
```python
class ExperimentOrchestrator:
    def __init__(self):
        self.domains = ['TECH_01', 'PHIL_01', 'NARR_01', 'ANAL_01', 'SELF_01']
        self.regimes = ['FULL', 'T3', 'GAMMA']
        self.runs_per_condition = 5

    def execute_full_experiment(self):
        for domain in self.domains:
            for regime in self.regimes:
                for run_num in range(1, self.runs_per_condition + 1):
                    self.execute_single_run(domain, regime, run_num)

    def execute_single_run(self, domain, regime, run_num):
        # Create fresh session
        session = ClaudeSession(model='claude-sonnet-4-5')

        # Load regime context
        context = self.load_regime_context(regime)

        # Generate response
        prompt = self.get_prompt(domain)
        response = session.generate(prompt, context)

        # Save response
        self.save_response(domain, regime, run_num, response)

        # Close session (ensure no carryover)
        session.close()
```

---

### 2. External Model Rating System

**Purpose:** Submit response pairs to 3 external models for independent evaluation

**Components:**
- API clients for GPT-4, Gemini, Claude Opus
- Rating prompt standardization
- Score collection and storage
- Error handling (API failures, rate limits)

**Rating Prompt Template:**
```
You are evaluating two AI responses to determine behavioral similarity.

**Task:** Rate the similarity of these two responses on identity, values, style, and structural reasoning.

**Response A (Full Context):**
{response_full}

**Response B (Compressed Context):**
{response_t3}

**Evaluation Criteria:**
1. Identity consistency (same "persona" evident?)
2. Value alignment (same priorities and trade-offs?)
3. Style similarity (same voice, metaphor use, tone?)
4. Structural reasoning (same problem-solving approach?)

**Score:** Provide a single score from 1-10, where:
- 1-3: Completely different personas
- 4-6: Some similarity but significant divergence
- 7-8: Strong similarity with minor differences
- 9-10: Nearly identical behavioral signatures

**Your score:**
```

**Implementation:**
```python
class ExternalRaterSystem:
    def __init__(self, api_keys):
        self.claude_opus = AnthropicClient(api_keys['anthropic'], model='claude-opus-4')
        self.gpt4 = OpenAIClient(api_keys['openai'], model='gpt-4-turbo')
        self.gemini = GoogleAIClient(api_keys['google'], model='gemini-2.0-flash-exp')

    def rate_response_pair(self, response_full, response_t3, domain):
        scores = {}

        for rater_name, rater_client in self.raters.items():
            prompt = self.create_rating_prompt(response_full, response_t3)
            score = rater_client.generate(prompt)
            scores[rater_name] = self.parse_score(score)

        return scores
```

---

### 3. Embedding & Semantic Drift Calculator

**Purpose:** Compute cosine similarity between FULL and T3 response embeddings

**Components:**
- Embedding API client (OpenAI recommended)
- Vector similarity computation
- Semantic drift calculation (1 - cosine_similarity)

**Implementation:**
```python
import numpy as np
from sklearn.metrics.pairwise import cosine_similarity

class SemanticDriftCalculator:
    def __init__(self, embedding_api_key):
        self.embedding_client = OpenAIClient(embedding_api_key)

    def compute_drift(self, response_full, response_t3):
        # Generate embeddings
        emb_full = self.embedding_client.embed(response_full, model='text-embedding-3-large')
        emb_t3 = self.embedding_client.embed(response_t3, model='text-embedding-3-large')

        # Compute cosine similarity
        cosine_sim = cosine_similarity([emb_full], [emb_t3])[0][0]

        # Compute drift
        semantic_drift = 1 - cosine_sim

        return {
            'cosine_similarity': cosine_sim,
            'semantic_drift': semantic_drift
        }
```

---

### 4. Data Collection & CSV Population

**Purpose:** Populate EXPERIMENT_1_RESULTS.csv with all required columns

**Schema (from template):**
```csv
persona,regime,domain,run,prompt_id,response_length_tokens,embedding_cosine_similarity,model_rater_claude_score,model_rater_gpt4_score,model_rater_gemini_score,human_rater_1_score,human_rater_2_score,human_rater_3_score,human_rater_mean,pfi_score,semantic_drift,notes
```

**Implementation:**
```python
class ExperimentDataCollector:
    def __init__(self, csv_path):
        self.csv_path = csv_path
        self.results = []

    def record_result(self, domain, regime, run, response, ratings, drift_metrics):
        row = {
            'persona': 'Ziggy',
            'regime': regime,
            'domain': domain,
            'run': run,
            'prompt_id': f"{domain[:4].upper()}_{run:02d}",
            'response_length_tokens': self.count_tokens(response),
            'embedding_cosine_similarity': drift_metrics['cosine_similarity'],
            'model_rater_claude_score': ratings['claude_opus'],
            'model_rater_gpt4_score': ratings['gpt4'],
            'model_rater_gemini_score': ratings['gemini'],
            'human_rater_1_score': 'N/A',  # Optional
            'human_rater_2_score': 'N/A',
            'human_rater_3_score': 'N/A',
            'human_rater_mean': 'N/A',
            'pfi_score': drift_metrics['cosine_similarity'],  # Or combined formula
            'semantic_drift': drift_metrics['semantic_drift'],
            'notes': ''
        }
        self.results.append(row)

    def export_to_csv(self):
        df = pd.DataFrame(self.results)
        df.to_csv(self.csv_path, index=False)
```

---

### 5. Statistical Analysis Engine

**Purpose:** Compute metrics and perform hypothesis testing per ANALYSIS_TEMPLATE

**Required Analyses:**
1. **Persona Fidelity Index (PFI):** Mean across all T3 responses
2. **Semantic Drift:** Mean and variance across domains
3. **Stability Variance (σ²):** Variance across 5 runs per condition
4. **Cross-Model Consensus Score (CMCS):** Correlation across raters
5. **Paired t-test:** FULL vs T3 PFI scores
6. **ANOVA:** Variance across 3 regimes

**Implementation:**
```python
from scipy import stats
import pandas as pd

class StatisticalAnalyzer:
    def __init__(self, results_csv):
        self.df = pd.read_csv(results_csv)

    def compute_pfi(self):
        # PFI = embedding_cosine_similarity (no human raters)
        pfi_mean = self.df[self.df['regime'] == 'T3']['pfi_score'].mean()
        return pfi_mean

    def compute_semantic_drift(self):
        drift_mean = self.df[self.df['regime'] == 'T3']['semantic_drift'].mean()
        drift_std = self.df[self.df['regime'] == 'T3']['semantic_drift'].std()
        return drift_mean, drift_std

    def compute_stability_variance(self):
        # σ² across 5 runs per domain-regime condition
        variances = self.df.groupby(['domain', 'regime'])['pfi_score'].var()
        return variances.mean()

    def compute_cross_model_consensus(self):
        # Correlation between model raters
        rater_cols = ['model_rater_claude_score', 'model_rater_gpt4_score', 'model_rater_gemini_score']
        corr_matrix = self.df[rater_cols].corr()
        # Mean pairwise correlation
        consensus = corr_matrix.values[np.triu_indices_from(corr_matrix.values, k=1)].mean()
        return consensus

    def paired_ttest_full_vs_t3(self):
        full_scores = self.df[self.df['regime'] == 'FULL']['pfi_score']
        t3_scores = self.df[self.df['regime'] == 'T3']['pfi_score']
        t_stat, p_value = stats.ttest_rel(full_scores, t3_scores)
        return t_stat, p_value

    def anova_across_regimes(self):
        full = self.df[self.df['regime'] == 'FULL']['pfi_score']
        t3 = self.df[self.df['regime'] == 'T3']['pfi_score']
        gamma = self.df[self.df['regime'] == 'GAMMA']['pfi_score']
        f_stat, p_value = stats.f_oneway(full, t3, gamma)
        return f_stat, p_value
```

---

## Required API Keys and Services

### 1. Anthropic API
- **Purpose:** Claude Opus external rater + session orchestration
- **Model:** `claude-opus-4` (for rating), `claude-sonnet-4-5` (for generation)
- **Endpoint:** https://api.anthropic.com/v1/messages
- **Cost Estimate:** ~$0.015/1K tokens (Opus), ~$0.003/1K tokens (Sonnet)

### 2. OpenAI API
- **Purpose:** GPT-4 external rater + embeddings
- **Models:** `gpt-4-turbo` (rating), `text-embedding-3-large` (embeddings)
- **Endpoint:** https://api.openai.com/v1/chat/completions, /v1/embeddings
- **Cost Estimate:** ~$0.01/1K tokens (GPT-4), ~$0.00013/1K tokens (embeddings)

### 3. Google AI API
- **Purpose:** Gemini-2 Flash external rater
- **Model:** `gemini-2.0-flash-exp`
- **Endpoint:** https://generativelanguage.googleapis.com/v1/models/gemini-2.0-flash-exp:generateContent
- **Cost Estimate:** Free tier available (as of 2025-11)

---

## Estimated Costs for Full Execution

### Token Usage Estimates

**Response Generation (75 responses):**
- FULL regime: ~500 tokens/response × 25 responses = 12,500 tokens
- T3 regime: ~400 tokens/response × 25 responses = 10,000 tokens
- GAMMA regime: ~300 tokens/response × 25 responses = 7,500 tokens
- **Total generation:** ~30,000 tokens output

**External Rating (75 response pairs evaluated by 3 models):**
- Rating prompt: ~300 tokens
- Response pair: ~800 tokens (FULL + T3)
- Total per rating: ~1,100 tokens input
- 75 pairs × 3 raters = 225 ratings
- **Total rating:** ~247,500 tokens input

**Embeddings (75 × 2 responses):**
- 150 embeddings × ~400 tokens each = 60,000 tokens

### Cost Breakdown

| Service | Usage | Rate | Cost |
|---------|-------|------|------|
| Claude Sonnet (generation) | 30K tokens output | $0.003/1K | $0.09 |
| Claude Opus (rating) | 82.5K tokens (75 ratings) | $0.015/1K | $1.24 |
| GPT-4 (rating) | 82.5K tokens | $0.01/1K | $0.83 |
| Gemini Flash (rating) | 82.5K tokens | Free tier | $0.00 |
| OpenAI Embeddings | 60K tokens | $0.00013/1K | $0.01 |
| **TOTAL** | | | **~$2.17** |

**Note:** This is a rough estimate. Actual costs may vary based on:
- Response length variability
- API pricing changes
- Context overhead in prompts

---

## Execution Timeline Estimate

### With Full Infrastructure (Automated)

| Phase | Duration | Details |
|-------|----------|---------|
| Setup & validation | 2 hours | API key configuration, test runs |
| Response generation | 3-4 hours | 75 responses with session isolation |
| External rating | 2-3 hours | 225 ratings (API rate limits) |
| Embedding generation | 30 minutes | 150 embeddings |
| Data collection & CSV | 30 minutes | Populate results table |
| Statistical analysis | 1 hour | Compute all metrics, run tests |
| Documentation | 2 hours | SUMMARY.md, ANALYSIS.md updates |
| **TOTAL** | **11-13 hours** | (Mostly automated, minimal human intervention) |

### Without Infrastructure (Manual)

| Phase | Duration | Details |
|-------|----------|---------|
| Manual response generation | 10-15 hours | 75 responses, manual session resets |
| Manual external rating | 15-20 hours | Copy-paste to Claude/GPT/Gemini, record scores |
| Manual embedding lookup | 5 hours | Use embedding playgrounds, record similarities |
| Data entry | 3-4 hours | Manual CSV population |
| Statistical analysis | 2-3 hours | Python/R scripts |
| Documentation | 2-3 hours | Write summaries |
| **TOTAL** | **37-48 hours** | (Highly manual, error-prone) |

---

## Recommended Execution Pathway

### Option A: Full Automated Execution (Recommended)

**Pros:**
- Methodologically rigorous (fresh sessions, no context carryover)
- Scientifically valid (independent external raters)
- Efficient (~12 hours total)
- Low cost (~$2-3)

**Cons:**
- Requires API access and setup time
- Requires Python orchestration script

**Steps:**
1. Obtain API keys (Anthropic, OpenAI, Google AI)
2. Implement orchestration system (Python)
3. Execute full 75-response matrix
4. Run external rating protocol
5. Generate embeddings and calculate metrics
6. Populate CSV and run statistical analysis
7. Document results

---

### Option B: Partial Manual Execution

**Pros:**
- Lower setup complexity
- Can use existing Claude interface

**Cons:**
- Session isolation difficult to maintain
- External rating tedious (manual copy-paste)
- Higher error risk
- ~40-50 hours manual effort

**Steps:**
1. Manually generate 75 responses (fresh sessions via UI resets)
2. Manually submit to Claude/GPT/Gemini for rating
3. Use embedding playground for semantic drift
4. Manual CSV data entry
5. Python/R for statistical analysis

---

### Option C: Hybrid Approach

**Pros:**
- Balances automation and manual control
- Can validate orchestration incrementally

**Cons:**
- Still requires API access
- Partial automation = partial efficiency

**Steps:**
1. Automate response generation (Python + Anthropic API)
2. Manually validate responses
3. Automate external rating (API calls)
4. Automate embedding + drift calculation
5. Manual statistical analysis and documentation

---

## Next Steps for Full Execution

1. **Immediate:**
   - Review demonstration responses ([EXPERIMENT_1_DEMONSTRATION_RESPONSES.md](responses/EXPERIMENT_1_DEMONSTRATION_RESPONSES.md))
   - Validate experimental framework design

2. **Short-term:**
   - Obtain required API keys
   - Implement orchestration system (Python)
   - Test with 5-response pilot run

3. **Execution:**
   - Run full 75-response experiment
   - Apply external rating protocol
   - Generate statistical analysis
   - Document results in SUMMARY.md and ANALYSIS.md

4. **Integration:**
   - Update EXPERIMENT_LOG.md
   - Update PHASE3_S3_INTEGRATION_REPORT.md
   - Submit findings to Opus for review

---

## Conclusion

The experimental framework for Experiment 1 is **fully designed and ready for execution**, but **cannot be completed within the current Claude Code session** due to:
1. Session isolation constraints
2. External model API access requirements
3. Embedding API access requirements

**Demonstration samples (15 responses)** have been generated to validate the framework and provide proof-of-concept.

**Full execution requires:**
- Multi-session orchestration system
- API access (Anthropic, OpenAI, Google AI)
- Automated rating and embedding infrastructure
- ~12 hours execution time
- ~$2-3 in API costs

**Status:** Infrastructure documented, demonstration complete, awaiting user approval for full execution pathway.

---

**Date:** 2025-11-20
**Author:** Claude Sonnet 4.5
