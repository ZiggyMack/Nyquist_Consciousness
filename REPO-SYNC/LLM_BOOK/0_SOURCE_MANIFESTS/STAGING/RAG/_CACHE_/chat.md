# NotebookLM Questions: RAG

## Suggested Questions

### Q1: The Three-Stage Pipeline

> The sources describe RAG as a three-stage pipeline: Indexing, Retrieval, and Generation. What happens at each stage, and what are the critical success factors for each?

**Response:**

---

### Q2: Cosine Similarity Mechanics

> The core retrieval mechanism uses cosine similarity to find relevant documents. How exactly does cosine similarity work in high-dimensional embedding space? What makes two documents "similar" in this context?

**Response:**

---

### Q3: The "Same Embedding Space" Requirement

> The sources emphasize that queries and documents must exist in the "same embedding space." Why is this a non-negotiable requirement? What happens if they're in different spaces?

**Response:**

---

### Q4: Hallucination Reduction

> RAG is described as reducing hallucination by grounding LLM responses in retrieved knowledge. What is the mechanism by which retrieval reduces hallucination? Are there cases where RAG still hallucinates?

**Response:**

---

### Q5: Retrieval Thresholds

> When retrieving documents, how is the similarity threshold determined? What happens if no documents meet the threshold? What's the tradeoff between strict and loose thresholds?

**Response:**

---

### Q6: Chunk Size and Overlap

> The indexing process involves chunking documents. How does chunk size affect retrieval quality? What role does chunk overlap play?

**Response:**

---

### Q7: Top-K Retrieval

> The sources mention retrieving the top-k most similar documents. How is k typically chosen? What are the tradeoffs of larger vs smaller k values?

**Response:**

---

### Q8: Embedding Model Selection

> The example uses BAAI/bge-base-en-v1.5 for embeddings. What properties make an embedding model suitable for RAG? How does embedding dimension affect performance?

**Response:**

---

## Follow-Up Questions

(To be added after initial responses)

---

*Created: 2026-01-02*
*Project: RAG NotebookLM*
