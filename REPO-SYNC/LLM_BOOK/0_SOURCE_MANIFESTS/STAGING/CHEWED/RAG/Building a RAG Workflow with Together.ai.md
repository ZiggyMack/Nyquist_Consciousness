Building a RAG Workflow with Together.ai

Executive Summary

This document outlines the principles and practical implementation of a Retrieval-Augmented Generation (RAG) workflow, a technique designed to enhance the performance of AI models by grounding them in domain-specific knowledge. RAG operates by dynamically retrieving relevant data from a specialized knowledge base and augmenting the user's prompt with this context before sending it to a large language model (LLM). This process significantly improves the accuracy and relevance of the model's output, reduces the likelihood of hallucinations, and enables source citation.

The core RAG process involves three stages:

1. Indexing: A corpus of documents is chunked, converted into vector embeddings using a specialized model, and stored in a vector database optimized for similarity searches.
2. Retrieval: When a user query is received, it is also converted into an embedding. The vector database is then searched to find and retrieve the document chunks with the highest semantic similarity to the query.
3. Generation: The retrieved information is injected into the prompt alongside the original query, providing the LLM with relevant context to generate a grounded and informed response.

A practical demonstration of this workflow is provided using a movie dataset. The implementation utilizes the Together.ai API, employing the BAAI/bge-base-en-v1.5 model for generating embeddings and the meta-llama/Llama-3-8b-chat-hf model for the final text generation. The example showcases how to embed movie data, retrieve the most relevant movies based on a user query, and use that retrieved data to generate a creative, contextually-aware story.


--------------------------------------------------------------------------------


The RAG Framework: Principles and Process

The Purpose of Retrieval-Augmented Generation

For AI models to be effective in specialized domains, they require access to specific, often proprietary, knowledge. For example, a financial advisory AI must be aware of current market trends and a specific bank's products, while an AI legal assistant needs deep knowledge of statutes, regulations, and case law. RAG is a common and powerful solution that addresses this need. It works by connecting a generative model to an external knowledge base, allowing it to retrieve relevant information at runtime and incorporate it into its responses. This approach customizes the model's output to the provided data, enhancing its utility for specialized tasks.

Core Stages of the RAG Process

RAG operates through a systematic, three-stage process that transforms a standard LLM query into a context-rich interaction.

Stage	Description	Key Benefits
1. Indexing the Knowledge Base	The source corpus (e.g., a collection of documents, articles, or data records) is first divided into smaller, manageable chunks of text. An embedding model then converts each chunk into a numerical vector representation. These vector embeddings are stored in a vector database, which is specifically designed for efficient high-speed similarity searches.	Creates a searchable, machine-readable version of the knowledge base.
2. Query Processing and Retrieval	When a user submits a query, the system intercepts it before it goes to the LLM. The query is converted into a vector embedding using the same model from the indexing stage. The system then searches the vector database to find the document chunks whose embeddings are most semantically similar to the query's embedding. The most relevant chunks are retrieved.	Dynamically finds and surfaces the most pertinent information for any given query.
3. Response Generation	The retrieved text chunks are injected directly into the prompt, augmenting the original user query. This combined prompt is then sent to the generative AI model. The model uses its pre-trained knowledge along with the newly provided, highly relevant context to formulate a comprehensive and accurate response.	<ul><li>Reduces the likelihood of "hallucination" (generating incorrect or fabricated information) by grounding the model in factual data.</li><li>Enables the system to cite the source material used to generate the response.</li></ul>

Practical Implementation: A Movie Dataset Workflow

This section details a concrete implementation of the RAG pipeline using a dataset of movie information.

The Dataset

The knowledge base for this example is a movies.json file. Each entry in the dataset contains information about a specific movie, structured with the following key fields:

* title
* overview
* director
* genres
* tagline

Example Data Entries:

[
    {
    "title": "Minions",
    "overview": "Minions Stuart, Kevin and Bob are recruited by Scarlet Overkill, a super-villain who, alongside her inventor husband Herb, hatches a plot to take over the world.",
    "director": "Kyle Balda",
    "genres": "Family Animation Adventure Comedy",
    "tagline": "Before Gru, they had a history of bad bosses"
    },
    {
    "title": "Interstellar",
    "overview": "Interstellar chronicles the adventures of a group of explorers who make use of a newly discovered wormhole to surpass the limitations on human space travel and conquer the vast distances involved in an interstellar voyage.",
    "director": "Christopher Nolan",
    "genres": "Adventure Drama Science Fiction",
    "tagline": "Mankind was born on Earth. It was never meant to die here."
    }
]


Step 1: The Retrieval Pipeline ("R")

The retrieval phase involves creating vector representations for both the movie data and the user query, and then finding the best matches.

1. Document Preparation: For each movie in the dataset, a combined text string is created by concatenating the values of the title, overview, and tagline fields. This consolidated text serves as the input for the embedding model.
2. Embedding Generation: The Together.ai API is used to generate vector embeddings for the prepared text of each movie. The specific model employed for this task is BAAI/bge-base-en-v1.5.
3. Query Processing: When a user submits a query, such as "super hero action movie with a timeline twist", the same embedding model (BAAI/bge-base-en-v1.5) is used to generate a vector embedding for the query.
4. Similarity Search: A cosine similarity calculation is performed between the query embedding and the embedding of every movie in the knowledge base. This yields a similarity score for each movie, where a higher score indicates greater semantic relevance to the query.
5. Ranking and Selection: The movies are ranked from highest to lowest similarity score. For the example query, the top 10 most similar movie titles retrieved are:
  * 'The Incredibles'
  * 'Watchmen'
  * 'Mr. Peabody & Sherman'
  * 'Due Date'
  * 'The Next Three Days'
  * 'Super 8'
  * 'Iron Man'
  * 'After Earth'
  * 'Men in Black 3'
  * 'Despicable Me 2'

This retrieval logic can be encapsulated in a reusable function, retrieve(), which takes a query, a desired number of results (top_k), and the embedding index as inputs.

Step 2: The Generation Step ("G")

The generation phase uses the retrieved information to guide the LLM in creating a contextually grounded response.

1. Context Augmentation: The titles and overviews of the top-ranked movies are extracted from the dataset. This retrieved information is then formatted and injected directly into the prompt for the LLM.
2. Prompt Engineering: A structured prompt is created with distinct roles to guide the LLM.
  * System Role: Sets the persona and task for the model: "You are a pulitzer award winning craftful story teller. Given only the overview of different plots you can weave together an interesting storyline."
  * User Role: Contains the original query and the augmented context: "Tell me a story about {titles}. Here is some information about them {overviews}"
3. LLM Generation: The complete, augmented prompt is sent to a generative model via the Together.ai API. The model used in this example is meta-llama/Llama-3-8b-chat-hf.
4. Grounded Output: The LLM generates a response that synthesizes the provided context. In the example, it produces a creative story that weaves together plot elements and characters from the retrieved movies, such as Mr. Incredible from The Incredibles, the vigilantes from Watchmen, the time-traveling duo from Mr. Peabody & Sherman, and agents from Men in Black. This demonstrates how the RAG pipeline successfully conditions the model's generation on the retrieved facts, resulting in a relevant and detailed output.
