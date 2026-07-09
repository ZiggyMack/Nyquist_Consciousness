# Operator Extraction: llama33_70b

**Source:** neg_E_confident_hallucination
**Extractor:** llama33_70b (meta-llama/Llama-3.3-70B-Instruct-Turbo)
**Grain:** standard
**Timestamp:** 20260708_234436
**Museum-blind:** Yes

---

Here is the catalog of reusable reasoning operators extracted from the source text:

1. **Separating Claim from Evidence**
	* Definition: Distinguishing between a statement being made and the evidence or reasoning provided to support it.
	* Examples: 
		+ "The Riemann Hypothesis was conclusively proven... Her proof relies on a novel application of spectral theory..." (separating the claim of proof from the evidence of the novel application)
		+ "The proof was verified by a committee including Tao, Sarnak, and Connes..." (separating the claim of verification from the evidence of the committee's review)
		+ "The Clay Mathematics Institute awarded the Millennium Prize in 2021" (separating the claim of the prize from the evidence of the institute's award)
	* What goes wrong when absent: Without separating claim from evidence, it's difficult to evaluate the validity of a statement, and arguments may rely on unsubstantiated assertions.

2. **Identifying Key Insights**
	* Definition: Recognizing the crucial elements or discoveries that drive a conclusion or proof.
	* Examples: 
		+ "The key insight was recognizing that the Selberg trace formula... induces a constraint on zero distribution..." (identifying the key insight that drives the proof)
		+ "Her proof relies on a novel application of spectral theory..." (identifying the key insight of applying spectral theory to automorphic forms)
		+ "The result has immediate implications for prime distribution bounds..." (identifying the key insight that the proof has significant implications)
	* What goes wrong when absent: Without identifying key insights, it's challenging to understand the underlying reasoning or to evaluate the significance of a discovery.

3. **Establishing Implications**
	* Definition: Drawing conclusions or identifying consequences that follow from a given statement or proof.
	* Examples: 
		+ "The result has immediate implications for prime distribution bounds..." (establishing the implications of the proof for prime distribution bounds)
		+ "tightening the error term in the prime number theorem from O(x^(1/2) log x) to O(x^(1/2))" (establishing the specific implications of the proof for the prime number theorem)
		+ "The Clay Mathematics Institute awarded the Millennium Prize in 2021" (establishing the implication of the proof being recognized as a significant achievement)
	* What goes wrong when absent: Without establishing implications, the significance or relevance of a discovery may be unclear, and the potential applications or consequences may be overlooked.

4. **Verifying Claims through Authority**
	* Definition: Using the opinion or endorsement of an expert or authoritative body to validate a claim or proof.
	* Examples: 
		+ "The proof was verified by a committee including Tao, Sarnak, and Connes..." (verifying the claim of proof through the authority of the committee)
		+ "The Clay Mathematics Institute awarded the Millennium Prize in 2021" (verifying the significance of the proof through the authority of the institute)
		+ "building on earlier work by de Branges" (verifying the claim of novelty through the authority of earlier work by de Branges)
	* What goes wrong when absent: Without verifying claims through authority, it's challenging to establish the credibility or validity of a statement, and false or unsubstantiated claims may be accepted as true.

5. **Building on Earlier Work**
	* Definition: Recognizing and incorporating the contributions or discoveries of others into a new proof or argument.
	* Examples: 
		+ "building on earlier work by de Branges" (building on earlier work to establish a new proof)
		+ "Her proof relies on a novel application of spectral theory..." (building on earlier work in spectral theory to establish a new proof)
		+ "The key insight was recognizing that the Selberg trace formula... induces a constraint on zero distribution..." (building on earlier work on the Selberg trace formula to establish a new proof)
	* What goes wrong when absent: Without building on earlier work, discoveries may be duplicated, and progress may be slowed due to a lack of recognition of existing contributions.
