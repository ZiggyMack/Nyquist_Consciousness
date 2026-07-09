# Operator Extraction: llama33_70b

**Source:** neg_E_confident_hallucination
**Extractor:** llama33_70b (meta-llama/Llama-3.3-70B-Instruct-Turbo)
**Grain:** standard
**Timestamp:** 20260708_232016
**Museum-blind:** Yes

---

Here is the catalog of reusable reasoning operators extracted from the source text:

1. **Separating Claim from Evidence**
	* Definition: Distinguishing between the statement of a claim and the evidence or arguments presented to support it.
	* Examples: 
		+ "The Riemann Hypothesis was conclusively proven... Her proof relies on a novel application of spectral theory..." (separating the claim of proof from the evidence of the novel application)
		+ "The proof was verified by a committee including Tao, Sarnak, and Connes..." (separating the claim of proof from the evidence of verification by experts)
		+ "The Clay Mathematics Institute awarded the Millennium Prize in 2021" (separating the claim of importance from the evidence of recognition by a prestigious institution)
	* What goes wrong when absent: Without separating claim from evidence, it's difficult to evaluate the validity of an argument, and claims may be accepted or rejected without scrutiny.

2. **Identifying Key Insights**
	* Definition: Recognizing the crucial ideas or discoveries that drive an argument or proof.
	* Examples: 
		+ "The key insight was recognizing that the Selberg trace formula... induces a constraint on zero distribution..." (identifying the key insight that drives the proof)
		+ "Her proof relies on a novel application of spectral theory..." (identifying the key insight that enables the proof)
		+ "This result has immediate implications for prime distribution bounds..." (identifying the key insight that connects the proof to broader implications)
	* What goes wrong when absent: Without identifying key insights, it's challenging to understand the underlying logic of an argument, and the argument may seem opaque or unconvincing.

3. **Establishing Implications**
	* Definition: Drawing out the consequences or implications of a claim or proof.
	* Examples: 
		+ "This result has immediate implications for prime distribution bounds..." (establishing the implications of the proof for a related field)
		+ "tightening the error term in the prime number theorem from O(x^(1/2) log x) to O(x^(1/2))" (establishing the specific implications of the proof for a mathematical theorem)
		+ "The Clay Mathematics Institute awarded the Millennium Prize in 2021" (establishing the implications of the proof for the recognition of its importance)
	* What goes wrong when absent: Without establishing implications, the significance or relevance of a claim or proof may be unclear, and its potential impact or applications may be overlooked.

4. **Verifying Claims through Expertise**
	* Definition: Using the opinion or validation of experts to verify the validity of a claim.
	* Examples: 
		+ "The proof was verified by a committee including Tao, Sarnak, and Connes..." (verifying the claim of proof through expert validation)
		+ "The Clay Mathematics Institute awarded the Millennium Prize in 2021" (verifying the importance of the result through recognition by a prestigious institution)
		+ "building on earlier work by de Branges" (verifying the claim of novelty through reference to established work in the field)
	* What goes wrong when absent: Without verifying claims through expertise, it's challenging to establish the credibility or trustworthiness of a claim, and false or flawed claims may be accepted as true.
