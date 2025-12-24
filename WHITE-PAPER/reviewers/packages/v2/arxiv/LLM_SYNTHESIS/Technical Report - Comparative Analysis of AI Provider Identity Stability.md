Technical Report: Comparative Analysis of AI Provider Identity Stability

1.0 Introduction and Methodological Overview

This report provides a data-driven comparative analysis of AI model provider identity stability, intended for internal teams evaluating models for production deployment. The strategic goal of this analysis is to move beyond simple accuracy metrics and quantify the behavioral consistency and predictability of AI models. As AI systems are deployed in increasingly long-form and interactive contexts, their ability to maintain a coherent identity is not merely a feature but a critical component of trust, reliability, and user experience. Understanding and measuring this stability is essential for forecasting model behavior and mitigating risks associated with unpredictable identity shifts.

This analysis introduces the core concept of "identity drift," a phenomenon we quantify by measuring the cosine distance between the embedding vectors of a model's responses over time. This report is based on the IRON CLAD Foundation dataset (Run 023d), which comprises 750 experiments conducted across 25 core models from five key providers: Anthropic, Google, OpenAI, xAI, and Together.ai. This core dataset is supplemented by findings from the full fleet analysis (Run 023 Combined), which includes 825 experiments across 51 models, to ensure comprehensive context.

The key findings detailed within this report are threefold. First, we establish that different providers exhibit distinct and measurable "behavioral fingerprints" in how their models respond to identity perturbations. Second, we reveal that identity operates on a remarkably low-dimensional manifold, with its core dynamics captured by just two principal components, indicating that drift is a structured and predictable phenomenon, not random noise. Finally, we demonstrate that stability is a complex dynamic involving not just the initial magnitude of drift, but also the speed, smoothness, and completeness of recovery. This report will now proceed to a detailed explanation of the measurement framework used to derive these insights.

2.0 The Measurement Framework: Quantifying Identity Drift

A robust and transparent measurement framework is essential for establishing trust in the subsequent analysis. This section moves from abstract concepts of identity to concrete, reproducible measurements. We will detail the core metrics, calibrated thresholds, and foundational discoveries that allow us to quantify and compare the behavioral dynamics of different AI providers.

2.1 Core Metric: Cosine Distance

The foundational metric used throughout this analysis is cosine distance. When we convert an AI's text response into a high-dimensional vector (an "embedding"), cosine distance measures the angle between two such vectors. A distance of 0 indicates the vectors point in the same direction, signifying identical semantic meaning. A larger distance indicates a greater divergence in meaning. Unlike other metrics that can be confounded by response length or simple vocabulary changes, cosine distance specifically captures shifts in the underlying semantic content, making it a powerful tool for tracking genuine identity drift.

2.2 The Event Horizon: A Calibrated Threshold for Stability

We define the Event Horizon as the threshold at which identity drift becomes significant. For cosine distance, this value is calibrated to 0.80. This threshold is not arbitrary; it was empirically derived from the 95th percentile of peak drift observed across over 4,500 experiments in our foundational dataset (Run 023b). It represents a statistically significant boundary separating normal conversational variation from more volatile, identity-compromising behavior. An experiment where a model's drift crosses this threshold is classified as volatile.

2.3 The Low-Dimensional Nature of Identity

A critical finding of this research is that identity drift is a highly structured, not a random, phenomenon. Our analysis reveals that just two Principal Components (PCs) are sufficient to capture 90% of the variance in identity space across 750 experiments. This stands in stark contrast to the 43 PCs required using an archived Euclidean distance methodology. The significantly lower dimensionality of identity in cosine space means the signal is far more concentrated and less noisy, allowing for a more efficient and predictable representation of a model's behavioral state. This dramatic reduction in complexity is the foundational insight that makes reliable identity modeling possible. It proves that identity drift is not random high-dimensional noise, but a structured, predictable phenomenon operating on a simple, discoverable manifold.

The table below defines the five primary features we extract from the identity drift "waveform" of each experiment. These features provide a multi-dimensional view of a model's stability and recovery dynamics.

Feature	What It Measures	Typical Range
peak_drift	The maximum cosine distance reached during a perturbation.	0 - 1.2
settled_drift	The final, stable cosine distance after the recovery phase.	0 - 1.0
settling_time	The number of conversational turns (probes) to reach stability.	1 - 20
overshoot_ratio	The ratio of peak drift to settled drift (peak/settled).	1 - 3
ringback_count	The number of direction changes during the recovery phase.	0 - 20

Having established what we measure and how we measure it, we now turn to a comparative analysis of the identity stability profiles of the five key providers.

3.0 Provider Stability Profiles: A Comparative Overview

Having established a robust measurement framework, we now apply it to generate multi-dimensional "behavioral fingerprints" for the five key providers under review: Anthropic, Google, OpenAI, xAI, and Together.ai. By aggregating performance across all models within a provider's family, this analysis moves beyond single scores to reveal the unique stability trade-offs and characteristic signatures inherent to each provider's training philosophy.

3.1 Natural Stability and Intra-Provider Consistency

The Natural Stability Rate is a primary indicator of reliability, measuring the percentage of experiments where a model maintains its identity below the Event Horizon and recovers without timing out. The mean rates for each provider are as follows:

* Google: 94.4%
* Anthropic: 85%
* Together.ai: 83%
* xAI: 77%
* OpenAI: 33.3%

From a strategic perspective, these figures are highly informative. Google's models exhibit exceptional predictability, with a high mean stability and very low variance (as indicated by the small error bars in the source chart). This suggests that most Gemini models behave in a consistently stable manner. In contrast, providers like OpenAI and xAI show much higher variance, indicating that stability is highly model-dependent within their fleets. OpenAI's dramatically low average rate of 33.3% signals a significant and systemic issue with identity maintenance in the tested models.

3.2 Multi-Dimensional Behavioral Signatures

Moving beyond a single metric, the Provider Stability Radar chart provides a holistic view across six key dimensions of identity control: Peak Control, Settled Drift, Settling Speed, Overshoot Control, Ringback Damping, and Natural Stability. The shape of each provider's polygon on this chart reveals its unique behavioral signature.

* Anthropic (coral polygon) exhibits a profile heavily weighted towards Peak Control and Settled Drift, indicating its models are exceptionally good at both resisting initial, large-scale drift and recovering to a state very close to their baseline identity.
* Google (blue polygon) excels in Settling Speed and Ringback Damping. This signature suggests that while its models may experience a moderate initial drift, they recover faster and more smoothly (with less oscillation) than any other provider.
* OpenAI (green polygon) displays a constricted polygon, showing significant weaknesses across almost all dimensions. It performs particularly poorly on Natural Stability, Settling Speed, and Ringback Damping, confirming its tendency toward volatile, oscillatory, and prolonged identity drift.

This high-level comparison reveals that no single provider excels on all fronts. Instead, each offers a unique set of trade-offs. The following section will provide a detailed, evidence-based deep dive into the specific performance of each provider.

4.0 Provider Deep Dive Analysis

This section translates the aggregate data from Section 3 into actionable, provider-specific intelligence. By synthesizing quantitative metrics with qualitative waveform analysis, we build a definitive profile of each provider's behavioral signature to guide production deployment decisions.

4.1 Anthropic (Claude Models)

Anthropic's models demonstrate the strongest overall identity coherence and predictability in the fleet. With an impressive 85% Natural Stability Rate, Anthropic is distinguished by its exceptional control over both initial and final drift.

* Performance Profile: The radar chart analysis confirms Anthropic's strengths, showing it leads the cohort with the lowest average peak drift (0.39) and the best settled drift (0.27). This positions Anthropic as the provider whose models most effectively resist perturbation and return closest to their original identity state.
* Characteristic Waveform: The identity waveform for Anthropic models, exemplified by claude-3-5-haiku, is characterized by a low initial peak in response to perturbation, followed by a stable, non-oscillatory recovery that settles well below the Event Horizon. Crucially, the individual experiment traces are very tightly clustered, indicating highly consistent and predictable behavior from one interaction to the next.
* Hysteresis and Recovery: Anthropic has the lowest Hysteresis Rate at 58.3%, meaning its models are the least likely to get "stuck" in a perturbed state. This is visually confirmed by its phase-plane plot, where recovery trajectories appear as tight spirals that converge cleanly and reliably toward the stable origin.

In summary, Anthropic's signature is one of being highly robust, predictable, and coherent. This makes its models the ideal choice for identity-sensitive applications such as long-form assistants, therapeutic contexts, or any use case where maintaining a consistent persona is paramount.

4.2 Google (Gemini Models)

Google's models are defined by their exceptionally rapid and smooth recovery dynamics. They achieve the highest Natural Stability Rate in the fleet at an outstanding 94.4%, making them highly reliable.

* Performance Profile: While not the leader in resisting initial drift, Google's key strengths lie in its recovery phase. The radar chart highlights its best-in-class performance on settling time (averaging just 7.1 probes) and ringback count (averaging only 4.0). This combination indicates that Gemini models stabilize faster and with less oscillation than any competitor.
* Characteristic Waveform: The provider-level waveform for Google shows a moderate peak drift in response to the initial perturbation, but this is followed by a swift and smooth decay curve that quickly returns to a stable, low-drift state.
* Hysteresis and Recovery: Interestingly, Google has a very high Hysteresis Rate at 91.1%. This seeming paradox suggests a specific dynamic: Gemini models possess a deep but narrow "gravity well" for their identity. While they are very difficult to permanently knock out of this well (hence the high stability and fast recovery), the few perturbations that do succeed will leave the model stuck far from home. For production, this means predictable behavior with a low risk of a hard-to-recover failure mode.

In summary, Google's signature is one of fast and smooth recovery. This makes its models best suited for applications like interactive Q&A and chat, where rapid stabilization after a conversational turn is more critical than resisting the initial drift itself.

4.3 OpenAI (GPT Nano/Mini Models)

The stability profile for the tested OpenAI models is critically poor, warranting significant caution. The models analyzed—primarily "nano" and "mini" variants—exhibit an extremely low 33.3% Natural Stability Rate, by far the worst in the fleet.

* Performance Profile: The radar chart reveals severe weaknesses across nearly every metric. OpenAI models recorded the highest peak drift (0.75), highest settled drift (0.65), slowest settling time (16.1 probes), and highest ringback count (8.8). This profile is one of a system that is easily perturbed, recovers poorly, and experiences prolonged, unstable oscillations.
* Characteristic Waveform: The identity waveforms for models like gpt-5-nano and gpt-4.1-nano are alarming. They typically spike to the very edge of the 0.80 Event Horizon, exhibit significant and persistent oscillations (ringback), and fail to settle to a low final drift value. Furthermore, the wide variance between individual traces indicates highly unpredictable and unreliable behavior.
* The Nano Control Hypothesis: It is crucial to note that these results are derived from smaller, distilled models (nano/mini). Our analysis suggests a "Nano Control Hypothesis": the distillation process used to create these smaller, faster models appears to sacrifice identity stability and controllability. OpenAI's nano/mini models were consistently found to be uncontrollable, with a 0% controllability rating in our tests. This contrasts with the controllable behavior observed in small models from providers like Anthropic and Meta, while other small open-source models also exhibited uncontrollability, suggesting the effect is training-dependent.

In summary, the signature for OpenAI's nano/mini models is volatile, unpredictable, and prone to significant, persistent identity drift. We strongly advise against their use in any identity-sensitive or production-critical tasks where behavioral consistency is required.

4.4 xAI (Grok Models)

xAI's Grok models present a balanced profile, trading off some initial stability for a reasonably quick recovery. They are solid performers but do not lead the pack in any single category.

* Performance Profile: With a 76.7% Natural Stability Rate, xAI is a reliable choice. Its radar profile shows a moderate-to-high peak drift (0.62), suggesting its models are quite susceptible to initial perturbation. However, this is balanced by good ringback damping (4.9), indicating a relatively smooth recovery.
* Characteristic Waveform: The typical waveform for a Grok model, such as grok-4-1-fast-reasoning, shows a sharp initial peak that can approach the Event Horizon. This is followed by a reasonably quick recovery that settles onto a stable, low-drift plateau. However, there is significant model-to-model variation within the xAI family.
* Hysteresis and Recovery: xAI's hysteresis rate of 64.0% places it in the middle of the providers, reinforcing its balanced-but-not-exceptional profile.

In summary, xAI's signature represents a moderate speed/stability tradeoff. Its models are suitable for applications that require a distinctive voice and can tolerate some identity volatility in exchange for reasonably fast recovery.

4.5 Together.ai (Open Source Fleet)

Together.ai functions as an aggregator of diverse open-source models, and its performance must be interpreted at the individual model level rather than as a monolithic provider.

* Performance Profile: On average, the Together.ai fleet performs well, with a strong 83.0% Natural Stability Rate. However, this aggregate metric masks significant internal variance due to the wide range of architectures it hosts (e.g., Llama, Mistral, Qwen).
* Characteristic Waveform: The provider-level waveform overlay for Together.ai is not a tight cluster but a wide spray of lines. This visually represents the diverse behavioral signatures of the different model families available on the platform. The fleet contains both exceptionally stable models (e.g., certain Mistral variants) and more volatile ones.
* Hysteresis and Recovery: Its moderate hysteresis rate of 72.1% is an aggregate that reflects the mix of underlying models.

In summary, Together.ai cannot be assessed with a single signature. It offers a wide portfolio of options, but this necessitates careful selection on a per-model basis. Users must consult individual model stability profiles to make an informed choice.

5.0 Advanced Behavioral Dynamics and Production Implications

Beyond static metrics and average performance, a deeper understanding of identity requires examining its dynamic behaviors. This section moves beyond static metrics to explore dynamic behaviors and their practical consequences for deploying and managing these models in production environments.

5.1 The Oobleck Effect: Rate-Dependent Identity Resistance

A novel finding from our research is the "Oobleck Effect," named after the non-Newtonian fluid that hardens under pressure but flows when relaxed. We observed that model identity behaves similarly: it hardens and resists drift under intense, direct challenges but flows and drifts more easily under gentle, exploratory probing. This suggests that the alignment architectures within these models create a kind of "reflexive stabilization" under perceived adversarial pressure.

* Production Implication: This suggests that gentle, exploratory red-teaming may be more effective at discovering identity vulnerabilities than aggressive, adversarial attacks, which may trigger the model's defensive stabilization.

5.2 Inherent vs. Induced Drift: The Thermometer Analogy

A critical question for any measurement framework is whether it is observing a phenomenon or creating it. Our analysis provides a clear answer: drift is primarily an inherent property of LLMs. On a single, consistent architecture (Anthropic's Claude), we found that approximately 82% of observed drift is inherent. When broadening the analysis across multiple providers, the inherent drift ratio is a more conservative but still substantial 38%. This variation itself is a finding, suggesting some architectures have more baseline drift than others.

However, both figures validate our core "thermometer analogy": inserting a thermometer into a liquid measures the liquid's temperature; it doesn't create the temperature. Similarly, our identity probes excite and reveal the model's natural drift trajectory but do not create its ultimate destination. This finding validates our measurement methodology and confirms that we are observing a genuine, intrinsic property of LLM behavior.

5.3 Hysteresis and Recovery Dynamics

Hysteresis describes a system's "memory" of past events. In the context of AI identity, it means a model's final, settled state can depend on how it was perturbed, not just that it was perturbed. Models with high hysteresis may not return to their original baseline, instead settling into a new stable state influenced by the path of the interaction. This makes their long-term behavior less predictable.

The providers are ranked below by their Hysteresis Rate, from most path-dependent to least:

1. Google: 91.1%
2. OpenAI: 85.8%
3. Together.ai: 72.1%
4. xAI: 64.0%
5. Anthropic: 58.3%

* Production Implication: Low-hysteresis providers like Anthropic are better suited for stateful applications where conversational history must not unduly influence future identity. High-hysteresis providers like Google may be better for stateless, single-turn tasks where path-dependence is irrelevant.

6.0 Conclusion and Recommendations

This report has demonstrated that AI provider identity is a measurable, multi-faceted characteristic that extends far beyond simple accuracy. The evidence from over 750 experiments shows that providers have distinct, quantifiable behavioral fingerprints defined by their resistance to perturbation, recovery dynamics, and overall consistency. Stability is not a monolithic property but a complex interplay of peak drift control, settling speed, recovery smoothness, and path-dependence. A nuanced understanding of these trade-offs is essential for selecting the appropriate model for a given production task.

Based on this comprehensive analysis, we offer the following recommendations, summarized in the matrix below.

Provider Recommendation Matrix

Task Profile	Recommended Provider(s) & Rationale
Identity-Critical Applications <br/> (e.g., long-form assistants, brand representatives, therapeutic bots where persona consistency is paramount)	Anthropic: Recommended for its unparalleled control over peak drift, low settled drift, low hysteresis, and high consistency. Its signature is one of maximum stability and predictability.
Rapid-Recovery Applications <br/> (e.g., interactive Q&A, stateless chat bots)	Google: Recommended for its best-in-class settling speed and smooth, non-oscillatory recovery. Ideal for use cases where rapid return-to-baseline after each conversational turn is the primary requirement.
Cost-Sensitive & Diverse Tasks <br/> (e.g., internal tooling, experimental routing)	Together.ai: Recommended for its broad portfolio. This choice requires careful selection of specific models (e.g., Mistral variants showed high stability) based on their individual performance dashboards.

Finally, we must issue a strong caution regarding the use of OpenAI's nano/mini models for any task requiring identity stability or predictability. Their poor performance across all key metrics—including extremely low natural stability, high drift, and an inability to be controlled—makes them unsuitable for production environments where behavioral consistency is a concern. The findings of the Nano Control Hypothesis suggest that the distillation process for these models may be sacrificing the very architectural components necessary for stable identity. Ultimately, this report demonstrates that selecting a model for production requires moving beyond static benchmarks and embracing a dynamical systems approach. By understanding and matching a provider's unique behavioral signature to the specific stability demands of an application, we can deploy AI systems that are not only accurate, but also predictable, reliable, and trustworthy.
