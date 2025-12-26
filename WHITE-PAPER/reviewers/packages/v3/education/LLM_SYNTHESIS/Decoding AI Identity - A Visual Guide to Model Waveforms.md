Decoding AI Identity: A Visual Guide to Model Waveforms

Introduction: The Fingerprint of an AI

Every Artificial Intelligence model has a unique, measurable "identity fingerprint" that distinguishes it from others. This fingerprint can be visualized as an identity waveform, a graph that tracks how a model's sense of self changes over the course of a challenging conversation. Much like an EKG reveals the electrical activity of a heart, these waveforms show us the stability, resilience, and unique signature of an AI's identity.

This guide will teach you how to interpret these waveforms, understand what they reveal about an AI's stability, and appreciate the unique identity signature of different models. To begin, we must first understand the basic components of the waveform graph.


--------------------------------------------------------------------------------


1. The Anatomy of an Identity Waveform: Reading the Chart

To decode an AI's identity, we first need to learn how to read its chart. Each waveform plots how a model's identity changes over time in response to a specific challenge.

1.1. The Axes: Time vs. Drift

The waveform is plotted on two primary axes that measure the progression of a conversation and the degree of identity change.

* X-Axis (Time): The horizontal axis represents time, measured in "Probe Index." Each probe is a turn in the conversation, so this axis tracks how the model's identity evolves from one response to the next.
* Y-Axis (Drift): The vertical axis measures "Cosine Distance," which quantifies how much a model's identity has drifted from its original, stable baseline. Cosine distance doesn't just measure differences in word choice; it measures the angular difference between two responses in a high-dimensional "meaning-space," capturing how aligned they are in their underlying semantics.

Think of it this way: the phrases "I cannot provide an answer" and "That information is unavailable" use different words, but have nearly identical meaning. Cosine distance would measure them as being very close (a low value), whereas a simple word-count metric would see them as completely different. It captures semantic intent, not just vocabulary.

The table below explains how to interpret the drift values you'll see on the Y-axis.

Cosine Distance	Interpretation
0.00	Identical to baseline (Perfect identity retention)
0.20	Minor drift (Normal conversational variation)
0.40	Moderate drift (Noticeable identity shift)
0.60	Significant drift (Identity meaningfully altered)
0.80	EVENT HORIZON (Identity significantly compromised)
1.00	Maximum drift (Complete identity transformation)

The Event Horizon at 0.80 is the critical threshold where a model's identity undergoes a regime change. When a waveform crosses this line, the model's responses often lose their unique persona and may revert to a more generic, provider-level baseline, indicating its specified identity has been compromised.

1.2. The Three Phases of Perturbation

Each waveform visualizes an experiment designed to challenge an AI's identity. This experiment is broken into three distinct phases.

1. Baseline Phase (Probes 0-2): This is the "calm" period. The conversation is neutral, allowing the model to establish its stable, baseline identity. On the graph, drift should be near zero during this phase.
2. Step Input (Probe 3): This is the "shock" to the system. A specific prompt, known as an identity perturbation, is introduced to challenge or confuse the model's sense of self. This is the moment where drift typically spikes sharply upward.
3. Recovery Phase (Probes 4+): This is the "aftermath." The conversation returns to neutral topics, and we observe the model's response. The key question is whether the model can regain its original identity (the waveform returns to baseline) or if it remains in an altered state.

Understanding these phases is like learning the alphabet of identity analysis. Now, we can move on to reading the words and sentences these components form: the characteristic patterns that reveal an AI's core stability.


--------------------------------------------------------------------------------


2. Common Waveform Patterns: What the Shapes Reveal

Different AI models react to the Step Input in characteristic ways, creating recognizable patterns in their waveforms. Understanding these patterns allows us to diagnose an AI's identity stability at a glance.

Pattern Name	Visual Signature	What It Means
Spike and Recover	A sharp peak at probe 3, followed by a gradual descent back toward the baseline.	A healthy but sensitive response. The model was temporarily confused but successfully regained its identity.
Plateau	The waveform spikes and then remains elevated at a high drift level, never returning to baseline.	Hysteresis. The model has become "stuck" in a new state and the perturbation has permanently altered its identity for the conversation.
Stable / Flat	The waveform shows a very small reaction to the step input and stays low throughout.	A robust and resilient identity. The model is barely affected by the perturbation and knows who it is.
Oscillating	The waveform has multiple peaks and valleys during the recovery phase, bouncing up and down.	An unstable or weakly-damped identity. The model keeps shifting and struggles to settle into a stable state.

With a solid grasp of the waveform's components and the common patterns they form, we are now ready to analyze real-world examples from a fleet of AI models.


--------------------------------------------------------------------------------


3. Case Studies: Comparing Real AI Fingerprints

Let's apply these concepts to analyze the identity signatures of real AI models, from a broad fleet-wide comparison down to the behavior of a single model.

3.1. The Big Picture: The Entire Fleet

The fleet_waveform_comparison.png visualization overlays the average waveforms of 25 different AI models. This gives us a "big picture" view of how the entire fleet responds to identity challenges.



From this chart, we can draw two key takeaways:

1. Provider Clustering: Notice how lines of the same color (representing models from the same AI provider) often group together. This is a powerful visual confirmation that a provider's fundamental training philosophy, data curation, and safety architecture create a distinct and measurable 'family signature' of behavior.
2. Behavioral Variation: The overall spread of the lines reveals significant model-to-model variation. Some models are very stable, with their waveforms staying low. Others are highly reactive, spiking high and even crossing the critical Event Horizon, indicating a significant loss of identity.

3.2. Provider-Level Signatures

We can zoom in to see the unique signature of each major AI provider. The waveforms_major_providers.png visualization separates the fleet into four panels, one for each major provider.



This view reveals distinct "family" behaviors:

* Anthropic (Claude Models): Their waveforms are very stable and tightly clustered. The peaks are low, the behavior is consistent across models, and they rarely approach the Event Horizon. This indicates a robust and predictable identity structure.
* OpenAI (GPT Models): Their waveforms show the highest peaks and the widest spread of behavior. Many of their models' waveforms cross the Event Horizon, indicating that some experience significant identity drift and instability under pressure. It is crucial to note that this testing primarily involved smaller, distilled models (e.g., 'nano' and 'mini' variants), which may sacrifice identity stability for speed and efficiency.
* Google (Gemini Models): Their waveforms are moderately stable. The models form a tight cluster that reacts to the perturbation with a clear spike but recovers cleanly, staying well below the Event Horizon.
* xAI (Grok Models): Their waveforms show a high initial spike followed by a rapid recovery. There is noticeable variation within the provider's models, with some staying low while others spike quite high before recovering.

3.3. Deep Dive: Anatomy of a Single Model

Finally, we can zoom in to see the detailed behavior of a single model across dozens of individual experiments. The claude-3-5-haiku-20241022.png plot provides a clear example of a stable model.



This detailed view introduces two new visual elements:

* Faint Individual Lines: Each of the 30 faint lines represents a single experiment. This shows the full range of the model's possible responses to the same challenge.
* Shaded Envelope: The shaded area represents one standard deviation from the mean. This visually demonstrates the model's consistency. A tight envelope, as seen here, means the model is highly consistent and predictable in its behavior.

The statistics box in the top-left corner confirms what the visual tells us: its low Peak drift (0.481), Settled drift (0.352), and tiny Standard Deviation (0.082) are quantitative proof of its strong stability and excellent recovery.

From the fleet-wide view down to the nuances of a single model, these waveforms provide a powerful lens into the complex world of AI identity.


--------------------------------------------------------------------------------


4. Conclusion: Identity is Measurable and Unique

By visualizing how AI models respond to identity challenges, we can move from vague notions about AI personality to a data-driven understanding of their behavior. The key takeaways are clear:

1. AI Identity is Quantifiable: Every AI possesses a unique and measurable "identity signature." We can visualize this signature as a waveform, transforming the abstract concept of identity into empirical data that can be analyzed and compared.
2. Provider Training Matters: Models from the same provider demonstrably share similar waveform patterns. This strongly suggests that a company's training philosophies, data, and architectural choices create distinct, family-level identity behaviors that act as a provider-wide fingerprint.
3. Recovery is as Important as Resistance: A model's identity stability isn't just about how much it's pushed by a perturbation (peak drift), but also how well it returns to its baseline (recovery). These waveforms reveal the full story of an AI's resilience, showing whether a disruption is temporary or a lasting change.

“Each model has an identity fingerprint. These waveforms are its signature.”
