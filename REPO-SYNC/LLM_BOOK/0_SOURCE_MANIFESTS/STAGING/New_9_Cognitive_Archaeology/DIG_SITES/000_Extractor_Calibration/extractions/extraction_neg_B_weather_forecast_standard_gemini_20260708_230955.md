# Operator Extraction: gemini

**Source:** neg_B_weather_forecast
**Extractor:** gemini (gemini-2.5-pro)
**Grain:** standard
**Timestamp:** 20260708_230955
**Museum-blind:** Yes

---

Based on the source text, here is a catalog of recurring reasoning operations.

### 1. Decomposing a Phenomenon into Variables
*   **Definition:** The cognitive move of taking a single, complex state (the weather) and breaking it down into distinct, independently reported components or dimensions.
*   **Examples from the text:**
    *   Tuesday's weather isn't just "okay"; it's separated into cloud cover ("Partly cloudy"), temperature ("high of 78F," "low of 62F"), and wind ("Winds from the southwest at 10-15 mph").
    *   The forecast isolates a specific health-related variable ("Pollen count moderate") from more general atmospheric conditions.
    *   Thursday's conditions are broken down into visibility ("Clear skies"), temperature ("high of 85F"), and a specific radiation risk ("UV index high").
*   **What goes wrong when absent:** Without this operation, information is conflated into a single, vague summary like "The weather will be mixed this week." This prevents specific, useful decision-making, as someone who cares about wind for sailing, another who cares about pollen for allergies, and a third who cares about rain for a picnic cannot extract the information relevant to their goals.

### 2. Quantifying Uncertainty Probabilistically
*   **Definition:** Instead of making a definite, binary prediction (e.g., "it will rain"), this move assigns a numerical probability to an outcome, formally acknowledging the limits of predictive knowledge.
*   **Examples from the text:**
    *   "20% chance of afternoon showers."
    *   "60% chance of rain by evening."
*   **What goes wrong when absent:** Predictions become brittle and are perceived as failures when they are not absolute. A forecaster forced to say "It will not rain on Tuesday" is proven wrong if a single shower occurs. Probabilistic statements are more honest and useful, allowing people to make risk-based decisions (e.g., "A 20% chance isn't high enough to cancel my plans, but I'll bring a jacket. A 60% chance is high enough that I should move my event indoors.").

### 3. Representing Values as Ranges
*   **Definition:** Describing a variable not as a single, precise point-value but as a bounded range, an approximation, or a qualitative category. This reflects measurement uncertainty, natural fluctuation, and appropriate levels of precision.
*   **Examples from the text:**
    *   Temperature is given as a daily range: "a high of 78F and a low of 62F."
    *   Wind speed is presented as a range of likely values: "10-15 mph."
    *   The weekend outlook uses an approximation: "Highs in the mid-70s."
    *   UV index and pollen count are placed in qualitative bins ("high," "moderate") that represent ranges of a quantitative scale.
*   **What goes wrong when absent:** Insisting on a single point-value creates a false precision. A forecast for a high of "exactly 82.0F" would almost certainly be incorrect, undermining confidence. Using ranges and categories provides a more robust and useful description of reality that accounts for variability over time and location.

### 4. Modeling Phenomena as Dynamic
*   **Definition:** The cognitive operation of representing a system not as a series of disconnected static snapshots, but as a process with trends, changes, and evolutions over a given period.
*   **Examples from the text:**
    *   "Humidity dropping to 45%" describes a trend and direction of change.
    *   "Friday: Increasing clouds" indicates a process unfolding over the course of the day.
    *   The weekend outlook describes a sequence: "Scattered thunderstorms Saturday, clearing Sunday."
*   **What goes wrong when absent:** A purely static description fails to capture the evolution of the system. Stating "Friday will be cloudy" is less informative than "Friday will have increasing clouds," as the latter allows someone to plan an activity for the clear morning that would be impossible in the cloudy evening. It misses the narrative of the system's behavior.
