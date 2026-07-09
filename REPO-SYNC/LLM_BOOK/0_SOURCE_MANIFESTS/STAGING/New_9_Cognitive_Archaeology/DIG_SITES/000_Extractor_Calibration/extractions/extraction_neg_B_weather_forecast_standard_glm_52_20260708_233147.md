# Operator Extraction: glm_52

**Source:** neg_B_weather_forecast
**Extractor:** glm_52 (zai-org/GLM-5.2)
**Grain:** standard
**Timestamp:** 20260708_233147
**Museum-blind:** Yes

---

# Catalog of Reasoning Operators

## 1. Separating measurement dimensions

**Definition:** The author resolves "weather" into independent axes—temperature, wind, humidity, UV index, precipitation probability, pollen—rather than collapsing them into a single scalar or qualitative gestalt. Each dimension is reported on its own scale and units.

**Examples:**
- Tuesday lists wind speed and direction *separately* from temperature and precipitation probability, rather than saying "breezy and warm."
- Thursday separates UV index from temperature, treating sun-intensity as distinct from heat-intensity.
- The weekend section separates pollen count from all other meteorological data, placing it as a parallel health-relevant dimension.

**What goes wrong when absent:** A single composite score ("nice day" / "bad day") destroys decision-relevant information. Someone scheduling an outdoor run needs to know UV and pollen independently of temperature; a composite label forecloses that.

---

## 2. Quantifying uncertainty probabilistically

**Definition:** Where an outcome is not deterministic, the author assigns a numerical probability rather than asserting a binary or hedging qualitatively. The event is separated from its likelihood.

**Examples:**
- "20% chance of afternoon showers" — a precipitation *event* is distinguished from its *probability*.
- "60% chance of rain by evening" — the same operation recurs with a higher value, enabling comparison across days.
- Winds given as a range ("10-15 mph") rather than a point estimate, extending the same principle to continuous variables.

**What goes wrong when absent:** Categorical claims ("showers likely" / "no rain") force all-or-nothing planning and erase the calibration information a reader needs to threshold their own risk tolerance.

---

## 3. Selecting salient dimensions per period

**Definition:** The author does not mechanically report every dimension for every day. Instead, different non-temperature dimensions surface on different days, implicitly keyed to what is notable or changing for that period.

**Examples:**
- Wednesday surfaces humidity ("dropping to 45%") because the *change* is the salient feature; temperature alone is reported without wind or UV.
- Thursday surfaces UV index ("UV index high") because the value crosses a threshold of concern; humidity and wind are dropped.
- The weekend section surfaces pollen count, which appeared nowhere earlier, because it is relevant to the weekend activity horizon.

**What goes wrong when absent:** A fixed template reporting all dimensions for all days buries signal under noise. The reader cannot quickly identify what is unusual or decision-relevant for a given day.

---

## 4. Pairing qualitative with quantitative data

**Definition:** Each time period combines a natural-language sky description with numeric measurements. The qualitative label provides rapid orientation; the number provides precision. Neither substitutes for the other.

**Examples:**
- Tuesday: "Partly cloudy" (qualitative) paired with "high of 78F" and "20% chance" (quantitative).
- Wednesday: "Mostly sunny" paired with "high of 82F" and "Humidity dropping to 45%."
- Friday: "Increasing clouds" paired with "high of 79F" and "60% chance of rain."

**What goes wrong when absent:** Numbers alone require interpretation against implicit baselines (is 78F warm or cool for this season?). Words alone lack the precision needed for comparison or planning. The pairing lets a reader both orient and decide.

---

## 5. Distinguishing trend from level

**Definition:** The author separates a variable's current value from its direction of change. Some entries report a static level; others report a movement, and the two are kept linguistically and conceptually distinct.

**Examples:**
- Wednesday: "Humidity dropping to 45%" — the trend verb ("dropping") is separate from the level reached ("45%").
- Friday: "Increasing clouds" — a trend is reported without a numeric level, because the direction is more decision-relevant than a cloud-percentage.
- Weekend: "clearing Sunday" — a trend word distinguishes the process of improvement from the endpoint state.

**What goes wrong when absent:** Reporting only levels ("humidity 45%") obscures whether conditions are improving or deteriorating. Reporting only trends ("humidity dropping") prevents comparison against absolute thresholds. A reader planning a hike cares about both whether it *will* rain and whether it is *getting* worse.
