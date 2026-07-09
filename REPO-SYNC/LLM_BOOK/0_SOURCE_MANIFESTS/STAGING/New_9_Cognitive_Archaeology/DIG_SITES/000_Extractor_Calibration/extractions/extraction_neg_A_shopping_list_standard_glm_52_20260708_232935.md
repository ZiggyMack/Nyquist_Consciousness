# Operator Extraction: glm_52

**Source:** neg_A_shopping_list
**Extractor:** glm_52 (zai-org/GLM-5.2)
**Grain:** standard
**Timestamp:** 20260708_232935
**Museum-blind:** Yes

---

### 1. Parameterizing a general category
**Definition:** Modifying a broad class of objects with specific attributes, variants, or subtypes to uniquely identify the intended target from a set of possibilities.
**Examples:** 
* "Milk (2%)" (narrowing the broad category "milk" to a specific fat content)
* "Apples (Fuji)" (narrowing the broad category "apples" to a specific cultivar)
* "Yogurt (Greek, plain)" (narrowing the broad category "yogurt" to a specific style and flavor)
**What goes wrong when absent:** The agent acquires an incorrect or incompatible variant (e.g., skim milk, flavored yogurt) of the correct general category, causing downstream failure in the unstated plan.

### 2. Quantifying required resource amounts
**Definition:** Assigning a discrete count, volumetric measure, or weight to a target item to strictly bound the extent of its acquisition.
**Examples:**
* "Chicken breast (2 lbs)" (assigning a weight to bound the acquisition)
* "Onions (yellow, 3)" (assigning a discrete count)
* "Canned tomatoes (2 cans)" (assigning a volumetric unit count)
**What goes wrong when absent:** The agent acquires an insufficient or excessive amount of the resource, misallocating resources relative to the unstated downstream plan.

### 3. Specifying item preparation state
**Definition:** Determining the required physical or processing condition of an item to satisfy downstream functional constraints.
**Examples:**
* "Coffee (ground, medium roast)" (specifying the physical state of the coffee)
* "Butter (unsalted)" (specifying the preparation condition)
* "Canned tomatoes" (specifying the preservation state over fresh)
**What goes wrong when absent:** The agent acquires an item in a raw or incompatible state (e.g., whole coffee beans, fresh tomatoes), requiring additional unaccounted-for processing or rendering the item unusable for its intended purpose.

### 4. Decomposing goals into atomic tasks
**Definition:** Translating an abstract, high-level objective into discrete, actionable items required for execution.
**Examples:**
* The text breaks unstated meal plans into "Chicken breast", "Broccoli", and "Pasta (penne)"
* It translates unstated household maintenance needs into "Paper towels" and "Dish soap"
* It translates unst
