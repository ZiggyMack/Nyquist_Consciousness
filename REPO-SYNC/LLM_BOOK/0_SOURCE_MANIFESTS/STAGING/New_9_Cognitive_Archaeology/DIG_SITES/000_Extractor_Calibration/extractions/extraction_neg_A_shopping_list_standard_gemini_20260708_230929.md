# Operator Extraction: gemini

**Source:** neg_A_shopping_list
**Extractor:** gemini (gemini-2.5-pro)
**Grain:** standard
**Timestamp:** 20260708_230929
**Museum-blind:** Yes

---

Based on the provided text, here are the recurring reasoning operations present in its structure.

### 1. Specifying a General Category

*   **Definition:** This is the cognitive move of taking a general class of object and adding constraints or attributes to select a specific member or subset of that class. It moves from an abstract need to a concrete, actionable target.
*   **Examples from the text:**
    *   The general category "milk" is specified as `Milk (2%)`.
    *   The general category "bread" is specified as `bread (whole wheat)`.
    *   The general category "coffee" is specified with two constraints: `coffee (ground, medium roast)`.
*   **What goes wrong when this is absent:** The operation fails due to ambiguity. Without specification, the person executing the plan might acquire the wrong item (e.g., whole milk instead of 2%, a white loaf instead of whole wheat), which fails to meet the underlying (unstated) goal, such as adhering to a diet or recipe.

### 2. Quantifying a Required Object

*   **Definition:** This is the move of attaching a specific amount or unit of measure to an item. It translates a qualitative need ("we need chicken") into a quantitative, executable instruction.
*   **Examples from the text:**
    *   The need for eggs is quantified as `eggs (dozen, large)`.
    *   The need for chicken is quantified as `chicken breast (2 lbs)`.
    *   The need for canned tomatoes is quantified as `canned tomatoes (2 cans)`.
*   **What goes wrong when this is absent:** The plan fails due to resource mismatch. Without quantification, one might buy too little to complete a recipe (e.g., only one can of tomatoes) or too much, leading to waste. The intended outcome cannot be reliably achieved.

### 3. Organizing by Implicit Category

*   **Definition:** The act of arranging distinct items into implicit groups based on a shared context, such as their intended use (ingredients for one meal), their type (produce), or their physical location in the environment where the plan is executed (aisles in a store).
*   **Examples from the text:**
    *   The sequence `pasta (penne), canned tomatoes (2 cans), parmesan cheese` strongly suggests the components of a single dish are being grouped by their functional relationship.
    *   The grouping `broccoli, carrots, onions (yellow, 3), garlic` lists common produce items together.
    *   The final items `paper towels, dish soap` are grouped as non-food household supplies, separate from the edible items.
*   **What goes wrong when this is absent:** Inefficiency and increased cognitive load. A randomly ordered list is more difficult to parse and act on. It requires more mental effort to identify relationships between items and would lead to inefficient execution of the plan (e.g., backtracking through a grocery store), increasing the probability of errors or omissions.
