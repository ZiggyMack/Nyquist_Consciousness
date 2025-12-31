# 1_Maps - Cross-Lab Routing Matrices

Routing intelligence for directing LLM Book distillations to appropriate Pan Handler labs.

## Files

| File | Purpose |
|------|---------|
| `research_to_labs.json` | Maps R&D topics to beneficiary labs |
| `llm_book_routing.json` | Pattern-based routing rules |
| `dependency_graph.json` | Inter-lab dependencies (future) |

## How Routing Works

### 1. Topic-Based Routing (`research_to_labs.json`)

Maps specific R&D batch names to labs:

```json
{
  "HOFFMAN": {
    "primary": ["New_3_Human_Validation", "cfa"],
    "secondary": ["avlar-studio"],
    "rationale": "Conscious Realism theory..."
  }
}
```

### 2. Pattern-Based Routing (`llm_book_routing.json`)

Regex patterns match content keywords:

```json
{
  "pattern": "consciousness|identity|drift|PFI",
  "destinations": ["nyquist_consciousness"],
  "priority": "high"
}
```

## Usage

```bash
# Show routing for a specific batch
py chew.py --route HOFFMAN

# Show all routing mappings
py chew.py --route --all

# Regenerate maps from current state
py chew.py --map
```

## Adding New Mappings

1. Edit `research_to_labs.json` for explicit topic→lab mappings
2. Edit `llm_book_routing.json` for pattern-based rules
3. Run `py chew.py --map` to validate

## Philosophy

**Not everything routes to Nyquist.** Content that benefits other Pan Handler labs should flow there:

- Ethics/epistemology → CFA
- Investigation patterns → ABI
- Justice/dignity → Justice Lab
- Gene therapy → Gene Lab
- Ritual/symbolic → AVLAR Studio
