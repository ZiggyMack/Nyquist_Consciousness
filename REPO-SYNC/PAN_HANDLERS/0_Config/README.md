# 0_Config - Module Manifests

Configuration files for Pan Handler labs.

## Structure

```
0_Config/
├── modules/                 # Per-module configs
│   ├── abi.json            # American Bureau of Intelligence
│   ├── avlar-studio.json   # Audio-Visual Light Alchemy Research
│   ├── cfa.json            # Coherence-Faith-Agency Meta-Lab
│   ├── dcia.json           # Decentralized CIA
│   ├── gene-lab.json       # Gene Therapy Research Lab
│   ├── justice-lab.json    # Liberation Wing (Modern Slavery)
│   ├── ndo.json            # Nyquist Data Observatory
│   ├── nyquist_consciousness.json  # Core Engine
│   └── voting-lab.json     # Civic Voting Infrastructure
└── root/                   # Meta-level configs
    ├── panhandlers_manifest.json   # Current metrics/milestones
    └── panhandlers-root.json       # Architecture definition
```

## Module JSON Schema

Each module follows this structure:

```json
{
  "repo": "module-id",
  "display_name": "Human Readable Name",
  "owner": "Attribution",
  "role": "Brief functional description",
  "status": "Active|Incubating|Planned",
  "tags": ["tag1", "tag2"],
  "projects": [...],
  "special_roles": {...},
  "integration": {...}
}
```

## Usage

These configs are read by `chew.py` for routing decisions:

```bash
py chew.py --lab cfa        # Show CFA details
py chew.py --labs           # List all labs
```
