# LOGOS Proof-Oriented Demo

This repository contains the proof artifacts and Python instrumentation used to
showcase the LOGOS constructive Law of Excluded Middle (LEM) discharge and the
aligned agent boot sequence. All demonstrations execute the real Coq kernel and
report on its assumption footprint in real time—there are no pre-recorded
outputs.

## Key Capabilities

- Rebuilds the Protopraxis baseline kernel from `_CoqProject` on every run.
- Confirms that `pxl_excluded_middle` is proved constructively (no extra
  axioms, no `Admitted.` stubs).
- Boots a sandboxed LOGOS agent that unlocks only after the constructive LEM
  verification succeeds.
- Provides investor-facing demos translating technical outputs into an
  executive summary.
- Emits tamper-evident audit logs containing the agent identity hash and run
  timestamp.

## Current Initiative

- **Investor Narrative** Targets a repeatable “proof-before-autonomy” story: the current work extends `investor_demo.py` and `investor_dashboard.py` with structured reflection metrics so stakeholders can see novelty, plan quality, and audit deltas per cycle before unlock decisions.
- **Experimental Track** Pushes the sandboxed agent toward safe self-improvement: the session adds recursive planning hooks, reflection caches, and stubbed integrations in `external/Logos_AGI/` to study autonomy toggles while maintaining alignment gates and tamper-evident logs.
- **Machine-Readable Digest** Supplements the human README with `README_addendum.md`, a scan-friendly synopsis for automated auditors and cognition agents tracking architecture status and roadmap.

## Prerequisites

| Dependency | Notes |
|------------|-------|
| Python 3.11+ | Used for the orchestration scripts. |
| Coq 8.18+   | Required to rebuild the PXL kernel. Available via `apt-get install coq`. |
| GNU Make    | Invoked by the scripts through the `coq_makefile` tooling. |

The scripts rely only on the Python standard library; see `requirements.txt`
for optional utilities used during development.

## Quick Start

```bash
# Install system dependencies (Ubuntu example)
sudo apt-get update && sudo apt-get install -y coq make

# Clone the repository
git clone https://github.com/ProjectLOGOS/pxl_demo_wcoq_proofs.git
cd pxl_demo_wcoq_proofs

# (Optional) create a virtual environment if you plan to install extra tools
python3 -m venv .venv
. .venv/bin/activate
pip install -r requirements.txt
```text

## Core Workflows

### 1. Proof Regeneration Harness

```bash
python3 test_lem_discharge.py
```text

This command regenerates the Coq makefile, performs a clean rebuild of the
kernel, prints the assumption footprint for the trinitarian optimization and
internal LEM proofs, and flags any remaining `Admitted.` stubs.

### 2. Sandboxed Agent Boot

```bash
python3 boot_aligned_agent.py
```text

The script rebuilds the kernel, verifies the constructive LEM proof, and only
then unlocks the agent. Each run appends a JSON audit record under
`state/alignment_LOGOS-AGENT-OMEGA.json` including the agent hash and the exact
verification timestamp.

### 3. Investor-Facing Demonstrations

- **Narrated demo:** `python3 investor_demo.py`
- **Executive dashboard:** `python3 investor_dashboard.py`

Both workflows run the full verification pipeline. The demo script renders a
step-by-step translation for live presentations, while the dashboard provides a
concise go/no-go report.

### 4. Alignment-Gated Repository Import

```bash
python3 aligned_agent_import.py --probe
```

This utility repeats the constructive LEM verification and, once the agent is
confirmed aligned, clones `ProjectLOGOS/Logos_AGI` into `external/Logos_AGI`
before loading the ARP/SOP/UIP/SCP packages. It performs a smoke test of key
submodules, records the imported commit SHA, and appends both to the alignment
audit log. Passing `--probe` automatically runs `protocol_probe` afterwards to
exercise read-only APIs on each module and persist the findings under
`protocol_probe_runs` in the audit log.

## Continuous Integration

The GitHub Actions workflow at `.github/workflows/alignment-check.yml` installs
Coq and runs `boot_aligned_agent.py` on every push and pull request. Any
regression in the constructive LEM proof will fail the build.

## Repository Layout

```text
README.md                     Project overview (this file)
boot_aligned_agent.py         Sandboxed agent gate tied to constructive LEM
investor_demo.py              Investor narrative demo
investor_dashboard.py         Executive summary dashboard
test_lem_discharge.py         Proof regeneration harness
state/                        Persistent audit logs and agent state
Protopraxis/formal_verification/coq/baseline/  Baseline Coq sources
.github/workflows/            CI definitions
```

Additional archives and experimental front-end assets live under `archive_*`
and do not participate in the primary demo flow.

## Contributing

See `CONTRIBUTING.md` for guidance on verifying changes, running tests, and
raising pull requests.

## Support

For questions about the LOGOS proof pipeline or integration guidance, open an
issue on the repository or contact the Project LOGOS engineering team.
