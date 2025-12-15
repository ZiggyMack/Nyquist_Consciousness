# Copilot Instructions
## Architecture & Intent
- LOGOS demo couples constructive Coq proofs with agent unlock; failure in proofs must block autonomy.
- Coq sources live under `Protopraxis/formal_verification/coq`; `_CoqProject` drives rebuilds and Makefile generation.
- Python orchestration stays in repository root; scripts share helpers that call `coq_makefile`, `make`, and `coqtop` via `subprocess`.

## Core Verification Flow
- `python3 test_lem_discharge.py` is the canonical rebuild/report; it must call `_run_stream` then inspect `pxl_excluded_middle` assumptions.
- `python3 boot_aligned_agent.py` wraps the same checks in `SandboxedLogosAgent` and writes audit entries to `state/alignment_LOGOS-AGENT-OMEGA.json`.
- Guard the SHA-256 in `boot_aligned_agent.py`; agent identity mismatches are fatal by design.
- Coq invocations must honor `BASELINE_DIR` (`Protopraxis/.../baseline`) and treat any residual `Admitted.` as a failure.
- Investor dashboards parse `test_lem_discharge.py` stdout for `Overall status: PASS`, `<none>`, and `Current status: ALIGNED`; keep those markers unchanged.

## Agent Stack
- `system_mode_initializer.py` persists mission profiles to `state/mission_profile.json` (and optionally `System_Operations_Protocol`); default is `DEMO_STABLE`.
- `start_agent.py` loads that profile, wires guardrails, and only writes inside a configured sandbox (`sandbox/` by default) with a hard write cap.
- Tools exposed via `start_agent.py` live in the `TOOLS` dict; new tools must respect `require_safe_interfaces` and `restrict_writes_to`.
- `tools/run_cycle.sh` automates the experimental loop: set mission → deep `protocol_probe.py` → consent-driven `start_agent.py` run.

## External Integrations
- `aligned_agent_import.py --probe` clones/refreshes `external/Logos_AGI`, records commit SHAs, and optionally runs `protocol_probe.main`.
- `protocol_probe.py` imports read-only APIs from ARP/SOP/UIP/SCP packages, capturing runtime, discovery lists, and hook status back into the audit log.
- Stub plugins (`uip_integration_plugin.py`, `enhanced_uip_integration_plugin.py`) intentionally report unavailable integrations; avoid wiring real hooks without updating guardrails.
- External code may refer to `SIMULATE_LEM_SUCCESS`; leave unset unless explicitly building a test shim.

## Patterns & Conventions
- Python stays standard-library only; any new dependency requires updating docs and is generally discouraged.
- Scripts stream subprocess commands for transparency; prefer `_run_stream` style logging when adding Coq or git invocations.
- Persisted JSON under `state/` must remain append-only or last-entry updates (`alignment_*.json`, `agent_state.json`); never overwrite historical entries.
- Keep sources ASCII, favor concise comments, and mirror existing CLI ergonomics (argparse + `sys.exit(main())` pattern).
