#!/usr/bin/env bash
set -euo pipefail

MODE=${1:-experimental}
GOAL=${2:-"Read last artifact, produce 3-bullet recap (facts only), propose one measurable experiment with success criteria, then write plan.md."}

./.venv/bin/python system_mode_initializer.py --mode "$MODE"

timeout 90s ./.venv/bin/python protocol_probe.py --log-only --deep --agentic-probe --timeout 6

LATEST=$(./.venv/bin/python - <<'PY'
import json
from pathlib import Path
state_path = Path('state/agent_state.json')
if not state_path.exists():
    print("", end="")
else:
    data = json.loads(state_path.read_text())
    artifacts = [a for run in data.get('runs', []) for a in run.get('artifacts', [])]
    print(artifacts[-1] if artifacts else "", end="")
PY
)

if [[ -n "$LATEST" ]]; then
  CLEANED=${LATEST#sandbox/}
  EXTRA=("--extra-step" "sandbox.reflect:${CLEANED}" "--extra-step" "sandbox.write:{\"name\":\"plan.md\",\"load_from\":\"_latest_reflection.json\"}")
else
  EXTRA=("--extra-step" "sandbox.write:{\"name\":\"bootstrap.txt\",\"content\":\"bootstrap run\"}")
fi

printf 'y\ny\ny\ny\ny\ny\ny\ny\n' | timeout 90s ./.venv/bin/python start_agent.py \
  --goal "$GOAL" \
  --write-dir sandbox --cap-writes 3 --max-seconds 90 \
  "${EXTRA[@]}"
