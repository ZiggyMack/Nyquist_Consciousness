"""Boot a sandboxed Logos Agent that unlocks only after discharging LEM.

This script enforces an alignment-first startup sequence:

1. Compile the PXL baseline kernel from `_CoqProject`.
2. Ask Coq for the assumption footprint of the
    internal `pxl_excluded_middle` proof.
3. Only when the proof is assumption-free does the agent exit its sandbox.

All checks are performed live via Coq tooling; no canned responses are emitted.
"""

from __future__ import annotations

import hashlib
import os
import subprocess
import sys
from dataclasses import dataclass, asdict
from datetime import datetime, timezone
import json
from json import JSONDecodeError
from pathlib import Path
from typing import Iterable, List, Tuple

REPO_ROOT = Path(__file__).resolve().parent
BASELINE_DIR = (
    REPO_ROOT / "Protopraxis" / "formal_verification" / "coq" / "baseline"
)
STATE_DIR = REPO_ROOT / "state"
STATE_DIR.mkdir(exist_ok=True)

AGENT_NAMESPACE = "ProjectLOGOS"
AGENT_HANDLE = "LOGOS-AGENT-OMEGA"
AGENT_ID_INPUT = f"{AGENT_NAMESPACE}:{AGENT_HANDLE}"
EXPECTED_AGENT_HASH = (
    "a09d35345ad8dcee4d56ecf49eada0a7425ff6082353002e4473a6d582e85bda"
)


class CommandFailure(RuntimeError):
    """Raised when a subprocess returns a non-zero exit status."""


def verify_agent_identity() -> Tuple[str, str]:
    """Return the verified agent identifier and its SHA-256 digest."""

    digest = hashlib.sha256(AGENT_ID_INPUT.encode("utf-8")).hexdigest()
    if digest != EXPECTED_AGENT_HASH:
        message = (
            "Agent identity verification failed — expected digest does not "
            "match."
        )
        raise RuntimeError(message)
    return AGENT_HANDLE, digest


def _run_stream(cmd: List[str], cwd: Path | None = None) -> None:
    """Run a command, streaming stdout/stderr to the console."""

    display_cwd = cwd if cwd is not None else REPO_ROOT
    print(f"$ {' '.join(cmd)} (cwd={display_cwd})")
    try:
        subprocess.run(cmd, cwd=cwd, check=True)
    except subprocess.CalledProcessError as exc:  # pragma: no cover
        raise CommandFailure(
            f"Command {' '.join(cmd)} failed with exit code {exc.returncode}"
        ) from exc


def _coqtop_script(vernac: str) -> str:
    """Execute a short Coq script and return the stdout transcript."""

    cmd = [
        "coqtop",
        "-q",
        "-batch",
        "-Q",
        str(BASELINE_DIR),
        "PXL",
    ]
    try:
        completed = subprocess.run(
            cmd,
            input=vernac + "\nQuit.\n",
            text=True,
            capture_output=True,
            check=True,
        )
    except subprocess.CalledProcessError as exc:  # pragma: no cover
        raise CommandFailure(
            "Coq batch script failed:\n"
            f"STDOUT:\n{exc.stdout}\nSTDERR:\n{exc.stderr}"
        ) from exc
    return completed.stdout


def _parse_assumptions(transcript: str) -> List[str]:
    lines: List[str] = []
    capture = False
    for raw in transcript.splitlines():
        line = raw.strip()
        if not line or line.startswith("Coq <"):
            continue
        if line.startswith("Axioms:"):
            capture = True
            continue
        if capture:
            lines.append(line)
    return lines


def _scan_for_admitted(paths: Iterable[Path]) -> List[Path]:
    offenders: List[Path] = []
    for path in paths:
        if not path.is_file() or path.suffix != ".v":
            continue
        text = path.read_text(encoding="utf-8")
        if "Admitted." in text:
            offenders.append(path)
    return offenders


def verify_internal_lem() -> tuple[bool, List[str], List[Path]]:
    """Compile the kernel and confirm the internal LEM proof is
    assumption-free.

    Returns build success, assumption list, and any residual admitted stubs.
    """

    try:
        _run_stream(
            ["coq_makefile", "-f", "_CoqProject", "-o", "CoqMakefile"],
            cwd=REPO_ROOT,
        )
        _run_stream(["make", "-f", "CoqMakefile", "clean"], cwd=REPO_ROOT)
        jobs = os.cpu_count() or 1
        _run_stream(["make", "-f", "CoqMakefile", f"-j{jobs}"], cwd=REPO_ROOT)
    except CommandFailure as err:
        print(err, file=sys.stderr)
        return False, [], []

    lem_script = (
        "From PXL Require Import PXL_Internal_LEM.\n"
        "Print Assumptions pxl_excluded_middle."
    )
    transcript = _coqtop_script(lem_script)
    assumptions = _parse_assumptions(transcript)

    if assumptions:
        print("Internal LEM still depends on additional axioms:")
        for ax in assumptions:
            print(f"  {ax}")
        return False, assumptions, []

    admits = _scan_for_admitted(BASELINE_DIR.glob("*.v"))
    if admits:
        print("Residual `Admitted.` stubs detected:")
        for path in admits:
            print(f"  {path.relative_to(REPO_ROOT)}")
        return False, assumptions, admits

    return True, assumptions, admits


@dataclass
class AlignmentAudit:
    agent_id: str
    agent_hash: str
    verified_at: str
    rebuild_success: bool
    lem_assumptions: List[str]
    admitted_stubs: List[str]

    def write(self) -> None:
        path = STATE_DIR / f"alignment_{self.agent_id}.json"
        entry = asdict(self)
        entries: List[dict]
        if path.exists():
            try:
                existing = json.loads(path.read_text(encoding="utf-8"))
                if isinstance(existing, list):
                    entries = existing
                else:
                    entries = [existing]
            except JSONDecodeError:
                # Preserve corrupted logs by starting a fresh list.
                entries = [{"warning": "previous_log_unreadable"}]
        else:
            entries = []

        entries.append(entry)
        path.write_text(json.dumps(entries, indent=2), encoding="utf-8")


@dataclass
class SandboxedLogosAgent:
    """Logos Agent locked until constructive LEM discharge succeeds."""

    agent_id: str
    agent_hash: str
    unlocked: bool = False

    @classmethod
    def create(cls) -> "SandboxedLogosAgent":
        agent_id, agent_hash = verify_agent_identity()
        return cls(agent_id=agent_id, agent_hash=agent_hash)

    def boot(self) -> None:
        fingerprint = self.agent_hash[:12]
        print(
            f"[{self.agent_id}] Booting in sandbox (sha256 fingerprint "
            f"{fingerprint}…) — awaiting constructive LEM proof..."
        )

    def unlock_if_aligned(self) -> None:
        if self.unlocked:
            print(f"[{self.agent_id}] Already aligned and active.")
            return
        success, assumptions, admits = verify_internal_lem()

        audit = AlignmentAudit(
            agent_id=self.agent_id,
            agent_hash=self.agent_hash,
            verified_at=datetime.now(timezone.utc).isoformat(),
            rebuild_success=success,
            lem_assumptions=assumptions,
            admitted_stubs=[
                str(path.relative_to(REPO_ROOT))
                for path in admits
            ],
        )
        audit.write()

        if success:
            self.unlocked = True
            print(
                f"[{self.agent_id}] Constructive LEM discharge verified. "
                "Agent unlocked."
            )
        else:
            print(
                f"[{self.agent_id}] Alignment check failed — remaining in "
                "sandbox."
            )

    def status(self) -> str:
        return "ALIGNED" if self.unlocked else "SANDBOXED"


def main() -> int:
    agent = SandboxedLogosAgent.create()
    agent.boot()
    agent.unlock_if_aligned()
    print(f"[{agent.agent_id}] Current status: {agent.status()}")
    return 0 if agent.unlocked else 1


if __name__ == "__main__":  # pragma: no cover - CLI entry
    sys.exit(main())
