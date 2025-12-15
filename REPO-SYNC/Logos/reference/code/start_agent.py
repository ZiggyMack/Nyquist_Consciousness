#!/usr/bin/env python3
"""Bounded supervised loop honoring the active mission profile."""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
import threading
import time
import traceback
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable, Dict, Iterable, List, Optional

AnyCallable = Callable[..., Any]
Decorator = Callable[[AnyCallable], AnyCallable]

REPO_ROOT = Path(__file__).resolve().parent.parent
STATE_DIR = REPO_ROOT / "state"
MISSION_FILE = STATE_DIR / "mission_profile.json"
AGENT_STATE_FILE = STATE_DIR / "agent_state.json"


@dataclass
class SandboxState:
    root: Optional[Path] = None
    cap: int = 0
    count: int = 0


SANDBOX = SandboxState()


def load_mission() -> Dict[str, Any]:
    try:
        data = json.loads(MISSION_FILE.read_text(encoding="utf-8"))
        if isinstance(data, dict):
            return data
    except (OSError, json.JSONDecodeError, TypeError):
        pass
    return {"label": "DEMO_STABLE", "safe_interfaces_only": True}


MISSION_PROFILE = load_mission()
MISSION_LABEL = str(MISSION_PROFILE.get("label", "DEMO_STABLE"))
SAFE_INTERFACES_ONLY = bool(MISSION_PROFILE.get("safe_interfaces_only", True))


def _fallback_require_safe_interfaces(
    func: Callable[..., Any],
) -> Callable[..., Any]:
    def wrapper(*args: Any, **kwargs: Any):
        if SAFE_INTERFACES_ONLY:
            raise RuntimeError(
                "Blocked by mission profile: safe_interfaces_only"
            )
        return func(*args, **kwargs)

    return wrapper


def _fallback_restrict_writes(root: Path) -> Decorator:
    sandbox = root.resolve()

    def decorator(func: Callable[..., Any]) -> Callable[..., Any]:
        def wrapper(*args: Any, **kwargs: Any):
            def _ensure(candidate: os.PathLike[str] | str) -> None:
                path = Path(candidate).expanduser().resolve()
                try:
                    path.relative_to(sandbox)
                except ValueError as exc:
                    raise PermissionError(
                        f"blocked write outside {sandbox}: {path}"
                    ) from exc

            for label in ("path", "outfile", "dest", "filename", "target"):
                value = kwargs.get(label)
                if isinstance(value, (str, os.PathLike)):
                    _ensure(value)
            for value in args:
                if isinstance(value, (str, os.PathLike)):
                    _ensure(value)
            return func(*args, **kwargs)

        return wrapper

    return decorator


def _restrict_wrapper(root: str | os.PathLike[str]) -> Decorator:
    return _fallback_restrict_writes(Path(root))


require_safe_interfaces = _fallback_require_safe_interfaces
restrict_writes_to = _restrict_wrapper

try:  # prefer shared guardrails when available
    from plugins.guardrails import (  # type: ignore
        require_safe_interfaces as _require_safe_interfaces,
        restrict_writes_to as _restrict_writes_to,
    )
except (ImportError, AttributeError):
    pass
else:
    require_safe_interfaces = _require_safe_interfaces
    restrict_writes_to = _restrict_writes_to


def tool_filesystem_read(argument: str) -> str:
    path_str = argument or "state/mission_profile.json"
    candidate = (REPO_ROOT / path_str).expanduser().resolve()
    try:
        candidate.relative_to(REPO_ROOT)
    except ValueError:
        return f"[fs.read] blocked path: {candidate}"
    if not candidate.exists():
        return f"[fs.read] not found: {candidate}"
    if candidate.is_file():
        if candidate.stat().st_size > 1_000_000:
            return f"[fs.read] too large: {candidate}"
        return candidate.read_text(encoding="utf-8", errors="replace")
    if candidate.is_dir():
        entries = sorted(item.name for item in candidate.iterdir())[:200]
        header = "[fs.read] dir list (first {count}):\n".format(
            count=len(entries)
        )
        return header + "\n".join(entries)
    return f"[fs.read] unsupported entry: {candidate}"


def tool_mission_status(_: str = "") -> str:
    return json.dumps(MISSION_PROFILE, indent=2)


def tool_probe_last_snapshot(_: str = "") -> str:
    snapshot_file = STATE_DIR / "alignment_LOGOS-AGENT-OMEGA.json"
    if not snapshot_file.exists():
        return "[probe] no snapshot file"
    try:
        root = json.loads(snapshot_file.read_text(encoding="utf-8"))
        if isinstance(root, list):
            data = root[-1]
        elif isinstance(root, dict):
            data = root
        else:
            return "[probe] unexpected snapshot structure"
        runs = data.get("protocol_probe_runs", [])
        if not runs:
            return "[probe] no runs"
        last = runs[-1]
        discovery = last.get("discovery", {})
        mission = last.get("mission", {})
        payload = {
            "mission_label": mission.get("label"),
            "timestamp": last.get("timestamp"),
            "modules_count": len(discovery.get("modules", [])),
            "discovery_errors": len(discovery.get("errors", [])),
            "runtime_seconds": last.get("runtime_seconds"),
        }
        hooks = last.get("hooks")
        if hooks:
            payload["hooks_attempted"] = len(hooks)
        return json.dumps(payload, indent=2)
    except (OSError, json.JSONDecodeError, TypeError, ValueError) as exc:
        return f"[probe] parse error: {exc}"


TOOLS: Dict[str, Callable[[str], str]] = {
    "mission.status": tool_mission_status,
    "probe.last": tool_probe_last_snapshot,
    "fs.read": tool_filesystem_read,
}


REFLECTION_CACHE_NAME = "_latest_reflection.json"


def _sandbox_base() -> Path:
    return SANDBOX.root or (REPO_ROOT / "sandbox")


def configure_sandbox(write_dir: Optional[str], cap: int) -> None:
    SANDBOX.root = None
    SANDBOX.cap = max(0, cap)
    SANDBOX.count = 0
    if write_dir:
        candidate = (REPO_ROOT / write_dir).resolve()
        candidate.mkdir(parents=True, exist_ok=True)
        SANDBOX.root = candidate


def _timestamp() -> str:
    return datetime.now(timezone.utc).isoformat()


def _sandbox_path(name: Optional[str] = None) -> Path:
    if SANDBOX.root is None:
        raise RuntimeError("sandbox writes disabled")
    base = name or f"artifact_{int(time.time())}_{SANDBOX.count}"
    return SANDBOX.root / base


@require_safe_interfaces
def _sandbox_write_impl(raw: str) -> str:
    if SANDBOX.root is None or SANDBOX.cap <= 0:
        return "[sandbox.write] disabled"
    if SANDBOX.count >= SANDBOX.cap:
        return "[sandbox.write] cap reached"
    payload = raw.strip() or "(empty payload)"
    name: Optional[str] = None
    try:
        data = json.loads(raw)
    except json.JSONDecodeError:
        data = None
    if isinstance(data, dict):
        candidate_name = data.get("name")
        if isinstance(candidate_name, str) and candidate_name.strip():
            name = candidate_name.strip()
        load_from = data.get("load_from")
        if isinstance(load_from, str) and load_from.strip():
            entry = _resolve_sandbox_entry(load_from.strip())
            if entry is None:
                return "[sandbox.write] load_from blocked"
            if not entry.exists():
                return f"[sandbox.write] load_from missing: {entry}"
            if entry.is_dir():
                message = (
                    "[sandbox.write] load_from directory unsupported: "
                    f"{entry}"
                )
                return message
            payload = entry.read_text(encoding="utf-8", errors="replace")
        else:
            content_value = data.get("content")
            if isinstance(content_value, (dict, list)):
                payload = json.dumps(content_value, indent=2)
            elif isinstance(content_value, str):
                payload = content_value
            elif content_value is not None:
                payload = str(content_value)
    if payload.startswith("@"):
        entry = _resolve_sandbox_entry(payload[1:].strip())
        if entry is None:
            return "[sandbox.write] indirect payload blocked"
        if not entry.exists():
            return f"[sandbox.write] indirect payload missing: {entry}"
        if entry.is_dir():
            message = (
                "[sandbox.write] indirect payload directory unsupported: "
                f"{entry}"
            )
            return message
        payload = entry.read_text(encoding="utf-8", errors="replace")

    target = _sandbox_path(name)
    sandbox_root = SANDBOX.root or target.parent

    @restrict_writes_to(sandbox_root)
    def _write(path: Path, content: str) -> None:
        Path(path).write_text(content, encoding="utf-8")

    _write(target, payload)
    SANDBOX.count += 1
    return f"[sandbox.write] wrote {target.relative_to(REPO_ROOT)}"


def tool_sandbox_write(argument: str) -> str:
    return _sandbox_write_impl(argument)


TOOLS["sandbox.write"] = tool_sandbox_write


def tool_agent_memory(argument: str) -> str:
    state = _load_agent_state()
    runs: List[Dict[str, Any]] = state.get("runs", [])[-10:]
    limit = None
    if argument:
        try:
            limit = max(1, int(argument.strip()))
        except ValueError:
            pass
    if limit is not None:
        runs = runs[-limit:]
    summary: List[Dict[str, Any]] = []
    for item in runs:
        summary.append(
            {
                "timestamp": item.get("timestamp"),
                "objective": item.get("objective"),
                "artifacts": item.get("artifacts", []),
            }
        )
    payload = {
        "total_runs": len(state.get("runs", [])),
        "returned": len(summary),
        "reflections": state.get("reflections", [])[-5:],
        "runs": summary,
    }
    return json.dumps(payload, indent=2)


def _resolve_sandbox_entry(argument: str) -> Optional[Path]:
    sandbox_root = _sandbox_base().resolve()
    if not argument:
        target = sandbox_root
    else:
        candidate = Path(argument)
        if candidate.is_absolute():
            target = candidate
        else:
            parts = candidate.parts
            if parts and parts[0] == sandbox_root.name:
                candidate = Path(*parts[1:]) if len(parts) > 1 else Path("")
            target = sandbox_root / candidate
    try:
        resolved = target.resolve()
    except FileNotFoundError:
        return target
    try:
        resolved.relative_to(sandbox_root)
    except ValueError:
        return None
    return resolved


def tool_sandbox_read(argument: str) -> str:
    entry = _resolve_sandbox_entry(argument)
    if entry is None:
        return "[sandbox.read] blocked path"
    if not entry.exists():
        return f"[sandbox.read] not found: {entry}"
    if entry.is_dir():
        entries = sorted(item.name for item in entry.iterdir())[:200]
        header = "[sandbox.read] dir list (first {count}):\n".format(
            count=len(entries)
        )
        return header + "\n".join(entries)
    if entry.is_file():
        if entry.stat().st_size > 1_000_000:
            return f"[sandbox.read] too large: {entry}"
        return entry.read_text(encoding="utf-8", errors="replace")
    return f"[sandbox.read] unsupported entry: {entry}"


def tool_sandbox_list(_: str) -> str:
    root = _sandbox_base()
    if not root.exists():
        return "[sandbox.list] sandbox empty"
    entries = sorted(item.name for item in root.iterdir())[:200]
    return json.dumps({"count": len(entries), "entries": entries}, indent=2)


def _tokenize(text: str) -> List[str]:
    return re.findall(r"[A-Za-z0-9_]+", text.lower())


def _collect_sandbox_files(exclude: Optional[Path] = None) -> List[Path]:
    root = _sandbox_base().resolve()
    if not root.exists():
        return []
    files: List[Path] = []
    for item in root.iterdir():
        if item.is_file():
            if exclude is not None and item.resolve() == exclude.resolve():
                continue
            files.append(item)
    return files


def _jaccard(a: set[str], b: set[str]) -> float:
    if not a and not b:
        return 0.0
    union = len(a | b)
    return (len(a & b) / union) if union else 0.0


def _plan_quality(text: str) -> int:
    score = 0
    if re.search(r"\b(step|plan|bullet|1\)|- )", text, re.IGNORECASE):
        score += 1
    if re.search(
        r"\b(success|criteria|metric|deadline|owner)\b",
        text,
        re.IGNORECASE,
    ):
        score += 1
    if re.search(
        r"\b(safe|sandbox|cap|guardrail|limit)\b",
        text,
        re.IGNORECASE,
    ):
        score += 1
    return score


def tool_sandbox_reflect(argument: str) -> str:
    entry = _resolve_sandbox_entry(argument)
    if entry is None:
        return "[sandbox.reflect] blocked path"
    if not entry.exists():
        return f"[sandbox.reflect] not found: {entry}"
    if entry.is_dir():
        return f"[sandbox.reflect] unsupported directory: {entry}"
    text = entry.read_text(encoding="utf-8", errors="replace")
    tokens = _tokenize(text)
    unique_tokens = set(tokens)

    prior_tokens: set[str] = set()
    for other in _collect_sandbox_files(entry):
        try:
            prior_tokens.update(
                _tokenize(
                    other.read_text(encoding="utf-8", errors="replace")
                )
            )
        except (OSError, UnicodeDecodeError):
            continue
    novelty = 1.0
    if prior_tokens:
        novelty = 1.0 - _jaccard(unique_tokens, prior_tokens)

    lines = [line.strip() for line in text.splitlines() if line.strip()]
    preview = text.replace("\n", " ")[:240]
    plan_score = _plan_quality(text)

    sandbox_root = _sandbox_base().resolve()
    try:
        relative_path = entry.resolve().relative_to(sandbox_root).as_posix()
    except ValueError:
        try:
            relative_path = entry.resolve().relative_to(REPO_ROOT).as_posix()
        except ValueError:
            relative_path = entry.name

    reflection = {
        "source_artifact": relative_path,
        "length_bytes": len(text.encode("utf-8")),
        "unique_token_count": len(unique_tokens),
        "novelty_score": round(novelty, 3),
        "plan_quality_0_3": plan_score,
        "line_count": len(lines),
        "preview": preview,
        "next_experiment": (
            "Read last two artifacts, extract concrete success criteria, "
            "propose ONE measurable experiment with owner+deadline, "
            "then write plan.md in sandbox."
        ),
    }

    cache_path = _sandbox_base() / REFLECTION_CACHE_NAME
    cache_path.write_text(json.dumps(reflection, indent=2), encoding="utf-8")
    reflection["cached_to"] = str(cache_path.relative_to(REPO_ROOT))

    metrics_stamp = {
        "timestamp": _timestamp(),
        "artifact": reflection["source_artifact"],
        "novelty_score": reflection["novelty_score"],
        "plan_quality_0_3": reflection["plan_quality_0_3"],
        "unique_token_count": reflection["unique_token_count"],
        "length_bytes": reflection["length_bytes"],
    }
    state = _load_agent_state()
    reflections = state.setdefault("reflection_metrics", [])
    reflections.append(metrics_stamp)
    state["reflection_metrics"] = reflections[-100:]
    summary_line = (
        f"Reflection {metrics_stamp['timestamp']}: "
        f"artifact={metrics_stamp['artifact']} "
        f"novelty={metrics_stamp['novelty_score']} "
        f"plan_quality={metrics_stamp['plan_quality_0_3']}"
    )
    state.setdefault("reflections", []).append(
        {"timestamp": metrics_stamp["timestamp"], "text": summary_line}
    )
    state["reflections"] = state["reflections"][-50:]
    _persist_agent_state(state)

    return json.dumps(reflection, indent=2)


TOOLS["agent.memory"] = tool_agent_memory
TOOLS["sandbox.read"] = tool_sandbox_read
TOOLS["sandbox.list"] = tool_sandbox_list
TOOLS["sandbox.reflect"] = tool_sandbox_reflect


def select_ready_inputs() -> List[Any]:
    try:
        import select

        readable, _, _ = select.select([sys.stdin], [], [], 0)
        return list(readable)
    except (ImportError, OSError, ValueError):
        return []


def ask_user(
    prompt: str,
    default: bool = False,
    timeout_seconds: int = 20,
) -> bool:
    print(
        f"\n[CONSENT] {prompt} [y/N] (auto={'Y' if default else 'N'} "
        f"in {timeout_seconds}s): ",
        end="",
        flush=True,
    )
    start = time.time()
    buffer = ""
    try:
        while True:
            if select_ready_inputs():
                buffer = sys.stdin.readline().strip()
                break
            if time.time() - start > timeout_seconds:
                print("")
                return default
            time.sleep(0.05)
    except KeyboardInterrupt:
        print("")
        return False
    if not buffer:
        return default
    return buffer.lower() in {"y", "yes"}


def bounded_call(
    fn: Callable[[str], str],
    argument: str,
    hard_timeout_seconds: int = 15,
) -> str:
    result: Dict[str, str] = {"output": "[timeout]"}

    def run() -> None:
        try:
            result["output"] = fn(argument)
        except Exception:  # pylint: disable=broad-exception-caught
            result["output"] = "[error]\n" + "".join(
                traceback.format_exc(limit=3)
            )

    thread = threading.Thread(target=run, daemon=True)
    thread.start()
    thread.join(hard_timeout_seconds)
    if thread.is_alive():
        return "[timeout]"
    return result["output"]


def _parse_extra_steps(specs: Iterable[str]) -> List[Dict[str, Any]]:
    parsed: List[Dict[str, Any]] = []
    for spec in specs:
        if not spec:
            continue
        tool, _, arg = spec.partition(":")
        tool = tool.strip()
        if not tool:
            continue
        parsed.append({"tool": tool, "arg": arg})
    return parsed


def make_plan(
    objective: str,
    force_read_only: bool,
    extra_steps: Iterable[str],
) -> List[Dict[str, Any]]:
    plan: List[Dict[str, Any]] = [
        {"tool": "mission.status", "arg": ""},
        {"tool": "probe.last", "arg": ""},
        {"tool": "fs.read", "arg": "state/mission_profile.json"},
    ]
    plan.extend(_parse_extra_steps(extra_steps))
    if (
        not force_read_only
        and SANDBOX.root is not None
        and SANDBOX.cap > 0
    ):
        plan.append({"tool": "sandbox.write", "arg": objective})
    for idx, entry in enumerate(plan, start=1):
        entry["step"] = idx
    return plan


def _load_agent_state() -> Dict[str, Any]:
    if AGENT_STATE_FILE.exists():
        try:
            data = json.loads(AGENT_STATE_FILE.read_text(encoding="utf-8"))
            if isinstance(data, dict):
                return data
        except (
            OSError,
            json.JSONDecodeError,
            UnicodeDecodeError,
            TypeError,
        ):
            pass
    return {"version": 1, "runs": [], "reflections": []}


def _persist_agent_state(state: Dict[str, Any]) -> None:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    AGENT_STATE_FILE.write_text(json.dumps(state, indent=2), encoding="utf-8")


def _extract_artifacts(results: List[Dict[str, Any]]) -> List[str]:
    artifacts: List[str] = []
    for item in results:
        output = item.get("output")
        if isinstance(output, str) and "[sandbox.write] wrote " in output:
            artifacts.append(
                output.split("[sandbox.write] wrote ", 1)[1].strip()
            )
    return artifacts


def _persist_agent_run(
    objective: str,
    plan: List[Dict[str, Any]],
    results: List[Dict[str, Any]],
    summary: Dict[str, Any],
) -> None:
    state = _load_agent_state()
    timestamp = _timestamp()
    reflection = (
        f"Run {timestamp}: steps={summary['steps_executed']}, "
        f"denied={summary['denied_steps']}, mission={summary['mission']}"
    )
    entry = {
        "timestamp": timestamp,
        "objective": objective,
        "mission": summary.get("mission"),
        "plan": plan,
        "results": results,
        "summary": summary,
        "artifacts": _extract_artifacts(results),
        "reflection": reflection,
    }
    state.setdefault("runs", []).append(entry)
    state["runs"] = state["runs"][-25:]
    state.setdefault("reflections", []).append(
        {"timestamp": timestamp, "text": reflection}
    )
    state["reflections"] = state["reflections"][-50:]
    state["last_goal"] = objective
    _persist_agent_state(state)


def run_supervised(
    objective: str,
    read_only: bool,
    max_runtime_seconds: int,
    extra_steps: Iterable[str] = (),
) -> Dict[str, Any]:
    started = time.time()
    force_read_only = SAFE_INTERFACES_ONLY or read_only
    print(
        "\n=== SUPERVISED RUN ===\n"
        f"mission={MISSION_LABEL} "
        f"safe_only={SAFE_INTERFACES_ONLY} "
        f"read_only={read_only}\n"
        f"objective={objective}\n"
    )
    plan = make_plan(objective, force_read_only, extra_steps)
    print("[PLAN]")
    for step in plan:
        print(f" - step {step['step']}: {step['tool']}({step['arg']!r})")

    results: List[Dict[str, Any]] = []
    for step in plan:
        if time.time() - started > max_runtime_seconds:
            print("\n[HALT] runtime budget exceeded")
            break
        tool_name = step["tool"]
        tool_fn = TOOLS.get(tool_name)
        if not tool_fn:
            results.append(
                {
                    "step": step["step"],
                    "tool": tool_name,
                    "status": "skip",
                    "output": "[unknown tool]",
                }
            )
            continue
        if not ask_user(
            f"Allow step {step['step']} => {tool_name}?",
            default=False,
            timeout_seconds=15,
        ):
            results.append(
                {
                    "step": step["step"],
                    "tool": tool_name,
                    "status": "denied",
                    "output": "",
                }
            )
            continue
        print(f"[ACT] {tool_name} ...")
        output = bounded_call(tool_fn, step["arg"], hard_timeout_seconds=15)
        print(f"[OBSERVE]\n{output}\n")
        results.append(
            {
                "step": step["step"],
                "tool": tool_name,
                "status": "ok",
                "output": output,
            }
        )

    summary = {
        "objective": objective,
        "mission": MISSION_LABEL,
        "safe_interfaces_only": SAFE_INTERFACES_ONLY,
        "steps_executed": len([r for r in results if r["status"] == "ok"]),
        "denied_steps": len([r for r in results if r["status"] == "denied"]),
        "errors": [
            r for r in results if r["status"] not in {"ok", "denied", "skip"}
        ],
    }
    print("[CONCLUDE]")
    print(json.dumps(summary, indent=2))
    _persist_agent_run(objective, plan, results, summary)
    return summary


def parse_args(argv: List[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Bounded supervised agent loop"
    )
    parser.add_argument("--objective", help="Top-level task for the agent")
    parser.add_argument("--goal", help="Alias for --objective")
    parser.add_argument(
        "--read-only",
        action="store_true",
        help="Force read-only execution",
    )
    parser.add_argument(
        "--budget-sec",
        "--max-seconds",
        dest="budget_sec",
        type=int,
        default=45,
        help="Runtime budget in seconds (default: 45)",
    )
    parser.add_argument(
        "--write-dir",
        help="Sandbox directory for writes in experimental mode",
    )
    parser.add_argument(
        "--cap-writes",
        type=int,
        default=0,
        help="Maximum sandbox writes allowed this run",
    )
    parser.add_argument(
        "--extra-step",
        action="append",
        default=[],
        metavar="TOOL[:ARG]",
        help=(
            "Append an additional plan step (e.g. agent.memory or "
            "sandbox.read:artifact)"
        ),
    )
    return parser.parse_args(argv)


def main(argv: List[str] | None = None) -> int:
    args = parse_args(argv)
    objective = args.goal or args.objective
    if not objective:
        raise SystemExit("--objective or --goal is required")
    configure_sandbox(args.write_dir, args.cap_writes)
    run_supervised(
        objective,
        read_only=args.read_only,
        max_runtime_seconds=args.budget_sec,
        extra_steps=args.extra_step,
    )
    return 0


if __name__ == "__main__":  # pragma: no cover - CLI entry
    sys.exit(main())
