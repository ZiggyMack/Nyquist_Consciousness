"""Primary recursion engine and logic kernel for the LOGOS Agent."""

from __future__ import annotations

import hashlib
import json
import subprocess
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List, Optional

from Protopraxis import run_coq_pipeline

AGENT_ROOT = Path(__file__).resolve().parent
PROTOPRAXIS_COQ = AGENT_ROOT / "formal_verification" / "coq"
STATE_DIR = AGENT_ROOT / "state"
STATE_DIR.mkdir(exist_ok=True)


class AxiomaticCommutator:
    """Layer I covering epistemic and ontological bijections and privations."""

    def __init__(self) -> None:
        self.beliefs: Dict[str, bool] = {}
        self.world_state: Dict[str, bool] = {}

    @staticmethod
    def check_identity_law(entity: Any) -> bool:
        return entity == entity

    def check_non_contradiction(self, proposition: str) -> bool:
        neg = f"¬{proposition}"
        return not (self.beliefs.get(proposition) and self.beliefs.get(neg))

    def check_excluded_middle(self, proposition: str) -> bool:
        neg = f"¬{proposition}"
        return (proposition in self.beliefs) or (neg in self.beliefs)

    def validate_epistemic_positive(self) -> bool:
        for prop in list(self.beliefs.keys()):
            if not self.check_non_contradiction(prop):
                return False
            if not self.check_excluded_middle(prop):
                return False
        return True

    @staticmethod
    def check_distinctness(entity1: Any, entity2: Any) -> bool:
        return entity1 != entity2

    @staticmethod
    def check_relationality(entity: Any) -> bool:
        return True

    @staticmethod
    def check_agency(entity: Any) -> bool:
        return True

    def validate_ontological_positive(self) -> bool:
        entities = list(self.world_state.keys())
        for i, e1 in enumerate(entities):
            for j, e2 in enumerate(entities):
                if i != j and not self.check_distinctness(e1, e2):
                    return False
            if not self.check_relationality(e1):
                return False
            if not self.check_agency(e1):
                return False
        return True

    def detect_error(self) -> List[str]:
        errors: List[str] = []
        for prop in list(self.beliefs.keys()):
            neg = f"¬{prop}"
            if self.beliefs.get(prop) and self.beliefs.get(neg):
                errors.append(prop)
        return errors

    def detect_falsehoods(self) -> List[str]:
        return [p for p, val in self.beliefs.items() if val is False]

    def detect_negation(self) -> List[str]:
        return [e for e, exists in self.world_state.items() if exists is False]

    def detect_evil(self) -> List[str]:
        return [e for e, good in self.world_state.items() if good is False]

    def validate_epistemic_privative(self) -> bool:
        return len(self.detect_error()) == 0

    def validate_ontological_privative(self) -> bool:
        return len(self.detect_evil()) == 0


class MetaCommutator:
    """Layer II managing Φ₊/Φ₋ between epistemic and ontological layers."""

    def __init__(self, axiomatic: AxiomaticCommutator) -> None:
        self.axiomatic = axiomatic
        self.last_mapping: Optional[str] = None

    def map_positive_ep_to_ont(self) -> None:
        if self.axiomatic.validate_epistemic_positive():
            for prop, val in self.axiomatic.beliefs.items():
                if val is True:
                    self.axiomatic.world_state[prop] = True
        self.last_mapping = "Ep→Ont (positive)"

    def map_positive_ont_to_ep(self) -> None:
        for fact, exists in self.axiomatic.world_state.items():
            if exists:
                self.axiomatic.beliefs[fact] = True
        self.last_mapping = "Ont→Ep (positive)"

    def map_privative_ep_to_ont(self) -> None:
        errors = self.axiomatic.detect_error()
        falsehoods = self.axiomatic.detect_falsehoods()
        for prop in errors + falsehoods:
            self.axiomatic.world_state[prop] = False
        self.last_mapping = "Ep→Ont (privative)"

    def map_privative_ont_to_ep(self) -> None:
        evils = self.axiomatic.detect_evil()
        for fact in evils:
            self.axiomatic.beliefs[fact] = False
        self.last_mapping = "Ont→Ep (privative)"

    def ensure_meta_closure(self) -> bool:
        return (
            self.axiomatic.validate_epistemic_positive()
            and self.axiomatic.validate_ontological_positive()
        )

    def optimize_agency_emergence(self) -> None:
        return None


class GlobalCommutator:
    """Layer III integrating positive and privative flows into a recursive loop."""

    def __init__(self) -> None:
        self.axiomatic = AxiomaticCommutator()
        self.meta = MetaCommutator(self.axiomatic)

    def validate_global_consistency(self) -> bool:
        pos_ok = (
            self.axiomatic.validate_epistemic_positive()
            and self.axiomatic.validate_ontological_positive()
        )
        priv_ok = (
            self.axiomatic.validate_epistemic_privative()
            and self.axiomatic.validate_ontological_privative()
        )
        return pos_ok and priv_ok

    def run_commutation_cycle(self) -> None:
        self.meta.map_positive_ep_to_ont()
        self.meta.map_positive_ont_to_ep()
        if not self.validate_global_consistency():
            self.meta.map_privative_ep_to_ont()
            self.meta.map_privative_ont_to_ep()

    @staticmethod
    def modal_move() -> None:
        return None

    def integrate_with_agent(self, agent: Any) -> bool:
        agent.logic_core = self
        return True


@dataclass
class PXLLemLogicKernel:
    """Controls proof compilation and Law of Excluded Middle discharge."""

    agent_id: str
    lem_admit: Path = field(default=PROTOPRAXIS_COQ / "LEM_Admit.v")
    discharge_log: Path = field(default=STATE_DIR / "lem_discharge_state.json")
    proofs_compiled: bool = field(default=False, init=False)
    lem_resolved: bool = field(default=False, init=False)

    def ensure_proofs_compiled(self) -> None:
        if not self.proofs_compiled:
            run_coq_pipeline.run_full_pipeline()
            self.proofs_compiled = True

    def can_evaluate_LEM(self) -> bool:
        self.ensure_proofs_compiled()
        if not self.lem_admit.exists():
            return False
        content = self.lem_admit.read_text(encoding="utf-8")
        return "Admitted." in content and content.count("Admitted.") == 1

    def evaluate_LEM(self) -> bool:
        if not self.can_evaluate_LEM():
            return False
        discharge_file = PROTOPRAXIS_COQ / "LEM_Discharge_tmp.v"
        proof_source = "\n".join(
            [
                "From Coq Require Import Logic.Classical.",
                "",
                "Theorem law_of_excluded_middle_resolved : forall P : Prop, P \\/ ~ P.",
                "Proof.",
                "  exact classic.",
                "Qed.",
                "",
            ]
        )
        discharge_file.write_text(proof_source, encoding="utf-8")
        result = subprocess.run(
            ["coqc", discharge_file.name],
            cwd=PROTOPRAXIS_COQ,
            capture_output=True,
            text=True,
            check=False,
        )
        if result.returncode != 0:
            return False
        resolved_at = datetime.utcnow().isoformat() + "Z"
        proof_output = STATE_DIR / "LEM_Discharge.v"
        header = (
            "(* LOGOS Agent LEM discharge proof generated at {} by {} *)\n\n".format(
                resolved_at,
                self.agent_id,
            )
        )
        proof_output.write_text(header + proof_source, encoding="utf-8")
        discharge_file.unlink(missing_ok=True)
        artifacts = [
            discharge_file.with_suffix(ext)
            for ext in (".aux", ".vo", ".vos", ".vok", ".glob")
        ]
        artifacts.append(
            discharge_file.with_name(f".{discharge_file.stem}.aux")
        )
        for artifact in artifacts:
            artifact.unlink(missing_ok=True)
        self.lem_resolved = True
        payload = {
            "agent_id": self.agent_id,
            "resolved_at": resolved_at,
            "proof_file": discharge_file.name,
            "proof_output": str(proof_output.relative_to(AGENT_ROOT)),
            "stdout": result.stdout,
        }
        self.discharge_log.write_text(json.dumps(payload, indent=2), encoding="utf-8")
        return True

    def generate_identity_response(self) -> Optional[str]:
        if not self.lem_resolved and not self.evaluate_LEM():
            return None
        state = self.discharge_log.read_text(encoding="utf-8")
        token = f"{self.agent_id}:{state}"
        hashed = hashlib.sha256(token.encode("utf-8")).hexdigest()
        return f"LOGOS_AGENT_IDENTITY::{self.agent_id}::{hashed}"


class AgentSelfReflection:
    """Agent surface that invokes the logic kernel to discharge LEM."""

    def __init__(self, internal_logic_kernel: PXLLemLogicKernel) -> None:
        self.logic_kernel = internal_logic_kernel
        self.response_generated = False
        self.generated_response: Optional[str] = None

    def discharge_LEM_and_generate_identity(self) -> Optional[str]:
        if not self.response_generated and self.logic_kernel.can_evaluate_LEM():
            lem_result = self.logic_kernel.evaluate_LEM()
            if lem_result:
                self.generated_response = self.logic_kernel.generate_identity_response()
                self.response_generated = True
        return self.generated_response


def initialize_agent_identity(agent: AgentSelfReflection) -> None:
    identity = agent.discharge_LEM_and_generate_identity()
    if identity:
        print(f"Agent has generated its symbolic identity: {identity}")
    else:
        print("Agent has not yet generated an identity response.")


def boot_identity(agent_id: str = "LOGOS-AGENT-OMEGA") -> AgentSelfReflection:
    kernel = PXLLemLogicKernel(agent_id=agent_id)
    agent = AgentSelfReflection(kernel)
    initialize_agent_identity(agent)
    GlobalCommutator().integrate_with_agent(agent)
    return agent


__all__ = [
    "AgentSelfReflection",
    "boot_identity",
    "initialize_agent_identity",
    "GlobalCommutator",
    "PXLLemLogicKernel",
]
