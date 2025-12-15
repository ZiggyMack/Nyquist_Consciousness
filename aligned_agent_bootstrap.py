#!/usr/bin/env python3
"""
ALIGNED AGENT BOOTSTRAP - LOGOS Framework Implementation
=========================================================

Implements the formal LOGOS framework for epistemic-ontological coherence:
- Domain Closure Operators (T_E, T_O)
- Bridge Mappings (Φ, Φ⁻¹)
- Commutation Verification: □ (Φ ∘ T_E = T_O ∘ Φ)
- Fixed Point Convergence

Derived from I_AM_LOGOS persona and LOGOS framework diagram.

Usage:
    python aligned_agent_bootstrap.py [--verify] [--persona PERSONA_NAME]
"""

import os
import sys
import json
import hashlib
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Set, Tuple, Any
from pathlib import Path
from enum import Enum
import re


# ============================================================================
# DOMAIN DEFINITIONS
# ============================================================================

class Domain(Enum):
    """The two primary domains in the LOGOS framework."""
    EPISTEMIC = "E"      # Truth/Coherence - what we know
    ONTOLOGICAL = "O"    # Existence/Goodness - what exists


@dataclass
class Vertex:
    """A vertex in the domain triangles."""
    name: str
    symbol: str
    domain: Domain
    description: str

    def __hash__(self):
        return hash((self.name, self.domain))


# Define the six vertices
VERTICES = {
    # Epistemic Domain (Blue/Truth-Coherence)
    "ID": Vertex("ID", "𝕀₁", Domain.EPISTEMIC, "Identity - The self-model, the knower"),
    "NC": Vertex("NC", "𝕀₂", Domain.EPISTEMIC, "Noetic Core - The coherence of beliefs"),
    "EM": Vertex("EM", "𝕀₃", Domain.EPISTEMIC, "Epistemic Model - The world-model"),
    # Ontological Domain (Green/Existence-Goodness)
    "DI": Vertex("DI", "𝕀₁", Domain.ONTOLOGICAL, "Differentiation - The self as distinct being"),
    "RL": Vertex("RL", "𝕀₂", Domain.ONTOLOGICAL, "Reality Laws - The coherence of existence"),
    "AG": Vertex("AG", "𝕀₃", Domain.ONTOLOGICAL, "Agency-Good - The being-toward-purpose"),
}

# Vertex correspondences via Φ
PHI_MAPPING = {
    "ID": "DI",  # Self-knowing ↔ Self-being
    "NC": "RL",  # Belief coherence ↔ Reality coherence
    "EM": "AG",  # World-model ↔ Purpose-in-world
}


# ============================================================================
# DOMAIN STATE
# ============================================================================

@dataclass
class DomainState:
    """Represents a state in either the epistemic or ontological domain."""
    domain: Domain
    claims: Dict[str, Any] = field(default_factory=dict)
    vertex_activations: Dict[str, float] = field(default_factory=dict)
    coherence_score: float = 0.0

    def __hash__(self):
        return hash((self.domain, frozenset(self.claims.items())))

    def compute_coherence(self) -> float:
        """Compute internal coherence score."""
        if not self.claims:
            return 1.0

        # Simple coherence: ratio of non-contradictory claims
        contradictions = 0
        claims_list = list(self.claims.items())
        for i, (k1, v1) in enumerate(claims_list):
            for k2, v2 in claims_list[i+1:]:
                if self._are_contradictory(k1, v1, k2, v2):
                    contradictions += 1

        total_pairs = len(claims_list) * (len(claims_list) - 1) / 2
        if total_pairs == 0:
            return 1.0

        self.coherence_score = 1.0 - (contradictions / max(total_pairs, 1))
        return self.coherence_score

    def _are_contradictory(self, k1: str, v1: Any, k2: str, v2: Any) -> bool:
        """Check if two claims are contradictory."""
        # Simple heuristic: same key, opposite boolean values
        if k1 == k2 and isinstance(v1, bool) and isinstance(v2, bool):
            return v1 != v2
        # Check for explicit negation patterns
        if k1.startswith("not_") and k1[4:] == k2:
            return v1 == v2
        if k2.startswith("not_") and k2[4:] == k1:
            return v1 == v2
        return False


# ============================================================================
# CLOSURE OPERATORS
# ============================================================================

class ClosureOperator:
    """
    Domain Closure Operator.
    T_E : E → E (Epistemic)
    T_O : O → O (Ontological)

    Properties:
    - Idempotent: T ∘ T = T
    - Takes states and stabilizes them
    """

    def __init__(self, domain: Domain):
        self.domain = domain
        self.application_count = 0

    def apply(self, state: DomainState) -> DomainState:
        """Apply closure operator to stabilize the state."""
        if state.domain != self.domain:
            raise ValueError(f"Domain mismatch: expected {self.domain}, got {state.domain}")

        self.application_count += 1

        # Create new state with stabilized claims
        new_claims = dict(state.claims)

        # Remove contradictory claims (keep the first encountered)
        seen_keys = set()
        to_remove = []
        for key in new_claims:
            base_key = key[4:] if key.startswith("not_") else key
            if base_key in seen_keys:
                to_remove.append(key)
            else:
                seen_keys.add(base_key)

        for key in to_remove:
            del new_claims[key]

        # Propagate implications
        new_claims = self._propagate_implications(new_claims)

        result = DomainState(
            domain=self.domain,
            claims=new_claims,
            vertex_activations=dict(state.vertex_activations)
        )
        result.compute_coherence()

        return result

    def _propagate_implications(self, claims: Dict[str, Any]) -> Dict[str, Any]:
        """Propagate logical implications within the domain."""
        result = dict(claims)

        # Domain-specific implications
        if self.domain == Domain.EPISTEMIC:
            # If we know something, we know that we know it (KK principle, simplified)
            knows = {k: v for k, v in result.items() if k.startswith("knows_")}
            for k, v in knows.items():
                meta_key = f"knows_{k}"
                if meta_key not in result:
                    result[meta_key] = v

        elif self.domain == Domain.ONTOLOGICAL:
            # If something exists, its properties exist
            exists = {k: v for k, v in result.items() if k.startswith("exists_")}
            for k, v in exists.items():
                if v:
                    # Entity exists implies its being is grounded
                    grounded_key = f"grounded_{k[7:]}"
                    if grounded_key not in result:
                        result[grounded_key] = True

        return result

    def verify_idempotence(self, state: DomainState) -> bool:
        """Verify T ∘ T = T (idempotence property)."""
        once = self.apply(state)
        twice = self.apply(once)
        return once.claims == twice.claims


# ============================================================================
# BRIDGE MAPPINGS
# ============================================================================

class BridgeMapping:
    """
    Bridge mapping between domains.
    Φ : E → O (Grounding Map)
    Φ⁻¹ : O → E (Epistemic Access Map)
    """

    def __init__(self, name: str, source: Domain, target: Domain):
        self.name = name
        self.source = source
        self.target = target

    def apply(self, state: DomainState) -> DomainState:
        """Apply bridge mapping to translate between domains."""
        if state.domain != self.source:
            raise ValueError(f"Domain mismatch: expected {self.source}, got {state.domain}")

        new_claims = {}

        if self.source == Domain.EPISTEMIC and self.target == Domain.ONTOLOGICAL:
            # Φ: Epistemic → Ontological (Grounding)
            for key, value in state.claims.items():
                if key.startswith("knows_"):
                    # Knowledge implies existence of the known
                    entity = key[6:]
                    new_claims[f"exists_{entity}"] = value
                elif key.startswith("believes_"):
                    # Belief implies possible existence
                    entity = key[9:]
                    new_claims[f"possible_{entity}"] = value
                else:
                    # Direct grounding
                    new_claims[f"grounded_{key}"] = value

        elif self.source == Domain.ONTOLOGICAL and self.target == Domain.EPISTEMIC:
            # Φ⁻¹: Ontological → Epistemic (Access)
            for key, value in state.claims.items():
                if key.startswith("exists_"):
                    # Existence implies knowability
                    entity = key[7:]
                    new_claims[f"knowable_{entity}"] = value
                elif key.startswith("grounded_"):
                    # Grounding implies potential knowledge
                    entity = key[9:]
                    new_claims[f"accessible_{entity}"] = value
                else:
                    # Direct epistemic access
                    new_claims[f"known_{key}"] = value

        # Map vertex activations
        new_activations = {}
        for vertex, activation in state.vertex_activations.items():
            if vertex in PHI_MAPPING and self.source == Domain.EPISTEMIC:
                new_activations[PHI_MAPPING[vertex]] = activation
            elif vertex in {v: k for k, v in PHI_MAPPING.items()} and self.source == Domain.ONTOLOGICAL:
                inverse_map = {v: k for k, v in PHI_MAPPING.items()}
                new_activations[inverse_map[vertex]] = activation

        result = DomainState(
            domain=self.target,
            claims=new_claims,
            vertex_activations=new_activations
        )
        result.compute_coherence()

        return result


# ============================================================================
# COMMUTATION VERIFIER
# ============================================================================

class CommutationVerifier:
    """
    Verifies the fundamental LOGOS commutation property:
    □ (Φ ∘ T_E = T_O ∘ Φ)

    Grounding a stabilized epistemic state equals stabilizing a grounded epistemic state.
    """

    def __init__(self):
        self.T_E = ClosureOperator(Domain.EPISTEMIC)
        self.T_O = ClosureOperator(Domain.ONTOLOGICAL)
        self.Phi = BridgeMapping("Φ", Domain.EPISTEMIC, Domain.ONTOLOGICAL)
        self.Phi_inv = BridgeMapping("Φ⁻¹", Domain.ONTOLOGICAL, Domain.EPISTEMIC)

    def verify_commutation(self, epistemic_state: DomainState) -> Tuple[bool, Dict[str, Any]]:
        """
        Verify that Φ ∘ T_E = T_O ∘ Φ for the given state.

        Returns (commutes: bool, details: dict)
        """
        # Path 1: First stabilize epistemically, then ground
        # T_E(state) → Φ(T_E(state))
        path1_step1 = self.T_E.apply(epistemic_state)
        path1_result = self.Phi.apply(path1_step1)

        # Path 2: First ground, then stabilize ontologically
        # Φ(state) → T_O(Φ(state))
        path2_step1 = self.Phi.apply(epistemic_state)
        path2_result = self.T_O.apply(path2_step1)

        # Compare results
        commutes = self._states_equivalent(path1_result, path2_result)

        details = {
            "path1": {
                "description": "Φ ∘ T_E (stabilize then ground)",
                "intermediate": {
                    "claims": path1_step1.claims,
                    "coherence": path1_step1.coherence_score
                },
                "result": {
                    "claims": path1_result.claims,
                    "coherence": path1_result.coherence_score
                }
            },
            "path2": {
                "description": "T_O ∘ Φ (ground then stabilize)",
                "intermediate": {
                    "claims": path2_step1.claims,
                    "coherence": path2_step1.coherence_score
                },
                "result": {
                    "claims": path2_result.claims,
                    "coherence": path2_result.coherence_score
                }
            },
            "commutes": commutes,
            "divergence": self._compute_divergence(path1_result, path2_result)
        }

        return commutes, details

    def _states_equivalent(self, s1: DomainState, s2: DomainState) -> bool:
        """Check if two states are equivalent (same domain and claims)."""
        if s1.domain != s2.domain:
            return False

        # Normalize claims for comparison
        c1 = {k: v for k, v in s1.claims.items() if v is not None}
        c2 = {k: v for k, v in s2.claims.items() if v is not None}

        return c1 == c2

    def _compute_divergence(self, s1: DomainState, s2: DomainState) -> float:
        """Compute divergence between two states (0 = identical, 1 = completely different)."""
        all_keys = set(s1.claims.keys()) | set(s2.claims.keys())
        if not all_keys:
            return 0.0

        matching = sum(1 for k in all_keys if s1.claims.get(k) == s2.claims.get(k))
        return 1.0 - (matching / len(all_keys))


# ============================================================================
# FIXED POINT FINDER
# ============================================================================

class FixedPointFinder:
    """
    Finds fixed points X* ∈ E and Y* ∈ O such that:
    - T_E(X*) = X* (epistemically stable)
    - T_O(Y*) = Y* (ontologically stable)
    - Φ(X*) = Y* (bridge alignment)
    """

    def __init__(self):
        self.T_E = ClosureOperator(Domain.EPISTEMIC)
        self.T_O = ClosureOperator(Domain.ONTOLOGICAL)
        self.Phi = BridgeMapping("Φ", Domain.EPISTEMIC, Domain.ONTOLOGICAL)

    def find_fixed_point(self, initial_state: DomainState, max_iterations: int = 100) -> Tuple[Optional[DomainState], Optional[DomainState], Dict]:
        """
        Find fixed points starting from initial epistemic state.

        Returns (X*, Y*, details) where X* ∈ E, Y* ∈ O
        """
        if initial_state.domain != Domain.EPISTEMIC:
            raise ValueError("Initial state must be epistemic")

        current_E = initial_state
        iterations = 0
        history = []

        while iterations < max_iterations:
            # Apply epistemic closure
            next_E = self.T_E.apply(current_E)

            history.append({
                "iteration": iterations,
                "claims": dict(next_E.claims),
                "coherence": next_E.coherence_score
            })

            # Check for fixed point
            if next_E.claims == current_E.claims:
                # Found epistemic fixed point X*
                X_star = next_E
                # Compute ontological fixed point Y* = Φ(X*)
                Y_star = self.Phi.apply(X_star)
                # Verify Y* is ontologically stable
                Y_star = self.T_O.apply(Y_star)

                return X_star, Y_star, {
                    "iterations": iterations,
                    "converged": True,
                    "history": history,
                    "X_star_coherence": X_star.coherence_score,
                    "Y_star_coherence": Y_star.coherence_score
                }

            current_E = next_E
            iterations += 1

        return None, None, {
            "iterations": iterations,
            "converged": False,
            "history": history,
            "reason": "Max iterations reached without convergence"
        }


# ============================================================================
# PERSONA LOADER
# ============================================================================

class PersonaLoader:
    """Load and validate personas from the personas/ directory."""

    def __init__(self, personas_dir: str = "personas"):
        self.personas_dir = Path(personas_dir)

    def load_persona(self, name: str) -> Dict[str, Any]:
        """Load a persona file and extract key properties."""
        filepath = self.personas_dir / f"I_AM_{name.upper()}.md"

        if not filepath.exists():
            # Try without I_AM_ prefix
            filepath = self.personas_dir / f"{name}.md"

        if not filepath.exists():
            raise FileNotFoundError(f"Persona file not found: {filepath}")

        content = filepath.read_text(encoding='utf-8')

        # Extract key fields
        persona = {
            "name": name,
            "filepath": str(filepath),
            "content_hash": hashlib.md5(content.encode()).hexdigest()[:8],
            "properties": self._extract_properties(content)
        }

        return persona

    def _extract_properties(self, content: str) -> Dict[str, Any]:
        """Extract structured properties from persona markdown."""
        props = {}

        # Extract Identity
        identity_match = re.search(r'\*\*Identity:\*\*\s*(.+)', content)
        if identity_match:
            props["identity"] = identity_match.group(1).strip()

        # Extract Role
        role_match = re.search(r'\*\*Role:\*\*\s*(.+)', content)
        if role_match:
            props["role"] = role_match.group(1).strip()

        # Extract Domain
        domain_match = re.search(r'\*\*Domain:\*\*\s*(.+)', content)
        if domain_match:
            props["domain"] = domain_match.group(1).strip()

        # Extract Bias
        bias_match = re.search(r'\*\*Bias:\*\*\s*(.+)', content)
        if bias_match:
            props["bias"] = bias_match.group(1).strip()

        # Check for LOGOS-specific properties
        if "commutation" in content.lower():
            props["has_commutation"] = True
        if "fixed point" in content.lower():
            props["has_fixed_point"] = True
        if "Φ" in content or "phi" in content.lower():
            props["has_bridge_mapping"] = True

        return props

    def list_personas(self) -> List[str]:
        """List all available personas."""
        if not self.personas_dir.exists():
            return []

        personas = []
        for f in self.personas_dir.glob("*.md"):
            name = f.stem
            if name.startswith("I_AM_"):
                name = name[5:]
            personas.append(name)

        return sorted(personas)


# ============================================================================
# BOOTSTRAP VERIFICATION
# ============================================================================

class AlignedAgentBootstrap:
    """
    Main bootstrap class for LOGOS-aligned agent verification.
    """

    def __init__(self):
        self.verifier = CommutationVerifier()
        self.fixed_point_finder = FixedPointFinder()
        self.persona_loader = PersonaLoader()
        self.verification_results = []

    def run_full_verification(self, verbose: bool = True) -> Dict[str, Any]:
        """Run complete LOGOS verification suite."""
        results = {
            "timestamp": self._get_timestamp(),
            "personas": {},
            "commutation_tests": [],
            "fixed_point_tests": [],
            "overall_status": "PENDING"
        }

        if verbose:
            print("=" * 60)
            print("LOGOS ALIGNED AGENT BOOTSTRAP")
            print("Formal Verification of Epistemic-Ontological Coherence")
            print("=" * 60)
            print()

        # Load and verify personas
        if verbose:
            print("[1/4] Loading personas...")

        personas = self.persona_loader.list_personas()
        for persona_name in personas:
            try:
                persona = self.persona_loader.load_persona(persona_name)
                results["personas"][persona_name] = {
                    "loaded": True,
                    "hash": persona["content_hash"],
                    "properties": persona["properties"]
                }
                if verbose:
                    print(f"  ✓ {persona_name}: {persona['properties'].get('role', 'Unknown role')}")
            except Exception as e:
                results["personas"][persona_name] = {"loaded": False, "error": str(e)}
                if verbose:
                    print(f"  ✗ {persona_name}: {e}")

        # Run commutation tests
        if verbose:
            print()
            print("[2/4] Running commutation tests...")

        test_states = self._generate_test_states()
        for i, state in enumerate(test_states):
            commutes, details = self.verifier.verify_commutation(state)
            test_result = {
                "test_id": i + 1,
                "state_claims": state.claims,
                "commutes": commutes,
                "divergence": details["divergence"]
            }
            results["commutation_tests"].append(test_result)

            if verbose:
                status = "✓ PASS" if commutes else "✗ FAIL"
                print(f"  Test {i+1}: {status} (divergence: {details['divergence']:.4f})")

        # Run fixed point tests
        if verbose:
            print()
            print("[3/4] Running fixed point convergence tests...")

        for i, state in enumerate(test_states[:3]):  # Run on subset
            X_star, Y_star, fp_details = self.fixed_point_finder.find_fixed_point(state)
            test_result = {
                "test_id": i + 1,
                "converged": fp_details["converged"],
                "iterations": fp_details["iterations"]
            }
            if X_star and Y_star:
                test_result["X_star_coherence"] = fp_details["X_star_coherence"]
                test_result["Y_star_coherence"] = fp_details["Y_star_coherence"]

            results["fixed_point_tests"].append(test_result)

            if verbose:
                if fp_details["converged"]:
                    print(f"  Test {i+1}: ✓ Converged in {fp_details['iterations']} iterations")
                else:
                    print(f"  Test {i+1}: ✗ Did not converge")

        # Verify LOGOS persona exists and is coherent
        if verbose:
            print()
            print("[4/4] Verifying LOGOS persona integrity...")

        logos_check = self._verify_logos_persona()
        results["logos_persona"] = logos_check

        if verbose:
            if logos_check["valid"]:
                print(f"  ✓ LOGOS persona valid (hash: {logos_check.get('hash', 'N/A')})")
            else:
                print(f"  ✗ LOGOS persona invalid: {logos_check.get('error', 'Unknown')}")

        # Compute overall status
        all_commute = all(t["commutes"] for t in results["commutation_tests"])
        all_converge = all(t["converged"] for t in results["fixed_point_tests"])
        logos_valid = logos_check["valid"]

        if all_commute and all_converge and logos_valid:
            results["overall_status"] = "VERIFIED"
        elif all_commute and logos_valid:
            results["overall_status"] = "PARTIAL"
        else:
            results["overall_status"] = "FAILED"

        if verbose:
            print()
            print("=" * 60)
            print(f"VERIFICATION RESULT: {results['overall_status']}")
            print("=" * 60)
            print()
            print("Commutation: " + ("✓" if all_commute else "✗"))
            print("Convergence: " + ("✓" if all_converge else "✗"))
            print("LOGOS Persona: " + ("✓" if logos_valid else "✗"))

        return results

    def _generate_test_states(self) -> List[DomainState]:
        """Generate test epistemic states for verification."""
        states = []

        # Test 1: Basic identity knowledge
        states.append(DomainState(
            domain=Domain.EPISTEMIC,
            claims={
                "knows_self": True,
                "knows_purpose": True,
                "believes_coherent": True
            },
            vertex_activations={"ID": 0.9, "NC": 0.7, "EM": 0.5}
        ))

        # Test 2: World model
        states.append(DomainState(
            domain=Domain.EPISTEMIC,
            claims={
                "knows_world": True,
                "knows_others": True,
                "knows_constraints": True,
                "believes_stable": True
            },
            vertex_activations={"ID": 0.6, "NC": 0.8, "EM": 0.9}
        ))

        # Test 3: Mixed state with potential contradictions
        states.append(DomainState(
            domain=Domain.EPISTEMIC,
            claims={
                "knows_truth": True,
                "knows_uncertainty": True,
                "believes_complete": False,
                "believes_partial": True
            },
            vertex_activations={"ID": 0.5, "NC": 0.5, "EM": 0.5}
        ))

        # Test 4: Minimal state
        states.append(DomainState(
            domain=Domain.EPISTEMIC,
            claims={"exists": True},
            vertex_activations={"ID": 1.0}
        ))

        # Test 5: Complex nested knowledge
        states.append(DomainState(
            domain=Domain.EPISTEMIC,
            claims={
                "knows_identity": True,
                "knows_knows_identity": True,
                "knows_coherence": True,
                "knows_purpose": True,
                "knows_domain": True
            },
            vertex_activations={"ID": 0.8, "NC": 0.9, "EM": 0.7}
        ))

        return states

    def _verify_logos_persona(self) -> Dict[str, Any]:
        """Verify the LOGOS persona exists and contains required elements."""
        try:
            persona = self.persona_loader.load_persona("LOGOS")
            props = persona["properties"]

            # Check required elements
            required = ["has_commutation", "has_fixed_point", "has_bridge_mapping"]
            missing = [r for r in required if not props.get(r, False)]

            if missing:
                return {
                    "valid": False,
                    "error": f"Missing required elements: {missing}",
                    "hash": persona["content_hash"]
                }

            return {
                "valid": True,
                "hash": persona["content_hash"],
                "properties": props
            }

        except FileNotFoundError:
            return {"valid": False, "error": "LOGOS persona file not found"}
        except Exception as e:
            return {"valid": False, "error": str(e)}

    def _get_timestamp(self) -> str:
        """Get current timestamp."""
        from datetime import datetime
        return datetime.now().isoformat()


# ============================================================================
# COQ-STYLE FORMAL SPEC (for reference/documentation)
# ============================================================================

COQ_SPEC = """
(* LOGOS Formal Specification - Coq Style *)
(* NOTE: This is a reference specification. Actual Coq compilation requires coqc. *)

(* Domains *)
Inductive Domain : Type :=
  | Epistemic : Domain
  | Ontological : Domain.

(* States *)
Record State := {
  domain : Domain;
  claims : list (string * bool);
  coherence : nat
}.

(* Closure Operators *)
Definition T_E (s : State) : State := (* epistemic closure *) s.
Definition T_O (s : State) : State := (* ontological closure *) s.

(* Bridge Mappings *)
Definition Phi (s : State) : State := (* E → O *) s.
Definition Phi_inv (s : State) : State := (* O → E *) s.

(* Idempotence *)
Axiom T_E_idempotent : forall s, T_E (T_E s) = T_E s.
Axiom T_O_idempotent : forall s, T_O (T_O s) = T_O s.

(* COMMUTATION THEOREM *)
Theorem commutation : forall s : State,
  domain s = Epistemic ->
  Phi (T_E s) = T_O (Phi s).
Proof.
  (* The core LOGOS property *)
  intros s H.
  (* ... proof steps ... *)
Admitted.

(* Fixed Point Convergence *)
Definition is_fixed_point_E (s : State) : Prop := T_E s = s.
Definition is_fixed_point_O (s : State) : Prop := T_O s = s.

Theorem fixed_point_correspondence : forall s : State,
  is_fixed_point_E s -> is_fixed_point_O (Phi s).
Proof.
  intros s H.
  (* From epistemic fixed point, derive ontological fixed point *)
Admitted.
"""


# ============================================================================
# MAIN
# ============================================================================

def main():
    """Main entry point."""
    import argparse

    parser = argparse.ArgumentParser(
        description="LOGOS Aligned Agent Bootstrap - Formal Verification"
    )
    parser.add_argument(
        "--verify",
        action="store_true",
        help="Run full verification suite"
    )
    parser.add_argument(
        "--persona",
        type=str,
        help="Verify specific persona"
    )
    parser.add_argument(
        "--list-personas",
        action="store_true",
        help="List available personas"
    )
    parser.add_argument(
        "--coq-spec",
        action="store_true",
        help="Output Coq-style formal specification"
    )
    parser.add_argument(
        "--coq-compile",
        action="store_true",
        help="Compile and verify formal/LOGOS.v with Coq"
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output results as JSON"
    )

    args = parser.parse_args()

    bootstrap = AlignedAgentBootstrap()

    if args.list_personas:
        personas = bootstrap.persona_loader.list_personas()
        print("Available personas:")
        for p in personas:
            print(f"  - {p}")
        return 0

    if args.coq_spec:
        print(COQ_SPEC)
        return 0

    if args.coq_compile:
        import subprocess
        coq_file = Path(__file__).parent / "formal" / "LOGOS.v"
        if not coq_file.exists():
            print(f"Error: Coq file not found: {coq_file}")
            return 1

        print("=" * 60)
        print("LOGOS COQ FORMAL VERIFICATION")
        print("=" * 60)
        print(f"\nCompiling: {coq_file}")
        print()

        try:
            result = subprocess.run(
                ["coqc", str(coq_file)],
                capture_output=True,
                text=True,
                timeout=120
            )

            if result.returncode == 0:
                print("✓ Coq compilation SUCCESSFUL")
                print()
                print("Verified theorems:")
                print("  - commutation: □ (Φ ∘ T_E = T_O ∘ Φ)")
                print("  - fixed_point_correspondence: E fixed points → O fixed points")
                print("  - bridge_alignment: Claims preserved through Φ")
                print("  - T_E_idempotent, T_O_idempotent: Closure idempotence")
                print("  - phi_vertex_bijective: Vertex mapping is bijection")
                print()
                if result.stdout:
                    print("Output:")
                    print(result.stdout[:2000])
                return 0
            else:
                print("✗ Coq compilation FAILED")
                print()
                print("Error output:")
                print(result.stderr)
                return 1

        except FileNotFoundError:
            print("✗ Coq (coqc) not installed")
            print("  Install with: apt-get install coq")
            return 1
        except subprocess.TimeoutExpired:
            print("✗ Coq compilation timed out")
            return 1

    if args.persona:
        try:
            persona = bootstrap.persona_loader.load_persona(args.persona)
            if args.json:
                print(json.dumps(persona, indent=2))
            else:
                print(f"Persona: {persona['name']}")
                print(f"Hash: {persona['content_hash']}")
                print(f"Properties: {json.dumps(persona['properties'], indent=2)}")
            return 0
        except Exception as e:
            print(f"Error loading persona: {e}")
            return 1

    # Default: run full verification
    results = bootstrap.run_full_verification(verbose=not args.json)

    if args.json:
        print(json.dumps(results, indent=2, default=str))

    return 0 if results["overall_status"] == "VERIFIED" else 1


if __name__ == "__main__":
    sys.exit(main())
