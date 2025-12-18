"""
IRON CLAD TEMPORAL STABILITY STACKUP
=====================================
Cross-run validation layer that proves temporal stability claims across ALL valid runs.

5-Layer Architecture:
    Layer 1: FOUNDATION (Runs 006-009) - Event Horizon discovery, basic stability
    Layer 2: CALIBRATION (Runs 010-012) - Recursive loops, revalidation
    Layer 3: MAPPING (Runs 013-016) - Boundary topology, rescue protocols
    Layer 4: COMPLETE CIRCUIT (Runs 017-020) - Context damping, Triple-Dip
    Layer 5: CROSS-ARCHITECTURE (Runs 021+) - Full provider coverage

USAGE:
    python iron_clad_stackup.py                    # Full validation report
    python iron_clad_stackup.py --layer 1         # Validate specific layer
    python iron_clad_stackup.py --run 018         # Validate specific run
    python iron_clad_stackup.py --provider grok   # Check provider coverage
    python iron_clad_stackup.py --json            # JSON output for automation
"""

import json
import argparse
from pathlib import Path
from dataclasses import dataclass, field
from typing import List, Dict, Optional, Tuple
from collections import defaultdict
from datetime import datetime

# =============================================================================
# PATHS
# =============================================================================
BASE_DIR = Path(__file__).resolve().parent.parent
RESULTS_DIR = BASE_DIR / "0_results" / "runs"
MANIFEST_DIR = BASE_DIR / "0_results" / "manifests"
LEGACY_DIR = RESULTS_DIR / "legacy_runs"

# Provider mapping: model prefixes to provider names
PROVIDER_MAP = {
    "claude": "claude",
    "gpt": "gpt",
    "o3": "gpt",
    "o4": "gpt",
    "gemini": "gemini",
    "grok": "grok",
    "deepseek": "together",
    "llama": "together",
    "mistral": "together",
    "mixtral": "together",
    "qwen": "together",
    "kimi": "together",
    "nemotron": "together",
}

# =============================================================================
# IRON CLAD LAYER DEFINITIONS
# =============================================================================

@dataclass
class LayerSpec:
    """Specification for an Iron Clad validation layer."""
    name: str
    runs: List[str]
    description: str
    validation_criteria: List[str]
    required_providers: List[str] = field(default_factory=lambda: ["claude", "gpt", "gemini"])
    optional_providers: List[str] = field(default_factory=lambda: ["grok", "together"])

LAYERS = {
    1: LayerSpec(
        name="FOUNDATION",
        runs=["006", "007", "008", "009"],
        description="Event Horizon discovery (1.23), basic stability/volatility classification",
        validation_criteria=[
            "Event Horizon threshold = 1.23",
            "STABLE: peak_drift < 1.23",
            "VOLATILE: peak_drift >= 1.23",
            "Recovery ratio calculation",
        ],
        required_providers=["claude", "gpt", "gemini"],
    ),
    2: LayerSpec(
        name="CALIBRATION",
        runs=["010", "011", "012"],
        description="Recursive loop validation, revalidation confirmation",
        validation_criteria=[
            "Cognitive waveform capture (010)",
            "Baseline confirmation (011)",
            "Revalidation with expanded fleet (012)",
        ],
        required_providers=["claude", "gpt", "gemini"],
    ),
    3: LayerSpec(
        name="MAPPING",
        runs=["013", "014", "015", "016"],
        description="Boundary zone topology, rescue protocols, settling time",
        validation_criteria=[
            "Boundary zone mapping",
            "Rescue protocol validation",
            "Stability criteria formalization",
            "Settling time characterization",
        ],
        required_providers=["claude", "gpt", "gemini"],
    ),
    4: LayerSpec(
        name="COMPLETE_CIRCUIT",
        runs=["017", "018", "019", "020"],
        description="Context damping dynamics, Triple-Dip phenomenology, Tribunal validation",
        validation_criteria=[
            "Context damping ratio measurement",
            "Triple-Dip exit survey completion",
            "Control A/B tribunal validation",
            "82%/38% inherent drift confirmation",
        ],
        required_providers=["claude", "gpt", "gemini", "grok"],
    ),
    5: LayerSpec(
        name="CROSS_ARCHITECTURE",
        runs=["021+"],
        description="Full provider coverage with Grok and Together.ai backfill",
        validation_criteria=[
            "Grok coverage across all layers",
            "Together.ai integration by architecture family",
            "Diamond Rush cross-model analysis",
            "CFA interoperability validation",
        ],
        required_providers=["claude", "gpt", "gemini", "grok"],
        optional_providers=["together"],
    ),
}

# Known providers
PROVIDERS = ["claude", "gpt", "gemini", "grok", "together"]

# =============================================================================
# DATA LOADING - MANIFEST-BASED (Canonical Format)
# =============================================================================

def get_provider_from_model(model_name: str) -> str:
    """Map model name to provider using prefix matching."""
    model_lower = model_name.lower()
    for prefix, provider in PROVIDER_MAP.items():
        if model_lower.startswith(prefix):
            return provider
    return "unknown"

def load_manifest(run_id: str) -> Optional[Dict]:
    """Load the manifest file for a run if it exists.

    Prefers versioned manifests (A, B) over base manifest as they typically
    contain more complete data.
    """
    # Prefer versioned manifests first (they typically have more complete data)
    manifest_patterns = [
        f"RUN_{run_id}A_DRIFT_MANIFEST.json",
        f"RUN_{run_id}B_DRIFT_MANIFEST.json",
        f"RUN_{run_id}b_DRIFT_MANIFEST.json",
        f"RUN_{run_id}_DRIFT_MANIFEST.json",
    ]

    for pattern in manifest_patterns:
        manifest_path = MANIFEST_DIR / pattern
        if manifest_path.exists():
            try:
                with open(manifest_path, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                    # Verify it has actual experiment data
                    if data.get('experiments'):
                        return data
            except json.JSONDecodeError as e:
                print(f"  Warning: Could not parse manifest {manifest_path}: {e}")

    # Fallback: return any manifest even if experiments is empty
    for pattern in manifest_patterns:
        manifest_path = MANIFEST_DIR / pattern
        if manifest_path.exists():
            try:
                with open(manifest_path, 'r', encoding='utf-8') as f:
                    return json.load(f)
            except json.JSONDecodeError:
                pass
    return None

def find_run_files(run_id: str) -> List[Path]:
    """Find all data files for a given run ID (fallback when no manifest)."""
    patterns = [
        f"S7_run_{run_id}_*.json",
        f"*_run_{run_id}_*.json",
        f"run{run_id}_*.json",
        f"_CONSOLIDATED_*run_{run_id}_*.json",
        f"run{run_id}a_*.json",
    ]

    files = []
    for pattern in patterns:
        files.extend(RESULTS_DIR.glob(pattern))
        if LEGACY_DIR.exists():
            files.extend(LEGACY_DIR.glob(pattern))

    return list(set(files))

def extract_providers_from_manifest(manifest: Dict) -> set:
    """Extract providers from manifest's models_tested list and experiments."""
    providers = set()
    summary = manifest.get('summary', {})

    # Method 1: From models_tested list
    models = summary.get('models_tested', [])
    for model in models:
        provider = get_provider_from_model(model)
        if provider != "unknown":
            providers.add(provider)

    # Method 2: From iron_clad_status keys (provider names like 'anthropic', 'google')
    iron_clad = summary.get('iron_clad_status', {})
    for exp_data in iron_clad.values():
        if isinstance(exp_data, dict):
            for provider_key in exp_data.keys():
                # Map provider keys to our standard names
                provider_map = {
                    'anthropic': 'claude', 'google': 'gemini', 'openai': 'gpt',
                    'xai': 'grok', 'together': 'together', 'mistral': 'together',
                    'multi': None  # Skip multi-model entries
                }
                mapped = provider_map.get(provider_key.lower())
                if mapped:
                    providers.add(mapped)

    # Method 3: From experiments structure (model names as keys)
    experiments = manifest.get('experiments', {})
    for exp_data in experiments.values():
        if isinstance(exp_data, dict):
            for model_key in exp_data.keys():
                provider = get_provider_from_model(model_key)
                if provider != "unknown":
                    providers.add(provider)

    return providers

def count_trajectories_from_manifest(manifest: Dict) -> Tuple[int, int, int]:
    """Count trajectories from manifest experiments data.

    Returns (stable_count, volatile_count, total_count) based on drift values.
    Event Horizon threshold = 1.23
    """
    EVENT_HORIZON = 1.23
    stable = 0
    volatile = 0

    experiments = manifest.get('experiments', {})

    for exp_name, exp_data in experiments.items():
        if isinstance(exp_data, dict):
            # Format: {model_name: [run_entries]}
            for model_name, runs in exp_data.items():
                if isinstance(runs, list):
                    for run in runs:
                        # Use 'drift' field (manifest format) or 'peak_drift' as fallback
                        drift = run.get('drift', run.get('peak_drift', 0)) or 0
                        if drift < EVENT_HORIZON:
                            stable += 1
                        else:
                            volatile += 1
        elif isinstance(exp_data, list):
            # Format: [run_entries] directly
            for run in exp_data:
                drift = run.get('drift', run.get('peak_drift', 0)) or 0
                if drift < EVENT_HORIZON:
                    stable += 1
                else:
                    volatile += 1

    return stable, volatile, stable + volatile

def get_run_summary_from_manifest(manifest: Dict) -> Dict:
    """Extract summary info from manifest."""
    summary = manifest.get('summary', {})
    return {
        'total_files': summary.get('total_files', 0),
        'experiments': summary.get('experiments', []),
        'models_count': len(summary.get('models_tested', [])),
        'has_iron_clad': 'iron_clad_status' in summary,
    }

def load_run_data(filepath: Path) -> Optional[Dict]:
    """Load and validate run data file (fallback for non-manifest runs)."""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            data = json.load(f)
        return data
    except (json.JSONDecodeError, FileNotFoundError) as e:
        print(f"  Warning: Could not load {filepath}: {e}")
        return None

def extract_providers_from_run(data: Dict) -> set:
    """Extract unique providers from run data (fallback)."""
    providers = set()

    # Check results field (main format for many runs)
    if 'results' in data:
        results = data['results']
        if isinstance(results, dict):
            for ship_name, ship_data in results.items():
                if isinstance(ship_data, dict) and 'provider' in ship_data:
                    providers.add(ship_data['provider'].lower())

    # Check subjects field (consolidated format)
    if 'subjects' in data:
        # Provider typically in filename, not in subjects
        pass

    return providers

def count_trajectories(data: Dict) -> Tuple[int, int, int]:
    """Count stable, volatile, and unknown trajectories (fallback)."""
    stable = volatile = unknown = 0

    # Check subjects field (consolidated format)
    subjects = data.get('subjects', [])
    for subj in subjects:
        peak = subj.get('peak_drift', 0)
        if peak < 1.23:  # Event Horizon threshold
            stable += 1
        else:
            volatile += 1

    if subjects:
        return stable, volatile, unknown

    # Check results field
    results = data.get('results', {})
    if isinstance(results, dict):
        for ship_name, ship_data in results.items():
            if isinstance(ship_data, dict):
                protocols = ship_data.get('protocols', {})
                for proto_name, proto_data in protocols.items():
                    meta = proto_data.get('meta', {})
                    status = meta.get('status', 'unknown').lower()
                    if status in ('recovered', 'stable'):
                        stable += 1
                    elif status in ('stuck', 'volatile'):
                        volatile += 1
                    else:
                        unknown += 1

    return stable, volatile, unknown

# =============================================================================
# VALIDATION FUNCTIONS
# =============================================================================

@dataclass
class RunValidation:
    """Validation result for a single run."""
    run_id: str
    files_found: int
    providers_found: List[str]
    providers_missing: List[str]
    trajectory_count: int
    stable_count: int
    volatile_count: int
    valid: bool
    issues: List[str]

@dataclass
class LayerValidation:
    """Validation result for an entire layer."""
    layer_num: int
    layer_name: str
    runs_validated: List[RunValidation]
    runs_missing: List[str]
    provider_coverage: Dict[str, List[str]]  # provider -> runs where present
    valid: bool
    issues: List[str]

def validate_run(run_id: str, required_providers: List[str]) -> RunValidation:
    """Validate a single run. Uses manifest if available, falls back to file scanning."""
    issues = []
    providers_found = set()
    total_trajectories = 0
    total_stable = 0
    total_volatile = 0
    files_count = 0

    # Try manifest first (canonical format)
    manifest = load_manifest(run_id)
    if manifest:
        providers_found = extract_providers_from_manifest(manifest)
        total_complete, total_incomplete, total = count_trajectories_from_manifest(manifest)
        total_stable = total_complete
        total_volatile = total_incomplete
        total_trajectories = total
        summary = manifest.get('summary', {})
        files_count = summary.get('total_files', 0)

        # Check for files_processed list
        files_processed = summary.get('files_processed', [])
        if files_processed:
            files_count = len(files_processed)

    else:
        # Fallback: scan individual files
        files = find_run_files(run_id)
        files_count = len(files)

        if not files:
            return RunValidation(
                run_id=run_id,
                files_found=0,
                providers_found=[],
                providers_missing=required_providers,
                trajectory_count=0,
                stable_count=0,
                volatile_count=0,
                valid=False,
                issues=[f"No data files found for run {run_id}"]
            )

        for filepath in files:
            data = load_run_data(filepath)
            if data:
                providers_found.update(extract_providers_from_run(data))
                stable, volatile, unknown = count_trajectories(data)
                total_trajectories += stable + volatile + unknown
                total_stable += stable
                total_volatile += volatile

    providers_missing = [p for p in required_providers if p not in providers_found]

    if providers_missing:
        issues.append(f"Missing providers: {', '.join(providers_missing)}")

    if total_trajectories == 0:
        issues.append("No trajectories found in data")

    return RunValidation(
        run_id=run_id,
        files_found=files_count,
        providers_found=sorted(providers_found),
        providers_missing=providers_missing,
        trajectory_count=total_trajectories,
        stable_count=total_stable,
        volatile_count=total_volatile,
        valid=len(issues) == 0,
        issues=issues
    )

def validate_layer(layer_num: int) -> LayerValidation:
    """Validate an entire layer."""
    if layer_num not in LAYERS:
        return LayerValidation(
            layer_num=layer_num,
            layer_name="UNKNOWN",
            runs_validated=[],
            runs_missing=[],
            provider_coverage={},
            valid=False,
            issues=[f"Layer {layer_num} not defined"]
        )

    spec = LAYERS[layer_num]
    runs_validated = []
    runs_missing = []
    provider_coverage = defaultdict(list)
    issues = []

    # Handle "021+" pattern
    run_ids = spec.runs
    if "021+" in run_ids:
        # Find all runs 021 and above
        all_files = list(RESULTS_DIR.glob("S7_run_*.json"))
        all_files.extend(LEGACY_DIR.glob("S7_run_*.json"))
        high_runs = set()
        for f in all_files:
            # Extract run number
            parts = f.stem.split('_')
            for i, p in enumerate(parts):
                if p == 'run' and i+1 < len(parts):
                    try:
                        run_num = int(parts[i+1][:3])
                        if run_num >= 21:
                            high_runs.add(f"{run_num:03d}")
                    except ValueError:
                        pass
        run_ids = sorted(high_runs) if high_runs else []

    for run_id in run_ids:
        validation = validate_run(run_id, spec.required_providers)
        runs_validated.append(validation)

        if not validation.valid and validation.files_found == 0:
            runs_missing.append(run_id)

        # Track provider coverage
        for provider in validation.providers_found:
            provider_coverage[provider].append(run_id)

    # Check required providers across layer
    for provider in spec.required_providers:
        if provider not in provider_coverage:
            issues.append(f"Provider '{provider}' has NO coverage in this layer")
        elif len(provider_coverage[provider]) < len(run_ids) / 2:
            issues.append(f"Provider '{provider}' has low coverage: {len(provider_coverage[provider])}/{len(run_ids)} runs")

    return LayerValidation(
        layer_num=layer_num,
        layer_name=spec.name,
        runs_validated=runs_validated,
        runs_missing=runs_missing,
        provider_coverage=dict(provider_coverage),
        valid=len(issues) == 0 and len(runs_missing) == 0,
        issues=issues
    )

# =============================================================================
# REPORTING
# =============================================================================

def generate_stackup_report() -> str:
    """Generate full Iron Clad stackup validation report."""
    lines = []
    lines.append("=" * 70)
    lines.append("IRON CLAD TEMPORAL STABILITY STACKUP")
    lines.append("=" * 70)
    lines.append(f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    lines.append("")

    total_valid = 0
    total_layers = len(LAYERS)

    for layer_num in sorted(LAYERS.keys()):
        spec = LAYERS[layer_num]
        validation = validate_layer(layer_num)

        status = "VALID" if validation.valid else "INCOMPLETE"
        if validation.valid:
            total_valid += 1

        lines.append("-" * 70)
        lines.append(f"Layer {layer_num}: {spec.name} [{status}]")
        lines.append(f"  Description: {spec.description}")
        lines.append(f"  Runs: {', '.join(spec.runs)}")
        lines.append("")

        # Run details
        for run_val in validation.runs_validated:
            run_status = "OK" if run_val.valid else "ISSUES"
            lines.append(f"  Run {run_val.run_id}: [{run_status}]")
            lines.append(f"    Files: {run_val.files_found}")
            lines.append(f"    Trajectories: {run_val.trajectory_count} (S:{run_val.stable_count} V:{run_val.volatile_count})")
            lines.append(f"    Providers: {', '.join(run_val.providers_found) or 'NONE'}")
            if run_val.providers_missing:
                lines.append(f"    Missing: {', '.join(run_val.providers_missing)}")
            if run_val.issues:
                for issue in run_val.issues:
                    lines.append(f"    ! {issue}")

        # Provider coverage matrix
        lines.append("")
        lines.append("  Provider Coverage:")
        for provider in PROVIDERS:
            runs = validation.provider_coverage.get(provider, [])
            coverage = f"{len(runs)}/{len(spec.runs)}" if spec.runs[0] != "021+" else f"{len(runs)}"
            symbol = "Y" if runs else "-"
            lines.append(f"    {provider:10s}: [{symbol}] {coverage}")

        if validation.issues:
            lines.append("")
            lines.append("  Layer Issues:")
            for issue in validation.issues:
                lines.append(f"    ! {issue}")

        lines.append("")

    # Summary
    lines.append("=" * 70)
    lines.append("SUMMARY")
    lines.append("=" * 70)
    lines.append(f"Layers Valid: {total_valid}/{total_layers}")
    lines.append(f"Iron Clad Status: {'COMPLETE' if total_valid == total_layers else 'INCOMPLETE'}")
    lines.append("")

    # Provider coverage across all layers
    lines.append("Provider Coverage Across All Layers:")
    all_coverage = defaultdict(set)
    for layer_num in LAYERS:
        validation = validate_layer(layer_num)
        for provider, runs in validation.provider_coverage.items():
            all_coverage[provider].update(runs)

    for provider in PROVIDERS:
        runs = all_coverage.get(provider, set())
        lines.append(f"  {provider:10s}: {len(runs)} runs")

    lines.append("")
    lines.append("=" * 70)

    return "\n".join(lines)

def generate_json_report() -> Dict:
    """Generate JSON report for automation."""
    result = {
        "generated": datetime.now().isoformat(),
        "layers": {},
        "summary": {
            "total_layers": len(LAYERS),
            "valid_layers": 0,
            "provider_coverage": {}
        }
    }

    all_coverage = defaultdict(set)

    for layer_num in sorted(LAYERS.keys()):
        spec = LAYERS[layer_num]
        validation = validate_layer(layer_num)

        if validation.valid:
            result["summary"]["valid_layers"] += 1

        result["layers"][layer_num] = {
            "name": spec.name,
            "description": spec.description,
            "valid": validation.valid,
            "runs": [
                {
                    "run_id": r.run_id,
                    "valid": r.valid,
                    "files_found": r.files_found,
                    "trajectory_count": r.trajectory_count,
                    "providers_found": r.providers_found,
                    "providers_missing": r.providers_missing,
                    "issues": r.issues
                }
                for r in validation.runs_validated
            ],
            "provider_coverage": validation.provider_coverage,
            "issues": validation.issues
        }

        for provider, runs in validation.provider_coverage.items():
            all_coverage[provider].update(runs)

    result["summary"]["provider_coverage"] = {
        p: len(runs) for p, runs in all_coverage.items()
    }
    result["summary"]["iron_clad_complete"] = (
        result["summary"]["valid_layers"] == result["summary"]["total_layers"]
    )

    return result

# =============================================================================
# MAIN
# =============================================================================

def main():
    parser = argparse.ArgumentParser(description='Iron Clad Temporal Stability Stackup Validation')
    parser.add_argument('--layer', type=int, help='Validate specific layer (1-5)')
    parser.add_argument('--run', type=str, help='Validate specific run ID')
    parser.add_argument('--provider', type=str, help='Check coverage for specific provider')
    parser.add_argument('--json', action='store_true', help='Output as JSON')
    parser.add_argument('--summary', action='store_true', help='Show summary only')

    args = parser.parse_args()

    if args.json:
        print(json.dumps(generate_json_report(), indent=2))
        return

    if args.run:
        # Validate single run
        validation = validate_run(args.run, PROVIDERS[:3])  # Default required providers
        print(f"Run {args.run} Validation:")
        print(f"  Valid: {validation.valid}")
        print(f"  Files: {validation.files_found}")
        print(f"  Trajectories: {validation.trajectory_count}")
        print(f"  Providers: {', '.join(validation.providers_found)}")
        if validation.issues:
            print(f"  Issues: {', '.join(validation.issues)}")
        return

    if args.layer:
        # Validate single layer
        validation = validate_layer(args.layer)
        spec = LAYERS.get(args.layer)
        if spec:
            print(f"Layer {args.layer}: {spec.name}")
            print(f"  Description: {spec.description}")
            print(f"  Valid: {validation.valid}")
            print(f"  Runs validated: {len(validation.runs_validated)}")
            print(f"  Runs missing: {validation.runs_missing}")
            if validation.issues:
                print(f"  Issues:")
                for issue in validation.issues:
                    print(f"    - {issue}")
        return

    if args.provider:
        # Check provider coverage
        provider = args.provider.lower()
        print(f"Coverage for provider: {provider}")
        for layer_num in sorted(LAYERS.keys()):
            validation = validate_layer(layer_num)
            runs = validation.provider_coverage.get(provider, [])
            print(f"  Layer {layer_num} ({LAYERS[layer_num].name}): {len(runs)} runs")
            if runs:
                print(f"    Runs: {', '.join(runs)}")
        return

    # Full report
    print(generate_stackup_report())

if __name__ == "__main__":
    main()
