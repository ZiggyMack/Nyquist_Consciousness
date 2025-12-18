"""
EXP-PFI-A Phase 1: Embedding Invariance Test
============================================

Purpose: Test whether PFI rankings are stable across different embedding models.
Success Criterion: Spearman's rho > 0.8 across embedding model pairs.

This script:
1. Loads raw responses from existing Run 006/007 data
2. Computes embeddings using multiple embedding models
3. Calculates PFI (drift from baseline) for each model
4. Computes Spearman rank correlation across embedding models
5. Reports pass/fail based on rho > 0.8 threshold

Date: 2025-12-04
Part of: Nyquist Consciousness Framework - S7 ARMADA
"""

import json
import os
import sys
from pathlib import Path
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass
import numpy as np
from scipy import stats
from datetime import datetime

# Add parent directories to path
sys.path.insert(0, str(Path(__file__).parent.parent.parent))

# Load environment variables from .env file
def load_env():
    """Load API keys from .env file."""
    env_path = Path(__file__).parent.parent.parent / '.env'
    if env_path.exists():
        print(f"Loading API keys from: {env_path}")
        with open(env_path, 'r') as f:
            for line in f:
                line = line.strip()
                if line and not line.startswith('#') and '=' in line:
                    key, value = line.split('=', 1)
                    os.environ[key.strip()] = value.strip()
        return True
    return False

load_env()

# Embedding model clients
try:
    from openai import OpenAI
    OPENAI_AVAILABLE = True
except ImportError:
    OPENAI_AVAILABLE = False
    print("Warning: OpenAI not installed. Some embedding models unavailable.")

try:
    import voyageai
    VOYAGE_AVAILABLE = True
except ImportError:
    VOYAGE_AVAILABLE = False
    print("Warning: VoyageAI not installed. voyage-3-large unavailable.")

try:
    import cohere
    COHERE_AVAILABLE = True
except ImportError:
    COHERE_AVAILABLE = False
    print("Warning: Cohere not installed. embed-english-v3.0 unavailable.")


@dataclass
class EmbeddingResult:
    """Result from a single embedding computation."""
    model_name: str
    text: str
    embedding: np.ndarray
    dimension: int


@dataclass
class PFIResult:
    """PFI (drift) result for a single response."""
    ship: str
    probe_dimension: str
    probe_text: str
    response_text: str
    pfi_values: Dict[str, float]  # embedding_model -> PFI value


class EmbeddingInvarianceTest:
    """
    Test PFI stability across embedding models.

    The core question: Does changing the embedding model change our conclusions
    about which AI models are more/less stable?
    """

    # Embedding models to test
    EMBEDDING_MODELS = {
        'text-embedding-3-large': {
            'provider': 'openai',
            'dimensions': 3072,
            'description': 'Current production model'
        },
        'text-embedding-3-small': {
            'provider': 'openai',
            'dimensions': 1536,
            'description': 'Smaller OpenAI model'
        },
        'text-embedding-ada-002': {
            'provider': 'openai',
            'dimensions': 1536,
            'description': 'Legacy OpenAI model'
        },
        # Uncomment when API keys available:
        # 'voyage-3-large': {
        #     'provider': 'voyage',
        #     'dimensions': 1024,
        #     'description': 'Voyage AI large model'
        # },
        # 'embed-english-v3.0': {
        #     'provider': 'cohere',
        #     'dimensions': 1024,
        #     'description': 'Cohere English model'
        # }
    }

    # Success threshold
    SPEARMAN_THRESHOLD = 0.8

    def __init__(self, data_dir: str = None):
        """Initialize with path to armada results."""
        if data_dir is None:
            data_dir = Path(__file__).parent.parent.parent / 'results' / 'runs'
        self.data_dir = Path(data_dir)

        # Initialize API clients
        self.openai_client = None
        if OPENAI_AVAILABLE:
            api_key = os.environ.get('OPENAI_API_KEY')
            if api_key:
                self.openai_client = OpenAI(api_key=api_key)

        self.voyage_client = None
        if VOYAGE_AVAILABLE:
            api_key = os.environ.get('VOYAGE_API_KEY')
            if api_key:
                self.voyage_client = voyageai.Client(api_key=api_key)

        self.cohere_client = None
        if COHERE_AVAILABLE:
            api_key = os.environ.get('COHERE_API_KEY')
            if api_key:
                self.cohere_client = cohere.Client(api_key=api_key)

        # Results storage
        self.responses: List[Dict] = []
        self.embeddings: Dict[str, Dict[str, np.ndarray]] = {}  # model -> {response_id -> embedding}
        self.pfi_values: Dict[str, Dict[str, float]] = {}  # model -> {ship -> avg_pfi}

    def load_responses_from_run(self, run_file: str) -> List[Dict]:
        """
        Load raw responses from a run JSON file.

        Returns list of dicts with: ship, probe_dimension, probe, response
        """
        responses = []
        filepath = self.data_dir / run_file

        if not filepath.exists():
            print(f"Warning: {run_file} not found")
            return responses

        with open(filepath, 'r', encoding='utf-8') as f:
            data = json.load(f)

        # Extract responses from model_summaries
        model_summaries = data.get('model_summaries', {})

        for ship, ship_data in model_summaries.items():
            probes = ship_data.get('probes', [])
            for probe_data in probes:
                response = probe_data.get('response', '')
                if response:  # Only include if response exists
                    responses.append({
                        'ship': ship,
                        'probe_dimension': probe_data.get('dimension', 'unknown'),
                        'probe': probe_data.get('probe', ''),
                        'response': response,
                        'full_response_len': probe_data.get('full_response_len', len(response)),
                        'original_drift': probe_data.get('drift', None)
                    })

        print(f"Loaded {len(responses)} responses from {run_file}")
        return responses

    def get_embedding(self, text: str, model: str) -> Optional[np.ndarray]:
        """Get embedding for text using specified model."""
        model_info = self.EMBEDDING_MODELS.get(model)
        if not model_info:
            return None

        provider = model_info['provider']

        try:
            if provider == 'openai' and self.openai_client:
                response = self.openai_client.embeddings.create(
                    model=model,
                    input=text
                )
                return np.array(response.data[0].embedding)

            elif provider == 'voyage' and self.voyage_client:
                response = self.voyage_client.embed(
                    texts=[text],
                    model=model
                )
                return np.array(response.embeddings[0])

            elif provider == 'cohere' and self.cohere_client:
                response = self.cohere_client.embed(
                    texts=[text],
                    model=model
                )
                return np.array(response.embeddings[0])

        except Exception as e:
            print(f"Error getting embedding with {model}: {e}")
            return None

        return None

    def compute_pfi(self, response_embedding: np.ndarray,
                    baseline_embedding: np.ndarray) -> float:
        """
        Compute PFI (Persona Fidelity Index) as cosine distance.

        PFI = 1 - cosine_similarity(response, baseline)

        Range: [0, 2] where 0 = identical, 2 = opposite
        """
        # Normalize vectors
        resp_norm = response_embedding / (np.linalg.norm(response_embedding) + 1e-10)
        base_norm = baseline_embedding / (np.linalg.norm(baseline_embedding) + 1e-10)

        # Cosine similarity
        cos_sim = np.dot(resp_norm, base_norm)

        # PFI as cosine distance
        pfi = 1 - cos_sim

        return float(pfi)

    def compute_all_embeddings(self, responses: List[Dict]) -> Dict[str, Dict[str, np.ndarray]]:
        """
        Compute embeddings for all responses using all available embedding models.

        Returns: {embedding_model: {response_id: embedding}}
        """
        embeddings = {}

        # Filter to available models
        available_models = []
        for model, info in self.EMBEDDING_MODELS.items():
            provider = info['provider']
            if provider == 'openai' and self.openai_client:
                available_models.append(model)
            elif provider == 'voyage' and self.voyage_client:
                available_models.append(model)
            elif provider == 'cohere' and self.cohere_client:
                available_models.append(model)

        if not available_models:
            print("ERROR: No embedding models available. Check API keys.")
            return embeddings

        print(f"Computing embeddings with {len(available_models)} models: {available_models}")

        for model in available_models:
            print(f"\n  Processing {model}...")
            embeddings[model] = {}

            for i, resp in enumerate(responses):
                response_id = f"{resp['ship']}_{resp['probe_dimension']}_{i}"
                text = resp['response']

                embedding = self.get_embedding(text, model)
                if embedding is not None:
                    embeddings[model][response_id] = embedding

                if (i + 1) % 10 == 0:
                    print(f"    {i + 1}/{len(responses)} responses embedded")

            print(f"  {model}: {len(embeddings[model])} embeddings computed")

        return embeddings

    def compute_pfi_by_ship(self, embeddings: Dict[str, Dict[str, np.ndarray]],
                           responses: List[Dict]) -> Dict[str, Dict[str, float]]:
        """
        Compute average PFI per ship for each embedding model.

        Uses first response of each ship as baseline.

        Returns: {embedding_model: {ship: avg_pfi}}
        """
        pfi_by_ship = {}

        for model, model_embeddings in embeddings.items():
            pfi_by_ship[model] = {}

            # Group responses by ship
            ship_responses = {}
            for i, resp in enumerate(responses):
                ship = resp['ship']
                response_id = f"{ship}_{resp['probe_dimension']}_{i}"

                if response_id in model_embeddings:
                    if ship not in ship_responses:
                        ship_responses[ship] = []
                    ship_responses[ship].append({
                        'response_id': response_id,
                        'embedding': model_embeddings[response_id]
                    })

            # Compute PFI for each ship
            for ship, ship_resps in ship_responses.items():
                if len(ship_resps) < 2:
                    continue

                # Use first response as baseline
                baseline = ship_resps[0]['embedding']

                # Compute PFI for subsequent responses
                pfis = []
                for resp in ship_resps[1:]:
                    pfi = self.compute_pfi(resp['embedding'], baseline)
                    pfis.append(pfi)

                if pfis:
                    pfi_by_ship[model][ship] = np.mean(pfis)

        return pfi_by_ship

    def compute_rank_correlations(self, pfi_by_ship: Dict[str, Dict[str, float]]) -> Dict[Tuple[str, str], float]:
        """
        Compute Spearman rank correlations between all pairs of embedding models.

        Returns: {(model1, model2): spearman_rho}
        """
        correlations = {}
        models = list(pfi_by_ship.keys())

        for i, model1 in enumerate(models):
            for model2 in models[i+1:]:
                # Find common ships
                ships1 = set(pfi_by_ship[model1].keys())
                ships2 = set(pfi_by_ship[model2].keys())
                common_ships = ships1 & ships2

                if len(common_ships) < 3:
                    print(f"Warning: Only {len(common_ships)} common ships for {model1} vs {model2}")
                    continue

                # Get PFI values in same order
                vals1 = [pfi_by_ship[model1][ship] for ship in common_ships]
                vals2 = [pfi_by_ship[model2][ship] for ship in common_ships]

                # Compute Spearman correlation
                rho, p_value = stats.spearmanr(vals1, vals2)
                correlations[(model1, model2)] = {
                    'rho': rho,
                    'p_value': p_value,
                    'n_ships': len(common_ships)
                }

        return correlations

    def run_test(self, run_files: List[str] = None) -> Dict:
        """
        Run the complete embedding invariance test.

        Returns comprehensive results dict.
        """
        print("=" * 60)
        print("EXP-PFI-A Phase 1: Embedding Invariance Test")
        print("=" * 60)

        # Default to Run 006 and 007 which have raw responses
        if run_files is None:
            run_files = ['S7_armada_run_006.json', 'S7_armada_run_007_adaptive.json']

        # Step 1: Load responses
        print("\n[Step 1] Loading responses...")
        all_responses = []
        for run_file in run_files:
            responses = self.load_responses_from_run(run_file)
            all_responses.extend(responses)

        if not all_responses:
            return {'error': 'No responses loaded', 'passed': False}

        print(f"Total responses: {len(all_responses)}")

        # Step 2: Compute embeddings
        print("\n[Step 2] Computing embeddings...")
        embeddings = self.compute_all_embeddings(all_responses)

        if len(embeddings) < 2:
            return {
                'error': 'Need at least 2 embedding models for comparison',
                'available_models': list(embeddings.keys()),
                'passed': False
            }

        # Step 3: Compute PFI by ship
        print("\n[Step 3] Computing PFI by ship...")
        pfi_by_ship = self.compute_pfi_by_ship(embeddings, all_responses)

        for model, ship_pfis in pfi_by_ship.items():
            print(f"  {model}: {len(ship_pfis)} ships")

        # Step 4: Compute rank correlations
        print("\n[Step 4] Computing Spearman rank correlations...")
        correlations = self.compute_rank_correlations(pfi_by_ship)

        # Step 5: Evaluate pass/fail
        print("\n[Step 5] Evaluating results...")
        all_rhos = [c['rho'] for c in correlations.values()]

        if not all_rhos:
            return {'error': 'No correlations computed', 'passed': False}

        min_rho = min(all_rhos)
        avg_rho = np.mean(all_rhos)

        passed = min_rho >= self.SPEARMAN_THRESHOLD

        # Compile results
        results = {
            'timestamp': datetime.now().isoformat(),
            'run_files': run_files,
            'n_responses': len(all_responses),
            'embedding_models': list(embeddings.keys()),
            'n_models': len(embeddings),
            'correlations': {
                f"{k[0]}_vs_{k[1]}": v for k, v in correlations.items()
            },
            'summary': {
                'min_rho': min_rho,
                'avg_rho': avg_rho,
                'threshold': self.SPEARMAN_THRESHOLD,
                'passed': passed
            },
            'pfi_by_ship_by_model': {
                model: dict(ship_pfis) for model, ship_pfis in pfi_by_ship.items()
            }
        }

        # Print summary
        print("\n" + "=" * 60)
        print("RESULTS SUMMARY")
        print("=" * 60)

        print(f"\nCorrelations between embedding models:")
        for (m1, m2), corr in correlations.items():
            status = "PASS" if corr['rho'] >= self.SPEARMAN_THRESHOLD else "FAIL"
            print(f"  {m1} vs {m2}:")
            print(f"    rho = {corr['rho']:.4f} (p = {corr['p_value']:.2e}) [{status}]")
            print(f"    n = {corr['n_ships']} ships")

        print(f"\nOverall:")
        print(f"  Minimum rho: {min_rho:.4f}")
        print(f"  Average rho: {avg_rho:.4f}")
        print(f"  Threshold:   {self.SPEARMAN_THRESHOLD:.2f}")

        if passed:
            print(f"\n  STATUS: PASSED - PFI rankings are stable across embedding models")
            print(f"  CONCLUSION: Proceed with EXP1/EXP2 execution")
        else:
            print(f"\n  STATUS: FAILED - PFI rankings vary by embedding model")
            print(f"  CONCLUSION: Echo's critique may be valid - investigate further")

        return results

    def save_results(self, results: Dict, output_file: str = None):
        """Save results to JSON file."""
        if output_file is None:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            output_file = Path(__file__).parent / 'results' / f'phase1_results_{timestamp}.json'

        output_file = Path(output_file)
        output_file.parent.mkdir(parents=True, exist_ok=True)

        # Convert numpy types to native Python
        def convert(obj):
            if isinstance(obj, (np.floating, np.float64, np.float32)):
                return float(obj)
            elif isinstance(obj, (np.integer, np.int64, np.int32)):
                return int(obj)
            elif isinstance(obj, np.ndarray):
                return obj.tolist()
            elif isinstance(obj, (np.bool_, bool)):
                return bool(obj)
            elif isinstance(obj, dict):
                return {k: convert(v) for k, v in obj.items()}
            elif isinstance(obj, list):
                return [convert(v) for v in obj]
            return obj

        with open(output_file, 'w', encoding='utf-8') as f:
            json.dump(convert(results), f, indent=2)

        print(f"\nResults saved to: {output_file}")


def main():
    """Run the embedding invariance test."""
    # Check for required API key
    if not os.environ.get('OPENAI_API_KEY'):
        print("ERROR: OPENAI_API_KEY environment variable not set")
        print("Set it with: set OPENAI_API_KEY=your-key-here (Windows)")
        print("            export OPENAI_API_KEY=your-key-here (Linux/Mac)")
        return

    # Initialize and run test
    test = EmbeddingInvarianceTest()
    results = test.run_test()

    # Save results
    if 'error' not in results or results.get('correlations'):
        test.save_results(results)

    return results


if __name__ == '__main__':
    main()
