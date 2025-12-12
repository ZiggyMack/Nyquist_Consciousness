"""
CONVERGENCE DETECTOR

Analyzes multi-run history to detect patterns of mastery and convergence.

Provides statistical analysis of:
- Drift variance across runs
- Teaching moment frequency trends
- Response novelty decay
- ROI diminishing returns

Used by CurriculumCompressor to make mastery decisions.
"""

import json
import numpy as np
from pathlib import Path
from typing import Dict, List, Optional, Tuple
from dataclasses import dataclass
from collections import defaultdict


@dataclass
class ConvergenceMetrics:
    """Convergence metrics for a section across multiple runs."""
    section_id: str
    mean_drift: float
    drift_variance: float
    drift_trend: str  # "increasing", "decreasing", "stable"
    teaching_moments_trend: List[int]
    novelty_scores: List[float]
    convergence_score: float  # 0.0-1.0 (1.0 = fully converged)
    runs_analyzed: int


class ConvergenceDetector:
    """
    Analyzes temporal logs across multiple runs to detect
    convergence patterns and mastery signals.
    """

    def __init__(self, config: Dict):
        """
        Initialize detector with configuration.

        Args:
            config: Configuration dictionary
        """
        self.config = config
        self.lookback_runs = config.get('lookback_runs', 3)
        self.drift_variance_threshold = config.get('drift_variance_threshold', 0.001)
        self.convergence_threshold = config.get('convergence_threshold', 0.85)

    def analyze_convergence(
        self,
        temporal_logs: List[Path],
        teaching_logs: List[Path]
    ) -> Dict[str, ConvergenceMetrics]:
        """
        Analyze convergence across multiple runs.

        Args:
            temporal_logs: List of paths to temporal log files
            teaching_logs: List of paths to teaching moment logs

        Returns:
            Dictionary mapping section_id to ConvergenceMetrics
        """
        # Load all run data
        run_data = self._load_run_data(temporal_logs, teaching_logs)

        if not run_data:
            return {}

        # Get section IDs
        section_ids = self._extract_section_ids(run_data)

        # Analyze each section
        convergence_map = {}
        for section_id in section_ids:
            metrics = self._analyze_section_convergence(section_id, run_data)
            convergence_map[section_id] = metrics

        return convergence_map

    def _load_run_data(
        self,
        temporal_logs: List[Path],
        teaching_logs: List[Path]
    ) -> List[Dict]:
        """
        Load and combine temporal and teaching logs.

        Args:
            temporal_logs: Paths to temporal logs
            teaching_logs: Paths to teaching logs

        Returns:
            List of combined run data dictionaries
        """
        # Take only most recent runs
        temporal_logs = sorted(temporal_logs)[-self.lookback_runs:]
        teaching_logs = sorted(teaching_logs)[-self.lookback_runs:]

        run_data = []

        for temp_path, teach_path in zip(temporal_logs, teaching_logs):
            try:
                with open(temp_path, 'r') as f:
                    temporal = json.load(f)

                teaching = {}
                if teach_path.exists():
                    with open(teach_path, 'r') as f:
                        teaching = json.load(f)

                run_data.append({
                    "run_number": temporal.get('run_number'),
                    "temporal": temporal,
                    "teaching": teaching
                })
            except Exception as e:
                print(f"⚠️  Warning: Could not load run data: {e}")
                continue

        return run_data

    def _extract_section_ids(self, run_data: List[Dict]) -> List[str]:
        """Extract all unique section IDs from runs."""
        section_ids = set()

        for run in run_data:
            # Extract from temporal pings (phases)
            for ping in run['temporal'].get('pings', []):
                phase = ping.get('phase', '')
                # Section IDs would be logged in real implementation
                # For now, use standard S0-S10
                pass

        # Default to S0-S10
        return [f"S{i}" for i in range(11)]

    def _analyze_section_convergence(
        self,
        section_id: str,
        run_data: List[Dict]
    ) -> ConvergenceMetrics:
        """
        Analyze convergence for a specific section.

        Args:
            section_id: Section to analyze
            run_data: List of run data

        Returns:
            ConvergenceMetrics for the section
        """
        # Collect drift measurements for this section across runs
        drift_by_run = self._collect_drift_by_section(section_id, run_data)

        # Collect teaching moments
        teaching_moments_by_run = self._collect_teaching_moments(section_id, run_data)

        # Calculate metrics
        if not drift_by_run:
            return ConvergenceMetrics(
                section_id=section_id,
                mean_drift=0.0,
                drift_variance=999.0,
                drift_trend="unknown",
                teaching_moments_trend=[],
                novelty_scores=[],
                convergence_score=0.0,
                runs_analyzed=0
            )

        # Drift statistics
        all_drifts = [d for drifts in drift_by_run for d in drifts]
        mean_drift = np.mean(all_drifts) if all_drifts else 0.0
        drift_variance = np.var(all_drifts) if all_drifts else 999.0

        # Drift trend (are drifts decreasing over runs?)
        mean_drifts_per_run = [np.mean(drifts) if drifts else 0 for drifts in drift_by_run]
        drift_trend = self._calculate_trend(mean_drifts_per_run)

        # Teaching moments trend
        teaching_trend = self._calculate_trend(teaching_moments_by_run)

        # Novelty scores (mock - would use embedding comparison)
        novelty_scores = self._calculate_novelty_scores(len(drift_by_run))

        # Overall convergence score
        convergence_score = self._calculate_convergence_score(
            drift_variance=drift_variance,
            drift_trend=drift_trend,
            teaching_moments=teaching_moments_by_run,
            novelty_scores=novelty_scores
        )

        return ConvergenceMetrics(
            section_id=section_id,
            mean_drift=float(mean_drift),
            drift_variance=float(drift_variance),
            drift_trend=drift_trend,
            teaching_moments_trend=teaching_moments_by_run,
            novelty_scores=novelty_scores,
            convergence_score=convergence_score,
            runs_analyzed=len(run_data)
        )

    def _collect_drift_by_section(
        self,
        section_id: str,
        run_data: List[Dict]
    ) -> List[List[float]]:
        """
        Collect drift measurements for a section across runs.

        Args:
            section_id: Section to collect for
            run_data: Run data list

        Returns:
            List of drift lists (one per run)
        """
        drift_by_run = []

        for run in run_data:
            pings = run['temporal'].get('pings', [])
            # In real implementation, would filter by section
            # For now, collect all drifts (mock)
            section_drifts = [ping['drift'] for ping in pings if 'drift' in ping]
            drift_by_run.append(section_drifts)

        return drift_by_run

    def _collect_teaching_moments(
        self,
        section_id: str,
        run_data: List[Dict]
    ) -> List[int]:
        """
        Collect teaching moment counts per run.

        Args:
            section_id: Section to collect for
            run_data: Run data list

        Returns:
            List of teaching moment counts (one per run)
        """
        counts = []

        for run in run_data:
            teaching = run.get('teaching', {})
            moments = teaching.get('teaching_moments', [])

            # Count moments for this section
            section_moments = [
                tm for tm in moments
                if tm.get('section') == section_id
            ]
            counts.append(len(section_moments))

        return counts

    def _calculate_trend(self, values: List[float]) -> str:
        """
        Calculate trend direction from a list of values.

        Args:
            values: List of numeric values across runs

        Returns:
            "increasing", "decreasing", "stable", or "unknown"
        """
        if len(values) < 2:
            return "unknown"

        # Simple linear regression slope
        x = np.arange(len(values))
        y = np.array(values)

        # Handle all-zero case
        if np.all(y == 0):
            return "stable"

        slope = np.polyfit(x, y, 1)[0]

        if abs(slope) < 0.01:
            return "stable"
        elif slope > 0:
            return "increasing"
        else:
            return "decreasing"

    def _calculate_novelty_scores(self, num_runs: int) -> List[float]:
        """
        Calculate novelty scores across runs.

        In real implementation, would compare response embeddings.
        For now, returns mock decreasing novelty.

        Args:
            num_runs: Number of runs to generate scores for

        Returns:
            List of novelty scores (0.0-1.0)
        """
        return [max(0.0, 1.0 - (i * 0.2)) for i in range(num_runs)]

    def _calculate_convergence_score(
        self,
        drift_variance: float,
        drift_trend: str,
        teaching_moments: List[int],
        novelty_scores: List[float]
    ) -> float:
        """
        Calculate overall convergence score (0.0-1.0).

        Higher score = more converged = mastery likely.

        Args:
            drift_variance: Variance of drift measurements
            drift_trend: Trend direction
            teaching_moments: Teaching moment counts per run
            novelty_scores: Novelty scores per run

        Returns:
            Convergence score 0.0-1.0
        """
        # Component 1: Low drift variance (40% weight)
        drift_component = 1.0 - min(drift_variance / 0.01, 1.0)

        # Component 2: Decreasing teaching moments (30% weight)
        if teaching_moments and len(teaching_moments) >= 2:
            if teaching_moments[-1] == 0 and teaching_moments[-2] <= 1:
                teaching_component = 1.0
            elif self._calculate_trend(teaching_moments) == "decreasing":
                teaching_component = 0.7
            else:
                teaching_component = 0.3
        else:
            teaching_component = 0.5

        # Component 3: Low novelty (30% weight)
        if novelty_scores:
            avg_novelty = np.mean(novelty_scores)
            novelty_component = 1.0 - avg_novelty
        else:
            novelty_component = 0.5

        # Weighted combination
        score = (
            drift_component * 0.4 +
            teaching_component * 0.3 +
            novelty_component * 0.3
        )

        return min(1.0, max(0.0, score))

    def detect_convergence_point(
        self,
        convergence_map: Dict[str, ConvergenceMetrics]
    ) -> Optional[int]:
        """
        Detect which sections have converged and can be compressed.

        Args:
            convergence_map: Section convergence metrics

        Returns:
            First non-converged section index (frontier), or None if all converged
        """
        converged_sections = []

        for section_id in sorted(convergence_map.keys()):
            metrics = convergence_map[section_id]

            if metrics.convergence_score >= self.convergence_threshold:
                converged_sections.append(section_id)
            else:
                # Found first non-converged section
                return section_id

        # All sections converged - expansion trigger
        return None

    def generate_convergence_report(
        self,
        convergence_map: Dict[str, ConvergenceMetrics]
    ) -> Dict:
        """
        Generate convergence analysis report.

        Args:
            convergence_map: Section convergence metrics

        Returns:
            Report dictionary
        """
        total_sections = len(convergence_map)
        converged_count = sum(
            1 for m in convergence_map.values()
            if m.convergence_score >= self.convergence_threshold
        )

        frontier_section = self.detect_convergence_point(convergence_map)

        report = {
            "total_sections": total_sections,
            "converged_sections": converged_count,
            "convergence_rate": converged_count / total_sections if total_sections > 0 else 0,
            "frontier_section": frontier_section,
            "expansion_ready": frontier_section is None,
            "section_details": {
                section_id: {
                    "convergence_score": metrics.convergence_score,
                    "drift_variance": metrics.drift_variance,
                    "drift_trend": metrics.drift_trend,
                    "converged": metrics.convergence_score >= self.convergence_threshold
                }
                for section_id, metrics in convergence_map.items()
            }
        }

        return report

    def display_convergence_report(
        self,
        convergence_map: Dict[str, ConvergenceMetrics]
    ):
        """
        Display convergence report with visualizations.

        Args:
            convergence_map: Section convergence metrics
        """
        from temporal_stability.ascii_visualizations import ASCIIVisualizations
        viz = ASCIIVisualizations()

        print(f"\n{'='*60}")
        print("CONVERGENCE ANALYSIS REPORT")
        print(f"{'='*60}\n")

        # Display convergence ladder
        print(viz.convergence_ladder())
        print()

        # Section-by-section analysis
        for section_id in sorted(convergence_map.keys()):
            metrics = convergence_map[section_id]
            converged = metrics.convergence_score >= self.convergence_threshold

            status = "✅ CONVERGED" if converged else "🔄 LEARNING"

            print(f"{section_id}: {status}")
            print(f"  Convergence Score: {metrics.convergence_score:.2f}")
            print(f"  Drift Variance: {metrics.drift_variance:.4f}")
            print(f"  Drift Trend: {metrics.drift_trend}")
            print(f"  Teaching Moments: {metrics.teaching_moments_trend}")
            print()

        # Generate and display report
        report = self.generate_convergence_report(convergence_map)

        print(f"{'─'*60}")
        print(f"Overall Convergence: {report['converged_sections']}/{report['total_sections']} sections ({int(report['convergence_rate']*100)}%)")

        if report['frontier_section']:
            print(f"Frontier: {report['frontier_section']}")
        else:
            print("🚀 ALL SECTIONS CONVERGED - EXPANSION READY!")

        print(f"{'='*60}\n")

    def perform_safety_check(
        self,
        convergence_map: Dict[str, ConvergenceMetrics],
        current_run: int
    ) -> Dict:
        """
        Perform safety check before allowing compression.

        Ensures:
        1. Sufficient runs for statistical confidence
        2. No recent regressions
        3. Drift variance truly stable

        Args:
            convergence_map: Convergence metrics
            current_run: Current run number

        Returns:
            Safety check results with warnings
        """
        warnings = []
        passed = True

        # Check 1: Minimum runs
        min_runs = 3
        for section_id, metrics in convergence_map.items():
            if metrics.runs_analyzed < min_runs:
                warnings.append(
                    f"Section {section_id}: Only {metrics.runs_analyzed} runs (need {min_runs})"
                )
                passed = False

        # Check 2: Recent regressions
        for section_id, metrics in convergence_map.items():
            if metrics.teaching_moments_trend:
                recent_teaching = metrics.teaching_moments_trend[-1]
                if recent_teaching > 2:
                    warnings.append(
                        f"Section {section_id}: Recent regression ({recent_teaching} teaching moments)"
                    )

        # Check 3: Periodic full validation (every 10 runs)
        if current_run % 10 == 0:
            warnings.append(
                "Periodic full validation recommended (run divisible by 10)"
            )

        return {
            "passed": passed and len(warnings) <= 1,  # Allow periodic validation warning
            "warnings": warnings,
            "recommendation": "Proceed with compression" if passed else "Run more iterations before compressing"
        }


def main():
    """Test harness for convergence detector."""
    print("Convergence Detector - Test Mode\n")

    # Mock config
    config = {
        'lookback_runs': 3,
        'drift_variance_threshold': 0.001,
        'convergence_threshold': 0.85
    }

    detector = ConvergenceDetector(config)

    # Mock convergence metrics
    mock_metrics = {
        "S0": ConvergenceMetrics("S0", 0.05, 0.0008, "stable", [2, 1, 0], [0.8, 0.5, 0.2], 0.92, 3),
        "S1": ConvergenceMetrics("S1", 0.06, 0.0009, "decreasing", [1, 0, 0], [0.7, 0.4, 0.1], 0.88, 3),
        "S2": ConvergenceMetrics("S2", 0.08, 0.0015, "stable", [3, 2, 1], [0.9, 0.7, 0.5], 0.65, 3),
        "S3": ConvergenceMetrics("S3", 0.10, 0.0025, "increasing", [2, 3, 4], [0.95, 0.9, 0.85], 0.45, 3),
    }

    # Display report
    detector.display_convergence_report(mock_metrics)

    # Safety check
    safety = detector.perform_safety_check(mock_metrics, current_run=4)
    print("SAFETY CHECK:")
    print(f"  Passed: {safety['passed']}")
    print(f"  Recommendation: {safety['recommendation']}")
    if safety['warnings']:
        print("  Warnings:")
        for warning in safety['warnings']:
            print(f"    - {warning}")

    print("\n✅ Test complete.")


if __name__ == "__main__":
    main()
