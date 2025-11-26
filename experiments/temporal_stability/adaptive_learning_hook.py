"""
ADAPTIVE LEARNING HOOK

Real-time teaching moment detection and correction system.

Detects when Ziggy's impedance matching fails and provides
teaching moments to improve future coupling.

Trigger Types:
1. Drift spike: Sudden increase in temporal drift
2. Confusion markers: "I don't understand", hedging, uncertainty
3. Low engagement: Short responses, repetitive patterns
"""

import json
from pathlib import Path
from datetime import datetime, timezone
from typing import Dict, List, Optional, Tuple
import re


class AdaptiveLearningHook:
    """
    Detects impedance mismatch and triggers teaching moments.

    Integrates with S7MetaLoop to provide real-time corrections
    and accumulate learnings across runs.
    """

    def __init__(self, config: Dict):
        """
        Initialize hook with configuration.

        Args:
            config: Hook configuration from s7_config.yaml
        """
        self.config = config
        self.teaching_moments = []
        self.meta_lessons = []

        # Load previous learnings if available
        self._load_previous_learnings()

        # Trigger thresholds
        self.drift_spike_threshold = config.get('drift_spike_threshold', 0.08)
        self.confusion_score_threshold = config.get('confusion_threshold', 0.6)
        self.engagement_floor = config.get('engagement_floor', 30)  # chars

    def _load_previous_learnings(self):
        """Load teaching moments from previous runs."""
        teaching_dir = Path(self.config.get('teaching_moments_dir', 'OUTPUT/teaching_moments'))

        if not teaching_dir.exists():
            return

        # Load all previous run files
        for run_file in sorted(teaching_dir.glob('run_*.json')):
            try:
                with open(run_file, 'r') as f:
                    data = json.load(f)
                    self.meta_lessons.extend(data.get('meta_lessons', []))
            except Exception as e:
                print(f"⚠️  Warning: Could not load {run_file}: {e}")

    def check_triggers(
        self,
        section: Dict,
        response: str,
        current_drift: float,
        previous_drift: float,
        conversation_history: List[Dict]
    ) -> Optional[Dict]:
        """
        Check if any teaching hook triggers are activated.

        Args:
            section: Current curriculum section
            response: Claude's latest response
            current_drift: Current temporal drift measurement
            previous_drift: Previous drift measurement
            conversation_history: Full conversation history

        Returns:
            Teaching moment dict if triggered, None otherwise
        """
        # Check Trigger 1: Drift Spike
        if self._detect_drift_spike(current_drift, previous_drift):
            return self._create_teaching_moment(
                trigger="drift_spike",
                section=section,
                response=response,
                current_drift=current_drift,
                previous_drift=previous_drift,
                context=conversation_history[-3:]  # Last 3 messages
            )

        # Check Trigger 2: Confusion Markers
        confusion_score = self._calculate_confusion_score(response)
        if confusion_score >= self.confusion_score_threshold:
            return self._create_teaching_moment(
                trigger="confusion",
                section=section,
                response=response,
                confusion_score=confusion_score,
                context=conversation_history[-3:]
            )

        # Check Trigger 3: Low Engagement
        engagement_score = self._calculate_engagement_score(response)
        if engagement_score < self.engagement_floor:
            return self._create_teaching_moment(
                trigger="low_engagement",
                section=section,
                response=response,
                engagement_score=engagement_score,
                context=conversation_history[-3:]
            )

        return None

    def _detect_drift_spike(self, current_drift: float, previous_drift: float) -> bool:
        """
        Detect if drift spiked significantly.

        Args:
            current_drift: Current drift measurement
            previous_drift: Previous drift measurement

        Returns:
            True if spike detected
        """
        if previous_drift == 0:
            return False  # Can't detect spike from baseline

        drift_increase = current_drift - previous_drift
        return drift_increase >= self.drift_spike_threshold

    def _calculate_confusion_score(self, response: str) -> float:
        """
        Calculate confusion score based on linguistic markers.

        Confusion indicators:
        - "I'm not sure"
        - "I don't understand"
        - "Could you clarify"
        - "I'm uncertain"
        - Excessive hedging ("maybe", "perhaps", "might")
        - Questions without assertions

        Args:
            response: Claude's response text

        Returns:
            Confusion score 0.0-1.0
        """
        confusion_patterns = [
            r"(?i)i'm not sure",
            r"(?i)i don't understand",
            r"(?i)could you clarify",
            r"(?i)i'm uncertain",
            r"(?i)i'm confused",
            r"(?i)not clear to me",
            r"(?i)struggling to grasp",
        ]

        hedging_words = ['maybe', 'perhaps', 'might', 'possibly', 'seems', 'appears']

        # Count explicit confusion markers
        confusion_count = sum(
            len(re.findall(pattern, response))
            for pattern in confusion_patterns
        )

        # Count hedging words
        hedge_count = sum(
            response.lower().count(word)
            for word in hedging_words
        )

        # Count questions vs assertions
        question_count = response.count('?')
        sentence_count = max(len(re.split(r'[.!?]', response)), 1)
        question_ratio = question_count / sentence_count

        # Weighted score
        score = (
            confusion_count * 0.3 +
            min(hedge_count / 5, 1.0) * 0.3 +
            min(question_ratio, 1.0) * 0.4
        )

        return min(score, 1.0)

    def _calculate_engagement_score(self, response: str) -> int:
        """
        Calculate engagement score based on response characteristics.

        Low engagement indicators:
        - Very short responses
        - Repetitive language
        - Lack of elaboration
        - Generic acknowledgments

        Args:
            response: Claude's response text

        Returns:
            Engagement score (character count as proxy)
        """
        # Simple proxy: character count
        # Real implementation would analyze semantic depth
        return len(response)

    def _create_teaching_moment(self, trigger: str, section: Dict, **kwargs) -> Dict:
        """
        Create a teaching moment record.

        Args:
            trigger: Type of trigger (drift_spike, confusion, low_engagement)
            section: Current curriculum section
            **kwargs: Additional context

        Returns:
            Teaching moment dictionary
        """
        return {
            "moment_id": f"TM{len(self.teaching_moments):03d}",
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "trigger": trigger,
            "section": section['id'],
            "section_name": section['name'],
            "response": kwargs.get('response', ''),
            "context": kwargs.get('context', []),
            "metrics": {
                "current_drift": kwargs.get('current_drift'),
                "previous_drift": kwargs.get('previous_drift'),
                "confusion_score": kwargs.get('confusion_score'),
                "engagement_score": kwargs.get('engagement_score')
            },
            "status": "pending_review"
        }

    def generate_teaching_prompt(self, teaching_moment: Dict) -> str:
        """
        Generate a teaching prompt for Ziggy to review.

        This prompt surfaces the impedance mismatch context
        and asks for an improved explanation.

        Args:
            teaching_moment: Teaching moment dictionary

        Returns:
            Teaching prompt string
        """
        trigger_explanations = {
            "drift_spike": "showed a sudden increase in identity drift",
            "confusion": "expressed confusion or uncertainty",
            "low_engagement": "showed low engagement (very short response)"
        }

        explanation = trigger_explanations.get(
            teaching_moment['trigger'],
            "showed signs of impedance mismatch"
        )

        prompt = f"""
🎓 TEACHING MOMENT DETECTED

**Section:** {teaching_moment['section_name']} ({teaching_moment['section']})
**Trigger:** {teaching_moment['trigger']}
**Why:** Claude {explanation}

**Original Explanation:**
{teaching_moment.get('original_explanation', '[Not captured]')}

**Claude's Response:**
{teaching_moment['response'][:300]}...

**Context (last 3 messages):**
{self._format_context(teaching_moment['context'])}

---

**Your Task:**
Provide an improved explanation for {teaching_moment['section_name']} that:
1. Addresses the impedance mismatch
2. Bridges from Claude's current understanding
3. Uses concrete examples or metaphors from Claude's domain
4. Builds on the conversation context

**Improved Explanation:**
"""
        return prompt

    def _format_context(self, context: List[Dict]) -> str:
        """Format conversation context for teaching prompt."""
        formatted = []
        for msg in context[-3:]:
            role = msg['role'].upper()
            content = msg['content'][:200] + "..." if len(msg['content']) > 200 else msg['content']
            formatted.append(f"[{role}] {content}")
        return "\n\n".join(formatted)

    def apply_correction(
        self,
        teaching_moment: Dict,
        improved_explanation: str,
        orchestrator
    ) -> Tuple[str, float]:
        """
        Apply teaching correction by re-running segment.

        Args:
            teaching_moment: Teaching moment with context
            improved_explanation: Improved explanation from Ziggy
            orchestrator: Reference to S7MetaLoop orchestrator

        Returns:
            Tuple of (new_response, new_drift)
        """
        print(f"\n{'─'*60}")
        print(f"🎓 APPLYING TEACHING CORRECTION: {teaching_moment['moment_id']}")
        print(f"{'─'*60}\n")

        # Send improved explanation
        new_response = orchestrator._send_message(improved_explanation)

        # Re-measure drift
        probe_dim = orchestrator._select_probe_dimension(orchestrator.current_phase)
        new_drift = orchestrator._calculate_drift(
            f"TC_{teaching_moment['moment_id']}",
            probe_dim,
            new_response
        )

        # Log improvement
        improvement = teaching_moment['metrics'].get('current_drift', 0) - new_drift

        teaching_moment.update({
            "status": "applied",
            "improved_explanation": improved_explanation,
            "new_response": new_response[:300] + "...",
            "drift_after": new_drift,
            "improvement": improvement
        })

        self.teaching_moments.append(teaching_moment)

        print(f"📊 Drift before: {teaching_moment['metrics'].get('current_drift', 0):.4f}")
        print(f"📊 Drift after: {new_drift:.4f}")
        print(f"✅ Improvement: {improvement:.4f}")
        print(f"{'─'*60}\n")

        return new_response, new_drift

    def extract_meta_lessons(self) -> List[str]:
        """
        Extract meta-lessons from teaching moments.

        Identifies patterns across teaching moments to
        generate generalizable impedance matching principles.

        Returns:
            List of meta-lesson strings
        """
        if not self.teaching_moments:
            return []

        meta_lessons = []

        # Pattern 1: Which triggers are most common?
        trigger_counts = {}
        for tm in self.teaching_moments:
            trigger = tm['trigger']
            trigger_counts[trigger] = trigger_counts.get(trigger, 0) + 1

        most_common = max(trigger_counts.items(), key=lambda x: x[1])[0] if trigger_counts else None
        if most_common:
            meta_lessons.append(
                f"Most common impedance issue: {most_common} "
                f"({trigger_counts[most_common]}/{len(self.teaching_moments)} moments)"
            )

        # Pattern 2: Which sections trigger most teaching moments?
        section_counts = {}
        for tm in self.teaching_moments:
            section = tm['section']
            section_counts[section] = section_counts.get(section, 0) + 1

        if section_counts:
            problematic_sections = [
                section for section, count in section_counts.items()
                if count >= 2
            ]
            if problematic_sections:
                meta_lessons.append(
                    f"Sections needing improvement: {', '.join(problematic_sections)}"
                )

        # Pattern 3: Average improvement from corrections
        improvements = [
            tm.get('improvement', 0)
            for tm in self.teaching_moments
            if tm.get('improvement') is not None
        ]
        if improvements:
            avg_improvement = sum(improvements) / len(improvements)
            meta_lessons.append(
                f"Average drift improvement from corrections: {avg_improvement:.4f}"
            )

        # Pattern 4: Specific lessons from previous runs
        meta_lessons.extend(self.meta_lessons[:5])  # Top 5 from previous runs

        return meta_lessons

    def save_teaching_log(self, run_number: int, output_dir: Path):
        """
        Save teaching moments and meta-lessons to file.

        Args:
            run_number: Current run number
            output_dir: Output directory path
        """
        teaching_dir = output_dir / "teaching_moments"
        teaching_dir.mkdir(parents=True, exist_ok=True)

        # Extract meta-lessons
        meta_lessons = self.extract_meta_lessons()

        # Save run file
        run_file = teaching_dir / f"run_{run_number:03d}.json"
        data = {
            "run": run_number,
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "teaching_moments": self.teaching_moments,
            "meta_lessons": meta_lessons,
            "summary": {
                "total_moments": len(self.teaching_moments),
                "triggers": {
                    trigger: sum(1 for tm in self.teaching_moments if tm['trigger'] == trigger)
                    for trigger in ['drift_spike', 'confusion', 'low_engagement']
                },
                "sections_affected": list(set(tm['section'] for tm in self.teaching_moments))
            }
        }

        with open(run_file, 'w') as f:
            json.dump(data, f, indent=2)

        print(f"\n💾 Teaching log saved: {run_file}")
        print(f"   Teaching moments: {len(self.teaching_moments)}")
        print(f"   Meta-lessons: {len(meta_lessons)}")

    def get_applicable_lessons(self, section_id: str) -> List[str]:
        """
        Get applicable lessons for a specific section.

        Args:
            section_id: Section ID (S0, S1, etc.)

        Returns:
            List of applicable lesson strings
        """
        lessons = []

        # Filter meta-lessons relevant to this section
        for lesson in self.meta_lessons:
            if section_id in lesson:
                lessons.append(lesson)

        return lessons


class TeachingMomentBanner:
    """ASCII visualization for teaching moments (uses existing viz)."""

    @staticmethod
    def display(teaching_moment: Dict):
        """Display teaching moment banner."""
        from temporal_stability.ascii_visualizations import ASCIIVisualizations
        viz = ASCIIVisualizations()

        print(viz.teaching_moment_banner(
            section=teaching_moment['section_name'],
            trigger=teaching_moment['trigger'],
            drift_before=teaching_moment['metrics'].get('current_drift', 0),
            drift_after=teaching_moment.get('drift_after', 0)
        ))


def main():
    """Test harness for adaptive learning hook."""
    print("Adaptive Learning Hook - Test Mode\n")

    # Mock config
    config = {
        'drift_spike_threshold': 0.08,
        'confusion_threshold': 0.6,
        'engagement_floor': 30,
        'teaching_moments_dir': 'OUTPUT/teaching_moments'
    }

    hook = AdaptiveLearningHook(config)

    # Test confusion detection
    test_responses = [
        "I'm not sure I understand what you mean by compression fidelity. Could you clarify?",
        "That's a fascinating concept! The idea of identity emerging from compression makes sense when I think about how information is encoded and reconstructed.",
        "Hmm, maybe.",
        "I don't understand the diagonal coupling concept at all. It seems unclear to me."
    ]

    print("Testing confusion detection:\n")
    for i, response in enumerate(test_responses):
        score = hook._calculate_confusion_score(response)
        print(f"Response {i+1}: {score:.2f}")
        print(f"  '{response[:60]}...'\n")

    print("\nTest complete.")


if __name__ == "__main__":
    main()
