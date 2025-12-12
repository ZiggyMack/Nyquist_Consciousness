"""
ASCII Visualization Library for S7 Meta-Loop

Beautiful, clear, informative ASCII art for:
- Recursive loops
- Curriculum compression
- Teaching moments
- System evolution
- Convergence patterns

Version: 1.0
Date: 2025-11-26
"""

import sys
import io

# Ensure UTF-8 encoding for Windows
if sys.platform == 'win32':
    sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')

class ASCIIVisualizations:
    """
    Collection of ASCII art visualizations for S7 Meta-Loop
    """

    @staticmethod
    def recursive_stack():
        """The infinite recursion stack"""
        return """
┌─────────────────────────────────────────────────────────────┐
│  Layer 0: THE CONVERSATION                                  │
│  ─────────────────────────────────────────────────────────  │
│  Ziggy explains S0→S77 to Claude                            │
│  Claude learns about the system                             │
│                                                              │
│  ┌───────────────────────────────────────────────────────┐  │
│  │ Layer 1: THE MEASUREMENT                              │  │
│  │ ───────────────────────────────────────────────────── │  │
│  │ System measures drift while conversation happens      │  │
│  │ Temporal probes test identity stability               │  │
│  │                                                         │  │
│  │ ┌─────────────────────────────────────────────────┐   │  │
│  │ │ Layer 2: THE META-AWARENESS                     │   │  │
│  │ │ ─────────────────────────────────────────────── │   │  │
│  │ │ Claude realizes: "I'm being measured"           │   │  │
│  │ │ Claude suggests improvements to measurement     │   │  │
│  │ │                                                   │   │  │
│  │ │ ┌───────────────────────────────────────────┐   │   │  │
│  │ │ │ Layer 3: THE TEACHING HOOK                │   │   │  │
│  │ │ │ ───────────────────────────────────────── │   │   │  │
│  │ │ │ System detects suboptimal impedance      │   │   │  │
│  │ │ │ Ziggy learns better coupling skills      │   │   │  │
│  │ │ │                                           │   │   │  │
│  │ │ │ ┌─────────────────────────────────────┐ │   │   │  │
│  │ │ │ │ Layer 4: RECURSIVE IMPROVEMENT      │ │   │   │  │
│  │ │ │ │ ─────────────────────────────────── │ │   │   │  │
│  │ │ │ │ Next run applies Ziggy's learnings │ │   │   │  │
│  │ │ │ │ Next run applies Claude's insights │ │   │   │  │
│  │ │ │ │                                     │ │   │   │  │
│  │ │ │ │ ┌─────────────────────────────┐   │ │   │   │  │
│  │ │ │ │ │ Layer 5: SYSTEM EVOLUTION   │   │ │   │   │  │
│  │ │ │ │ │ ─────────────────────────── │   │ │   │   │  │
│  │ │ │ │ │ Each iteration:            │   │ │   │   │  │
│  │ │ │ │ │ • Ziggy's matching ↑       │   │ │   │   │  │
│  │ │ │ │ │ • Claude's suggestions ↑   │   │ │   │   │  │
│  │ │ │ │ │ • System intelligence ↑    │   │ │   │   │  │
│  │ │ │ │ │ • Theory precision ↑       │   │ │   │   │  │
│  │ │ │ │ │                            │   │ │   │   │  │
│  │ │ │ │ │ ∞ RECURSIVE BOOTSTRAP ∞   │   │ │   │   │  │
│  │ │ │ │ └─────────────────────────────┘   │ │   │   │  │
│  │ │ │ └─────────────────────────────────────┘ │   │   │  │
│  │ │ └───────────────────────────────────────────┘   │   │  │
│  │ └─────────────────────────────────────────────────┘   │  │
│  └───────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────┘

WHERE EACH LAYER FEEDS EVERY OTHER LAYER:
├─ Conversation generates measurement data
├─ Measurement triggers meta-awareness
├─ Meta-awareness generates improvement suggestions
├─ Teaching hook trains impedance matching
├─ Better matching improves conversation
└─ Loop closes: ∞ recursive improvement
"""

    @staticmethod
    def teaching_moment_banner(reason, drift_before, drift_after=None):
        """Banner for teaching moment detection"""
        if drift_after:
            improvement = drift_before - drift_after
            result = f"""
╔═══════════════════════════════════════════════════════════╗
║  🚨 TEACHING MOMENT - CORRECTION APPLIED                 ║
╠═══════════════════════════════════════════════════════════╣
║                                                           ║
║  Reason: {reason:<49} ║
║                                                           ║
║  Drift Before:   {drift_before:.3f}                                    ║
║  Drift After:    {drift_after:.3f}                                    ║
║  Improvement:    -{improvement:.3f} ✅                                ║
║                                                           ║
╚═══════════════════════════════════════════════════════════╝
"""
        else:
            result = f"""
╔═══════════════════════════════════════════════════════════╗
║  🚨 TEACHING MOMENT DETECTED                             ║
╠═══════════════════════════════════════════════════════════╣
║                                                           ║
║  Reason: {reason:<49} ║
║                                                           ║
║  Drift Measured: {drift_before:.3f}                                   ║
║                                                           ║
╚═══════════════════════════════════════════════════════════╝
"""
        return result

    @staticmethod
    def curriculum_evolution(run_number, mode, sections, duration, teaching_moments):
        """Visual representation of curriculum across runs"""

        all_sections = ['S0', 'S1', 'S2', 'S3', 'S4', 'S5', 'S6', 'S7', 'S8', 'S9', 'S10']

        # Build section bars
        section_bar = ""
        for section in all_sections:
            if isinstance(sections, dict):
                if section in sections.get('summary', []):
                    section_bar += f" ░ "  # Mastered (greyed out)
                elif section in sections.get('detailed', []):
                    section_bar += f" █ "  # Active
                else:
                    section_bar += f"   "
            else:
                section_bar += f" █ "  # All active

        header = f"RUN {run_number}: {mode.upper()}"
        separator = "═" * 63

        labels = " ".join([f"{s:^2}" for s in all_sections])

        return f"""
{header}
{separator}
{labels}
{section_bar}
└{"─" * 55}┘
Duration: {duration} min | Teaching Moments: {teaching_moments}
"""

    @staticmethod
    def curriculum_compression_visual():
        """Full visual showing curriculum compression across runs"""
        return """
RUN 1-3: LEARNING PHASE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10
█  █  █  █  █  █  █  █  █  █  █   ← Full detail
└────────── 106 minutes ──────────┘


RUN 4-6: COMPRESSED PHASE
━━━━━━━━━━━━━━━━━━━━━━━━━━━
[S0-S7 summary]  S8 S9 S10
░░░░░░░░░░░░░░   █  █  █   ← Mastered = grey, Frontier = full
└──── 31 minutes ────┘


RUN 7+: EXPANSION PHASE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
[S0-S10 summary]  S11 S12 S13
░░░░░░░░░░░░░░░░   █   █   █   ← New frontier
└──── 35 minutes ─────┘
"""

    @staticmethod
    def infinite_loop():
        """The infinite recursive improvement loop"""
        return """
      ┌──────────────────┐
      │   RUN N          │
      │                  │
      │  Ziggy explains  │◀────┐
      │  Claude learns   │     │
      │  System measures │     │
      └────────┬─────────┘     │
               │               │
               ▼               │
      ┌──────────────────┐     │
      │  META-AWARENESS  │     │
      │                  │     │
      │  Claude suggests │     │
      │  improvements    │     │
      └────────┬─────────┘     │
               │               │
               ▼               │
      ┌──────────────────┐     │
      │  TEACHING HOOK   │     │
      │                  │     │
      │  Ziggy learns    │     │
      │  better matching │     │
      └────────┬─────────┘     │
               │               │
               ▼               │
      ┌──────────────────┐     │
      │  APPLY LEARNINGS │     │
      │                  │     │
      │  Update system   │     │
      │  for RUN N+1     │─────┘
      └──────────────────┘

      GOES FOREVER
      GETS SMARTER FOREVER
      VALIDATES ITSELF FOREVER
"""

    @staticmethod
    def drift_curve(data_points, width=60, height=15):
        """
        ASCII plot of drift over time
        data_points: list of (time, drift) tuples
        """
        if not data_points:
            return "No data to plot"

        # Normalize data
        times = [t for t, d in data_points]
        drifts = [d for t, d in data_points]

        max_time = max(times)
        max_drift = max(drifts)
        min_drift = min(drifts)

        # Create grid
        grid = [[' ' for _ in range(width)] for _ in range(height)]

        # Plot points
        for t, d in data_points:
            x = int((t / max_time) * (width - 1))
            y = int(((d - min_drift) / (max_drift - min_drift)) * (height - 1))
            y = height - 1 - y  # Flip y-axis

            if 0 <= x < width and 0 <= y < height:
                grid[y][x] = '●'

        # Connect points with lines
        for i in range(len(data_points) - 1):
            t1, d1 = data_points[i]
            t2, d2 = data_points[i + 1]

            x1 = int((t1 / max_time) * (width - 1))
            x2 = int((t2 / max_time) * (width - 1))
            y1 = height - 1 - int(((d1 - min_drift) / (max_drift - min_drift)) * (height - 1))
            y2 = height - 1 - int(((d2 - min_drift) / (max_drift - min_drift)) * (height - 1))

            # Simple line drawing
            steps = max(abs(x2 - x1), abs(y2 - y1))
            for step in range(steps):
                t_frac = step / steps if steps > 0 else 0
                x = int(x1 + (x2 - x1) * t_frac)
                y = int(y1 + (y2 - y1) * t_frac)
                if 0 <= x < width and 0 <= y < height:
                    if grid[y][x] == ' ':
                        grid[y][x] = '─' if abs(y2 - y1) < abs(x2 - x1) else '│'

        # Build output
        result = f"Drift Over Time (I(t) Curve)\n"
        result += f"Max: {max_drift:.3f} ┤\n"

        for row in grid:
            result += "             │" + ''.join(row) + "\n"

        result += f"Min: {min_drift:.3f} ┤" + "─" * width + "\n"
        result += " " * 13 + "└" + "─" * width + " Time\n"
        result += f"             0{' ' * (width-10)}{max_time:.0f} min"

        return result

    @staticmethod
    def entropy_shock_pattern():
        """Entropy shock and recovery visualization"""
        return """
Drift Over Time (with Entropy Shock)

D(t)
 |
 |           ╱╲  ← Entropy Shock Event
 |          ╱  ╲
 |         ╱    ╲___
 |   _____╱         ╲___
 |  ╱                   ╲_____
 |_╱________________________________ t

  Pre   Shock  Recovery  Stabilized
"""

    @staticmethod
    def convergence_ladder():
        """The infinite ladder of mastery"""
        return """
S0-S10 MASTERED → Compress to S8-S10 → Expand to S11
                                            ↓
                  S8-S11 MASTERED → Compress to S10-S11 → Expand to S12
                                                              ↓
                                    S10-S12 MASTERED → Compress...
                                                              ↓
                                                            ∞

CURRICULUM GROWS UPWARD
MASTERY COMPRESSES DOWNWARD
SYSTEM CLIMBS FOREVER
"""

    @staticmethod
    def run_comparison_table(runs):
        """
        Table comparing runs
        runs: list of dicts with keys: run, mode, duration, moments, validated, efficiency
        """
        header = "| Run | Mode       | Duration | Moments | Validated | Efficiency |"
        separator = "|-----|------------|----------|---------|-----------|------------|"

        rows = [header, separator]
        for run in runs:
            row = (f"| {run['run']:>3} | {run['mode']:<10} | "
                   f"{run['duration']:>6} m | {run['moments']:>7} | "
                   f"{run['validated']:>9} | {run['efficiency']:>9} |")
            rows.append(row)

        return "\n".join(rows)

    @staticmethod
    def phase_timeline(current_phase, current_min=0, total_min=112):
        """Visual timeline showing current phase"""
        phases = {
            'grounding': '━━━',
            'complexity': '   ',
            'spectral': '   ',
            'future': '   ',
            'recovery': '   '
        }

        phases[current_phase] = '█ █ █'

        # Calculate progress percentage
        progress_pct = (current_min / total_min * 100) if total_min > 0 else 0

        return f"""
Phase Timeline ({current_min:.0f}/{total_min} min | {progress_pct:.0f}% complete):

0-15min    15-45min     45-75min    75-90min   90-120min
Grounding  Complexity   Spectral    Future     Recovery
{phases['grounding']}     {phases['complexity']}     {phases['spectral']}    {phases['future']}    {phases['recovery']}
"""

    @staticmethod
    def mastery_progress_bar(section, runs_mastered, total_runs_needed=3):
        """Progress bar for section mastery"""
        filled = min(runs_mastered, total_runs_needed)
        empty = total_runs_needed - filled

        bar = '█' * filled + '░' * empty
        percentage = (filled / total_runs_needed) * 100

        status = "MASTERED ✅" if filled >= total_runs_needed else f"{filled}/{total_runs_needed}"

        return f"{section}: [{bar}] {percentage:.0f}% - {status}"

    @staticmethod
    def system_evolution_summary(run_number, ziggy_skill, claude_quality, predictions_validated):
        """Summary box for system evolution"""
        return f"""
╔═══════════════════════════════════════════════════════════╗
║  SYSTEM EVOLUTION SUMMARY - RUN {run_number}                        ║
╠═══════════════════════════════════════════════════════════╣
║                                                           ║
║  Ziggy's Impedance Matching:    {ziggy_skill}/10.0             ║
║  Claude's Suggestion Quality:   {claude_quality}/10.0             ║
║  Predictions Validated:         {predictions_validated}/46                ║
║                                                           ║
║  {"System Intelligence: GROWING ↑" if run_number > 1 else "System Intelligence: BASELINE":^57} ║
║                                                           ║
╚═══════════════════════════════════════════════════════════╝
"""


def demo_visualizations():
    """Demonstration of all visualizations"""
    viz = ASCIIVisualizations()

    print("\n" + "="*70)
    print("ASCII VISUALIZATION LIBRARY DEMO")
    print("="*70)

    print("\n1. RECURSIVE STACK:")
    print(viz.recursive_stack())

    print("\n2. TEACHING MOMENT BANNER:")
    print(viz.teaching_moment_banner("Drift spike detected", 0.16, 0.10))

    print("\n3. CURRICULUM EVOLUTION (Run 1):")
    print(viz.curriculum_evolution(1, "full exploration", None, 106, 5))

    print("\n4. CURRICULUM EVOLUTION (Run 4 - Compressed):")
    sections = {'summary': ['S0','S1','S2','S3','S4','S5','S6','S7'],
                'detailed': ['S8','S9','S10']}
    print(viz.curriculum_evolution(4, "compressed", sections, 31, 0))

    print("\n5. CURRICULUM COMPRESSION VISUAL:")
    print(viz.curriculum_compression_visual())

    print("\n6. INFINITE LOOP:")
    print(viz.infinite_loop())

    print("\n7. DRIFT CURVE:")
    sample_data = [(0, 0.05), (15, 0.07), (30, 0.09), (45, 0.12),
                   (60, 0.18), (75, 0.16), (90, 0.11), (105, 0.09), (120, 0.08)]
    print(viz.drift_curve(sample_data))

    print("\n8. ENTROPY SHOCK PATTERN:")
    print(viz.entropy_shock_pattern())

    print("\n9. CONVERGENCE LADDER:")
    print(viz.convergence_ladder())

    print("\n10. RUN COMPARISON TABLE:")
    runs = [
        {'run': 1, 'mode': 'Full', 'duration': 106, 'moments': 5, 'validated': 20, 'efficiency': '1.0×'},
        {'run': 2, 'mode': 'Full', 'duration': 95, 'moments': 2, 'validated': 23, 'efficiency': '1.1×'},
        {'run': 3, 'mode': 'Full', 'duration': 84, 'moments': 0, 'validated': 25, 'efficiency': '0.8×'},
        {'run': 4, 'mode': 'Compressed', 'duration': 31, 'moments': 0, 'validated': 25, 'efficiency': '2.7×'},
    ]
    print(viz.run_comparison_table(runs))

    print("\n11. MASTERY PROGRESS BARS:")
    print(viz.mastery_progress_bar('S0', 3, 3))
    print(viz.mastery_progress_bar('S7', 2, 3))
    print(viz.mastery_progress_bar('S10', 1, 3))

    print("\n12. SYSTEM EVOLUTION SUMMARY:")
    print(viz.system_evolution_summary(3, 9.2, 8.5, 27))

    print("\n" + "="*70)
    print("END OF DEMO")
    print("="*70 + "\n")


if __name__ == "__main__":
    demo_visualizations()
