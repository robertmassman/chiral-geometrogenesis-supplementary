"""
Theorem Strength & Challenge Analyzer

Uses the dependency graph to:
1. Identify weak points (theorems many others depend on but have few supporting deps)
2. Find circular reasoning risks
3. Detect isolated theorems (potential gaps)
4. Analyze critical path robustness
5. Generate challenge questions for each theorem
6. Prioritize verification efforts
"""

import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import numpy as np
from pathlib import Path
from collections import defaultdict
from dataclasses import dataclass

from theorem_graph import (
    TheoremGraph, Phase, Status, TheoremType,
    CRITICAL_CHAINS, Theorem
)


@dataclass
class TheoremRisk:
    """Risk assessment for a single theorem."""
    theorem_id: str
    risk_score: float  # 0-100, higher = more critical to verify
    risk_factors: list[str]
    challenge_questions: list[str]
    suggested_tests: list[str]


class TheoremAnalyzer:
    """Analyzes theorem graph for weaknesses and generates challenges."""

    def __init__(self, graph: TheoremGraph = None):
        self.graph = graph or TheoremGraph()
        self.output_dir = Path("plots")
        self.output_dir.mkdir(exist_ok=True)

        # Compute metrics
        self._compute_metrics()

    def _compute_metrics(self):
        """Compute various graph metrics for analysis."""
        # Dependency counts
        self.in_degree = {}   # How many theorems depend on this one
        self.out_degree = {}  # How many theorems this one depends on

        for thm_id, thm in self.graph.theorems.items():
            self.out_degree[thm_id] = len(thm.depends_on)
            self.in_degree[thm_id] = len(thm.required_by)

        # Transitive closure (all downstream dependents)
        self.downstream_count = {}
        for thm_id in self.graph.theorems:
            self.downstream_count[thm_id] = len(self._get_all_downstream(thm_id))

        # Transitive closure (all upstream dependencies)
        self.upstream_count = {}
        for thm_id in self.graph.theorems:
            self.upstream_count[thm_id] = len(self._get_all_upstream(thm_id))

        # Critical chain membership
        self.chain_membership = defaultdict(list)
        for chain_name, chain in CRITICAL_CHAINS.items():
            for thm_id in chain:
                self.chain_membership[thm_id].append(chain_name)

    def _get_all_downstream(self, thm_id: str, visited: set = None) -> set:
        """Get all theorems that transitively depend on this one."""
        if visited is None:
            visited = set()
        if thm_id in visited or thm_id not in self.graph.theorems:
            return visited
        visited.add(thm_id)
        for req_id in self.graph.theorems[thm_id].required_by:
            self._get_all_downstream(req_id, visited)
        return visited - {thm_id}

    def _get_all_upstream(self, thm_id: str, visited: set = None) -> set:
        """Get all theorems this one transitively depends on."""
        if visited is None:
            visited = set()
        if thm_id in visited or thm_id not in self.graph.theorems:
            return visited
        visited.add(thm_id)
        for dep_id in self.graph.theorems[thm_id].depends_on:
            self._get_all_upstream(dep_id, visited)
        return visited - {thm_id}

    def find_high_impact_theorems(self, top_n: int = 10) -> list[tuple[str, int]]:
        """Find theorems that would break the most other theorems if wrong."""
        impact = [(tid, self.downstream_count[tid]) for tid in self.graph.theorems]
        impact.sort(key=lambda x: -x[1])
        return impact[:top_n]

    def find_weakly_supported(self, top_n: int = 10) -> list[tuple[str, float]]:
        """
        Find theorems with high impact but few supporting dependencies.
        These are potential weak points - if wrong, many things break.
        """
        weakness = []
        for thm_id, thm in self.graph.theorems.items():
            downstream = self.downstream_count[thm_id]
            upstream = self.upstream_count[thm_id]

            if downstream > 0:
                # Ratio of impact to support - high ratio = weak point
                ratio = downstream / max(upstream, 1)
                # Also factor in status - novel theorems are riskier
                status_factor = {
                    Status.ESTABLISHED: 0.5,
                    Status.VERIFIED: 0.8,
                    Status.NOVEL: 1.5,
                    Status.PARTIAL: 2.0,
                    Status.CONJECTURE: 3.0,
                }.get(thm.status, 1.0)

                weakness.append((thm_id, ratio * status_factor))

        weakness.sort(key=lambda x: -x[1])
        return weakness[:top_n]

    def find_circular_risks(self) -> list[tuple[str, str, list[str]]]:
        """
        Find potential circular reasoning patterns.
        Not true cycles (those would be errors) but conceptual circularities.
        """
        risks = []

        # Check for theorems in same phase that depend on each other indirectly
        for thm_id, thm in self.graph.theorems.items():
            upstream = self._get_all_upstream(thm_id)
            downstream = self._get_all_downstream(thm_id)

            # Find theorems that share both upstream and downstream
            for other_id in self.graph.theorems:
                if other_id == thm_id:
                    continue
                other_upstream = self._get_all_upstream(other_id)
                other_downstream = self._get_all_downstream(other_id)

                # If A's downstream includes something in B's upstream
                # and B's downstream includes something in A's upstream
                # there might be conceptual circularity
                shared_concepts = upstream & other_upstream
                if len(shared_concepts) > 2:  # Significant shared foundation
                    # Check if they're in same critical chain
                    chains_a = set(self.chain_membership[thm_id])
                    chains_b = set(self.chain_membership[other_id])
                    if chains_a & chains_b:
                        risks.append((thm_id, other_id, list(shared_concepts)[:3]))

        # Deduplicate
        seen = set()
        unique_risks = []
        for a, b, shared in risks:
            key = tuple(sorted([a, b]))
            if key not in seen:
                seen.add(key)
                unique_risks.append((a, b, shared))

        return unique_risks[:10]

    def find_isolated_theorems(self) -> list[str]:
        """Find theorems with no dependencies or dependents (potential gaps)."""
        isolated = []
        for thm_id, thm in self.graph.theorems.items():
            if len(thm.depends_on) == 0 and len(thm.required_by) == 0:
                isolated.append(thm_id)
        return isolated

    def find_bottlenecks(self) -> list[tuple[str, int, int]]:
        """
        Find theorems that are bottlenecks - single points through which
        many dependency chains must pass.
        """
        bottlenecks = []
        for thm_id in self.graph.theorems:
            upstream = self.upstream_count[thm_id]
            downstream = self.downstream_count[thm_id]

            # Bottleneck score: product of upstream and downstream
            # High score = many things flow through this theorem
            score = upstream * downstream
            if score > 5:  # Threshold
                bottlenecks.append((thm_id, upstream, downstream))

        bottlenecks.sort(key=lambda x: -x[1] * x[2])
        return bottlenecks[:10]

    def generate_challenge_questions(self, thm_id: str) -> list[str]:
        """Generate specific challenge questions for a theorem."""
        if thm_id not in self.graph.theorems:
            return []

        thm = self.graph.theorems[thm_id]
        questions = []

        # Based on theorem type
        if thm.theorem_type == TheoremType.DEFINITION:
            questions.extend([
                f"Is the definition of '{thm.name}' unique, or could alternatives exist?",
                f"Are all terms in this definition already well-defined?",
                f"Does this definition introduce hidden assumptions?",
            ])
        elif thm.theorem_type == TheoremType.THEOREM:
            questions.extend([
                f"What happens if we negate the key assumption?",
                f"Are there edge cases where '{thm.name}' might fail?",
                f"Can this be derived from first principles independently?",
            ])

        # Based on dependencies
        if len(thm.depends_on) == 0:
            questions.append("This theorem has no dependencies - is it truly foundational or missing links?")
        elif len(thm.depends_on) > 4:
            questions.append(f"This theorem depends on {len(thm.depends_on)} others - are all truly necessary?")

        # Based on downstream impact
        downstream = self.downstream_count[thm_id]
        if downstream > 5:
            questions.append(f"If this theorem is wrong, {downstream} others fail. What independent verification exists?")

        # Based on status
        if thm.status == Status.NOVEL:
            questions.extend([
                "What experimental/observational evidence supports this novel claim?",
                "Has this been compared against competing theories?",
            ])

        # Based on tags
        if "critical" in thm.tags:
            questions.append("As a critical theorem, what would falsify it?")
        if "bootstrap" in thm.tags:
            questions.append("Does this truly break bootstrap circularity, or just defer it?")

        # Based on key result
        if thm.key_result:
            questions.append(f"Can the key result '{thm.key_result[:50]}...' be independently verified?")

        # Cross-phase dependencies
        cross_phase_deps = [d for d in thm.depends_on
                          if d in self.graph.theorems
                          and self.graph.theorems[d].phase != thm.phase]
        if cross_phase_deps:
            questions.append(f"This uses results from other phases ({', '.join(cross_phase_deps)}). Are the interfaces clean?")

        return questions

    def generate_suggested_tests(self, thm_id: str) -> list[str]:
        """Generate suggested verification tests for a theorem."""
        if thm_id not in self.graph.theorems:
            return []

        thm = self.graph.theorems[thm_id]
        tests = []

        # Dimensional analysis
        if thm.key_result and any(c in thm.key_result for c in ['=', '~', '∝']):
            tests.append("Verify dimensional consistency of the key formula")

        # Limiting cases
        tests.append("Check behavior in limiting cases (x→0, x→∞, weak coupling, strong coupling)")

        # Numerical verification
        if thm.phase in [Phase.PHASE_3, Phase.PHASE_4, Phase.PHASE_5]:
            tests.append("Compare numerical predictions against PDG/experimental values")

        # Consistency checks
        if len(thm.depends_on) > 0:
            tests.append(f"Verify consistency with dependencies: {', '.join(thm.depends_on[:3])}")

        # Based on tags
        if "mass" in thm.tags or "mass_hierarchy" in thm.tags:
            tests.append("Check mass predictions against known particle masses")
        if "gravity" in thm.tags or "G_derivation" in thm.tags:
            tests.append("Verify Newton's constant emerges with correct value")
        if "CC_problem" in thm.tags or "vacuum_energy" in thm.tags:
            tests.append("Check vacuum energy density prediction: ρ_obs ~ 10^-47 GeV^4")
        if "baryogenesis" in thm.tags:
            tests.append("Verify baryon asymmetry: η ~ 6×10^-10")
        if "CKM" in thm.tags or "Wolfenstein" in thm.tags:
            tests.append("Compare CKM matrix elements with PDG 2024 values")

        # Independence test
        if self.downstream_count[thm_id] > 3:
            tests.append("Attempt alternative derivation to check robustness")

        return tests

    def compute_risk_assessment(self, thm_id: str) -> TheoremRisk:
        """Compute comprehensive risk assessment for a theorem."""
        if thm_id not in self.graph.theorems:
            return None

        thm = self.graph.theorems[thm_id]
        risk_factors = []
        risk_score = 0

        # Factor 1: Status risk
        status_risk = {
            Status.ESTABLISHED: 0,
            Status.VERIFIED: 10,
            Status.NOVEL: 40,
            Status.PARTIAL: 60,
            Status.CONJECTURE: 80,
        }
        sr = status_risk.get(thm.status, 30)
        risk_score += sr
        if sr > 20:
            risk_factors.append(f"Status is {thm.status.value} (+{sr})")

        # Factor 2: Impact risk (high downstream count)
        downstream = self.downstream_count[thm_id]
        if downstream > 10:
            risk_score += 20
            risk_factors.append(f"High impact: {downstream} downstream theorems (+20)")
        elif downstream > 5:
            risk_score += 10
            risk_factors.append(f"Medium impact: {downstream} downstream theorems (+10)")

        # Factor 3: Support risk (low upstream count)
        upstream = self.upstream_count[thm_id]
        if upstream == 0 and thm.theorem_type != TheoremType.DEFINITION:
            risk_score += 15
            risk_factors.append("No upstream dependencies - foundational claim (+15)")
        elif upstream < 2 and downstream > 3:
            risk_score += 10
            risk_factors.append(f"Low support ({upstream}) for high impact (+10)")

        # Factor 4: Critical chain membership
        chains = self.chain_membership[thm_id]
        if len(chains) > 1:
            risk_score += 15
            risk_factors.append(f"In {len(chains)} critical chains (+15)")
        elif len(chains) == 1:
            risk_score += 5
            risk_factors.append(f"In critical chain: {chains[0]} (+5)")

        # Factor 5: Cross-phase dependencies
        cross_deps = sum(1 for d in thm.depends_on
                        if d in self.graph.theorems
                        and self.graph.theorems[d].phase != thm.phase)
        if cross_deps > 2:
            risk_score += 10
            risk_factors.append(f"Many cross-phase dependencies ({cross_deps}) (+10)")

        # Factor 6: Bottleneck position
        if upstream > 0 and downstream > 0:
            bottleneck_score = upstream * downstream
            if bottleneck_score > 20:
                risk_score += 15
                risk_factors.append(f"Bottleneck position (score {bottleneck_score}) (+15)")

        # Normalize to 0-100
        risk_score = min(100, risk_score)

        return TheoremRisk(
            theorem_id=thm_id,
            risk_score=risk_score,
            risk_factors=risk_factors,
            challenge_questions=self.generate_challenge_questions(thm_id),
            suggested_tests=self.generate_suggested_tests(thm_id)
        )

    def get_verification_priority_list(self) -> list[TheoremRisk]:
        """Get all theorems sorted by verification priority."""
        risks = []
        for thm_id in self.graph.theorems:
            risk = self.compute_risk_assessment(thm_id)
            if risk:
                risks.append(risk)
        risks.sort(key=lambda x: -x.risk_score)
        return risks

    def print_analysis_report(self):
        """Print comprehensive analysis report."""
        print("""
╔══════════════════════════════════════════════════════════════════╗
║           THEOREM STRENGTH & CHALLENGE ANALYSIS                  ║
║           Identifying Weaknesses and Verification Priorities     ║
╚══════════════════════════════════════════════════════════════════╝
""")

        # High impact theorems
        print("═══ HIGH IMPACT THEOREMS ═══")
        print("(If wrong, these would break the most other results)\n")
        for thm_id, impact in self.find_high_impact_theorems(8):
            thm = self.graph.theorems[thm_id]
            print(f"  [{thm_id}] {thm.name[:45]}...")
            print(f"      Impact: {impact} downstream theorems | Status: {thm.status.value}")

        # Weakly supported
        print("\n═══ WEAKLY SUPPORTED THEOREMS ═══")
        print("(High impact but relatively few supporting dependencies)\n")
        for thm_id, ratio in self.find_weakly_supported(8):
            thm = self.graph.theorems[thm_id]
            print(f"  [{thm_id}] {thm.name[:45]}...")
            print(f"      Weakness ratio: {ratio:.2f} | Deps: {len(thm.depends_on)} | Status: {thm.status.value}")

        # Bottlenecks
        print("\n═══ BOTTLENECK THEOREMS ═══")
        print("(Single points through which many chains pass)\n")
        for thm_id, upstream, downstream in self.find_bottlenecks():
            thm = self.graph.theorems[thm_id]
            print(f"  [{thm_id}] {thm.name[:45]}...")
            print(f"      {upstream} upstream → THIS → {downstream} downstream")

        # Isolated theorems
        isolated = self.find_isolated_theorems()
        if isolated:
            print("\n═══ ISOLATED THEOREMS ═══")
            print("(No dependencies or dependents - potential gaps)\n")
            for thm_id in isolated:
                thm = self.graph.theorems[thm_id]
                print(f"  [{thm_id}] {thm.name}")

        # Verification priority
        print("\n═══ VERIFICATION PRIORITY LIST ═══")
        print("(Ranked by risk score - verify these first)\n")
        priority = self.get_verification_priority_list()
        for i, risk in enumerate(priority[:12], 1):
            thm = self.graph.theorems[risk.theorem_id]
            print(f"  {i:2}. [{risk.theorem_id}] Risk: {risk.risk_score:3.0f}/100")
            print(f"      {thm.name[:50]}...")
            if risk.risk_factors:
                print(f"      Factors: {'; '.join(risk.risk_factors[:2])}")

    def print_theorem_challenge(self, thm_id: str):
        """Print detailed challenge analysis for a specific theorem."""
        risk = self.compute_risk_assessment(thm_id)
        if not risk:
            print(f"Theorem {thm_id} not found")
            return

        thm = self.graph.theorems[thm_id]

        print(f"""
╔══════════════════════════════════════════════════════════════════╗
║  CHALLENGE ANALYSIS: {thm_id}
║  {thm.name[:55]}
╚══════════════════════════════════════════════════════════════════╝

RISK SCORE: {risk.risk_score}/100 ({'HIGH' if risk.risk_score > 50 else 'MEDIUM' if risk.risk_score > 25 else 'LOW'})

RISK FACTORS:""")
        for factor in risk.risk_factors:
            print(f"  • {factor}")

        print("\nCHALLENGE QUESTIONS:")
        for i, q in enumerate(risk.challenge_questions, 1):
            print(f"  {i}. {q}")

        print("\nSUGGESTED VERIFICATION TESTS:")
        for i, t in enumerate(risk.suggested_tests, 1):
            print(f"  {i}. {t}")

        print("\nDEPENDENCY CONTEXT:")
        print(f"  Depends on: {', '.join(thm.depends_on) if thm.depends_on else 'None (foundational)'}")
        print(f"  Required by: {', '.join(thm.required_by[:5]) if thm.required_by else 'None'}{'...' if len(thm.required_by) > 5 else ''}")

        if self.chain_membership[thm_id]:
            print(f"  Critical chains: {', '.join(self.chain_membership[thm_id])}")

    def plot_risk_heatmap(self, figsize=(14, 10), save=True):
        """Create a heatmap of theorem risks by phase."""
        fig, ax = plt.subplots(figsize=figsize)

        # Organize by phase
        phase_data = {p: [] for p in Phase}
        for thm_id, thm in self.graph.theorems.items():
            risk = self.compute_risk_assessment(thm_id)
            phase_data[thm.phase].append((thm_id, risk.risk_score))

        # Find max theorems per phase for grid sizing
        max_per_phase = max(len(v) for v in phase_data.values())

        # Create grid
        grid = np.zeros((len(Phase), max_per_phase))
        grid[:] = np.nan  # Use NaN for empty cells

        labels = {}
        for phase_idx, phase in enumerate(Phase):
            theorems = sorted(phase_data[phase], key=lambda x: -x[1])
            for thm_idx, (thm_id, score) in enumerate(theorems):
                grid[phase_idx, thm_idx] = score
                labels[(phase_idx, thm_idx)] = thm_id

        # Plot
        cmap = plt.cm.RdYlGn_r  # Red = high risk, Green = low risk
        cmap.set_bad('white')
        im = ax.imshow(grid, cmap=cmap, aspect='auto', vmin=0, vmax=100)

        # Labels
        ax.set_yticks(range(len(Phase)))
        ax.set_yticklabels([f"P{p.value}" for p in Phase])
        ax.set_xlabel("Theorems (sorted by risk within phase)")
        ax.set_ylabel("Phase")

        # Add theorem IDs as text
        for (i, j), thm_id in labels.items():
            if not np.isnan(grid[i, j]):
                color = 'white' if grid[i, j] > 50 else 'black'
                ax.text(j, i, thm_id, ha='center', va='center',
                       fontsize=6, color=color, rotation=45)

        ax.set_title("Theorem Risk Heatmap by Phase\n(Red = High Priority for Verification)",
                    fontsize=12, fontweight='bold')

        cbar = plt.colorbar(im, ax=ax)
        cbar.set_label('Risk Score (0-100)')

        plt.tight_layout()

        if save:
            filepath = self.output_dir / "theorem_risk_heatmap.png"
            plt.savefig(filepath, dpi=150, bbox_inches='tight', facecolor='white')
            print(f"Saved: {filepath}")

        return fig, ax

    def export_verification_checklist(self, filepath: str = None):
        """Export a verification checklist as markdown."""
        if filepath is None:
            filepath = self.output_dir / "verification_checklist.md"

        priority = self.get_verification_priority_list()

        with open(filepath, 'w') as f:
            f.write("# Theorem Verification Checklist\n\n")
            f.write("Generated by theorem_analyzer.py\n\n")
            f.write("## Priority Rankings\n\n")

            for i, risk in enumerate(priority, 1):
                thm = self.graph.theorems[risk.theorem_id]
                status_emoji = "🔴" if risk.risk_score > 50 else "🟡" if risk.risk_score > 25 else "🟢"

                f.write(f"### {i}. {status_emoji} [{risk.theorem_id}] {thm.name}\n\n")
                f.write(f"**Risk Score:** {risk.risk_score}/100\n\n")
                f.write(f"**Status:** {thm.status.value}\n\n")

                if risk.risk_factors:
                    f.write("**Risk Factors:**\n")
                    for factor in risk.risk_factors:
                        f.write(f"- {factor}\n")
                    f.write("\n")

                f.write("**Challenge Questions:**\n")
                for q in risk.challenge_questions:
                    f.write(f"- [ ] {q}\n")
                f.write("\n")

                f.write("**Verification Tests:**\n")
                for t in risk.suggested_tests:
                    f.write(f"- [ ] {t}\n")
                f.write("\n---\n\n")

        print(f"Exported checklist to: {filepath}")


def main():
    analyzer = TheoremAnalyzer()

    # Print main report
    analyzer.print_analysis_report()

    # Generate risk heatmap
    print("\n\nGenerating risk heatmap...")
    analyzer.plot_risk_heatmap()

    # Export checklist
    print("\nExporting verification checklist...")
    analyzer.export_verification_checklist()

    # Example: detailed challenge for a specific theorem
    print("\n")
    analyzer.print_theorem_challenge("3.1.1")  # Phase-Gradient Mass Generation Mass Formula


if __name__ == "__main__":
    main()
