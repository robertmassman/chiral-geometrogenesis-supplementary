"""
Phase Interaction Visualizations

Shows how theorem phases combine and affect each other:
- Cross-phase dependency flows
- Phase coupling matrix
- Information flow diagrams
- Combined phase network views
"""

import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.patches import FancyArrowPatch, FancyBboxPatch
from matplotlib.colors import LinearSegmentedColormap
import matplotlib.patheffects as pe
import networkx as nx
import numpy as np
from pathlib import Path
from collections import defaultdict

from theorem_graph import (
    TheoremGraph, Phase, Status, TheoremType,
    CRITICAL_CHAINS
)


# Color schemes
PHASE_COLORS = {
    Phase.PHASE_0: "#4CAF50",  # Green - Pre-geometric
    Phase.PHASE_1: "#2196F3",  # Blue - Foundational
    Phase.PHASE_2: "#FF9800",  # Orange - Pressure-Depression
    Phase.PHASE_3: "#E91E63",  # Pink - Mass Generation
    Phase.PHASE_4: "#9C27B0",  # Purple - Solitons
    Phase.PHASE_5: "#FFC107",  # Amber - Spacetime
}

PHASE_COLORS_LIGHT = {
    Phase.PHASE_0: "#C8E6C9",
    Phase.PHASE_1: "#BBDEFB",
    Phase.PHASE_2: "#FFE0B2",
    Phase.PHASE_3: "#F8BBD9",
    Phase.PHASE_4: "#E1BEE7",
    Phase.PHASE_5: "#FFF9C4",
}

PHASE_NAMES = {
    Phase.PHASE_0: "Phase 0\nPre-Geometric",
    Phase.PHASE_1: "Phase 1\nFoundational",
    Phase.PHASE_2: "Phase 2\nPressure-Depression",
    Phase.PHASE_3: "Phase 3\nMass Generation",
    Phase.PHASE_4: "Phase 4\nSolitons",
    Phase.PHASE_5: "Phase 5\nSpacetime & Gravity",
}

PHASE_SHORT = {
    Phase.PHASE_0: "P0: Pre-Geometric",
    Phase.PHASE_1: "P1: Foundational",
    Phase.PHASE_2: "P2: Pressure",
    Phase.PHASE_3: "P3: Mass",
    Phase.PHASE_4: "P4: Solitons",
    Phase.PHASE_5: "P5: Gravity",
}


class PhaseInteractionVisualizer:
    """Visualizes interactions between theorem phases."""

    def __init__(self, graph: TheoremGraph = None):
        self.graph = graph or TheoremGraph()
        self.output_dir = Path("plots")
        self.output_dir.mkdir(exist_ok=True)

        # Compute phase interaction data
        self._compute_interactions()

    def _compute_interactions(self):
        """Compute cross-phase dependency statistics."""
        self.phase_deps = defaultdict(lambda: defaultdict(list))  # from_phase -> to_phase -> [(from_id, to_id)]
        self.cross_phase_edges = []
        self.within_phase_edges = []

        for thm_id, thm in self.graph.theorems.items():
            for dep_id in thm.depends_on:
                if dep_id in self.graph.theorems:
                    dep_thm = self.graph.theorems[dep_id]
                    self.phase_deps[dep_thm.phase][thm.phase].append((dep_id, thm_id))

                    if dep_thm.phase != thm.phase:
                        self.cross_phase_edges.append((dep_id, thm_id))
                    else:
                        self.within_phase_edges.append((dep_id, thm_id))

    def plot_phase_flow_diagram(self, figsize=(16, 12), save=True):
        """Create a Sankey-style flow diagram showing phase interactions."""
        fig, ax = plt.subplots(figsize=figsize)
        ax.set_xlim(-1, 7)
        ax.set_ylim(-1, 6)

        # Position phases in a circular/flowing arrangement
        phase_positions = {
            Phase.PHASE_0: (0.5, 4.5),
            Phase.PHASE_1: (1.5, 2.5),
            Phase.PHASE_2: (3, 4.5),
            Phase.PHASE_3: (3, 1.5),
            Phase.PHASE_4: (5, 3),
            Phase.PHASE_5: (6, 1.5),
        }

        # Draw phase nodes
        for phase, (x, y) in phase_positions.items():
            theorems = self.graph.get_phase_theorems(phase)
            n_theorems = len(theorems)
            n_critical = len([t for t in theorems if "critical" in t.tags])

            # Draw phase box
            box = FancyBboxPatch(
                (x - 0.6, y - 0.5), 1.2, 1.0,
                boxstyle="round,pad=0.05,rounding_size=0.1",
                facecolor=PHASE_COLORS_LIGHT[phase],
                edgecolor=PHASE_COLORS[phase],
                linewidth=3
            )
            ax.add_patch(box)

            # Phase label
            ax.text(x, y + 0.2, PHASE_NAMES[phase], ha='center', va='center',
                   fontsize=9, fontweight='bold', color=PHASE_COLORS[phase])
            ax.text(x, y - 0.25, f"{n_theorems} thms", ha='center', va='center',
                   fontsize=8, color='gray')
            if n_critical > 0:
                ax.text(x, y - 0.4, f"★{n_critical} critical", ha='center', va='center',
                       fontsize=7, color='red')

        # Draw connections between phases
        for from_phase in Phase:
            for to_phase in Phase:
                edges = self.phase_deps[from_phase][to_phase]
                if edges and from_phase != to_phase:
                    n_deps = len(edges)

                    from_pos = phase_positions[from_phase]
                    to_pos = phase_positions[to_phase]

                    # Determine if this is forward or backward flow
                    is_forward = to_phase.value > from_phase.value

                    # Line width based on number of dependencies
                    lw = 1 + min(n_deps, 5) * 0.8

                    # Color based on direction
                    color = PHASE_COLORS[from_phase] if is_forward else '#E57373'
                    alpha = 0.7 if is_forward else 0.5

                    # Draw arrow
                    arrow = FancyArrowPatch(
                        from_pos, to_pos,
                        arrowstyle='-|>',
                        mutation_scale=15,
                        lw=lw,
                        color=color,
                        alpha=alpha,
                        connectionstyle='arc3,rad=0.2'
                    )
                    ax.add_patch(arrow)

                    # Label with count
                    mid_x = (from_pos[0] + to_pos[0]) / 2
                    mid_y = (from_pos[1] + to_pos[1]) / 2
                    ax.text(mid_x, mid_y, str(n_deps), fontsize=8, fontweight='bold',
                           ha='center', va='center',
                           bbox=dict(boxstyle='round', facecolor='white', alpha=0.8, edgecolor='gray'))

        ax.set_title("Phase Interaction Flow Diagram\n(Arrow thickness = dependency count)",
                    fontsize=14, fontweight='bold', pad=20)
        ax.axis('off')
        ax.set_aspect('equal')

        # Legend
        legend_elements = [
            mpatches.Patch(color=PHASE_COLORS[p], label=f"Phase {p.value}")
            for p in Phase
        ]
        ax.legend(handles=legend_elements, loc='lower left', fontsize=8)

        plt.tight_layout()

        if save:
            filepath = self.output_dir / "phase_flow_diagram.png"
            plt.savefig(filepath, dpi=150, bbox_inches='tight', facecolor='white')
            print(f"Saved: {filepath}")

        return fig, ax

    def plot_phase_coupling_matrix(self, figsize=(10, 8), save=True):
        """Create a heatmap showing how many dependencies flow between phases."""
        fig, ax = plt.subplots(figsize=figsize)

        # Build coupling matrix
        n_phases = len(Phase)
        matrix = np.zeros((n_phases, n_phases))

        for from_phase in Phase:
            for to_phase in Phase:
                edges = self.phase_deps[from_phase][to_phase]
                matrix[to_phase.value, from_phase.value] = len(edges)

        # Create heatmap
        cmap = LinearSegmentedColormap.from_list('coupling', ['white', '#4CAF50', '#2196F3', '#9C27B0'])
        im = ax.imshow(matrix, cmap=cmap, aspect='auto')

        # Labels
        phase_labels = [f"P{p.value}" for p in Phase]
        ax.set_xticks(range(n_phases))
        ax.set_yticks(range(n_phases))
        ax.set_xticklabels(phase_labels, fontsize=10)
        ax.set_yticklabels(phase_labels, fontsize=10)

        # Add value annotations
        for i in range(n_phases):
            for j in range(n_phases):
                val = int(matrix[i, j])
                if val > 0:
                    color = 'white' if val > matrix.max() / 2 else 'black'
                    ax.text(j, i, str(val), ha='center', va='center',
                           fontsize=11, fontweight='bold', color=color)

        ax.set_xlabel("Source Phase (provides dependencies)", fontsize=11)
        ax.set_ylabel("Target Phase (receives dependencies)", fontsize=11)
        ax.set_title("Phase Coupling Matrix\n(How many dependencies flow from column to row)",
                    fontsize=12, fontweight='bold')

        # Colorbar
        cbar = plt.colorbar(im, ax=ax)
        cbar.set_label('Number of Dependencies', fontsize=10)

        # Add phase name annotations on sides
        for i, phase in enumerate(Phase):
            ax.text(n_phases + 0.3, i, PHASE_SHORT[phase], va='center', fontsize=8, color='gray')
            ax.text(i, -0.8, PHASE_SHORT[phase], ha='center', fontsize=8, color='gray', rotation=45)

        plt.tight_layout()

        if save:
            filepath = self.output_dir / "phase_coupling_matrix.png"
            plt.savefig(filepath, dpi=150, bbox_inches='tight', facecolor='white')
            print(f"Saved: {filepath}")

        return fig, ax

    def plot_combined_network(self, figsize=(20, 14), save=True):
        """Create a network graph with phases as clusters showing all connections."""
        fig, ax = plt.subplots(figsize=figsize)

        G = nx.DiGraph()

        # Add all theorems as nodes
        for thm_id, thm in self.graph.theorems.items():
            G.add_node(thm_id, phase=thm.phase,
                      critical="critical" in thm.tags,
                      name=thm.name[:20])

        # Add all edges
        for thm_id, thm in self.graph.theorems.items():
            for dep_id in thm.depends_on:
                if dep_id in self.graph.theorems:
                    G.add_edge(dep_id, thm_id)

        # Create positions using phase-based clustering
        pos = self._clustered_layout(G)

        # Draw phase backgrounds
        for phase in Phase:
            phase_nodes = [n for n in G.nodes if G.nodes[n]['phase'] == phase]
            if phase_nodes:
                xs = [pos[n][0] for n in phase_nodes]
                ys = [pos[n][1] for n in phase_nodes]

                # Draw ellipse around phase
                from matplotlib.patches import Ellipse
                center_x = np.mean(xs)
                center_y = np.mean(ys)
                width = (max(xs) - min(xs)) + 2
                height = (max(ys) - min(ys)) + 1.5

                ellipse = Ellipse((center_x, center_y), width, height,
                                 facecolor=PHASE_COLORS_LIGHT[phase],
                                 edgecolor=PHASE_COLORS[phase],
                                 linewidth=2, alpha=0.3, zorder=0)
                ax.add_patch(ellipse)

                # Phase label
                ax.text(center_x, center_y + height/2 + 0.3,
                       f"Phase {phase.value}", ha='center', fontsize=11,
                       fontweight='bold', color=PHASE_COLORS[phase])

        # Draw within-phase edges (lighter)
        within_edges = [(u, v) for u, v in G.edges()
                       if G.nodes[u]['phase'] == G.nodes[v]['phase']]
        nx.draw_networkx_edges(G, pos, ax=ax, edgelist=within_edges,
                              edge_color='gray', alpha=0.3, arrows=True,
                              arrowsize=10, connectionstyle='arc3,rad=0.1')

        # Draw cross-phase edges (prominent)
        cross_edges = [(u, v) for u, v in G.edges()
                      if G.nodes[u]['phase'] != G.nodes[v]['phase']]
        edge_colors = [PHASE_COLORS[G.nodes[u]['phase']] for u, v in cross_edges]
        nx.draw_networkx_edges(G, pos, ax=ax, edgelist=cross_edges,
                              edge_color=edge_colors, alpha=0.7, arrows=True,
                              arrowsize=12, width=1.5,
                              connectionstyle='arc3,rad=0.15')

        # Draw nodes by phase
        for phase in Phase:
            phase_nodes = [n for n in G.nodes if G.nodes[n]['phase'] == phase]
            critical_nodes = [n for n in phase_nodes if G.nodes[n]['critical']]
            normal_nodes = [n for n in phase_nodes if not G.nodes[n]['critical']]

            # Normal nodes
            nx.draw_networkx_nodes(G, pos, ax=ax, nodelist=normal_nodes,
                                  node_color=PHASE_COLORS[phase],
                                  node_size=300, alpha=0.9)

            # Critical nodes (larger with red ring)
            if critical_nodes:
                nx.draw_networkx_nodes(G, pos, ax=ax, nodelist=critical_nodes,
                                      node_color=PHASE_COLORS[phase],
                                      node_size=500, alpha=0.9)
                nx.draw_networkx_nodes(G, pos, ax=ax, nodelist=critical_nodes,
                                      node_color='none', edgecolors='red',
                                      node_size=600, linewidths=2)

        # Labels
        labels = {n: n for n in G.nodes}
        nx.draw_networkx_labels(G, pos, labels, ax=ax, font_size=7)

        ax.set_title("Combined Phase Network\n(Cross-phase connections highlighted, ★ = critical theorems)",
                    fontsize=14, fontweight='bold')
        ax.axis('off')

        # Stats annotation
        stats_text = f"Cross-phase: {len(cross_edges)} deps | Within-phase: {len(within_edges)} deps"
        ax.text(0.5, 0.02, stats_text, transform=ax.transAxes, ha='center',
               fontsize=10, style='italic')

        plt.tight_layout()

        if save:
            filepath = self.output_dir / "combined_phase_network.png"
            plt.savefig(filepath, dpi=150, bbox_inches='tight', facecolor='white')
            print(f"Saved: {filepath}")

        return fig, ax

    def _clustered_layout(self, G: nx.DiGraph) -> dict:
        """Create a layout with nodes clustered by phase."""
        pos = {}

        # Phase cluster centers (arranged in a flow)
        centers = {
            Phase.PHASE_0: (0, 3),
            Phase.PHASE_1: (3, 4.5),
            Phase.PHASE_2: (6, 3),
            Phase.PHASE_3: (9, 4.5),
            Phase.PHASE_4: (12, 3),
            Phase.PHASE_5: (15, 3),
        }

        def parse_id(tid):
            parts = tid.replace('a', '.1').replace('b', '.2').split('.')
            return tuple(float(p) for p in parts if p)

        for phase in Phase:
            phase_nodes = sorted(
                [n for n in G.nodes if G.nodes[n]['phase'] == phase],
                key=parse_id
            )

            if not phase_nodes:
                continue

            cx, cy = centers[phase]
            n = len(phase_nodes)

            # Arrange in a grid within the cluster
            cols = int(np.ceil(np.sqrt(n)))
            for i, node in enumerate(phase_nodes):
                row = i // cols
                col = i % cols
                x = cx + (col - (cols-1)/2) * 0.8
                y = cy + (row - (n/cols-1)/2) * 0.6
                pos[node] = (x, y)

        return pos

    def plot_critical_path_overlay(self, figsize=(18, 10), save=True):
        """Show all critical chains overlaid on the phase structure."""
        fig, ax = plt.subplots(figsize=figsize)

        # Phase positions (horizontal layout)
        phase_y = {
            Phase.PHASE_0: 0,
            Phase.PHASE_1: 0,
            Phase.PHASE_2: 0,
            Phase.PHASE_3: 0,
            Phase.PHASE_4: 0,
            Phase.PHASE_5: 0,
        }
        phase_x_start = {
            Phase.PHASE_0: 0,
            Phase.PHASE_1: 3,
            Phase.PHASE_2: 6,
            Phase.PHASE_3: 9,
            Phase.PHASE_4: 12,
            Phase.PHASE_5: 15,
        }

        # Draw phase lanes
        for phase in Phase:
            x_start = phase_x_start[phase]
            rect = plt.Rectangle((x_start - 0.5, -2), 2.5, 4,
                                 facecolor=PHASE_COLORS_LIGHT[phase],
                                 edgecolor=PHASE_COLORS[phase],
                                 linewidth=2, alpha=0.5, zorder=0)
            ax.add_patch(rect)
            ax.text(x_start + 0.75, 2.3, f"P{phase.value}", ha='center',
                   fontsize=10, fontweight='bold', color=PHASE_COLORS[phase])

        # Position theorems within their phase lanes
        def parse_id(tid):
            parts = tid.replace('a', '.1').replace('b', '.2').split('.')
            return tuple(float(p) for p in parts if p)

        pos = {}
        for phase in Phase:
            phase_thms = sorted(
                [t for t in self.graph.theorems.values() if t.phase == phase],
                key=lambda t: parse_id(t.id)
            )
            x_base = phase_x_start[phase]
            n = len(phase_thms)
            for i, thm in enumerate(phase_thms):
                y = 1.5 - (i / max(n-1, 1)) * 3  # spread vertically
                pos[thm.id] = (x_base + 0.75, y)

        # Draw critical chains with different colors
        chain_colors = {
            "bootstrap_resolution": "#E53935",      # Red
            "chirality_arrow_of_time": "#8E24AA",   # Purple
            "matter_antimatter": "#43A047",          # Green
            "gravity_emergence": "#1E88E5",          # Blue
            "mass_hierarchy": "#FB8C00",             # Orange
        }

        chain_offsets = {
            "bootstrap_resolution": 0,
            "chirality_arrow_of_time": 0.15,
            "matter_antimatter": -0.15,
            "gravity_emergence": 0.3,
            "mass_hierarchy": -0.3,
        }

        # Draw chains
        for chain_name, chain in CRITICAL_CHAINS.items():
            color = chain_colors.get(chain_name, 'gray')
            offset = chain_offsets.get(chain_name, 0)

            valid_chain = [tid for tid in chain if tid in pos]

            for i in range(len(valid_chain) - 1):
                from_id = valid_chain[i]
                to_id = valid_chain[i + 1]

                x1, y1 = pos[from_id]
                x2, y2 = pos[to_id]

                # Apply offset to avoid overlap
                y1 += offset
                y2 += offset

                arrow = FancyArrowPatch(
                    (x1, y1), (x2, y2),
                    arrowstyle='-|>',
                    mutation_scale=12,
                    lw=2.5,
                    color=color,
                    alpha=0.8,
                    connectionstyle='arc3,rad=0.1',
                    zorder=5
                )
                ax.add_patch(arrow)

        # Draw theorem nodes
        for thm_id, (x, y) in pos.items():
            thm = self.graph.theorems[thm_id]
            is_critical = "critical" in thm.tags

            # Check which chains this theorem is in
            in_chains = [name for name, chain in CRITICAL_CHAINS.items() if thm_id in chain]

            if in_chains:
                # Node is in a critical chain
                size = 200 if is_critical else 120
                ax.scatter([x], [y], s=size, c=[PHASE_COLORS[thm.phase]],
                          edgecolors='black', linewidths=1.5, zorder=10)
                ax.text(x, y - 0.25, thm_id, fontsize=6, ha='center', va='top', zorder=11)
            else:
                # Background node
                ax.scatter([x], [y], s=50, c=[PHASE_COLORS[thm.phase]],
                          alpha=0.3, zorder=1)

        # Legend
        legend_elements = [
            mpatches.Patch(color=color, label=name.replace('_', ' ').title())
            for name, color in chain_colors.items()
        ]
        ax.legend(handles=legend_elements, loc='upper left', fontsize=9,
                 title="Critical Chains", title_fontsize=10)

        ax.set_xlim(-1, 18)
        ax.set_ylim(-2.5, 3)
        ax.set_title("Critical Dependency Chains Across Phases\n(Showing how key results flow through the framework)",
                    fontsize=14, fontweight='bold')
        ax.axis('off')

        plt.tight_layout()

        if save:
            filepath = self.output_dir / "critical_path_overlay.png"
            plt.savefig(filepath, dpi=150, bbox_inches='tight', facecolor='white')
            print(f"Saved: {filepath}")

        return fig, ax

    def plot_phase_dependency_summary(self, figsize=(14, 10), save=True):
        """Create a summary showing key cross-phase dependencies with theorem names."""
        fig, ax = plt.subplots(figsize=figsize)

        # Collect significant cross-phase dependencies
        significant_deps = []
        for from_phase in Phase:
            for to_phase in Phase:
                if from_phase != to_phase:
                    edges = self.phase_deps[from_phase][to_phase]
                    for from_id, to_id in edges:
                        from_thm = self.graph.theorems[from_id]
                        to_thm = self.graph.theorems[to_id]
                        # Include if either is critical
                        if "critical" in from_thm.tags or "critical" in to_thm.tags:
                            significant_deps.append((from_thm, to_thm))

        # Build text summary
        y_pos = 0.95
        ax.text(0.5, 0.98, "Key Cross-Phase Dependencies", transform=ax.transAxes,
               fontsize=14, fontweight='bold', ha='center', va='top')
        ax.text(0.5, 0.94, "(Dependencies involving critical theorems)", transform=ax.transAxes,
               fontsize=10, ha='center', va='top', style='italic', color='gray')

        y_pos = 0.88
        current_from_phase = None

        for from_thm, to_thm in sorted(significant_deps, key=lambda x: (x[0].phase.value, x[1].phase.value)):
            if from_thm.phase != current_from_phase:
                current_from_phase = from_thm.phase
                y_pos -= 0.03
                ax.text(0.05, y_pos, f"From {PHASE_SHORT[from_thm.phase]}:",
                       transform=ax.transAxes, fontsize=11, fontweight='bold',
                       color=PHASE_COLORS[from_thm.phase])
                y_pos -= 0.04

            from_mark = "★" if "critical" in from_thm.tags else "•"
            to_mark = "★" if "critical" in to_thm.tags else "•"

            text = f"  {from_mark} {from_thm.id}: {from_thm.name[:35]}..."
            ax.text(0.08, y_pos, text, transform=ax.transAxes, fontsize=9,
                   color=PHASE_COLORS[from_thm.phase])

            y_pos -= 0.025
            text = f"      → {to_mark} {to_thm.id}: {to_thm.name[:35]}... (P{to_thm.phase.value})"
            ax.text(0.08, y_pos, text, transform=ax.transAxes, fontsize=9,
                   color=PHASE_COLORS[to_thm.phase])
            y_pos -= 0.035

            if y_pos < 0.05:
                break

        ax.axis('off')

        if save:
            filepath = self.output_dir / "phase_dependency_summary.png"
            plt.savefig(filepath, dpi=150, bbox_inches='tight', facecolor='white')
            print(f"Saved: {filepath}")

        return fig, ax

    def generate_all_phase_plots(self):
        """Generate all phase interaction visualizations."""
        print("\n=== Generating Phase Interaction Visualizations ===\n")

        print("1. Phase flow diagram...")
        self.plot_phase_flow_diagram()

        print("2. Phase coupling matrix...")
        self.plot_phase_coupling_matrix()

        print("3. Combined network view...")
        self.plot_combined_network()

        print("4. Critical path overlay...")
        self.plot_critical_path_overlay()

        print("5. Dependency summary...")
        self.plot_phase_dependency_summary()

        print(f"\nAll plots saved to: {self.output_dir.absolute()}")

        # Print summary statistics
        print("\n=== Cross-Phase Dependency Summary ===")
        print(f"Total cross-phase dependencies: {len(self.cross_phase_edges)}")
        print(f"Total within-phase dependencies: {len(self.within_phase_edges)}")
        print(f"Cross-phase ratio: {100*len(self.cross_phase_edges)/(len(self.cross_phase_edges)+len(self.within_phase_edges)):.1f}%")


if __name__ == "__main__":
    visualizer = PhaseInteractionVisualizer()
    visualizer.generate_all_phase_plots()
