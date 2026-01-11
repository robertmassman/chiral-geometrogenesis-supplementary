"""
Theorem Visualization Module

Creates visual representations of the Chiral Geometrogenesis theorem network:
- Dependency graphs (network diagrams)
- Phase-level summaries
- Critical path visualizations
- Status dashboards
"""

import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.colors import LinearSegmentedColormap
import networkx as nx
import numpy as np
from pathlib import Path

from theorem_graph import (
    TheoremGraph, Phase, Status, TheoremType,
    CRITICAL_CHAINS
)


# Color schemes
PHASE_COLORS = {
    Phase.PHASE_0: "#E8F5E9",  # Light green - Pre-geometric
    Phase.PHASE_1: "#E3F2FD",  # Light blue - Foundational
    Phase.PHASE_2: "#FFF3E0",  # Light orange - Pressure-Depression
    Phase.PHASE_3: "#FCE4EC",  # Light pink - Mass Generation
    Phase.PHASE_4: "#F3E5F5",  # Light purple - Solitons
    Phase.PHASE_5: "#FFFDE7",  # Light yellow - Spacetime
}

PHASE_EDGE_COLORS = {
    Phase.PHASE_0: "#4CAF50",  # Green
    Phase.PHASE_1: "#2196F3",  # Blue
    Phase.PHASE_2: "#FF9800",  # Orange
    Phase.PHASE_3: "#E91E63",  # Pink
    Phase.PHASE_4: "#9C27B0",  # Purple
    Phase.PHASE_5: "#FFC107",  # Amber
}

STATUS_COLORS = {
    Status.ESTABLISHED: "#4CAF50",  # Green
    Status.VERIFIED: "#2196F3",     # Blue
    Status.NOVEL: "#FF9800",        # Orange
    Status.PARTIAL: "#FFC107",      # Yellow
    Status.CONJECTURE: "#9E9E9E",   # Gray
}

TYPE_SHAPES = {
    TheoremType.DEFINITION: "s",    # Square
    TheoremType.THEOREM: "o",       # Circle
    TheoremType.LEMMA: "^",         # Triangle
    TheoremType.COROLLARY: "d",     # Diamond
}


class TheoremVisualizer:
    """Visualization tools for the theorem graph."""

    def __init__(self, graph: TheoremGraph = None):
        self.graph = graph or TheoremGraph()
        self.output_dir = Path("plots")
        self.output_dir.mkdir(exist_ok=True)

    def create_networkx_graph(self, filter_phase: Phase = None) -> nx.DiGraph:
        """Create a NetworkX directed graph from the theorem graph."""
        G = nx.DiGraph()

        theorems = self.graph.theorems.values()
        if filter_phase:
            theorems = [t for t in theorems if t.phase == filter_phase]

        for thm in theorems:
            G.add_node(
                thm.id,
                name=thm.name,
                phase=thm.phase,
                status=thm.status,
                theorem_type=thm.theorem_type,
                tags=thm.tags
            )

        for thm in theorems:
            for dep_id in thm.depends_on:
                if dep_id in G.nodes:
                    G.add_edge(dep_id, thm.id)

        return G

    def plot_full_dependency_graph(self, figsize=(20, 16), save=True):
        """Plot the complete theorem dependency network."""
        G = self.create_networkx_graph()

        fig, ax = plt.subplots(figsize=figsize)
        ax.set_title("Chiral Geometrogenesis: Complete Theorem Dependency Network",
                     fontsize=16, fontweight='bold', pad=20)

        # Use hierarchical layout based on phases
        pos = self._hierarchical_layout(G)

        # Draw edges
        nx.draw_networkx_edges(
            G, pos, ax=ax,
            edge_color='gray',
            alpha=0.5,
            arrows=True,
            arrowsize=15,
            arrowstyle='-|>',
            connectionstyle='arc3,rad=0.1'
        )

        # Draw nodes by phase
        for phase in Phase:
            phase_nodes = [n for n in G.nodes if G.nodes[n].get('phase') == phase]
            if phase_nodes:
                node_colors = [STATUS_COLORS.get(G.nodes[n].get('status'), '#9E9E9E')
                               for n in phase_nodes]
                nx.draw_networkx_nodes(
                    G, pos, ax=ax,
                    nodelist=phase_nodes,
                    node_color=node_colors,
                    node_size=800,
                    edgecolors=PHASE_EDGE_COLORS[phase],
                    linewidths=2
                )

        # Draw labels
        labels = {n: n for n in G.nodes}
        nx.draw_networkx_labels(G, pos, labels, ax=ax, font_size=8)

        # Highlight critical theorems
        critical_nodes = [n for n in G.nodes if 'critical' in G.nodes[n].get('tags', [])]
        nx.draw_networkx_nodes(
            G, pos, ax=ax,
            nodelist=critical_nodes,
            node_size=1200,
            node_color='none',
            edgecolors='red',
            linewidths=3,
            node_shape='o'
        )

        # Create legend
        self._add_legend(ax)

        ax.axis('off')
        plt.tight_layout()

        if save:
            filepath = self.output_dir / "theorem_dependency_graph.png"
            plt.savefig(filepath, dpi=150, bbox_inches='tight',
                        facecolor='white', edgecolor='none')
            print(f"Saved: {filepath}")

        return fig, ax

    def _hierarchical_layout(self, G: nx.DiGraph) -> dict:
        """Create a hierarchical layout based on phases."""
        pos = {}

        # Group nodes by phase
        phase_groups = {phase: [] for phase in Phase}
        for node in G.nodes:
            phase = G.nodes[node].get('phase')
            if phase:
                phase_groups[phase].append(node)

        # Position nodes
        y_positions = {
            Phase.PHASE_0: 5,
            Phase.PHASE_1: 4,
            Phase.PHASE_2: 3,
            Phase.PHASE_3: 2,
            Phase.PHASE_4: 1,
            Phase.PHASE_5: 0
        }

        def parse_theorem_id(tid):
            """Parse theorem ID for sorting (handles formats like 0.1.1, 3.1.2a, etc.)"""
            # Remove letters and convert to tuple for sorting
            parts = tid.replace('a', '.1').replace('b', '.2').split('.')
            return tuple(float(p) for p in parts if p)

        for phase, nodes in phase_groups.items():
            if not nodes:
                continue
            y = y_positions[phase]
            # Sort nodes by ID for consistent ordering
            nodes_sorted = sorted(nodes, key=parse_theorem_id)
            n = len(nodes_sorted)
            for i, node in enumerate(nodes_sorted):
                x = (i - (n - 1) / 2) * 1.5
                pos[node] = (x, y)

        return pos

    def _add_legend(self, ax):
        """Add legend for phases and status."""
        # Phase legend
        phase_patches = [
            mpatches.Patch(edgecolor=PHASE_EDGE_COLORS[phase], facecolor='white',
                          linewidth=2, label=f"Phase {phase.value}")
            for phase in Phase
        ]

        # Status legend
        status_patches = [
            mpatches.Patch(color=STATUS_COLORS[status], label=status.value.capitalize())
            for status in Status
        ]

        # Critical indicator
        critical_patch = mpatches.Patch(edgecolor='red', facecolor='none',
                                        linewidth=3, label='Critical (red ring)')

        legend1 = ax.legend(handles=phase_patches, loc='upper left',
                           title='Phases', fontsize=8)
        ax.add_artist(legend1)

        legend2 = ax.legend(handles=status_patches + [critical_patch],
                           loc='upper right', title='Status', fontsize=8)

    def plot_phase_summary(self, figsize=(14, 8), save=True):
        """Create a summary visualization of theorems by phase."""
        fig, axes = plt.subplots(2, 3, figsize=figsize)
        axes = axes.flatten()

        phase_names = [
            "Phase 0: Pre-Geometric",
            "Phase 1: Foundational Math",
            "Phase 2: Pressure-Depression",
            "Phase 3: Mass Generation",
            "Phase 4: Topological Solitons",
            "Phase 5: Emergent Gravity"
        ]

        for idx, phase in enumerate(Phase):
            ax = axes[idx]
            theorems = self.graph.get_phase_theorems(phase)

            # Count by status
            status_counts = {s: 0 for s in Status}
            for thm in theorems:
                status_counts[thm.status] += 1

            # Create pie chart
            sizes = [status_counts[s] for s in Status]
            colors = [STATUS_COLORS[s] for s in Status]
            labels = [s.value.capitalize() for s in Status]

            # Filter out zero values
            non_zero = [(s, c, l) for s, c, l in zip(sizes, colors, labels) if s > 0]
            if non_zero:
                sizes, colors, labels = zip(*non_zero)

                wedges, texts, autotexts = ax.pie(
                    sizes, colors=colors, autopct='%1.0f%%',
                    startangle=90, pctdistance=0.75
                )
                for autotext in autotexts:
                    autotext.set_fontsize(9)

            ax.set_title(f"{phase_names[idx]}\n({len(theorems)} theorems)",
                        fontsize=10, fontweight='bold')

        # Add overall legend
        legend_patches = [
            mpatches.Patch(color=STATUS_COLORS[s], label=s.value.capitalize())
            for s in Status
        ]
        fig.legend(handles=legend_patches, loc='lower center', ncol=5,
                  fontsize=9, bbox_to_anchor=(0.5, 0.02))

        fig.suptitle("Theorem Status by Phase", fontsize=14, fontweight='bold', y=0.98)
        plt.tight_layout(rect=[0, 0.08, 1, 0.95])

        if save:
            filepath = self.output_dir / "theorem_phase_summary.png"
            plt.savefig(filepath, dpi=150, bbox_inches='tight',
                        facecolor='white', edgecolor='none')
            print(f"Saved: {filepath}")

        return fig, axes

    def plot_critical_chains(self, figsize=(16, 12), save=True):
        """Visualize the critical dependency chains."""
        fig, axes = plt.subplots(2, 3, figsize=figsize)
        axes = axes.flatten()

        chain_titles = {
            "bootstrap_resolution": "Bootstrap Resolution Chain",
            "chirality_arrow_of_time": "Chirality → Arrow of Time",
            "matter_antimatter": "Matter-Antimatter Asymmetry",
            "gravity_emergence": "Gravity Emergence",
            "mass_hierarchy": "Mass Hierarchy"
        }

        for idx, (chain_name, chain) in enumerate(CRITICAL_CHAINS.items()):
            if idx >= len(axes):
                break

            ax = axes[idx]
            self._plot_chain(ax, chain, chain_titles.get(chain_name, chain_name))

        # Hide unused axes
        for idx in range(len(CRITICAL_CHAINS), len(axes)):
            axes[idx].axis('off')

        fig.suptitle("Critical Dependency Chains", fontsize=14, fontweight='bold')
        plt.tight_layout()

        if save:
            filepath = self.output_dir / "theorem_critical_chains.png"
            plt.savefig(filepath, dpi=150, bbox_inches='tight',
                        facecolor='white', edgecolor='none')
            print(f"Saved: {filepath}")

        return fig, axes

    def _plot_chain(self, ax, chain: list, title: str):
        """Plot a single dependency chain."""
        G = nx.DiGraph()

        # Add nodes and edges
        for i, thm_id in enumerate(chain):
            if thm_id in self.graph.theorems:
                thm = self.graph.theorems[thm_id]
                G.add_node(thm_id,
                          phase=thm.phase,
                          status=thm.status,
                          name=thm.name[:25] + '...' if len(thm.name) > 25 else thm.name)

        for i in range(len(chain) - 1):
            if chain[i] in G.nodes and chain[i+1] in G.nodes:
                G.add_edge(chain[i], chain[i+1])

        if len(G.nodes) == 0:
            ax.text(0.5, 0.5, "No data", ha='center', va='center')
            ax.set_title(title)
            ax.axis('off')
            return

        # Vertical layout
        pos = {}
        for i, node in enumerate(chain):
            if node in G.nodes:
                pos[node] = (0, -i)

        # Draw
        node_colors = [STATUS_COLORS.get(G.nodes[n].get('status'), '#9E9E9E')
                       for n in G.nodes]
        edge_colors = [PHASE_EDGE_COLORS.get(G.nodes[n].get('phase'), '#666')
                       for n in G.nodes]

        nx.draw_networkx_nodes(G, pos, ax=ax, node_color=node_colors,
                              node_size=600, edgecolors=edge_colors, linewidths=2)
        nx.draw_networkx_edges(G, pos, ax=ax, edge_color='gray',
                              arrows=True, arrowsize=15)

        # Labels with theorem names
        labels = {}
        for node in G.nodes:
            name = G.nodes[node].get('name', node)
            labels[node] = f"{node}\n{name}"

        nx.draw_networkx_labels(G, pos, labels, ax=ax, font_size=7)

        ax.set_title(title, fontsize=10, fontweight='bold')
        ax.axis('off')

    def plot_dependency_matrix(self, figsize=(14, 12), save=True):
        """Create a dependency matrix heatmap."""
        fig, ax = plt.subplots(figsize=figsize)

        def parse_theorem_id(tid):
            """Parse theorem ID for sorting (handles formats like 0.1.1, 3.1.2a, etc.)"""
            parts = tid.replace('a', '.1').replace('b', '.2').split('.')
            return tuple(float(p) for p in parts if p)

        # Get sorted list of theorems
        theorem_ids = sorted(self.graph.theorems.keys(),
                            key=lambda x: (self.graph.theorems[x].phase.value,
                                          parse_theorem_id(x)))

        n = len(theorem_ids)
        matrix = np.zeros((n, n))

        id_to_idx = {tid: idx for idx, tid in enumerate(theorem_ids)}

        # Fill matrix
        for thm_id, thm in self.graph.theorems.items():
            if thm_id in id_to_idx:
                for dep_id in thm.depends_on:
                    if dep_id in id_to_idx:
                        matrix[id_to_idx[thm_id], id_to_idx[dep_id]] = 1

        # Create heatmap
        cmap = LinearSegmentedColormap.from_list('dep', ['white', '#2196F3'])
        im = ax.imshow(matrix, cmap=cmap, aspect='auto')

        # Set ticks
        ax.set_xticks(range(n))
        ax.set_yticks(range(n))
        ax.set_xticklabels(theorem_ids, rotation=90, fontsize=7)
        ax.set_yticklabels(theorem_ids, fontsize=7)

        # Add phase separators
        prev_phase = None
        for idx, tid in enumerate(theorem_ids):
            phase = self.graph.theorems[tid].phase
            if prev_phase is not None and phase != prev_phase:
                ax.axhline(y=idx - 0.5, color='red', linewidth=1, alpha=0.5)
                ax.axvline(x=idx - 0.5, color='red', linewidth=1, alpha=0.5)
            prev_phase = phase

        ax.set_xlabel("Depends On (Column)", fontsize=10)
        ax.set_ylabel("Theorem (Row)", fontsize=10)
        ax.set_title("Theorem Dependency Matrix\n(Row depends on Column)",
                    fontsize=12, fontweight='bold')

        plt.colorbar(im, ax=ax, label='Dependency')
        plt.tight_layout()

        if save:
            filepath = self.output_dir / "theorem_dependency_matrix.png"
            plt.savefig(filepath, dpi=150, bbox_inches='tight',
                        facecolor='white', edgecolor='none')
            print(f"Saved: {filepath}")

        return fig, ax

    def plot_statistics_dashboard(self, figsize=(14, 10), save=True):
        """Create a statistics dashboard."""
        fig = plt.figure(figsize=figsize)

        stats = self.graph.get_statistics()

        # Subplot 1: Total by phase (bar chart)
        ax1 = fig.add_subplot(2, 2, 1)
        phases = list(stats["by_phase"].keys())
        counts = list(stats["by_phase"].values())
        colors = [PHASE_EDGE_COLORS[Phase[p]] for p in phases]
        bars = ax1.bar(range(len(phases)), counts, color=colors)
        ax1.set_xticks(range(len(phases)))
        ax1.set_xticklabels([f"P{i}" for i in range(6)], fontsize=10)
        ax1.set_ylabel("Count")
        ax1.set_title("Theorems by Phase", fontweight='bold')
        for bar, count in zip(bars, counts):
            ax1.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 0.2,
                    str(count), ha='center', fontsize=9)

        # Subplot 2: By type (pie chart)
        ax2 = fig.add_subplot(2, 2, 2)
        types = list(stats["by_type"].keys())
        type_counts = list(stats["by_type"].values())
        type_colors = ['#4CAF50', '#2196F3', '#FF9800', '#9C27B0']
        non_zero = [(t, c, col) for t, c, col in zip(types, type_counts, type_colors) if c > 0]
        if non_zero:
            types, type_counts, type_colors = zip(*non_zero)
            ax2.pie(type_counts, labels=types, colors=type_colors, autopct='%1.0f%%',
                   startangle=90)
        ax2.set_title("By Type", fontweight='bold')

        # Subplot 3: By status (horizontal bar)
        ax3 = fig.add_subplot(2, 2, 3)
        statuses = list(stats["by_status"].keys())
        status_counts = list(stats["by_status"].values())
        status_colors = [STATUS_COLORS[Status(s)] for s in statuses]
        y_pos = range(len(statuses))
        bars = ax3.barh(y_pos, status_counts, color=status_colors)
        ax3.set_yticks(y_pos)
        ax3.set_yticklabels([s.capitalize() for s in statuses])
        ax3.set_xlabel("Count")
        ax3.set_title("By Verification Status", fontweight='bold')
        for bar, count in zip(bars, status_counts):
            ax3.text(bar.get_width() + 0.2, bar.get_y() + bar.get_height()/2,
                    str(count), va='center', fontsize=9)

        # Subplot 4: Summary text
        ax4 = fig.add_subplot(2, 2, 4)
        ax4.axis('off')

        summary_text = f"""
        THEOREM GRAPH SUMMARY
        ═══════════════════════════════════

        Total Theorems:     {stats['total_theorems']}
        Critical Theorems:  {stats['critical_count']}
        Total Dependencies: {stats['total_dependencies']}

        VERIFICATION STATUS
        ───────────────────
        • Established:  {stats['by_status'].get('established', 0)}
        • Verified:     {stats['by_status'].get('verified', 0)}
        • Novel:        {stats['by_status'].get('novel', 0)}
        • Partial:      {stats['by_status'].get('partial', 0)}
        • Conjecture:   {stats['by_status'].get('conjecture', 0)}

        KEY METRICS
        ───────────────────
        Avg deps/theorem:   {stats['total_dependencies']/max(1,stats['total_theorems']):.1f}
        Verification rate:  {100*(stats['by_status'].get('verified',0)+stats['by_status'].get('established',0))/max(1,stats['total_theorems']):.0f}%
        """

        ax4.text(0.1, 0.9, summary_text, transform=ax4.transAxes,
                fontsize=10, fontfamily='monospace', verticalalignment='top')

        fig.suptitle("Chiral Geometrogenesis: Theorem Statistics Dashboard",
                    fontsize=14, fontweight='bold')
        plt.tight_layout(rect=[0, 0, 1, 0.96])

        if save:
            filepath = self.output_dir / "theorem_statistics_dashboard.png"
            plt.savefig(filepath, dpi=150, bbox_inches='tight',
                        facecolor='white', edgecolor='none')
            print(f"Saved: {filepath}")

        return fig

    def generate_all_plots(self):
        """Generate all visualization plots."""
        print("\n=== Generating Theorem Visualizations ===\n")

        print("1. Full dependency graph...")
        self.plot_full_dependency_graph()

        print("2. Phase summary...")
        self.plot_phase_summary()

        print("3. Critical chains...")
        self.plot_critical_chains()

        print("4. Dependency matrix...")
        self.plot_dependency_matrix()

        print("5. Statistics dashboard...")
        self.plot_statistics_dashboard()

        print(f"\nAll plots saved to: {self.output_dir.absolute()}")


if __name__ == "__main__":
    visualizer = TheoremVisualizer()
    visualizer.generate_all_plots()
