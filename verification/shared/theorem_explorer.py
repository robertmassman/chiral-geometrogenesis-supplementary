"""
Interactive Theorem Explorer

A command-line tool for exploring the Chiral Geometrogenesis theorem network.
Provides queries, dependency analysis, and chain visualization.
"""

import sys
from theorem_graph import (
    TheoremGraph, Phase, Status, TheoremType,
    CRITICAL_CHAINS
)


class TheoremExplorer:
    """Interactive explorer for the theorem graph."""

    def __init__(self):
        self.graph = TheoremGraph()

    def print_header(self):
        """Print welcome header."""
        print("""
╔══════════════════════════════════════════════════════════════╗
║       CHIRAL GEOMETROGENESIS THEOREM EXPLORER                ║
║       Interactive Navigation of the Framework                ║
╚══════════════════════════════════════════════════════════════╝
""")

    def print_theorem(self, thm_id: str, verbose: bool = True):
        """Print details of a single theorem."""
        if thm_id not in self.graph.theorems:
            print(f"  ❌ Theorem '{thm_id}' not found")
            return

        thm = self.graph.theorems[thm_id]
        status_emoji = {
            Status.ESTABLISHED: "✅",
            Status.VERIFIED: "🔵",
            Status.NOVEL: "🔶",
            Status.PARTIAL: "🔸",
            Status.CONJECTURE: "🔮"
        }

        print(f"\n  {status_emoji.get(thm.status, '•')} {thm.full_id()}: {thm.name}")
        print(f"     Phase: {thm.phase.value} | Status: {thm.status.value.upper()}")

        if verbose:
            print(f"     {thm.description}")
            if thm.key_result:
                print(f"     Key Result: {thm.key_result}")
            if thm.depends_on:
                print(f"     Depends on: {', '.join(thm.depends_on)}")
            if thm.required_by:
                print(f"     Required by: {', '.join(thm.required_by)}")
            if thm.tags:
                print(f"     Tags: {', '.join(thm.tags)}")
            if thm.verification_date:
                print(f"     Verified: {thm.verification_date}")

    def list_phase(self, phase_num: int):
        """List all theorems in a phase."""
        try:
            phase = Phase(phase_num)
        except ValueError:
            print(f"  ❌ Invalid phase number: {phase_num}")
            return

        phase_names = {
            0: "Pre-Geometric Structure",
            1: "Foundational Mathematics",
            2: "Pressure-Depression Mechanism",
            3: "Mass Generation via Phase-Gradient Mass Generation",
            4: "Topological Solitons as Matter",
            5: "Emergent Spacetime and Gravity"
        }

        print(f"\n  ═══ PHASE {phase_num}: {phase_names.get(phase_num, '')} ═══")

        theorems = self.graph.get_phase_theorems(phase)
        theorems.sort(key=lambda t: t.id)

        for thm in theorems:
            self.print_theorem(thm.id, verbose=False)

    def show_dependencies(self, thm_id: str, direction: str = "both"):
        """Show dependency tree for a theorem."""
        if thm_id not in self.graph.theorems:
            print(f"  ❌ Theorem '{thm_id}' not found")
            return

        thm = self.graph.theorems[thm_id]
        print(f"\n  ═══ Dependencies for {thm.full_id()} ═══")

        if direction in ("both", "up"):
            print("\n  ▲ DEPENDS ON (upstream):")
            self._print_tree_up(thm_id, visited=set(), depth=0)

        if direction in ("both", "down"):
            print("\n  ▼ REQUIRED BY (downstream):")
            self._print_tree_down(thm_id, visited=set(), depth=0)

    def _print_tree_up(self, thm_id: str, visited: set, depth: int):
        """Print upstream dependencies."""
        if thm_id in visited or thm_id not in self.graph.theorems:
            return
        visited.add(thm_id)

        thm = self.graph.theorems[thm_id]
        indent = "    " * depth

        if depth > 0:
            critical = "★" if "critical" in thm.tags else " "
            print(f"  {indent}└── {critical} {thm_id}: {thm.name[:40]}...")

        for dep_id in thm.depends_on:
            self._print_tree_up(dep_id, visited, depth + 1)

    def _print_tree_down(self, thm_id: str, visited: set, depth: int):
        """Print downstream dependents."""
        if thm_id in visited or thm_id not in self.graph.theorems:
            return
        visited.add(thm_id)

        thm = self.graph.theorems[thm_id]
        indent = "    " * depth

        if depth > 0:
            critical = "★" if "critical" in thm.tags else " "
            print(f"  {indent}└── {critical} {thm_id}: {thm.name[:40]}...")

        for req_id in thm.required_by:
            self._print_tree_down(req_id, visited, depth + 1)

    def show_chain(self, chain_name: str):
        """Show a predefined critical chain."""
        if chain_name not in CRITICAL_CHAINS:
            print(f"  ❌ Unknown chain: {chain_name}")
            print(f"  Available chains: {', '.join(CRITICAL_CHAINS.keys())}")
            return

        chain = CRITICAL_CHAINS[chain_name]
        print(f"\n  ═══ {chain_name.replace('_', ' ').upper()} ═══\n")

        for i, thm_id in enumerate(chain):
            if thm_id in self.graph.theorems:
                thm = self.graph.theorems[thm_id]
                arrow = "    ↓" if i < len(chain) - 1 else ""
                critical = "★" if "critical" in thm.tags else " "
                print(f"  {critical} [{thm_id}] {thm.name}")
                if thm.key_result:
                    print(f"     → {thm.key_result[:60]}...")
                print(arrow)

    def search(self, query: str):
        """Search theorems by name, tags, or content."""
        query_lower = query.lower()
        matches = []

        for thm_id, thm in self.graph.theorems.items():
            if (query_lower in thm.name.lower() or
                query_lower in thm.description.lower() or
                query_lower in thm_id.lower() or
                any(query_lower in tag for tag in thm.tags) or
                (thm.key_result and query_lower in thm.key_result.lower())):
                matches.append(thm)

        if not matches:
            print(f"  No theorems found matching '{query}'")
            return

        print(f"\n  ═══ Search Results for '{query}' ({len(matches)} found) ═══")
        for thm in matches:
            self.print_theorem(thm.id, verbose=False)

    def show_critical(self):
        """Show all critical theorems."""
        print("\n  ═══ CRITICAL THEOREMS ═══")
        print("  (★ = critical breakthrough for the framework)\n")

        for thm in self.graph.get_critical_theorems():
            self.print_theorem(thm.id, verbose=True)

    def show_stats(self):
        """Show graph statistics."""
        stats = self.graph.get_statistics()

        print("\n  ═══ THEOREM GRAPH STATISTICS ═══\n")
        print(f"  Total theorems:     {stats['total_theorems']}")
        print(f"  Critical theorems:  {stats['critical_count']}")
        print(f"  Total dependencies: {stats['total_dependencies']}")

        print("\n  By Phase:")
        for phase, count in stats["by_phase"].items():
            print(f"    {phase}: {count}")

        print("\n  By Status:")
        for status, count in stats["by_status"].items():
            print(f"    {status}: {count}")

        print("\n  By Type:")
        for thm_type, count in stats["by_type"].items():
            print(f"    {thm_type}: {count}")

    def show_help(self):
        """Show available commands."""
        help_text = """
  ═══ AVAILABLE COMMANDS ═══

  NAVIGATION:
    phase <0-5>      - List all theorems in a phase
    show <id>        - Show detailed info for theorem (e.g., show 3.1.1)
    deps <id>        - Show dependency tree for theorem

  DISCOVERY:
    search <query>   - Search by name, tags, or content
    critical         - List all critical theorems
    chains           - List available critical chains
    chain <name>     - Show a specific critical chain

  ANALYSIS:
    stats            - Show graph statistics

  UTILITY:
    help             - Show this help
    quit / exit      - Exit explorer

  EXAMPLES:
    phase 3          - Show mass generation theorems
    show 5.2.4       - Details on Newton's constant derivation
    deps 3.1.1       - Dependencies for phase-gradient mass generation formula
    search gravity   - Find gravity-related theorems
    chain bootstrap_resolution - Show bootstrap chain
"""
        print(help_text)

    def run_interactive(self):
        """Run interactive command loop."""
        self.print_header()
        self.show_help()

        while True:
            try:
                cmd = input("\n  theorem> ").strip()
            except (EOFError, KeyboardInterrupt):
                print("\n  Goodbye!")
                break

            if not cmd:
                continue

            parts = cmd.split(maxsplit=1)
            command = parts[0].lower()
            arg = parts[1] if len(parts) > 1 else ""

            if command in ("quit", "exit", "q"):
                print("  Goodbye!")
                break
            elif command == "help":
                self.show_help()
            elif command == "phase":
                try:
                    self.list_phase(int(arg))
                except ValueError:
                    print("  Usage: phase <0-5>")
            elif command == "show":
                self.print_theorem(arg)
            elif command == "deps":
                self.show_dependencies(arg)
            elif command == "search":
                self.search(arg)
            elif command == "critical":
                self.show_critical()
            elif command == "chains":
                print("\n  Available chains:")
                for name in CRITICAL_CHAINS:
                    print(f"    • {name}")
            elif command == "chain":
                self.show_chain(arg)
            elif command == "stats":
                self.show_stats()
            else:
                print(f"  Unknown command: {command}")
                print("  Type 'help' for available commands")

    def run_batch(self, commands: list):
        """Run a list of commands non-interactively."""
        self.print_header()

        for cmd in commands:
            print(f"\n  >>> {cmd}")
            parts = cmd.split(maxsplit=1)
            command = parts[0].lower()
            arg = parts[1] if len(parts) > 1 else ""

            if command == "phase":
                self.list_phase(int(arg))
            elif command == "show":
                self.print_theorem(arg)
            elif command == "deps":
                self.show_dependencies(arg)
            elif command == "search":
                self.search(arg)
            elif command == "critical":
                self.show_critical()
            elif command == "chain":
                self.show_chain(arg)
            elif command == "stats":
                self.show_stats()


def main():
    explorer = TheoremExplorer()

    if len(sys.argv) > 1:
        # Command-line arguments provided
        cmd = " ".join(sys.argv[1:])
        explorer.run_batch([cmd])
    else:
        # Interactive mode
        explorer.run_interactive()


if __name__ == "__main__":
    main()
