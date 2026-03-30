#!/usr/bin/env python3
"""
StellaLang Interpreter
======================
A ternary programming language derived from Chiral Geometrogenesis.
Every operation is grounded in a proven theorem from the CG framework.

See spec.md for the full specification and proof mappings.

Usage:
    python3 interpreter.py -c "r.r.r."           # Inline code
    python3 interpreter.py program.stella          # From file
    python3 interpreter.py -c "r.r.r." -v          # Verbose trace
    python3 interpreter.py -c "[>r<R]" --strict    # Forward-only mode
"""

import sys
import argparse


# --- Proof-grounded constants ---

# Initial tape size: 8 vertices of the stella octangula
# Proof: Definition 0.1.1 (Stella Octangula Boundary Topology)
STELLA_VERTICES = 8

# Z_3 modulus: three color field phases
# Proof: Definition 0.1.2 (Three Color Fields), Prop 0.0.XXa (First Stable Principle)
Z3_MODULUS = 3

# Natural frequency: omega = 220 MeV (from Casimir equipartition)
# Proof: Proposition 0.0.17l (Internal Frequency from Casimir Equipartition)
OMEGA_MEV = 220.0

# Valid instruction characters
INSTRUCTIONS = set("rR><.,[]")


class StellaError(Exception):
    """Base exception for StellaLang errors."""
    pass


class SuperselectionError(StellaError):
    """Raised when strict mode forbids an operation."""
    pass


class StellaVM:
    """
    Virtual machine for StellaLang programs.

    Memory: tape of trit cells with cyclic wrapping.
    Clock: lambda counter (strictly increasing internal time).

    Proof basis for overall architecture:
        - Prop 0.0.XXb (Bootstrap Computability): framework is computable
        - Theorem 0.2.2 (Internal Time Emergence): lambda as execution clock
        - Def 0.1.1 (Stella Octangula): 8-vertex initial tape size
        - Def 0.1.2 (Three Color Fields): Z_3 trit data type

    Architectural note: The stella octangula has two disjoint tetrahedra
    (T+ and T-), but this interpreter flattens them into a single tape.
    The Stella Soup VM (soup.c) more faithfully models the T+/T- structure
    with two independent heads. See spec.md Section 7.3.
    """

    def __init__(self, tape_size=STELLA_VERTICES, max_tape=30000, strict=False):
        self.tape = [0] * tape_size
        self.max_tape = max_tape
        self.pointer = 0
        self.lambda_tick = 0
        self.strict = strict

        # I/O
        self.input_buffer = []
        self.output_buffer = []

        # Execution trace (for verbose mode)
        self.trace = []

    @property
    def cell(self):
        """Current cell value (Z_3 phase)."""
        return self.tape[self.pointer]

    @cell.setter
    def cell(self, value):
        """Set current cell, enforcing Z_3 constraint."""
        self.tape[self.pointer] = value % Z3_MODULUS

    def _tick(self, instruction, detail=""):
        """Advance lambda by one tick. Lambda is strictly monotonic.

        Proof: Prop 0.0.17c (Arrow of Time from Information Geometry)
        """
        self.lambda_tick += 1
        if self.trace is not None:
            self.trace.append({
                "lambda": self.lambda_tick,
                "instruction": instruction,
                "detail": detail,
                "pointer": self.pointer,
                "cell": self.cell,
                "tape": self.tape[:min(len(self.tape), 16)],
            })

    # --- Phase Operations ---

    def rotate(self):
        """Apply omega (forward phase rotation): cell = (cell + 1) mod 3.

        The single forward rotation, following R -> G -> B chirality.
        This is the ONLY rotation direction permitted by the arrow of time.

        Proof:
            - Definition 0.1.2: Three color fields with Z_3 phases
            - Theorem 2.2.4: R->G->B chirality selection (forward only)
            - Prop 0.0.17c: Arrow of time locks rotation direction
        """
        old = self.cell
        self.cell = old + 1
        self._tick("r", f"rotate: {old} -> {self.cell}")

    def double_rotate(self):
        """Apply omega^2 (two forward rotations): cell = (cell + 2) mod 3.

        NOT a backward rotation. omega^2 is a valid Z_3 group element
        reached by applying omega twice: omega * omega = omega^2.
        The result equals (cell - 1) mod 3, but the physical mechanism
        is two forward steps on the R -> G -> B cycle.

        Proof:
            - Prop 0.0.5a: Z_3 center structure (omega^2 is group inverse)
            - Z_3 group closure: omega * omega^2 = 1 (identity)
        """
        old = self.cell
        self.cell = old + 2
        self._tick("R", f"double_rotate: {old} -> {self.cell}")

    # --- Pointer Movement ---

    def advance(self):
        """Move pointer forward by one position.

        If at tape boundary, extend tape (new configuration becomes
        accessible as lambda evolves). At max tape size, wraps cyclically.

        This is a spatial operation — lambda still increases (Prop 0.0.17c).

        Note: Pointer movement is a computational primitive, not derived
        from Prop 0.0.17p's geodesics (which describe phase configuration
        space, not spatial memory). See spec.md Section 4.2.
        """
        self.pointer += 1
        if self.pointer >= len(self.tape):
            if len(self.tape) < self.max_tape:
                self.tape.append(0)
            else:
                self.pointer = 0  # Wrap on cyclic tape
        self._tick(">", f"advance -> pos {self.pointer}")

    def cycle(self):
        """Move pointer backward by one position (wraps cyclically).

        Equivalent to (N-1) forward advances on a cyclic tape, so this
        adds no computational power. Strict mode disables it.

        This is a spatial operation -- lambda still increases (Prop 0.0.17c).
        Moving the pointer backward is NOT time reversal.

        Note: This is a computational convenience, not derived from the
        proofs. See spec.md Section 4.2 for details.
        """
        if self.strict:
            raise SuperselectionError(
                "Strict mode: '<' (long geodesic) is disabled. "
                f"Use {len(self.tape) - 1} '>' operations instead "
                "(equivalent on cyclic tape)."
            )
        self.pointer = (self.pointer - 1) % len(self.tape)
        self._tick("<", f"cycle -> pos {self.pointer}")

    # --- I/O ---

    def observe(self):
        """Output current cell value (observer measurement).

        The internal observer applies M_obs to the current cell,
        producing a trit value. Subject to Z_3 superselection.

        Proof:
            - Definition 0.0.32: Internal Observer (M_obs map)
            - Prop 0.0.17a: Born rule from geodesic flow
        """
        self.output_buffer.append(self.cell)
        self._tick(".", f"observe: {self.cell}")

    def couple(self):
        """Read input into current cell (external coupling).

        Input is reduced mod 3, enforcing the Z_3 constraint.
        If no input available, cell is set to 0 (identity phase).

        Proof:
            - Definition 0.0.32: Internal Observer (observation map)
            - Z_3 constraint: all values reduced mod 3
        """
        if self.input_buffer:
            val = self.input_buffer.pop(0)
        else:
            val = 0
        old = self.cell
        self.cell = val
        self._tick(",", f"couple: {old} -> {self.cell}")

    # --- Execution ---

    def execute(self, program, input_data=None, max_steps=1_000_000):
        """Execute a StellaLang program.

        Each instruction advances lambda by one tick.

        Proof:
            - Prop 0.0.17l: omega = 220 MeV (natural tick frequency)
            - Theorem 0.2.2: lambda as internal time parameter

        Args:
            program: String of StellaLang instructions.
            input_data: Optional input string (each char reduced mod 3).
            max_steps: Maximum lambda-ticks before forced halt.

        Returns:
            List of output trit values.
        """
        if input_data is not None:
            self.input_buffer = [ord(c) % Z3_MODULUS for c in input_data]

        # Strip non-instructions (everything else is a comment)
        code = [c for c in program if c in INSTRUCTIONS]

        # Match brackets (superselection gates)
        bracket_map = _match_brackets(code)

        pc = 0
        while pc < len(code) and self.lambda_tick < max_steps:
            cmd = code[pc]

            if cmd == "r":
                self.rotate()
            elif cmd == "R":
                self.double_rotate()
            elif cmd == ">":
                self.advance()
            elif cmd == "<":
                self.cycle()
            elif cmd == ".":
                self.observe()
            elif cmd == ",":
                self.couple()
            elif cmd == "[":
                # Z_3 superselection gate: identity phase triggers skip
                # Proof: Prop 0.0.17h (Information Horizon Derivation)
                if self.cell == 0:
                    pc = bracket_map[pc]
                self._tick("[", f"gate: cell={self.cell}, {'skip' if self.cell == 0 else 'enter'}")
            elif cmd == "]":
                # Loop: re-execute at later lambda (NOT time reversal)
                # Proof: Prop 0.0.17h (gate), Prop 0.0.17c (lambda forward)
                if self.cell != 0:
                    pc = bracket_map[pc]
                self._tick("]", f"loop: cell={self.cell}, {'continue' if self.cell != 0 else 'exit'}")

            pc += 1

        return self.output_buffer

    def format_trace(self, max_lines=50):
        """Format execution trace for display."""
        lines = []
        lines.append(f"{'lambda':>6} | {'cmd':>3} | {'ptr':>3} | {'cell':>4} | {'tape':<24} | detail")
        lines.append("-" * 80)
        for entry in self.trace[:max_lines]:
            tape_str = " ".join(str(t) for t in entry["tape"])
            lines.append(
                f"{entry['lambda']:>6} | "
                f"  {entry['instruction']} | "
                f"{entry['pointer']:>3} | "
                f"{entry['cell']:>4} | "
                f"{tape_str:<24} | "
                f"{entry['detail']}"
            )
        if len(self.trace) > max_lines:
            lines.append(f"  ... ({len(self.trace) - max_lines} more ticks)")
        return "\n".join(lines)

    def stats(self):
        """Return execution statistics."""
        return {
            "lambda_ticks": self.lambda_tick,
            "tape_size": len(self.tape),
            "pointer": self.pointer,
            "output_length": len(self.output_buffer),
            "omega_MeV": OMEGA_MEV,
            "physical_time_seconds": self.lambda_tick * (2 * 3.14159265 / (OMEGA_MEV * 1e6 * 1.602e-19 / 1.055e-34)),
        }


def _match_brackets(code):
    """Match [ ] superselection gate pairs.

    Proof basis: Prop 0.0.17h (Information Horizon Derivation)
    The gate structure requires matched pairs -- unmatched gates
    would violate the self-consistency of the superselection mechanism.
    """
    stack = []
    bracket_map = {}
    for i, cmd in enumerate(code):
        if cmd == "[":
            stack.append(i)
        elif cmd == "]":
            if not stack:
                raise StellaError(f"Unmatched ']' at instruction {i}")
            j = stack.pop()
            bracket_map[j] = i
            bracket_map[i] = j
    if stack:
        raise StellaError(f"Unmatched '[' at instruction {stack[-1]}")
    return bracket_map


def phase_name(trit):
    """Map trit value to color field name."""
    return ["R (0)", "G (2pi/3)", "B (4pi/3)"][trit % Z3_MODULUS]


def main():
    parser = argparse.ArgumentParser(
        description="StellaLang interpreter: ternary language from Chiral Geometrogenesis",
        epilog="See spec.md for the full language specification and proof mappings.",
    )
    parser.add_argument("program", nargs="?", help="Program file (.stella)")
    parser.add_argument("-c", "--code", help="Inline program code")
    parser.add_argument("-i", "--input", help="Input string", default="")
    parser.add_argument(
        "-t", "--tape-size", type=int, default=STELLA_VERTICES,
        help=f"Initial tape size (default: {STELLA_VERTICES}, stella vertices)",
    )
    parser.add_argument(
        "-s", "--max-steps", type=int, default=1_000_000,
        help="Maximum lambda-ticks before halt (default: 1000000)",
    )
    parser.add_argument(
        "-v", "--verbose", action="store_true",
        help="Show execution trace (lambda-ticks, tape state)",
    )
    parser.add_argument(
        "--strict", action="store_true",
        help="Forward-only mode: disable '<' (long geodesic)",
    )
    parser.add_argument(
        "--raw", action="store_true",
        help="Output raw trit values separated by spaces",
    )
    parser.add_argument(
        "--phases", action="store_true",
        help="Output color field names instead of trit values",
    )

    args = parser.parse_args()

    # Load program
    if args.code:
        program = args.code
    elif args.program:
        with open(args.program, "r") as f:
            program = f.read()
    else:
        parser.print_help()
        return

    # Create VM and execute
    vm = StellaVM(tape_size=args.tape_size, strict=args.strict)

    try:
        output = vm.execute(program, input_data=args.input, max_steps=args.max_steps)
    except StellaError as e:
        print(f"StellaLang Error: {e}", file=sys.stderr)
        sys.exit(1)

    # Display output
    if args.phases:
        print(" ".join(phase_name(t) for t in output))
    elif args.raw:
        print(" ".join(str(t) for t in output))
    else:
        print("".join(str(t) for t in output))

    # Verbose: show trace and stats
    if args.verbose:
        print(f"\n--- Execution Trace ---")
        print(vm.format_trace())
        stats = vm.stats()
        print(f"\n--- Statistics ---")
        print(f"Lambda ticks:  {stats['lambda_ticks']}")
        print(f"Tape size:     {stats['tape_size']} cells")
        print(f"Final pointer: {stats['pointer']}")
        print(f"Output length: {stats['output_length']} trits")
        print(f"Clock freq:    omega = {stats['omega_MeV']} MeV")


if __name__ == "__main__":
    main()
