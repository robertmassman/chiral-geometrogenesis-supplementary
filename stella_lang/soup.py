#!/usr/bin/env python3
"""
Stella Soup: Computational Life on a Ternary Substrate
======================================================
Inspired by "Computational Life" (Aguera y Arcas et al., 2024),
adapted to StellaLang's ternary (Z_3) building blocks.

Instead of BFF (extended Brainfuck with 256-value bytes), we use an
extended StellaLang with trit cells (3 values) and two tape heads.

The stella octangula's two interpenetrating tetrahedra (T+ and T-)
provide the physical basis for the two heads:
  - head0 (T+): instruction/read head
  - head1 (T-): write head
  - Copy operations transfer information between T+ and T-

Proof basis:
  - Def 0.1.1:  Stella octangula = two disjoint tetrahedra (T+, T-)
  - Def 0.1.2:  Three color fields -> trit data type {0, 1, 2}
  - Thm 0.2.1:  Field superposition -> info transfer between heads
  - Prop 0.0.17h: Z_3 superselection -> loop gate mechanism
  - Head movement: pointer advance (computational primitive)

Reference:
  Aguera y Arcas et al., "Computational Life: How Well-formed,
  Self-replicating Programs Emerge from Simple Interaction" (2024)
  arXiv:2406.19108

Usage:
  python3 soup.py                        # Default simulation
  python3 soup.py --epochs 5000          # More epochs
  python3 soup.py --soup-size 8192       # Larger soup
  python3 soup.py --no-mutations         # No background mutations
  python3 soup.py --seed 42 --verbose    # Reproducible + verbose
"""

import argparse
import sys
import time
import zlib
from collections import Counter

import numpy as np

# === TERNARY CONSTANTS ===
# Proof: Prop 0.0.XXa (First Stable Principle) -> N=3 is minimal stable
Z3 = 3

# === INSTRUCTION SET ===
# Each instruction = pair of trits (9 possible codes).
# Instructions and data coexist on the same tape (like BFF).
# Proof: each instruction maps to a CG theorem.

NOP   = (0, 0)  # No operation / zero for loop exit
ROT   = (0, 1)  # tape[h0] = (tape[h0]+1) % 3    Def 0.1.2 (phase rotate)
FWD0  = (0, 2)  # h0 += 1                          advance h0
BCK0  = (1, 0)  # h0 -= 1                          retreat h0 (cyclic)
FWD1  = (1, 1)  # h1 += 1                          Def 0.1.1 (T- traversal)
OPEN  = (1, 2)  # if tape[h0]==0: jump to CLOSE    Prop 0.0.17h (gate)
CLOSE = (2, 0)  # if tape[h0]!=0: jump to OPEN     Prop 0.0.17h
CPY01 = (2, 1)  # tape[h1] = tape[h0]              Thm 0.2.1 (T+ -> T-)
CPY10 = (2, 2)  # tape[h0] = tape[h1]              Thm 0.2.1 (T- -> T+)

INSTR_NAMES = {
    NOP: "NOP", ROT: "ROT", FWD0: "FWD0", BCK0: "BCK0",
    FWD1: "FWD1", OPEN: "[", CLOSE: "]", CPY01: "CPY+", CPY10: "CPY-",
}


def execute_tape(tape, max_steps, tape_len):
    """Execute a program on the tape. Returns modified tape.

    The instruction pointer reads trit pairs as instructions.
    head0 and head1 operate on the same tape.
    All positions are cyclic (torus topology).

    This is the core VM, kept tight for performance.
    """
    ip = 0      # Instruction pointer (advances by 2 per instruction)
    h0 = 0      # Head 0 (T+ tetrahedron)
    h1 = tape_len // 2  # Head 1 (T- tetrahedron), starts at midpoint
    steps = 0

    while steps < max_steps and ip + 1 < tape_len:
        high = tape[ip]
        low = tape[ip + 1]

        if high == 0:
            if low == 0:
                pass  # NOP
            elif low == 1:
                # ROT: tape[h0] = (tape[h0] + 1) % 3
                tape[h0] = (tape[h0] + 1) % Z3
            else:  # low == 2
                # FWD0: h0 += 1
                h0 = (h0 + 1) % tape_len

        elif high == 1:
            if low == 0:
                # BCK0: h0 -= 1
                h0 = (h0 - 1) % tape_len
            elif low == 1:
                # FWD1: h1 += 1
                h1 = (h1 + 1) % tape_len
            else:  # low == 2
                # OPEN [: if tape[h0] == 0, jump past matching ]
                if tape[h0] == 0:
                    depth = 1
                    pos = ip + 2
                    while depth > 0 and pos + 1 < tape_len:
                        if tape[pos] == 1 and tape[pos + 1] == 2:
                            depth += 1
                        elif tape[pos] == 2 and tape[pos + 1] == 0:
                            depth -= 1
                        pos += 2
                    if depth == 0:
                        ip = pos - 2
                    # Unmatched [ -> treat as NOP (skip)

        elif high == 2:
            if low == 0:
                # CLOSE ]: if tape[h0] != 0, jump back to matching [
                if tape[h0] != 0:
                    depth = 1
                    pos = ip - 2
                    while depth > 0 and pos >= 0:
                        if tape[pos] == 2 and tape[pos + 1] == 0:
                            depth += 1
                        elif tape[pos] == 1 and tape[pos + 1] == 2:
                            depth -= 1
                        pos -= 2
                    if depth == 0:
                        ip = pos + 2
                    # Unmatched ] -> treat as NOP (skip)
            elif low == 1:
                # CPY01: tape[h1] = tape[h0]  (T+ -> T-)
                tape[h1] = tape[h0]
            else:  # low == 2
                # CPY10: tape[h0] = tape[h1]  (T- -> T+)
                tape[h0] = tape[h1]

        ip += 2
        steps += 1

    return tape


class StellaSoup:
    """Primordial soup simulation for ternary computational life.

    Methodology (adapted from Aguera y Arcas et al. 2024):
    - Soup of N programs, each P trits long, randomly initialized
    - Each epoch: random pairs interact via concatenation + execution
    - Self-replicators may emerge from pure interaction dynamics
    - Optional background mutations (cosmic rays)

    CG connection: the soup is a population of field configurations
    on the stella octangula boundary. Interactions are collisions
    between configurations. Self-replicators are autocatalytic
    fixed points -- the computational analog of the bootstrap
    (Prop 0.0.XXb: Bootstrap Computability).
    """

    def __init__(self, soup_size=4096, program_size=24,
                 max_steps=729, mutation_rate=0.001, seed=None):
        self.rng = np.random.default_rng(seed)
        self.soup_size = soup_size
        self.program_size = program_size
        self.max_steps = max_steps
        self.mutation_rate = mutation_rate

        # Initialize soup with random trits (uniform over Z_3)
        self.soup = self.rng.integers(0, Z3, size=(soup_size, program_size))

        self.epoch = 0
        self.history = []
        self.replicator_log = []

    def interact(self, idx_a, idx_b):
        """Interact two programs: concatenate, execute, split.

        Equation (3) from the paper:
          A + B -> split(exec(AB)) = A' + B'

        This is an irreversible chemical reaction where order matters.
        Programs modify themselves and each other via shared tape.
        """
        # Concatenate into a single tape
        tape = np.concatenate([self.soup[idx_a], self.soup[idx_b]]).copy()
        tape_len = len(tape)

        # Execute
        tape = execute_tape(tape, self.max_steps, tape_len)

        # Split back
        self.soup[idx_a] = tape[:self.program_size]
        self.soup[idx_b] = tape[self.program_size:]

    def mutate(self):
        """Apply random background mutations (cosmic rays).

        Each trit has mutation_rate probability of being replaced
        by a uniformly random trit value.
        """
        if self.mutation_rate <= 0:
            return
        mask = self.rng.random(self.soup.shape) < self.mutation_rate
        n_mutations = mask.sum()
        if n_mutations > 0:
            self.soup[mask] = self.rng.integers(0, Z3, size=n_mutations)

    def compute_metrics(self):
        """Compute complexity metrics for the current soup state."""
        # Unique programs
        tuples = [tuple(p) for p in self.soup]
        counts = Counter(tuples)
        unique = len(counts)
        top_program, top_count = counts.most_common(1)[0]

        # Compression ratio (approximation of Kolmogorov complexity)
        flat = bytes(self.soup.flatten().tolist())
        compressed_size = len(zlib.compress(flat, level=6))
        raw_size = len(flat)
        compression_ratio = compressed_size / raw_size

        # Trit distribution entropy
        all_trits = self.soup.flatten()
        trit_counts = np.bincount(all_trits, minlength=Z3).astype(float)
        trit_probs = trit_counts / trit_counts.sum()
        trit_entropy = -sum(
            p * np.log2(p) for p in trit_probs if p > 0
        )

        return {
            "epoch": self.epoch,
            "unique_programs": unique,
            "top_count": top_count,
            "top_program": list(top_program),
            "compression_ratio": round(compression_ratio, 4),
            "trit_entropy": round(trit_entropy, 4),
        }

    def check_self_replicators(self, sample_size=200):
        """Test programs for self-replication.

        A program S is a self-replicator if:
          S + F -> split(exec(SF)) = (S, S)
        for at least some food F.

        We test against random food, which is the standard test
        from the paper.
        """
        indices = self.rng.choice(self.soup_size,
                                  size=min(sample_size, self.soup_size),
                                  replace=False)
        replicators = []

        for idx in indices:
            program = self.soup[idx].copy()

            # Test with zero food (blank tape)
            food_zero = np.zeros(self.program_size, dtype=int)
            tape = np.concatenate([program, food_zero]).copy()
            result = execute_tape(tape, self.max_steps, len(tape))
            a = result[:self.program_size]
            b = result[self.program_size:]

            if np.array_equal(a, program) and np.array_equal(b, program):
                replicators.append(("perfect", idx, program.copy()))
                continue

            # Test with random food
            food_rand = self.rng.integers(0, Z3, size=self.program_size)
            tape = np.concatenate([program, food_rand]).copy()
            result = execute_tape(tape, self.max_steps, len(tape))
            a = result[:self.program_size]
            b = result[self.program_size:]

            if np.array_equal(a, program) and np.array_equal(b, program):
                replicators.append(("perfect", idx, program.copy()))
            elif np.array_equal(a, program) or np.array_equal(b, program):
                replicators.append(("partial", idx, program.copy()))

        return replicators

    def run_epoch(self):
        """Run one epoch: N/2 random pair interactions + mutations."""
        n_interactions = self.soup_size // 2

        for _ in range(n_interactions):
            a, b = self.rng.choice(self.soup_size, size=2, replace=False)
            self.interact(a, b)

        self.mutate()
        self.epoch += 1

    def run(self, epochs, log_interval=100, check_interval=500, verbose=False):
        """Run the primordial soup simulation.

        Args:
            epochs: Number of epochs to run
            log_interval: Epochs between metric logging
            check_interval: Epochs between self-replicator checks
            verbose: Print detailed information
        """
        start_time = time.time()

        print(f"Stella Soup: Ternary Computational Life Simulation")
        print(f"=" * 60)
        print(f"Soup size:     {self.soup_size} programs")
        print(f"Program size:  {self.program_size} trits ({self.program_size // 2} instruction pairs)")
        print(f"Max steps:     {self.max_steps} per interaction")
        print(f"Mutation rate: {self.mutation_rate}")
        print(f"Epochs:        {epochs}")
        print(f"=" * 60)
        print()
        print(f"{'Epoch':>6} | {'Unique':>6} | {'Top':>5} | {'Compress':>8} | {'H(trit)':>7} | Notes")
        print("-" * 70)

        for e in range(epochs):
            self.run_epoch()

            if self.epoch % log_interval == 0:
                metrics = self.compute_metrics()
                self.history.append(metrics)

                notes = ""

                # Check for self-replicators at check_interval
                if self.epoch % check_interval == 0:
                    replicators = self.check_self_replicators()
                    if replicators:
                        perfect = [r for r in replicators if r[0] == "perfect"]
                        partial = [r for r in replicators if r[0] == "partial"]
                        if perfect:
                            notes = f"REPLICATORS: {len(perfect)} perfect"
                            self.replicator_log.append(
                                (self.epoch, perfect[0][2].tolist())
                            )
                        elif partial:
                            notes = f"partial: {len(partial)}"

                print(
                    f"{metrics['epoch']:>6} | "
                    f"{metrics['unique_programs']:>6} | "
                    f"{metrics['top_count']:>5} | "
                    f"{metrics['compression_ratio']:>8.4f} | "
                    f"{metrics['trit_entropy']:>7.4f} | "
                    f"{notes}"
                )

                if verbose and notes.startswith("REPLICATORS"):
                    rep = self.replicator_log[-1][1]
                    print(f"  -> First replicator: {rep}")
                    self.print_program(rep)

        elapsed = time.time() - start_time
        print(f"\nCompleted {epochs} epochs in {elapsed:.1f}s")
        print(f"({elapsed / epochs * 1000:.1f}ms per epoch)")

        # Final report
        self.report()

    def report(self):
        """Print final simulation report."""
        print(f"\n{'=' * 60}")
        print("Final Report")
        print(f"{'=' * 60}")

        metrics = self.compute_metrics()
        print(f"Final unique programs: {metrics['unique_programs']}")
        print(f"Most common program count: {metrics['top_count']}")
        print(f"Compression ratio: {metrics['compression_ratio']:.4f}")
        print(f"Trit entropy: {metrics['trit_entropy']:.4f} (max = {np.log2(Z3):.4f})")

        if self.replicator_log:
            print(f"\nSelf-replicators found at epochs: "
                  f"{[e for e, _ in self.replicator_log]}")
            print(f"First replicator:")
            self.print_program(self.replicator_log[0][1])
        else:
            print(f"\nNo perfect self-replicators detected.")
            print("(Try more epochs, larger soup, or different parameters)")

        # Check for dominant programs (potential replicators not caught by sampling)
        tuples = [tuple(p) for p in self.soup]
        counts = Counter(tuples)
        top5 = counts.most_common(5)
        if top5[0][1] > 10:
            print(f"\nTop 5 most common programs:")
            for prog, count in top5:
                pct = 100 * count / self.soup_size
                print(f"  count={count:5d} ({pct:5.1f}%): {[int(t) for t in prog]}")

        # CG connection
        print(f"\n{'=' * 60}")
        print("Connection to Chiral Geometrogenesis")
        print(f"{'=' * 60}")
        print("""
This simulation tests whether self-replicating programs emerge
from random ternary (Z_3) interactions on the stella octangula.

The building blocks are the same as the CG framework:
  - Trit cells from Z_3 center symmetry (Def 0.1.2)
  - Two heads from the two tetrahedra T+, T- (Def 0.1.1)
  - Copy = information transfer between T+ and T- (Thm 0.2.1)
  - Loops = Z_3 superselection gates (Prop 0.0.17h)
  - Head movement = pointer advance (computational primitive)

If self-replicators emerge, this demonstrates that the CG
building blocks are sufficient not just for universal computation
(StellaLang is Turing-complete) but for computational LIFE --
self-organizing, self-replicating structures arising from
pure Z_3 interactions with no fitness landscape.

This connects to:
  - Prop 0.0.XXb (Bootstrap Computability): the framework computes
  - Def 0.0.32 (Internal Observer): self-modeling subsystems
  - Thm 0.0.19 (Self-Reference Uniqueness): unique fixed points
""")

    @staticmethod
    def print_program(trits):
        """Pretty-print a program as instructions."""
        parts = []
        for i in range(0, len(trits) - 1, 2):
            pair = (trits[i], trits[i + 1])
            name = INSTR_NAMES.get(pair, "???")
            parts.append(name)
        print(f"  Instructions: {' '.join(parts)}")
        print(f"  Raw trits:    {trits}")


def main():
    parser = argparse.ArgumentParser(
        description="Stella Soup: ternary computational life simulation",
    )
    parser.add_argument("--soup-size", type=int, default=4096,
                        help="Number of programs in soup (default: 4096)")
    parser.add_argument("--program-size", type=int, default=24,
                        help="Trits per program (default: 24)")
    parser.add_argument("--max-steps", type=int, default=729,
                        help="Max execution steps per interaction (default: 729)")
    parser.add_argument("--mutation-rate", type=float, default=0.001,
                        help="Per-trit mutation probability (default: 0.001)")
    parser.add_argument("--no-mutations", action="store_true",
                        help="Disable background mutations")
    parser.add_argument("--epochs", type=int, default=2000,
                        help="Number of epochs to run (default: 2000)")
    parser.add_argument("--log-interval", type=int, default=100,
                        help="Epochs between logging (default: 100)")
    parser.add_argument("--check-interval", type=int, default=500,
                        help="Epochs between replicator checks (default: 500)")
    parser.add_argument("--seed", type=int, default=None,
                        help="Random seed for reproducibility")
    parser.add_argument("--verbose", action="store_true",
                        help="Print detailed information")

    args = parser.parse_args()

    mutation_rate = 0.0 if args.no_mutations else args.mutation_rate

    soup = StellaSoup(
        soup_size=args.soup_size,
        program_size=args.program_size,
        max_steps=args.max_steps,
        mutation_rate=mutation_rate,
        seed=args.seed,
    )

    soup.run(
        epochs=args.epochs,
        log_interval=args.log_interval,
        check_interval=args.check_interval,
        verbose=args.verbose,
    )


if __name__ == "__main__":
    main()
