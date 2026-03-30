#!/usr/bin/env python3
"""
StellaLang Example Programs
============================
Each example demonstrates a feature of StellaLang and maps it
to the underlying CG proof that grounds the operation.

Run: python3 examples.py
"""

from interpreter import StellaVM, phase_name


def run_example(name, code, description, proof_basis, input_data=None,
                tape_size=8, verbose=True):
    """Run a StellaLang example with explanation."""
    print(f"\n{'='*60}")
    print(f"Example: {name}")
    print(f"{'='*60}")
    print(f"Code:    {code}")
    print(f"Purpose: {description}")
    print(f"Proofs:  {proof_basis}")
    if input_data:
        print(f"Input:   {input_data!r}")

    vm = StellaVM(tape_size=tape_size)
    output = vm.execute(code, input_data=input_data, max_steps=10000)

    print(f"Output:  {' '.join(str(t) for t in output)}")
    print(f"Phases:  {' '.join(phase_name(t) for t in output)}")
    print(f"Lambda:  {vm.lambda_tick} ticks")

    if verbose and vm.trace:
        print(f"\nTrace (first 20 ticks):")
        print(vm.format_trace(max_lines=20))

    return output


def main():
    print("StellaLang Examples")
    print("A ternary programming language from Chiral Geometrogenesis")
    print("Every operation grounded in proven theorems.")

    # --- Example 1: Three Phases ---
    run_example(
        name="Three Phases (Z_3 Cycle)",
        code="r.r.r.",
        description=(
            "Rotates through all three Z_3 phases and observes each. "
            "Demonstrates the R -> G -> B -> R cycle."
        ),
        proof_basis="Def 0.1.2 (Three Color Fields), Thm 2.2.4 (Chirality Selection)",
    )

    # --- Example 2: Double Rotation ---
    run_example(
        name="Double Rotation (omega^2)",
        code="r.R.R.R.",
        description=(
            "Start at 0, rotate to 1, then apply omega^2 three times. "
            "Shows omega^2 is two forward steps (1->0->2->1), not backward."
        ),
        proof_basis="Prop 0.0.5a (Z_3 Center), omega^2 = forward twice",
    )

    # --- Example 3: Write to Adjacent Cell ---
    run_example(
        name="Write Adjacent Cell",
        code="rr>r.",
        description=(
            "Set cell 0 to 2 (two rotations), advance pointer, "
            "rotate cell 1 once, observe. Demonstrates pointer movement."
        ),
        proof_basis="Def 0.1.2 (phase rotation), pointer advance (computational primitive)",
    )

    # --- Example 4: Simple Loop ---
    run_example(
        name="Countdown Loop",
        code="rr[.R]",
        description=(
            "Set cell to 2, then loop: observe, double-rotate (decrement). "
            "Loop exits when cell reaches 0 (identity phase). "
            "Output: 2, 1 (two observations before hitting 0)."
        ),
        proof_basis=(
            "Prop 0.0.17h (Z_3 Superselection Gate), "
            "Prop 0.0.17c (lambda forward during loop)"
        ),
    )

    # --- Example 5: Long Geodesic (Torus Wrap) ---
    run_example(
        name="Pointer Retreat (Cyclic Wrapping)",
        code="rr>rr>rr<.",
        description=(
            "Set cells 0,1,2 to value 2 each, then use '<' (retreat) "
            "to return to cell 1 and observe. Demonstrates cyclic wrapping: "
            "'<' at position 2 goes to position 1."
        ),
        proof_basis="Cyclic wrapping (computational convention), Prop 0.0.17c (lambda still forward)",
    )

    # --- Example 6: Copy Cell ---
    run_example(
        name="Copy Cell (Destructive)",
        code="rr[>r<R]>.",
        description=(
            "Copy the value of cell 0 to cell 1. Loop transfers one "
            "rotation at a time: for each unit in cell 0, increment cell 1 "
            "and double-rotate cell 0. Cell 0 ends at 0, cell 1 has the copy."
        ),
        proof_basis=(
            "Def 0.1.2 (phase rotation), "
            "Prop 0.0.17h (gate on zero)"
        ),
    )

    # --- Example 7: Ternary Addition ---
    run_example(
        name="Ternary Addition (mod 3)",
        code="rr>r<[>r<R]>.",
        description=(
            "Add cell 0 (=2) and cell 1 (=1): result in cell 1. "
            "Transfer loop moves value from cell 0 to cell 1 by "
            "rotating cell 1 up and cell 0 down. Result: (2+1) mod 3 = 0."
        ),
        proof_basis=(
            "Z_3 group addition (Def 0.1.2), "
            "Superselection gate (Prop 0.0.17h)"
        ),
    )

    # --- Example 8: Initialize All Stella Vertices ---
    run_example(
        name="Initialize Stella Vertices",
        code="r>rr>r>rr>r>rr>r>rr",
        description=(
            "Set all 8 cells (stella octangula vertices) to alternating "
            "values 1 and 2, demonstrating the full initial memory space. "
            "Pattern: R=1, G=2, B=1, W=2, R_bar=1, G_bar=2, B_bar=1, W_bar=2"
        ),
        proof_basis="Def 0.1.1 (Stella Octangula: 8 vertices = 4+4 from T+ and T-)",
        verbose=False,
    )

    # --- Example 9: Strict Mode Demo ---
    print(f"\n{'='*60}")
    print(f"Example: Strict Mode (Forward-Only)")
    print(f"{'='*60}")
    print(f"Code:    rr>>>>>>>.")
    print(f"Purpose: In strict mode, reach 'previous' cell via 7 forward steps")
    print(f"         on 8-cell cyclic tape (retreat = 7 advances)")
    print(f"Proofs:  Arrow of time (Prop 0.0.17c): no '<' needed")

    vm = StellaVM(tape_size=8, strict=True, max_tape=8)
    # Set cell 0 to 2, then advance 8 times (wraps back to cell 0 on cyclic tape)
    output = vm.execute("rr>>>>>>>>.", max_steps=10000)
    print(f"Output:  {' '.join(str(t) for t in output)}")
    print(f"Lambda:  {vm.lambda_tick} ticks")
    print(f"Pointer: {vm.pointer} (back at cell 0 after 8 advances on 8-cell tape)")
    print(f"Note:    8 advances wraps back to cell 0 (value 2) -- cyclic wrapping")
    print(f"         This is the strict-mode equivalent of '<' without any reversal")

    # --- Summary ---
    print(f"\n{'='*60}")
    print("Summary: Proof-Operation Mapping")
    print(f"{'='*60}")
    print("""
| Instruction | Operation           | Grounding                         |
|-------------|---------------------|-----------------------------------|
| r           | Rotate (+1 mod 3)   | (P) Def 0.1.2, Thm 2.2.4        |
| R           | Double Rotate       | (P) Prop 0.0.5a (Z_3 closure)   |
|             | (+2 mod 3)          |                                   |
| >           | Advance pointer     | (M) computational primitive       |
| <           | Retreat pointer     | (M) convenience (= N-1 advances) |
| [           | Superselection open  | (P) Prop 0.0.17h (Info Horizon)  |
| ]           | Superselection close | (P) Prop 0.0.17h + 0.0.17c      |
| .           | Observe             | (P) Def 0.0.32 (Internal Observer)|
| ,           | Couple              | (P) Def 0.0.32 (Observation Map) |
|-------------|---------------------|-----------------------------------|
| clock tick  | lambda += 1         | (P) Thm 0.2.2, Prop 0.0.17l     |
| trit cell   | {0, 1, 2}           | (P) Def 0.1.2, Prop 0.0.XXa     |
| 8-cell tape | stella vertices     | (P) Def 0.1.1 (Stella Octangula) |
| cyclic wrap | ptr % tape_length   | (M) computational convention      |

(P) = Proof-grounded, (M) = Proof-motivated design choice
""")


if __name__ == "__main__":
    main()
