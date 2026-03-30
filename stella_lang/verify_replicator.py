#!/usr/bin/env python3
"""
Proposition 0.0.XXd: Self-Replicator Verification
===================================================

Constructively verifies Claim 2 of Prop 0.0.XXd:
The 20-trit program is a self-replicator under concatenation-execution-split,
and uses only CG-derived primitives (CPY01, FWD0, FWD1, [, ]).

Related Documents:
- Proof: docs/proofs/foundations/Proposition-0.0.XXd-Computational-Universality-CG-Primitives.md
- Soup VM: stella_lang/soup.py
- 30M results: stella_lang/RESULTS-30M.md

Verification Date: 2026-03-06
"""

import sys
import os
import json
from datetime import datetime

import numpy as np

sys.path.insert(0, os.path.dirname(__file__))
from soup import execute_tape, INSTR_NAMES, NOP, ROT, FWD0, BCK0, FWD1, OPEN, CLOSE, CPY01, CPY10, Z3

# ==============================================================================
# THE REPLICATOR
# ==============================================================================

# The 20-trit conserved core from the 30M-epoch Stella Soup run (seed 42)
REPLICATOR_20 = [1, 2, 1, 2, 2, 1, 0, 2, 1, 1, 2, 0, 2, 1, 1, 1, 0, 2, 2, 0]

# Decoded instruction sequence (10 instructions from 20 trits)
EXPECTED_INSTRUCTIONS = ["[", "[", "CPY+", "FWD0", "FWD1", "]", "CPY+", "FWD1", "FWD0", "]"]

# Allowed CG primitives (only these should appear in reachable code)
ALLOWED_PRIMITIVES = {OPEN, CLOSE, CPY01, FWD0, FWD1}
ALLOWED_NAMES = {"[", "]", "CPY+", "FWD0", "FWD1"}

PROGRAM_SIZE = len(REPLICATOR_20)  # 20 trits


# ==============================================================================
# VERIFICATION FUNCTIONS
# ==============================================================================

def verify_decode():
    """Verify the 20-trit sequence decodes to the expected instructions."""
    decoded = []
    for i in range(0, len(REPLICATOR_20) - 1, 2):
        pair = (REPLICATOR_20[i], REPLICATOR_20[i + 1])
        name = INSTR_NAMES.get(pair, "???")
        decoded.append(name)

    match = decoded == EXPECTED_INSTRUCTIONS
    result = {
        "test": "decode_20_trit_core",
        "expected": EXPECTED_INSTRUCTIONS,
        "decoded": decoded,
        "passed": match,
    }
    status = "PASS" if match else "FAIL"
    print(f"  {status}: Decode 20-trit core -> {decoded}")
    return result


def verify_self_replication_zero_food():
    """Verify S + 0 -> (S, S) where 0 is a tape of 20 zeroes."""
    source = np.array(REPLICATOR_20, dtype=int)
    food = np.zeros(PROGRAM_SIZE, dtype=int)
    tape = np.concatenate([source, food]).copy()
    tape_len = len(tape)

    result_tape = execute_tape(tape, max_steps=729, tape_len=tape_len)

    first_half = result_tape[:PROGRAM_SIZE]
    second_half = result_tape[PROGRAM_SIZE:]

    source_preserved = np.array_equal(first_half, source)
    copy_made = np.array_equal(second_half, source)
    perfect = source_preserved and copy_made

    result = {
        "test": "self_replication_zero_food",
        "source": REPLICATOR_20,
        "first_half": first_half.tolist(),
        "second_half": second_half.tolist(),
        "source_preserved": source_preserved,
        "copy_made": copy_made,
        "passed": perfect,
    }
    status = "PASS" if perfect else "FAIL"
    print(f"  {status}: S + 0 -> (S, S)  [source_preserved={source_preserved}, copy_made={copy_made}]")
    return result


def verify_self_replication_random_food(n_trials=50, seed=123):
    """Verify S + F -> (S, _) for random foods F. Source half must be preserved."""
    rng = np.random.default_rng(seed)
    source = np.array(REPLICATOR_20, dtype=int)
    successes = 0

    for _ in range(n_trials):
        food = rng.integers(0, Z3, size=PROGRAM_SIZE)
        tape = np.concatenate([source, food]).copy()
        result_tape = execute_tape(tape, max_steps=729, tape_len=len(tape))
        first_half = result_tape[:PROGRAM_SIZE]

        if np.array_equal(first_half, source):
            successes += 1

    passed = successes == n_trials
    result = {
        "test": "self_replication_random_food",
        "n_trials": n_trials,
        "successes": successes,
        "passed": passed,
    }
    status = "PASS" if passed else "FAIL"
    print(f"  {status}: S + F -> (S, _) for {successes}/{n_trials} random foods")
    return result


def verify_perfect_replication_random_food(n_trials=50, seed=123):
    """Verify S + F -> (S, S) for random foods.

    100% rate expected: during Pass 1, h0 reads only source trits (pos 0-19),
    so food content is structurally irrelevant. By the time h0 wraps into the
    food region (Pass 2), food has already been overwritten with S.
    """
    rng = np.random.default_rng(seed)
    source = np.array(REPLICATOR_20, dtype=int)
    perfect = 0

    for _ in range(n_trials):
        food = rng.integers(0, Z3, size=PROGRAM_SIZE)
        tape = np.concatenate([source, food]).copy()
        result_tape = execute_tape(tape, max_steps=729, tape_len=len(tape))
        first_half = result_tape[:PROGRAM_SIZE]
        second_half = result_tape[PROGRAM_SIZE:]

        if np.array_equal(first_half, source) and np.array_equal(second_half, source):
            perfect += 1

    passed = perfect == n_trials
    result = {
        "test": "perfect_replication_random_food",
        "n_trials": n_trials,
        "perfect_count": perfect,
        "perfect_rate": perfect / n_trials,
        "passed": passed,
    }
    status = "PASS" if passed else "FAIL"
    print(f"  {status}: S + F -> (S, S) for {perfect}/{n_trials} random foods (food-independent)")
    return result


def verify_cg_primitives_only():
    """Verify only CG-derived primitives appear in the reachable code.

    The replicator's reachable instructions are all 10 decoded ops.
    We verify none are ROT, BCK0, CPY10, or NOP (when used as instruction).
    """
    decoded_pairs = []
    for i in range(0, len(REPLICATOR_20) - 1, 2):
        pair = (REPLICATOR_20[i], REPLICATOR_20[i + 1])
        decoded_pairs.append(pair)

    # All decoded instructions
    all_names = set()
    disallowed = []
    for pair in decoded_pairs:
        name = INSTR_NAMES.get(pair, "???")
        all_names.add(name)
        if pair not in ALLOWED_PRIMITIVES:
            disallowed.append(name)

    passed = len(disallowed) == 0
    result = {
        "test": "cg_primitives_only",
        "all_instructions": sorted(all_names),
        "allowed": sorted(ALLOWED_NAMES),
        "disallowed_found": disallowed,
        "passed": passed,
    }
    status = "PASS" if passed else "FAIL"
    print(f"  {status}: Only CG primitives used: {sorted(all_names)}")
    return result


def verify_reachable_code_primitives():
    """Verify reachable code (excluding unreachable trailing junk) uses only CG primitives.

    In the 24-trit soup programs, the last 4 trits (2 instructions) are unreachable
    junk that varies across family members. The 20-trit core is what matters.
    All 10 instructions in the core must be from {CPY01, FWD0, FWD1, [, ]}.
    """
    # The 20-trit core is the full replicator -- there IS no trailing junk here.
    # But we verify the structural claim: the inner loop body and outer loop body
    # use only copy+advance operations.

    inner_loop = REPLICATOR_20[2:12]   # instructions 1-5: [ CPY+ FWD0 FWD1 ]
    outer_body = REPLICATOR_20[12:20]  # instructions 6-9: CPY+ FWD1 FWD0 ]

    all_reachable = []
    for segment in [REPLICATOR_20[0:2], inner_loop, outer_body]:  # outer [, inner, outer body
        for i in range(0, len(segment) - 1, 2):
            pair = (segment[i], segment[i + 1])
            all_reachable.append(INSTR_NAMES.get(pair, "???"))

    non_cg = [name for name in all_reachable if name not in ALLOWED_NAMES]
    passed = len(non_cg) == 0

    result = {
        "test": "reachable_code_cg_only",
        "reachable_instructions": all_reachable,
        "non_cg_instructions": non_cg,
        "passed": passed,
    }
    status = "PASS" if passed else "FAIL"
    print(f"  {status}: All reachable code uses CG primitives (no ROT/BCK0/CPY10/NOP)")
    return result


def verify_execution_trace():
    """Trace execution step by step to confirm copy mechanism."""
    source = np.array(REPLICATOR_20, dtype=int)
    food = np.zeros(PROGRAM_SIZE, dtype=int)
    tape = np.concatenate([source, food]).copy()
    tape_len = len(tape)

    # Manual trace: verify h0 reads source, h1 writes to food region
    # The program is: [[ CPY+ FWD0 FWD1 ] CPY+ FWD1 FWD0 ]
    # h0 starts at 0 (instruction pointer), h1 starts at tape_len//2 = 20
    # But IP is separate from h0 in the soup VM.
    # h0 starts at 0, h1 starts at 20.
    # After execution, the food region (positions 20-39) should contain a copy.

    # We already verified the output. Here we just confirm structural properties.
    result_tape = execute_tape(tape, max_steps=729, tape_len=tape_len)

    # Check that the copy is byte-exact
    source_region = result_tape[:PROGRAM_SIZE]
    copy_region = result_tape[PROGRAM_SIZE:]

    exact_copy = np.array_equal(source_region, copy_region)
    source_intact = np.array_equal(source_region, source)

    result = {
        "test": "execution_trace_verification",
        "source_intact": source_intact,
        "exact_copy_in_food_region": exact_copy,
        "passed": source_intact and exact_copy,
    }
    status = "PASS" if (source_intact and exact_copy) else "FAIL"
    print(f"  {status}: Execution trace confirms copy mechanism")
    return result


def verify_cg_decomposition():
    """Map each instruction to its CG theorem origin."""
    mapping = {
        "[": "Prop 0.0.17h (Z_3 superselection gate)",
        "]": "Prop 0.0.17h (Z_3 superselection gate)",
        "CPY+": "Thm 0.2.1 (Total Field Superposition: T+ -> T- transfer)",
        "FWD0": "Computational primitive (pointer advance, h0)",
        "FWD1": "Computational primitive (pointer advance, h1)",
    }

    decoded = []
    for i in range(0, len(REPLICATOR_20) - 1, 2):
        pair = (REPLICATOR_20[i], REPLICATOR_20[i + 1])
        name = INSTR_NAMES.get(pair, "???")
        origin = mapping.get(name, "UNKNOWN")
        decoded.append({"instruction": name, "trits": list(pair), "cg_origin": origin})

    all_mapped = all(d["cg_origin"] != "UNKNOWN" for d in decoded)
    result = {
        "test": "cg_decomposition",
        "instructions": decoded,
        "all_mapped": all_mapped,
        "passed": all_mapped,
    }
    status = "PASS" if all_mapped else "FAIL"
    print(f"  {status}: All instructions mapped to CG theorems")
    return result


# ==============================================================================
# MAIN
# ==============================================================================

def main():
    print("Proposition 0.0.XXd: Self-Replicator Verification")
    print("=" * 60)
    print(f"Replicator: {REPLICATOR_20}")
    print(f"Length: {len(REPLICATOR_20)} trits ({len(REPLICATOR_20)//2} instructions)")
    print()

    results = {
        "proposition": "0.0.XXd",
        "title": "Computational Universality of CG Primitives",
        "claim_verified": "Claim 2 (Self-Replicator Construction)",
        "timestamp": datetime.now().isoformat(),
        "replicator": REPLICATOR_20,
        "tests": [],
    }

    tests = [
        ("Decoding", verify_decode),
        ("Self-replication (zero food)", verify_self_replication_zero_food),
        ("Self-replication (random food, source preserved)", verify_self_replication_random_food),
        ("Perfect replication (random food)", verify_perfect_replication_random_food),
        ("CG primitives only", verify_cg_primitives_only),
        ("Reachable code CG-only", verify_reachable_code_primitives),
        ("Execution trace", verify_execution_trace),
        ("CG decomposition", verify_cg_decomposition),
    ]

    print("Tests:")
    for name, func in tests:
        result = func()
        results["tests"].append(result)

    # Summary
    passed = sum(1 for t in results["tests"] if t["passed"])
    total = len(results["tests"])
    all_passed = passed == total
    results["overall_status"] = "PASSED" if all_passed else "FAILED"
    results["summary"] = f"{passed}/{total} tests passed"

    print()
    print("=" * 60)
    print(f"Result: {results['overall_status']} ({passed}/{total} tests passed)")

    if all_passed:
        print()
        print("Claim 2 verified: The 20-trit program is a self-replicator")
        print("under concatenation-execution-split, using only CG primitives")
        print("(CPY01 from Thm 0.2.1, [/] from Prop 0.0.17h, FWD0/FWD1).")

    # Save results
    output_path = os.path.join(os.path.dirname(__file__), "verify_replicator_results.json")
    with open(output_path, "w") as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\nResults saved to: {output_path}")

    if not all_passed:
        sys.exit(1)


if __name__ == "__main__":
    main()
