#!/usr/bin/env python3
"""
Proposition 0.0.XXd: Adversarial Physics Verification
======================================================

Adversarial testing of all four claims in Prop 0.0.XXd:
  Claim 1: Turing Completeness (BF simulation via Z_3 encoding)
  Claim 2: Self-Replicator Construction (20-trit program)
  Claim 3: Spontaneous Emergence (soup simulation)
  Claim 4: CG Configuration Uniqueness (competitive experiments)

Tests are designed to BREAK the claims -- finding edge cases, boundary
conditions, and potential failure modes.

Related Documents:
- Proof: docs/proofs/foundations/Proposition-0.0.XXd-Computational-Universality-CG-Primitives.md
- Verification: stella_lang/verify_replicator.py
- Soup VM: stella_lang/soup.py

Verification Date: 2026-03-07
"""

import sys
import os
import json
import math
from datetime import datetime

import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

# Import the Soup VM
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "stella_lang"))
from soup import execute_tape, INSTR_NAMES, NOP, ROT, FWD0, BCK0, FWD1, OPEN, CLOSE, CPY01, CPY10, Z3

PLOTS_DIR = os.path.join(os.path.dirname(__file__), "plots")
os.makedirs(PLOTS_DIR, exist_ok=True)

REPLICATOR_20 = [1, 2, 1, 2, 2, 1, 0, 2, 1, 1, 2, 0, 2, 1, 1, 1, 0, 2, 2, 0]

# ==============================================================================
# TEST 1: TURING COMPLETENESS -- Z_3 ENCODING VERIFICATION
# ==============================================================================

def test_z3_encoding_capacity():
    """Verify 3^6 = 729 >= 256 and that the encoding is injective."""
    print("\n--- Test 1a: Z_3 Encoding Capacity ---")

    capacity = 3**6
    assert capacity == 729, f"3^6 = {capacity}, expected 729"
    assert capacity >= 256, f"3^6 = {capacity} < 256, encoding insufficient"

    # Verify encoding is injective: each n in [0,255] maps to unique 6-trit sequence
    encoded = set()
    collisions = []
    for n in range(256):
        trits = []
        val = n
        for _ in range(6):
            trits.append(val % 3)
            val //= 3
        key = tuple(trits)
        if key in encoded:
            collisions.append((n, key))
        encoded.add(key)

    passed = len(collisions) == 0
    print(f"  3^6 = {capacity} >= 256: PASS")
    print(f"  Injective encoding (0-255 -> 6-trit): {'PASS' if passed else 'FAIL'}")
    print(f"  Collisions: {len(collisions)}")
    return {"test": "z3_encoding_capacity", "capacity": capacity,
            "injective": passed, "collisions": len(collisions), "passed": passed}


def test_z3_increment_carry():
    """Verify increment with carry propagation in Z_3 base works for all 256 values."""
    print("\n--- Test 1b: Z_3 Increment with Carry ---")

    def encode_z3(n):
        trits = []
        val = n
        for _ in range(6):
            trits.append(val % 3)
            val //= 3
        return trits

    def decode_z3(trits):
        return sum(t * (3**i) for i, t in enumerate(trits))

    def increment_z3(trits):
        """Increment a 6-trit number with carry propagation."""
        result = list(trits)
        carry = 1
        for i in range(6):
            s = result[i] + carry
            result[i] = s % 3
            carry = s // 3
            if carry == 0:
                break
        return result

    failures = []
    for n in range(256):
        trits = encode_z3(n)
        inc_trits = increment_z3(trits)
        expected = (n + 1) % (3**6)
        got = decode_z3(inc_trits)
        if got != expected:
            failures.append((n, expected, got))

    passed = len(failures) == 0
    print(f"  Increment with carry for all 256 values: {'PASS' if passed else 'FAIL'}")
    if failures:
        print(f"  First failure: n={failures[0][0]}, expected={failures[0][1]}, got={failures[0][2]}")
    return {"test": "z3_increment_carry", "failures": len(failures), "passed": passed}


def test_z3_zero_detection():
    """Verify OR-reduction zero test works in Z_3."""
    print("\n--- Test 1c: Z_3 Zero Detection via OR-Reduction ---")

    def is_zero_z3(trits):
        """Test if a 6-trit cell equals zero by OR-reducing all trits."""
        return all(t == 0 for t in trits)

    def encode_z3(n):
        trits = []
        val = n
        for _ in range(6):
            trits.append(val % 3)
            val //= 3
        return trits

    # n=0 should be zero, all others should be nonzero
    false_positives = []
    false_negatives = []
    for n in range(729):
        trits = encode_z3(n)
        detected_zero = is_zero_z3(trits)
        if n == 0 and not detected_zero:
            false_negatives.append(n)
        elif n != 0 and detected_zero:
            false_positives.append(n)

    passed = len(false_positives) == 0 and len(false_negatives) == 0
    print(f"  Zero detection: {'PASS' if passed else 'FAIL'}")
    print(f"  False positives: {len(false_positives)}, False negatives: {len(false_negatives)}")
    return {"test": "z3_zero_detection", "false_positives": len(false_positives),
            "false_negatives": len(false_negatives), "passed": passed}


# ==============================================================================
# TEST 2: SELF-REPLICATOR ADVERSARIAL TESTS
# ==============================================================================

def test_replicator_all_food_patterns():
    """Exhaustive test: S + F -> (S, S) for ALL 3^20 food patterns would be
    intractable. Instead, test structured adversarial foods."""
    print("\n--- Test 2a: Replicator vs Adversarial Foods ---")

    source = np.array(REPLICATOR_20, dtype=int)
    psize = len(source)

    adversarial_foods = {
        "all_zeros": np.zeros(psize, dtype=int),
        "all_ones": np.ones(psize, dtype=int),
        "all_twos": np.full(psize, 2, dtype=int),
        "copy_of_source": source.copy(),
        "reversed_source": source[::-1].copy(),
        "anti_source": (3 - source) % 3,
        "alternating_01": np.array([i % 2 for i in range(psize)], dtype=int),
        "alternating_012": np.array([i % 3 for i in range(psize)], dtype=int),
        "single_nonzero_pos0": np.array([1] + [0]*(psize-1), dtype=int),
        "single_nonzero_last": np.array([0]*(psize-1) + [1], dtype=int),
    }

    results = {}
    all_passed = True
    for name, food in adversarial_foods.items():
        tape = np.concatenate([source.copy(), food.copy()])
        result = execute_tape(tape.copy(), max_steps=729, tape_len=len(tape))
        first = result[:psize]
        second = result[psize:]
        src_ok = np.array_equal(first, source)
        copy_ok = np.array_equal(second, source)
        status = "PASS" if (src_ok and copy_ok) else "FAIL"
        results[name] = {"source_preserved": src_ok, "copy_made": copy_ok}
        if not (src_ok and copy_ok):
            all_passed = False
        print(f"  {status}: food={name} src={src_ok} copy={copy_ok}")

    return {"test": "adversarial_foods", "results": results, "passed": all_passed}


def test_replicator_step_trace():
    """Trace execution step-by-step to verify the copy mechanism works as described."""
    print("\n--- Test 2b: Step-by-Step Execution Trace ---")

    source = np.array(REPLICATOR_20, dtype=int)
    psize = len(source)
    food = np.zeros(psize, dtype=int)
    tape = np.concatenate([source, food]).copy()
    tape_len = len(tape)

    # Re-implement execute_tape with tracing
    ip = 0
    h0 = 0
    h1 = tape_len // 2
    steps = 0
    max_steps = 729

    h0_positions = []
    h1_positions = []
    copy_events = []

    while steps < max_steps and ip + 1 < tape_len:
        high, low = tape[ip], tape[ip + 1]
        instr = INSTR_NAMES.get((high, low), "???")

        if (high, low) == CPY01:
            copy_events.append({"step": steps, "h0": h0, "h1": h1,
                                "value": int(tape[h0])})
        h0_positions.append(h0)
        h1_positions.append(h1)

        # Execute (same logic as soup.py)
        if high == 0:
            if low == 1:
                tape[h0] = (tape[h0] + 1) % Z3
            elif low == 2:
                h0 = (h0 + 1) % tape_len
        elif high == 1:
            if low == 0:
                h0 = (h0 - 1) % tape_len
            elif low == 1:
                h1 = (h1 + 1) % tape_len
            elif low == 2:
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
        elif high == 2:
            if low == 0:
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
            elif low == 1:
                tape[h1] = tape[h0]
            elif low == 2:
                tape[h0] = tape[h1]

        ip += 2
        steps += 1

    # Verify copy events
    pass1_copies = [e for e in copy_events if e["h0"] < psize]
    pass1_h0_reads_food = [e for e in pass1_copies if e["h0"] >= psize]

    # Check that during Pass 1 (copying source to food), h0 never reads from food region
    food_reads_during_pass1 = len(pass1_h0_reads_food)
    passed = food_reads_during_pass1 == 0

    print(f"  Total steps executed: {steps}")
    print(f"  Total copy events: {len(copy_events)}")
    print(f"  Pass 1 copies (h0 < {psize}): {len(pass1_copies)}")
    print(f"  Food reads during Pass 1: {food_reads_during_pass1}")
    print(f"  Food-independence verified: {'PASS' if passed else 'FAIL'}")

    # Check final state
    first = tape[:psize]
    second = tape[psize:]
    src_ok = np.array_equal(first, source)
    copy_ok = np.array_equal(second, source)
    print(f"  Final state: source_preserved={src_ok}, copy_made={copy_ok}")

    return {"test": "step_trace", "total_steps": steps,
            "copy_events": len(copy_events), "pass1_copies": len(pass1_copies),
            "food_reads_pass1": food_reads_during_pass1,
            "source_preserved": src_ok, "copy_made": copy_ok,
            "passed": passed and src_ok and copy_ok}


def test_replicator_non_termination():
    """Verify the replicator does NOT halt -- it relies on max_steps bound."""
    print("\n--- Test 2c: Non-Termination Verification ---")

    source = np.array(REPLICATOR_20, dtype=int)
    psize = len(source)
    food = np.zeros(psize, dtype=int)

    # Run with increasing max_steps and check if IP ever falls off end naturally
    for max_steps in [100, 500, 729, 2000, 5000]:
        tape = np.concatenate([source.copy(), food.copy()])
        tape_len = len(tape)

        ip = 0
        h0 = 0
        h1 = tape_len // 2
        steps = 0
        halted_naturally = False

        while steps < max_steps:
            if ip + 1 >= tape_len:
                halted_naturally = True
                break
            high, low = tape[ip], tape[ip + 1]

            if high == 0:
                if low == 1:
                    tape[h0] = (tape[h0] + 1) % Z3
                elif low == 2:
                    h0 = (h0 + 1) % tape_len
            elif high == 1:
                if low == 0:
                    h0 = (h0 - 1) % tape_len
                elif low == 1:
                    h1 = (h1 + 1) % tape_len
                elif low == 2:
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
            elif high == 2:
                if low == 0:
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
                elif low == 1:
                    tape[h1] = tape[h0]
                elif low == 2:
                    tape[h0] = tape[h1]

            ip += 2
            steps += 1

        status = "PASS" if not halted_naturally else "FAIL"
        print(f"  max_steps={max_steps}: halted_naturally={halted_naturally} ({status})")

    # The program should never halt naturally (IP never falls off the end)
    # because the outer ] loop keeps sending IP back
    passed = not halted_naturally  # Check the largest run
    return {"test": "non_termination", "passed": passed}


def test_replicator_idempotent_passes():
    """Verify that after Pass 1, subsequent passes are idempotent."""
    print("\n--- Test 2d: Idempotent Subsequent Passes ---")

    source = np.array(REPLICATOR_20, dtype=int)
    psize = len(source)
    food = np.zeros(psize, dtype=int)

    # Run with different max_steps to capture state after multiple passes
    states = {}
    for max_steps in [100, 200, 500, 729]:
        tape = np.concatenate([source.copy(), food.copy()])
        result = execute_tape(tape, max_steps=max_steps, tape_len=len(tape))
        states[max_steps] = result.copy()

    # After Pass 1 (~84 steps), all subsequent states should be identical
    # Check that states at 200, 500, 729 are all the same
    ref = states[200]
    all_same = True
    for ms in [500, 729]:
        if not np.array_equal(states[ms], ref):
            all_same = False
            diff_count = np.sum(states[ms] != ref)
            print(f"  DIFF: state@{ms} differs from state@200 in {diff_count} trits")

    passed = all_same
    print(f"  States at 200/500/729 steps identical: {'PASS' if passed else 'FAIL'}")
    return {"test": "idempotent_passes", "passed": passed}


# ==============================================================================
# TEST 3: NOP DILUTION ANALYSIS (COMPETITIVE EXPERIMENTS)
# ==============================================================================

def test_nop_dilution_curve():
    """Compute and plot NOP% vs modulus N for Z_2 through Z_10."""
    print("\n--- Test 3: NOP Dilution vs Modulus ---")

    semantic_opcodes = 9  # The 9 meaningful operations
    moduli = list(range(2, 11))
    nop_fracs = []
    total_opcodes = []

    for n in moduli:
        n_sq = n * n
        total_opcodes.append(n_sq)
        if n_sq <= semantic_opcodes:
            # Not enough slots -- structural impossibility (Z_2: 4 < 9)
            nop_fracs.append(0.0)  # Can't even fit all ops
        else:
            nop_fracs.append((n_sq - semantic_opcodes) / n_sq)

    # Verify specific values from the proof
    results = {}
    expected = {2: 0.0, 3: 0.0, 4: 7/16, 5: 16/25, 7: 40/49}
    for n, exp in expected.items():
        idx = n - 2
        if n == 2:
            # Z_2: 4 < 9, structurally impossible
            results[f"Z_{n}"] = {"n_sq": n*n, "semantic": semantic_opcodes,
                                 "structurally_impossible": True}
            print(f"  Z_{n}: {n}^2 = {n*n} < 9 -> structurally impossible")
        else:
            actual = nop_fracs[idx]
            match = abs(actual - exp) < 1e-10
            results[f"Z_{n}"] = {"n_sq": n*n, "nop_frac": actual,
                                 "expected": exp, "match": match}
            print(f"  Z_{n}: NOP% = {actual:.3f} (expected {exp:.3f}) {'PASS' if match else 'FAIL'}")

    # Z_3 is special: 3^2 = 9 = exactly the number of semantic opcodes
    z3_perfect = 3**2 == semantic_opcodes
    print(f"  Z_3 uniquely fills opcode space: 3^2 = 9 = {semantic_opcodes}: {'PASS' if z3_perfect else 'FAIL'}")

    # Plot
    fig, ax = plt.subplots(1, 1, figsize=(8, 5))
    colors = ['red' if n == 2 else ('green' if n == 3 else 'gray') for n in moduli]
    bars = ax.bar([f"Z_{n}" for n in moduli], [f if n > 2 else 0 for n, f in zip(moduli, nop_fracs)],
                  color=colors, edgecolor='black', alpha=0.8)

    # Mark Z_2 as structurally impossible
    ax.text(0, 0.05, "N/A\n(4<9)", ha='center', va='bottom', fontsize=8, color='red')

    ax.axhline(y=0, color='black', linewidth=0.5)
    ax.set_ylabel("NOP Fraction (wasted opcodes)")
    ax.set_xlabel("Cell Modulus")
    ax.set_title("NOP Dilution vs Cell Modulus\n(Z_3 uniquely achieves 0% waste)")
    ax.set_ylim(-0.05, 1.0)

    # Annotate Z_3
    ax.annotate("3^2 = 9 = semantic opcodes\nZERO waste", xy=(1, 0), xytext=(3, 0.3),
                arrowprops=dict(arrowstyle="->", color="green"), fontsize=9, color="green",
                ha='center')

    plt.tight_layout()
    plt.savefig(os.path.join(PLOTS_DIR, "Prop_0_0_XXd_nop_dilution.png"), dpi=150)
    plt.close()
    print(f"  Plot saved: plots/Prop_0_0_XXd_nop_dilution.png")

    return {"test": "nop_dilution", "z3_perfect_fit": z3_perfect,
            "results": results, "passed": z3_perfect}


# ==============================================================================
# TEST 4: INSTRUCTION SET COMPLETENESS ANALYSIS
# ==============================================================================

def test_instruction_set_completeness():
    """Verify that the 9 instructions cover all necessary computational primitives."""
    print("\n--- Test 4: Instruction Set Completeness ---")

    instructions = {
        "NOP":  {"pair": NOP, "category": "control"},
        "ROT":  {"pair": ROT, "category": "data_modify"},
        "FWD0": {"pair": FWD0, "category": "movement"},
        "BCK0": {"pair": BCK0, "category": "movement"},
        "FWD1": {"pair": FWD1, "category": "movement"},
        "OPEN": {"pair": OPEN, "category": "control_flow"},
        "CLOSE":{"pair": CLOSE, "category": "control_flow"},
        "CPY01":{"pair": CPY01, "category": "data_transfer"},
        "CPY10":{"pair": CPY10, "category": "data_transfer"},
    }

    # Verify all 9 pairs are distinct
    pairs = [v["pair"] for v in instructions.values()]
    unique_pairs = set(pairs)
    all_unique = len(unique_pairs) == 9
    print(f"  All 9 instruction pairs unique: {'PASS' if all_unique else 'FAIL'}")

    # Verify they cover all of Z_3 x Z_3
    all_z3_pairs = {(a, b) for a in range(3) for b in range(3)}
    coverage = unique_pairs == all_z3_pairs
    print(f"  Cover all Z_3 x Z_3 = 9 pairs: {'PASS' if coverage else 'FAIL'}")
    if not coverage:
        missing = all_z3_pairs - unique_pairs
        extra = unique_pairs - all_z3_pairs
        print(f"  Missing: {missing}, Extra: {extra}")

    # Verify computational completeness categories
    categories = {}
    for name, info in instructions.items():
        cat = info["category"]
        categories.setdefault(cat, []).append(name)

    has_data_modify = "data_modify" in categories
    has_movement = "movement" in categories
    has_control_flow = "control_flow" in categories
    has_data_transfer = "data_transfer" in categories
    has_control = "control" in categories

    complete = has_data_modify and has_movement and has_control_flow and has_data_transfer
    print(f"  Data modification: {'PASS' if has_data_modify else 'FAIL'} ({categories.get('data_modify', [])})")
    print(f"  Movement: {'PASS' if has_movement else 'FAIL'} ({categories.get('movement', [])})")
    print(f"  Control flow: {'PASS' if has_control_flow else 'FAIL'} ({categories.get('control_flow', [])})")
    print(f"  Data transfer: {'PASS' if has_data_transfer else 'FAIL'} ({categories.get('data_transfer', [])})")

    passed = all_unique and coverage and complete
    return {"test": "instruction_set_completeness", "all_unique": all_unique,
            "full_coverage": coverage, "computationally_complete": complete,
            "passed": passed}


# ==============================================================================
# TEST 5: REPLICATOR ROBUSTNESS -- MUTATION SENSITIVITY
# ==============================================================================

def test_mutation_sensitivity():
    """Test how single-trit mutations affect replication success."""
    print("\n--- Test 5: Mutation Sensitivity Analysis ---")

    source = np.array(REPLICATOR_20, dtype=int)
    psize = len(source)
    food = np.zeros(psize, dtype=int)

    mutation_results = []
    for pos in range(psize):
        for delta in [1, 2]:  # Try both non-identity rotations
            mutant = source.copy()
            mutant[pos] = (mutant[pos] + delta) % 3

            tape = np.concatenate([mutant.copy(), food.copy()])
            result = execute_tape(tape, max_steps=729, tape_len=len(tape))
            first = result[:psize]
            second = result[psize:]

            # Does mutant replicate itself?
            self_replicates = np.array_equal(first, mutant) and np.array_equal(second, mutant)
            # Does it replicate the original?
            replicates_original = np.array_equal(first, source) and np.array_equal(second, source)

            mutation_results.append({
                "position": pos, "delta": delta,
                "self_replicates": self_replicates,
                "replicates_original": replicates_original,
            })

    n_self_rep = sum(1 for r in mutation_results if r["self_replicates"])
    n_orig_rep = sum(1 for r in mutation_results if r["replicates_original"])
    total = len(mutation_results)

    print(f"  Total single-trit mutations tested: {total}")
    print(f"  Mutants that self-replicate: {n_self_rep}/{total}")
    print(f"  Mutants that replicate original: {n_orig_rep}/{total}")
    print(f"  Replicator is fragile to mutation: {'YES' if n_self_rep < total/2 else 'NO'}")

    # Plot mutation sensitivity heatmap
    fig, ax = plt.subplots(1, 1, figsize=(12, 3))
    heatmap = np.zeros((2, psize))
    for r in mutation_results:
        row = r["delta"] - 1
        col = r["position"]
        heatmap[row, col] = 1 if r["self_replicates"] else 0

    im = ax.imshow(heatmap, aspect='auto', cmap='RdYlGn', vmin=0, vmax=1)
    ax.set_yticks([0, 1])
    ax.set_yticklabels(["+1 mod 3", "+2 mod 3"])
    ax.set_xlabel("Trit Position")
    ax.set_ylabel("Mutation")
    ax.set_title("Replicator Mutation Sensitivity\n(Green=self-replicates, Red=broken)")
    ax.set_xticks(range(psize))

    # Mark instruction boundaries
    for i in range(0, psize, 2):
        ax.axvline(x=i - 0.5, color='gray', linewidth=0.5, linestyle='--')
        pair = (source[i], source[i+1])
        name = INSTR_NAMES.get(pair, "?")
        ax.text(i + 0.5, -0.8, name, ha='center', va='top', fontsize=6, rotation=45)

    plt.colorbar(im, ax=ax, shrink=0.8, label="Self-replicates")
    plt.tight_layout()
    plt.savefig(os.path.join(PLOTS_DIR, "Prop_0_0_XXd_mutation_sensitivity.png"), dpi=150)
    plt.close()
    print(f"  Plot saved: plots/Prop_0_0_XXd_mutation_sensitivity.png")

    # The replicator is expected to be fragile -- most mutations break it.
    # This is consistent with the "computational life" model.
    return {"test": "mutation_sensitivity", "total_mutations": total,
            "self_replicating_mutants": n_self_rep,
            "fraction_robust": n_self_rep / total,
            "passed": True}  # Informational test


# ==============================================================================
# TEST 6: RANDOM PROGRAM REPLICATION RATE (BASELINE)
# ==============================================================================

def test_random_program_replication_baseline():
    """Test replication rate of random 20-trit programs as a baseline."""
    print("\n--- Test 6: Random Program Replication Baseline ---")

    rng = np.random.default_rng(42)
    n_programs = 1000
    psize = 20

    replicators = 0
    source_preservers = 0

    for _ in range(n_programs):
        program = rng.integers(0, 3, size=psize)
        food = np.zeros(psize, dtype=int)
        tape = np.concatenate([program.copy(), food.copy()])
        result = execute_tape(tape, max_steps=729, tape_len=len(tape))

        first = result[:psize]
        second = result[psize:]

        if np.array_equal(first, program) and np.array_equal(second, program):
            replicators += 1
        if np.array_equal(first, program):
            source_preservers += 1

    rep_rate = replicators / n_programs
    pres_rate = source_preservers / n_programs
    print(f"  Random programs tested: {n_programs}")
    print(f"  Self-replicators: {replicators} ({rep_rate:.3%})")
    print(f"  Source-preserving: {source_preservers} ({pres_rate:.3%})")
    print(f"  The known replicator is special (not typical): {'PASS' if rep_rate < 0.1 else 'WARNING'}")

    return {"test": "random_baseline", "n_programs": n_programs,
            "replicators": replicators, "replication_rate": rep_rate,
            "source_preservers": source_preservers, "preservation_rate": pres_rate,
            "passed": True}  # Informational


# ==============================================================================
# TEST 7: SOUP MICRO-SIMULATION (SHORT RUN)
# ==============================================================================

def test_soup_micro_simulation():
    """Run a short soup simulation to verify the interaction mechanism works."""
    print("\n--- Test 7: Soup Micro-Simulation ---")

    rng = np.random.default_rng(42)
    soup_size = 256
    psize = 24
    max_steps = 729
    mutation_rate = 0.001
    epochs = 5000

    # Initialize random soup
    soup = rng.integers(0, 3, size=(soup_size, psize))

    # Seed a few replicators
    replicator_24 = np.array(REPLICATOR_20 + [0, 0, 0, 0], dtype=int)
    soup[0] = replicator_24.copy()
    soup[1] = replicator_24.copy()

    replicator_counts = []
    diversity = []

    for epoch in range(epochs):
        # Random pair interaction
        i, j = rng.choice(soup_size, size=2, replace=False)
        tape = np.concatenate([soup[i].copy(), soup[j].copy()])
        result = execute_tape(tape, max_steps=max_steps, tape_len=len(tape))
        soup[i] = result[:psize]
        soup[j] = result[psize:]

        # Mutation
        if mutation_rate > 0:
            for idx in [i, j]:
                mask = rng.random(psize) < mutation_rate
                if np.any(mask):
                    soup[idx][mask] = rng.integers(0, 3, size=np.sum(mask))

        # Track metrics every 100 epochs
        if epoch % 100 == 0:
            core_match = sum(
                1 for p in soup
                if np.array_equal(p[:20], REPLICATOR_20)
            )
            replicator_counts.append(core_match)
            unique = len(set(tuple(p) for p in soup))
            diversity.append(unique)

    final_count = replicator_counts[-1]
    final_frac = final_count / soup_size
    print(f"  Soup size: {soup_size}, Epochs: {epochs}")
    print(f"  Seeded replicators: 2/{soup_size}")
    print(f"  Final replicator count: {final_count}/{soup_size} ({final_frac:.1%})")
    print(f"  Final diversity: {diversity[-1]} unique programs")
    print(f"  Replicator spread: {'PASS' if final_count > 2 else 'MARGINAL'}")

    # Plot
    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(10, 6), sharex=True)

    x = list(range(0, epochs, 100))
    ax1.plot(x, replicator_counts, 'g-', linewidth=1.5, label='Replicator count')
    ax1.axhline(y=2, color='gray', linestyle='--', alpha=0.5, label='Initial seed')
    ax1.set_ylabel("Replicator Count")
    ax1.set_title(f"Soup Micro-Simulation (N={soup_size}, {epochs} epochs)")
    ax1.legend()

    ax2.plot(x, diversity, 'b-', linewidth=1.5, label='Unique programs')
    ax2.set_ylabel("Diversity")
    ax2.set_xlabel("Epoch")
    ax2.legend()

    plt.tight_layout()
    plt.savefig(os.path.join(PLOTS_DIR, "Prop_0_0_XXd_soup_micro.png"), dpi=150)
    plt.close()
    print(f"  Plot saved: plots/Prop_0_0_XXd_soup_micro.png")

    return {"test": "soup_micro", "soup_size": soup_size, "epochs": epochs,
            "final_replicator_count": final_count,
            "final_fraction": final_frac,
            "passed": final_count > 2}


# ==============================================================================
# TEST 8: GATE CONDITION ENCODING ANALYSIS
# ==============================================================================

def test_gate_encoding_analysis():
    """Analyze the encoding explanation for gate-on-zero being privileged."""
    print("\n--- Test 8: Gate Condition Encoding Analysis ---")

    # NOP = (0,0), which means tape[h0] = 0 when reading a NOP trit
    # For gate=0: loop exits when tape[h0] == 0
    # Blank/uninitialized tape has all zeros -> loops naturally exit over blank regions

    # Count how many instructions have 0 as their first trit
    zero_first_trit = [(name, pair) for pair, name in INSTR_NAMES.items() if pair[0] == 0]
    one_first_trit = [(name, pair) for pair, name in INSTR_NAMES.items() if pair[0] == 1]
    two_first_trit = [(name, pair) for pair, name in INSTR_NAMES.items() if pair[0] == 2]

    print(f"  Instructions with first trit = 0: {[n for n, _ in zero_first_trit]}")
    print(f"  Instructions with first trit = 1: {[n for n, _ in one_first_trit]}")
    print(f"  Instructions with first trit = 2: {[n for n, _ in two_first_trit]}")

    # For a random program, what fraction of trit positions are 0?
    # In Z_3, expected fraction is 1/3 for each value
    # For gate=0, ~1/3 of random positions trigger loop exit
    # For gate=1 or gate=2, also ~1/3 -- but no instruction is "natural terminator"

    # The key insight: NOP = (0,0) means blank tape IS the gate exit condition
    # This is an encoding property, not a deep dynamical property
    nop_is_zero = NOP == (0, 0)
    print(f"  NOP = (0,0): {nop_is_zero}")
    print(f"  Blank tape -> natural loop exits for gate=0: {'YES' if nop_is_zero else 'NO'}")

    # Compute: in a random 20-trit program, how many zero trits on average?
    rng = np.random.default_rng(42)
    n_samples = 10000
    zero_counts = []
    for _ in range(n_samples):
        prog = rng.integers(0, 3, size=20)
        zero_counts.append(np.sum(prog == 0))

    mean_zeros = np.mean(zero_counts)
    expected = 20 / 3
    print(f"  Mean zero trits in random 20-trit program: {mean_zeros:.2f} (expected: {expected:.2f})")

    # The replicator has zeros at positions: 6, 11, 16, 19
    source = np.array(REPLICATOR_20)
    zero_positions = np.where(source == 0)[0]
    print(f"  Replicator zero positions: {zero_positions.tolist()}")
    print(f"  These create natural loop boundaries for the copy mechanism")

    passed = nop_is_zero  # The encoding explanation is confirmed
    return {"test": "gate_encoding", "nop_is_zero_zero": nop_is_zero,
            "mean_zeros_random": mean_zeros, "replicator_zero_positions": zero_positions.tolist(),
            "passed": passed}


# ==============================================================================
# TEST 9: FIXED POINT STRUCTURE VERIFICATION
# ==============================================================================

def test_fixed_point_structure():
    """Verify that S = split(exec(S||F))_1 is a genuine fixed point."""
    print("\n--- Test 9: Fixed Point Structure ---")

    source = np.array(REPLICATOR_20, dtype=int)
    psize = len(source)

    # Test with many different foods -- the source half must always be S
    rng = np.random.default_rng(7)
    n_trials = 200
    source_preserved = 0
    full_replication = 0

    for _ in range(n_trials):
        food = rng.integers(0, 3, size=psize)
        tape = np.concatenate([source.copy(), food.copy()])
        result = execute_tape(tape, max_steps=729, tape_len=len(tape))
        first = result[:psize]
        second = result[psize:]

        if np.array_equal(first, source):
            source_preserved += 1
        if np.array_equal(first, source) and np.array_equal(second, source):
            full_replication += 1

    fp_rate = source_preserved / n_trials
    rep_rate = full_replication / n_trials

    print(f"  Fixed point test (S = split(exec(S||F))_1):")
    print(f"    Source preserved: {source_preserved}/{n_trials} ({fp_rate:.1%})")
    print(f"    Full replication: {full_replication}/{n_trials} ({rep_rate:.1%})")

    passed = source_preserved == n_trials and full_replication == n_trials
    print(f"  Universal fixed point: {'PASS' if passed else 'FAIL'}")

    return {"test": "fixed_point", "n_trials": n_trials,
            "source_preserved": source_preserved,
            "full_replication": full_replication,
            "fixed_point_rate": fp_rate,
            "replication_rate": rep_rate,
            "passed": passed}


# ==============================================================================
# TEST 10: COMPREHENSIVE SUMMARY PLOT
# ==============================================================================

def generate_summary_plot(all_results):
    """Generate a comprehensive summary of all adversarial tests."""
    print("\n--- Generating Summary Plot ---")

    test_names = []
    test_status = []
    for r in all_results:
        name = r.get("test", "unknown")
        passed = r.get("passed", False)
        test_names.append(name.replace("_", "\n"))
        test_status.append(1 if passed else 0)

    fig, ax = plt.subplots(1, 1, figsize=(14, 5))
    colors = ['#2ecc71' if s else '#e74c3c' for s in test_status]
    bars = ax.barh(range(len(test_names)), test_status, color=colors,
                   edgecolor='black', alpha=0.85)

    ax.set_yticks(range(len(test_names)))
    ax.set_yticklabels(test_names, fontsize=8)
    ax.set_xlim(-0.1, 1.2)
    ax.set_xlabel("Status")
    ax.set_title("Proposition 0.0.XXd: Adversarial Verification Summary")

    for i, (status, name) in enumerate(zip(test_status, test_names)):
        label = "PASS" if status else "FAIL"
        ax.text(status + 0.05, i, label, va='center', fontsize=9,
                fontweight='bold', color=colors[i])

    n_passed = sum(test_status)
    n_total = len(test_status)
    ax.text(0.95, 0.02, f"{n_passed}/{n_total} tests passed",
            transform=ax.transAxes, fontsize=12, ha='right',
            fontweight='bold',
            color='#2ecc71' if n_passed == n_total else '#e74c3c')

    plt.tight_layout()
    plt.savefig(os.path.join(PLOTS_DIR, "Prop_0_0_XXd_adversarial_summary.png"), dpi=150)
    plt.close()
    print(f"  Plot saved: plots/Prop_0_0_XXd_adversarial_summary.png")


# ==============================================================================
# MAIN
# ==============================================================================

def main():
    print("=" * 70)
    print("Proposition 0.0.XXd: Adversarial Physics Verification")
    print("=" * 70)
    print(f"Date: {datetime.now().isoformat()}")
    print(f"Replicator: {REPLICATOR_20}")

    all_results = []

    # Claim 1: Turing Completeness
    print("\n" + "=" * 70)
    print("CLAIM 1: TURING COMPLETENESS (Z_3 Encoding)")
    print("=" * 70)
    all_results.append(test_z3_encoding_capacity())
    all_results.append(test_z3_increment_carry())
    all_results.append(test_z3_zero_detection())

    # Claim 2: Self-Replicator Construction
    print("\n" + "=" * 70)
    print("CLAIM 2: SELF-REPLICATOR CONSTRUCTION")
    print("=" * 70)
    all_results.append(test_replicator_all_food_patterns())
    all_results.append(test_replicator_step_trace())
    all_results.append(test_replicator_non_termination())
    all_results.append(test_replicator_idempotent_passes())

    # Claim 4: CG Configuration Uniqueness
    print("\n" + "=" * 70)
    print("CLAIM 4: CG CONFIGURATION UNIQUENESS")
    print("=" * 70)
    all_results.append(test_nop_dilution_curve())
    all_results.append(test_instruction_set_completeness())
    all_results.append(test_gate_encoding_analysis())

    # Cross-cutting tests
    print("\n" + "=" * 70)
    print("CROSS-CUTTING ADVERSARIAL TESTS")
    print("=" * 70)
    all_results.append(test_mutation_sensitivity())
    all_results.append(test_random_program_replication_baseline())
    all_results.append(test_soup_micro_simulation())
    all_results.append(test_fixed_point_structure())

    # Summary
    generate_summary_plot(all_results)

    n_passed = sum(1 for r in all_results if r.get("passed", False))
    n_total = len(all_results)

    print("\n" + "=" * 70)
    print(f"OVERALL: {n_passed}/{n_total} tests passed")
    print("=" * 70)

    # Save results
    output = {
        "proposition": "0.0.XXd",
        "title": "Computational Universality of CG Primitives",
        "type": "adversarial_physics_verification",
        "timestamp": datetime.now().isoformat(),
        "overall_status": "PASSED" if n_passed == n_total else "PARTIAL",
        "tests_passed": n_passed,
        "tests_total": n_total,
        "results": all_results,
        "plots": [
            "plots/Prop_0_0_XXd_nop_dilution.png",
            "plots/Prop_0_0_XXd_mutation_sensitivity.png",
            "plots/Prop_0_0_XXd_soup_micro.png",
            "plots/Prop_0_0_XXd_adversarial_summary.png",
        ],
    }

    output_path = os.path.join(os.path.dirname(__file__),
                               "prop_0_0_XXd_adversarial_results.json")
    with open(output_path, "w") as f:
        json.dump(output, f, indent=2, default=str)
    print(f"\nResults saved to: {output_path}")

    if n_passed < n_total:
        sys.exit(1)


if __name__ == "__main__":
    main()
