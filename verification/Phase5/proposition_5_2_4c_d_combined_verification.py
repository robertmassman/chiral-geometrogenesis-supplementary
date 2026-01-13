#!/usr/bin/env python3
"""
Combined Verification Runner for Propositions 5.2.4c & 5.2.4d
==============================================================

This script runs both individual verification suites:
- proposition_5_2_4c_verification.py: Tensor Rank from Derivative Structure
- proposition_5_2_4d_verification.py: Geometric Higher-Spin Exclusion

For individual proposition verification, run the respective scripts directly.

Author: Verification Suite
Date: 2026-01-12
"""

import subprocess
import sys
import os


def run_verification(script_name: str) -> bool:
    """Run a verification script and return success status."""
    script_path = os.path.join(os.path.dirname(__file__), script_name)

    print(f"\n{'='*70}")
    print(f"Running: {script_name}")
    print('='*70)

    result = subprocess.run([sys.executable, script_path], capture_output=False)
    return result.returncode == 0


def main():
    """Run all verification suites for Props 5.2.4c and 5.2.4d."""
    print("="*70)
    print("COMBINED VERIFICATION SUITE")
    print("Propositions 5.2.4c & 5.2.4d")
    print("="*70)

    all_passed = True

    # Run Proposition 5.2.4c verification
    prop_c_passed = run_verification("proposition_5_2_4c_verification.py")
    all_passed &= prop_c_passed

    # Run Proposition 5.2.4d verification
    prop_d_passed = run_verification("proposition_5_2_4d_verification.py")
    all_passed &= prop_d_passed

    # Summary
    print("\n" + "="*70)
    print("COMBINED VERIFICATION SUMMARY")
    print("="*70)

    print(f"\n  Proposition 5.2.4c (Tensor Rank): {'✅ PASS' if prop_c_passed else '❌ FAIL'}")
    print(f"  Proposition 5.2.4d (Higher-Spin): {'✅ PASS' if prop_d_passed else '❌ FAIL'}")

    print("\n" + "="*70)
    if all_passed:
        print("✅ ALL VERIFICATION SUITES PASSED")
        print("\nBoth propositions are verified:")
        print("  • Prop 5.2.4c: Tensor rank = 2 from derivative structure")
        print("  • Prop 5.2.4d: Spin-2 is unique gravitational mediator")
    else:
        print("❌ SOME VERIFICATION SUITES FAILED")
    print("="*70)

    return 0 if all_passed else 1


if __name__ == "__main__":
    exit(main())
