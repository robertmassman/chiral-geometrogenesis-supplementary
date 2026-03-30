#!/usr/bin/env python3
"""
Adversarial Verification Plots: Proposition 0.0.XXg
====================================================

Generates figures from CSV data produced by adversarial_prop_XXg_spectral_prime.c

Related Documents:
- Proof: docs/proofs/foundations/Proposition-0.0.XXg-Q3-Spectral-Structure-Stella-Octangula.md
- Verification Report: docs/proofs/verification-records/Proposition-0.0.XXg-Multi-Agent-Verification-2026-03-27.md

Build/Run:
  cc -O3 -o adversarial_prop_XXg adversarial_prop_XXg_spectral_prime.c -lm
  ./adversarial_prop_XXg
  python3 adversarial_prop_XXg_plots.py
"""

import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import os

PLOT_DIR = os.path.join(os.path.dirname(__file__), "plots")

# ─── Plot 1: Sigma sweep — eigenvalue magnitude vs sigma ───────────────────

def plot_sigma_sweep():
    path = os.path.join(PLOT_DIR, "test3_sigma_sweep.csv")
    if not os.path.exists(path):
        print(f"  SKIP: {path} not found")
        return
    data = np.genfromtxt(path, delimiter=',', names=True)

    fig, axes = plt.subplots(1, 2, figsize=(14, 5))

    # Left: max eigenvalue vs sigma (shows coupling decay at small sigma)
    ax = axes[0]
    ax.semilogy(data['sigma'], data['max_ev'], 'b-', linewidth=1.5)
    ax.set_xlabel(r'$\sigma$', fontsize=12)
    ax.set_ylabel('Max eigenvalue', fontsize=12)
    ax.set_title('Eigenvalue magnitude vs confinement', fontsize=13)
    ax.axvline(x=0.37, color='r', linestyle='--', alpha=0.5, label=r'$\sigma = 0.37$ (claimed threshold)')
    ax.legend()
    ax.grid(True, alpha=0.3)

    # Right: max/min_nz ratio vs sigma (should be ~3 for Q3 pattern)
    ax = axes[1]
    mask = data['ratio_max_min'] > 0
    ax.plot(data['sigma'][mask], data['ratio_max_min'][mask], 'r-', linewidth=1.5)
    ax.axhline(y=3.0, color='k', linestyle='--', alpha=0.5, label='Q₃ ratio = 3.0')
    ax.set_xlabel(r'$\sigma$', fontsize=12)
    ax.set_ylabel(r'$\lambda_{max} / \lambda_{min,nz}$', fontsize=12)
    ax.set_title('Eigenvalue ratio max/min (nonzero)', fontsize=13)
    ax.legend()
    ax.grid(True, alpha=0.3)
    ax.set_ylim(0, 5)

    fig.suptitle('TEST 3: σ limit tests — eigenvalue structure vs confinement', fontsize=14, y=1.02)
    plt.tight_layout()
    outpath = os.path.join(PLOT_DIR, "adversarial_XXg_test3_sigma_limits.png")
    plt.savefig(outpath, dpi=150, bbox_inches='tight')
    print(f"  Saved: {outpath}")
    plt.close()

# ─── Plot 2: Z_N comparison — eigenvalue ratios across Z_N orders ──────────

def plot_z3_comparison():
    path = os.path.join(PLOT_DIR, "test4_z3_comparison.csv")
    if not os.path.exists(path):
        print(f"  SKIP: {path} not found")
        return
    data = np.genfromtxt(path, delimiter=',', names=True)

    fig, ax = plt.subplots(figsize=(10, 6))
    ax.plot(data['sigma'], data['noZ3_ratio_max'], 'k-', linewidth=2, label='No Z_N')
    ax.plot(data['sigma'], data['Z3_ratio_max'], 'r--', linewidth=2, label='Z₃')
    ax.plot(data['sigma'], data['Z2_ratio_max'], 'b:', linewidth=2, label='Z₂')
    ax.plot(data['sigma'], data['Z5_ratio_max'], 'g-.', linewidth=2, label='Z₅')
    ax.plot(data['sigma'], data['Z7_ratio_max'], 'm-', linewidth=1.5, alpha=0.7, label='Z₇')
    ax.axhline(y=3.0, color='gray', linestyle='--', alpha=0.4, label='Q₃ ratio = 3')

    ax.set_xlabel(r'$\sigma$', fontsize=12)
    ax.set_ylabel(r'$\lambda_{max} / \lambda_{min,nz}$', fontsize=12)
    ax.set_title('TEST 4: Eigenvalue ratio vs Z_N order — is the pattern Z₃-specific?', fontsize=13)
    ax.legend(fontsize=10)
    ax.grid(True, alpha=0.3)
    ax.set_ylim(0, 5)

    outpath = os.path.join(PLOT_DIR, "adversarial_XXg_test4_zn_comparison.png")
    plt.savefig(outpath, dpi=150, bbox_inches='tight')
    print(f"  Saved: {outpath}")
    plt.close()

# ─── Plot 3: Fisher formula consistency ────────────────────────────────────

def plot_fisher_consistency():
    path = os.path.join(PLOT_DIR, "test5_fisher_consistency.csv")
    if not os.path.exists(path):
        print(f"  SKIP: {path} not found")
        return
    data = np.genfromtxt(path, delimiter=',', names=True)

    fig, axes = plt.subplots(1, 3, figsize=(18, 5))

    # Left: 1D with 2*x factor
    ax = axes[0]
    ax.plot(data['K'], data['prime_1d_with2x'], 'ro-', label='Primes', markersize=5)
    ax.plot(data['K'], data['int_1d_with2x'], 'bs-', label='Integers', markersize=5)
    ax.set_xlabel('K (number of frequencies)', fontsize=11)
    ax.set_ylabel('Effective rank', fontsize=11)
    ax.set_title('1D with 2·x factor (original)', fontsize=12)
    ax.legend()
    ax.grid(True, alpha=0.3)

    # Middle: 1D without 2*x factor
    ax = axes[1]
    ax.plot(data['K'], data['prime_1d_no2x'], 'ro-', label='Primes', markersize=5)
    ax.plot(data['K'], data['int_1d_no2x'], 'bs-', label='Integers', markersize=5)
    ax.set_xlabel('K (number of frequencies)', fontsize=11)
    ax.set_ylabel('Effective rank', fontsize=11)
    ax.set_title('1D without 2·x factor (corrected)', fontsize=12)
    ax.legend()
    ax.grid(True, alpha=0.3)

    # Right: Stella graph
    ax = axes[2]
    ax.plot(data['K'], data['prime_stella'], 'ro-', label='Primes', markersize=5)
    ax.plot(data['K'], data['int_stella'], 'bs-', label='Integers', markersize=5)
    ax.set_xlabel('K (number of frequencies)', fontsize=11)
    ax.set_ylabel('Effective rank', fontsize=11)
    ax.set_title('Stella graph (8 vertices)', fontsize=12)
    ax.legend()
    ax.grid(True, alpha=0.3)

    fig.suptitle('TEST 5: Does the 2·x factor in 1D Fisher formula cause the inversion?', fontsize=14, y=1.02)
    plt.tight_layout()
    outpath = os.path.join(PLOT_DIR, "adversarial_XXg_test5_fisher_formula.png")
    plt.savefig(outpath, dpi=150, bbox_inches='tight')
    print(f"  Saved: {outpath}")
    plt.close()

# ─── Plot 4: Control geometry comparison ──────────────────────────────────

def plot_control_geometry():
    path = os.path.join(PLOT_DIR, "test6_control_geometry.csv")
    if not os.path.exists(path):
        print(f"  SKIP: {path} not found")
        return
    data = np.genfromtxt(path, delimiter=',', names=True)

    fig, axes = plt.subplots(1, 2, figsize=(14, 5))

    # Left: Stella
    ax = axes[0]
    ax.plot(data['K'], data['prime_stella'], 'ro-', label='Primes', markersize=6)
    ax.plot(data['K'], data['int_stella'], 'bs-', label='Integers', markersize=6)
    ax.set_xlabel('K', fontsize=12)
    ax.set_ylabel('Effective rank', fontsize=12)
    ax.set_title('Stella octangula (8 vertices)', fontsize=13)
    ax.legend(fontsize=11)
    ax.grid(True, alpha=0.3)

    # Right: Control
    ax = axes[1]
    ax.plot(data['K'], data['prime_control'], 'ro-', label='Primes', markersize=6)
    ax.plot(data['K'], data['int_control'], 'bs-', label='Integers', markersize=6)
    ax.set_xlabel('K', fontsize=12)
    ax.set_ylabel('Effective rank', fontsize=12)
    ax.set_title('Control geometry — cube vertices (8 vertices)', fontsize=13)
    ax.legend(fontsize=11)
    ax.grid(True, alpha=0.3)

    fig.suptitle('TEST 6: Is "information amplification" stella-specific?', fontsize=14, y=1.02)
    plt.tight_layout()
    outpath = os.path.join(PLOT_DIR, "adversarial_XXg_test6_control_geometry.png")
    plt.savefig(outpath, dpi=150, bbox_inches='tight')
    print(f"  Saved: {outpath}")
    plt.close()

# ─── Main ──────────────────────────────────────────────────────────────────

if __name__ == "__main__":
    print("Generating adversarial verification plots for Prop 0.0.XXg...")
    plot_sigma_sweep()
    plot_z3_comparison()
    plot_fisher_consistency()
    plot_control_geometry()
    print("Done.")
