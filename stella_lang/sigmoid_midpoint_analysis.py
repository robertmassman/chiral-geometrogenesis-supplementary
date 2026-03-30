#!/usr/bin/env python3
"""
Priority 5: Sigmoid Midpoint Analysis
======================================

Parses sigmoid_midpoint_campaign logs, extracts per-stella nucleation outcomes,
fits a logistic function P_nuc(N) = 1/(1 + exp(-k(N - N₅₀))), and tests
whether the midpoint N₅₀ coincides with 3⁶ = 729.

Usage:
  python3 stella_lang/sigmoid_midpoint_analysis.py
  python3 stella_lang/sigmoid_midpoint_analysis.py --plot
"""

import argparse
import json
import re
import sys
from pathlib import Path
from datetime import datetime
from collections import defaultdict

import numpy as np
from scipy.optimize import curve_fit
from scipy.stats import beta as beta_dist

# ============================================================================
# PATHS
# ============================================================================

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
LOG_DIR = REPO_ROOT / "verification" / "stella_lang" / "sigmoid_midpoint_logs"
RESULTS_FILE = REPO_ROOT / "verification" / "stella_lang" / "sigmoid_midpoint_results.json"

# ============================================================================
# LOG PARSING (adapted from n_scaling_analysis.py)
# ============================================================================

def parse_log(logfile):
    """Parse a single campaign log file. Returns config + per-stella emergence."""
    text = logfile.read_text()
    lines = text.split("\n")

    result = {"logfile": str(logfile.name), "config": {}, "stellae": [],
              "completed": False}

    # Parse config
    for line in lines:
        m = re.search(r"n_sub=(\d+)", line)
        if m and "n_sub" not in result["config"]:
            result["config"]["n_sub"] = int(m.group(1))

        m = re.search(r"Tiles/stella:\s+(\d+)", line)
        if m:
            result["config"]["N"] = int(m.group(1))

        m = re.search(r"Pairing:\s+(global random|local neighbors)", line)
        if m:
            result["config"]["pairing"] = "global" if "global" in m.group(1) else "local"

        m = re.search(r"Seed:\s+(\d+)", line)
        if m:
            result["config"]["seed"] = int(m.group(1))

        m = re.search(r"Epochs:\s+(\d+)", line)
        if m:
            result["config"]["epochs"] = int(m.group(1))

        m = re.match(r"FCC lattice: L=\d+, (\d+) stellae", line)
        if m:
            result["config"]["n_stellae"] = int(m.group(1))

    # Parse census lines for emergence
    n_stellae = result["config"].get("n_stellae", 4)
    first_emergence = {}
    current_census_epoch = None

    for line in lines:
        m = re.search(r"CENSUS epoch (\d+):", line)
        if m:
            current_census_epoch = int(m.group(1))

        if current_census_epoch is not None:
            m = re.search(r"Stella\s+(\d+):\s+(\d+)\s+/\s+(\d+)", line)
            if m:
                stella_id = int(m.group(1))
                n_rep = int(m.group(2))
                if n_rep > 0 and stella_id not in first_emergence:
                    first_emergence[stella_id] = current_census_epoch

    for s in range(n_stellae):
        result["stellae"].append({
            "stella_id": s,
            "emerged": s in first_emergence,
            "emergence_epoch": first_emergence.get(s, None),
        })

    m = re.search(r"Completed (\d+) epochs in ([\d.]+)s", text)
    if m:
        result["completed"] = True

    return result


def parse_all_logs():
    """Parse all log files in the sigmoid campaign directory."""
    if not LOG_DIR.exists():
        print(f"ERROR: No log directory found: {LOG_DIR}")
        sys.exit(1)

    results = []
    for logfile in sorted(LOG_DIR.glob("*.log")):
        try:
            result = parse_log(logfile)
            if result["config"] and result["completed"]:
                results.append(result)
        except Exception as e:
            print(f"Warning: failed to parse {logfile.name}: {e}")
    return results


# ============================================================================
# NUCLEATION PROBABILITY COMPUTATION
# ============================================================================

def compute_pnuc(parsed_logs):
    """Compute P_nuc per N value with Clopper-Pearson confidence intervals."""
    # Group by N
    groups = defaultdict(lambda: {"emerged": 0, "total": 0, "N": 0, "n_sub": 0})

    for log in parsed_logs:
        N = log["config"]["N"]
        n_sub = log["config"]["n_sub"]
        for stella in log["stellae"]:
            groups[N]["total"] += 1
            groups[N]["N"] = N
            groups[N]["n_sub"] = n_sub
            if stella["emerged"]:
                groups[N]["emerged"] += 1

    # Compute P_nuc and confidence intervals
    results = []
    for N in sorted(groups.keys()):
        g = groups[N]
        k = g["emerged"]
        n = g["total"]
        p = k / n if n > 0 else 0

        # Clopper-Pearson 95% CI
        if k == 0:
            ci_low = 0.0
        else:
            ci_low = beta_dist.ppf(0.025, k, n - k + 1)
        if k == n:
            ci_high = 1.0
        else:
            ci_high = beta_dist.ppf(0.975, k + 1, n - k)

        results.append({
            "n_sub": g["n_sub"],
            "N": N,
            "emerged": k,
            "total": n,
            "P_nuc": p,
            "CI_low": ci_low,
            "CI_high": ci_high,
        })

    return results


# ============================================================================
# SIGMOID FITTING
# ============================================================================

def logistic(N, N50, k):
    """Logistic function: P = 1 / (1 + exp(-k*(N - N50)))"""
    return 1.0 / (1.0 + np.exp(-k * (N - N50)))


def logistic_3param(N, N50, k, P_max):
    """3-parameter logistic: P = P_max / (1 + exp(-k*(N - N50)))"""
    return P_max / (1.0 + np.exp(-k * (N - N50)))


def fit_sigmoid(pnuc_data):
    """Fit logistic function to P_nuc(N) data.

    Returns dict with fit parameters and diagnostics.
    """
    N_arr = np.array([d["N"] for d in pnuc_data])
    P_arr = np.array([d["P_nuc"] for d in pnuc_data])
    n_arr = np.array([d["total"] for d in pnuc_data])

    # Weights: inverse binomial variance (with floor to avoid division by zero)
    var = np.maximum(P_arr * (1 - P_arr) / n_arr, 1e-6)
    weights = 1.0 / var

    results = {}

    # --- Model 1: 2-parameter logistic (N₅₀, k) ---
    try:
        popt, pcov = curve_fit(logistic, N_arr, P_arr, p0=[600, 0.005],
                               sigma=np.sqrt(var), absolute_sigma=True,
                               maxfev=10000)
        N50, k = popt
        N50_se, k_se = np.sqrt(np.diag(pcov))

        P_pred = logistic(N_arr, N50, k)
        SSR = np.sum((P_arr - P_pred) ** 2)
        SST = np.sum((P_arr - np.mean(P_arr)) ** 2)
        R2 = 1 - SSR / SST

        results["logistic_2p"] = {
            "N50": float(N50),
            "N50_SE": float(N50_se),
            "k": float(k),
            "k_SE": float(k_se),
            "R2": float(R2),
            "SSR": float(SSR),
            "N50_95CI": [float(N50 - 1.96 * N50_se), float(N50 + 1.96 * N50_se)],
        }
    except Exception as e:
        results["logistic_2p"] = {"error": str(e)}

    # --- Model 2: 3-parameter logistic (N₅₀, k, P_max) ---
    try:
        popt3, pcov3 = curve_fit(logistic_3param, N_arr, P_arr,
                                 p0=[600, 0.005, 0.9],
                                 sigma=np.sqrt(var), absolute_sigma=True,
                                 bounds=([0, 0, 0.5], [2000, 1.0, 1.0]),
                                 maxfev=10000)
        N50_3, k_3, Pmax = popt3
        se3 = np.sqrt(np.diag(pcov3))

        P_pred3 = logistic_3param(N_arr, N50_3, k_3, Pmax)
        SSR3 = np.sum((P_arr - P_pred3) ** 2)
        R2_3 = 1 - SSR3 / SST

        results["logistic_3p"] = {
            "N50": float(N50_3),
            "N50_SE": float(se3[0]),
            "k": float(k_3),
            "k_SE": float(se3[1]),
            "P_max": float(Pmax),
            "P_max_SE": float(se3[2]),
            "R2": float(R2_3),
            "SSR": float(SSR3),
            "N50_95CI": [float(N50_3 - 1.96 * se3[0]),
                         float(N50_3 + 1.96 * se3[0])],
        }
    except Exception as e:
        results["logistic_3p"] = {"error": str(e)}

    # --- Bootstrap CI for N₅₀ ---
    n_boot = 10000
    N50_boot = []
    rng = np.random.default_rng(42)

    for _ in range(n_boot):
        # Resample P_nuc from binomial at each N
        P_boot = np.array([
            rng.binomial(d["total"], d["P_nuc"]) / d["total"]
            for d in pnuc_data
        ])
        try:
            popt_b, _ = curve_fit(logistic, N_arr, P_boot, p0=[600, 0.005],
                                  maxfev=5000)
            if 0 < popt_b[0] < 3000:  # sanity check
                N50_boot.append(popt_b[0])
        except Exception:
            pass

    if N50_boot:
        N50_boot = np.array(N50_boot)
        results["bootstrap"] = {
            "n_successful": len(N50_boot),
            "N50_mean": float(np.mean(N50_boot)),
            "N50_median": float(np.median(N50_boot)),
            "N50_std": float(np.std(N50_boot)),
            "N50_95CI": [float(np.percentile(N50_boot, 2.5)),
                         float(np.percentile(N50_boot, 97.5))],
        }

    # --- Test N₅₀ = 729 ---
    if "logistic_2p" in results and "error" not in results["logistic_2p"]:
        N50_fit = results["logistic_2p"]["N50"]
        N50_se_fit = results["logistic_2p"]["N50_SE"]
        z = (N50_fit - 729) / N50_se_fit
        results["test_729"] = {
            "N50_fit": float(N50_fit),
            "N50_SE": float(N50_se_fit),
            "target": 729,
            "deviation_tiles": float(N50_fit - 729),
            "deviation_percent": float(abs(N50_fit - 729) / 729 * 100),
            "z_score": float(z),
            "consistent": bool(abs(z) < 1.96),
            "p_value": float(2 * (1 - __import__('scipy').stats.norm.cdf(abs(z)))),
        }

    if "bootstrap" in results:
        ci = results["bootstrap"]["N50_95CI"]
        results["test_729"]["bootstrap_consistent"] = bool(ci[0] <= 729 <= ci[1])
        results["test_729"]["bootstrap_95CI"] = ci

    return results


# ============================================================================
# PLOTTING
# ============================================================================

def plot_sigmoid(pnuc_data, fit_results, outpath):
    """Plot P_nuc(N) with logistic fit and 729 marker."""
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
    except ImportError:
        print("matplotlib not available, skipping plot")
        return

    N_arr = np.array([d["N"] for d in pnuc_data])
    P_arr = np.array([d["P_nuc"] for d in pnuc_data])
    CI_lo = np.array([d["CI_low"] for d in pnuc_data])
    CI_hi = np.array([d["CI_high"] for d in pnuc_data])

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))

    # --- Left panel: P_nuc(N) with logistic fit ---
    ax1.errorbar(N_arr, P_arr, yerr=[P_arr - CI_lo, CI_hi - P_arr],
                 fmt='ko', capsize=3, markersize=6, label='Data (52 experiments/point)')

    # Fit curve
    N_fine = np.linspace(100, 1200, 500)
    fit_2p = fit_results.get("logistic_2p", {})
    if "N50" in fit_2p:
        P_fit = logistic(N_fine, fit_2p["N50"], fit_2p["k"])
        ax1.plot(N_fine, P_fit, 'b-', linewidth=2,
                 label=f'Logistic fit: N₅₀ = {fit_2p["N50"]:.0f} ± {fit_2p["N50_SE"]:.0f}')

    fit_3p = fit_results.get("logistic_3p", {})
    if "N50" in fit_3p:
        P_fit3 = logistic_3param(N_fine, fit_3p["N50"], fit_3p["k"], fit_3p["P_max"])
        ax1.plot(N_fine, P_fit3, 'r--', linewidth=1.5,
                 label=f'3-param: N₅₀ = {fit_3p["N50"]:.0f}, P_max = {fit_3p["P_max"]:.2f}')

    # 729 marker
    ax1.axvline(729, color='green', linestyle=':', linewidth=2, alpha=0.7,
                label='3⁶ = 729')
    ax1.axhline(0.5, color='gray', linestyle=':', alpha=0.5)

    # Bootstrap CI shading
    boot = fit_results.get("bootstrap", {})
    if "N50_95CI" in boot:
        ax1.axvspan(boot["N50_95CI"][0], boot["N50_95CI"][1],
                     alpha=0.15, color='blue', label=f'Bootstrap 95% CI: [{boot["N50_95CI"][0]:.0f}, {boot["N50_95CI"][1]:.0f}]')

    ax1.set_xlabel('N (tiles per stella)', fontsize=12)
    ax1.set_ylabel('P_nuc (nucleation probability)', fontsize=12)
    ax1.set_title('Priority 5: Sigmoid Midpoint Campaign', fontsize=13)
    ax1.legend(fontsize=9, loc='lower right')
    ax1.set_ylim(-0.05, 1.05)
    ax1.grid(True, alpha=0.3)

    # --- Right panel: zoom on transition region ---
    ax2.errorbar(N_arr, P_arr, yerr=[P_arr - CI_lo, CI_hi - P_arr],
                 fmt='ko', capsize=3, markersize=6)

    if "N50" in fit_2p:
        P_fit = logistic(N_fine, fit_2p["N50"], fit_2p["k"])
        ax2.plot(N_fine, P_fit, 'b-', linewidth=2)

    ax2.axvline(729, color='green', linestyle=':', linewidth=2, alpha=0.7)
    ax2.axhline(0.5, color='gray', linestyle=':', alpha=0.5)

    if "N50_95CI" in boot:
        ax2.axvspan(boot["N50_95CI"][0], boot["N50_95CI"][1],
                     alpha=0.15, color='blue')

    ax2.set_xlim(300, 1100)
    ax2.set_ylim(0.1, 0.9)
    ax2.set_xlabel('N (tiles per stella)', fontsize=12)
    ax2.set_ylabel('P_nuc', fontsize=12)
    ax2.set_title('Transition Region (zoom)', fontsize=13)
    ax2.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig(outpath, dpi=150, bbox_inches='tight')
    print(f"Plot saved: {outpath}")


# ============================================================================
# MAIN
# ============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="Priority 5: Sigmoid midpoint analysis")
    parser.add_argument("--plot", action="store_true",
                        help="Generate plots")
    args = parser.parse_args()

    print("=" * 70)
    print("Priority 5: Sigmoid Midpoint Analysis")
    print("=" * 70)

    # 1. Parse logs
    print(f"\nParsing logs from {LOG_DIR}...")
    parsed = parse_all_logs()
    print(f"  Parsed {len(parsed)} completed log files")

    # 2. Compute P_nuc
    pnuc_data = compute_pnuc(parsed)

    print(f"\n{'n_sub':>5}  {'N':>6}  {'emerged':>7} / {'total':>5}  {'P_nuc':>6}  "
          f"{'95% CI':>15}")
    print("-" * 60)
    for d in pnuc_data:
        print(f"{d['n_sub']:>5}  {d['N']:>6}  {d['emerged']:>7} / {d['total']:>5}  "
              f"{d['P_nuc']:>6.3f}  [{d['CI_low']:.3f}, {d['CI_high']:.3f}]")

    # 3. Fit sigmoid
    print("\nFitting logistic functions...")
    fit_results = fit_sigmoid(pnuc_data)

    # 4. Report results
    print("\n" + "=" * 70)
    print("FIT RESULTS")
    print("=" * 70)

    fit_2p = fit_results.get("logistic_2p", {})
    if "N50" in fit_2p:
        print(f"\n  2-Parameter Logistic: P = 1/(1 + exp(-k(N - N₅₀)))")
        print(f"    N₅₀ = {fit_2p['N50']:.1f} ± {fit_2p['N50_SE']:.1f}")
        print(f"    k   = {fit_2p['k']:.5f} ± {fit_2p['k_SE']:.5f}")
        print(f"    R²  = {fit_2p['R2']:.4f}")
        print(f"    95% CI for N₅₀: [{fit_2p['N50_95CI'][0]:.0f}, {fit_2p['N50_95CI'][1]:.0f}]")

    fit_3p = fit_results.get("logistic_3p", {})
    if "N50" in fit_3p:
        print(f"\n  3-Parameter Logistic: P = P_max/(1 + exp(-k(N - N₅₀)))")
        print(f"    N₅₀   = {fit_3p['N50']:.1f} ± {fit_3p['N50_SE']:.1f}")
        print(f"    k     = {fit_3p['k']:.5f} ± {fit_3p['k_SE']:.5f}")
        print(f"    P_max = {fit_3p['P_max']:.3f} ± {fit_3p['P_max_SE']:.3f}")
        print(f"    R²    = {fit_3p['R2']:.4f}")
        print(f"    95% CI for N₅₀: [{fit_3p['N50_95CI'][0]:.0f}, {fit_3p['N50_95CI'][1]:.0f}]")

    boot = fit_results.get("bootstrap", {})
    if boot:
        print(f"\n  Bootstrap (n={boot['n_successful']}):")
        print(f"    N₅₀ mean   = {boot['N50_mean']:.1f}")
        print(f"    N₅₀ median = {boot['N50_median']:.1f}")
        print(f"    N₅₀ std    = {boot['N50_std']:.1f}")
        print(f"    95% CI: [{boot['N50_95CI'][0]:.0f}, {boot['N50_95CI'][1]:.0f}]")

    test = fit_results.get("test_729", {})
    if test:
        print(f"\n  Test: N₅₀ = 3⁶ = 729")
        print(f"    N₅₀ fit = {test['N50_fit']:.1f}")
        print(f"    Deviation: {test['deviation_tiles']:.1f} tiles "
              f"({test['deviation_percent']:.1f}%)")
        print(f"    z-score: {test['z_score']:.2f}")
        print(f"    p-value: {test['p_value']:.4f}")
        print(f"    Consistent (|z| < 1.96): {'YES' if test['consistent'] else 'NO'}")
        if "bootstrap_consistent" in test:
            print(f"    Bootstrap 95% CI contains 729: "
                  f"{'YES' if test['bootstrap_consistent'] else 'NO'}")
            print(f"    Bootstrap 95% CI: [{test['bootstrap_95CI'][0]:.0f}, "
                  f"{test['bootstrap_95CI'][1]:.0f}]")

        # Verdict
        print(f"\n  {'='*50}")
        if test.get("consistent") and test.get("bootstrap_consistent"):
            print(f"  VERDICT: N₅₀ = 729 is CONSISTENT with the data")
            print(f"  The sigmoid midpoint cannot be distinguished from 3⁶ = 729")
        elif test.get("consistent") or test.get("bootstrap_consistent"):
            print(f"  VERDICT: N₅₀ = 729 is MARGINALLY consistent")
        else:
            print(f"  VERDICT: N₅₀ = 729 is NOT consistent with the data")
            print(f"  The sigmoid midpoint is at N₅₀ = {test['N50_fit']:.0f}, "
                  f"significantly different from 729")
        print(f"  {'='*50}")

    # 5. Save results
    output = {
        "timestamp": datetime.now().isoformat(),
        "campaign": {
            "log_dir": str(LOG_DIR),
            "n_logs_parsed": len(parsed),
            "n_stellae_total": sum(d["total"] for d in pnuc_data),
        },
        "pnuc_data": pnuc_data,
        "fits": fit_results,
    }

    with open(RESULTS_FILE, "w") as f:
        json.dump(output, f, indent=2, default=str)
    print(f"\nResults saved: {RESULTS_FILE}")

    # 6. Plot
    if args.plot:
        plot_dir = REPO_ROOT / "verification" / "plots"
        plot_dir.mkdir(parents=True, exist_ok=True)
        plot_sigmoid(pnuc_data, fit_results,
                     plot_dir / "sigmoid_midpoint_p5.png")


if __name__ == "__main__":
    main()
