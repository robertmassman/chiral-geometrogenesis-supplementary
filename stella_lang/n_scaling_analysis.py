#!/usr/bin/env python3
"""
N-Scaling Analysis: Parse Campaign Logs and Fit T_emerge(N)
===========================================================

Parses logs from n_scaling_campaign.py, extracts per-stella emergence times,
and fits competing models:
  - Model A (Poisson):     T_emerge = C / N
  - Model B (Cooperative): T_emerge = C * N^(η-1)

Produces:
  1. Summary table of all emergence times
  2. Model fits with AIC/BIC comparison
  3. Plots: T_emerge vs N with model curves, residuals
  4. JSON results for downstream use

Related Documents:
  - Lemma 0.0.XXe-NP §3.5 (Models A and B)
  - Campaign: stella_lang/n_scaling_campaign.py

Usage:
  python3 stella_lang/n_scaling_analysis.py
  python3 stella_lang/n_scaling_analysis.py --plot
  python3 stella_lang/n_scaling_analysis.py --update-lemma
"""

import argparse
import json
import re
import os
import sys
from pathlib import Path
from datetime import datetime
from collections import defaultdict

import numpy as np

# ============================================================================
# PATHS
# ============================================================================

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
LOG_DIR = REPO_ROOT / "verification" / "stella_lang" / "n_scaling_logs"
PLOT_DIR = REPO_ROOT / "verification" / "plots"
RESULTS_FILE = REPO_ROOT / "verification" / "stella_lang" / "n_scaling_results.json"


# ============================================================================
# LOG PARSING
# ============================================================================

def parse_log(logfile):
    """Parse a single campaign log file.

    Returns dict with:
      - config: {n_sub, N, pairing, seed, epochs}
      - stellae: list of {stella_id, emergence_epoch or None}
      - completed: bool
      - wall_time: float (seconds)
    """
    text = logfile.read_text()
    lines = text.split("\n")

    result = {
        "logfile": str(logfile),
        "config": {},
        "stellae": [],
        "completed": False,
        "wall_time": None,
    }

    # Parse config from header
    for line in lines:
        m = re.search(r"Subdivisions:\s+(\d+)\s+per edge", line)
        if m:
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

    # Parse census lines to find first emergence per stella
    # Format: "  CENSUS epoch 100000:  Stella   0: 5 / 1666 (0.3%)"
    # or "  Stella   0: 0 / 1666 (0.0%)"
    n_stellae = result["config"].get("n_stellae", 4)
    first_emergence = {}  # stella_id -> first epoch with replicators

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

    # Build stellae list
    for s in range(n_stellae):
        result["stellae"].append({
            "stella_id": s,
            "emergence_epoch": first_emergence.get(s, None),
        })

    # Check completion
    m = re.search(r"Completed (\d+) epochs in ([\d.]+)s", text)
    if m:
        result["completed"] = True
        result["wall_time"] = float(m.group(2))

    return result


def parse_all_logs():
    """Parse all log files in the campaign directory."""
    if not LOG_DIR.exists():
        print(f"No log directory found: {LOG_DIR}")
        return []

    results = []
    for logfile in sorted(LOG_DIR.glob("*.log")):
        try:
            result = parse_log(logfile)
            if result["config"]:
                results.append(result)
        except Exception as e:
            print(f"Warning: failed to parse {logfile.name}: {e}")
    return results


# ============================================================================
# DATA EXTRACTION
# ============================================================================

def extract_emergence_data(results):
    """Extract emergence times into structured arrays.

    Returns list of dicts: {N, pairing, seed, stella_id, T_emerge, censored}
    """
    data = []
    for r in results:
        if not r["completed"]:
            continue
        cfg = r["config"]
        N = cfg.get("N")
        pairing = cfg.get("pairing")
        seed = cfg.get("seed")
        epochs = cfg.get("epochs", 5_000_000)

        for s in r["stellae"]:
            T = s["emergence_epoch"]
            data.append({
                "N": N,
                "pairing": pairing,
                "seed": seed,
                "stella_id": s["stella_id"],
                "T_emerge": T if T is not None else epochs,
                "censored": T is None,  # True if no emergence detected
            })
    return data


# ============================================================================
# MODEL FITTING
# ============================================================================

def fit_poisson_model(N_arr, T_arr, censored_arr):
    """Fit Model A: T = C/N (Poisson nucleation).

    For uncensored data, log(T) = log(C) - log(N).
    Uses simple OLS on uncensored points. Returns C, R², residuals.
    """
    mask = ~censored_arr
    if mask.sum() < 2:
        return None

    logN = np.log(N_arr[mask])
    logT = np.log(T_arr[mask])

    # Fit: logT = a + b*logN, expecting b ≈ -1
    A = np.vstack([np.ones_like(logN), logN]).T
    coeffs, residuals_ss, _, _ = np.linalg.lstsq(A, logT, rcond=None)
    a, b = coeffs

    C = np.exp(a)
    logT_pred = a + b * logN
    ss_res = np.sum((logT - logT_pred) ** 2)
    ss_tot = np.sum((logT - np.mean(logT)) ** 2)
    R2 = 1 - ss_res / ss_tot if ss_tot > 0 else 0

    n = mask.sum()
    k = 2  # parameters
    aic = n * np.log(ss_res / n + 1e-30) + 2 * k
    bic = n * np.log(ss_res / n + 1e-30) + k * np.log(n)

    return {
        "model": "A (Poisson: T = C/N)",
        "C": float(C),
        "exponent": float(b),
        "expected_exponent": -1.0,
        "R2": float(R2),
        "AIC": float(aic),
        "BIC": float(bic),
        "n_uncensored": int(mask.sum()),
        "n_censored": int((~mask).sum()),
    }


def fit_cooperative_model(N_arr, T_arr, censored_arr):
    """Fit Model B: T = C * N^(η-1) (cooperative assembly).

    For uncensored data, log(T) = log(C) + (η-1)*log(N).
    Returns C, η, R², residuals.
    """
    mask = ~censored_arr
    if mask.sum() < 2:
        return None

    logN = np.log(N_arr[mask])
    logT = np.log(T_arr[mask])

    A = np.vstack([np.ones_like(logN), logN]).T
    coeffs, _, _, _ = np.linalg.lstsq(A, logT, rcond=None)
    a, b = coeffs

    C = np.exp(a)
    eta = b + 1  # T ∝ N^(η-1), so exponent = η-1
    logT_pred = a + b * logN
    ss_res = np.sum((logT - logT_pred) ** 2)
    ss_tot = np.sum((logT - np.mean(logT)) ** 2)
    R2 = 1 - ss_res / ss_tot if ss_tot > 0 else 0

    n = mask.sum()
    k = 2
    aic = n * np.log(ss_res / n + 1e-30) + 2 * k
    bic = n * np.log(ss_res / n + 1e-30) + k * np.log(n)

    return {
        "model": "B (Cooperative: T = C * N^(η-1))",
        "C": float(C),
        "eta": float(eta),
        "exponent": float(b),
        "R2": float(R2),
        "AIC": float(aic),
        "BIC": float(bic),
        "n_uncensored": int(mask.sum()),
        "n_censored": int((~mask).sum()),
    }


def fit_constant_model(N_arr, T_arr, censored_arr):
    """Fit Model C: T = C (rate-limited, N-independent).

    log(T) = log(C). Returns C, R².
    """
    mask = ~censored_arr
    if mask.sum() < 2:
        return None

    logT = np.log(T_arr[mask])
    logN = np.log(N_arr[mask])
    C = np.exp(np.mean(logT))

    ss_res = np.sum((logT - np.mean(logT)) ** 2)
    ss_tot = np.sum((logT - np.mean(logT)) ** 2)  # same as ss_res for constant model
    # R² against a model with slope:
    logT_pred_slope = np.polyval(np.polyfit(logN, logT, 1), logN)
    ss_tot_full = np.sum((logT - np.mean(logT)) ** 2)

    n = mask.sum()
    k = 1
    aic = n * np.log(ss_res / n + 1e-30) + 2 * k
    bic = n * np.log(ss_res / n + 1e-30) + k * np.log(n)

    return {
        "model": "C (Rate-limited: T = const)",
        "C": float(C),
        "exponent": 0.0,
        "R2": 0.0,  # by definition, no N-dependence explained
        "AIC": float(aic),
        "BIC": float(bic),
        "n_uncensored": int(mask.sum()),
        "n_censored": int((~mask).sum()),
    }


# ============================================================================
# SUMMARY AND REPORTING
# ============================================================================

def compute_summary_stats(data):
    """Compute per-(N, pairing) summary statistics."""
    groups = defaultdict(list)
    for d in data:
        key = (d["N"], d["pairing"])
        groups[key].append(d)

    summary = []
    for (N, pairing), entries in sorted(groups.items()):
        T_all = [e["T_emerge"] for e in entries]
        T_uncensored = [e["T_emerge"] for e in entries if not e["censored"]]
        n_censored = sum(1 for e in entries if e["censored"])

        row = {
            "N": N,
            "pairing": pairing,
            "n_total": len(entries),
            "n_censored": n_censored,
            "n_emerged": len(T_uncensored),
        }

        if T_uncensored:
            T_unc = np.array(T_uncensored)
            row["median_T"] = float(np.median(T_unc))
            row["mean_T"] = float(np.mean(T_unc))
            row["std_T"] = float(np.std(T_unc))
            row["min_T"] = float(np.min(T_unc))
            row["max_T"] = float(np.max(T_unc))
            row["IQR_low"] = float(np.percentile(T_unc, 25))
            row["IQR_high"] = float(np.percentile(T_unc, 75))
        else:
            row["median_T"] = None
            row["mean_T"] = None

        summary.append(row)

    return summary


def print_summary_table(summary):
    """Print formatted summary table."""
    print("\n" + "=" * 90)
    print("EMERGENCE TIME SUMMARY (per N, pairing mode)")
    print("=" * 90)
    print(f"{'N':>6} | {'Pairing':>7} | {'n':>3} | {'Cens':>4} | {'Median T':>12} | "
          f"{'IQR':>20} | {'γ_eff':>8}")
    print("-" * 90)

    for row in summary:
        N = row["N"]
        pairing = row["pairing"]
        n = row["n_total"]
        cens = row["n_censored"]

        if row["median_T"] is not None:
            med = f"{row['median_T']:.0f}"
            iqr_lo = row.get("IQR_low")
            iqr_hi = row.get("IQR_high")
            iqr = f"[{iqr_lo:.0f}, {iqr_hi:.0f}]" if iqr_lo is not None else "—"
            # γ_eff = ln2 / (median_T * N * r/3^L) ... simplified as programs/tile/epoch
            # From §3.3: γ_eff = ln(2) * 3^L / (r * T * N)
            r = 120
            gamma = np.log(2) * (3**24) / (r * row["median_T"] * N) if row["median_T"] > 0 else 0
            gamma_str = f"{gamma:.2f}" if gamma < 100 else f"{gamma:.1e}"
        else:
            med = "> 5M"
            iqr = "—"
            gamma_str = "—"

        print(f"{N:>6} | {pairing:>7} | {n:>3} | {cens:>4} | {med:>12} | {iqr:>20} | {gamma_str:>8}")

    print("-" * 90)


def print_model_comparison(fits, pairing):
    """Print model comparison for a given pairing mode."""
    print(f"\n{'='*70}")
    print(f"MODEL FITS — {pairing.upper()} pairing")
    print(f"{'='*70}")

    for fit in fits:
        if fit is None:
            continue
        print(f"\n  {fit['model']}")
        print(f"    Exponent: {fit['exponent']:.3f}")
        if "eta" in fit:
            print(f"    η (cooperative): {fit['eta']:.3f}")
        print(f"    C: {fit['C']:.2e}")
        print(f"    R²: {fit['R2']:.4f}")
        print(f"    AIC: {fit['AIC']:.1f}, BIC: {fit['BIC']:.1f}")
        print(f"    Data: {fit['n_uncensored']} uncensored, {fit['n_censored']} censored")

    # Model selection
    valid = [f for f in fits if f is not None]
    if len(valid) >= 2:
        best = min(valid, key=lambda f: f["AIC"])
        print(f"\n  → Best model (lowest AIC): {best['model']}")
        print(f"    Fitted exponent: {best['exponent']:.3f}")
        if abs(best["exponent"] - (-1.0)) < 0.3:
            print(f"    Consistent with Poisson (T ∝ 1/N)")
        elif best["exponent"] > 0:
            print(f"    Consistent with cooperative assembly (T grows with N)")
        else:
            print(f"    Intermediate scaling")


# ============================================================================
# PLOTTING
# ============================================================================

def make_plots(data, summary, fits_by_pairing):
    """Generate N-scaling plots."""
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
    except ImportError:
        print("matplotlib not available, skipping plots")
        return

    PLOT_DIR.mkdir(parents=True, exist_ok=True)

    fig, axes = plt.subplots(1, 2, figsize=(14, 6))

    for idx, pairing in enumerate(["local", "global"]):
        ax = axes[idx]

        # Scatter all emergence times
        for d in data:
            if d["pairing"] != pairing:
                continue
            marker = "v" if d["censored"] else "o"
            color = "red" if d["censored"] else "steelblue"
            alpha = 0.3 if d["censored"] else 0.6
            ax.scatter(d["N"], d["T_emerge"], marker=marker, color=color,
                       alpha=alpha, s=30, zorder=2)

        # Plot medians with IQR
        pairing_summary = [s for s in summary if s["pairing"] == pairing and s["median_T"] is not None]
        if pairing_summary:
            Ns = [s["N"] for s in pairing_summary]
            meds = [s["median_T"] for s in pairing_summary]
            iqr_lo = [s.get("IQR_low", s["median_T"]) for s in pairing_summary]
            iqr_hi = [s.get("IQR_high", s["median_T"]) for s in pairing_summary]
            yerr_lo = [m - lo for m, lo in zip(meds, iqr_lo)]
            yerr_hi = [hi - m for m, hi in zip(meds, iqr_hi)]
            ax.errorbar(Ns, meds, yerr=[yerr_lo, yerr_hi],
                        fmt="s", color="darkblue", markersize=8, capsize=5,
                        linewidth=2, zorder=3, label="Median ± IQR")

        # Plot model fits
        fits = fits_by_pairing.get(pairing, [])
        # Dynamically set plot range based on data
        all_N = [d["N"] for d in data if d["pairing"] == pairing]
        N_lo = min(all_N) * 0.8 if all_N else 1400
        N_hi = max(all_N) * 1.2 if all_N else 4500
        N_range = np.linspace(N_lo, N_hi, 200)
        colors_model = ["green", "orange", "gray"]
        for i, fit in enumerate(fits):
            if fit is None:
                continue
            T_pred = fit["C"] * N_range ** fit["exponent"]
            ax.plot(N_range, T_pred, "--", color=colors_model[i % 3],
                    linewidth=1.5, alpha=0.8,
                    label=f"{fit['model'].split('(')[0].strip()} (exp={fit['exponent']:.2f})")

        ax.set_xlabel("N (tiles per stella)")
        ax.set_ylabel("T_emerge (epochs)")
        ax.set_title(f"{pairing.capitalize()} pairing")
        ax.set_yscale("log")
        ax.set_xscale("log")
        ax.legend(fontsize=8, loc="best")
        ax.grid(True, alpha=0.3)

    fig.suptitle("N-Scaling of Nucleation Time (Lemma 0.0.XXe-NP §3.5.3)", fontsize=13)
    plt.tight_layout()

    outpath = PLOT_DIR / "n_scaling_T_emerge_vs_N.png"
    plt.savefig(outpath, dpi=150, bbox_inches="tight")
    print(f"\nPlot saved: {outpath}")
    plt.close()

    # Discriminating ratio plot
    fig2, ax2 = plt.subplots(figsize=(8, 5))
    for pairing in ["local", "global"]:
        ps = [s for s in summary if s["pairing"] == pairing and s["median_T"] is not None]
        if len(ps) < 2:
            continue
        # Ratio relative to smallest N
        ref = min(ps, key=lambda s: s["N"])
        Ns = [s["N"] for s in ps]
        ratios = [s["median_T"] / ref["median_T"] for s in ps]
        ax2.plot(Ns, ratios, "o-", label=f"{pairing}", markersize=8)

    # Model A prediction: ratio = N_ref / N
    N_ref = min(s["N"] for s in summary if s["median_T"] is not None) if summary else 1666
    all_N_vals = [s["N"] for s in summary if s["median_T"] is not None]
    N_lo = min(all_N_vals) * 0.8 if all_N_vals else 1400
    N_hi = max(all_N_vals) * 1.2 if all_N_vals else 4500
    N_range = np.linspace(N_lo, N_hi, 200)
    ax2.plot(N_range, N_ref / N_range, "--", color="green", alpha=0.7, label="Model A: T∝1/N")
    # Model B (η=4) prediction: ratio = (N/N_ref)^3
    ax2.plot(N_range, (N_range / N_ref) ** 3, "--", color="orange", alpha=0.7, label="Model B: T∝N³ (η=4)")

    ax2.set_xlabel("N (tiles per stella)")
    ax2.set_ylabel(f"T_emerge / T_emerge(N={N_ref})")
    ax2.set_title("Discriminating Test: median(T₄₁₀₈)/median(T₁₆₆₆)")
    ax2.legend()
    ax2.grid(True, alpha=0.3)
    ax2.set_yscale("log")

    outpath2 = PLOT_DIR / "n_scaling_discriminating_ratio.png"
    plt.savefig(outpath2, dpi=150, bbox_inches="tight")
    print(f"Plot saved: {outpath2}")
    plt.close()


# ============================================================================
# MAIN
# ============================================================================

def main():
    parser = argparse.ArgumentParser(description="N-scaling analysis (Lemma 0.0.XXe-NP §3.5.3)")
    parser.add_argument("--plot", action="store_true", help="Generate plots")
    parser.add_argument("--update-lemma", action="store_true",
                        help="Print suggested text for updating the lemma")
    args = parser.parse_args()

    # Parse all logs
    results = parse_all_logs()
    if not results:
        print("No log files found. Run the campaign first:")
        print("  python3 stella_lang/n_scaling_campaign.py")
        return

    n_complete = sum(1 for r in results if r["completed"])
    n_total = len(results)
    print(f"Parsed {n_total} log files ({n_complete} complete)")

    # Extract emergence data
    data = extract_emergence_data(results)
    if not data:
        print("No emergence data extracted.")
        return

    n_emerged = sum(1 for d in data if not d["censored"])
    n_censored = sum(1 for d in data if d["censored"])
    print(f"Emergence data: {len(data)} stellae ({n_emerged} emerged, {n_censored} censored)")

    # Summary statistics
    summary = compute_summary_stats(data)
    print_summary_table(summary)

    # Model fitting per pairing mode
    fits_by_pairing = {}
    for pairing in ["local", "global"]:
        pairing_data = [d for d in data if d["pairing"] == pairing]
        if not pairing_data:
            continue

        N_arr = np.array([d["N"] for d in pairing_data], dtype=float)
        T_arr = np.array([d["T_emerge"] for d in pairing_data], dtype=float)
        cens_arr = np.array([d["censored"] for d in pairing_data])

        fit_a = fit_poisson_model(N_arr, T_arr, cens_arr)
        fit_b = fit_cooperative_model(N_arr, T_arr, cens_arr)
        fit_c = fit_constant_model(N_arr, T_arr, cens_arr)

        fits = [fit_a, fit_b, fit_c]
        fits_by_pairing[pairing] = fits
        print_model_comparison(fits, pairing)

    # Discriminating test from §3.5.3
    print(f"\n{'='*70}")
    print("DISCRIMINATING TEST (§3.5.3)")
    print(f"{'='*70}")
    for pairing in ["local", "global"]:
        ps = {s["N"]: s for s in summary if s["pairing"] == pairing and s["median_T"] is not None}
        if 1666 in ps and 4108 in ps:
            ratio = ps[4108]["median_T"] / ps[1666]["median_T"]
            print(f"\n  {pairing}: median(T_4108) / median(T_1666) = {ratio:.3f}")
            print(f"    Model A predicts: {1666/4108:.3f}")
            print(f"    Model B (η=4) predicts: {(4108/1666)**3:.1f}")
            if ratio < 1:
                print(f"    → Consistent with Model A (larger N → faster emergence)")
            else:
                print(f"    → Consistent with Model B (larger N → slower or same emergence)")
        else:
            have = sorted(ps.keys())
            print(f"\n  {pairing}: insufficient data (have N={have}, need N=1666 and N=4108)")

    # Save results
    output = {
        "timestamp": datetime.now().isoformat(),
        "campaign": {
            "n_logs": n_total,
            "n_complete": n_complete,
            "n_stellae": len(data),
            "n_emerged": n_emerged,
            "n_censored": n_censored,
        },
        "summary": summary,
        "fits": {
            pairing: [f for f in fits if f is not None]
            for pairing, fits in fits_by_pairing.items()
        },
        "raw_data": data,
    }

    RESULTS_FILE.parent.mkdir(parents=True, exist_ok=True)
    with open(RESULTS_FILE, "w") as f:
        json.dump(output, f, indent=2, default=str)
    print(f"\nResults saved: {RESULTS_FILE}")

    # Plots
    if args.plot:
        make_plots(data, summary, fits_by_pairing)

    # Suggested lemma update
    if args.update_lemma:
        print(f"\n{'='*70}")
        print("SUGGESTED LEMMA UPDATE (§3.5.3 → §3.5.4)")
        print(f"{'='*70}")
        print("\nAdd the following after §3.5.3:\n")
        print("#### 3.5.4 Multi-Seed Campaign Results\n")
        for pairing in ["local", "global"]:
            ps = [s for s in summary if s["pairing"] == pairing and s["median_T"] is not None]
            if not ps:
                continue
            print(f"**{pairing.capitalize()} pairing:**\n")
            print(f"| N | Median T | IQR | n_emerged/total |")
            print(f"|---|---------|-----|-----------------|")
            for s in ps:
                ne = s["n_emerged"]
                nt = s["n_total"]
                iqr = f"[{s.get('IQR_low',0):.0f}, {s.get('IQR_high',0):.0f}]"
                print(f"| {s['N']} | {s['median_T']:.0f} | {iqr} | {ne}/{nt} |")
            print()

        fits_a = {p: next((f for f in fs if "Poisson" in f.get("model", "")), None)
                  for p, fs in fits_by_pairing.items()}
        for pairing, fit in fits_a.items():
            if fit:
                print(f"Model A fit ({pairing}): exponent = {fit['exponent']:.3f} "
                      f"(expected -1.0), R² = {fit['R2']:.3f}")


if __name__ == "__main__":
    main()
