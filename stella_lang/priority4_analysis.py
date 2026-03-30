#!/usr/bin/env python3
"""
Priority 4 Analysis: Large-N Scaling Confirmation
==================================================

Analyzes the extended N-scaling data (N = 1,666 to 50,050) for:
1. Power-law confirmation over 1.5 decades
2. η stability in rolling N windows
3. Logarithmic correction test: T ~ N^(-η) × (1 + a/ln(N))
4. Updated theory comparison

Uses raw uncensored data from n_scaling_results.json.
"""

import json
import numpy as np
from pathlib import Path
from datetime import datetime

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
RESULTS_FILE = REPO_ROOT / "verification" / "stella_lang" / "n_scaling_results.json"
OUTPUT_FILE = REPO_ROOT / "verification" / "stella_lang" / "priority4_analysis_results.json"


def load_data():
    with open(RESULTS_FILE) as f:
        data = json.load(f)
    return data["raw_data"], data["summary"]


def fit_power_law(N_arr, T_arr):
    """Fit log(T) = a + b*log(N), return η = -b, C = exp(a), R², SE."""
    logN = np.log(N_arr)
    logT = np.log(T_arr)
    A = np.vstack([np.ones_like(logN), logN]).T
    coeffs, _, _, _ = np.linalg.lstsq(A, logT, rcond=None)
    a, b = coeffs
    logT_pred = a + b * logN
    ss_res = np.sum((logT - logT_pred) ** 2)
    ss_tot = np.sum((logT - np.mean(logT)) ** 2)
    R2 = 1 - ss_res / ss_tot if ss_tot > 0 else 0
    n = len(N_arr)
    se_b = np.sqrt(ss_res / (n - 2) / np.sum((logN - np.mean(logN))**2)) if n > 2 else np.nan
    return {
        "eta": float(-b),
        "eta_se": float(se_b),
        "C": float(np.exp(a)),
        "exponent": float(b),
        "R2": float(R2),
        "n_points": int(n),
    }


def fit_log_correction(N_arr, T_arr):
    """Fit log(T) = a + b*log(N) + c/ln(N).

    Model: T = C * N^(-η) * exp(c/ln(N)) ≈ C * N^(-η) * (1 + c/ln(N))
    In log space: log(T) = a + b*log(N) + c/ln(N)
    """
    logN = np.log(N_arr)
    logT = np.log(T_arr)
    inv_logN = 1.0 / logN

    A = np.vstack([np.ones_like(logN), logN, inv_logN]).T
    coeffs, _, _, _ = np.linalg.lstsq(A, logT, rcond=None)
    a, b, c = coeffs

    logT_pred = a + b * logN + c * inv_logN
    ss_res = np.sum((logT - logT_pred) ** 2)
    ss_tot = np.sum((logT - np.mean(logT)) ** 2)
    R2 = 1 - ss_res / ss_tot if ss_tot > 0 else 0

    n = len(N_arr)
    k_pure = 2  # pure power law
    k_log = 3   # with log correction
    aic_pure = n * np.log(ss_tot * (1 - fit_power_law(N_arr, T_arr)["R2"]) / n + 1e-30) + 2 * k_pure
    aic_log = n * np.log(ss_res / n + 1e-30) + 2 * k_log

    return {
        "eta": float(-b),
        "C": float(np.exp(a)),
        "log_correction_coeff": float(c),
        "R2": float(R2),
        "AIC_log_model": float(aic_log),
        "AIC_pure_power_law": float(aic_pure),
        "delta_AIC": float(aic_log - aic_pure),
        "n_points": int(n),
        "interpretation": (
            "log correction preferred (ΔAIC < -2)" if (aic_log - aic_pure) < -2
            else "pure power law preferred (ΔAIC > 2)" if (aic_log - aic_pure) > 2
            else "inconclusive (|ΔAIC| < 2)"
        ),
    }


def rolling_eta(raw_data, pairing):
    """Fit η in cumulative N windows to test stability."""
    points = [(d["N"], d["T_emerge"]) for d in raw_data
              if d["pairing"] == pairing and not d["censored"]]
    points.sort(key=lambda x: x[0])

    N_arr = np.array([p[0] for p in points])
    T_arr = np.array([p[1] for p in points])

    unique_N = sorted(set(N_arr))
    results = []

    for cutoff in unique_N:
        mask = N_arr <= cutoff
        if mask.sum() < 5:
            continue
        fit = fit_power_law(N_arr[mask], T_arr[mask])
        results.append({
            "N_max": int(cutoff),
            "eta": fit["eta"],
            "eta_se": fit["eta_se"],
            "R2": fit["R2"],
            "n_points": fit["n_points"],
        })

    return results


def main():
    raw_data, summary = load_data()

    results = {
        "timestamp": datetime.now().isoformat(),
        "description": "Priority 4 analysis: large-N scaling confirmation",
        "n_range": {
            "N_min": min(d["N"] for d in raw_data),
            "N_max": max(d["N"] for d in raw_data),
            "decades": float(np.log10(max(d["N"] for d in raw_data) / min(d["N"] for d in raw_data))),
        },
    }

    print("=" * 70)
    print("PRIORITY 4 ANALYSIS: Large-N Scaling Confirmation")
    print("=" * 70)
    print(f"N range: {results['n_range']['N_min']:,} – {results['n_range']['N_max']:,} "
          f"({results['n_range']['decades']:.2f} decades)")

    # ---- 1. Full-range power law fits ----
    print(f"\n{'='*70}")
    print("1. POWER-LAW FITS (full range)")
    print(f"{'='*70}")

    results["power_law_fits"] = {}
    for pairing in ["global", "local"]:
        points = [(d["N"], d["T_emerge"]) for d in raw_data
                  if d["pairing"] == pairing and not d["censored"]]
        N_arr = np.array([p[0] for p in points])
        T_arr = np.array([p[1] for p in points])
        fit = fit_power_law(N_arr, T_arr)
        results["power_law_fits"][pairing] = fit

        print(f"\n  {pairing.upper()} pairing:")
        print(f"    η = {fit['eta']:.4f} ± {fit['eta_se']:.4f}")
        print(f"    R² = {fit['R2']:.4f}")
        print(f"    n = {fit['n_points']} uncensored points")

    # ---- 2. η stability (rolling windows) ----
    print(f"\n{'='*70}")
    print("2. η STABILITY (cumulative windows)")
    print(f"{'='*70}")

    results["eta_stability"] = {}
    for pairing in ["global", "local"]:
        stability = rolling_eta(raw_data, pairing)
        results["eta_stability"][pairing] = stability

        print(f"\n  {pairing.upper()} pairing:")
        print(f"  {'N_max':>8} | {'η':>8} | {'± SE':>8} | {'R²':>6} | {'n':>4}")
        print(f"  {'-'*46}")
        for s in stability:
            print(f"  {s['N_max']:>8,} | {s['eta']:>8.4f} | {s['eta_se']:>8.4f} | "
                  f"{s['R2']:>6.4f} | {s['n_points']:>4}")

    # ---- 3. Logarithmic correction test ----
    print(f"\n{'='*70}")
    print("3. LOGARITHMIC CORRECTION TEST")
    print(f"{'='*70}")

    results["log_correction"] = {}
    for pairing in ["global", "local"]:
        points = [(d["N"], d["T_emerge"]) for d in raw_data
                  if d["pairing"] == pairing and not d["censored"]]
        N_arr = np.array([p[0] for p in points])
        T_arr = np.array([p[1] for p in points])
        lc = fit_log_correction(N_arr, T_arr)
        results["log_correction"][pairing] = lc

        print(f"\n  {pairing.upper()} pairing:")
        print(f"    η (with correction) = {lc['eta']:.4f}")
        print(f"    Log correction coeff c = {lc['log_correction_coeff']:.4f}")
        sign = "positive (slowing)" if lc['log_correction_coeff'] > 0 else "negative (accelerating)"
        print(f"    Sign: {sign}")
        print(f"    R² (log model) = {lc['R2']:.4f}")
        print(f"    ΔAIC (log − pure) = {lc['delta_AIC']:.2f}")
        print(f"    Verdict: {lc['interpretation']}")

    # ---- 4. Theory comparison ----
    print(f"\n{'='*70}")
    print("4. THEORY COMPARISON (updated with N=50k data)")
    print(f"{'='*70}")

    theory = {}
    for pairing, predicted, label in [("global", 2/3, "1 − 1/N_c = 2/3"),
                                       ("local", 1/2, "CDP z=2 → 1/2")]:
        fit = results["power_law_fits"][pairing]
        deviation = abs(fit["eta"] - predicted) / predicted * 100
        within_1se = abs(fit["eta"] - predicted) < fit["eta_se"]
        within_2se = abs(fit["eta"] - predicted) < 2 * fit["eta_se"]

        theory[pairing] = {
            "predicted": predicted,
            "predicted_label": label,
            "measured": fit["eta"],
            "measured_se": fit["eta_se"],
            "deviation_pct": float(deviation),
            "within_1_sigma": bool(within_1se),
            "within_2_sigma": bool(within_2se),
        }

        sigma_away = abs(fit["eta"] - predicted) / fit["eta_se"] if fit["eta_se"] > 0 else float('inf')
        print(f"\n  {pairing.upper()}: η = {fit['eta']:.4f} ± {fit['eta_se']:.4f}")
        print(f"    Predicted: {label} = {predicted:.4f}")
        print(f"    Deviation: {deviation:.1f}% ({sigma_away:.1f}σ)")
        print(f"    Within 2σ: {'YES' if within_2se else 'NO'}")

    results["theory_comparison"] = theory

    # ---- 5. N=50k specific ----
    print(f"\n{'='*70}")
    print("5. N=50,050 EMERGENCE STATISTICS")
    print(f"{'='*70}")

    n50k = {}
    for pairing in ["global", "local"]:
        s = next((s for s in summary if s["N"] == 50050 and s["pairing"] == pairing), None)
        if s:
            n50k[pairing] = s
            print(f"\n  {pairing.upper()}: median T = {s['median_T']:,.0f} epochs")
            print(f"    IQR: [{s.get('IQR_low', 0):,.0f}, {s.get('IQR_high', 0):,.0f}]")
            print(f"    Emerged: {s['n_emerged']}/{s['n_total']} (P_nuc = {s['n_emerged']/s['n_total']:.0%})")

    results["n50k_stats"] = n50k

    # Save
    with open(OUTPUT_FILE, "w") as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\nResults saved: {OUTPUT_FILE}")


if __name__ == "__main__":
    main()
