#!/usr/bin/env python3
"""
K3: Lyapunov divergence front speed — zone-aware analysis.

Measures whether the chaotic trit-Hamming divergence front has a finite
propagation speed (emergent causality) by tracking per-shell arrival
times split by open (VM dynamics) and blocked (Kuramoto) pressure zones.

Key metric: front speed v(n_sub) as n_sub → ∞. If v converges to a
finite value, the soup has an emergent light cone.
"""
import subprocess, json, math, sys, os

BIN = "./genesis_soup_metal"

def run_k3(n_sub, epochs, burn_in, diag_interval, perturb_delta, seed=42):
    """Run K3 experiment and return parsed JSONL records."""
    args = [
        BIN,
        "-n", str(n_sub),
        "-e", str(epochs),
        "-b", str(burn_in),
        "-d", str(diag_interval),
        "-p", str(burn_in),  # perturb at burn_in epoch
        "-D", str(perturb_delta),
        "-S", str(seed),
    ]
    # Remove stale JSONL before running
    jsonl_file = "phase_K3_gpu_diag.jsonl"
    if os.path.exists(jsonl_file):
        os.remove(jsonl_file)

    r = subprocess.run(args, capture_output=True, text=True, timeout=600)

    # Parse JSONL from the output file (written fresh by this run)
    records = []
    if os.path.exists(jsonl_file):
        with open(jsonl_file) as f:
            for line in f:
                line = line.strip()
                if line:
                    try:
                        records.append(json.loads(line))
                    except:
                        pass
    return records, r.stderr

def extract_arrivals(records):
    """Extract arrival data from the final 'arrivals' record."""
    for rec in records:
        if rec.get("type") == "arrivals":
            return rec.get("data", [])
    return []

def extract_timeseries(records):
    """Extract per-shell hamming timeseries from epoch records."""
    series = []
    for rec in records:
        if "rel_epoch" in rec and "shells" in rec:
            series.append(rec)
    return series

def compute_front_speed(arrivals, key="t_trit_open", max_d_frac=0.5):
    """Fit front speed from arrival data.

    Only uses shells in the inner max_d_frac of max BFS distance to
    avoid boundary effects. Uses log-log regression d = C * t^alpha.
    Also computes linear velocity v from d = v*t.
    """
    pts = []
    for entry in arrivals:
        d = entry["d"]
        t = entry.get(key, -1)
        if d > 0 and t > 0:
            pts.append((d, t))

    if len(pts) < 3:
        return {"alpha": None, "v": None, "n_pts": len(pts)}

    # Filter to inner fraction
    max_d = max(d for d, t in pts)
    cutoff = int(max_d * max_d_frac)
    pts = [(d, t) for d, t in pts if d <= cutoff]

    if len(pts) < 3:
        return {"alpha": None, "v": None, "n_pts": len(pts)}

    # Power-law fit: ln(d) = alpha * ln(t) + ln(C)
    n = len(pts)
    sx = sum(math.log(t) for d, t in pts)
    sy = sum(math.log(d) for d, t in pts)
    sxx = sum(math.log(t)**2 for d, t in pts)
    sxy = sum(math.log(t)*math.log(d) for d, t in pts)
    denom = n * sxx - sx * sx
    if abs(denom) < 1e-12:
        alpha = None
    else:
        alpha = (n * sxy - sx * sy) / denom

    # Linear velocity: d = v*t (fit through origin-ish)
    sx2 = sum(t for d, t in pts)
    sy2 = sum(d for d, t in pts)
    sxx2 = sum(t*t for d, t in pts)
    sxy2 = sum(t*d for d, t in pts)
    den2 = n * sxx2 - sx2 * sx2
    v = (n * sxy2 - sx2 * sy2) / den2 if abs(den2) > 1e-12 else None

    return {"alpha": alpha, "v": v, "n_pts": n}

def compute_early_front_speed(series, zone="open", threshold=0.001, max_shells=15,
                               metric="phase"):
    """Compute front speed from the early-time timeseries.

    Track how quickly the phase-deviation front advances through
    the FIRST max_shells shells. Uses phase deviation (continuous)
    rather than trit Hamming (quantized) for higher sensitivity.
    """
    if metric == "phase":
        key = "po" if zone == "open" else "pb"
    else:
        key = "ho" if zone == "open" else "hb"

    arrivals = {}  # d -> first rel_epoch where metric > threshold
    for rec in series:
        ep = rec["rel_epoch"]
        for s in rec["shells"]:
            d = s["d"]
            if d <= 0 or d > max_shells:
                continue
            n_zone = s.get("no" if zone == "open" else "nb", 0)
            if n_zone == 0:
                continue
            h = s[key]
            if h > threshold and d not in arrivals:
                arrivals[d] = ep

    pts = sorted(arrivals.items())  # (d, t) sorted by d
    if len(pts) < 3:
        return None, None, pts

    # Linear fit: d = v*t + b
    n = len(pts)
    sx = sum(t for d, t in pts)
    sy = sum(d for d, t in pts)
    sxx = sum(t*t for d, t in pts)
    sxy = sum(t*d for d, t in pts)
    den = n*sxx - sx*sx
    if abs(den) < 1e-12:
        return None, None, pts
    v = (n*sxy - sx*sy) / den

    # Power-law fit
    valid = [(d, t) for d, t in pts if d > 0 and t > 0]
    if len(valid) < 3:
        return v, None, pts
    n2 = len(valid)
    sx2 = sum(math.log(t) for d, t in valid)
    sy2 = sum(math.log(d) for d, t in valid)
    sxx2 = sum(math.log(t)**2 for d, t in valid)
    sxy2 = sum(math.log(t)*math.log(d) for d, t in valid)
    den2 = n2*sxx2 - sx2*sx2
    alpha = (n2*sxy2 - sx2*sy2) / den2 if abs(den2) > 1e-12 else None

    return v, alpha, pts


# ============================================================
# MAIN EXPERIMENT
# ============================================================

print("=" * 80)
print("K3: LYAPUNOV DIVERGENCE FRONT SPEED")
print("=" * 80)
print()

# Parameters — start with smaller lattices to understand the signal
nsub_vals = [16, 24, 32, 48]
perturb_delta = 1.047  # π/3
seeds = [42, 137]  # two seeds for initial exploration

print(f"{'n_sub':>5} | {'seed':>4} | {'n_sites':>6} | "
      f"{'α_open':>8} {'v_open':>8} | "
      f"{'α_blk':>8} {'v_blk':>8} | "
      f"{'α_phase':>8} {'v_phase':>8} | "
      f"{'max_d':>5}")
print("-" * 100)

results = []

for nsub in nsub_vals:
    burn_in = max(1000, nsub * 30)  # enough to equilibrate
    analysis = max(2000, nsub * 80)  # enough for front to propagate
    epochs = burn_in + analysis
    diag_int = max(1, nsub // 16)  # fine resolution

    for seed in seeds:
        records, stderr = run_k3(nsub, epochs, burn_in, diag_int, perturb_delta, seed)

        if not records:
            print(f"{nsub:>5} | {seed:>4} | {'ERR':>6} | -- | -- | -- |")
            continue

        # Get header info
        header = next((r for r in records if r.get("type") == "header"), {})
        n_sites = header.get("n_sites", "?")
        max_bfs = header.get("max_bfs_d", "?")

        # Extract timeseries for early-front analysis
        series = extract_timeseries(records)
        max_shells = min(15, max_bfs // 2) if isinstance(max_bfs, int) else 15

        v_open, a_open, pts_open = compute_early_front_speed(
            series, "open", threshold=0.001, max_shells=max_shells, metric="phase")
        v_blk, a_blk, pts_blk = compute_early_front_speed(
            series, "blocked", threshold=0.001, max_shells=max_shells, metric="phase")

        # Phase front from arrivals record
        arrivals = extract_arrivals(records)
        phase_fit = compute_front_speed(arrivals, "t_phase", max_d_frac=0.4)

        def fmt(val, width=8):
            return f"{val:{width}.4f}" if val is not None else f"{'--':>{width}}"

        print(f"{nsub:>5} | {seed:>4} | {n_sites:>6} | "
              f"{fmt(a_open)} {fmt(v_open)} | "
              f"{fmt(a_blk)} {fmt(v_blk)} | "
              f"{fmt(phase_fit['alpha'])} {fmt(phase_fit['v'])} | "
              f"{max_bfs:>5}")

        results.append({
            "n_sub": nsub, "seed": seed, "n_sites": n_sites,
            "max_bfs_d": max_bfs,
            "alpha_open": a_open, "v_open": v_open, "n_pts_open": len(pts_open),
            "alpha_blocked": a_blk, "v_blocked": v_blk, "n_pts_blocked": len(pts_blk),
            "alpha_phase": phase_fit["alpha"], "v_phase": phase_fit["v"],
        })

# ============================================================
# SUMMARY: AVERAGED OVER SEEDS
# ============================================================
print()
print("=" * 80)
print("SEED-AVERAGED RESULTS")
print("=" * 80)
print(f"{'n_sub':>5} | {'α_open':>12} | {'v_open':>12} | "
      f"{'α_blocked':>12} | {'v_blocked':>12}")
print("-" * 70)

for nsub in nsub_vals:
    subset = [r for r in results if r["n_sub"] == nsub]
    if not subset:
        continue

    def avg_field(field):
        vals = [r[field] for r in subset if r[field] is not None]
        if not vals:
            return None, None
        mean = sum(vals) / len(vals)
        if len(vals) > 1:
            std = math.sqrt(sum((v - mean)**2 for v in vals) / (len(vals) - 1))
        else:
            std = 0
        return mean, std

    ao, ao_s = avg_field("alpha_open")
    vo, vo_s = avg_field("v_open")
    ab, ab_s = avg_field("alpha_blocked")
    vb, vb_s = avg_field("v_blocked")

    def fmt_pm(mean, std):
        if mean is None:
            return f"{'--':>12}"
        return f"{mean:6.3f}±{std:5.3f}"

    print(f"{nsub:>5} | {fmt_pm(ao, ao_s):>12} | {fmt_pm(vo, vo_s):>12} | "
          f"{fmt_pm(ab, ab_s):>12} | {fmt_pm(vb, vb_s):>12}")

# ============================================================
# DETAILED TIMESERIES FOR LARGEST n_sub
# ============================================================
# ============================================================
# ZONE TOPOLOGY AND BLOCKED-CORE FRONT SPEED
# ============================================================
print()
print("=" * 80)
print("ZONE TOPOLOGY: open/blocked sites per shell")
print("=" * 80)

for nsub in nsub_vals:
    burn_in = max(1000, nsub * 30)
    analysis = max(2000, nsub * 80)
    records, _ = run_k3(nsub, burn_in + analysis, burn_in, 1, perturb_delta, 42)
    series = extract_timeseries(records)
    header = next((r for r in records if r.get("type") == "header"), {})

    if not series:
        print(f"n_sub={nsub}: no data")
        continue

    # Zone distribution from first epoch
    rec0 = series[0]
    print(f"\nn_sub={nsub} (n_sites={header.get('n_sites','?')}, max_bfs={header.get('max_bfs_d','?')}):")
    blocked_core_max = 0
    gap_start = -1
    for s in rec0["shells"]:
        d = s["d"]
        no, nb = s.get("no", 0), s.get("nb", 0)
        if d <= 25:
            marker = ""
            if nb == 0 and no > 0 and gap_start < 0:
                gap_start = d
                marker = " ← OPEN BARRIER BEGINS"
            elif nb > 0 and gap_start >= 0 and gap_start > 0:
                marker = f" ← blocked resumes (gap d={gap_start}-{d-1})"
                gap_start = -2  # mark as found
            if nb > 0 and gap_start < 0:
                blocked_core_max = d
            print(f"  d={d:3d}: open={no:4d} blocked={nb:4d}{marker}")

    print(f"  Blocked core radius: d=0..{blocked_core_max}")

    # Measure front speed in blocked core only
    print(f"\n  Blocked-core phase front (d=1..{blocked_core_max}):")
    arrivals_core = {}
    for rec in series:
        ep = rec["rel_epoch"]
        for s in rec["shells"]:
            d = s["d"]
            if d <= 0 or d > blocked_core_max:
                continue
            nb = s.get("nb", 0)
            if nb == 0:
                continue
            pb = s.get("pb", 0)
            if pb > 0.001 and d not in arrivals_core:
                arrivals_core[d] = ep

    for d in sorted(arrivals_core.keys()):
        print(f"    d={d:2d}: arrival at epoch {arrivals_core[d]}")

    # Power-law fit on core arrivals
    pts = sorted(arrivals_core.items())
    if len(pts) >= 3:
        n = len(pts)
        sx = sum(math.log(t) for d, t in pts if t > 0)
        sy = sum(math.log(d) for d, t in pts if d > 0 and t > 0)
        sxx = sum(math.log(t)**2 for d, t in pts if t > 0)
        sxy = sum(math.log(t)*math.log(d) for d, t in pts if d > 0 and t > 0)
        valid = [(d, t) for d, t in pts if d > 0 and t > 0]
        nv = len(valid)
        if nv >= 3:
            sx = sum(math.log(t) for d, t in valid)
            sy = sum(math.log(d) for d, t in valid)
            sxx = sum(math.log(t)**2 for d, t in valid)
            sxy = sum(math.log(t)*math.log(d) for d, t in valid)
            den = nv * sxx - sx * sx
            if abs(den) > 1e-12:
                alpha = (nv * sxy - sx * sy) / den
                # Linear velocity
                sx2 = sum(t for d, t in valid)
                sy2 = sum(d for d, t in valid)
                sxx2 = sum(t*t for d, t in valid)
                sxy2 = sum(t*d for d, t in valid)
                den2 = nv*sxx2 - sx2*sx2
                v = (nv*sxy2 - sx2*sy2) / den2 if abs(den2) > 1e-12 else None
                print(f"  Power-law: d ~ t^{alpha:.3f}  (0.5=diffusive, 1.0=ballistic)")
                if v:
                    print(f"  Linear velocity: v = {v:.5f} hops/epoch")
                    # Physical mapping
                    R_stella_fm = 0.44847
                    a_lattice = 2 * math.sqrt(2) * R_stella_fm / (math.sqrt(3) * nsub)
                    hbar_c = 197.3269804  # MeV·fm
                    omega_0 = 220.0  # MeV
                    v_phys = v * a_lattice  # fm/epoch
                    dt_natural = hbar_c / omega_0
                    v_over_c = v_phys / dt_natural
                    print(f"  a_lattice = {a_lattice:.5f} fm, v/c = {v_over_c:.6f}")

print("\nDone.")
