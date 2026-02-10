#!/usr/bin/env python3
"""
Path F: Uniqueness Test (Numerology Control)
=============================================

Tests whether λ = (1/φ³) × sin(72°) is uniquely simple among formulas
matching the Cabibbo angle, or whether many equally simple formulas exist.

Approach:
  1. Generate algebraic expressions involving φ with bounded complexity
  2. Generate trigonometric values sin(kπ/n) and cos(kπ/n) for small n
  3. Form all products (algebraic × trigonometric)
  4. Filter for matches within 1σ of PDG: λ = 0.22497 ± 0.00070
  5. Rank by complexity metric
  6. Statistical analysis and conclusion

Complexity metric:
  - φ^n contributes |n|
  - Integer fraction p/q contributes max(|p|, |q|)
  - sin(kπ/m) or cos(kπ/m) contributes k + m
  - Products sum component complexities

Reference: Derivation-Three-Phi-Factors-Explicit.md §11.2, Path F
"""

import numpy as np
import json
from fractions import Fraction
from collections import defaultdict
from math import gcd

# ================================================================
# Constants
# ================================================================
PHI = (1 + np.sqrt(5)) / 2
LAMBDA_PDG = 0.22497
LAMBDA_ERR = 0.00070
LAMBDA_MIN = LAMBDA_PDG - LAMBDA_ERR
LAMBDA_MAX = LAMBDA_PDG + LAMBDA_ERR
LAMBDA_FORMULA = (1 / PHI**3) * np.sin(2 * np.pi / 5)


def banner(text):
    print("\n" + "=" * 72)
    print(text)
    print("=" * 72)


banner("PATH F: UNIQUENESS TEST (NUMEROLOGY CONTROL)")
print(f"\nTarget:  λ_PDG = {LAMBDA_PDG} ± {LAMBDA_ERR}")
print(f"Window:  [{LAMBDA_MIN:.5f}, {LAMBDA_MAX:.5f}]")
print(f"Formula: (1/φ³)·sin(72°) = {LAMBDA_FORMULA:.6f}")
print(f"Deviation: {abs(LAMBDA_FORMULA - LAMBDA_PDG)/LAMBDA_ERR:.2f}σ")

# ================================================================
# PART 1: Generate algebraic values involving φ
# ================================================================
# Each entry: (numerical_value, label_string, complexity_score)
algebraic = {}


def add_alg(key, val, label, complexity):
    """Add an algebraic value if it's in a reasonable range."""
    if 0.001 < abs(val) < 100 and val > 0:
        algebraic[key] = (val, label, complexity)


# --- Category A: Pure φ-powers: φ^n for n in [-6, 6] ---
for n in range(-6, 7):
    val = PHI ** n
    if n == 0:
        continue  # Skip 1 (handled separately)
    label = f"φ^({n})" if n < 0 else f"φ^{n}"
    if n == 1:
        label = "φ"
    if n == -1:
        label = "1/φ"
    add_alg(f"phi_{n}", val, label, abs(n))

# --- Category B: (p/q)·φ^n for small p, q, n ---
for p in range(1, 7):
    for q in range(1, 7):
        if p == q:
            continue
        f = Fraction(p, q)
        if f.numerator != p or f.denominator != q:
            continue  # skip non-reduced
        for n in range(-5, 6):
            val = float(f) * PHI ** n
            c = max(p, q) + abs(n)
            if n == 0:
                label = f"{p}/{q}"
            elif n == 1:
                label = f"({p}/{q})·φ"
            elif n == -1:
                label = f"({p}/{q})/φ"
            else:
                label = f"({p}/{q})·φ^({n})"
            add_alg(f"frac_{p}_{q}_phi_{n}", val, label, c)

# --- Category C: Simple integer fractions (control group) ---
for p in range(1, 21):
    for q in range(1, 21):
        f = Fraction(p, q)
        if f.numerator != p or f.denominator != q:
            continue
        val = float(f)
        label = f"{p}/{q}" if q > 1 else str(p)
        add_alg(f"rat_{p}_{q}", val, label, max(p, q))

# --- Category D: φ-related algebraic constants ---
special = [
    ("sqrt5m2", np.sqrt(5) - 2, "√5−2", 3),            # = 1/φ³
    ("sqrt5m1_2", (np.sqrt(5) - 1) / 2, "(√5−1)/2", 3),  # = 1/φ
    ("sqrt5p1_2", (np.sqrt(5) + 1) / 2, "(√5+1)/2", 3),  # = φ
    ("sqrt5m1_4", (np.sqrt(5) - 1) / 4, "(√5−1)/4", 4),  # = cos(72°)
    ("sqrt5p1_4", (np.sqrt(5) + 1) / 4, "(√5+1)/4", 4),  # = cos(36°)
    ("2sqrt5m4", 2*np.sqrt(5) - 4, "2√5−4", 4),           # = 2/φ³
]
for key, val, label, c in special:
    add_alg(key, val, label, c)

# --- Category E: Sums/differences of φ powers ---
for n1 in range(-4, 5):
    for n2 in range(n1 + 1, 5):
        for sign in [1, -1]:
            val = PHI ** n1 + sign * PHI ** n2
            if val <= 0:
                continue
            op = "+" if sign > 0 else "−"
            label = f"φ^({n1}){op}φ^({n2})"
            c = abs(n1) + abs(n2) + 2
            add_alg(f"sum_{n1}_{op}_{n2}", val, label, c)

# --- Category F: √n and 1/√n ---
for n in [2, 3, 5, 6, 7, 10]:
    add_alg(f"sqrt{n}", np.sqrt(n), f"√{n}", n)
    add_alg(f"invsqrt{n}", 1 / np.sqrt(n), f"1/√{n}", n + 1)
    # Also φ^k/√n
    for k in range(-3, 4):
        if k == 0:
            continue
        val = PHI ** k / np.sqrt(n)
        label = f"φ^({k})/√{n}"
        add_alg(f"phi{k}_sqrt{n}", val, label, abs(k) + n)

# --- Category G: Products of two φ-powers with small rationals ---
# (a·φ^n + b) for small a, b, n
for a in range(-3, 4):
    for b in range(-3, 4):
        if a == 0 and b == 0:
            continue
        for n in range(-3, 4):
            if a == 0:
                val = float(b)
            elif n == 0:
                val = float(a + b)
            else:
                val = a * PHI ** n + b
            if val <= 0:
                continue
            label = f"{a}·φ^({n})+{b}" if a != 0 else str(b)
            c = abs(a) + abs(b) + abs(n) + 1
            add_alg(f"linphi_{a}_{n}_{b}", val, label, c)

print(f"\nAlgebraic values generated: {len(algebraic)}")

# ================================================================
# PART 2: Generate trigonometric values
# ================================================================
trig = {}


def add_trig(key, val, label, complexity):
    if abs(val) > 0.01:
        trig[key] = (abs(val), label, complexity)


# sin(kπ/n) and cos(kπ/n) for n=1..12
for n in range(1, 13):
    for k in range(1, 2 * n):
        f = Fraction(k, n)
        # Use reduced form for complexity
        kr, nr = f.numerator, f.denominator
        angle_rad = float(f) * np.pi
        angle_deg = float(f) * 180.0

        s = np.sin(angle_rad)
        c = np.cos(angle_rad)

        # Format nice label
        deg = round(angle_deg, 1)
        if abs(deg - round(deg)) < 0.01:
            deg = int(round(deg))

        if abs(s) > 0.01:
            add_trig(f"sin_{kr}_{nr}", s, f"sin({deg}°)", kr + nr)
        if abs(c) > 0.01:
            add_trig(f"cos_{kr}_{nr}", c, f"cos({deg}°)", kr + nr)

# Identity (no trig factor)
trig["id"] = (1.0, "1", 0)

# Deduplicate trig by value (keep lowest complexity)
seen_vals = {}
deduped_trig = {}
for key, (val, label, c) in trig.items():
    rv = round(val, 10)
    if rv not in seen_vals or c < seen_vals[rv][2]:
        if rv in seen_vals:
            old_key = seen_vals[rv][3]
            deduped_trig.pop(old_key, None)
        seen_vals[rv] = (val, label, c, key)
        deduped_trig[key] = (val, label, c)
trig = deduped_trig

print(f"Trigonometric values generated: {len(trig)}")

# ================================================================
# PART 3: Search all products for matches within 1σ
# ================================================================
matches = []
total_products = 0

for akey, (aval, alabel, ac) in algebraic.items():
    for tkey, (tval, tlabel, tc) in trig.items():
        total_products += 1
        product = aval * tval
        if LAMBDA_MIN <= product <= LAMBDA_MAX:
            total_c = ac + tc
            if tkey == "id":
                formula = alabel
            else:
                formula = f"({alabel})·{tlabel}"
            dev = (product - LAMBDA_PDG) / LAMBDA_ERR
            matches.append({
                "formula": formula,
                "value": product,
                "dev_sigma": dev,
                "complexity": total_c,
                "akey": akey,
                "tkey": tkey,
                "aval": aval,
                "tval": tval,
                "ac": ac,
                "tc": tc,
            })

print(f"\nTotal products evaluated: {total_products:,}")
print(f"Raw matches within 1σ: {len(matches)}")

# ================================================================
# PART 4: Deduplicate by numerical value
# ================================================================
groups = defaultdict(list)
for m in matches:
    groups[round(m["value"], 9)].append(m)

unique = []
for val, grp in groups.items():
    grp.sort(key=lambda x: x["complexity"])
    best = grp[0].copy()
    best["alt_count"] = len(grp) - 1
    best["alternatives"] = [g["formula"] for g in grp[1:4]]
    unique.append(best)

unique.sort(key=lambda x: (x["complexity"], abs(x["dev_sigma"])))

print(f"Unique numerical values within 1σ: {len(unique)}")

# ================================================================
# PART 5: Identify our formula
# ================================================================
OUR_VAL = round(LAMBDA_FORMULA, 9)
our_rank = None
our_entry = None
for i, m in enumerate(unique):
    if abs(m["value"] - LAMBDA_FORMULA) < 1e-8:
        our_rank = i + 1
        our_entry = m
        break

if our_entry is None:
    # Try to find it in the raw matches
    for m in matches:
        if abs(m["value"] - LAMBDA_FORMULA) < 1e-8:
            our_entry = m
            break

# ================================================================
# PART 6: Classify matches
# ================================================================
# Separate into categories
phi_trig = []        # Contains φ AND a trig factor
phi_only = []        # Contains φ, no trig
rational_trig = []   # No φ, has trig
pure_rational = []   # No φ, no trig

for m in unique:
    has_phi = ("φ" in m["formula"] or "√5" in m["formula"])
    has_trig = m["tkey"] != "id"
    if has_phi and has_trig:
        phi_trig.append(m)
    elif has_phi:
        phi_only.append(m)
    elif has_trig:
        rational_trig.append(m)
    else:
        pure_rational.append(m)

# ================================================================
# PART 7: Display results
# ================================================================
banner("ALL MATCHES WITHIN 1σ — RANKED BY COMPLEXITY")

print(f"\n{'Rank':<6}{'C':>3}  {'Value':<11}{'σ':>7}  {'Formula':<55} {'Cat':<8}{'Alts'}")
print("─" * 100)

for i, m in enumerate(unique[:60]):
    has_phi = ("φ" in m["formula"] or "√5" in m["formula"])
    has_trig = m["tkey"] != "id"
    if has_phi and has_trig:
        cat = "φ×trig"
    elif has_phi:
        cat = "φ-only"
    elif has_trig:
        cat = "rat×tr"
    else:
        cat = "rational"

    marker = ""
    if abs(m["value"] - LAMBDA_FORMULA) < 1e-8:
        marker = " ◄◄◄ OUR FORMULA"

    print(f"{i+1:<6}{m['complexity']:>3}  {m['value']:<11.7f}{m['dev_sigma']:>+6.2f}σ  "
          f"{m['formula']:<55} {cat:<8}{m['alt_count']}{marker}")

# ================================================================
banner("CATEGORY BREAKDOWN")
print(f"\n  φ × trig formulas:       {len(phi_trig):>4}")
print(f"  φ-only (no trig):        {len(phi_only):>4}")
print(f"  Rational × trig:         {len(rational_trig):>4}")
print(f"  Pure rational:           {len(pure_rational):>4}")
print(f"  ─────────────────────────────")
print(f"  Total unique matches:    {len(unique):>4}")

# ================================================================
banner("φ × TRIG MATCHES (DIRECT COMPETITORS)")

print(f"\n{'Rank':<6}{'C':>3}  {'Value':<11}{'σ':>7}  {'Formula'}")
print("─" * 80)
for i, m in enumerate(phi_trig[:30]):
    marker = " ◄◄◄" if abs(m["value"] - LAMBDA_FORMULA) < 1e-8 else ""
    print(f"{i+1:<6}{m['complexity']:>3}  {m['value']:<11.7f}{m['dev_sigma']:>+6.2f}σ  "
          f"{m['formula']}{marker}")

# ================================================================
banner("PURE RATIONAL MATCHES (CONTROL GROUP)")

print(f"\n{'Rank':<6}{'C':>3}  {'Value':<11}{'σ':>7}  {'Formula'}")
print("─" * 80)
for i, m in enumerate(pure_rational[:15]):
    print(f"{i+1:<6}{m['complexity']:>3}  {m['value']:<11.7f}{m['dev_sigma']:>+6.2f}σ  "
          f"{m['formula']}")

# ================================================================
banner("φ-ONLY MATCHES (NO TRIG)")

print(f"\n{'Rank':<6}{'C':>3}  {'Value':<11}{'σ':>7}  {'Formula'}")
print("─" * 80)
for i, m in enumerate(phi_only[:15]):
    print(f"{i+1:<6}{m['complexity']:>3}  {m['value']:<11.7f}{m['dev_sigma']:>+6.2f}σ  "
          f"{m['formula']}")

# ================================================================
banner("COMPLEXITY DISTRIBUTION")

brackets = [(0, 4), (4, 7), (7, 10), (10, 13), (13, 16), (16, 20), (20, 30)]
print(f"\n{'Bracket':<15}{'All':>6}{'φ×trig':>8}{'φ-only':>8}{'rat×tr':>8}{'pure':>8}")
print("─" * 55)
for lo, hi in brackets:
    n_all = sum(1 for m in unique if lo <= m["complexity"] < hi)
    n_pt = sum(1 for m in phi_trig if lo <= m["complexity"] < hi)
    n_po = sum(1 for m in phi_only if lo <= m["complexity"] < hi)
    n_rt = sum(1 for m in rational_trig if lo <= m["complexity"] < hi)
    n_pr = sum(1 for m in pure_rational if lo <= m["complexity"] < hi)
    print(f"  [{lo:>2},{hi:>2})      {n_all:>6}{n_pt:>8}{n_po:>8}{n_rt:>8}{n_pr:>8}")

# ================================================================
banner("STATISTICAL ANALYSIS")

# Our formula's rank within its category
phi_trig_rank = None
for i, m in enumerate(phi_trig):
    if abs(m["value"] - LAMBDA_FORMULA) < 1e-8:
        phi_trig_rank = i + 1
        break

if our_entry:
    simpler_all = sum(1 for m in unique if m["complexity"] < our_entry["complexity"])
    equal_all = sum(1 for m in unique if m["complexity"] == our_entry["complexity"])
    simpler_pt = sum(1 for m in phi_trig if m["complexity"] < our_entry["complexity"])
    equal_pt = sum(1 for m in phi_trig if m["complexity"] == our_entry["complexity"])
else:
    simpler_all = equal_all = simpler_pt = equal_pt = -1

print(f"\nOur formula: (1/φ³)·sin(72°)")
print(f"  Value:       {LAMBDA_FORMULA:.7f}")
print(f"  Deviation:   {(LAMBDA_FORMULA - LAMBDA_PDG)/LAMBDA_ERR:+.2f}σ")
if our_entry:
    print(f"  Complexity:  {our_entry['complexity']}")
    print(f"  Overall rank:        #{our_rank} of {len(unique)}")
    print(f"  φ×trig category rank: #{phi_trig_rank} of {len(phi_trig)}")
    print(f"\n  Formulas simpler (all categories): {simpler_all}")
    print(f"  Formulas equal complexity (all):    {equal_all}")
    print(f"  Formulas simpler (φ×trig only):     {simpler_pt}")
    print(f"  Formulas equal complexity (φ×trig):  {equal_pt}")

# Density analysis: what fraction of the search space matches?
hit_rate = len(unique) / total_products
window_fraction = (LAMBDA_MAX - LAMBDA_MIN) / 1.0  # relative to [0,1]
enrichment = hit_rate / window_fraction if window_fraction > 0 else 0

print(f"\nSearch space statistics:")
print(f"  Total products searched: {total_products:,}")
print(f"  Unique matches:          {len(unique)}")
print(f"  Hit rate:                {hit_rate:.6%}")
print(f"  Window fraction [0,1]:   {window_fraction:.4%}")
print(f"  Enrichment factor:       {enrichment:.1f}×")

# How special is the φ×trig class?
total_phi_trig_combos = sum(
    1 for akey in algebraic
    if "φ" in algebraic[akey][1] or "√5" in algebraic[akey][1]
) * sum(1 for tkey in trig if tkey != "id")
phi_trig_hit_rate = len(phi_trig) / total_phi_trig_combos if total_phi_trig_combos > 0 else 0

print(f"\n  φ×trig combinations:     {total_phi_trig_combos:,}")
print(f"  φ×trig matches:          {len(phi_trig)}")
print(f"  φ×trig hit rate:         {phi_trig_hit_rate:.6%}")

# ================================================================
# PART 8: Quality assessment
# ================================================================
banner("QUALITY ASSESSMENT: Is (1/φ³)·sin(72°) special?")

# Criteria for "special":
# 1. Among the simplest in its category
# 2. Both components have independent geometric meaning
# 3. Low deviation from PDG
# 4. Not many equally simple competitors

# Check: is it the simplest φ×trig formula?
if phi_trig:
    min_c_pt = phi_trig[0]["complexity"]
    at_min = [m for m in phi_trig if m["complexity"] == min_c_pt]
    print(f"\nSimplest φ×trig complexity: {min_c_pt}")
    print(f"  Formulas at this complexity: {len(at_min)}")
    for m in at_min[:5]:
        marker = " ◄◄◄" if abs(m["value"] - LAMBDA_FORMULA) < 1e-8 else ""
        print(f"    {m['formula']} = {m['value']:.7f} ({m['dev_sigma']:+.2f}σ){marker}")

# Check: closest match among low-complexity φ×trig
low_c_pt = [m for m in phi_trig if m["complexity"] <= 12]
if low_c_pt:
    low_c_pt.sort(key=lambda x: abs(x["dev_sigma"]))
    print(f"\nBest-matching φ×trig with complexity ≤ 12:")
    for m in low_c_pt[:5]:
        marker = " ◄◄◄" if abs(m["value"] - LAMBDA_FORMULA) < 1e-8 else ""
        print(f"    C={m['complexity']:>2}  {m['formula']} = {m['value']:.7f} "
              f"({m['dev_sigma']:+.2f}σ){marker}")

# Deeper check: what about 2σ and 3σ?
matches_2sigma = []
matches_3sigma = []
for akey, (aval, alabel, ac) in algebraic.items():
    for tkey, (tval, tlabel, tc) in trig.items():
        product = aval * tval
        dev = abs(product - LAMBDA_PDG) / LAMBDA_ERR
        has_phi = ("φ" in alabel or "√5" in alabel)
        has_trig = tkey != "id"
        if has_phi and has_trig:
            if dev <= 2.0:
                matches_2sigma.append((product, ac + tc, alabel, tlabel, dev))
            if dev <= 3.0:
                matches_3sigma.append((product, ac + tc, alabel, tlabel, dev))

# Deduplicate
def dedup_by_val(lst):
    seen = set()
    result = []
    for item in lst:
        rv = round(item[0], 9)
        if rv not in seen:
            seen.add(rv)
            result.append(item)
    return result

matches_2sigma = dedup_by_val(matches_2sigma)
matches_3sigma = dedup_by_val(matches_3sigma)

print(f"\nφ×trig matches at different σ thresholds:")
print(f"  Within 1σ: {len(phi_trig)}")
print(f"  Within 2σ: {len(matches_2sigma)}")
print(f"  Within 3σ: {len(matches_3sigma)}")

# ================================================================
# PART 9: Geometric meaning assessment
# ================================================================
banner("GEOMETRIC MEANING FILTER")

print("""
Not all φ×trig formulas are equally meaningful. Our formula has both
components traceable to 600-cell geometry:
  - 1/φ³: arises in icosahedral (H₄) symmetry structures
  - sin(72°) = sin(2π/5): the pentagonal angle from 5-fold symmetry

Filters for "geometrically motivated" formulas:
  1. The φ-part should be a simple power φ^n (not an arbitrary fraction)
  2. The angle should relate to a regular polygon (360°/n or supplement)
""")

geo_motivated = []
for m in phi_trig:
    akey = m["akey"]
    tkey = m["tkey"]
    # Check if algebraic part is a pure φ-power
    is_pure_phi_power = akey.startswith("phi_")
    # Also accept √5−2 = 1/φ³
    is_special_phi = akey in ["sqrt5m2"]
    # Check if trig part is a "nice" polygon angle
    # Nice angles: multiples of 30°, 36°, 45°, 60°, 72°, etc.
    is_nice_angle = False
    if "_" in tkey:
        parts = tkey.split("_")
        if len(parts) == 3:
            try:
                k, n = int(parts[1]), int(parts[2])
                # "Nice" if the denominator n ≤ 6 (polygon with ≤ 12 sides)
                is_nice_angle = (n <= 6)
            except ValueError:
                pass

    if (is_pure_phi_power or is_special_phi) and is_nice_angle:
        geo_motivated.append(m)

print(f"Geometrically motivated φ×trig matches: {len(geo_motivated)}")
print(f"\n{'Rank':<6}{'C':>3}  {'Value':<11}{'σ':>7}  {'Formula'}")
print("─" * 70)
for i, m in enumerate(geo_motivated[:20]):
    marker = " ◄◄◄" if abs(m["value"] - LAMBDA_FORMULA) < 1e-8 else ""
    print(f"{i+1:<6}{m['complexity']:>3}  {m['value']:<11.7f}{m['dev_sigma']:>+6.2f}σ  "
          f"{m['formula']}{marker}")

# Among geometrically motivated, what's the rank?
geo_rank = None
for i, m in enumerate(geo_motivated):
    if abs(m["value"] - LAMBDA_FORMULA) < 1e-8:
        geo_rank = i + 1
        break

if geo_rank is not None:
    print(f"\nOur formula rank (geo-motivated): #{geo_rank} of {len(geo_motivated)}")

# ================================================================
# PART 10: Conclusion
# ================================================================
banner("CONCLUSION")

# Determine verdict
if our_entry:
    c_ours = our_entry["complexity"]
else:
    c_ours = 8  # 3 + 5 = |−3| + (2+5)... estimate

# Count genuine competitors
genuine_competitors = [m for m in phi_trig
                       if m["complexity"] <= c_ours
                       and abs(m["value"] - LAMBDA_FORMULA) > 1e-8]

print(f"\nFormula: λ = (1/φ³) × sin(72°) = {LAMBDA_FORMULA:.6f}")
print(f"PDG:     λ = {LAMBDA_PDG} ± {LAMBDA_ERR}")
print(f"Deviation: {abs(LAMBDA_FORMULA - LAMBDA_PDG)/LAMBDA_ERR:.2f}σ")
print(f"\nIn the φ×trig category:")
print(f"  Total matches within 1σ:  {len(phi_trig)}")
print(f"  Matches at ≤ our complexity ({c_ours}): {len(genuine_competitors) + 1}")
print(f"  Genuine competitors:       {len(genuine_competitors)}")

if phi_trig_rank is not None and phi_trig_rank <= 3 and len(genuine_competitors) <= 5:
    verdict = "STRONG_UNIQUENESS"
    verdict_text = (
        f"STRONG UNIQUENESS: (1/φ³)·sin(72°) ranks #{phi_trig_rank} among "
        f"{len(phi_trig)} φ×trig matches. Only {len(genuine_competitors)} "
        f"competitors at equal or lower complexity. The formula is NOT a "
        f"generic numerological coincidence — it is distinguished by its "
        f"simplicity within the φ×trig class."
    )
elif phi_trig_rank is not None and len(genuine_competitors) <= 15:
    verdict = "MODERATE_UNIQUENESS"
    verdict_text = (
        f"MODERATE UNIQUENESS: (1/φ³)·sin(72°) ranks #{phi_trig_rank} among "
        f"{len(phi_trig)} φ×trig matches. {len(genuine_competitors)} competitors "
        f"at equal or lower complexity. The formula is relatively distinguished "
        f"but not uniquely so."
    )
else:
    verdict = "WEAK_UNIQUENESS"
    verdict_text = (
        f"WEAK UNIQUENESS: (1/φ³)·sin(72°) ranks #{phi_trig_rank} among "
        f"{len(phi_trig)} φ×trig matches with {len(genuine_competitors)} "
        f"competitors. Many equally simple formulas exist."
    )

# Additional nuance: geometric motivation
if geo_motivated:
    geo_competitors = len([m for m in geo_motivated
                          if abs(m["value"] - LAMBDA_FORMULA) > 1e-8
                          and m["complexity"] <= c_ours])
    verdict_text += (
        f"\n\n  Geometric motivation filter: Among {len(geo_motivated)} "
        f"geometrically motivated formulas,\n  {geo_competitors} are at "
        f"≤ our complexity (rank #{geo_rank})."
    )

# Control group comparison
verdict_text += (
    f"\n\n  Control group: {len(pure_rational)} pure rational fractions "
    f"also match within 1σ.\n  This provides the numerological baseline — "
    f"any target in [0,1] will have\n  ~{len(pure_rational)} simple rational "
    f"matches, so the φ×trig matches must be\n  assessed relative to this "
    f"background."
)

print(f"\n{verdict_text}")

# ================================================================
# PART 11: Save results
# ================================================================
results = {
    "test": "Path F — Uniqueness Test (Numerology Control)",
    "date": "2026-02-07",
    "script": "verification/Phase3/path_f_uniqueness_test.py",
    "target": {
        "lambda_PDG": LAMBDA_PDG,
        "sigma": LAMBDA_ERR,
        "window": [LAMBDA_MIN, LAMBDA_MAX],
    },
    "our_formula": {
        "expression": "(1/φ³) × sin(72°)",
        "value": float(LAMBDA_FORMULA),
        "deviation_sigma": float((LAMBDA_FORMULA - LAMBDA_PDG) / LAMBDA_ERR),
        "complexity": c_ours,
        "overall_rank": our_rank,
        "phi_trig_rank": phi_trig_rank,
        "geo_motivated_rank": geo_rank,
    },
    "search_space": {
        "algebraic_values": len(algebraic),
        "trigonometric_values": len(trig),
        "total_products": total_products,
    },
    "results_1sigma": {
        "total_unique_matches": len(unique),
        "phi_trig_matches": len(phi_trig),
        "phi_only_matches": len(phi_only),
        "rational_trig_matches": len(rational_trig),
        "pure_rational_matches": len(pure_rational),
        "geo_motivated_matches": len(geo_motivated),
    },
    "sigma_scan": {
        "phi_trig_1sigma": len(phi_trig),
        "phi_trig_2sigma": len(matches_2sigma),
        "phi_trig_3sigma": len(matches_3sigma),
    },
    "competitors": {
        "at_leq_our_complexity": len(genuine_competitors),
        "geo_motivated_at_leq_ours": geo_competitors if geo_motivated else 0,
    },
    "conclusion": {
        "verdict": verdict,
        "text": verdict_text,
    },
    "top_matches_all": [
        {
            "rank": i + 1,
            "formula": m["formula"],
            "value": float(m["value"]),
            "deviation_sigma": float(m["dev_sigma"]),
            "complexity": m["complexity"],
            "alt_count": m.get("alt_count", 0),
        }
        for i, m in enumerate(unique[:30])
    ],
    "top_phi_trig": [
        {
            "rank": i + 1,
            "formula": m["formula"],
            "value": float(m["value"]),
            "deviation_sigma": float(m["dev_sigma"]),
            "complexity": m["complexity"],
        }
        for i, m in enumerate(phi_trig[:20])
    ],
    "geo_motivated_matches": [
        {
            "rank": i + 1,
            "formula": m["formula"],
            "value": float(m["value"]),
            "deviation_sigma": float(m["dev_sigma"]),
            "complexity": m["complexity"],
        }
        for i, m in enumerate(geo_motivated[:20])
    ],
}

output_path = "/Users/robertmassman/Dropbox/Coding_Projects/eqalateralCube/verification/Phase3/path_f_uniqueness_test_results.json"
with open(output_path, "w") as f:
    json.dump(results, f, indent=2)
print(f"\nResults saved to path_f_uniqueness_test_results.json")
print("\nDone.")
