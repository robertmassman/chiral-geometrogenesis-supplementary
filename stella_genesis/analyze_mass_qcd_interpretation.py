#!/usr/bin/env python3
"""
QCD phenomenology interpretation of vertex-concentrated mass (Q4 open question 3).

Maps the genesis_soup mass distribution to constituent quark model predictions:
- Vertices anchor color fields → mass concentrates near vertices (Q2 result)
- Each tetrahedron has 4 vertices, 3 of which are color-assigned (Def 0.1.3)
- Constituent quarks in QCD carry ~1/3 of hadron mass each

This script loads mass_geography.json and analyzes:
1. Mass concentration ratio: vertex zone / face center zone
2. Per-vertex mass budgets (3 color vertices + 1 central)
3. Effective "baryon mass" = sum of 3 color-vertex masses per tetrahedron
4. Ratio of vertex-localized mass / total mass vs constituent quark fraction
5. Spatial decay profile: mass vs distance from nearest vertex

References:
- Q2 result: Pearson r=+0.63 (mass vs P_ratio), r=-0.60 (mass vs dist_vertex)
- PDG: constituent quark mass m_u ≈ 336 MeV, m_d ≈ 340 MeV
- Proton mass: 938.3 MeV → constituent quarks carry ~3×338/938 ≈ 1.08 (overcounting)
- More precisely: constituent quarks ≈ 60-70% of hadron mass (rest = gluons/binding)
"""

import json
import os
import sys
import numpy as np

BASE = os.path.dirname(os.path.abspath(__file__))
GEO_FILE = os.path.join(BASE, 'mass_geography.json')

# PDG reference values
M_CONSTITUENT_U = 0.336  # GeV (constituent up quark mass)
M_CONSTITUENT_D = 0.340  # GeV (constituent down quark mass)
M_PROTON = 0.9383        # GeV
CONSTITUENT_FRACTION = 3 * 0.338 / M_PROTON  # ~1.08 (naive), effective ~0.6-0.7


def load_geography(path=GEO_FILE):
    """Load mass geography JSON."""
    if not os.path.exists(path):
        print(f"ERROR: {path} not found.")
        print("Run genesis_soup with mass_mode=1 first to generate this file.")
        sys.exit(1)
    with open(path) as f:
        return json.load(f)


def vertex_zone_analysis(data, surface='tp'):
    """Analyze mass distribution by proximity to vertices."""
    mass = np.array(data[f'mass_{surface}'])
    dist = np.array(data[f'dist_vertex_{surface}'])
    p_ratio = np.array(data[f'p_ratio_{surface}'])
    n = len(mass)

    print(f"\n=== {surface.upper()} Surface: Vertex-Zone Mass Analysis ===\n")

    # Define zones by distance thresholds
    # Vertex zone: dist < 0.6 (near vertices, P_ratio > 0.7 typically)
    # Mid zone: 0.6 <= dist < 1.2
    # Face zone: dist >= 1.2 (face centers, P_ratio < 0.5)
    zones = [
        ('Vertex (d<0.6)', dist < 0.6),
        ('Mid (0.6≤d<1.2)', (dist >= 0.6) & (dist < 1.2)),
        ('Face (d≥1.2)', dist >= 1.2),
    ]

    total_mass = mass.sum()
    print(f"{'Zone':25s}  {'N sites':>8s}  {'Mean mass':>10s}  {'Total mass':>11s}  {'% of total':>10s}")
    print("-" * 70)
    for name, mask in zones:
        if mask.sum() == 0:
            continue
        zm = mass[mask]
        print(f"{name:25s}  {mask.sum():8d}  {zm.mean():10.4f}  {zm.sum():11.2f}  {100*zm.sum()/total_mass:9.1f}%")

    # Concentration ratio: vertex mass density / face mass density
    vx_mask = dist < 0.6
    face_mask = dist >= 1.2
    if vx_mask.sum() > 0 and face_mask.sum() > 0:
        vx_density = mass[vx_mask].mean()
        face_density = mass[face_mask].mean()
        ratio = vx_density / face_density if face_density > 0 else float('inf')
        print(f"\nConcentration ratio (vertex/face density): {ratio:.2f}×")

    return mass, dist, p_ratio


def per_vertex_mass(data, surface='tp'):
    """Compute mass budget per individual vertex."""
    mass = np.array(data[f'mass_{surface}'])
    pos = np.array(data[f'{surface}_pos'])
    vertices = np.array(data['tv_plus'] if surface == 'tp' else data['tv_minus'])

    print(f"\n=== {surface.upper()} Surface: Per-Vertex Mass Budget ===\n")

    # Assign each site to its nearest vertex
    n_sites = len(mass)
    n_verts = len(vertices)
    assignments = np.zeros(n_sites, dtype=int)
    for i in range(n_sites):
        dists = np.linalg.norm(pos[i] - vertices, axis=1)
        assignments[i] = np.argmin(dists)

    total_mass = mass.sum()
    print(f"{'Vertex':>8s}  {'Coords':>20s}  {'N sites':>8s}  {'Sum mass':>10s}  {'Mean mass':>10s}  {'% total':>8s}")
    print("-" * 75)

    vertex_masses = []
    for v in range(n_verts):
        mask = assignments == v
        vm = mass[mask]
        vertex_masses.append(vm.sum())
        coord_str = f"({vertices[v][0]:+.0f},{vertices[v][1]:+.0f},{vertices[v][2]:+.0f})"
        print(f"{'V'+str(v):>8s}  {coord_str:>20s}  {mask.sum():8d}  {vm.sum():10.2f}  {vm.mean():10.4f}  {100*vm.sum()/total_mass:7.1f}%")

    vertex_masses = np.array(vertex_masses)
    print(f"\nVertex mass uniformity: CV = {vertex_masses.std()/vertex_masses.mean():.4f}")

    # "Baryon mass" = sum of 3 color-vertex masses (vertices 1,2,3 are color vertices)
    # Vertex 0 is the "origin" vertex of the tetrahedron
    color_vertex_mass = vertex_masses[1:].sum()
    print(f"\nColor-vertex mass (V1+V2+V3): {color_vertex_mass:.2f}")
    print(f"Total mass: {total_mass:.2f}")
    print(f"Color-vertex fraction: {color_vertex_mass/total_mass:.3f}")
    print(f"  (cf. QCD constituent quark fraction: ~0.60-0.70 of hadron mass)")

    return vertex_masses


def mass_decay_profile(data, surface='tp'):
    """Radial mass decay profile from nearest vertex."""
    mass = np.array(data[f'mass_{surface}'])
    dist = np.array(data[f'dist_vertex_{surface}'])

    print(f"\n=== {surface.upper()} Surface: Mass Decay Profile ===\n")

    # Bin by distance
    bins = np.linspace(0, dist.max() * 1.01, 11)
    print(f"{'Distance':>12s}  {'N':>5s}  {'Mean mass':>10s}  {'Std':>8s}")
    print("-" * 40)

    bin_means = []
    bin_centers = []
    for i in range(len(bins) - 1):
        mask = (dist >= bins[i]) & (dist < bins[i+1])
        if mask.sum() == 0:
            continue
        bm = mass[mask]
        center = (bins[i] + bins[i+1]) / 2
        bin_means.append(bm.mean())
        bin_centers.append(center)
        print(f"[{bins[i]:.2f},{bins[i+1]:.2f})  {mask.sum():5d}  {bm.mean():10.4f}  {bm.std():8.4f}")

    # Fit power law: mass ~ d^(-alpha)
    if len(bin_centers) > 3:
        bc = np.array(bin_centers)
        bm = np.array(bin_means)
        # Avoid log(0): only fit where both are positive
        valid = (bc > 0) & (bm > 0)
        if valid.sum() > 2:
            log_d = np.log(bc[valid])
            log_m = np.log(bm[valid])
            coeffs = np.polyfit(log_d, log_m, 1)
            alpha = -coeffs[0]  # mass ~ d^(-alpha)
            print(f"\nPower-law fit: mass ~ d^(-{alpha:.2f})  (R² from log-log)")
            # Compute R²
            pred = coeffs[0] * log_d + coeffs[1]
            ss_res = np.sum((log_m - pred)**2)
            ss_tot = np.sum((log_m - log_m.mean())**2)
            r2 = 1 - ss_res / ss_tot if ss_tot > 0 else 0
            print(f"  R² = {r2:.3f}")
            print(f"  (Coulomb-like 1/r² would give α=2; "
                  f"confinement-like linear would give different profile)")


def color_symmetry_check(data):
    """Check if mass respects the Z₃ color symmetry."""
    print("\n=== Color Symmetry of Mass Distribution ===\n")

    for surface in ['tp', 'tm']:
        mass = np.array(data[f'mass_{surface}'])
        pos = np.array(data[f'{surface}_pos'])
        vertices = np.array(data['tv_plus'] if surface == 'tp' else data['tv_minus'])

        # Group sites by nearest vertex, compute mass per vertex
        n_sites = len(mass)
        vertex_sums = np.zeros(4)
        vertex_counts = np.zeros(4)
        for i in range(n_sites):
            dists = np.linalg.norm(pos[i] - vertices, axis=1)
            v = np.argmin(dists)
            vertex_sums[v] += mass[i]
            vertex_counts[v] += 1

        # Vertices 1,2,3 are the three color vertices
        color_masses = vertex_sums[1:4]
        if color_masses.mean() > 0:
            cv = color_masses.std() / color_masses.mean()
            max_dev = np.max(np.abs(color_masses - color_masses.mean())) / color_masses.mean()
            print(f"  {surface.upper()}: Color vertex masses = [{', '.join(f'{m:.2f}' for m in color_masses)}]")
            print(f"       CV = {cv:.4f}, max deviation = {max_dev:.4f}")
            if cv < 0.05:
                print(f"       → Z₃ symmetry: GOOD (CV < 5%)")
            elif cv < 0.15:
                print(f"       → Z₃ symmetry: APPROXIMATE (CV < 15%)")
            else:
                print(f"       → Z₃ symmetry: BROKEN (CV ≥ 15%)")


def summary(data):
    """Print overall QCD phenomenology summary."""
    mass_tp = np.array(data['mass_tp'])
    mass_tm = np.array(data['mass_tm'])
    dist_tp = np.array(data['dist_vertex_tp'])
    dist_tm = np.array(data['dist_vertex_tm'])

    total_mass = mass_tp.sum() + mass_tm.sum()
    vertex_mass = mass_tp[dist_tp < 0.6].sum() + mass_tm[dist_tm < 0.6].sum()
    face_mass = mass_tp[dist_tp >= 1.2].sum() + mass_tm[dist_tm >= 1.2].sum()

    print("\n" + "=" * 70)
    print("QCD PHENOMENOLOGY SUMMARY")
    print("=" * 70)
    print(f"\nTotal mass (both surfaces): {total_mass:.2f} (lattice units)")
    print(f"Vertex-zone mass: {vertex_mass:.2f} ({100*vertex_mass/total_mass:.1f}%)")
    print(f"Face-zone mass: {face_mass:.2f} ({100*face_mass/total_mass:.1f}%)")
    print(f"Concentration ratio: {vertex_mass/face_mass:.1f}× (vertex/face)")
    print()
    print("Physical interpretation:")
    print("  - Mass concentrates near tetrahedron vertices (color sources)")
    print("  - Each tetrahedron has 3 color vertices → analog of 3 constituent quarks")
    print("  - The vertex-localized mass pattern parallels the constituent quark model")
    print("    where quarks carry ~60-70% of hadron mass")
    print("  - Face centers (equidistant from all vertices) have minimal mass")
    print("    → analog of the 'empty' interior of a hadron in the bag model")
    print()
    vfrac = vertex_mass / total_mass
    print(f"  Vertex-mass fraction: {vfrac:.2f}")
    print(f"  QCD reference (constituent quark fraction): ~0.60-0.70")
    if 0.4 < vfrac < 0.85:
        print(f"  → CONSISTENT with constituent quark picture")
    elif vfrac >= 0.85:
        print(f"  → STRONGER concentration than constituent quarks (confinement-dominated)")
    else:
        print(f"  → WEAKER concentration than constituent quarks")


def main():
    print("=" * 70)
    print("QCD Phenomenology Interpretation of Mass Geography")
    print("(Q4 Open Question 3: vertex-concentrated mass → constituent quarks)")
    print("=" * 70)

    data = load_geography()
    print(f"\nLoaded: {data['n_sites']} sites/surface, epoch {data['epoch']}")

    for surface in ['tp', 'tm']:
        vertex_zone_analysis(data, surface)
        per_vertex_mass(data, surface)
        mass_decay_profile(data, surface)

    color_symmetry_check(data)
    summary(data)


if __name__ == '__main__':
    main()
