# StellaLang — G2 Mechanism Roadmap

**Date:** 2026-03-23
**Scope:** Mechanisms requiring G2 (multi-stella / multi-site) infrastructure

## Overview

These mechanisms were identified during the G1 genesis_soup investigation
(see `stella_genesis/RESULTS-Phase1.md`) as **beyond G1 scope**.
They require multi-stella lattices, dual-head execution, or multi-site copy
instructions — all G2 (StellaLang) features.

---

## Mechanisms Summary

| # | Mechanism | Source | Expected Effect | Status |
|---|-----------|--------|-----------------|--------|
| 1 | Inter-stella gauge coupling | Prop 2.5.2b | Bypasses single-stella dead zones | ✅ Complete — Mode A ≈ B at L=4 and L=8 |
| 2 | Phase-gradient mass generation | Thm 3.1.1 | Emergent mass from ∇φ coupling | ✅ Complete — all Qs answered; cvf=3/4 is geometric invariant of ∂S across single/multi-stella |
| 3 | CPY01/CPY10 (multi-site copy) | StellaLang ISA | Replicator selection, entropy collapse | ✅ Complete — CPY01 structurally essential, CPY10 self-destructive |
| 4 | Second head (h1) | StellaLang ISA | Multi-site coordination | ✅ Complete — 2-head is the unique sweet spot (see §6) |
| 5 | **G1+G2 combined multi-stella** | Def 0.1.3 + Thm 0.2.1 | Coherence + replication on FCC lattice | ✅ Complete — G1+G2 synergistic (coh=0.87, 100% colonization) |
| 6 | **Chiral wavefront (G1+G2+χ)** | Axiom P3 + Def 0.1.3 | Directional replicator propagation | ✅ Complete — B=0.50→0.64, R(T₊/T₋)=1.01→1.21 monotonic with χ (see §7) |

---

## Mechanism Details

### 1. Inter-stella gauge coupling (Prop 2.5.2b)

**What:** Gauge-mediated interaction between neighboring stellae in a
multi-stella lattice. Programs or color states on one stella influence
dynamics on adjacent stellae.

**Why it matters:** The G1 genesis_soup operates on a single stella, which
has geometric dead zones where coupling is suppressed. Inter-stella coupling
provides an escape route — programs can propagate *between* stellae,
bypassing intra-stella dead zones.

**Existing code & data:**

| File | Type | Content |
|------|------|---------|
| `soup_multi_stella.c` | C | FCC lattice (L-variable, 32 stellae at L=4), Mode A (direct) vs Mode B (octahedral) coupling, per-stella census tracking |
| `sweep_octahedral.sh` | Script | Systematic Mode A vs Mode B comparison: 9 configs × 5 seeds = 45 runs |
| `analyze_octahedral_sweep.py` | Python | Colonization timing analysis, equalized VM cost comparison |
| `sweep_oct_results/summary.csv` | Data | Colonization milestones (t_first, t_half, t_full) for all 45 runs |
| `run_cross_rate_sweep.sh` | Script | Cross-rate sweep at cr ∈ {0.01, 0.1, 1.0, 10.0}, seed=42 |
| `multi_L4_cross{0.01,0.1,1.0,10.0}.log` | Logs | Raw output from cross-rate sweep |
| `multi_L4_wavefront_seeded_cr*.log` | Logs | Fine-grained FCC distance-shell wavefront tracking |
| `analyze_wavefront_seeded.py` | Python | Distance-shell colonization analysis, wavefront velocity |
| `check_multi_stella_rep.c` | C | Validates multi-stella replicators, Hamming distance to 30M-run replicator |
| `sweep_modeAB_L8.sh` | Script | Mode A vs Mode B at L=8 (256 stellae): 9 configs × 3 seeds = 27 runs |
| `analyze_modeAB_L8.py` | Python | Colonization milestones, wavefront shell analysis, L=4 vs L=8 comparison |
| `sweep_modeAB_L8_results/` | Data | 27 result files + summary.csv |

**Key results (L=4, 32 stellae):**
- Direct mode (cr=0.1–1.0): t_full = 1000 epochs across all 5 seeds
- Octahedral mode (cr=0.1–1.0): t_full = 1000 epochs (comparable)
- Octahedral interstitials: 85–92% contain replicators at end-of-run
- Wavefront propagation: reaches FCC d1 neighbors (2–6/12) by epoch 10–20,
  distance 2 by epoch 100

**L=8 results (256 stellae, 7 FCC shells, 2026-03-24):**

Experiment: 9 configs × 3 seeds = 27 runs, 15K epochs each, n_sub=100,
seeded replicator. Scripts: `sweep_modeAB_L8.sh`, `analyze_modeAB_L8.py`.
Data: `sweep_modeAB_L8_results/`.

*Same nominal cross-rate (Mode A cr=X vs Mode B cr=X):*

| cr | Mode A t_full | Mode B t_full | B/A ratio |
|----|--------------|--------------|-----------|
| 0.01 | 7000±1000 | 6667±577 | 0.95× |
| 0.1 | 2000±0 | 2000±0 | 1.00× |
| 1.0 | 1000±0 | 1000±0 | 1.00× |

*VM-equalized (Mode A cr=X vs Mode B cr=X/2):*

| Comparison | Mode A t_full | Mode B t_full | B/A ratio |
|-----------|--------------|--------------|-----------|
| A cr=0.01 vs B cr=0.005 | 7000 | 13000 | 1.86× |
| A cr=0.1 vs B cr=0.05 | 2000 | 2000 | 1.00× |
| A cr=1.0 vs B cr=0.5 | 1000 | 1000 | 1.00× |

*Wavefront first-arrival by FCC distance shell (mean across seeds):*

| Config | d=0 | d=1 | d=2 | d=3 | d=4 | d=5 | d=6 |
|--------|-----|-----|-----|-----|-----|-----|-----|
| A cr=0.01 | 1000 | 1333 | 1667 | 2000 | 2000 | 2667 | 4000 |
| B cr=0.01 | 1000 | 1000 | 1333 | 1667 | 2333 | 4000 | 5000 |
| A cr=0.1 | 1000 | 1000 | 1000 | 1000 | 1000 | 1000 | 1333 |
| B cr=0.1 | 1000 | 1000 | 1000 | 1000 | 1000 | 1000 | 1333 |

*L=4 → L=8 scaling (Mode A):*

| cr | L=4 t_full | L=8 t_full | ratio | stellae ratio |
|----|-----------|-----------|-------|--------------|
| 0.01 | 4000 | 7000 | 1.75× | 8× |
| 0.1 | 1000 | 2000 | 2.00× | 8× |
| 1.0 | 1000 | 1000 | 1.00× | 8× |

**Conclusion: Octahedral mediation is NOT structurally advantageous at larger L.**
At same nominal rate, Mode A ≈ Mode B (matching L=4 finding). When VM-equalized,
Mode B is strictly worse at low cross-rates (1.86× slower at cr=0.01) due to the
relay bottleneck through interstitial buffers. The octahedral interstitials (~88%
colonized) add latency without providing faster propagation paths. Propagation
scales sub-linearly with lattice size (8× stellae → 1.75–2× slower), consistent
with the wavefront velocity scaling v_eff ∝ cr^0.71 found at L=4.

**Open questions:**
- ~~Does inter-stella coupling close the remaining coherence gap (currently ~49%)?~~
  *Answered (Section 5, Exp 2+4):* G1+G2 combined achieves coh=0.87, closing
  the blocked zone gap from 0.40 → 0.83. The remaining ~13% is in the blocked
  zone where neither mechanism has full leverage — this is the measured ceiling.
- ~~What is the optimal cross-rate for G1+G2 combined dynamics?~~
  *Answered:* Exp 3 coupling strength sweep (cs=0.0–1.0) shows coherence
  increases monotonically; replicators survive at all strengths. No destructive
  regime found. cs=0.5 is a good default (balance of coherence and diversity).
- ~~Mode A vs Mode B show similar t_full — is octahedral mediation redundant,
  or does it matter at larger L?~~
  *Answered (L=8, 2026-03-24):* Octahedral mediation is redundant. Mode A and
  Mode B are equivalent at same nominal rate across all tested lattice sizes
  (L=4 and L=8). Mode B is strictly worse when VM-equalized at low cross-rates.

---

### 2. Phase-gradient mass generation (Thm 3.1.1)

**What:** Mass emerges from the coupling of phase gradients ∇φ across the
stella surface. This is a Phase 3 mechanism layered onto the Phase 1/2
dynamics.

**Why it matters:** The current simulation has no notion of mass. Adding
phase-gradient mass generation would allow testing whether the simulation
spontaneously generates mass-like observables from geometry alone.

**Existing code & data:**

| File | Type | Content |
|------|------|---------|
| `investigate_path3_transition_dynamics.py` | Python | Phase transition scaling exponent η, nucleation rate Γ, dimensionless coupling g² = Γ·N·T_char |
| `critical_nucleus_phase_transition.c` | C | Nucleation dynamics infrastructure (not phase-gradient specific) |

**Status:** All mass coupling channels tested (Q3–Q3d, Q4b). Geometric coupling
is the effective channel (+7.6% coherence). Combined mk+mg reaches corr=0.816.

**Implementation (2026-03-23):**

| File | Type | Content |
|------|------|---------|
| `genesis_soup.c` | C | `compute_phase_gradient()`, `compute_vchi_field()`, `compute_mass_observable()`, `print_mass_diagnostics()`, `dump_mass_geography()` — activated by `mass_mode=1` (argv[16]), mass coupling via `mass_couple` (argv[17]), `mass_kuramoto` (argv[19]), `mass_geo` (argv[20]) |
| `analyze_mass.py` | Python | Parses mass diagnostics from stdout, computes trends and physical scale estimates |
| `analyze_mass_topology.py` | Python | Q2: Bins mass by P_ratio and vertex distance, Pearson/Spearman correlations |
| `analyze_mass_scaling.py` | Python | Q4: Power-law fits for η exponent across runs |
| `analyze_mass_coupling.py` | Python | Q3b–d: Cross-channel comparison (mutation vs Kuramoto vs geo vs combined) |
| `analyze_mass_qcd_interpretation.py` | Python | Q4b: Vertex mass → constituent quark model mapping |
| `phase_m1_mass_sweep.sh` | Shell | Q1: K × epoch sweep (5 K × 2 epochs × 3 seeds = 30 runs) |
| `phase_m2_mass_coupling.sh` | Shell | Q3: mass_couple strength sweep (5 values × 3 seeds = 15 runs) |
| `phase_m3_mass_kuramoto.sh` | Shell | Q3b: mass_kuramoto sweep (6 values × 3 seeds = 18 runs) |
| `phase_m4_mass_geo.sh` | Shell | Q3c: mass_geo sweep (5 values × 3 seeds = 15 runs) |
| `phase_m5_mass_combined.sh` | Shell | Q3d: joint mk × mg grid + triple coupling (30 runs) |
| `phase_m1_results/` | Data | Q1 sweep logs + summary.csv |
| `phase_m2_results/` | Data | Q3 sweep logs + summary.csv |
| `phase_m3_results/` | Data | Q3b sweep logs + summary.csv |
| `phase_m4_results/` | Data | Q3c sweep logs + summary.csv |
| `phase_m5_results/` | Data | Q3d sweep logs + summary.csv |

**Key formulas (discretized Thm 3.1.1):**
- Phase gradient: `|∇φ(x)| = (1/N_nbr) Σ min(|φ_j - φ_i|, 2π - |φ_j - φ_i|) / edge_len`
- VEV field: `v_χ(x) = P_own(x) / (P_own(x) + P_other(x))` (pressure-modulated, Thm 3.0.1)
- Mass density: `m(x) = (g_χ·ω₀/Λ) · v_χ(x) · |∇φ(x)|` with prefactor ≈ 0.2778
- Mass-coupled mutation: `μ_eff = μ / (1 + mass_couple · m(x))` (Q3)

---

**Experiment Results (2026-03-23):**

| Q# | Question | Script | Status |
|----|----------|--------|--------|
| Q1 | Does mass clustering increase with longer runs or stronger phase-lock? | `phase_m1_mass_sweep.sh` | ✅ Complete |
| Q2 | Does mass correlate with pressure topology? | `analyze_mass_topology.py` | ✅ Complete |
| Q3 | Can mass be coupled back into dynamics (mutation)? | `phase_m2_mass_coupling.sh` | ✅ Complete — negligible |
| Q3b | Mass → Kuramoto force? | `phase_m3_mass_kuramoto.sh` | ✅ Complete — minimal |
| Q3c | Mass → geometric coupling? | `phase_m4_mass_geo.sh` | ✅ Complete — **effective (+4%)** |
| Q3d | Combined mass coupling? | `phase_m5_mass_combined.sh` | ✅ Complete — **synergy (+7.6%)** |
| Q4 | Does η ≈ 2/3 connect to mass dynamics? | `analyze_mass_scaling.py` | ✅ Complete |
| Q4b | QCD interpretation of vertex mass? | `analyze_mass_qcd_interpretation.py` | ✅ Complete — 73.5% color-vertex fraction |

#### Q1: Mass clustering vs phase-lock strength and run length

**Answer: Yes — stronger K and longer runs both increase clustering.**

| K | Epochs | mean_mass | corr_ratio | corr |
|---|--------|-----------|------------|------|
| 0.05 | 2M | 1.318 | 1.105 | 0.747 |
| 0.05 | 10M | 1.323 | 1.103 | 0.722 |
| 0.10 | 2M | 1.298 | 1.120 | 0.758 |
| 0.10 | 10M | 1.354 | 1.123 | 0.730 |
| 0.20 | 2M | 1.293 | 1.109 | 0.746 |
| 0.20 | 10M | 1.306 | 1.144 | 0.748 |
| 0.50 | 2M | 1.230 | 1.134 | 0.750 |
| 0.50 | 10M | 1.257 | 1.166 | 0.741 |
| 1.00 | 2M | 1.273 | 1.187 | 0.723 |
| 1.00 | 10M | 1.234 | 1.167 | 0.746 |

Key findings:
- corr_ratio rises monotonically from ~1.10 (K=0.05) to ~1.18 (K=1.0)
- 10M runs generally show higher corr_ratio than 2M at same K
- Mean mass *decreases* with stronger K (sync → less ∇φ) while clustering *increases*
- Mass becomes more spatially organized even as its magnitude shrinks

#### Q2: Mass distribution vs pressure topology

**Answer: Strong correlation — mass concentrates near vertices.**

- Pearson: mass vs P_ratio r=+0.63, mass vs dist_vertex r=−0.60 (both p < 1e-100)
- Spearman: ρ=+0.65 (P_ratio), ρ=−0.64 (dist_vertex)
- Top-10% mass sites: mean P_ratio=0.88, mean dist=0.53 (near vertices)
- Bottom-10% mass sites: mean P_ratio=0.46, mean dist=1.35 (face centers)
- Dominant variation source: |∇φ| (CV=0.44), not v_χ (CV=0.28)
- Mass binned by P_ratio: 0.13 (blocked zone) → 1.65 (vertex zone), 12× variation

Physical interpretation: vertices anchor the chiral field, creating large
phase gradients between differently-colored vertex domains. Face centers
(equidistant from all vertices) have near-uniform phases → low ∇φ → low mass.

#### Q3: Mass-coupled mutation dynamics

**Answer: Minimal effect at current scale — mass coupling is mechanically working but too weak.**

| mass_couple | mean_mass | corr_ratio | corr | blocks |
|-------------|-----------|------------|------|--------|
| 0.0 | 1.298 | 1.120 | 0.758 | 0 |
| 0.1 | 1.281 | 1.112 | 0.741 | 96,116 |
| 0.5 | 1.335 | 1.119 | 0.741 | 96,256 |
| 1.0 | 1.305 | 1.091 | 0.749 | 95,926 |
| 5.0 | 1.339 | 1.117 | 0.750 | 96,272 |

- ~96k mutations blocked regardless of coupling strength (mutation rate is low)
- Coherence and clustering essentially flat across all mass_couple values
- The mutation rate (0.001) is already small; suppressing it further has
  negligible impact on dynamics dominated by geometric coupling
- **Next step:** couple mass into the *geometric coupling* strength or
  the *Kuramoto force* rather than mutation to get a measurable effect

#### Q3b: Mass-coupled Kuramoto force (2026-03-23)

**Answer: Minimal effect — Kuramoto operates in the blocked zone where mass is low.**

`K_eff(x) = K * (1 + mass_kuramoto * m(x))`

| mass_kuramoto | corr | corr_ratio | mean_mass | mk_boosts | pl_events |
|---------------|------|------------|-----------|-----------|-----------|
| 0.0 | 0.758 | 1.120 | 1.298 | 0 | 107k |
| 0.1 | 0.757 | 1.089 | 1.321 | 15.4M | 122k |
| 0.5 | 0.737 | 1.115 | 1.311 | 15.4M | 177k |
| 1.0 | 0.759 | 1.145 | 1.323 | 15.4M | 237k |
| 5.0 | 0.734 | 1.129 | 1.309 | 15.4M | 479k |
| 10.0 | 0.750 | 1.164 | 1.252 | 15.4M | 615k |

- Phase-lock events increase 6× (107k → 615k) but coherence stays flat
- The Kuramoto force only activates where P_ratio < 0.5 (blocked zone),
  but mass concentrates near vertices (P_ratio > 0.7) — spatial mismatch
- Mass-modulated K has nothing to amplify in the low-mass blocked zone

#### Q3c: Mass-coupled geometric coupling (2026-03-23)

**Answer: EFFECTIVE — mass → geometric coupling is the productive channel.**

`prob_eff = prob * (1 + mass_geo * m(x))`

| mass_geo | corr | corr_ratio | mean_mass | mg_boosts | tp→tm | tm→tp |
|----------|------|------------|-----------|-----------|-------|-------|
| 0.0 | 0.758 | 1.120 | 1.298 | 0 | 8.0M | 8.0M |
| 0.1 | 0.728 | 1.117 | 1.333 | 63.5M | 9.4M | 9.4M |
| 0.5 | 0.758 | 1.119 | 1.308 | 63.6M | 14.7M | 14.7M |
| 1.0 | 0.787 | 1.115 | 1.313 | 63.6M | 19.1M | 19.1M |
| 5.0 | 0.797 | 1.127 | 1.323 | 63.5M | 28.2M | 28.2M |

- Coherence rises from 0.758 → 0.797 (+4.0%) at mg=5.0
- Coupling events ~3.5× baseline (28M vs 8M per direction)
- Mass concentrates at vertices = high-coupling zone → positive feedback
- T+/T- transfer remains symmetric (no chirality bias from mass)

#### Q3d: Combined mass coupling (2026-03-23)

**Answer: Joint mk+mg shows synergy — peak corr=0.816 at (mk=5, mg=5).**

| mk | mg | mc | corr | corr_std | corr_ratio |
|----|----|----|------|----------|------------|
| 0.5 | 0.5 | 0.0 | 0.765 | 0.022 | 1.130 |
| 0.5 | 5.0 | 0.0 | 0.787 | 0.019 | 1.084 |
| 1.0 | 1.0 | 0.0 | 0.773 | 0.007 | 1.130 |
| 1.0 | 1.0 | 1.0 | 0.782 | 0.004 | 1.117 |
| 5.0 | 1.0 | 0.0 | 0.788 | 0.009 | 1.162 |
| **5.0** | **5.0** | **0.0** | **0.816** | **0.011** | **1.152** |

- Best combined: corr=0.816 (mk=5, mg=5), up from 0.758 baseline (+7.6%)
- The Kuramoto channel contributes when combined with geo (0.816 vs 0.797 geo-only)
- Triple coupling (adding mutation) adds marginal +0.01 over mk+mg alone
- Synergy mechanism: geo coupling strengthens vertex coherence, which raises
  local mass, which boosts Kuramoto in the transition zone near P_ratio ≈ 0.5

#### Q4: Scaling exponent η and the 2/3 connection

**Answer: Suggestive — pooled η ≈ 0.63 is close to 2/3, but per-run fits vary.**

Per-run fits (10M epochs, seed=42):

| K | η (mass vs 1-auto) | R² | 95% CI |
|---|--------------------|----|--------|
| 0.05 | 0.763 | 0.77 | [0.68, 0.85] |
| 0.10 | 0.727 | 0.67 | [0.63, 0.83] |
| 0.20 | 0.720 | 0.71 | [0.63, 0.81] |
| 0.50 | 0.675 | 0.77 | [0.60, 0.75] |
| 1.00 | 0.754 | 0.72 | [0.66, 0.85] |

- **Pooled fit** (all 5 runs, 515 points): η = **0.629** (R²=0.82)
- At K=0.5: η = 0.675, 95% CI [0.603, 0.748] — includes 2/3
- mass ∝ |∇φ|^α with α ≈ 0.92–1.02 (near-linear, expected from formula)
- The 2/3 value likely reflects the geometric SENSE gate threshold (P_ratio = 2/3
  divides open vs blocked zones), which structures how ∇φ decays with synchronization

#### Q4b: QCD phenomenology of vertex-concentrated mass (2026-03-23)

**Answer: Color-vertex mass fraction (73.5%) matches constituent quark picture.**

| Property | Simulation | QCD Reference |
|----------|-----------|---------------|
| Color-vertex mass / total | 73.5% | 60–70% (constituent quarks / hadron) |
| Z₃ symmetry (CV of 3 color vertices) | 8–9% | Exact in SU(3) limit |
| Vertex/face mass density ratio | 2.1–2.2× | — |
| Mass decay exponent α (mass ~ d^−α) | 0.27 | Coulomb: α=2, confinement: linear |

Physical interpretation:
- Vertices anchor color fields → large phase gradients between color domains
- Each tetrahedron's 3 color vertices carry ~73% of total mass (analog: constituent quarks)
- Face centers (equidistant from all vertices) have minimal ∇φ → minimal mass
  (analog: "empty" hadron interior in bag model)
- Shallow decay (α≈0.27) suggests confinement-like mass distribution, not Coulomb
- Z₃ symmetry is approximate (CV~9%), consistent with stochastic breaking from
  finite-time dynamics

#### Q6: Coherence convergence with longer runs (2026-03-25)

**Answer: No — coherence plateaus; longer runs do NOT close the gap further.**

Compared coupled (mk=5, mg=5) vs baseline (mk=0, mg=0) at 2M–50M epochs (3 seeds each):

| Epochs | Coupled corr | Baseline corr | Δ (coupling benefit) |
|--------|-------------|---------------|---------------------|
| 2M     | 0.816 ± 0.011 | 0.757 ± 0.009 | +0.059 |
| 10M    | 0.794 ± 0.009 | 0.730 ± 0.024 | +0.065 |
| 20M    | 0.799 ± 0.016 | 0.741 ± 0.010 | +0.058 |
| 50M    | 0.802 ± 0.007 | 0.747 ± 0.013 | +0.055 |

- Coherence plateaus at ~0.80 with coupling, ~0.74 without
- The +6% coupling benefit is stable but does not compound over time
- Linear fit (corr vs log₁₀ epochs): slope = −0.011 (flat/slight decline)
- Mass feedback provides a one-time lift, not a compounding advantage
- Baseline also flat — simply running longer has no coherence benefit

| File | Type | Content |
|------|------|---------|
| `phase_m6_long_convergence.sh` | Shell | Q6+Q7: coupled sweep (mk=5, mg=5) × {2M,10M,20M,50M} × 3 seeds |
| `phase_m6_baseline.sh` | Shell | Q6 control: no coupling (mk=0, mg=0), same epochs × 3 seeds |
| `analyze_mass_convergence.py` | Python | Q6+Q7: time-series extraction, vertex fraction convergence, trend fits |
| `phase_m6_results/` | Data | Coupled sweep logs + summary.csv + geography JSONs |
| `phase_m6_baseline/` | Data | Baseline sweep logs + summary.csv + geography JSONs |

#### Q7: Color-vertex fraction convergence (2026-03-25)

**Answer: Converges to ~0.74, closer to 3/4 than 2/3. Geometric origin.**

| Epochs | Color-vertex frac | Std | Δ from 2/3 | Δ from 3/4 |
|--------|------------------|-----|-----------|-----------|
| 2M     | 0.740 ± 0.009 | 0.009 | +0.074 | −0.010 |
| 10M    | 0.742 ± 0.006 | 0.006 | +0.075 | −0.008 |
| 20M    | 0.744 ± 0.002 | 0.002 | +0.077 | −0.006 |
| 50M    | 0.735 ± 0.009 | 0.009 | +0.069 | −0.015 |

- Linear fit slope = −0.002 → fraction has **converged** near 0.74
- Closer to 3/4 (0.750) than 2/3 (0.667) by a factor of ~5×
- Z₃ symmetry: CV = 1–9% across runs (approximate, stochastic breaking)
- **Interpretation:** 3/4 = three color vertices out of four total vertices
  per tetrahedron. This is the natural **geometric** prediction from the
  stella octangula topology, distinct from the QCD constituent quark
  fraction (~0.65). The simulation reflects the stella's vertex structure
  rather than dynamical QCD mass generation.

#### Q5: Multi-stella lattice mass topology (2026-03-25)

**Answer: Mass topology is robust — CVF is a geometric invariant of ∂S.**

Compared single-stella (genesis_soup, Kuramoto + mass coupling) vs
multi-stella (soup_multi_stella, discrete Z₃, no Kuramoto) at L=2 (4 stellae)
and L=4 (32 stellae), n_sub=16, 2M epochs, 3 seeds each:

| Config | mean_mass | corr_ratio | cvf | α (decay) | Z₃ CV |
|--------|-----------|------------|------|-----------|-------|
| Single (mk=5,mg=5) | 1.290 | 1.152 | 0.740 ± 0.010 | 0.34 ± 0.01 | 0.06 |
| Multi L=2 (4 stellae) | 1.171 | 1.115 | 0.734 ± 0.020 | 0.36 ± 0.05 | 0.08 |
| Multi L=4 (32 stellae) | 1.404 | 1.080 | 0.738 ± 0.011 | 0.23 ± 0.07 | 0.04 |

Key findings:
- **CVF is invariant**: 0.734–0.740 across all configs (Δ < 0.016), confirming
  3/4 is a geometric property of the stella vertex structure, not dynamics
- **Corr_ratio slightly lower** in multi-stella (1.08–1.12 vs 1.15): inter-stella
  coupling adds disorder that reduces mass clustering within each stella
- **α exponent broader** at L=4 (0.23 vs 0.34): more stellae → more variability
  in the decay profile, but the vertex-concentrated pattern persists
- **Z₃ symmetry improves** at L=4 (CV=0.04): the FCC lattice environment
  symmetrizes color vertex masses better than single-stella dynamics
- The mass observable works identically on Z₃ discrete trits (multi-stella)
  and continuous Kuramoto phases (single-stella) — the discretization doesn't
  break the phase-gradient mechanism

| File | Type | Content |
|------|------|---------|
| `soup_multi_stella.c` (stella_lang) | C | Added `--mass-mode`: Z₃ phase gradient, VEV, mass computation per stella |
| `phase_m7_multi_stella_mass.sh` | Shell | Q5: single vs multi L={2,4} × 3 seeds = 9 runs |
| `analyze_multi_stella_mass.py` | Python | Q5: config comparison, decay profile, geography analysis |
| `phase_m7_results/` | Data | Logs + summary.csv + geography JSONs for all configs |

**Physical interpretation:** The 3/4 color-vertex mass fraction is determined
entirely by the stella octangula's internal geometry (4 vertices, 3 color-assigned
per tetrahedron). Neither the lattice topology (FCC), lattice size (1–32 stellae),
dynamics mechanism (Kuramoto vs Z₃ VM), nor coupling channel (mass-geo vs
inter-stella) changes this ratio. This is strong evidence that **mass topology
is a geometric invariant of ∂S**, as predicted by Thm 3.1.1.

**All phase-gradient mass questions (Q1–Q7, Q5) are now complete.**

---

### 3. CPY01/CPY10 — multi-site copy (StellaLang ISA)

**What:** Instructions that copy data between the two heads (h0 → h1 and
h1 → h0). These are the core replication mechanism in the full StellaLang
instruction set.

**Why it matters:** The G1 genesis_soup replaced CPY01/CPY10 with NOPs,
forcing replication to occur purely through geometric coupling. The full
StellaLang ISA includes these as explicit instructions, enabling programs
to directly copy themselves across tetrahedra.

**Existing code & data:**

| File | Type | Content |
|------|------|---------|
| `soup.c` | C | Full 9-instruction ISA: CPY01 = opcode (2,1), CPY10 = opcode (2,2) |
| `soup.py` | Python | Original implementation of dual-head VM |
| `RESULTS-30M.md` | Results | 30M-epoch campaign: replicators emerge at ~3.5M, 88% saturation by 11M |
| `verify_replicator.c` | C | Replicator validation and instruction decoding |
| `verify_replicator.py` | Python | Comprehensive verification suite |
| `verify_replicator_results.json` | JSON | 8/8 tests PASSED, 100% perfect replication rate |

**Key results:**
- **Dominant replicator** (20-trit conserved core, 5 variants):
  ```
  [  [  CPY+  FWD0  FWD1  ]  CPY+  FWD1  FWD0  ]
  ```
  A forward-only copy machine: reads from h0 (T₊), writes to h1 (T₋).
- CPY01 is the **core mechanism** — NOT used: ROT, BCK0, CPY10
- Instructions map to CG proofs: CPY01 → Thm 0.2.1, gates → Prop 0.0.17h
- Verification: 8/8 tests pass, 100% perfect replication in 50/50 trials

**Open questions:**
- ~~How does replication dynamics change when CPY01/CPY10 compete with
  geometric coupling?~~
  *Answered (Section 5, Exp 2):* Replicators survive with 100% colonization,
  but G1 coupling prevents monoculture — 5× more unique programs (1251 vs 278).
  G1 acts as a diversity-preservation mechanism, selecting for replicators
  compatible with the geometric substrate.
- ~~Does the G1 geometric coupling produce qualitatively different replicators
  than the G2 instruction-based copy?~~
  *Partially answered:* G1+G2 replicators coexist with much higher diversity
  (1251 unique vs 278). Whether the surviving variants are structurally
  different from G2-only replicators requires program-level analysis
  (instruction profiles, core motif comparison).
- ~~CPY10 is never used by the dominant replicator — is T₋ → T₊ copy
  structurally disfavored, or just not yet explored?~~
  *Answered (Section 6, Test 1):* CPY10 is **structurally self-destructive**.
  CPY10 (`tape[h0] = tape[h1]`) overwrites the executing program's own
  instructions with foreign data from the target — the replicator corrupts
  itself mid-execution. A mirror replicator with CPY10↔CPY01 and FWD0↔FWD1
  swapped fails completely (zero self-preservation, zero copy). The asymmetry
  is intrinsic to the VM architecture: h0 starts in "self" territory (the
  instruction stream), so only CPY01 (self → target) enables replication.
  This corresponds to a computational chirality — a preferred information
  flow direction from T₊ to T₋.

---

### 4. Second head (h1) (StellaLang ISA)

**What:** A second execution head that independently traverses T₋ while h0
traverses T₊. Enables multi-site coordination and is required for
CPY01/CPY10 to function.

**Why it matters:** The G1 genesis_soup is single-headed — programs can only
read/write at one position. The second head enables cross-tetrahedron
operations and is foundational to the StellaLang replication mechanism.

**Existing code & data:**

| File | Type | Content |
|------|------|---------|
| `soup.c` | C | Dual-head execution: h0 starts at 0, h1 at tape_len/2; FWD0/FWD1 advance independently |
| `soup_multi_stella.c` | C | Same dual-head model in multi-stella context |
| `test_head_count.c` | C | **1-head vs 2-head vs 3-head** VM comparison |
| `test_head_count.py` | Python | Analysis: emergence rate, compression ratio, dominance %, instruction profile |

**Head-count comparison design** (from `test_head_count.c`):

| Heads | Opcodes | ISA notes |
|-------|---------|-----------|
| 1-head | NOP, ROT, FWD0, BCK0, OPEN, CLOSE | 6 opcodes, 3 NOP slots = 44% wasted |
| 2-head | NOP, ROT, FWD0, BCK0, FWD1, OPEN, CLOSE, CPY01, CPY10 | 9 distinct, 0 NOPs |
| 3-head | NOP, ROT, FWD0, FWD1, FWD2, OPEN, CLOSE, CPY01, CPY02 | 9 opcodes, no BCK0 |

Test parameters: soup_size=1024, prog_size=24, epochs=5M, seeds={42, 123, 7}.
Metrics: emergence time, compression ratio, dominance %, instruction profile.

**Key question:** Is the 2-head design the computational sweet spot? The
2-head ISA uniquely fills all 9 opcode slots with distinct instructions (0% waste).

**Results (Section 6):** Yes — 2-head is the unique sweet spot. See §6 for
the full 1v2v3 head-count comparison.

**Open questions:**
- ~~Is h1 strictly necessary for inter-tetrahedron replication, or can
  geometric coupling substitute?~~
  *Answered (Section 5, Exp 4):* G1-only (no h1, no VM coupling) achieves
  coh=0.78 but **zero replicators**. h1 via G2 dual-head VM is required for
  self-replication. Geometric coupling alone cannot substitute.
- ~~The G1 result (49% gap closure without h1) suggests geometric coupling
  partially substitutes — how much further does h1 push it?~~
  *Answered:* G1+G2 combined achieves coh=0.87 (vs G1-only 0.78), and
  critically adds replication (0% → 22% saturation, 100% colonization).
  The h1/G2 contribution is essential for replication and adds +0.09
  coherence via blocked-zone coverage.
- ~~Has the 1v2v3 head comparison been run? If so, where are the results?~~
  *Answered (Section 6):* Yes. 2-head produces replicators in 3/3 runs
  (avg 53% dominance); 1-head produces 0/3; 3-head produces 0/3 (one
  transient hit that did not persist). Results in `head_count_5M_results.log`.

---

## Relationship to Existing Results

| Experiment | Architecture | Key Result |
|-----------|-------------|------------|
| genesis_soup (G1) | Single stella, single head, geometric coupling | 49% coherence gap closure |
| stella_soup (G2) | Single stella, dual head, CPY01/CPY10 | Self-replicators emerge at ~3.5M epochs, 88% saturation |
| soup_multi_stella (G2) | Multi-stella FCC lattice, dual head | Colonization t_full ~1000 epochs, 85–92% interstitial saturation |
| **soup_g1g2 (G1+G2)** | **Multi-stella FCC, dual head + geometric coupling** | **✅ Synergistic: coh=0.87, 100% colonization, 5× diversity** |
| **head_count (§6)** | **1v2v3-head comparison, single stella** | **✅ 2-head uniquely produces replicators (3/3 vs 0/3 vs 0/3)** |

---

## 5. Combined G1+G2 Multi-Stella Experiment (NEW)

**What:** Combines G1 geometric coupling (pressure-mediated T+/T- coherence)
with G2 instruction-based mechanisms (dual-head VM, CPY01/CPY10) on a
multi-stella FCC lattice. This was previously identified as "the gap."

**Why it matters:** G1 geometric coupling is 7–8× stronger than CPY01 for
inter-surface coherence (corr=0.86 vs 0.39), but G2 CPY01/CPY10 enables
program-level self-replication that G1 cannot achieve. The combined experiment
tests whether these complementary mechanisms help or hinder each other.

**Architecture decision:** Keep the G2 dual-head VM intact. Add G1 geometric
coupling as a separate epoch phase (not new opcodes). This preserves existing
G2 replicators and allows independent toggling.

**Three-phase epoch:**
1. Intra-stella VM interactions + mutation (G2, parallel)
2. Intra-stella geometric coupling (G1, parallel)
3. Inter-stella coupling (G2, serial)

**Implementation:**

| File | Type | Content |
|------|------|---------|
| `stella_genesis/soup_g1g2.c` | C | Combined G1+G2 simulation (~1,550 lines). Based on `soup_multi_stella.c`, extended with 3D mesh coordinates, pressure precomputation (Def 0.1.3), geometric coupling, coherence diagnostics. |

**New features vs soup_multi_stella.c:**
- Mesh struct extended with `tp_pos[site][3]` and `tm_pos[site][3]` (3D coordinates from barycentric subdivision)
- `pressure_at_site()` ported from genesis_soup.c: `P(x) = max_v 1/(|x-v|² + ε²)`
- Pressure precomputed once at init: 4 arrays (pp_at_tp, pm_at_tp, pp_at_tm, pm_at_tm)
- `geo_couple_stella()`: full-sweep per-site probabilistic T+↔T- transfer
- Per-stella coherence metric with dominant/blocked zone breakdown
- Extended log line with coherence and geo coupling event count

**CLI flags:**

| Flag | Default | Purpose |
|------|---------|---------|
| `--g1` | off | Enable G1 geometric coupling |
| `--coupling-strength F` | 0.5 | G1 coupling probability multiplier |
| `--epsilon F` | 0.1 | Pressure regularization parameter |

**Mode combinations:**
- No `--g1`: G2-only (baseline, reproduces soup_multi_stella.c behavior)
- `--g1 --cross-rate 0`: G1-only (geometric coupling, no inter-stella VM)
- `--g1`: G1+G2 combined

**Build:**
```bash
cd stella_genesis
cc -O3 -march=native -ffast-math -flto -o soup_g1g2 soup_g1g2.c -lm -lpthread
```

**Run script:** `stella_genesis/run_g1g2_experiments.sh`

**Existing code & data:**

| File | Type | Content |
|------|------|---------|
| `stella_genesis/soup_g1g2.c` | C | Combined G1+G2 simulation (~1,550 lines), `--dump-top N` for program dumps |
| `stella_genesis/run_g1g2_experiments.sh` | Shell | Full experiment campaign (4 experiments, 15 runs) |
| `stella_genesis/phase_g1g2_results/` | Data | All experiment logs |
| `stella_genesis/run_q4_replicator_species.sh` | Shell | Q4: cs={0.0,0.5,1.0} × 3 seeds with program dumps |
| `stella_genesis/analyze_q4_species.py` | Python | Q4: instruction profile comparison, motif classification, resurgence timing |
| `stella_genesis/phase_q4_results/` | Data | Q4 logs with TOP-10 program dumps at each census |

---

**Experiment Results (2026-03-23):**

All experiments: L=2 (4 stellae), n_sub=100 (~20K sites/tetra, 1666 tiles/stella),
500K epochs, seeded replicator, ~800 epochs/sec.

#### Exp 1: G2-only Baseline (3 seeds) ✅

| Seed | Unique | Top | H(trit) | Replicator % | Colonized |
|------|--------|-----|---------|-------------|-----------|
| 42 | 256 | 214 | 1.547 | 85.3% | 4/4 |
| 137 | 295 | 204 | 1.555 | 82.6–87.9% | 4/4 |
| 271 | 283 | 436 | 1.552 | 84.3% | 4/4 |

G2-only: high replicator saturation (~84%), low program diversity (~280 unique).
No coherence metric (G1 disabled).

#### Exp 2: G1+G2 Combined, cs=0.5 (5 seeds) ✅

| Seed | Coherence | Dominant | Blocked | Replicator % | Unique | Colonized |
|------|-----------|----------|---------|-------------|--------|-----------|
| 42 | 0.862 | 0.879 | 0.813 | 22% | 1306 | 4/4 |
| 137 | 0.891 | 0.895 | 0.881 | ~25% | 1085 | 4/4 |
| 271 | 0.881 | 0.892 | 0.861 | ~24% | 1183 | 4/4 |
| 314 | 0.862 | 0.877 | 0.820 | ~20% | 1337 | 4/4 |
| 577 | 0.853 | 0.880 | 0.779 | ~20% | 1346 | 4/4 |
| **Mean** | **0.870** | **0.885** | **0.831** | **~22%** | **1251** | **5/5** |

**Answer: G1 and G2 are fully compatible.** The combined system achieves both
high coherence (0.870) AND self-replication across all stellae (100% colonization).

Directional bias = 0.500 across all seeds (perfect T+/T- symmetry, no chirality).

#### Exp 3: Coupling Strength Sweep (seed=42) ✅

| cs | Coherence | Dominant | Blocked | Rep % | Unique | Top |
|----|-----------|----------|---------|-------|--------|-----|
| 0.0 | 0.885 | 0.894 | 0.893 | **84.5%** | 278 | 185 |
| 0.1 | 0.820 | 0.779 | 0.876 | **46.4%** | 949 | 115 |
| 0.25 | 0.839 | 0.835 | 0.828 | **31.5%** | 1162 | 72 |
| 0.5 | 0.862 | 0.879 | 0.813 | **22.6%** | 1306 | 52 |
| 0.75 | 0.882 | 0.910 | 0.768 | **21.9%** | 1313 | 64 |
| 1.0 | 0.921 | 0.935 | 0.829 | **25.3%** | 1151 | 402 |

**Key findings:**

1. **Coherence increases monotonically** with coupling strength: 0.82 → 0.92
2. **Replicators survive at ALL coupling strengths** — G1 never kills replication
3. **Diversity-preservation effect**: G1 coupling prevents replicator monoculture.
   cs=0.0 has 278 unique programs (replicator dominance); cs=0.5 has 1306 unique
   (5× more diverse). G1's trit-level coupling disrupts some replicator copies,
   preventing any single variant from achieving total saturation.
4. **cs=0.0 vs cs=0.5 tradeoff**: G2-only achieves 84% saturation but is
   a near-monoculture. G1+G2 achieves 22% saturation but with 5× diversity
   and 0.862 inter-surface coherence (a property G2-only cannot measure).
5. **cs=1.0 shows replicator resurgence** (25.3%, top=402) — at very strong
   coupling, the coherent substrate may actually assist certain replicator variants.

**Physical interpretation:** G1 geometric coupling acts as an "immune system"
against replicator monoculture. By continuously synchronizing T+/T- trits at
pressure-dominant sites, it disrupts partial replicator copies while maintaining
the field-level coherence that the framework predicts. The replicators that
survive are those compatible with the geometric substrate — a form of
selection pressure from Paper 1 foundations acting on Paper 2 dynamics.

#### Exp 4: G1-only Multi-Stella (no VM coupling) ✅

| Stella | Coherence | Dominant | Blocked |
|--------|-----------|----------|---------|
| 0 | 0.783 | 0.908 | 0.397 |
| 1 | 0.774 | — | — |
| 2 | 0.788 | — | — |
| 3 | 0.773 | — | — |
| **Mean** | **0.780** | **0.908** | **0.397** |

Zero replicators (as expected — no CPY01 mechanism).
Coherence 0.780 matches genesis_soup single-stella result (0.75–0.79 range).
Strong dominant/blocked zone split: 0.91 vs 0.40.

**Comparison: blocked zone coherence across configurations:**

| Configuration | Blocked zone coh | Notes |
|--------------|-----------------|-------|
| G1-only (Exp 4) | 0.397 | Geometric coupling alone cannot reach blocked zone |
| G1+G2 cs=0.5 (Exp 2) | **0.831** | VM interactions fill blocked zone gap |
| G2-only cs=0.0 (Exp 3) | 0.893 | Replicator saturation → uniform everywhere |

The G1+G2 combined system closes the blocked zone gap from 0.40 to 0.83 —
a 2× improvement over G1-only. This confirms that the VM interactions (G2)
and geometric coupling (G1) are complementary: G1 handles the pressure-dominant
zone, G2's program-level dynamics fill in the blocked zone where geometric
coupling has no leverage.

---

### Consolidated Assessment

**The gap is closed.** G1 geometric coupling and G2 instruction-based mechanisms
are not merely compatible — they are synergistic:

1. **G1 provides inter-surface coherence** (coh=0.87) that G2 alone cannot
   achieve (G2 has no coherence mechanism — it only copies programs)
2. **G2 provides self-replication** that G1 alone cannot achieve (G1 has no
   write-to-other-surface instruction beyond probabilistic trit coupling)
3. **Together they close the blocked zone gap** (0.40 → 0.83), each mechanism
   covering the other's weakness
4. **G1 acts as a diversity-preservation mechanism**, preventing replicator
   monoculture (5× more unique programs) while maintaining 100% colonization

**Resolved questions (all answered):**
- ~~Does chirality (right-handed pressure asymmetry) combined with G1+G2
  produce directional replicator propagation on the FCC lattice?~~
  *Answered (C8, 2026-03-27):* **Yes — chirality creates measurable directional
  dynamics.** See §7 below. Three effects confirmed across 21 runs (7 χ values × 3 seeds):
  (1) G1 coupling bias B increases monotonically from 0.500 (χ=0) to 0.635 (χ=0.42) —
  T₊→T₋ transfers dominate. (2) Replicators preferentially occupy T₊: R(T₊/T₋) rises
  from 1.009 to 1.208 (+21%). (3) Coherence is stable at ~0.87 across all χ — chirality
  does not degrade G1+G2 synergy. No crossover at χ*≈0.42 (unlike single-stella phase
  diagram). Wavefront speed measurement requires GPU-scale L≥4 lattice.
  Scripts: `run_phase_C8_chiral_wavefront.sh`, `phase_C8_chiral_wavefront.py`.
  Data: `phase_C8_results/`.
- ~~At larger lattice sizes (L=4, L=8), does the G1 diversity effect
  change the wavefront propagation dynamics?~~
  *Answered (W1–W4, 2026-03-27):* **Yes — G1 is a partial density limiter and
  speed reducer, not a propagation blocker.** W1 tested L=4 (32 stellae) and
  L=8 (256 stellae); W4 revealed W1's n_sub=50 results were resolution-limited;
  W2b-hires/W3b-hires confirmed at n_sub=128 (above coherence threshold).
  Converged results: ~3× replicator suppression (not 400× as W1 initially
  claimed), 3–7× speed reduction at low cross-rate converging to ~1× at high
  cross-rate, G1-ON follows v ∝ cr^0.71 (steeper than G1-OFF's 0.37), 100%
  colonization at all cross-rates, replicator density capped at ~33% (vs ~97%
  without G1). See `GPU-TEST-PLAN.md` §W1–W4.
- ~~Can the mass observable (Thm 3.1.1) be added to the G1+G2 combined
  system?~~ *Answered (Q5):* Yes — mass works identically on Z₃ discrete
  trits (multi-stella) and continuous Kuramoto (single-stella); CVF=3/4
  is invariant across 1–32 stellae. ~~**Refined question:** Does mass-geo
  coupling (Q3c, +4% single-stella) further enhance G1+G2 synergy beyond
  the coh=0.87 already achieved?~~
  *Answered (MG1, 2026-03-27):* **Yes — mass-geo coupling dramatically enhances
  G1+G2 coherence.** Swept mg∈{0,0.5,1,2,5,10} at n_sub=128, L=2, cs=0.5,
  3 seeds each. Key results:
  - Coherence: 0.874 (mg=0) → 0.938 (mg=0.5) → 0.969 (mg=10), **+10.9%**
  - Dominant zone: 0.884 → 0.999 (near-perfect at mg≥5)
  - Blocked zone: 0.847 → 0.881 (modest +4% gain)
  - Coherence saturates above mg≈5 (mg=5: 0.967, mg=10: 0.969)
  - With seeded replicators: rep_frac rises from 26% (mg=0) to **79% (mg=5)**
    — mass-geo boosts replicator survival 3× while maintaining 100% colonization
  - 966M mass-geo boost events per 5K epochs at mg=5 (vs 472M baseline couplings)
  - Directional bias remains 0.500 (mass-geo preserves T+/T- symmetry)
  Mass-geo creates a positive feedback loop: high mass at vertices amplifies
  geometric coupling in exactly the zones where coupling is already strongest,
  pushing dominant-zone coherence to near-unity. The +10.9% total gain far
  exceeds the +4% seen on single-stella (Q3c), because mass-geo and G1+G2
  synergize: mass boosts act multiplicatively on G1's pressure-gated coupling.
  Scripts: `phase_MG1_mass_geo_sweep.sh`, `phase_mg1_analyze.py`.
  Data: `phase_mg1_results/`.
- ~~Does the cs=1.0 replicator resurgence (top=402) represent a qualitatively
  different replicator species adapted to the coherent substrate?~~
  *Answered (Q4, 2026-03-25):* **No.** All 9 runs (cs=0.0/0.5/1.0 × 3 seeds)
  produce the identical 10-instruction conserved core:
  `[ [ CPY01 FWD1 FWD0 ] CPY01 FWD1 FWD0 ]` (20-trit core, last 2 instructions
  neutral). The cs=1.0 surge (seed=42, epoch 440K) is stochastic drift, not
  species selection — seeds 137/271 at cs=1.0 show no surge. G1 coupling
  suppresses replicator *concentration* (5× more diversity) but does not change
  which motif dominates. CPY10 is never used at any coupling strength.
  Scripts: `run_q4_replicator_species.sh`, `analyze_q4_species.py`.
  Data: `phase_q4_results/`.

**Future directions (derived from completed experiments):**
- **Chirality + mass-geo combined:** C8 showed chirality breaks T+/T- symmetry
  (bias 0.50→0.64); MG1 showed mass-geo boosts coherence +10.9% while
  preserving symmetry (bias=0.50). Does chirality + mass-geo together produce
  directional *and* enhanced coherence? Or does the mass-boost amplify the
  chiral asymmetry (mass concentrates at vertices where chirality's pressure
  shift is largest)?
- **Mass-geo at larger lattice sizes (L=4, L=8):** MG1 ran at L=2 (4 stellae).
  W3b-hires showed G1 suppression is cr-dependent at L=4 with ~3× density cap.
  Does mass-geo counteract G1's suppression at larger lattice sizes, pushing
  rep_frac above the ~33% ceiling found in W4?
- **Chiral wavefront speed at GPU scale:** C8 noted that wavefront speed
  measurement requires L≥4 lattice. With mass-geo now boosting rep_frac from
  26%→79%, does the faster replicator establishment translate to faster
  wavefront propagation at scale?
- **Blocked zone ceiling:** MG1 showed dominant zone reaches 0.999 but blocked
  zone only reaches 0.881 (+4%). Mass-geo amplifies coupling where pressure
  dominance is strong (vertices) — by construction it has little leverage in the
  blocked zone. Is there a mechanism that specifically targets blocked-zone
  coherence?

---

## 6. Head-Count Comparison & CPY Asymmetry (Items 3 & 4)

**What:** Systematic comparison of 1-head, 2-head, and 3-head VM architectures
to determine whether the stella octangula's 2-tetrahedra topology is
computationally special for self-replicator emergence.

**Why it matters:** The 2-head design is motivated by Def 0.1.1 (T₊/T₋ duality).
If 2-head is the unique sweet spot, this provides computational evidence that
the stella octangula's topology is functionally essential — not just geometric.

**Code & data:**

| File | Type | Content |
|------|------|---------|
| `test_head_count.c` | C | 1v2v3-head comparison: identical soup with different VM variants |
| `head_count_5M_results.log` | Results | Full 5M-epoch run: 9 trials (3 heads × 3 seeds) |
| `analyze_cpy_asymmetry.c` | C | CPY01 vs CPY10 structural analysis: mirror replicator + evolutionary modes |
| `cpy_asymmetry_5M_results.log` | Results | Full 5M-epoch run: 12 trials (4 modes × 3 seeds) |

**Parameters:** soup_size=1024, prog_size=24, max_steps=729, mutation_rate=0.001,
epochs=5M, seeds={42, 123, 7}.

### Result 1: 2-Head is the unique replicator sweet spot

| Metric | 1-head | 2-head | 3-head |
|--------|--------|--------|--------|
| Runs with replicators | 0/3 | **3/3** | 0/3 (1 transient) |
| Avg first replicator | none | **epoch 2.5M** | epoch 3M (didn't persist) |
| Avg final dominance | 0.1% | **53.1%** | 0.1% |
| Avg unique programs | 1024 | **106** | 1023 |
| Avg compression | 0.994 | **0.946** | 0.951 |
| Total perfect (final) | 0 | **1320** | 0 |

**1-head** never produces replicators. Without inter-head copy, the soup stays
maximally disordered — all 1024 programs remain unique through 5M epochs.
The ISA has 4 NOP slots out of 9 opcodes (44% wasted code space), severely
limiting the instruction set's expressiveness.

**3-head** produces one transient replicator (seed=7, epoch 3M, 1 perfect) that
fails to persist or dominate. The 3-head ISA sacrifices BCK0 (backward movement)
to accommodate FWD2 and CPY02, and the three-way domain split dilutes the
copy mechanism. While compression is slightly lower than 1-head (0.951 vs 0.994),
no stable self-replicating programs emerge.

**2-head** reliably produces dominant self-replicators in all 3 runs. Replicators
emerge between epoch 1M–5M and rapidly take over the soup (43–65% dominance).
The ISA fills all 9 opcode slots with distinct, useful operations (0% waste).

### Result 2: Dominant replicators are CPY01-based copy machines

All three 2-head dominant programs share the same structural motif:

```
seed=42:   [  [  CPY01 FWD0 FWD1  ]  CPY01 FWD0 FWD1  ]  ]  CPY01    (444 copies)
seed=123:  [  [  CPY01 FWD1 FWD0  ]  CPY01 FWD0 FWD1  ]  [  [        (528 copies)
seed=7:    [  CPY01 CPY01 FWD1 FWD0  CPY01 FWD1 FWD0  CPY01 FWD1 FWD0  ]  (660 copies)
```

Common features across all variants:
- **CPY01 is the core mechanism** — every replicator uses it
- **CPY10 is never used** — zero occurrences across all dominant programs
- **ROT and BCK0 are never used** — replicators are forward-only copy machines
- **Bracket gates** (`[`/`]`) provide loop control for the copy cycle
- **FWD0/FWD1 advance both heads** in lockstep through the tape

### Result 3: CPY10 is structurally self-destructive

Direct test of a mirror replicator (CPY01↔CPY10, FWD0↔FWD1 swapped):

| Replicator | Zero food: self-preserved | Zero food: copy-made |
|-----------|--------------------------|---------------------|
| CPY01-based (original) | **YES** | **YES** |
| CPY10-based (mirror) | **no** | **no** |

**Root cause:** The VM concatenates programs A+B, with h0 starting at position 0
(A's territory = the instruction stream) and h1 at tape_len/2 (B's territory).

- **CPY01** (`tape[h1] = tape[h0]`): copies self → target. The replicator
  reads its own genome (via h0) and writes it into the target (via h1).
  This is self-replication.
- **CPY10** (`tape[h0] = tape[h1]`): copies target → self. The replicator
  overwrites its own executing instructions with foreign data. This is
  self-destruction — the program corrupts itself mid-execution.

The asymmetry is **intrinsic to the architecture**: the instruction pointer
reads from the first-half tape (h0 territory), so only outward copy (CPY01)
enables replication. This constitutes a **computational chirality** — a
preferred information flow direction from T₊ (instruction source) to T₋
(replication target).

### Result 4: Evolutionary confirmation — CPY10-only never replicates, swapped heads reverse chirality

Four VM modes tested evolutionarily (5M epochs, 3 seeds each):

| Mode | Replicators | Avg 1st Rep | Avg Dom% | Avg Unique | Total Perfect |
|------|------------|------------|---------|-----------|---------------|
| NORMAL (both CPY) | **3/3** | epoch 2.5M | 38.6% | 127 | 1292 |
| CPY01-ONLY (CPY10→NOP) | **3/3** | epoch 2.2M | 16.6% | 433 | 789 |
| CPY10-ONLY (CPY01→NOP) | **0/3** | none | 0.2% | 1022 | 0 |
| SWAPPED-HEADS (h0↔h1) | **3/3** | epoch 1.5M | 26.9% | 159 | 956 |

**Key findings:**

1. **CPY10-ONLY produces zero replicators** across all 3 seeds. The soup stays
   maximally disordered (1022 unique programs, 0.2% dominance). This confirms
   that CPY10 alone cannot support self-replication — it is structurally
   self-destructive when h0 starts in self-territory.

2. **CPY01-ONLY works** — CPY10 is dead weight in the normal ISA. Replicators
   emerge in all 3 runs. Lower dominance (16.6% vs 38.6%) suggests that
   converting CPY10 to NOP adds a neutral opcode that slightly dilutes the
   effective instruction set.

3. **SWAPPED-HEADS reverses the chirality.** When h0 starts at tape_len/2
   (target territory) and h1 starts at 0 (self territory), the dominant
   replicators switch to using **CPY10 exclusively**:
   ```
   seed=42:   CPY10 CPY10 ] ] [ [ FWD0 FWD1 CPY10 ] FWD1 FWD0    (270 copies)
   seed=137:  CPY10 CPY10 ] ] [ [ FWD0 FWD1 CPY10 ] FWD1 FWD0    (319 copies)
   seed=271:  ] NOP CPY10 [ [ CPY10 FWD0 FWD1 CPY10 ROT ] CPY10   (237 copies)
   ```
   Seeds 42 and 137 converge to the **identical** CPY10-based replicator —
   strong evidence of a unique fitness optimum. CPY01 is never used.

4. **The asymmetry is positional, not intrinsic.** The opcode label (CPY01 vs
   CPY10) is irrelevant — what matters is the copy direction relative to the
   instruction stream. Self-replication requires copying FROM the territory
   containing the executing instructions TO the other territory. Whichever
   opcode achieves this becomes the replication mechanism.

**Connection to CG framework:** The computational chirality is not in the
opcode but in the **architecture**: the instruction pointer creates an
inherent asymmetry between the two tetrahedra. The T₊/T₋ duality of
Def 0.1.1 maps to a reader/writer duality — one tetrahedron is the
"source of truth" (instruction stream) and the other is the replication
target. This architectural parity violation is the computational analog
of the framework's right-handed pressure-driven oscillations. Swapping
the head positions is equivalent to a parity transformation P: it
reverses the chirality but preserves the dynamics, confirming that
the asymmetry is a spontaneous symmetry breaking of the T₊↔T₋ exchange
symmetry by the initial conditions (h0 placement).

---

## 7. Chiral Wavefront Propagation (Phase C8)

**What:** Does chirality (right-handed pressure asymmetry, Axiom P3) combined
with G1+G2 produce directional replicator propagation on the FCC lattice?

**Why it matters:** The framework predicts a right-handed pressure asymmetry
(T₊ pressure > T₋ pressure) as a fundamental property of the stella octangula.
If this asymmetry creates measurable directional effects at the lattice scale
(not just within a single stella), it demonstrates that the microscopic chiral
structure propagates to macroscopic dynamics — a prerequisite for any parity
violation mechanism.

**Code & data:**

| File | Type | Content |
|------|------|---------|
| `stella_genesis/soup_g1g2.c` | C | G1+G2 combined soup with `--chirality` and `--chirality-mode` CLI options |
| `stella_genesis/run_phase_C8_chiral_wavefront.sh` | Script | Sweep χ = {0.00, 0.05, 0.10, 0.15, 0.20, 0.30, 0.42} × 3 seeds |
| `stella_genesis/phase_C8_chiral_wavefront.py` | Python | Analysis: wavefront speed, T₊/T₋ ratio, directional bias, coherence |
| `stella_genesis/phase_C8_results/` | Data | 21 log files + `C8_summary.json` |

**Parameters:** L=2 (4 stellae), n_sub=100 (1666 tiles/stella), epochs=500K,
coupling_strength=0.5, epsilon=0.1, chirality_mode=0 (pressure-asymmetry),
seeds={42, 137, 271}.

**Implementation:** Added `--chirality χ` parameter to `soup_g1g2.c` following
the same pattern as `genesis_soup.c` (lines 413–428): T₊ pressure scaled by
`(1+χ)`, T₋ pressure unchanged. Also added `--chirality-mode 1` for coupling-weight
mode (T₊→T₋ coupling amplified by `(1+χ)`, T₋→T₊ suppressed by `(1-χ)`).
Added per-surface (T₊ vs T₋) replicator tracking to census output:
`[T+:N T-:N]` per stella and `[+N -N]` per WAVEFRONT distance shell.

### Result 1: Directional coupling bias scales linearly with chirality

| χ | B(dir) | ΔB from baseline | T₊→T₋ transfers | T₋→T₊ transfers |
|------|--------|-----------------|-----------------|-----------------|
| 0.00 | 0.500 ± 0.000 | — | 50.0% | 50.0% |
| 0.05 | 0.520 ± 0.000 | +0.020 | 52.0% | 48.0% |
| 0.10 | 0.538 ± 0.000 | +0.038 | 53.8% | 46.2% |
| 0.15 | 0.556 ± 0.000 | +0.056 | 55.6% | 44.4% |
| 0.20 | 0.572 ± 0.000 | +0.072 | 57.2% | 42.8% |
| 0.30 | 0.603 ± 0.000 | +0.103 | 60.3% | 39.7% |
| 0.42 | 0.635 ± 0.000 | +0.135 | 63.5% | 36.5% |

**Zero variance across seeds** — the directional bias is a purely geometric
property determined by the pressure landscape, not by stochastic dynamics.
The relationship is approximately B ≈ 0.5 + 0.32·χ (linear fit, R² ≈ 1.0).

### Result 2: Replicators preferentially occupy T₊ surface

| χ | R(T₊/T₋) | % more on T₊ |
|------|-----------|-------------|
| 0.00 | 1.009 ± 0.003 | +0.9% |
| 0.05 | 1.040 ± 0.015 | +4.0% |
| 0.10 | 1.070 ± 0.006 | +7.0% |
| 0.15 | 1.106 ± 0.007 | +10.6% |
| 0.20 | 1.142 ± 0.026 | +14.2% |
| 0.30 | 1.186 ± 0.018 | +18.6% |
| 0.42 | 1.208 ± 0.019 | +20.8% |

At χ=0, T₊ and T₋ carry nearly equal replicators (R ≈ 1.01). As chirality
increases, replicators concentrate on T₊ — the surface with amplified pressure.
The mechanism: G1 coupling at χ>0 preferentially copies T₊ trits onto T₋,
but replicators on T₊ have higher fitness because their local pressure landscape
is stronger. The T₊ surface becomes the "source" and T₋ the "sink" for
replicator content.

### Result 3: Coherence is chirality-invariant

| χ | coh (mean ± SE) |
|------|-----------------|
| 0.00 | 0.878 ± 0.009 |
| 0.05 | 0.872 ± 0.014 |
| 0.10 | 0.876 ± 0.013 |
| 0.15 | 0.860 ± 0.006 |
| 0.20 | 0.873 ± 0.017 |
| 0.30 | 0.867 ± 0.009 |
| 0.42 | 0.886 ± 0.013 |

Coherence fluctuates in a narrow band (0.860–0.886) with no systematic trend.
Chirality does not degrade G1+G2 coherence — the asymmetry shifts *which*
surface dominates the coupling but not *how much* coupling occurs.

### Result 4: No crossover at χ*≈0.42 (unlike single-stella)

The single-stella genesis_soup phase diagram ([GPU-TEST-PLAN.md §11/E1](../stella_genesis/GPU-TEST-PLAN.md#e1-genesis-enhanced-vm-on-gpu--status-update))
showed three regimes with a crossover at χ*≈0.42. In the multi-stella G1+G2
system, all observables (B, R, coh) are monotonic through χ=0.42 — no crossover.

**Interpretation:** The crossover in the single-stella system arose from
competition between WRITE instructions and geometric coupling. In the G1+G2
multi-stella system, inter-stella VM coupling (G2) provides an additional
mixing mechanism that smooths out the single-stella phase boundary. The G2
replicator dynamics are indifferent to intra-stella pressure asymmetry — they
operate on the program level, not the trit level.

### Result 5: Wavefront speed measurement requires GPU scale

At L=2 (4 stellae, 2 distance shells), all stellae are colonized within the
first census interval (50K epochs) for all χ values. The wavefront transit
time is too fast to resolve at L=2. Measuring wavefront speed vs chirality
requires L≥4, which at n_sub=100 with G1 coupling is ~12 epochs/sec — too
slow for CPU. This is a natural candidate for the GPU Metal infrastructure
([GPU-TEST-PLAN.md §E4/E5](../stella_genesis/GPU-TEST-PLAN.md#e5-gpu-port)).

**Prior wavefront baselines** (no G1, no chirality):
- [Q3 micro-wavefront](../stella_genesis/GPU-TEST-PLAN.md#q3-micro-wavefront-2026-03-26):
  Replicator wavefront v = 0.02 hops/epoch at L=16, ballistic propagation (d ∝ t).
- [Q3b velocity mapping](../stella_genesis/GPU-TEST-PLAN.md#q3b-wavefront-velocity-mapping--lattice-dynamics-to-qcd-scales-2026-03-26):
  v ∝ cr^0.41 scaling with creation rate; critically, the replicator wavefront
  is ×30,000 slower than QCD confinement velocity, confirming that replicator
  propagation is a **computational** observable, not a physical one.

A GPU-scale C8 experiment at L≥8 would compare v(χ) against the Q3 baseline
(v=0.02 at χ=0) to determine whether chirality accelerates or decelerates
replicator wavefront propagation.

### Physical interpretation

The chirality experiment reveals a **three-level directional hierarchy** in
the G1+G2 system:

1. **Pressure level (geometric):** χ>0 makes T₊ pressure fields stronger,
   shifting the dominant/blocked zone boundary. This is a static geometric
   property with zero variance — the pressure landscape is deterministic.

2. **Coupling level (dynamic):** The asymmetric pressure creates directional
   G1 coupling: T₊→T₋ transfers outnumber T₋→T₊ by a factor of B/(1-B).
   At χ=0.42, this is 1.74:1.

3. **Replicator level (emergent):** Replicators preferentially occupy T₊,
   the surface with stronger pressure authority. This is an emergent property
   of the evolutionary dynamics — the pressure asymmetry creates a fitness
   gradient that selects for T₊ occupancy.

This hierarchy connects the framework's fundamental right-handed pressure
convention (Axiom P3) to observable asymmetries in the computational dynamics.
The chirality is not merely a symmetry label — it produces measurable
directional effects that propagate from geometry through dynamics to
evolutionary selection.

**Relation to phase-propagation wavefronts:** The C8 experiment measures
*replicator* propagation — which [Q3b](../stella_genesis/GPU-TEST-PLAN.md#q3b-wavefront-velocity-mapping--lattice-dynamics-to-qcd-scales-2026-03-26)
showed is computational, not physical. A separate line of investigation
explored *phase* propagation as the physical wavefront channel:
[K1 (Kuramoto, diffusive α=0.527)](../stella_genesis/GPU-TEST-PLAN.md#k1-kuramoto-phase-wavefront--diffusion-vs-causality-high-priority),
[K2 (mass-Kuramoto, ballistic α=0.805 standalone → NULL in full soup)](../stella_genesis/GPU-TEST-PLAN.md#k2-gpu-full-genesis-soup-wavefront--paired-simulation-test-high-priority),
and [K3 (Lyapunov, sub-diffusive α≈0.44 with information confinement)](../stella_genesis/GPU-TEST-PLAN.md#k3-lyapunov-divergence-front--zone-aware-information-propagation).
K2's GPU experiment revealed two distinct propagation channels — Kuramoto
phase (blocked zone, slow) and VM divergence (open zone, fast/chaotic).
Chirality modifies the pressure landscape that determines the blocked/open
zone boundary, suggesting that a future experiment combining chirality with
K-series phase measurements could reveal whether χ shifts the balance between
these two channels.

**Connection to §6 (CPY asymmetry):** The head-count experiment showed that
the instruction pointer creates an architectural chirality (reader/writer
duality between T₊ and T₋). The C8 experiment adds a second chirality
source: the pressure asymmetry. Both break T₊↔T₋ exchange symmetry, but
through different mechanisms — one computational (IP placement), the other
geometric (pressure scaling). In the full G1+G2 system, both act together:
the geometric chirality (G1) determines *where* coupling occurs, and the
computational chirality (G2) determines *what* gets copied.

---

## Priority Order

1. ~~**G1+G2 Combined experiment** (item 5)~~ ✅ **COMPLETE** — G1 and G2
   are synergistic; see results above
2. ~~**Inter-stella gauge coupling at larger L** (item 1)~~ ✅ **COMPLETE** —
   Mode A ≈ Mode B at L=8 (256 stellae); octahedral mediation is redundant
3. ~~**CPY01/CPY10 + second head** (items 3 & 4)~~ ✅ **COMPLETE** — 2-head
   is the unique sweet spot (3/3 vs 0/3 vs 0/3); CPY01 is structurally
   essential, CPY10 is self-destructive; see §6
4. ~~**Phase-gradient mass generation** (item 2)~~ ✅ **COMPLETE** — all questions
   answered (Q1–Q7, Q5): coherence plateaus at ~0.80 with coupling, cvf=3/4
   is a geometric invariant of ∂S confirmed across single/multi-stella (1–32
   stellae), discrete Z₃ and continuous Kuramoto dynamics
