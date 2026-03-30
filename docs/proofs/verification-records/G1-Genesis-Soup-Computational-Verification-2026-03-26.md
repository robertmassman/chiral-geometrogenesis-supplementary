# G1 Genesis Soup — Computational Verification Record

**Date:** 2026-03-26
**Source:** `stella_genesis/RESULTS-Phase1.md` (2539 lines)
**Code:** `stella_genesis/genesis_soup.c` + Metal GPU port (`genesis_soup_metal.m`)
**Branch:** `autoinvestigate/G1-L1-coherence-fixes`

---

## 1. Purpose

This record documents the computational verification of G1 (Paper 1) foundations through the `genesis_soup.c` simulation — a Z₃ trit-based model on the stella octangula that tests whether Paper 2 dynamics (inter-component coupling, arrow of time, self-replication) emerge from Paper 1 geometry alone.

The simulation maps directly to the G1 proof chain:

| Simulation Component | G1 Source | Implementation |
|:---------------------|:----------|:---------------|
| Stella geometry (T₊/T₋) | Def 0.1.1 | 8 vertices, triangulated faces, n_sub parameter |
| Z₃ trit states (0,1,2) | Def 0.1.2 | Three color phases: 0, 2π/3, 4π/3 |
| Pressure fields P(x,v) | Def 0.1.3 | 1/(|x−v|² + ε²), dual-mesh evaluation |
| Right-handed asymmetry | Axiom P3 | P₊ scaled by (1+χ) |
| GenesisVM (9 opcodes) | Def 0.1.2 + 0.1.3 | Turing-complete Z₃ machine |
| Inter-tetrahedron coupling | Thm 0.2.1 | Pressure-gated bidirectional transfer |
| Phase-lock attractor | Thm 2.2.1 | P_ratio-gated neighbor majority vote / Kuramoto |
| Energy functional | Thm 0.2.4 | Paired flips + mutation bias toward |a_R|=|a_G|=|a_B| |

---

## 2. Verification Results

### 2.1 Pass/Fail Summary

| # | Claim | Proof Verified | Status | Key Evidence |
|:-:|:------|:---------------|:------:|:-------------|
| 1 | Inter-surface coherence emerges from geometry | Thm 0.2.1, Def 0.1.3 | **PASS** | corr = 0.724 vs 0.333 random (2.17×) |
| 2 | Geometric coupling is bidirectionally balanced | Def 0.1.1 | **PASS** | T₊→T₋ = 50.0%, T₋→T₊ = 50.0% (dual-mesh) |
| 3 | Local pattern replication emerges | Thm 0.2.1 | **PASS** | Local replication density 0.716 vs 0.333 random |
| 4 | Chirality produces directional bias | Axiom P3, Prop 0.0.17c | **PASS** | χ=0.1→0.538, χ=0.5→0.653, χ=1.0→0.742 |
| 5 | Pressure asymmetry is the correct chirality mechanism | Axiom P3 | **PASS** | Increases both bias AND coherence (unlike coupling weights) |
| 6 | Enhanced VM (SENSE/COUPLE) improves metrics | Def 0.1.3 | **PASS** | corr +10.1%, auto +17.1% over classic mode |
| 7 | Geometric coupling >> CPY01/CPY10 | Def 0.1.3 vs Thm 0.2.1 | **PASS** | 0.749–0.794 vs 0.389 (7–8× stronger) |
| 8 | WRITE instruction outperforms COUPLE | Def 0.1.3 | **PASS** | +0.088 corr, 77–78% success rate |
| 9 | No late-time phase transitions | — | **PASS** | Stable from 5M→50M epochs (Δcorr = +0.002) |
| 10 | Continuum coherence converges | — | **PASS** | Richardson extrapolation: 0.933 ± 0.005 |
| 11 | Energy functional drives color balance | Thm 0.2.4 | **PASS** | |χ|² reduced 66% (0.232→0.079) |
| 12 | Arrow of time emerges from symmetric G1 | — | **FAIL** | dir_bias = 0.500 ± 0.000 (exact symmetry) |
| 13 | Spontaneous symmetry breaking | — | **FAIL** | 5 seeds × 5M epochs: exact 50/50 |
| 14 | ~0.86 ceiling is mutation-rate artifact | — | **FAIL** | μ-invariant; intrinsic to geometry |

### 2.2 Quantitative Results (Dual-Mesh, Mode 0, 500K epochs)

| Metric | Value | Random Baseline | Ratio |
|:-------|:-----:|:------:|:-----:|
| T₊/T₋ correlation | 0.724 | 0.333 | 2.17× |
| H(T₊) entropy | 1.477 | 1.585 | 0.93× |
| H(T₋) entropy | 1.466 | 1.585 | 0.92× |
| Spatial autocorrelation (T₊) | 0.386 | 0.333 | 1.16× |
| Local replication | 0.716 | 0.333 | 2.15× |
| Directional bias | 0.500 | — | Symmetric |

### 2.3 Definitive G1 Ceiling (§8)

With all G1 mechanisms active (WRITE + χ=0.15 + Kuramoto phase-lock + per-color pressure):

| Metric | n_sub=16 (5-seed mean) | Continuum estimate |
|:-------|:----------------------:|:------------------:|
| Correlation | 0.863 ± 0.010 | 0.933 ± 0.005 |
| Entropy | 1.453 ± 0.025 | — |
| Spatial autocorrelation | 0.460–0.471 | — |
| Local replication | 0.860 ± 0.016 | — |
| WRITE success rate | 84.7% | — |

This ceiling is a true dynamical fixed point (reached by ~5M epochs, stable to 50M) and is intrinsic to geometric coupling — not a mutation-rate artifact (§3).

---

## 3. Negative Results (Documented Honestly)

### 3.1 No Arrow of Time from Symmetric Geometry

The stella octangula's inversion symmetry (T₊ ↔ T₋) ensures exactly equal bidirectional coupling when pressure functions are symmetric. Directional bias = 0.500 ± 0.000 across all seeds and timescales. **Chirality must be explicitly introduced** (Axiom P3) — it does not emerge.

### 3.2 Mesh Placement Artifact (Methodological Lesson)

The previously reported 92.1% directional bias was entirely a single-mesh sampling artifact. Swapping mesh origin flipped the bias to 7.9%. The dual-mesh architecture (evaluating pressure at both T₊ and T₋ positions independently) eliminates this artifact.

### 3.3 No Sharp Phase Transition

Coherence onset is a smooth crossover, not a sharp phase transition. No critical coupling strength threshold exists — even cs=0.01 produces measurable correlation above random.

### 3.4 Color Balance vs Correlation Tension

With the energy functional active (Thm 0.2.4), achieving color balance |a_R| ≈ |a_G| ≈ |a_B| costs 5.6% in T₊–T₋ correlation. Resolving this tension requires mechanisms beyond G1: inter-stella gauge coupling (Prop 2.5.2b) and phase-gradient mass generation (Thm 3.1.1).

---

## 4. Proofs Verified

This verification record provides computational evidence for the following proofs:

| Proof | What Is Verified | Evidence |
|:------|:-----------------|:---------|
| **Def 0.1.1** (Stella Boundary Topology) | Dual-tetrahedron geometry produces balanced bidirectional coupling | §2.2: T₊→T₋ = T₋→T₊ = 50.0% |
| **Def 0.1.2** (Three Color Fields) | Z₃ trit states implement color field dynamics; all 9 opcodes grounded in G1 | §Phase 4: 100% opcode utilization |
| **Def 0.1.3** (Pressure Functions) | Pressure-mediated coupling is the primary coherence mechanism | §2.1 #1,6,7: geometric coupling 7–8× stronger than CPY01 |
| **Axiom P3** (Right-Handed Pressure) | Chirality via P₊→(1+χ)P₊ produces both directional bias and enhanced coherence | §2.1 #4,5: continuous onset, pressure asymmetry superior |
| **Thm 0.2.1** (Total Field Superposition) | Inter-tetrahedron synchronization emerges without postulating CPY01 | §2.1 #1: corr = 0.724 from geometry alone |
| **Thm 0.2.4** (Pre-Geometric Energy) | Energy functional drives color equalization as predicted | §2.1 #11: |χ|² reduced 66% |
| **Thm 2.2.1** (Phase-Lock Attractor) | P_ratio-gated majority vote + Kuramoto dynamics produce intra-tetrahedron coherence | §7c,7d: 41%→49% gap closure |
| **Prop 0.0.17c** (KL Divergence Asymmetry) | Arrow of time requires explicit chirality, not spontaneous breaking | §3.1: exact 50/50 without chirality |

---

## 5. Advanced Results (§1–§8, §H15)

### 5.1 Chirality × VM Phase Diagram (§1)

Three regimes with crossover at χ* ≈ 0.42:
- Low χ: Classic coupling optimal
- Intermediate χ: Enhanced VM competitive
- High χ: WRITE mode dominant (wins 44% of parameter grid)

χ* correlation with cs: r = −0.66 (stronger coupling → lower crossover).

### 5.2 COUPLE Site Selection Geography (§2)

COUPLE site selection is NOT evolved — it's an instantaneous mechanical consequence of SENSE. Vertex/midplane ratio = 1.40 ± 0.03 (constant 0–5M epochs). Antipodal opposition network mirrors stella topology. Chi-squared test: χ² = 253K (strongly non-uniform, p ≈ 0).

### 5.3 Mutation Rate Independence (§3)

The ~0.86 ceiling (n_sub=16) is intrinsic to geometry, not a mutation artifact:
- μ = 0.0001–0.01: mean correlation unchanged
- μ = 0.001 optimal (same mean as 0.0001, 3× lower variance)
- No phase transition at any mutation rate

### 5.4 Continuum Convergence (§7)

Two distinct length scales resolved:
- h_pressure ≈ 0.12 (resolved by n_sub ≈ 24)
- h_coherence ≈ 0.02 (resolved by n_sub ≈ 96–128)

| n_sub | Sites | Correlation |
|:-----:|:-----:|:-----------:|
| 8 | ~18 | 0.828 |
| 16 | ~66 | 0.863 |
| 32 | ~258 | 0.903 |
| 64 | ~1,026 | 0.923 |
| 96 | ~2,306 | 0.929 |
| 128 | ~4,098 | 0.930 |
| ∞ | — | **0.933 ± 0.005** |

Uniform mesh (α=1.0) is optimal — vertex concentration degrades performance.

### 5.5 Coherence Gap Closure (§7b–§7d)

| Mechanism | Gap Closure | Blocked Zone Improvement |
|:----------|:----------:|:------------------------:|
| Per-color pressure (§7b) | +0.5–1% | +20.2pp deep-blocked zone |
| Gated phase-lock (§7c) | +3.2% | 48%→88% match rate |
| Full Kuramoto (§7d) | +8.2pp total | 99.6% deep-blocked zone |

### 5.6 Dominance Ratio (§5)

The 66.1% observed dominance converges to 3/4 = 75.0% in the continuum limit. The medial triangle occupies 1/4 of each face (pressure-balanced zone); three corner regions occupy 3/4 (one tetrahedron dominant).

---

## 6. Relationship to Existing Audits

This verification record complements but does not duplicate existing audit work:

| Document | Scope | Relationship |
|:---------|:------|:-------------|
| [G1-Validity-Audit-Final-Synthesis.md](../reviews/G1/G1-Validity-Audit-Final-Synthesis.md) | Mathematical validity of G1 proof chain | This record provides *computational* evidence for the same chain |
| [G1-Geometric-Foundation-Coherence-Audit.md](../reviews/G1/G1-Geometric-Foundation-Coherence-Audit.md) | Internal consistency (87/87) | This record tests whether consistent definitions *produce physical behavior* |
| [Proposition-0.0.XXe-Phase1-2D-Soup-Results.md](Proposition-0.0.XXe-Phase1-2D-Soup-Results.md) | 2D lifting for self-replication | This record covers the broader G1 dynamics program |
| [Prop 0.0.3a](../foundations/Proposition-0.0.3a-Computational-Crystallization-Stella-Octangula.md) (Crystallization) | Z₃→stella emergence | Crystallization uses same `genesis_soup.c` codebase |
| [Prop 0.0.XXg](../foundations/Proposition-0.0.XXg-Q3-Spectral-Structure-Stella-Octangula.md) (Spectral Encoding) | {2,3} eigenvalue ratios | H-series experiments use same stella geometry |

---

## 7. Reproducibility

All results are reproducible from source:

| Experiment | Executable | Build | Key Parameters |
|:-----------|:-----------|:------|:---------------|
| Phases 1–5 | `genesis_soup` | `cc -O3 -o genesis_soup genesis_soup.c -lm` | See CLI in RESULTS-Phase1.md §Simulation Architecture |
| §1 Phase diagram | `run_chirality_phase_diagram.py` | Python 3 | χ × cs grid |
| §2 COUPLE geography | `genesis_soup` | As above | COUPLE analysis mode |
| §3 Mutation sweep | `genesis_soup` | As above | μ = 0.0001–0.01 |
| §6 Long-timescale | `genesis_soup` | As above | 50M epochs, 5 seeds |
| §7 Mesh convergence | `genesis_soup` | As above | n_sub = 8–128 |
| §7d Kuramoto | `genesis_soup` | As above | K = 1.0 |
| §H15 Energy functional | `phase_h15_energy_functional` | `cc -O3 -o phase_h15_energy_functional phase_h15_energy_functional.c -lm` | λ = 0.0–5.0 |
| GPU port | `genesis_soup_metal` | Metal/Objective-C | Same parameters |

All source files are in `stella_genesis/`.

---

*Source data: [RESULTS-Phase1.md](../../stella_genesis/RESULTS-Phase1.md)*
*Simulation code: [genesis_soup.c](../../stella_genesis/genesis_soup.c)*
