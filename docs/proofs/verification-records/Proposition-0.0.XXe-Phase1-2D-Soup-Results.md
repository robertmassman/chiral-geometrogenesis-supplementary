# Proposition 0.0.XXe Phase 1: 2D Soup on Triangulated dS — Results

> **⚠️ CORRECTION NOTE (2026-03-13):** The ~55% equilibrium density values reported throughout this document were artifacts of a BFS Voronoi tiling bug in `soup_multi_stella.c` that left 16.4% of tiles permanently undersized. After patching with greedy-fill tiling and re-running all configurations (see `stella_lang/RERUN_PLAN.md`), the corrected equilibrium density is **~86–87%** across all cross-rates and lattice sizes. The qualitative findings (replicator emergence, propagation dynamics, wavefront structure) remain valid; only the absolute density values are affected. See WORKPLAN Q13 for full investigation.

## Date: 2026-03-06

## Overview

Phase 1 of the XXe workplan lifts the 1D Stella Soup (Prop 0.0.XXd) to the actual geometry of dS = T+ u T- (two interpenetrating tetrahedra). We tested whether self-replicating patterns emerge when Z_3 values live on triangulated tetrahedral surfaces.

Two interaction models were tested:
1. **Patch mode** (`soup_2d.c`): Programs are BFS-ordered patches on a shared surface. Patches overlap.
2. **Tile mode** (`soup_2d_tile.c`): Surface partitioned into non-overlapping Voronoi-like tiles. Each tile is an independent program.

**Main result: Nontrivial self-replicators emerge on the 2D stella geometry** when population size is sufficient (>= ~1600 tiles). This confirms that the Z_3 computational framework supports self-replication on the physical dS topology, not just in abstract 1D.

## Geometry (Tasks 1.1-1.2)

### Mesh Construction

Each tetrahedron surface is subdivided with `n_sub` divisions per edge. Vertices at shared edges/corners are merged. The mesh builder uses O(n^2) direct-index construction with canonical vertex numbering (corners, edge interiors, face interiors).

| n_sub | Sites per tetra | Total sites (dS) | Formula |
|-------|----------------|-------------------|---------|
| 8 | 130 | 260 | 2n^2 + 2 |
| 16 | 514 | 1028 | |
| 32 | 2,050 | 4,100 | |
| 100 | 20,002 | 40,004 | |
| 157 | 49,300 | 98,600 | |

Mesh neighbors: min=3 (tetrahedron corners), max=6 (interior), avg~6.0 (triangular lattice).

### FCC Lattice Grounding (Theorem 0.0.6)

The stella octangula sits at each vertex of the FCC lattice:
- FCC lattice: {(n1,n2,n3) in Z^3 : n1+n2+n3 = 0 mod 2}
- T+ vertices: even-parity cube corners (s1*s2*s3 = +1)
  - (1,1,1), (1,-1,-1), (-1,1,-1), (-1,-1,1)
- T- vertices: odd-parity cube corners (s1*s2*s3 = -1)
  - (-1,-1,-1), (-1,1,1), (1,-1,1), (1,1,-1)

The 12 FCC nearest neighbors at (+-1,+-1,0) and permutations form 8 equilateral triangles — these are the outer faces of the 8 tetrahedra meeting at each FCC vertex (which compose the stella).

### VM (Task 1.2)

The 1D VM is reused unchanged. A 2D patch/tile of `prog_size` Z_3 sites is linearized via BFS order, producing a 1D tape compatible with the original instruction set: NOP, ROT (Def 0.1.2), FWD0, BCK0, FWD1 (Def 0.1.1), OPEN/CLOSE (Prop 0.0.17h), CPY+/CPY- (Thm 0.2.1).

### Replication Definition (Task 1.3)

Same as 1D: a patch/tile P is a self-replicator if P concatenated with zeros, after VM execution, produces (P, P). Trivial replicators (all-same-trit) are filtered out.

---

## Patch Mode Results (Task 1.4)

### Parameter Sweep

| Run | n_sub | prog_size | mutation | locality | epochs | final H(trit) | partials/200 | perfect? |
|-----|-------|-----------|----------|----------|--------|---------------|-------------|----------|
| Main local | 16 | 24 | 0.001 | 3 hops | 5M | 0.93 | 41 | No |
| Main global | 16 | 24 | 0.001 | global | 5M | 1.55 | 76 | No |
| Small patches | 16 | 12 | 0.001 | 3 hops | 10M | 1.55 | 85@6M | No |
| Large patches | 16 | 48 | 0.001 | 3 hops | 2M | collapsing | 44@1M | No |
| High mutation | 16 | 24 | 0.003 | 3 hops | 2M | ~1.3 | 39@1M | No |
| Low mutation | 16 | 24 | 0.0005 | 3 hops | ~1M | 0.18 | trivial only | No |
| Wide locality | 16 | 24 | 0.001 | 6 hops | 2M | ~1.1 | 59@1M | No |
| Large mesh | 32 | 24 | 0.001 | 3 hops | 2M | ~1.3 | 53@1M | No |
| Medium mesh | 24 | 24 | 0.001 | 3 hops | 5M | ~1.4 | 59@1M | No |
| Small+global | 8 | 12 | 0.001 | global | 2M | 0.00 | collapsed | No |

### Key Finding: Monoculture Attractor

The patch-based model suffers from a **monoculture attractor** absent in the 1D soup. Because patches overlap on a shared surface, a dominant trit value propagates through every interaction, eventually collapsing the surface to a uniform state.

**Critical parameter: patch/surface ratio**

| prog_size / n_sites | Entropy behavior | Outcome |
|---------------------|-----------------|---------|
| < 3% (ps=12, n=514) | Stable ~1.55 | Healthy, many partials |
| ~5% (ps=24, n=514) | Fluctuating 1.1-1.5 | Marginal |
| ~9% (ps=48, n=514) | Dropping | Collapsing |
| ~9% (ps=12, n=130) | Collapsed to 0 | Dead |

### Why 2D Patches Differ from 1D Programs

In the 1D soup, programs are **independent entities** — modifying program A does not affect program B. In the 2D patch model, patches **overlap on a shared surface** — modifying one patch writes to sites that belong to neighboring patches. This creates:

1. **Spatial coupling**: Every interaction affects neighbors
2. **Positive feedback**: Dominant values spread faster than rare values
3. **Noise requirement**: Mutations must counteract the coupling, serving a different role than in 1D

---

## Tile Mode Results (Task 1.4, continued)

The tile mode partitions the surface into non-overlapping regions, restoring program independence while preserving 2D geometry.

### Small-Population Results (no replicators)

| Run | n_sub | tiles | pairing | epochs | final H | unique | partials/200 | perfect? |
|-----|-------|-------|---------|--------|---------|--------|-------------|----------|
| n_sub=16, local | 16 | 42 | local | 5M | 1.565 | 42/42 | 91-106 | No |
| n_sub=32, local | 32 | 170 | local | 5M | 1.537 | 169/170 | 77-105 | No |
| n_sub=32, global | 32 | 170 | global | 5M | 1.566 | 170/170 | 80-105 | No |

With 42-170 tiles, no perfect replicators emerged despite healthy entropy and ~50% partial replicator rates. All programs remained nearly unique (Top=1-4), indicating insufficient selection pressure.

### Large-Population Results: SELF-REPLICATORS EMERGE

The mesh builder was rewritten with O(n^2) direct-index construction (canonical vertex numbering for corners, edges, face interiors), enabling n_sub up to ~180.

#### n100 local (1,666 tiles) — Replicators at epoch 800K

| Epoch | Unique | Top copies | Nontrivial replicators | H(trit) |
|-------|--------|-----------|----------------------|---------|
| 790K | 1,641 | 8 | 0 | 1.562 |
| 800K | 698 | 130 | 99 | 1.582 |
| 900K | 568 | 218 | 116 | 1.582 |
| 1M | 625 | 230 | 92 | 1.581 |
| 2M | 502 | 349 | 122 | 1.580 |
| 3M | 559 | 178 | 120 | 1.581 |
| 5M | 532 | 221 | 129 | 1.583 |
| 7M | 497 | 256 | 135 | 1.582 |
| 10M | 698 | 187 | 115 | 1.582 |

Replicators sustained for **9.2M epochs** after emergence (entire remaining run). Nontrivial count fluctuates 91-135 (mean ~113). Dominant species oscillates 130-418 copies (mean ~250, or ~15% of population). Entropy stabilized at ~1.58 (higher than pre-emergence ~1.56).

**Top 5 programs at epoch 10M:**
```
count=187 ( 11.2%): [ [ CPY+ FWD1 FWD0 ] CPY+ FWD1 FWD0 ] ] FWD1
count=126 (  7.6%): [ [ CPY+ FWD1 FWD0 ] CPY+ FWD1 FWD0 ] ] CPY-
count=115 (  6.9%): [ [ CPY+ FWD1 FWD0 ] CPY+ FWD1 FWD0 ] ] [
count= 60 (  3.6%): [ [ CPY+ FWD1 FWD0 ] CPY+ FWD1 FWD0 ] ] NOP
count= 58 (  3.5%): [ [ CPY+ FWD1 FWD0 ] CPY+ FWD1 FWD0 ] ] BCK0
```

Total nontrivial replicators detected across all checks: **10,450**

#### n100 global (1,666 tiles) — Replicators at epoch 3.9M

| Epoch | Unique | Top copies | Nontrivial replicators | H(trit) |
|-------|--------|-----------|----------------------|---------|
| 3.8M | 1,643 | 6 | 0 | 1.565 |
| 3.9M | 822 | 287 | 60 | 1.562 |
| 4M | 845 | 335 | 59 | 1.551 |
| 5M | 1,030 | 256 | 32 | 1.551 |
| 6M | 790 | 408 | 61 | 1.573 |
| 7M | 1,180 | 219 | 33 | 1.551 |
| 8M | 889 | 330 | 48 | 1.552 |
| 9M | 955 | 297 | 43 | 1.550 |
| 10M | 986 | 321 | 52 | 1.563 |

Global pairing found replicators much later (3.9M vs 0.8M), close to the 1D soup timescale (~3.5M). Fewer nontrivial replicators (32-73 vs ~113), but dynamics are sustained over 6.1M epochs. Entropy is lower (~1.55 vs ~1.58), and more unique programs remain (~900 vs ~600).

**Top 5 programs at epoch 10M:**
```
count=321 ( 19.3%): ] ] [ [ CPY+ FWD0 FWD1 CPY+ CPY- ] FWD1 FWD0
count= 50 (  3.0%): CPY+ ] [ [ CPY+ FWD0 FWD1 CPY+ CPY- ] FWD1 FWD0
count= 21 (  1.3%): ] ] [ [ NOP NOP NOP NOP NOP NOP NOP NOP
count= 21 (  1.3%): CPY- NOP [ [ CPY+ FWD0 FWD1 CPY+ CPY- ] FWD1 FWD0
count= 19 (  1.1%): ] ] [ [ CPY+ FWD0 FWD1 CPY+ CPY- ] BCK0 NOP
```

Total nontrivial replicators detected across all checks: **2,961**

#### n157 local (4,108 tiles) — Replicators at epoch 9.65M

| Epoch | Unique | Top copies | Nontrivial replicators | H(trit) |
|-------|--------|-----------|----------------------|---------|
| 5M | 4,028 | 14 | 0 | 1.556 |
| 7M | 3,998 | 18 | 0 | 1.558 |
| 9M | 4,012 | 16 | 0 | 1.560 |
| 9.6M | 4,040 | 12 | 0 | 1.563 |
| 9.64M | 3,972 | 27 | — | 1.560 |
| 9.65M | 2,244 | 825 | — | 1.564 |
| 9.66M | 1,140 | 513 | — | 1.582 |
| 9.7M | 1,113 | 554 | 121 | 1.582 |
| 9.8M | 1,143 | 613 | 120 | 1.582 |
| 9.9M | 1,110 | 466 | 112 | 1.581 |
| 10M | 1,187 | 490 | 119 | 1.582 |

The n157 run demonstrates the same explosive emergence dynamics at larger scale: Top count jumped from 27 to 825 in a single 10K-epoch interval (~9.645M). The larger population (4,108 tiles vs 1,666) required significantly more search time (9.65M vs 0.8M epochs) to find a replicator, but once found, takeover was equally explosive.

**Top 5 programs at epoch 10M:**
```
count=490 ( 11.9%): [ [ CPY+ FWD0 FWD1 ] CPY+ FWD0 FWD1 ] ] FWD1
count=332 (  8.1%): [ [ CPY+ FWD0 FWD1 ] CPY+ FWD0 FWD1 ] ] BCK0
count=236 (  5.7%): [ [ CPY+ FWD0 FWD1 ] CPY+ FWD0 FWD1 ] BCK0 FWD1
count=234 (  5.7%): [ [ CPY+ FWD0 FWD1 ] CPY+ FWD0 FWD1 ] ] CPY-
count=202 (  4.9%): [ [ CPY+ FWD0 FWD1 ] CPY+ FWD0 FWD1 ] ] [
```

Total nontrivial replicators detected across all checks: **472** (only 4 checks post-emergence)

---

## Replicator Program Analysis

### Universal Replicator Core

All three runs converge on the same replicator structure, a **10-instruction core with a 1-2 instruction tail**:

```
[ [ CPY+ FWD{0,1} FWD{1,0} ] CPY+ FWD{0,1} FWD{1,0} ] ] {tail}
```

The core structure is: `[ [ CPY+ FWD FWD ] CPY+ FWD FWD ] ]`, which uses:
- **Brackets** `[ ]` for loop/copy control (Prop 0.0.17h)
- **CPY+** to copy the current trit forward (Thm 0.2.1)
- **FWD0/FWD1** to advance the tape head (Def 0.1.1)

The tail instruction varies freely (FWD1, CPY-, [, NOP, BCK0), creating a **quasispecies cloud** — a family of replicator variants that differ only in the functionally irrelevant tail position.

### Quasispecies Structure

| Run | Core | Tail variants in top 5 | Total species |
|-----|------|----------------------|---------------|
| n100 local | `CPY+ FWD1 FWD0` | FWD1, CPY-, [, NOP, BCK0 | 5+ |
| n100 global | `CPY+ FWD0 FWD1 CPY+ CPY-` | (different structure) | 3+ |
| n157 local | `CPY+ FWD0 FWD1` | FWD1, BCK0, (BCK0 FWD1), CPY-, [ | 5+ |

The n100 global run found a slightly different replicator structure (10 active instructions vs 8+2 tail), suggesting there are multiple solutions to the self-replication problem in the Z_3 VM. The local-pairing runs found the same core (with FWD order swapped: FWD1 FWD0 vs FWD0 FWD1), confirming the universality of the replicator mechanism.

### Comparison with 1D Soup Replicators

The 2D replicators are structurally identical to the 1D soup replicators — the same `[ [ CPY+ FWD FWD ] ... ]` pattern. This confirms that the replication mechanism is **VM-intrinsic, not geometry-dependent**. The 2D stella geometry affects *when* and *how fast* replicators emerge, but not *what* they look like.

---

## Key Findings (Final)

1. **Population size is the critical parameter**: 42-170 tiles insufficient; >= 1,666 tiles produces replicators. The minimum population for complex self-replicators to emerge through random variation is ~1,000-2,000 independent programs.

2. **Emergence is sudden and explosive**: From zero to ~100-120 perfect replicators in one 10K-epoch interval. The replicator immediately dominates ~12-20% of the population. This is the same phase-transition-like takeover dynamics seen in the 1D soup.

3. **Entropy INCREASES post-emergence**: From ~1.56 to ~1.58 (closer to max 1.585). Replicator variants create MORE diversity, not less — the quasispecies cloud explores nearby sequence space.

4. **Oscillatory population dynamics**: Dominant copy count fluctuates between ~130 and ~825, indicating competition among replicator variants. Classic evolutionary quasispecies behavior.

5. **Local pairing accelerates emergence**: n100 local found replicators at 800K vs n100 global at 3.9M (~5x faster). Local interactions create spatial niches where proto-replicators can build up before being disrupted.

6. **Larger populations take longer to find replicators**: n157 local (4,108 tiles) found replicators at 9.65M vs n100 local (1,666 tiles) at 800K. The larger search space requires more exploration time. This is consistent with the replicator being a rare sequence that must be found by random mutation.

7. **Replicator ecosystem is self-sustaining**: Once emerged, replicators persist indefinitely. n100 local sustained replicators for 9.2M epochs with no collapse. All three runs showed stable replicator populations at epoch 10M.

8. **Universal replicator structure**: All runs converge on the same `[ [ CPY+ FWD FWD ] CPY+ FWD FWD ] ]` core, confirming that the replication mechanism is VM-intrinsic, not geometry-dependent.

---

## Analysis (Task 1.5)

### Does dimensionality matter? (Open Question 2 from workplan)

**Yes, but the tile model resolves it.** The 2D shared-surface (patch) model introduces spatial coupling that creates a monoculture attractor, fundamentally different from 1D. However, the tile model — which preserves program independence while embedding on 2D geometry — recovers the same self-replicating dynamics as 1D, provided population is sufficient.

### What is the role of the two-component structure? (Open Question 3)

The T+ / T- cross-talk (modeled as 50% probability of cross-tetrahedron interaction) provides a mixing channel. Local pairing with T+/T- separation creates spatial niches that accelerate replicator emergence by ~5x compared to global pairing.

### Comparison with 1D Soup

| Property | 1D Soup | 2D n100 local | 2D n100 global | 2D n157 local |
|----------|---------|--------------|----------------|---------------|
| Population | 4,096 | 1,666 | 1,666 | 4,108 |
| Emergence epoch | ~3.5M | **0.8M** | 3.9M | 9.65M |
| Final nontrivial | ~100-200 | 115 | 52 | 119 |
| Dominant fraction | ~30-50% | ~11% | ~19% | ~12% |
| Entropy post-emergence | ~1.58 | 1.582 | 1.563 | 1.582 |
| Pairing mode | global | local | global | local |
| Replicator core | `[ [ CPY+ FWD FWD ]` | same | same | same |

The 2D local-pairing model with 1,666 tiles finds replicators ~4x faster than the 1D soup with 4,096 programs. This suggests that geometric locality (spatial niches on the stella surface) provides an evolutionary advantage absent in the abstract 1D model. The 2D global-pairing model matches the 1D timescale, confirming that the acceleration comes from spatial structure, not population size differences.

### Population Size vs Emergence Time

| Population | Pairing | Emergence epoch | Epochs per tile |
|------------|---------|-----------------|-----------------|
| 170 | local | >5M (never) | >29,412 |
| 1,666 | local | 800K | 480 |
| 1,666 | global | 3.9M | 2,341 |
| 4,108 | local | 9.65M | 2,349 |

The epochs-per-tile metric reveals that the n100 local run was anomalously fast (480 vs ~2,350), while n100 global and n157 local are consistent with each other. The n100 local speedup is likely due to spatial niche effects being most pronounced at intermediate population sizes.

### Implications for Phases 2-4

1. **Phase 2 (Potts model)**: The monoculture attractor in the patch model corresponds to the ordered phase in the Potts model. The critical temperature analog may be the patch/surface ratio.

2. **Phase 3 (Reaction-diffusion)**: The patch model IS a discrete reaction-diffusion system. The diffusion coefficient D corresponds to the locality parameter. The reaction term R is the VM execution. The monoculture attractor is the trivial fixed point.

3. **Phase 4 (Continuum limit)**: The tile model preserves program independence, suggesting that the continuum limit should preserve program boundaries (field configurations with spatial extent). The multi-stella FCC lattice version (next step) would provide the 3D lattice structure needed for a proper continuum limit.

---

## Multi-Stella FCC Lattice Results

### Architecture

Multiple stellae placed on an FCC lattice (Theorem 0.0.6) with inter-stella coupling via FCC nearest neighbors:

- FCC lattice of size L: L^3/2 stellae (periodic boundary conditions)
- Each stella: triangulated T+ and T- with Voronoi tiles (same as single-stella tile mode)
- Intra-stella interactions: parallel via persistent pthread thread pool
- Inter-stella interactions: serial phase (one tile from stella A interacts with one tile from FCC-neighbor stella B)
- Per-stella RNG for deterministic parallel execution
- FCC nearest-neighbor displacements: 12 vectors at (+-1,+-1,0) and permutations

### Design Constraint from Phase 1

The single-stella experiments established that **each stella needs >= ~1,666 tiles (n_sub >= 100)** for intra-stella replicator emergence. The original multi-stella defaults (n_sub=16, 42 tiles per stella) were in the "never finds replicators" range. Updated defaults:

| Parameter | Original | Updated | Rationale |
|-----------|----------|---------|-----------|
| n_sub | 16 | **100** | 42 tiles/stella insufficient; need >= 1,666 |
| lattice_size | 4 | **2** | 4 stellae sufficient for inter-stella propagation test |
| cross_rate | 0.1 | **1.0** | 1 cross-interaction per stella per epoch |

### Performance

| Configuration | Epochs/sec |
|---------------|-----------|
| L=2, n_sub=100, 1 thread | ~300 |
| L=2, n_sub=100, 16 threads | **999** |
| L=4, n_sub=100, 16 threads | **214** |

### L=2 Local Results (4 stellae, 6,664 tiles): REPLICATORS PROPAGATE BETWEEN STELLAE

| Epoch | Unique | Top copies | Nontrivial replicators | H(trit) |
|-------|--------|-----------|----------------------|---------|
| 1.66M | 1,695 | 10 | 0 | 1.553 |
| 1.67M | 615 | 292 | — | 1.569 |
| 1.70M | 658 | 192 | 114 | 1.584 |
| 1.80M | 579 | 303 | 120 | 1.582 |
| 2.0M | 596 | 267 | 108 | 1.583 |
| 2.5M | 609 | 235 | 111 | 1.583 |
| 3.0M | 692 | 256 | 99 | 1.582 |
| 3.5M | 623 | 211 | 122 | 1.582 |
| 4.0M | 584 | 310 | 113 | 1.582 |
| 4.5M | 600 | 236 | 113 | 1.581 |
| 5.0M | 604 | 325 | 105 | 1.581 |

Emergence at epoch ~1.67M — explosive transition (Top: 10 → 292 in one 10K interval). Replicators sustained for 3.3M+ epochs (entire remaining run).

#### L=2 Per-Stella Replicator Census (at epoch 5M)

```
Stella 0:  914 nontrivial replicators / 1666 tiles (54.9%)
Stella 1:  935 nontrivial replicators / 1666 tiles (56.1%)
Stella 2:  985 nontrivial replicators / 1666 tiles (59.1%)
Stella 3:  919 nontrivial replicators / 1666 tiles (55.2%)
Stellae with replicators: 4 / 4
```

**All 4 stellae contain replicators at nearly equal density (~55%).**

### L=4 Local Results (32 stellae, 53,312 tiles): PARALLEL EMERGENCE + FULL LATTICE COLONIZATION

| Epoch | Unique | Top copies | Nontrivial replicators | H(trit) |
|-------|--------|-----------|----------------------|---------|
| 70K | 1,935 | 5 | 0 | 1.556 |
| 80K | 781 | 200 | — | 1.581 |
| 100K | 702 | 261 | 110 | 1.583 |
| 200K | 760 | 251 | 116 | 1.582 |
| 500K | 737 | 287 | 108 | 1.582 |
| 1M | 731 | 289 | 107 | 1.582 |
| 2M | 699 | 282 | 115 | 1.582 |
| 3M | 692 | 256 | 99 | 1.582 |
| 4M | 726 | 260 | 110 | 1.583 |
| 5M | 762 | 268 | 111 | 1.583 |

**Emergence at epoch ~80K** — dramatically faster than any previous run. Top jumped from 5 to 200 in a single 10K interval. With 32 independent stellae running in parallel, the first replicator was found ~32x faster than in a single stella. Replicators then propagated to all stellae via FCC neighbor coupling and sustained for the entire 4.92M remaining epochs.

#### L=4 Per-Stella Replicator Census (at epoch 5M)

```
Stella  0:  906 / 1666 (54.4%)    Stella 16:  949 / 1666 (57.0%)
Stella  1:  950 / 1666 (57.0%)    Stella 17:  891 / 1666 (53.5%)
Stella  2:  919 / 1666 (55.2%)    Stella 18:  870 / 1666 (52.2%)
Stella  3:  930 / 1666 (55.8%)    Stella 19:  958 / 1666 (57.5%)
Stella  4:  881 / 1666 (52.9%)    Stella 20:  890 / 1666 (53.4%)
Stella  5:  951 / 1666 (57.1%)    Stella 21:  929 / 1666 (55.8%)
Stella  6:  916 / 1666 (55.0%)    Stella 22:  973 / 1666 (58.4%)
Stella  7:  928 / 1666 (55.7%)    Stella 23:  979 / 1666 (58.8%)
Stella  8: 1008 / 1666 (60.5%)    Stella 24:  890 / 1666 (53.4%)
Stella  9:  933 / 1666 (56.0%)    Stella 25:  947 / 1666 (56.8%)
Stella 10:  926 / 1666 (55.6%)    Stella 26:  956 / 1666 (57.4%)
Stella 11:  979 / 1666 (58.8%)    Stella 27:  898 / 1666 (53.9%)
Stella 12:  899 / 1666 (54.0%)    Stella 28:  864 / 1666 (51.9%)
Stella 13:  895 / 1666 (53.7%)    Stella 29:  946 / 1666 (56.8%)
Stella 14:  863 / 1666 (51.8%)    Stella 30:  982 / 1666 (58.9%)
Stella 15:  886 / 1666 (53.2%)    Stella 31:  936 / 1666 (56.2%)
Stellae with replicators: 32 / 32
```

**All 32 stellae colonized at uniform density.** Min: 51.8% (Stella 14), Max: 60.5% (Stella 8), Mean: 55.7%. No propagation gradient — the FCC lattice (diameter ~4 hops, 12 neighbors per site) is well-connected enough that replicator equilibrium is reached rapidly.

### Multi-Stella Key Findings

1. **Replicators propagate across FCC neighbor boundaries.** Both L=2 (4 stellae) and L=4 (32 stellae) show 100% colonization at cross_rate=1.0.

2. **Global equilibrium density is ~55%**, independent of lattice size. L=2 range: 54.9%-59.1%. L=4 range: 51.8%-60.5%. The slightly wider range at L=4 is consistent with statistical fluctuation across more stellae.

3. **Emergence scales inversely with stellae count.** With N stellae running independent evolutionary searches in parallel, the first replicator is found ~N times faster:

| Configuration | Stellae | Emergence epoch | Epoch × Stellae |
|---------------|---------|-----------------|-----------------|
| Single stella | 1 | 800K | 800K |
| L=2 | 4 | 1.67M | 6.68M |
| L=4 | 32 | 80K | 2.56M |

The "Epoch × Stellae" product is not constant because L=2 emergence is dominated by the time for the replicator to spread across stellae after being found in one. At L=4, there are enough parallel searches that the finding time dominates over the spreading time.

4. **No propagation gradient at cross_rate=1.0.** The FCC lattice is sufficiently well-connected that all stellae equilibrate. L=8 (256 stellae) is not needed at this coupling strength — uniform colonization is expected.

5. **Propagation speed scales as √(cross_rate).** Seeded-replicator experiments (known replicator planted in stella 0) measured wavefront speed directly: 70 epochs at cr=10.0 to 2,500 epochs at cr=0.01. The √(cross_rate) scaling indicates **diffusive spreading** — a reaction-diffusion process where both inter-stella transfer and intra-stella amplification contribute. This is consistent with the Phase 3 reaction-diffusion formulation.

6. **No critical coupling threshold exists.** Even cross_rate=0.0003 (0.01 interactions/epoch) still propagates — 19/32 colonized in 100K epochs. The replicator propagation mechanism is extremely robust — a single successful transfer event seeds exponential growth within the target stella.

7. **Scaling regime transition at low coupling.** At high cross_rates (0.1–10.0), propagation time scales as 1/√(cross_rate) — the diffusive regime where intra-stella amplification is the bottleneck. At very low cross_rates (0.0003–0.01), scaling transitions to ~1/cross_rate — the transfer-limited regime where the rare inter-stella interaction frequency becomes the bottleneck. The crossover occurs around cr ≈ 0.01–0.1, corresponding to the point where mean inter-stella transfer time equals intra-stella amplification time.

8. **Critical nucleus for replicator amplification.** A single replicator tile in 1,666 random tiles never amplifies (0/10 trials, 50K epochs). The critical nucleus is ~11 tiles (0.7%) — below this, success is stochastic; above, amplification is 100% reliable. Amplification follows logistic growth with τ_amplify ≈ 150–200 epochs to reach ~55% equilibrium, independent of seed size above threshold.

9. **Equilibrium density is a selection-mutation balance.** The ~55% density at μ=0.001 is not arbitrary — it varies smoothly from ~65% (zero mutation) to 0% (μ ≥ 0.005). The critical mutation rate μ_c ≈ 0.004–0.005 represents an error catastrophe threshold analogous to Eigen's quasispecies theory. The standard μ=0.001 sits at ~20% of μ_c, providing a ~4–5× safety margin.

### Comparison: Single-Stella vs Multi-Stella

| Property | Single n100 local | Multi L=2 (4) | Multi L=4 (32) |
|----------|------------------|--------------|----------------|
| Total tiles | 1,666 | 6,664 | 53,312 |
| Tiles per stella | 1,666 | 1,666 | 1,666 |
| Emergence epoch | 800K | 1.67M | **80K** |
| Final nontrivial | 115 (of 200) | 105 (of 200) | 111 (of 200) |
| Final entropy | 1.582 | 1.581 | 1.583 |
| Replicator density | ~55% | ~55% (all 4) | ~56% (all 32) |
| Stellae colonized | N/A | 4/4 | 32/32 |

---

## Files

| File | Description |
|------|-------------|
| `stella_lang/soup_2d.c` | Patch-mode implementation |
| `stella_lang/soup_2d_tile.c` | Tile-mode implementation (O(n^2) mesh, FCC geometry) |
| `stella_lang/soup_multi_stella.c` | Multi-stella FCC lattice implementation (pthreads) |
| `stella_lang/soup_2d_*.log` | Patch-mode run logs |
| `stella_lang/tile_n100_local.log` | n100 local tile run (10M epochs, complete) |
| `stella_lang/tile_n100_global.log` | n100 global tile run (10M epochs, complete) |
| `stella_lang/tile_n157_local.log` | n157 local tile run (10M epochs, complete) |
| `stella_lang/multi_L2_n100_local.log` | Multi-stella L=2 run (5M epochs, complete) |
| `stella_lang/multi_L4_n100_local.log` | Multi-stella L=4 run (5M epochs, complete) |
| `stella_lang/multi_L4_cross0.01.log` | Cross-rate sweep: cross_rate=0.01 (5M epochs, complete) |
| `stella_lang/multi_L4_cross0.1.log` | Cross-rate sweep: cross_rate=0.1 (5M epochs, complete) |
| `stella_lang/multi_L4_cross10.0.log` | Cross-rate sweep: cross_rate=10.0 (5M epochs, complete) |
| `stella_lang/multi_L4_propagation_cr*.log` | Seeded propagation runs (200K epochs, census every 1K, complete) |
| `stella_lang/multi_L4_wavefront_cr0.01.log` | 5M RNG-fixed run: cr=0.01, adaptive census (complete) |
| `stella_lang/multi_L4_wavefront_cr0.1.log` | 5M RNG-fixed run: cr=0.1, adaptive census (complete) |
| `stella_lang/multi_L4_wavefront_cr1.0.log` | 5M RNG-fixed run: cr=1.0, adaptive census (complete) |
| `stella_lang/multi_L4_wavefront_cr10.0.log` | 5M RNG-fixed run: cr=10.0, adaptive census (complete) |
| `stella_lang/run_cross_rate_sweep.sh` | Script to launch cross-rate sweep runs |

---

## Cross-Rate Sweep Results (Pre-RNG-Fix, Preliminary)

### Summary Table

| cross_rate | Inter/epoch | First detection | Final colonization | Mean density | Final H(trit) | Status |
|------------|------------|-----------------|-------------------|-------------|---------------|--------|
| 0.01 | 1 | 1.38M | 32/32 | ~57% | ~1.582 | Complete (5M) |
| 0.1 | 3 | 990K | 32/32 | ~55% | ~1.582 | Complete (5M) |
| 1.0 | 32 | 80K | 32/32 | ~56% | ~1.583 | Complete (5M) |
| 10.0 | 320 | 1.06M | 32/32 | ~56% | ~1.582 | Complete (5M) |

**Key result: ALL cross_rates achieve full lattice colonization.** Even cross_rate=0.01 (1 inter-stella interaction per epoch) colonizes all 32 stellae by epoch 5M. There is no critical coupling threshold within the tested range.

### Critical Finding: Emergence Timing Is Stochastic, Not Deterministic

**Initial hypothesis (WRONG):** Emergence is purely intra-stella and occurs at the same epoch in all runs because per-stella RNGs are identical.

**Corrected understanding:** While per-stella RNGs are seeded identically (`rng_seed(sites[s].rng, seed + 7919 * (s+1))`), the soup is a **chaotic system** where inter-stella interactions perturb tile contents, causing evolutionary trajectories to diverge across runs.

**Evidence from wavefront experiment:** Runs with identical seed=42 and cross_rate=1.0 but different `check_interval` (50K vs 100K) and `census_interval` (10K vs 0) produced completely different emergence times:

| Run | check_interval | census_interval | Epoch 80K Top | Emergence |
|-----|---------------|----------------|--------------|-----------|
| Original 5M | 100K | off | **200** (takeover) | ~80K |
| Wavefront 500K | 50K | 10K | **8** (no emergence) | >500K |

The different `check_interval` changes how many `master_rng` draws occur per epoch (because `mss_check_replicators` and `mss_metrics` draw from `master_rng`). This shifts the `master_rng` state, which changes which tiles are selected for inter-stella interactions (`mss_interact_cross` uses `master_rng`). Even though inter-stella modifications are only ~0.12% of all tile writes at cross_rate=1.0, the perturbations compound over thousands of epochs — different inter-stella writes → different tile contents → different VM execution results in subsequent intra-stella interactions → cascading divergence.

**The RNG architecture creates an unintended coupling:** `master_rng` is shared between inter-stella dynamics, metrics sampling, and replicator checking. Changing any parameter that affects the number of `master_rng` draws (check_interval, census_interval, log_interval) shifts the entire inter-stella trajectory.

### Detection Timing in the Original 5M Runs

In the four original 5M runs (cross_rate = 0.01, 0.1, 1.0, 10.0), the same `check_interval=100000` and `log_interval=10000` were used. The only difference was cross_rate, which changes the number of inter-stella `master_rng` draws per epoch:

| cross_rate | master_rng draws/epoch (inter-stella) | First detection |
|------------|--------------------------------------|----------------|
| 0.01 | 3 (1 interaction × 3 draws) | 1.38M |
| 0.1 | 9 (3 × 3) | 990K |
| 1.0 | 96 (32 × 3) | 80K |
| 10.0 | 960 (320 × 3) | 1.06M |

The different draw rates cause the master_rng to diverge across runs, which creates different inter-stella interaction patterns, which perturbs each stella's evolutionary trajectory differently. **The apparent first detection epoch is a compound effect of (a) different emergence timing due to different perturbation patterns and (b) different tile sampling in the metrics check.**

The cross_rate=1.0 run's early emergence at 80K was likely a lucky perturbation pattern, not representative. The single-stella baseline (n100 local) found replicators at 800K with zero inter-stella interactions.

### Implications

1. **No critical cross_rate exists in the tested range.** All four 5M runs achieved 32/32 colonization regardless of cross_rate. The replicator colonization mechanism is robust.

2. **Emergence timing is stochastic.** With 32 parallel stellae, emergence can occur anywhere from ~25K to >1M epochs depending on the specific perturbation pattern from inter-stella interactions. The 80K emergence in the original cross_rate=1.0 run was an anomalously fast outcome.

3. **Propagation speed requires controlled measurement.** To isolate the effect of cross_rate on propagation (not emergence), the wavefront experiment must run long enough for replicators to emerge. Runs with `census_interval=50000` at 5M epochs are in progress.

4. **RNG architecture lesson:** Future experiments should use a separate RNG for metrics/census sampling to avoid coupling between measurement and dynamics. The current design means changing measurement parameters (check_interval, census_interval) changes the dynamics.

### RNG Decoupling Fix

The RNG coupling issue (measurement draws from `master_rng` perturbing dynamics) was fixed by adding a separate `metrics_rng` to the simulation:

- **`master_rng`**: Used only for inter-stella dynamics (tile swaps and stella/neighbor selection) — 4 call sites
- **`metrics_rng`**: Used only for measurement sampling (metrics logging, replicator checking, census) — 5 call sites, seeded independently with `seed + 314159`

This ensures that changing `--check-interval`, `--log-interval`, or `--census-interval` no longer perturbs inter-stella dynamics. Runs with different measurement schedules but the same seed now produce identical evolutionary trajectories.

### Wavefront Propagation Speed: Seeded Replicator Experiment

To isolate propagation speed from the stochastic emergence wait, a `--seed-replicator` mode was added that plants the known replicator `[ [ CPY+ FWD1 FWD0 ] CPY+ FWD1 FWD0 ] ] FWD1` into all tiles of stella 0 at startup. This allows direct measurement of how fast replicators spread across the FCC lattice.

**Setup:** L=4 (32 stellae), n_sub=100, seed=42, census every 100 epochs (cr=1.0 and 10.0 at census every 10), known replicator seeded in stella 0.

#### Propagation Wavefront Data

**cross_rate = 0.01** (1 inter-stella interaction/epoch):

| Epoch | Stellae colonized | Epoch | Stellae colonized |
|-------|------------------|-------|------------------|
| 100 | 1/32 | 1400 | 10/32 |
| 200 | 1/32 | 1500 | 15/32 |
| 300 | 3/32 | 1600 | 16/32 |
| 400 | 3/32 | 1800 | 18/32 |
| 600 | 4/32 | 2000 | 22/32 |
| 800 | 5/32 | 2200 | 26/32 |
| 900 | 6/32 | 2400 | 29/32 |
| 1200 | 8/32 | **2500** | **32/32** |
| 1300 | 9/32 | | |

**cross_rate = 0.1** (3 inter-stella interactions/epoch):

| Epoch | Stellae colonized |
|-------|------------------|
| 100 | 5/32 |
| 200 | 7/32 |
| 300 | 8/32 |
| 400 | 11/32 |
| 500 | 20/32 |
| 700 | 25/32 |
| 800 | 29/32 |
| **900** | **32/32** |

**cross_rate = 1.0** (32 inter-stella interactions/epoch):

| Epoch | Stellae colonized |
|-------|------------------|
| 10 | 1/32 |
| 20 | 6/32 |
| 40 | 8/32 |
| 60 | 10/32 |
| 80 | 11/32 |
| 100 | 12/32 |
| 110 | 18/32 |
| 140 | 24/32 |
| 200 | 29/32 |
| **230** | **32/32** |

**cross_rate = 10.0** (320 inter-stella interactions/epoch):

| Epoch | Stellae colonized |
|-------|------------------|
| 10 | 13/32 |
| 20 | 17/32 |
| 40 | 22/32 |
| 50 | 28/32 |
| 60 | 31/32 |
| **70** | **32/32** |

#### Propagation Summary

| cross_rate | n_cross/epoch | Time to 32/32 | Effective speed (stellae/epoch) |
|-----------|---------------|---------------|-------------------------------|
| 0.01 | 1 | ~2,500 epochs | 0.013 |
| 0.1 | 3 | ~900 epochs | 0.036 |
| 1.0 | 32 | ~230 epochs | 0.14 |
| 10.0 | 320 | ~70 epochs | 0.46 |

#### Scaling Analysis

Propagation scales as approximately **√(cross_rate)**, not linearly:

| cross_rate ratio | Speed ratio | √(ratio) |
|-----------------|------------|-----------|
| 0.1 / 0.01 = 10x | 2.8x | 3.2x |
| 1.0 / 0.1 = 10x | 3.9x | 3.2x |
| 10.0 / 1.0 = 10x | 3.3x | 3.2x |

This √(cross_rate) scaling is consistent with **diffusive spreading** rather than ballistic propagation. Each inter-stella interaction transfers one tile — the replicator must then amplify within the target stella before it can seed further neighbors. The amplification time creates a diffusive bottleneck: the wavefront advances one lattice hop, waits for local amplification, then advances again.

The propagation is NOT transfer-limited (ballistic): at cross_rate=10.0, there are 320 transfers/epoch, but it still takes 70 epochs to colonize 32 stellae. It is NOT purely amplification-limited either: at cross_rate=0.01 (1 transfer/epoch), propagation takes 2,500 epochs — if amplification dominated, the time would be independent of cross_rate.

**The propagation regime is mixed diffusive**: both transfer probability and local amplification contribute to the wavefront speed. This is characteristic of a reaction-diffusion process — consistent with the Phase 3 reaction-diffusion formulation in the workplan.

#### Non-Monotonic Fluctuations

The census occasionally shows non-monotonic counts (e.g., cr=1.0: epoch 140 = 24/32, epoch 150 = 23/32). This occurs because the census samples a subset of tiles per stella — a stella near the colonization threshold can flicker above and below detection. It does NOT indicate that stellae lose their replicators; it is a sampling artifact.

#### Verification: L=2 Propagation

A quick L=2 test (4 stellae, cross_rate=1.0, census every 1000) showed 4/4 colonized at the very first census (epoch 1000), with all stellae at ~55% density. This confirmed that propagation at cross_rate=1.0 saturates within a few hundred epochs even at L=2, motivating the ultra-fine (census every 10-100 epochs) measurements above.

#### Per-Stella Wavefront Tracking (Diffusive Mechanism Confirmed)

To confirm the diffusive interpretation, FCC graph distances from the source stella were computed via BFS, and census output was enhanced to show colonization at each distance shell. The FCC L=4 lattice (32 stellae) has the following distance structure from stella 0:

| Distance | Stellae | Meaning |
|----------|---------|---------|
| d=0 | 1 | Source (seeded) |
| d=1 | 12 | Direct FCC neighbors |
| d=2 | 18 | Two hops away |
| d=3 | 1 | Maximum distance (periodic boundary) |

**Wavefront by distance shell** (epoch when first stellae at distance d are colonized, and epoch when all are colonized):

| cross_rate | d=1 first | d=1 complete | d=2 first | d=2 complete | d=3 first | d=3 complete |
|-----------|-----------|-------------|-----------|-------------|-----------|-------------|
| 0.01 | 300 | 2,200 | 600 | 2,500 | 2,300 | 2,300 |
| 0.1 | 100 | 900 | 300 | 900 | 500 | 500 |
| 1.0 | 20 | 150 | 60 | 230 | 210 | 210 |
| 10.0 | 10 | 20 | 10 | 60 | 70 | 70 |

**Key findings:**

1. **Wavefront is NOT strictly hop-by-hop.** At cr=0.01, d=2 stellae begin colonizing (epoch 600) long before all d=1 stellae are complete (epoch 2,200). At cr=0.1, the d=3 stella is colonized (epoch 500) before d=1 and d=2 are complete (epoch 900). This rules out ballistic propagation.

2. **Stochastic diffusion confirmed.** The fuzzy wavefront boundaries — where different distance shells overlap in colonization time — are characteristic of stochastic diffusion. Each inter-stella transfer has a probability (~55%) of carrying a replicator, and colonization requires multiple successful transfers to achieve self-sustaining density.

3. **Completion time scales with distance.** For cr=0.01: d=1 complete at 2,200; d=2 at 2,500; d=3 at 2,300. The d=2 shell (18 stellae) takes longer than d=3 (1 stella) because it has more stellae to fill. When normalized by number of stellae, the per-stella colonization rate is roughly constant within each distance shell.

4. **Long-range leaking.** At cr=0.1 and cr=10.0, far stellae (d=2, d=3) get colonized before the near shell (d=1) is complete. This occurs because the FCC lattice is highly connected (12 neighbors) — replicators can reach d=2 via multiple independent paths, some of which bypass uncolonized d=1 stellae.

5. **"First colonized" timing scales roughly linearly with distance** at a given cross_rate (consistent with diffusion: first arrival time ~ d for a random walk in high-connectivity graphs, even though mean colonization time ~ d²). The "complete" timing is dominated by the number of stellae at each distance, not the distance itself.

#### Very Low Cross-Rate Experiments (Propagation Failure Threshold)

To find the lower bound of the propagation regime, we extended seeded-replicator experiments to extremely low cross_rates using **fractional probabilistic coupling**. The original implementation clamped `n_cross = max(1, floor(cross_rate * n_fcc))`, which meant all cross_rates below 1/32 ≈ 0.03125 produced exactly 1 interaction/epoch. The fix: compute `expected_cross = cross_rate * n_fcc`, take the integer part, and probabilistically round up with probability equal to the fractional part. This allows sub-integer interaction rates.

**Control test:** cross_rate = 0.0 (zero coupling) correctly produces 0/32 colonization — the seeded stella cannot spread.

**Results (L=4, 32 stellae, seeded replicator in stella 0):**

| cross_rate | interactions/epoch | Time to 32/32 | T × cr |
|-----------|-------------------|---------------|--------|
| 0.0003 | 0.01 | >100K (19/32 at 100K) | >30 |
| 0.001 | 0.03 | ~61,000–65,000 | ~63 |
| 0.003 | 0.10 | ~27,000–28,000 | ~82 |
| 0.01 | 0.32 | ~5,500–7,000 | ~63 |
| 0.1 | 3.2 | ~900–1,600 | ~125 |
| 1.0 | 32 | ~230–560 | ~395 |
| 10.0 | 320 | ~70 | ~700 |

**Key findings:**

1. **No sharp propagation failure threshold.** Even at cr=0.0003 (one interaction every ~100 epochs on average), propagation continues — 19/32 stellae colonized in 100K epochs. The replicator is never "destroyed" by being rare; it simply spreads more slowly.

2. **Scaling regime transition.** At high cross_rates (0.1–10.0), propagation scales as √(cross_rate) — the diffusive regime where local amplification is the bottleneck. At very low cross_rates (0.0003–0.01), the product T×cr ≈ 60–80 is roughly constant, suggesting **linear scaling** T ∝ 1/cr. In this regime, each rare interaction directly matters and the bottleneck shifts from amplification to transfer frequency.

3. **Physical interpretation.** The transition from √(cr) scaling (high coupling) to 1/cr scaling (low coupling) corresponds to the competition between two timescales:
   - τ_transfer = 1/(cr × n_fcc): mean time between inter-stella interactions
   - τ_amplify: time for a transferred replicator to reach self-sustaining density (~55%) within the target stella

   When τ_transfer << τ_amplify (high coupling), amplification dominates → diffusive √(cr) scaling.
   When τ_transfer >> τ_amplify (low coupling), transfer dominates → linear 1/cr scaling.
   The crossover occurs around cr ≈ 0.01–0.1.

#### Intra-Stella Amplification (Single-Tile Seeding)

To measure the "reaction" timescale in the reaction-diffusion picture, we seeded varying numbers of replicator tiles into a single stella (cross_rate=0, no inter-stella coupling) and tracked amplification.

**Critical nucleus size (L=2, 1,666 tiles/stella, 10 trials each):**

| Seed tiles | % of stella | Amplification rate | Notes |
|-----------|------------|-------------------|-------|
| 1 | 0.06% | 0/10 (0%) | Never amplifies |
| 2 | 0.12% | 6/10 (60%) | Stochastic — depends on tile adjacency |
| 3 | 0.18% | 2/10 (20%) | Highly variable |
| 4 | 0.24% | 4/10 (40%) | Highly variable |
| 5 | 0.30% | 8/10 (80%) | Usually succeeds |
| 6–10 | 0.4–0.6% | 4–9/10 | Noisy mid-range |
| 11+ | 0.7%+ | 5/5 (100%) | Reliable amplification |
| 50+ | 3%+ | 5/5 (100%) | Always succeeds |

**Key findings:**

1. **A single replicator tile cannot amplify.** Even after 50,000 epochs, a lone replicator in 1,665 random tiles produces 0% colonization. The replicator is destroyed by interactions with random neighbors before it can reproduce. This establishes a **critical nucleus** for self-replication.

2. **Critical nucleus is ~11 tiles (0.7% of stella).** Below this, amplification is stochastic and unreliable. Above, it is 100% reliable. The mid-range (2–10 tiles) is noisy because success depends on whether seeded tiles are geometric neighbors — adjacent replicators can reinforce each other, while isolated ones are destroyed.

3. **Amplification is fast: τ_amplify ≈ 150–200 epochs.** Once above the critical nucleus, growth follows a logistic curve from seed to ~55% equilibrium density. The growth curve from 20 seeded tiles (1.2%):

   | Epoch | Density | % of equilibrium |
   |-------|---------|-----------------|
   | 10 | 1.4% | 3% |
   | 30 | 5.5% | 10% |
   | 50 | 8.6% | 16% |
   | 80 | 22.7% | 41% |
   | 100 | 31.8% | 58% |
   | 130 | 45.1% | 82% |
   | 150 | 50.6% | 92% |
   | 200 | 58.8% | ~100% (equilibrium) |

4. **Amplification time is independent of seed size** (above threshold). N=15, N=50, N=100, N=500 all reach equilibrium by epoch ~200. The logistic growth rate is set by the intra-stella interaction rate (833 pairings/epoch), not the initial seed density.

5. **Connection to reaction-diffusion.** The measured τ_amplify ≈ 200 epochs explains the scaling regime transition observed in the inter-stella propagation experiments. At cr=0.01 (τ_transfer = 1/0.32 ≈ 3 epochs), τ_transfer << τ_amplify, so amplification dominates → diffusive scaling. At cr=0.0003 (τ_transfer = 1/0.01 = 100 epochs), τ_transfer and τ_amplify are comparable → transition to transfer-limited regime. This quantitatively confirms the two-timescale interpretation.

#### Equilibrium Density vs Mutation Rate

The ~55% replicator density observed in all previous experiments (which used mutation_rate=0.001) is a **selection-mutation equilibrium** — the balance between replicator self-copying and mutation-driven degradation. To confirm this, we swept mutation rate at fixed geometry (L=2, 1,666 tiles/stella, fully seeded, cross_rate=0, 10K epochs, 3 trials each):

| mutation_rate | Avg density | Range | Notes |
|--------------|------------|-------|-------|
| 0.0000 | 65.0% | 63–67% | Upper bound — no mutation |
| 0.0001 | 63.0% | 61–65% | Near-zero mutation |
| 0.0003 | 60.6% | 57–63% | |
| 0.0005 | 61.2% | 60–63% | |
| 0.0007 | 56.6% | 55–58% | |
| **0.001** | **56.0%** | **55–57%** | **Standard value used in all experiments** |
| 0.0015 | 49.2% | 48–51% | |
| 0.002 | 46.0% | 44–49% | |
| 0.003 | 38.4% | 38–39% | |
| 0.004 | 20.4% | 17–25% | Near extinction |
| 0.005 | ~2% | 0–6% | Mostly extinct |
| 0.007 | 0% | 0% | Extinct |
| 0.01 | 0% | 0% | Extinct |

**Key findings:**

1. **Equilibrium density is a smooth, monotonically decreasing function of mutation rate.** This confirms it is a selection-mutation balance, not an arbitrary parameter. Even at zero mutation, density is ~65% (not 100%) because the VM interaction dynamics themselves create some non-replicating tiles.

2. **Critical mutation rate μ_c ≈ 0.004–0.005.** Above this, replicators cannot sustain themselves and go extinct. This is an **error threshold** analogous to Eigen's error catastrophe in quasispecies theory — the maximum mutation rate compatible with the persistence of genetic information.

3. **The standard mutation rate (0.001) sits comfortably below the error threshold.** The ratio μ/μ_c ≈ 0.2–0.25, providing a ~4–5× safety margin. This explains why replicators are robust across all tested conditions — the system operates well within the viable parameter regime.

4. **Physical interpretation.** The error threshold at μ_c ≈ 0.004 corresponds to ~0.4% mutation per trit per epoch. With prog_size=24 trits, this is ~0.1 mutations per program per epoch. When the expected number of mutations per replication cycle approaches 1, the replicator can no longer maintain its identity — the classic Eigen threshold. At the standard μ=0.001, there are ~0.024 mutations per program per epoch, well below the threshold.

5. **Zero-mutation density of ~65%** (not 100%) indicates that the VM interaction dynamics inherently produce some non-replicating configurations. When tile A copies into tile B, the combined execution doesn't always perfectly preserve A — the second tile's content can interfere with the copy process. This ~35% "interaction noise floor" is a property of the VM instruction set, not of mutation.

---

## 5M Epoch Natural Emergence Runs (RNG-Fixed)

These runs repeat the original cross-rate sweep with the RNG decoupling fix and adaptive census (`--census-fast 500`). Unlike the seeded wavefront experiments, replicators emerge naturally from random initial conditions — measuring both **emergence time** and **propagation time** in a single run.

**Setup:** L=4 (32 stellae), n_sub=100, seed=42, 5M epochs, mutation_rate=0.001, census every 50K (switching to 500 after first replicator detected), RNG-decoupled (`metrics_rng` independent of `master_rng`).

### Results

| cross_rate | Inter/epoch | Emergence epoch | First census >0 | 32/32 epoch | Propagation window | Runtime |
|-----------|------------|-----------------|-----------------|-------------|-------------------|---------|
| 0.01 | 0.32 | ~700K | 700K (1/32) | 1,950K | ~1,250K | 5.5 hrs |
| 0.1 | 3.2 | ~1,410K | 1,410K (1/32) | 1,570K | ~160K | 5.2 hrs |
| 1.0 | 32 | ~430K | 430K (32/32) | 430K | <50K (instant) | 5.8 hrs |
| 10.0 | 320 | ~80K | 80K (32/32) | 80K | <50K (instant) | 6.8 hrs |

**Note on "Emergence epoch":** The emergence time is estimated from the first non-zero census. The coarse 50K census interval means the true emergence could be up to 50K epochs earlier. The adaptive census (switching to 500 after detection) captures fine-grained propagation — but for cr=1.0 and cr=10.0, propagation was so fast that the first census after emergence already showed 32/32.

### Final Per-Stella Density (epoch 5M)

All 32 stellae in all 4 runs reached the ~55% equilibrium density:

| cross_rate | Min density | Max density | Mean density | Std dev |
|-----------|------------|------------|-------------|---------|
| 0.01 | 49.2% | 60.9% | 55.8% | ±2.7% |
| 0.1 | 51.0% | 60.6% | 55.6% | ±2.5% |
| 1.0 | 48.3% | 62.1% | 55.4% | ±3.0% |
| 10.0 | 47.5% | 61.3% | 55.2% | ±2.9% |

**Equilibrium density is independent of cross_rate** — all four runs converge to ~55% ± 3%, consistent with the selection-mutation balance at μ=0.001.

### Comparison with Pre-RNG-Fix Runs

| cross_rate | Old emergence (pre-fix) | New emergence (RNG-fixed) | Notes |
|-----------|------------------------|--------------------------|-------|
| 0.01 | 1.38M | ~700K | Different trajectories due to decoupled RNG |
| 0.1 | 990K | ~1,410K | |
| 1.0 | 80K | ~430K | Old run was anomalously fast |
| 10.0 | 1.06M | ~80K | |

The emergence times differ between old and new runs because the RNG decoupling changes the inter-stella interaction sequence (measurement draws no longer consume `master_rng` state). This confirms the stochastic nature of emergence — it depends sensitively on the exact perturbation history, not just on cross_rate.

### Propagation Speed: Consistency with Seeded Experiments

The propagation windows from these natural-emergence runs can be compared with the seeded wavefront experiments:

| cross_rate | Seeded propagation time | Natural propagation window | Ratio |
|-----------|------------------------|---------------------------|-------|
| 0.01 | ~2,500–7,000 | ~1,250,000 | ~250x |
| 0.1 | ~900–1,600 | ~160,000 | ~150x |
| 1.0 | ~230–560 | <50,000 | — |
| 10.0 | ~70 | <50,000 | — |

The natural propagation windows are 100–250x longer than seeded propagation times for cr=0.01 and cr=0.1. This is because:
1. **Emergence is gradual.** A naturally-emerging replicator starts as a single copy, not a fully-colonized stella. It must first amplify within the source stella (τ_amplify ≈ 200 epochs), cross the critical nucleus threshold (~11 tiles), and reach ~55% density before inter-stella transfer becomes effective.
2. **The coarse 50K census interval misses early progression.** For cr=0.01, the jump from 1/32 at 700K to 32/32 at 1,950K spans 1.25M epochs — but actual propagation (once the source stella is fully colonized) takes only ~2,500 epochs. The remaining ~1.2M epochs are the wait for the source stella to go from first replicator tile to full colonization, which involves stochastic amplification from a single copy.
3. **For cr=1.0 and 10.0**, propagation is fast enough that the source stella's amplification and inter-stella propagation happen within the same 50K census window — hence the first non-zero census shows 32/32.

### Key Findings

1. **All cross_rates achieve 32/32 colonization** — confirming the pre-fix result. The RNG decoupling changes individual trajectories but not the qualitative outcome.
2. **Higher cross_rate correlates with earlier emergence** in the RNG-fixed runs (80K at cr=10.0 vs 1,410K at cr=0.1). With 32 parallel stellae and more inter-stella mixing, the population explores more of the fitness landscape per epoch.
3. **Equilibrium is universal.** Once replicators emerge and propagate, all stellae converge to ~55% ± 3% density, independent of how they got there (natural emergence vs seeding, high vs low cross_rate).
4. **The dominant timescale is emergence, not propagation.** For all cross_rates, propagation (seeded experiments: 70–7,000 epochs) is negligible compared to emergence (80K–1,410K epochs). The practical bottleneck is the stochastic search for a self-replicating program.

---

## Cross-Rate Sweep: Theoretical Predictions from Proof Chain

The cross-rate sweep (varying inter-stella coupling at fixed L=4) connects the computational experiment to the analytical framework. Here we document what the proofs predict about the critical coupling strength.

### What cross_rate Means Physically

In each epoch, the simulation performs:
- **Intra-stella**: n_tiles_per_stella/2 = 833 interactions per stella (local tile pairing + VM execution)
- **Inter-stella**: cross_rate x n_fcc interactions total (random tile from stella A paired with random tile from FCC-neighbor stella B)

The inter/intra ratio per stella per epoch is cross_rate / 833:

| cross_rate | Inter-stella/epoch | Inter/Intra ratio | Status |
|------------|-------------------|-------------------|--------|
| 0.01 | 1 (clamped) | 0.001% | Complete (32/32 colonized) |
| 0.1 | 3 | 0.012% | Complete (32/32 colonized) |
| 1.0 | 32 | 0.12% | Complete (32/32 colonized) |
| 10.0 | 320 | 1.2% | Complete (32/32 colonized) |

### Prop 2.5.2b: All Faces Are Shared (Global Label Constraint)

In the FCC tetrahedral-octahedral honeycomb (Thm 0.0.6):
- Each tetrahedral face is shared with an adjacent octahedron
- Each octahedral face is shared with an adjacent tetrahedron
- **No faces are unshared** — the face-sharing graph is bipartite and connected

Character orthogonality integrals over shared edges force the representation labels of adjacent cells to agree. Since the face-sharing graph is connected, this propagates transitively: **ALL cells carry the same representation label R** (Prop 2.5.2b Claim (d)). In the exact gauge theory, the inter-stella coupling is not a free parameter — it is absolute.

### Prop 2.5.2c: Transfer Matrix Mass Gap

The intensive mass gap per spatial unit cell is:

    mu(beta) = -3 ln 3 - 8 ln u_3(beta)

At **physical coupling beta = 6** (lattice QCD): u_3 ~ 0.42 (Prop 2.5.2b section 5), giving:

    mu(6) = -3(1.099) - 8(-0.868) = -3.30 + 6.94 = 3.64

Correlation length xi = 1/mu ~ 0.27 lattice spacings. Gauge correlations are confined well within a single stella. This is the strong-coupling confinement regime.

### Topology Change: Isolated vs Coupled Exponents

The partition function exponents change when cells are assembled on the FCC lattice:

| System | Euler per cell | Faces per cell | Source |
|--------|---------------|----------------|--------|
| Isolated K_4 | 4 | 10 | Prop 0.0.38a |
| Coupled FCC | 3 | 8 | Prop 2.5.2b |

The reduction (4 -> 3, 10 -> 8) quantifies how much of each cell's topological structure is "given over" to inter-cell coupling via face sharing. Roughly **20-25%** of the dynamics involve face-sharing: (10-8)/10 = 20% of faces, (4-3)/4 = 25% of Euler characteristic.

If the inter/intra ratio matched this face-sharing topology, cross_rate would need to be ~833 x 0.2 ~ 170. The fact that replicators propagate at cross_rate = 1.0 (ratio 0.12%, far below 20%) shows that replicator propagation is a much weaker condition than the gauge theory's global label constraint.

### Predictions for the Sweep

**From above (strong coupling):** The exact theory has infinite coupling (global label constraint). cross_rate = 1.0 already achieves full colonization. Higher values (10.0) should show faster equilibration but the same steady-state density (~55%).

**From below (correlation length):** The gauge correlation length xi ~ 0.27 lattice spacings means correlations decay rapidly between stellae. However, replicator colonization is NOT a correlation phenomenon — it requires only a single successful replicator transfer event to seed exponential growth within the target stella. This suggests the critical cross_rate could be very low.

**Percolation analogy:** Each inter-stella interaction is a "bond" that can transmit a replicator. At cross_rate = 0.01, there is exactly 1 such bond per epoch. Over 5M epochs, that is 5M transfer opportunities. If replicators emerge at ~80K epochs (as in the L=4 cross_rate=1.0 run), there are ~4.9M epochs of post-emergence inter-stella transfer. Even at 1 transfer/epoch, and assuming ~55% of tiles in the source stella are replicators, the probability of transferring a replicator in any given interaction is ~55%. So ~2.7M replicator transfer events would occur over the run — far more than the 32 needed to seed each stella once. **Prediction: even cross_rate = 0.01 should achieve full colonization, but with a significant delay after intra-stella emergence.**

**Most interesting outcome:** If cross_rate = 0.01 shows **partial colonization** (some stellae colonized, others not) at epoch 5M, this would indicate a propagation timescale longer than the run. In the gauge theory language, this would map to a regime where the correlation length becomes comparable to the lattice size — a critical coupling regime. This would motivate an L=8 run at that cross_rate to test for finite-size effects.

### Connection to Octahedral Mediation (Prop 0.0.39)

The current simulation implements **direct coupling** (Mode A): a tile from stella A is paired directly with a tile from stella B. The physical FCC coupling, however, is mediated through **octahedral interstitials** — each tetrahedral face is shared with an adjacent octahedron, not directly with another tetrahedron (Prop 2.5.2b section 3.5).

The octahedral mediation experiment (listed in Next Steps) would implement Mode B: inter-stella VM execution runs stella-tile + octahedron-tile pairs. The octahedral interstitial acts as a "relay" that could either amplify or attenuate replicator propagation compared to direct coupling. Prop 0.0.39 establishes that the central octahedron is the "color-neutral core" where phase cancellation occurs; the FCC interstitial octahedra may play an analogous filtering role in inter-stella coupling.

---

## Octahedral Mediation Experiment (Mode B)

**Date:** 2026-03-09

### Overview

In the physical tetrahedral-octahedral honeycomb (Thm 0.0.6), **no two tetrahedra share a face** — each tetrahedral face is shared with an adjacent octahedron (Prop 2.5.2b §3.5). The direct coupling model (Mode A: stella tile + stella tile → VM → writeback) bypasses this geometric constraint. Mode B implements the physically faithful coupling: interactions pass through FCC interstitial octahedra acting as relays.

### Implementation

Added `--coupling-mode direct|octahedral` flag to `soup_multi_stella.c`. Mode B places one octahedral interstitial buffer (24 Z_3 trits = 1 tile) on each unique FCC edge. For L=4 (32 stellae), this creates 192 octahedral buffers (~5 KB total).

**Mode B cross-interaction algorithm (Prop 0.0.39 §5.2):**

1. Pick stella A and FCC neighbor direction → stella B
2. Find the octahedral interstitial on that edge
3. **Phase 1:** stella_A tile + oct_buffer → VM → writeback to both
4. **Phase 2:** oct_buffer + stella_B tile → VM → writeback to both

Key difference: Mode B does **2 VM executions** per cross event (vs 1 for Mode A). Information must relay through the octahedron to propagate between stellae.

### Systematic Sweep Results

**Configuration:** L=4 (32 stellae), n_sub=100, seeded replicator in stella 0, 5 seeds (42, 123, 456, 789, 1024) per configuration. Epochs: 15000 (cr=0.01), 5000 (cr=0.1), 2000 (cr=1.0).

#### Same Nominal Cross-Rate Comparison

At the same cross_rate, Mode B does 2× the VM work per event. This tests: "given the same number of coupling events, does octahedral mediation change propagation speed?"

| cross_rate | Mode | t_first | t_half (16/32) | t_full (32/32) | oct% |
|------------|------|---------|----------------|----------------|------|
| 0.01 | **A (direct)** | 560 ± 371 | 4060 ± 723 | 7880 ± 2155 | N/A |
| 0.01 | **B (octahedral)** | 440 ± 134 | **3100 ± 1173** | **6740 ± 1322** | 64.9% |
| 0.1 | **A (direct)** | 130 ± 104 | 690 ± 286 | 1010 ± 303 | N/A |
| 0.1 | **B (octahedral)** | 80 ± 45 | **530 ± 115** | 980 ± 168 | 65.3% |
| 1.0 | **A (direct)** | 16 ± 9 | 126 ± 11 | 256 ± 27 | N/A |
| 1.0 | **B (octahedral)** | 16 ± 9 | 122 ± 15 | 246 ± 21 | 63.7% |

**Result:** Mode B is **1.17–1.31× faster at t_half** than Mode A at the same cross_rate, with the advantage most pronounced at low coupling (cr=0.01, 1.31×). At high coupling (cr=1.0), the modes are essentially equivalent.

#### Equalized VM Cost Comparison

Since Mode B does 2 VM executions per cross event, Mode B at cr=X/2 equalizes the total computational work against Mode A at cr=X. This tests: "per unit of VM work, which coupling mode propagates faster?"

| Comparison | Mode A t_half | Mode B t_half | Ratio (A/B) |
|------------|--------------|---------------|-------------|
| A cr=0.01 vs B cr=0.005 | 4060 | 6100 | 0.67× |
| A cr=0.1 vs B cr=0.05 | 690 | 1090 | 0.63× |
| A cr=1.0 vs B cr=0.5 | 126 | 188 | 0.67× |

**Result:** At equalized VM cost, **Mode A is ~1.5× faster** (ratio ~0.67). The octahedral relay imposes a genuine propagation barrier — information must traverse the octahedron to cross between stellae, and the 2-step relay is less efficient per VM execution than direct coupling.

#### Octahedral Colonization

Octahedral interstitials consistently reach ~60–65% replicator occupancy (comparable to the ~55% equilibrium within stellae). This means octahedra are fully colonized by replicators and act as **persistent bridges** — once an octahedron contains a replicator, every subsequent interaction through it can seed the neighbor stella. This "bridge amplification" effect is why Mode B at the same cross_rate is faster than Mode A despite the relay overhead.

### Interpretation

1. **Per-event advantage (same cr):** Mode B is faster because each cross event does 2 VM executions. The octahedron becomes a persistent replicator cache — once colonized, it amplifies every subsequent interaction. This more than compensates for the relay overhead.

2. **Per-VM-work disadvantage (equalized cr):** When we equalize total VM cost, Mode A is ~1.5× more efficient. The 2-step relay (stella→oct→stella) is inherently less efficient than direct transfer (stella→stella) per unit of computational work.

3. **Physical significance:** The octahedral mediation does NOT create a propagation barrier or critical threshold. At all tested cross-rates, Mode B achieves full colonization. The octahedra, rather than filtering or attenuating replicator transfer, become colonized themselves and act as persistent bridges. This is consistent with the face-sharing constraint in Prop 2.5.2b: the global representation label forced by octahedral mediation does not obstruct information transfer — it mediates it.

4. **Connection to Prop 2.5.2b §0.7:** The octahedral cell has $a_R^8$ vs the tetrahedral $a_R^4$ — "more strongly confined" at strong coupling. In the computational model, this manifests as the octahedra reaching ~65% replicator occupancy (slightly higher than stellae at ~55%), suggesting the octahedral geometry may slightly favor replicator persistence.

---

## Inner Octahedron Analysis (CPY01 Redundancy)

**Date:** 2026-03-09

### Question

Does the central octahedron $\mathcal{O} = \text{conv}(T_+) \cap \text{conv}(T_-)$ — the color-neutral core from Prop 0.0.39 §3.4 — require separate modeling in the VM, or is it already implicitly captured by CPY01/CPY10 ($T_+ \leftrightarrow T_-$ information transfer)?

### Approach

Three VM variants tested on identical inputs, differing only in CPY01/CPY10 semantics:

| VM | CPY01 semantics | CPY10 semantics | Physical model |
|----|----------------|-----------------|----------------|
| **VM-A** (standard) | `tape[h1] = tape[h0]` | `tape[h0] = tape[h1]` | Direct $T_+ \to T_-$ transfer |
| **VM-B** (oct-buffer) | `oct_buf = tape[h0]` | `tape[h0] = oct_buf` | Inner octahedron as relay buffer |
| **VM-C** (phase-mix) | `tape[h1] = (tape[h0]+tape[h1])%3` | `tape[h0] = (tape[h0]+tape[h1])%3` | $\mathbb{Z}_3$ phase mixing at singlet core |

### Results

**Test 1: Known replicator copy fidelity (1000 trials per VM)**

The canonical replicator `[ [ CPY+ FWD1 FWD0 ] CPY+ FWD1 FWD0 ] ] FWD1` paired with random food:

| VM | Perfect copies | Avg Hamming distance | Source preserved |
|----|---------------|---------------------|-----------------|
| **VM-A (standard)** | **1000/1000** | **0.00** | 1000/1000 |
| VM-B (oct-buffer) | 0/1000 | 15.94 | 979/1000 |
| VM-C (phase-mix) | 0/1000 | 15.82 | 57/1000 |

VM-A achieves perfect replication in all 1000 trials. VM-B and VM-C completely fail — avg Hamming distance ~16 (of 24 trits) means the target is essentially random.

**Test 2: CPY instruction usage**

The known replicator uses CPY01 ×2, CPY10 ×0. Information flows unidirectionally from h0 (T+ instruction head) to h1 (T- data head). The inner octahedron would sit on this $T_+ \to T_-$ transfer path.

**Test 3: VM-B execution trace**

With deterministic food `[0,1,2,0,1,2,...]`:
- **VM-A:** `src_hamming=0, tgt_hamming=0` — PERFECT COPY
- **VM-B:** `src_hamming=0, tgt_hamming=18` — COPY FAILED. Target = food pattern (unchanged)

**Failure mechanism:** The replicator's copy loop `[CPY01 FWD1 FWD0]` repeatedly executes CPY01. In VM-B, each CPY01 writes to `oct_buf` (overwriting the previous value) but `tape[h1]` is **never written**. The entire copy mechanism is broken because the inner-octahedron buffer has only 1 cell — it cannot relay a multi-trit program.

### Geometric Argument

The inner octahedron is **redundant** with CPY01/CPY10 for five reasons:

1. **Surface vs. volume:** VM tiles live on $\partial\mathcal{S} = \partial T_+ \sqcup \partial T_-$ (boundary surfaces). The inner octahedron is a **volumetric interior** region with no independent surface. It has no tiles to host.

2. **Derived, not independent:** $\mathcal{O} = \text{conv}(T_+) \cap \text{conv}(T_-)$ — its field values are determined by $T_+$ and $T_-$ boundary data via bulk equations. Modeling it separately double-counts existing degrees of freedom.

3. **CPY01/CPY10 = geometric overlap:** The copy operations implement the physical fact that at any $x \in \mathcal{O}$, both $T_+$ and $T_-$ field values coexist. The copy is instantaneous because the overlap region has zero dynamical "thickness" — it's a region of coexistence, not a barrier to traverse.

4. **Color neutrality = transparent copy:** Prop 0.0.39 §3.4 shows $\chi_\text{total} = P(1 + \omega + \omega^2) = 0$ in $\mathcal{O}$ (phase cancellation). If the inner octahedron **added** a phase shift (VM-C), it would not be color-neutral. The singlet condition **requires** unmodified transfer, which is exactly CPY01.

5. **Contrast with FCC interstitial octahedra:** The inter-stella octahedra (Mode B) **are** independent cells with their own surfaces and tiling. The inner octahedron shares its boundary with the 8 corner tetrahedra and has no independent DOF:

| Property | Inner octahedron | FCC interstitial |
|----------|-----------------|------------------|
| Location | Inside stella | Between stellae |
| Surface | None (interior) | Own 8 faces |
| DOF | Derived from $T_\pm$ | Independent |
| In VM | CPY01/CPY10 | Mode B `oct_data` |
| Tiling | Not needed | Has own tiles |

### Conclusion

**The inner octahedron is implicitly and completely captured by CPY01/CPY10.** Separate modeling either:

- **(a)** Is semantically identical to direct copy (if the buffer is transparent), or
- **(b)** Breaks replication (if the buffer adds delay or phase mixing), because it introduces fictional degrees of freedom that don't exist in the physical geometry.

The inner octahedron's role is purely **kinematic** (phase cancellation from $\mathbb{Z}_3$ symmetry). It has no dynamical content beyond what the $T_+$ and $T_-$ surfaces already encode. No modification to the VM instruction set is needed.

**Verification script:** `stella_lang/analyze_inner_octahedron.c`

---

## Error Threshold ↔ Confinement Connection

**Date:** 2026-03-09

### Question

Does the critical mutation rate $\mu_c \approx 0.004$ (Eigen error catastrophe, measured in the 2D soup) have a formal analog in dynamical confinement (Thm 2.5.2)? Specifically: (a) what physical parameter does $\mu_c$ map to, (b) does the error threshold scale with `prog_size` like confinement scales with $N_c$, (c) does the ~35% interaction noise floor have a confinement analog?

### Approach

Three computational experiments using a flat-tile soup (independent tiles, no 2D mesh overlap — faster and cleaner for parameter sweeps):

1. **Experiment (a):** Mutation-rate sweep at multiple `prog_sizes` (24, 30, 36, 42, 48). Same 24-trit replicator core + NOP padding. Tests whether $\mu_c \times L = \text{const}$ (Eigen scaling) or $\mu_c = \text{const}$ (core-determined).

2. **Experiment (b):** Fine-grained sweep around $\mu_c$ for `prog_size=24`. Tests whether the transition is sharp (first-order, like Potts deconfinement) or smooth (crossover, like QCD with light quarks).

3. **Experiment (c):** Zero-mutation equilibrium density at each `prog_size`. Tests the origin of the ~35% noise floor.

**Configuration:** 1,666 tiles, fully seeded with known replicator, 5,000 epochs (equilibrium from seeded state), 3–5 trials per point.

### Results

#### (a) μ_c vs prog_size — Eigen scaling test

| μ | L=24 | L=30 | L=36 | L=42 | L=48 |
|-------|------|------|------|------|------|
| 0.000 | 100% | 100% | 100% | 100% | 100% |
| 0.001 | 90% | 90% | 90% | 88% | 89% |
| 0.002 | 83% | 81% | 83% | 83% | 81% |
| 0.004 | 66% | 66% | 65% | 64% | 64% |
| 0.006 | 50% | 47% | 48% | 46% | 46% |
| 0.008 | 36% | 36% | 31% | 32% | 32% |
| 0.010 | 19% | 22% | 23% | 19% | 16% |
| 0.012 | 0% | 0% | 4% | 0% | 0% |

**Error threshold extraction (density < 10%):**

| prog_size | $\mu_c$ | $\mu_c \times L$ | Eigen $1/L$ |
|-----------|---------|-----------------|-------------|
| 24 | 0.0109 | 0.263 | 0.042 |
| 30 | 0.0111 | 0.333 | 0.033 |
| 36 | 0.0113 | 0.408 | 0.028 |
| 42 | 0.0109 | 0.459 | 0.024 |
| 48 | 0.0107 | 0.515 | 0.021 |

**Key finding: $\mu_c \approx 0.011$ is CONSTANT across all prog_sizes.** The product $\mu_c \times L$ increases linearly from 0.26 to 0.52 — this **rejects** classic Eigen scaling ($\mu_c \sim 1/L$). Instead, $\mu_c$ depends only on the **functional core size** (24 trits), not the total genome length.

**Note:** The flat-tile $\mu_c \approx 0.011$ is higher than the 2D soup's $\mu_c \approx 0.004$. The difference is due to the 2D soup's BFS-patch overlap, which creates additional "interaction noise" that compounds with mutation damage. The flat-tile soup isolates the mutation effect from the geometric noise.

#### (b) Transition shape — sharp or smooth?

Fine sweep around $\mu_c$ for `prog_size=24`, 5 trials per point:

| μ | density | std_dev | $\mu \times L$ | order param |
|--------|---------|---------|---------|-------------|
| 0.0020 | 80.2% | ±2.5% | 0.048 | 1.23 |
| 0.0030 | 72.8% | ±1.8% | 0.072 | 1.12 |
| 0.0040 | 64.4% | ±2.9% | 0.096 | 0.99 |
| 0.0050 | 56.7% | ±3.5% | 0.120 | 0.87 |
| 0.0060 | 47.7% | ±3.4% | 0.144 | 0.73 |
| 0.0070 | 43.0% | ±4.2% | 0.168 | 0.66 |
| 0.0080 | 31.5% | ±7.2% | 0.192 | 0.48 |

**Key finding:** The transition is a **smooth crossover**, not a sharp first-order transition. The order parameter declines gradually over $\mu = 0.002$–$0.012$ (a factor of 6×). The std_dev increases from ±2% to ±7% near the transition, suggesting some critical fluctuations but not the bimodal distribution expected of a first-order transition.

**Comparison with QCD:** The smooth crossover parallels the QCD deconfinement transition with light dynamical quarks ($N_f = 2+1$), which is also a crossover rather than a sharp transition. The 3-state Potts model (Prop 2.5.2c) predicts a first-order transition for pure gauge SU(3), but light quarks smooth it into a crossover — analogous to how the VM's inherent stochasticity smears the error threshold.

#### (c) Zero-mutation noise floor

| prog_size | max_steps | density | noise floor |
|-----------|-----------|---------|-------------|
| 24 | 729 | 100% | 0% |
| 30 | 729 | 100% | 0% |
| 36 | 729 | 100% | 0% |
| 42 | 729 | 100% | 0% |
| 48 | 729 | 100% | 0% |

**Key finding:** The flat-tile soup shows **0% noise floor** at zero mutation across all prog_sizes. The ~35% noise floor from the Phase 1 2D soup results is entirely due to **BFS-patch overlap** on the triangulated mesh — when two overlapping patches are written back, the overlapping sites create interference that degrades some replicators.

**Physical interpretation:** The noise floor is a **geometric** property of the 2D tiling, analogous to how the gluon condensate $\langle G^2 \rangle$ depends on the lattice geometry (and serves as a non-perturbative vacuum property). It is NOT an intrinsic property of the VM instruction set.

### Physics Mapping

| Soup quantity | QCD analog | Role |
|---------------|-----------|------|
| Mutation rate $\mu$ | Temperature $T$ | Disorder parameter |
| $\mu_c$ (error threshold) | $T_c$ (deconfinement) | Critical point |
| Replicator density | String tension $\sigma(T)$ | Order parameter |
| Functional core size (24 trits) | Gauge sector SU(3) | What determines $\mu_c$ / $T_c$ |
| NOP padding (extra trits) | Matter sector (quarks) | Does NOT shift $\mu_c$ / $T_c$ |
| ~35% noise floor (2D) | Gluon condensate $\langle G^2 \rangle$ | Geometric vacuum fluctuation |
| Replicator ($\mu < \mu_c$) | Hadron ($T < T_c$) | Coherent structure |
| Random soup ($\mu > \mu_c$) | QGP ($T > T_c$) | Dissolved state |
| Smooth crossover | QCD crossover ($N_f = 2+1$) | Transition type |

### Key Conclusions

1. **$\mu_c$ maps to $T_c$** (deconfinement temperature). Both are critical scales below which coherent structures persist and above which they dissolve. The mapping $\mu \leftrightarrow T$ identifies mutation as the computational analog of thermal fluctuations.

2. **$\mu_c$ does NOT follow Eigen scaling.** Classic Eigen theory predicts $\mu_c \sim 1/L$ (error threshold inversely proportional to genome length). Our result: $\mu_c \approx 0.011$ independent of $L$ for $L \in [24, 48]$. This is because the replicator has a fixed 24-trit functional core — mutations in NOP padding change the stored genome but the copy loop doesn't reach the padding, so padded sites are effectively neutral... until a mutation changes them from 0 to non-zero, at which point they become part of the "copied" region and introduce errors.

   **However**, the observation that $\mu_c$ is constant despite all sites being deleterious (verified: any mutation anywhere breaks exact replication) indicates that **the error threshold is set by the mutation load per functional core**, not per total genome. This parallels QCD: $T_c$ depends on the gauge sector (SU(3) with $N_c = 3$), not on the total number of matter fields.

3. **The transition is a smooth crossover**, not first-order. This parallels the QCD deconfinement transition with dynamical quarks. The pure-gauge 3-state Potts transition (Prop 2.5.2c) is first-order, suggesting that the VM's stochastic dynamics play the role of "dynamical quarks" in smoothing the transition.

4. **The ~35% noise floor is geometric (2D patch overlap)**, not intrinsic to the VM. This identifies the noise floor as a property of the ∂S tiling geometry, analogous to the gluon condensate being a property of the QCD vacuum. The flat-tile model (no overlap) has zero noise floor.

**Verification script:** `stella_lang/error_threshold_confinement.c`

---

## Critical Nucleus ↔ Phase Transition Connection

**Question:** Does the ~11-tile critical nucleus (0.7% of stella) connect to first-order phase transitions (Thm 4.2.3) or the bag model (Thm 2.1.1)?

**Method:** Four experiments on flat-tile soup (no 2D geometry, isolating pure VM dynamics):
- (a) Critical nucleus survival probability: seed sizes 1–100, 1666 tiles, μ=0.001, 2000 epochs, 10 trials
- (b) Growth dynamics time series: 20 seeded tiles, sampled every 5 epochs, logistic transform
- (c) Minimum population sweep: 50–2000 tiles, fully seeded, μ=0.001, 5000 epochs, 5 trials
- (d) Surface tension: seed N tiles, run 1 epoch, measure survival rate

### Results

#### (a) Critical Nucleus as Critical Droplet

| N_seed | Survived | Avg Final % | Interpretation |
|--------|----------|-------------|----------------|
| 1 | 2/10 | 18.2% | Near-critical |
| 2 | 7/10 | 62.6% | Supercritical (some fail) |
| 3 | 7/10 | 63.6% | Supercritical (some fail) |
| 5 | 9/10 | 81.5% | Supercritical (some fail) |
| 7 | 10/10 | 90.1% | Supercritical |
| 10–100 | 10/10 | ~89% | Supercritical |

**Critical nucleus in flat-tile mode: N_c ≈ 1–2 tiles** (50% survival between N=1 and N=2). This is much smaller than the 2D soup value (~11 tiles) because flat tiles have no geometric surface effects — every interaction has equal probability of success. The 2D critical nucleus is inflated by patch-overlap losses (the same mechanism causing the ~35% noise floor).

The nucleation analogy holds: below N_c, seeded replicators are destroyed by random interactions faster than they replicate. Above N_c, they grow to fill the population. This maps directly to classical nucleation theory: ΔG(R) = −ΔG_v · V + σ · A, where subcritical droplets (R < R_c) shrink and supercritical droplets (R > R_c) grow.

#### (b) Growth Dynamics: Nucleation-and-Growth (NOT Spinodal)

| Phase | Epochs | Density | Behavior |
|-------|--------|---------|----------|
| Lag | 0–5 | 0.7% | Seed establishes, some tiles lost |
| Exponential | 5–25 | 7%→36% | Rapid growth, ln(ρ/(K−ρ)) roughly linear |
| Saturation | 25–50 | 36%→88% | Logistic slowdown |
| Equilibrium | 50+ | ~90% ± 3% | Stochastic fluctuations |

The growth follows a **logistic S-curve** with three distinct phases: lag, exponential, saturation. This is the signature of **nucleation-and-growth**, NOT spinodal decomposition. Key distinctions:

- **Nucleation-and-growth** (observed): Lag phase → exponential → saturation. Requires supercritical seed. Metastable initial state (random soup is "locally stable" but globally unfavorable).
- **Spinodal decomposition** (not observed): No lag phase. Immediate amplification everywhere simultaneously. Unstable initial state.

The random soup is a **metastable** state — it persists indefinitely without perturbation (no spontaneous replicators at μ=0 in flat tiles). A supercritical seed is needed to trigger the transition, exactly as in first-order phase transitions (Thm 4.2.3).

**Flat-tile equilibrium is ~90%** (vs ~55% in 2D soup). The difference is entirely explained by geometric patch-overlap losses in 2D.

#### (c) Minimum Population ↔ Confinement Volume

| N_tiles | Survived | Avg Density | Interpretation |
|---------|----------|-------------|----------------|
| 50 | 4/5 | 74.0% | Marginal |
| 100 | 5/5 | 92.6% | Confined (maintained) |
| 200–2000 | 5/5 | 83–89% | Confined (maintained) |

**Minimum maintenance population: ~50–100 tiles.** Below ~50, replicators go extinct even when fully seeded. This is the minimum "confinement volume" — the population must be large enough that replicators encounter each other frequently enough to maintain coherence against mutation-driven decay.

The bag model comparison (Thm 2.1.1):
- MIT Bag: R_eq ≈ 1.0 fm → V_bag ≈ 4.2 fm³ (proton equilibrium volume)
- CG stella: R_stella = 0.448 fm → V_stella ≈ 0.38 fm³
- Ratio: V_bag/V_stella ≈ 11 — a single stella is one "parton" of a hadron

The distinction between **maintenance minimum** (~50–100 tiles) and **emergence minimum** (~1,666 tiles from earlier 2D results) maps to: bag volume (equilibrium confinement) vs. critical bubble volume (nucleation from deconfined phase).

#### (d) Surface Tension

| N_seed | Loss Rate | Loss/√N |
|--------|-----------|---------|
| 5 | 0.320 | 0.72 |
| 10 | 0.290 | 0.92 |
| 50 | 0.324 | 2.29 |
| 200 | 0.270 | 3.81 |
| 500 | 0.204 | 4.56 |

In flat-tile soup, ALL tiles are "surface" tiles (well-mixed). The loss rate decreases with N because the fraction of non-replicator interaction partners shrinks: loss_rate ∝ (1 − N/N_total). This is consistent with an effective surface tension where the "surface energy" cost decreases relative to "bulk energy" gain as the cluster grows.

### Three Structural Parallels

1. **Critical nucleus ↔ critical bubble (Thm 4.2.3):** The critical nucleus N_c is the analog of the critical bubble radius R_c. Below: cluster shrinks. Above: cluster grows. The free energy functional F(N) = −Δf·N + σ_eff·√N mirrors the nucleation barrier ΔG(R) = −ΔG_v·(4π/3)R³ + σ·4πR².

2. **Logistic growth ↔ nucleation-and-growth (Phase 4.5):** Growth follows a logistic S-curve with lag, exponential, and saturation phases. This is nucleation-and-growth from a metastable state, NOT spinodal decomposition. The random soup is metastable (like a supercooled liquid), and the replicator seed triggers the phase transition.

3. **Minimum population ↔ bag model volume (Thm 2.1.1):** The maintenance minimum (~50–100 tiles) is the analog of the bag model's equilibrium radius. Below this volume, the replicator "phase" cannot be sustained. The emergence minimum (~1,666 tiles) is larger because it requires spontaneous nucleation — analogous to the critical bubble being larger than the equilibrium bag.

### Key Finding: 2D vs Flat-Tile Critical Nucleus

The 2D soup critical nucleus (~11 tiles) is ~5–10× larger than the flat-tile critical nucleus (~1–2 tiles). This inflation is caused by geometric surface effects (BFS-patch overlap), which destroy ~35% of replicator information per interaction regardless of mutation rate. The "geometric surface tension" in 2D is a physical effect of the triangulated ∂S topology — it represents the cost of embedding discrete Z₃ programs on a curved surface.

**Verification script:** `stella_lang/critical_nucleus_phase_transition.c`

---

## Next Steps

- [x] Demonstrate self-replication on 2D stella geometry
- [x] Identify population size as the critical parameter
- [x] Compare emergence timescales between 1D and 2D
- [x] Complete n157 run (4,108 tiles) — replicators found at epoch 9.65M
- [x] Characterize replicator programs — same universal core as 1D
- [x] Implement multi-stella FCC lattice simulation (soup_multi_stella.c)
- [x] Demonstrate inter-stella replicator propagation (all 4/4 stellae colonized)
- [x] Larger FCC lattice (L=4, 32 stellae) — all 32/32 colonized at ~56%, emergence at 80K
- [x] Cross-rate sweep at fixed L=4: vary cross_rate over {0.01, 0.1, 1.0, 10.0}. **COMPLETE.** No critical threshold — all cross_rates achieve 32/32 colonization. See "Cross-Rate Sweep Results" section.
- [x] L=8 FCC lattice — **NOT NEEDED.** All tested cross_rates (0.01-10.0) achieve 32/32 colonization. No propagation gradient to measure at L=8.
- [x] Wavefront propagation speed measurement. **COMPLETE.** Seeded-replicator experiments with census every 10-100 epochs. Propagation times: 70 epochs (cr=10.0) to 2,500 epochs (cr=0.01). Scaling is √(cross_rate) — diffusive, not ballistic. Mixed regime: both transfer probability and local amplification contribute. See "Wavefront Propagation Speed" section.
- [x] RNG decoupling fix: separated `metrics_rng` from `master_rng` so measurement parameters no longer perturb dynamics. See "RNG Decoupling Fix" section.
- [x] **Per-stella wavefront tracking (confirm diffusive mechanism).** **COMPLETE.** Added FCC BFS distance computation and per-distance-shell census output (`WAVEFRONT: d0=X/Y d1=X/Y ...`). Confirmed stochastic diffusion: wavefront is NOT hop-by-hop (d=2 colonizes before d=1 complete), long-range leaking occurs via multiple FCC paths, and first-arrival time scales roughly linearly with distance while completion time depends on shell size. See "Per-Stella Wavefront Tracking" section.
- [x] **Seed location dependence.** **COMPLETE.** Tested 7 seed locations (stellae 0, 5, 10, 15, 21, 25, 31) at cr=0.01. All have identical FCC distance structure (1 at d=0, 12 at d=1, 18 at d=2, 1 at d=3) confirming periodic translation invariance. Propagation times: 2,000–3,400 epochs (mean ~2,500, ±30% stochastic variation from different per-stella RNG neighborhoods). At cr=1.0, stellae 0 and 15 both reach 32/32 at epoch 230. No systematic dependence on seed location.
- [x] **Very low cross-rate (propagation failure threshold).** **COMPLETE.** Implemented fractional probabilistic coupling to test sub-integer interaction rates (cr=0.0003 to 0.01). No sharp failure threshold found — propagation continues at all tested rates, just slower. Scaling transitions from √(cr) (diffusive, high coupling) to ~1/cr (transfer-limited, low coupling) around cr ≈ 0.01–0.1. At cr=0.0003 (0.01 interactions/epoch), 19/32 stellae colonized in 100K epochs — still spreading. See "Very Low Cross-Rate Experiments" section.
- [x] **Single-tile seeding (measure intra-stella amplification time).** **COMPLETE.** Implemented `--seed-single-tile` and `--seed-n-tiles N` modes. Key findings: (1) Single tile never amplifies (0/10 trials) — critical nucleus exists. (2) Critical nucleus is ~11 tiles (0.7% of stella). (3) Amplification time τ_amplify ≈ 150–200 epochs, independent of seed size above threshold. (4) Logistic growth from seed to ~55% equilibrium. (5) τ_amplify quantitatively explains the scaling regime transition in inter-stella propagation. See "Intra-Stella Amplification" section.
- [x] Octahedral mediation experiment: implement Mode B inter-stella coupling where interactions pass through FCC interstitial octahedra (Prop 0.0.39 §5.2, Prop 2.5.2b §0.7) rather than direct stella-to-stella tile pairing. Octahedron surfaces tiled with Z_3 values; inter-stella VM execution runs stella-tile + octahedron-tile pairs. Compare replicator propagation rate and critical cross_rate against Mode A (direct coupling). **COMPLETE.** No propagation barrier — octahedra become colonized (~65%) and act as persistent bridges. Per-event: Mode B 1.17–1.31× faster (2 VM execs/event). Per-VM-work: Mode A ~1.5× more efficient (relay overhead). See "Octahedral Mediation Experiment" section.
- [x] Inner octahedron analysis: verify that the central octahedron (conv(T+) ∩ conv(T-), the color-neutral core from Prop 0.0.39) is already implicitly captured by CPY01 (T+ -> T- information transfer). Document whether separate modeling of the inner octahedron affects replication dynamics or is redundant with the existing VM instruction set. **COMPLETE.** Inner octahedron is REDUNDANT with CPY01/CPY10. Known replicator test: VM-A (direct copy) 1000/1000 perfect copies; VM-B (oct-buffer) 0/1000; VM-C (phase-mix) 0/1000. The inner octahedron has no independent surface tiles (it's volumetric interior), its field values are derived from T± boundary data, and CPY01's direct transfer IS the geometric realization of conv(T+) ∩ conv(T-) ≠ ∅. See "Inner Octahedron Analysis" section.
- [x] **Error threshold ↔ confinement connection:** Investigate whether the critical mutation rate μ_c ≈ 0.004 (Eigen error catastrophe) has a formal analog in dynamical confinement (Thm 2.5.2). **COMPLETE.** (a) μ_c maps to temperature T (disorder parameter), with μ_c ↔ T_c and replicator density ↔ string tension σ(T). (b) μ_c ≈ 0.011 is CONSTANT across prog_sizes 24–48 — does NOT follow Eigen scaling (μ_c × L ≠ const). Error threshold depends on functional core size (24 trits), not total genome. This parallels QCD: confinement depends on gauge sector SU(3), not total DOF count. (c) The ~35% noise floor is a GEOMETRIC property of 2D patch overlap, not intrinsic to VM — flat tiles show 0% noise at μ=0. Transition is smooth crossover (not first-order), analogous to QCD with light quarks. See "Error Threshold ↔ Confinement" section.
- [x] **Critical nucleus ↔ phase transition connection:** **COMPLETE.** (a) Critical nucleus IS a critical droplet: flat-tile N_c ≈ 1–2 tiles, 2D N_c ≈ 11 tiles (inflated by geometric surface effects). Below N_c: cluster shrinks; above: grows to ~90% (flat) or ~55% (2D). Maps to nucleation barrier ΔG(R) in Thm 4.2.3. (b) Growth is nucleation-and-growth (logistic S-curve with lag phase), NOT spinodal decomposition. Random soup is metastable, not unstable. (c) Minimum maintenance population ~50–100 tiles (bag model analog); minimum emergence population ~1,666 tiles (critical bubble analog, includes nucleation cost). See "Critical Nucleus ↔ Phase Transition Connection" section.
- [ ] Phase 2: Statistical mechanics (Potts model) analysis of the tile dynamics
