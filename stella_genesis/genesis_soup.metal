/* genesis_soup.metal — Metal compute kernels for Genesis dual-mesh simulation
 *
 * Port of genesis_soup.c to GPU using the StellaLang double-buffered snapshot
 * architecture. Five kernels handle the Genesis epoch pipeline:
 *   1. genesis_vm_couple — VM execution + geometric coupling (per tile)
 *   2. genesis_kuramoto — Kuramoto phase synchronization (per site)
 *   3. genesis_mass_precompute — phase gradient + mass density (per site)
 *   4. genesis_energy_count — atomic color reduction (per site)
 *   5. genesis_mutate — random trit mutations (per tile)
 *
 * Buffer layout:
 *   [0]  readData      — snapshot trits: [T+ (n)] [T- (n)]
 *   [1]  writeData     — live write trits: same layout
 *   [2]  tileSites     — [n_tiles * prog_size] uint32 site indices
 *   [3]  tileSize      — [n_tiles] uint32 actual tile sizes
 *   [4]  tileNbr       — [n_tiles * 8] uint32 neighbor tile IDs
 *   [5]  tileNbrCount  — [n_tiles] uint32 neighbor counts
 *   [6]  rngStates     — [n_tiles * 4] uint64 xoshiro256** per tile
 *   [7]  params        — GenesisParams struct
 *   [8]  phaseRead     — snapshot phases: [T+ (n floats)] [T- (n floats)]
 *   [9]  phaseWrite    — live write phases: same layout
 *   [10] pressure      — [pp_tp (n)] [pm_tp (n)] [pp_tm (n)] [pm_tm (n)] floats
 *   [11] meshNbr       — [T+ n*MAX_NBR] [T- n*MAX_NBR] uint32 neighbor indices
 *   [12] meshNbrCount  — [T+ n] [T- n] uint32 neighbor counts
 *   [13] massData      — [T+ n] [T- n] floats: mass density m(x)
 *   [14] dominantColor — [T+ n] [T- n] uint8: argmax_c P_c(x)
 *   [15] energyCounts  — 6 × uint32: [R,G,B] counts for T+ and T-
 *   [16] pressureColor — [c0_tp (n)] [c1_tp (n)] [c2_tp (n)] [c0_tm..] floats
 */

#include <metal_stdlib>
using namespace metal;

/* ── Shared parameter struct (must match genesis_soup_metal.m) ─────── */

struct GenesisParams {
    uint n_sites;           /* sites per tetrahedron */
    uint n_tiles;           /* total tiles (T+ and T-) */
    uint n_tiles_per;       /* tiles per tetrahedron (n_tiles/2) */
    uint prog_size;         /* sites per tile (24) */
    uint max_steps;         /* VM instruction limit (729) */
    float mutation_rate;
    float coupling_strength;
    float chirality;
    uint chirality_mode;
    uint instr_mode;        /* 0=classic, 1=enhanced, 2=write */
    uint color_pressure;    /* 0=max vertex, 1=per-color gate */
    float phase_lock;       /* Kuramoto K */
    uint kuramoto_mode;     /* 0=majority, 1=full Kuramoto */
    float energy_lambda;
    uint mass_mode;
    float mass_couple;
    float mass_kuramoto;
    float mass_geo;
    uint n_interactions;    /* tile ops dispatched per epoch */
    uint sub_round_idx;     /* RNG diversification */
    float epsilon;          /* pressure regularization */
    uint max_nbr;           /* max neighbors per site (8) */
};

/* ── Opcodes (Z₃ × Z₃ encoding, matches genesis_soup.c) ──────────── */

constant uint OP_NOP   = 0;
constant uint OP_ROT   = 1;
constant uint OP_DROT  = 2;
constant uint OP_FWD   = 3;
constant uint OP_BCK   = 4;
constant uint OP_OPEN  = 5;
constant uint OP_CLOSE = 6;
constant uint OP_SENSE = 7;
constant uint OP_COUPLE= 8;

/* ── RNG (xoshiro256**, same as StellaLang Metal) ─────────────────── */

static inline ulong rotl64(ulong x, int k) {
    return (x << k) | (x >> (64 - k));
}

static inline ulong rng_next(thread ulong *s) {
    ulong result = rotl64(s[1] * 5, 7) * 9;
    ulong t = s[1] << 17;
    s[2] ^= s[0]; s[3] ^= s[1]; s[1] ^= s[2]; s[0] ^= s[3];
    s[2] ^= t;
    s[3] = rotl64(s[3], 45);
    return result;
}

static inline uint rng_int_n(thread ulong *s, uint n) {
    return (uint)(rng_next(s) % (ulong)n);
}

static inline float rng_float_val(thread ulong *s) {
    return (float)(rng_next(s) >> 40) / 16777216.0f;
}

static void rng_seed_from(thread ulong *s, ulong base) {
    /* Splitmix64 seeding */
    for (int i = 0; i < 4; i++) {
        base += 0x9e3779b97f4a7c15UL;
        ulong z = base;
        z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9UL;
        z = (z ^ (z >> 27)) * 0x94d049bb133111ebUL;
        s[i] = z ^ (z >> 31);
    }
}

/* ── Tile scatter-gather ──────────────────────────────────────────── */

static void tile_read(const device uint8_t *data, const device uint *tile_sites,
                      uint tile_idx, uint prog_size, uint sz,
                      thread uint8_t *buf) {
    uint base = tile_idx * prog_size;
    for (uint i = 0; i < sz && i < prog_size; i++)
        buf[i] = data[tile_sites[base + i]];
    for (uint i = sz; i < prog_size; i++)
        buf[i] = 0;
}

static void tile_write(device uint8_t *data, const device uint *tile_sites,
                       uint tile_idx, uint prog_size, uint sz,
                       thread uint8_t *buf) {
    uint base = tile_idx * prog_size;
    for (uint i = 0; i < sz && i < prog_size; i++)
        data[tile_sites[base + i]] = buf[i];
}

/* ── VM execution (Genesis G1 opcodes) ────────────────────────────── */

static void genesis_vm(thread uint8_t *tape, uint tape_len, uint max_steps,
                       uint instr_mode, thread float *pressure_ratio,
                       thread uint8_t *other_tape, uint other_len,
                       uint color_pressure, thread float *pressure_ratio_color,
                       uint prog_size) {
    int ip = 0;
    int h = 0;
    uint steps = 0;

    while (steps < max_steps && ip + 1 < (int)tape_len) {
        uint op = (uint)tape[ip] * 3 + (uint)tape[ip + 1];

        if (op == OP_NOP) {
            /* no-op */
        } else if (op == OP_SENSE) {
            if (instr_mode >= 1) {
                float r = pressure_ratio[h];
                if (r > 0.6667f) tape[h] = 0;
                else if (r > 0.3333f) tape[h] = 1;
                else tape[h] = 2;
            }
        } else if (op == OP_COUPLE) {
            if (instr_mode == 2 && h < (int)other_len) {
                /* WRITE mode: copy tape[h] to other_tape[h] if pressure allows */
                float wr = pressure_ratio[h];
                if (color_pressure) {
                    float wr_c = pressure_ratio_color[(uint)tape[h] * prog_size + (uint)h];
                    if (wr_c > wr) wr = wr_c;
                }
                if (wr > 0.5f)
                    other_tape[h] = tape[h];
            }
        } else if (op == OP_ROT) {
            tape[h] = tape[h] < 2 ? tape[h] + 1 : 0;
        } else if (op == OP_DROT) {
            tape[h] = tape[h] > 0 ? tape[h] - 1 : 2;
        } else if (op == OP_FWD) {
            h = (h + 1) % (int)tape_len;
        } else if (op == OP_BCK) {
            h = ((h - 1) + (int)tape_len) % (int)tape_len;
        } else if (op == OP_OPEN) {
            if (tape[h] == 0) {
                int depth = 1, pos = ip + 2;
                while (depth > 0 && pos + 1 < (int)tape_len) {
                    uint inner = (uint)tape[pos] * 3 + (uint)tape[pos + 1];
                    if (inner == OP_OPEN) depth++;
                    else if (inner == OP_CLOSE) depth--;
                    pos += 2;
                }
                if (depth == 0) ip = pos - 2;
            }
        } else if (op == OP_CLOSE) {
            if (tape[h] != 0) {
                int depth = 1, pos = ip - 2;
                while (depth > 0 && pos >= 0) {
                    uint inner = (uint)tape[pos] * 3 + (uint)tape[pos + 1];
                    if (inner == OP_CLOSE) depth++;
                    else if (inner == OP_OPEN) depth--;
                    pos -= 2;
                }
                if (depth == 0) ip = pos + 2;
            }
        }

        ip += 2;
        steps++;
    }
}

/* ══════════════════════════════════════════════════════════════════════
 * Kernel 1: genesis_vm_couple — VM execution + geometric coupling
 *
 * Grid: n_interactions threads
 * Each thread picks a random tile, executes VM, then applies
 * geometric coupling at each tile site.
 * ═════════════════════════════════════════════════════════════════════ */

kernel void genesis_vm_couple(
    const device uint8_t     *readData       [[buffer(0)]],
    device uint8_t           *writeData      [[buffer(1)]],
    const device uint        *tileSites      [[buffer(2)]],
    const device uint        *tileSize       [[buffer(3)]],
    const device uint        *tileNbr        [[buffer(4)]],
    const device uint        *tileNbrCount   [[buffer(5)]],
    device ulong             *rngStates      [[buffer(6)]],
    constant GenesisParams   &params         [[buffer(7)]],
    const device float       *phaseRead      [[buffer(8)]],
    device float             *phaseWrite     [[buffer(9)]],
    const device float       *pressure       [[buffer(10)]],
    const device uint8_t     *dominantColor  [[buffer(14)]],
    const device float       *pressureColor  [[buffer(16)]],
    const device float       *massData       [[buffer(13)]],
    uint tid [[thread_position_in_grid]])
{
    if (tid >= params.n_interactions) return;

    uint n = params.n_sites;
    uint ps = params.prog_size;
    uint n_tp = params.n_tiles_per;  /* tiles 0..n_tp-1 are T+, n_tp..2*n_tp-1 are T- */

    /* RNG: seed from per-tile state + tid + sub_round for diversity */
    ulong rng[4];
    ulong base_seed = rngStates[(tid % params.n_tiles) * 4];
    rng_seed_from(rng, base_seed ^ ((ulong)tid * 0x517cc1b727220a95UL)
                                  ^ ((ulong)params.sub_round_idx * 0x9e3779b97f4a7c15UL));

    /* Pick a random tile */
    uint tile_a = rng_int_n(rng, params.n_tiles);
    bool is_tp = tile_a < n_tp;
    uint local_tile = is_tp ? tile_a : tile_a - n_tp;
    uint sz = tileSize[local_tile + (is_tp ? 0 : n_tp)];

    /* Scatter-gather read tile data from snapshot */
    uint8_t work_own[48];   /* max prog_size = 24, but allow headroom */
    uint8_t work_other[48];
    float pr[48];           /* pressure ratios */
    float pr_color[48 * 3]; /* per-color pressure ratios */

    /* Read sites */
    uint tile_base = (is_tp ? local_tile : (local_tile + n_tp)) * ps;
    for (uint i = 0; i < sz && i < ps; i++) {
        uint site = tileSites[tile_base + i];
        work_own[i] = readData[is_tp ? site : site + n];
        work_other[i] = readData[is_tp ? site + n : site];

        /* Pressure ratios for SENSE/WRITE gating */
        float pp_own, pm_own;
        if (is_tp) {
            pp_own = pressure[site];           /* pp_at_tp */
            pm_own = pressure[site + n];       /* pm_at_tp */
        } else {
            pp_own = pressure[site + 2*n];     /* pp_at_tm = P- at T- */
            pm_own = pressure[site + 3*n];     /* pm_at_tm = P+ at T- ... */
            /* For T-, "own" pressure is pm_at_tm, "other" is pp_at_tm */
            pp_own = pressure[site + 3*n];     /* pm_at_tm */
            pm_own = pressure[site + 2*n];     /* pp_at_tm */
        }
        float sum = pp_own + pm_own;
        pr[i] = sum > 1e-10f ? pp_own / sum : 0.5f;

        /* Per-color pressure ratios */
        if (params.color_pressure) {
            for (uint c = 0; c < 3; c++) {
                uint color_off = is_tp ? c * n + site : (c + 3) * n + site;
                pr_color[c * ps + i] = pressureColor[color_off];
            }
        }
    }

    /* VM execution: T+ tape reads T- (or vice versa) under snapshot */
    /* Save other tape for snapshot-correct cross-execution */
    uint8_t save_other[48];
    for (uint i = 0; i < sz; i++) save_other[i] = work_other[i];

    genesis_vm(work_own, sz, params.max_steps, params.instr_mode,
               pr, work_other, sz, params.color_pressure, pr_color, ps);

    /* Capture writes from own→other */
    uint8_t own_writes[48];
    for (uint i = 0; i < sz; i++) own_writes[i] = work_other[i];

    /* Restore other and execute other's VM against snapshot of own */
    for (uint i = 0; i < sz; i++) work_other[i] = save_other[i];
    uint8_t save_own[48];
    for (uint i = 0; i < sz; i++) save_own[i] = work_own[i];
    /* Re-read own from snapshot (other's VM sees original own) */
    for (uint i = 0; i < sz && i < ps; i++) {
        uint site = tileSites[tile_base + i];
        work_own[i] = readData[is_tp ? site : site + n];
    }

    /* Compute other's pressure ratios */
    float pr_other[48];
    float pr_color_other[48 * 3];
    for (uint i = 0; i < sz && i < ps; i++) {
        uint site = tileSites[tile_base + i];
        float pp_oth, pm_oth;
        if (is_tp) {
            /* Other is T-: own pressure is pm_at_tm */
            pm_oth = pressure[site + 3*n];
            pp_oth = pressure[site + 2*n];
        } else {
            pp_oth = pressure[site];
            pm_oth = pressure[site + n];
        }
        float sum = pp_oth + pm_oth;
        pr_other[i] = sum > 1e-10f ? pp_oth / sum : 0.5f;

        if (params.color_pressure) {
            for (uint c = 0; c < 3; c++) {
                uint color_off = is_tp ? (c + 3) * n + site : c * n + site;
                pr_color_other[c * ps + i] = pressureColor[color_off];
            }
        }
    }

    genesis_vm(work_other, sz, params.max_steps, params.instr_mode,
               pr_other, work_own, sz, params.color_pressure, pr_color_other, ps);

    /* Merge: restore own from its VM execution, apply own's writes to other */
    for (uint i = 0; i < sz; i++) work_own[i] = save_own[i];
    for (uint i = 0; i < sz; i++) {
        if (own_writes[i] != save_other[i])
            work_other[i] = own_writes[i];
    }

    /* Write back VM results (trits + phases) */
    float THIRD_2PI = 2.0f * M_PI_F / 3.0f;
    for (uint i = 0; i < sz && i < ps; i++) {
        uint site = tileSites[tile_base + i];
        uint own_off  = is_tp ? site : site + n;
        uint other_off = is_tp ? site + n : site;
        writeData[own_off]  = work_own[i];
        writeData[other_off] = work_other[i];
        phaseWrite[own_off]  = (float)work_own[i] * THIRD_2PI;
        phaseWrite[other_off] = (float)work_other[i] * THIRD_2PI;
    }

    /* ── Geometric coupling (pressure-gated T+↔T- transfer) ── */
    for (uint i = 0; i < sz && i < ps; i++) {
        uint site = tileSites[tile_base + i];

        /* T+ → T- direction */
        float pp_tp = pressure[site];
        float pm_tp = pressure[site + n];
        float delta_tp = pp_tp - pm_tp;
        if (delta_tp > 0.0f) {
            float sum_tp = pp_tp + pm_tp;
            float prob = params.coupling_strength * (delta_tp / sum_tp);
            if (params.mass_geo > 0.0f)
                prob *= (1.0f + params.mass_geo * massData[site]);
            if (rng_float_val(rng) < prob) {
                uint8_t trit = readData[site];
                writeData[site + n] = trit;
                phaseWrite[site + n] = (float)trit * THIRD_2PI;
            }
        }

        /* T- → T+ direction */
        float pm_tm = pressure[site + 3*n];
        float pp_tm = pressure[site + 2*n];
        float delta_tm = pm_tm - pp_tm;
        if (delta_tm > 0.0f) {
            float sum_tm = pm_tm + pp_tm;
            float prob = params.coupling_strength * (delta_tm / sum_tm);
            if (params.mass_geo > 0.0f)
                prob *= (1.0f + params.mass_geo * massData[site + n]);
            if (rng_float_val(rng) < prob) {
                uint8_t trit = readData[site + n];
                writeData[site] = trit;
                phaseWrite[site] = (float)trit * THIRD_2PI;
            }
        }
    }
}

/* ══════════════════════════════════════════════════════════════════════
 * Kernel 2: genesis_kuramoto — Phase synchronization
 *
 * Grid: n_sites threads (covers both T+ and T-)
 * Each thread handles one site on one surface.
 * Dispatch twice per surface, or once with n_sites covering one surface.
 * Re-dispatch with phase blit between sub-steps for GG2b.
 * ═════════════════════════════════════════════════════════════════════ */

kernel void genesis_kuramoto(
    const device float       *phaseRead     [[buffer(8)]],
    device float             *phaseWrite    [[buffer(9)]],
    device uint8_t           *writeData     [[buffer(1)]],
    constant GenesisParams   &params        [[buffer(7)]],
    const device float       *pressure      [[buffer(10)]],
    const device uint        *meshNbr       [[buffer(11)]],
    const device uint        *meshNbrCount  [[buffer(12)]],
    const device float       *massData      [[buffer(13)]],
    uint tid [[thread_position_in_grid]])
{
    uint n = params.n_sites;
    uint max_nbr = params.max_nbr;

    /* Thread covers 2*n sites: [0..n-1] = T+, [n..2n-1] = T- */
    if (tid >= 2 * n) return;

    bool is_tp = tid < n;
    uint site = is_tp ? tid : tid - n;

    /* Pressure ratio — only active in blocked zone (P_ratio < 0.5) */
    float pp, pm;
    if (is_tp) {
        pp = pressure[site];
        pm = pressure[site + n];
    } else {
        pp = pressure[site + 3*n];  /* pm_at_tm = own for T- */
        pm = pressure[site + 2*n];  /* pp_at_tm = other for T- */
    }
    float sum_p = pp + pm;
    float p_ratio = sum_p > 1e-10f ? pp / sum_p : 0.5f;

    if (p_ratio >= 0.5f) return;  /* vertex zone — coupling handles coherence */

    /* Mesh neighbor lookup */
    uint nbr_off = is_tp ? 0 : n * max_nbr;
    uint cnt_off = is_tp ? 0 : n;
    uint nn = meshNbrCount[cnt_off + site];
    if (nn == 0) return;

    /* Phase read offset */
    uint phase_off = is_tp ? 0 : n;

    /* Kuramoto coupling force: dφ = K/N × Σ sin(φ_j - φ_i) */
    float my_phase = phaseRead[phase_off + site];
    float force = 0.0f;
    for (uint j = 0; j < nn && j < max_nbr; j++) {
        uint nb = meshNbr[nbr_off + site * max_nbr + j];
        force += sin(phaseRead[phase_off + nb] - my_phase);
    }

    float K = params.phase_lock;
    if (params.mass_kuramoto > 0.0f) {
        uint mass_off = is_tp ? 0 : n;
        K *= (1.0f + params.mass_kuramoto * massData[mass_off + site]);
    }

    float dphi = K * force / (float)nn;
    float new_phase = my_phase + dphi;

    /* Wrap to [0, 2π) */
    float TWO_PI = 2.0f * M_PI_F;
    new_phase = fmod(new_phase, TWO_PI);
    if (new_phase < 0.0f) new_phase += TWO_PI;

    phaseWrite[phase_off + site] = new_phase;

    /* Quantize to nearest Z₃ trit */
    float THIRD = TWO_PI / 3.0f;
    int new_trit = ((int)round(new_phase / THIRD)) % 3;
    uint data_off = is_tp ? site : site + n;
    writeData[data_off] = (uint8_t)new_trit;
}

/* ══════════════════════════════════════════════════════════════════════
 * Kernel 3: genesis_mass_precompute — Phase gradient + mass density
 *
 * Grid: 2 * n_sites threads (T+ and T-)
 * ═════════════════════════════════════════════════════════════════════ */

kernel void genesis_mass_precompute(
    const device float       *phaseRead     [[buffer(8)]],
    constant GenesisParams   &params        [[buffer(7)]],
    const device float       *pressure      [[buffer(10)]],
    const device uint        *meshNbr       [[buffer(11)]],
    const device uint        *meshNbrCount  [[buffer(12)]],
    device float             *massData      [[buffer(13)]],
    uint tid [[thread_position_in_grid]])
{
    uint n = params.n_sites;
    uint max_nbr = params.max_nbr;
    if (tid >= 2 * n) return;

    bool is_tp = tid < n;
    uint site = is_tp ? tid : tid - n;

    uint nbr_off = is_tp ? 0 : n * max_nbr;
    uint cnt_off = is_tp ? 0 : n;
    uint phase_off = is_tp ? 0 : n;
    uint nn = meshNbrCount[cnt_off + site];

    /* Phase gradient: mean |sin(φ_j - φ_i)| over neighbors */
    float grad = 0.0f;
    float my_phase = phaseRead[phase_off + site];
    for (uint j = 0; j < nn && j < max_nbr; j++) {
        uint nb = meshNbr[nbr_off + site * max_nbr + j];
        grad += fabs(sin(phaseRead[phase_off + nb] - my_phase));
    }
    grad = nn > 0 ? grad / (float)nn : 0.0f;

    /* VEV field: v_χ(x) = P_ratio (pressure asymmetry as order parameter) */
    float pp, pm;
    if (is_tp) {
        pp = pressure[site];
        pm = pressure[site + n];
    } else {
        pp = pressure[site + 3*n];
        pm = pressure[site + 2*n];
    }
    float sum_p = pp + pm;
    float vchi = sum_p > 1e-10f ? fabs(pp - pm) / sum_p : 0.0f;

    /* Mass density: m(x) = g_χ · v_χ(x) · |∇φ(x)|
     * MASS_PREFACTOR = g_chi * w0 / L ≈ 0.1 (from genesis_soup.c) */
    float MASS_PREFACTOR = 0.1f;
    float mass = MASS_PREFACTOR * vchi * grad;

    uint mass_off = is_tp ? 0 : n;
    massData[mass_off + site] = mass;
}

/* ══════════════════════════════════════════════════════════════════════
 * Kernel 4: genesis_energy_count — Atomic color counting
 *
 * Grid: 2 * n_sites threads
 * Each thread atomically increments the count for its trit's color.
 * Results in energyCounts[0..5]: [R_tp, G_tp, B_tp, R_tm, G_tm, B_tm]
 * ═════════════════════════════════════════════════════════════════════ */

kernel void genesis_energy_count(
    const device uint8_t     *writeData     [[buffer(1)]],
    constant GenesisParams   &params        [[buffer(7)]],
    device atomic_uint       *energyCounts  [[buffer(15)]],
    uint tid [[thread_position_in_grid]])
{
    uint n = params.n_sites;
    if (tid >= 2 * n) return;

    uint8_t trit = writeData[tid];
    uint offset = (tid < n) ? trit : 3 + trit;
    atomic_fetch_add_explicit(&energyCounts[offset], 1, memory_order_relaxed);
}

/* ══════════════════════════════════════════════════════════════════════
 * Kernel 5: genesis_mutate — Random trit mutations
 *
 * Grid: n_tiles threads (one per tile)
 * ═════════════════════════════════════════════════════════════════════ */

kernel void genesis_mutate(
    device uint8_t           *writeData     [[buffer(1)]],
    device float             *phaseWrite    [[buffer(9)]],
    const device uint        *tileSites     [[buffer(2)]],
    const device uint        *tileSize      [[buffer(3)]],
    device ulong             *rngStates     [[buffer(6)]],
    constant GenesisParams   &params        [[buffer(7)]],
    const device float       *massData      [[buffer(13)]],
    uint tid [[thread_position_in_grid]])
{
    if (tid >= params.n_tiles) return;

    uint n = params.n_sites;
    uint ps = params.prog_size;
    uint n_tp = params.n_tiles_per;
    bool is_tp = tid < n_tp;
    uint local_tile = is_tp ? tid : tid - n_tp;
    uint tile_idx = is_tp ? local_tile : local_tile + n_tp;
    uint sz = tileSize[tile_idx];

    /* RNG seeded per tile */
    ulong rng[4];
    rng_seed_from(rng, rngStates[tid * 4]
                       ^ ((ulong)tid * 0x517cc1b727220a95UL)
                       ^ ((ulong)params.sub_round_idx * 0x9e3779b97f4a7c15UL));

    float TWO_PI = 2.0f * M_PI_F;
    float THIRD = TWO_PI / 3.0f;

    for (uint i = 0; i < sz && i < ps; i++) {
        uint site = tileSites[tile_idx * ps + i];
        uint data_off = is_tp ? site : site + n;
        uint mass_off = is_tp ? site : n + site;

        float mu = params.mutation_rate;
        if (params.mass_couple > 0.0f)
            mu /= (1.0f + params.mass_couple * massData[mass_off]);

        if (rng_float_val(rng) < mu) {
            uint8_t new_trit = (uint8_t)rng_int_n(rng, 3);
            writeData[data_off] = new_trit;
            phaseWrite[(is_tp ? 0 : n) + site] = (float)new_trit * THIRD;
        }
    }

    /* Write back RNG state */
    for (int i = 0; i < 4; i++)
        rngStates[tid * 4 + i] = rng[i];
}
