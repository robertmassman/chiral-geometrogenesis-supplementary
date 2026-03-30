#!/usr/bin/env python3
"""Quick test of the Z3 crystallization annealing to debug parameters."""
import numpy as np

N = 8
CHARGES = np.array([0,0,0,0,1,1,1,1])
S3 = 1/np.sqrt(3)

# Ideal stella
IDEAL_TP = np.array([[S3,S3,S3],[S3,-S3,-S3],[-S3,S3,-S3],[-S3,-S3,S3]])
IDEAL_TM = np.array([[-S3,-S3,-S3],[-S3,S3,S3],[S3,-S3,S3],[S3,S3,-S3]])

# Ideal sorted pairwise distances
D_WITHIN = np.sqrt(8/3)
D_CROSS_N = 2/np.sqrt(3)
D_CROSS_F = 2.0
IDEAL_DISTS = np.sort(np.concatenate([
    np.full(12, D_CROSS_N),
    np.full(12, D_WITHIN),
    np.full(4, D_CROSS_F)
]))

def random_on_sphere(n):
    pts = np.random.randn(n, 3)
    pts /= np.linalg.norm(pts, axis=1, keepdims=True)
    return pts

def compute_energy(pos, alpha, beta, soft2=0.0):
    E = 0
    for i in range(N):
        for j in range(i+1, N):
            d2 = np.sum((pos[i] - pos[j])**2) + soft2
            c = alpha if CHARGES[i] == CHARGES[j] else beta
            E += c / d2
    return E

def compute_rmsd(pos):
    dists = []
    for i in range(N):
        for j in range(i+1, N):
            dists.append(np.linalg.norm(pos[i] - pos[j]))
    dists = np.sort(dists)
    return np.sqrt(np.mean((dists - IDEAL_DISTS)**2))

def anneal_step(pos, alpha, beta, T, lr, soft2=0.0, grad_clip=None):
    grad = np.zeros((N, 3))
    for i in range(N):
        for j in range(N):
            if i == j: continue
            diff = pos[i] - pos[j]
            d2 = np.sum(diff**2) + soft2
            c = alpha if CHARGES[i] == CHARGES[j] else beta
            grad[i] += -2 * c / (d2**2) * diff

    # Project gradient to tangent plane of sphere
    for i in range(N):
        grad[i] -= np.dot(grad[i], pos[i]) * pos[i]

    # Clip gradient
    if grad_clip:
        for i in range(N):
            gm = np.linalg.norm(grad[i])
            if gm > grad_clip:
                grad[i] *= grad_clip / gm

    # Noise on tangent plane
    noise = np.random.randn(N, 3) * np.sqrt(max(0, 2*T*lr))
    for i in range(N):
        noise[i] -= np.dot(noise[i], pos[i]) * pos[i]

    # Step
    pos -= lr * grad + noise

    # Normalize to sphere
    pos /= np.linalg.norm(pos, axis=1, keepdims=True)
    return pos

# ====== Test different parameter sets ======
configs = [
    {"name": "Original (broken)",  "lr": 0.004, "T0": 0.8,  "soft2": 1e-6, "clip": None,  "decay": 5},
    {"name": "Fix v1 (my fix)",    "lr": 0.008, "T0": 0.3,  "soft2": 0.04, "clip": 25.0,  "decay": 6},
    {"name": "Conservative",       "lr": 0.002, "T0": 0.15, "soft2": 0.1,  "clip": 10.0,  "decay": 4},
    {"name": "Aggressive clip",    "lr": 0.01,  "T0": 0.2,  "soft2": 0.05, "clip": 15.0,  "decay": 5},
    {"name": "High steps low T",   "lr": 0.005, "T0": 0.1,  "soft2": 0.05, "clip": 20.0,  "decay": 4},
]

total_steps = 2000
n_trials = 10

print(f"Testing {len(configs)} configs × {n_trials} trials × {total_steps} steps")
print(f"Target: RMSD < 0.02 = stella\n")

for cfg in configs:
    successes = 0
    rmsd_vals = []
    for trial in range(n_trials):
        np.random.seed(trial * 42 + 7)
        pos = random_on_sphere(N)

        for s in range(total_steps):
            T = cfg["T0"] * np.exp(-cfg["decay"] * s / total_steps)
            pos = anneal_step(pos, 2.0, 1.0, T, cfg["lr"], cfg["soft2"], cfg["clip"])

        rmsd = compute_rmsd(pos)
        rmsd_vals.append(rmsd)
        if rmsd < 0.02:
            successes += 1

    avg_rmsd = np.mean(rmsd_vals)
    print(f"{cfg['name']:25s} | success: {successes}/{n_trials} | avg RMSD: {avg_rmsd:.4f} | "
          f"min: {min(rmsd_vals):.4f} | max: {max(rmsd_vals):.4f}")

# Also test: what does pure gradient descent (no noise) do?
print(f"\n--- Pure gradient descent (T=0) ---")
for soft2 in [0.0, 0.01, 0.05, 0.1]:
    for lr in [0.001, 0.005, 0.01]:
        successes = 0
        rmsd_vals = []
        for trial in range(n_trials):
            np.random.seed(trial * 42 + 7)
            pos = random_on_sphere(N)
            for s in range(total_steps):
                pos = anneal_step(pos, 2.0, 1.0, 0.0, lr, soft2, 20.0)
            rmsd = compute_rmsd(pos)
            rmsd_vals.append(rmsd)
            if rmsd < 0.02: successes += 1
        if successes > 0:
            print(f"  soft2={soft2:.2f} lr={lr:.3f} | success: {successes}/{n_trials} | avg RMSD: {np.mean(rmsd_vals):.4f}")

# Test at different alpha/beta
print(f"\n--- Alpha/beta sweep (best config) ---")
for ratio in [0.5, 1.0, 1.5, 1.8, 2.0, 2.5, 3.0, 4.0, 5.0]:
    successes = 0
    for trial in range(n_trials):
        np.random.seed(trial * 42 + 7)
        pos = random_on_sphere(N)
        for s in range(total_steps):
            T = 0.1 * np.exp(-4 * s / total_steps)
            pos = anneal_step(pos, ratio, 1.0, T, 0.005, 0.05, 20.0)
        rmsd = compute_rmsd(pos)
        if rmsd < 0.02: successes += 1
    print(f"  α/β = {ratio:.1f} | stella: {successes}/{n_trials}")
