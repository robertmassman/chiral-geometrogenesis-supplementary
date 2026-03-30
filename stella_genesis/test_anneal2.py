#!/usr/bin/env python3
"""Find parameters that give 100% stella convergence at α/β=2."""
import numpy as np

N = 8
CHARGES = np.array([0,0,0,0,1,1,1,1])
S3 = 1/np.sqrt(3)
D_WITHIN = np.sqrt(8/3)
D_CROSS_N = 2/np.sqrt(3)
D_CROSS_F = 2.0
IDEAL_DISTS = np.sort(np.concatenate([
    np.full(12, D_CROSS_N), np.full(12, D_WITHIN), np.full(4, D_CROSS_F)
]))

def random_on_sphere(n):
    pts = np.random.randn(n, 3)
    pts /= np.linalg.norm(pts, axis=1, keepdims=True)
    return pts

def compute_rmsd(pos):
    dists = []
    for i in range(N):
        for j in range(i+1, N):
            dists.append(np.linalg.norm(pos[i] - pos[j]))
    return np.sqrt(np.mean((np.sort(dists) - IDEAL_DISTS)**2))

def anneal_step(pos, alpha, beta, T, lr, soft2, clip):
    grad = np.zeros((N, 3))
    for i in range(N):
        for j in range(N):
            if i == j: continue
            diff = pos[i] - pos[j]
            d2 = np.sum(diff**2) + soft2
            c = alpha if CHARGES[i] == CHARGES[j] else beta
            grad[i] += -2 * c / (d2**2) * diff
    for i in range(N):
        grad[i] -= np.dot(grad[i], pos[i]) * pos[i]
        gm = np.linalg.norm(grad[i])
        if gm > clip: grad[i] *= clip / gm
    noise = np.random.randn(N, 3) * np.sqrt(max(0, 2*T*lr))
    for i in range(N):
        noise[i] -= np.dot(noise[i], pos[i]) * pos[i]
    pos -= lr * grad + noise
    pos /= np.linalg.norm(pos, axis=1, keepdims=True)
    return pos

# Strategy 1: Multi-stage annealing (hot explore, then cold optimize, with reheat)
print("=== Strategy 1: Multi-stage annealing with reheat ===")
n_trials = 20
steps = 3000
successes = 0
for trial in range(n_trials):
    np.random.seed(trial)
    pos = random_on_sphere(N)
    for s in range(steps):
        # 3-stage: hot, warm, cold
        frac = s / steps
        if frac < 0.2:
            T = 0.5 * (1 - frac/0.2) + 0.05
        elif frac < 0.4:
            T = 0.3 * (1 - (frac-0.2)/0.2) + 0.02  # reheat
        else:
            T = 0.02 * (1 - (frac-0.4)/0.6)
        pos = anneal_step(pos, 2.0, 1.0, T, 0.008, 0.02, 20.0)
    rmsd = compute_rmsd(pos)
    if rmsd < 0.02: successes += 1
print(f"  success: {successes}/{n_trials}")

# Strategy 2: Metropolis Monte Carlo
print("\n=== Strategy 2: Metropolis Monte Carlo ===")
def metropolis_step(pos, alpha, beta, T, step_size, soft2):
    # Pick random particle, propose random move on sphere
    i = np.random.randint(N)
    old_pos = pos[i].copy()

    # Current energy contribution from particle i
    def energy_i(p, idx):
        E = 0
        for j in range(N):
            if j == idx: continue
            d2 = np.sum((p[idx] - p[j])**2) + soft2
            c = alpha if CHARGES[idx] == CHARGES[j] else beta
            E += c / d2
        return E

    E_old = energy_i(pos, i)

    # Propose move: random displacement projected to sphere
    disp = np.random.randn(3) * step_size
    disp -= np.dot(disp, pos[i]) * pos[i]
    pos[i] += disp
    pos[i] /= np.linalg.norm(pos[i])

    E_new = energy_i(pos, i)
    dE = E_new - E_old

    if dE < 0 or (T > 0 and np.random.random() < np.exp(-dE / T)):
        return pos, True  # accept
    else:
        pos[i] = old_pos
        return pos, False  # reject

successes = 0
for trial in range(n_trials):
    np.random.seed(trial)
    pos = random_on_sphere(N)
    total_mc_steps = 50000
    for s in range(total_mc_steps):
        frac = s / total_mc_steps
        T = 1.0 * max(0.001, (1 - frac)**3)
        step_size = 0.3 * max(0.02, (1 - frac))
        pos, _ = metropolis_step(pos, 2.0, 1.0, T, step_size, 0.01)
    rmsd = compute_rmsd(pos)
    if rmsd < 0.02: successes += 1
print(f"  success: {successes}/{n_trials}")

# Strategy 3: Gradient descent with periodic random kicks
print("\n=== Strategy 3: GD + periodic kicks ===")
successes = 0
rmsd_vals = []
for trial in range(n_trials):
    np.random.seed(trial)
    pos = random_on_sphere(N)
    best_pos = pos.copy()
    best_rmsd = compute_rmsd(pos)

    for restart in range(5):
        # Gradient descent phase
        for s in range(600):
            pos = anneal_step(pos, 2.0, 1.0, 0.0, 0.01, 0.02, 20.0)
        rmsd = compute_rmsd(pos)
        if rmsd < best_rmsd:
            best_rmsd = rmsd
            best_pos = pos.copy()
        if rmsd < 0.02:
            break
        # Random kick
        pos = best_pos.copy()
        kick = np.random.randn(N, 3) * 0.3
        for i in range(N):
            kick[i] -= np.dot(kick[i], pos[i]) * pos[i]
        pos += kick
        pos /= np.linalg.norm(pos, axis=1, keepdims=True)

    rmsd_vals.append(best_rmsd)
    if best_rmsd < 0.02: successes += 1
print(f"  success: {successes}/{n_trials} | avg: {np.mean(rmsd_vals):.4f}")

# Strategy 4: GD + momentum (velocity Verlet style)
print("\n=== Strategy 4: GD + momentum + damping ===")
successes = 0
rmsd_vals = []
for trial in range(n_trials):
    np.random.seed(trial)
    pos = random_on_sphere(N)
    vel = np.zeros((N, 3))

    for s in range(3000):
        # Compute force (negative gradient)
        force = np.zeros((N, 3))
        for i in range(N):
            for j in range(N):
                if i == j: continue
                diff = pos[i] - pos[j]
                d2 = np.sum(diff**2) + 0.02
                c = 2.0 if CHARGES[i] == CHARGES[j] else 1.0
                force[i] += 2 * c / (d2**2) * diff  # repulsive force

        # Project force to tangent, clip
        for i in range(N):
            force[i] -= np.dot(force[i], pos[i]) * pos[i]
            fm = np.linalg.norm(force[i])
            if fm > 20: force[i] *= 20 / fm

        # Damping schedule: high damping at start (exploration), less later
        frac = s / 3000
        damping = 0.85 + 0.14 * frac  # 0.85 → 0.99
        dt = 0.003

        # Random perturbation (decreasing)
        noise_scale = 0.1 * max(0, 1 - 2*frac)
        noise = np.random.randn(N, 3) * noise_scale
        for i in range(N):
            noise[i] -= np.dot(noise[i], pos[i]) * pos[i]

        vel = damping * vel + dt * force + noise
        # Project velocity to tangent
        for i in range(N):
            vel[i] -= np.dot(vel[i], pos[i]) * pos[i]

        pos += dt * vel
        pos /= np.linalg.norm(pos, axis=1, keepdims=True)

    rmsd = compute_rmsd(pos)
    rmsd_vals.append(rmsd)
    if rmsd < 0.02: successes += 1
print(f"  success: {successes}/{n_trials} | avg: {np.mean(rmsd_vals):.4f}")
