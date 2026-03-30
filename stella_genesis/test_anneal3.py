#!/usr/bin/env python3
"""Find 100% convergence parameters."""
import numpy as np

N = 8
CHARGES = np.array([0,0,0,0,1,1,1,1])
D_WITHIN = np.sqrt(8/3)
D_CROSS_N = 2/np.sqrt(3)
IDEAL_DISTS = np.sort(np.concatenate([
    np.full(12, D_CROSS_N), np.full(12, D_WITHIN), np.full(4, 2.0)
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

def gd_step(pos, alpha, beta, lr, soft2, clip):
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
    pos -= lr * grad
    pos /= np.linalg.norm(pos, axis=1, keepdims=True)
    return pos

# Strategy 5: GD + kicks with more restarts, varying kick sizes
print("=== Strategy 5: GD + varying kicks, 10 restarts ===")
n_trials = 30
successes = 0
for trial in range(n_trials):
    np.random.seed(trial)
    pos = random_on_sphere(N)
    best_pos = pos.copy()
    best_rmsd = 999

    for restart in range(10):
        for s in range(400):
            pos = gd_step(pos, 2.0, 1.0, 0.01, 0.02, 20.0)
        rmsd = compute_rmsd(pos)
        if rmsd < best_rmsd:
            best_rmsd = rmsd
            best_pos = pos.copy()
        if rmsd < 0.02: break
        # Varying kick: larger early, smaller later
        kick_size = 0.5 * (1 - restart/10) + 0.1
        pos = best_pos.copy()
        kick = np.random.randn(N, 3) * kick_size
        for i in range(N):
            kick[i] -= np.dot(kick[i], pos[i]) * pos[i]
        pos += kick
        pos /= np.linalg.norm(pos, axis=1, keepdims=True)

    if best_rmsd < 0.02: successes += 1
print(f"  success: {successes}/{n_trials}")

# Strategy 6: Metropolis with longer run
print("\n=== Strategy 6: Long Metropolis MC ===")
def energy_i(pos, idx, alpha, beta, soft2):
    E = 0
    for j in range(N):
        if j == idx: continue
        d2 = np.sum((pos[idx] - pos[j])**2) + soft2
        c = alpha if CHARGES[idx] == CHARGES[j] else beta
        E += c / d2
    return E

successes = 0
for trial in range(n_trials):
    np.random.seed(trial)
    pos = random_on_sphere(N)
    total = 200000
    for s in range(total):
        frac = s / total
        T = 2.0 * (1 - frac)**2 + 0.001
        ss = 0.5 * (1 - frac) + 0.01
        i = np.random.randint(N)
        old = pos[i].copy()
        E_old = energy_i(pos, i, 2.0, 1.0, 0.01)
        disp = np.random.randn(3) * ss
        disp -= np.dot(disp, pos[i]) * pos[i]
        pos[i] += disp
        pos[i] /= np.linalg.norm(pos[i])
        E_new = energy_i(pos, i, 2.0, 1.0, 0.01)
        dE = E_new - E_old
        if dE > 0 and (T <= 0 or np.random.random() > np.exp(-dE/T)):
            pos[i] = old
    rmsd = compute_rmsd(pos)
    if rmsd < 0.02: successes += 1
print(f"  success: {successes}/{n_trials}")

# Strategy 7: Swap Monte Carlo (swap charges between particles)
print("\n=== Strategy 7: GD + charge-swap MC ===")
successes = 0
for trial in range(n_trials):
    np.random.seed(trial)
    pos = random_on_sphere(N)
    ch = CHARGES.copy()
    best_pos = pos.copy()
    best_ch = ch.copy()
    best_rmsd = 999

    for cycle in range(8):
        # GD phase
        for s in range(500):
            # Use current charge assignment
            grad = np.zeros((N, 3))
            for i in range(N):
                for j in range(N):
                    if i == j: continue
                    diff = pos[i] - pos[j]
                    d2 = np.sum(diff**2) + 0.02
                    c = 2.0 if ch[i] == ch[j] else 1.0
                    grad[i] += -2 * c / (d2**2) * diff
            for i in range(N):
                grad[i] -= np.dot(grad[i], pos[i]) * pos[i]
                gm = np.linalg.norm(grad[i])
                if gm > 20: grad[i] *= 20 / gm
            pos -= 0.01 * grad
            pos /= np.linalg.norm(pos, axis=1, keepdims=True)

        rmsd = compute_rmsd(pos)
        if rmsd < best_rmsd:
            best_rmsd = rmsd
            best_pos = pos.copy()
            best_ch = ch.copy()
        if rmsd < 0.02: break

        # Try swapping a charge-0 and charge-1 particle
        pos = best_pos.copy()
        ch = best_ch.copy()
        i0 = np.random.choice(np.where(ch == 0)[0])
        i1 = np.random.choice(np.where(ch == 1)[0])
        ch[i0], ch[i1] = ch[i1], ch[i0]

    if best_rmsd < 0.02: successes += 1
print(f"  success: {successes}/{n_trials}")

# Strategy 8: Many short GD from random starts, pick best
print("\n=== Strategy 8: 20 random restarts, short GD each ===")
successes = 0
for trial in range(n_trials):
    np.random.seed(trial * 100)
    best_rmsd = 999
    for attempt in range(20):
        np.random.seed(trial * 100 + attempt)
        pos = random_on_sphere(N)
        for s in range(300):
            pos = gd_step(pos, 2.0, 1.0, 0.01, 0.02, 20.0)
        rmsd = compute_rmsd(pos)
        if rmsd < best_rmsd:
            best_rmsd = rmsd
        if rmsd < 0.02: break
    if best_rmsd < 0.02: successes += 1
print(f"  success: {successes}/{n_trials}")
