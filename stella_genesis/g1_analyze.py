#!/usr/bin/env python3
"""
G1: Scale-Dependent Emergence — Analysis
=========================================

Parses g1_{gpu,cpu}_n{25,100,150}.log files and computes:
- Entropy trajectories and CPU-vs-GPU gap at each scale
- Wall-clock speed (epochs/sec)
- First replicator emergence epoch
- Final unique count and top_count

Outputs g1_results.json.
"""

import re
import json
import os
import sys
import numpy as np
from datetime import datetime

LOG_DIR = os.path.join(os.path.dirname(__file__), '..', 'stella_lang')

SCALES = [25, 100, 150]

def parse_log(filepath):
    """Parse a soup log file, returning header info and epoch data."""
    header = {}
    epochs = []

    if not os.path.exists(filepath):
        return None

    with open(filepath) as f:
        lines = f.readlines()

    # Parse header for tile counts and timing
    for line in lines:
        m = re.match(r'Total tiles:\s+(\d+)', line)
        if m:
            header['total_tiles'] = int(m.group(1))
        m = re.match(r'Tiles/stella:\s+(\d+)', line)
        if m:
            header['tiles_per_stella'] = int(m.group(1))
        m = re.match(r'Sites/tetra:\s+(\d+)', line)
        if m:
            header['sites_per_tetra'] = int(m.group(1))
        # Wall-clock from final summary line
        m = re.search(r'Wall clock:\s+([\d.]+)\s*s', line)
        if m:
            header['wall_clock_s'] = float(m.group(1))
        m = re.search(r'([\d.]+)\s*epochs/s', line)
        if m:
            header['epochs_per_sec'] = float(m.group(1))
        # Replicator detection
        if 'REPLICATOR' in line.upper() or 'replicator' in line:
            m2 = re.search(r'epoch\s+(\d+)', line, re.IGNORECASE)
            if m2 and 'first_replicator_epoch' not in header:
                header['first_replicator_epoch'] = int(m2.group(1))

    # Parse epoch data lines: "   10000 |   91 |   4 | 1.5768 |  144 |"
    for line in lines:
        m = re.match(r'\s+(\d+)\s*\|\s*(\d+)\s*\|\s*(\d+)\s*\|\s*([\d.]+)\s*\|\s*(\d+)', line)
        if m:
            epochs.append({
                'epoch': int(m.group(1)),
                'unique': int(m.group(2)),
                'top_count': int(m.group(3)),
                'trit_entropy': float(m.group(4)),
                'total_progs': int(m.group(5)),
            })

    return {'header': header, 'epochs': epochs}


def analyze_scale(nsub):
    """Analyze one scale point (gpu + cpu)."""
    gpu = parse_log(os.path.join(LOG_DIR, f'g1_gpu_n{nsub}.log'))
    cpu = parse_log(os.path.join(LOG_DIR, f'g1_cpu_n{nsub}.log'))

    if not gpu or not cpu:
        missing = []
        if not gpu: missing.append(f'g1_gpu_n{nsub}.log')
        if not cpu: missing.append(f'g1_cpu_n{nsub}.log')
        return {'nsub': nsub, 'status': 'missing', 'missing_files': missing}

    if not gpu['epochs'] or not cpu['epochs']:
        return {'nsub': nsub, 'status': 'empty'}

    # Entropy arrays
    gpu_h = np.array([e['trit_entropy'] for e in gpu['epochs']])
    cpu_h = np.array([e['trit_entropy'] for e in cpu['epochs']])

    # Late-half stats (last 50% of data)
    half = len(gpu_h) // 2
    gpu_late = gpu_h[half:]
    cpu_late = cpu_h[half:]

    gpu_unique_late = np.array([e['unique'] for e in gpu['epochs'][half:]])
    cpu_unique_late = np.array([e['unique'] for e in cpu['epochs'][half:]])
    gpu_top_late = np.array([e['top_count'] for e in gpu['epochs'][half:]])
    cpu_top_late = np.array([e['top_count'] for e in cpu['epochs'][half:]])

    result = {
        'nsub': nsub,
        'status': 'complete',
        'total_tiles': gpu['header'].get('total_tiles', '?'),
        'tiles_per_stella': gpu['header'].get('tiles_per_stella', '?'),
        'num_data_points': len(gpu['epochs']),
        'entropy': {
            'gpu_mean_late': round(float(np.mean(gpu_late)), 4),
            'cpu_mean_late': round(float(np.mean(cpu_late)), 4),
            'gpu_std_late': round(float(np.std(gpu_late)), 4),
            'cpu_std_late': round(float(np.std(cpu_late)), 4),
            'gap_late': round(float(np.mean(gpu_late) - np.mean(cpu_late)), 4),
            'gpu_final': round(float(gpu_h[-1]), 4),
            'cpu_final': round(float(cpu_h[-1]), 4),
        },
        'unique_programs': {
            'gpu_mean_late': round(float(np.mean(gpu_unique_late)), 1),
            'cpu_mean_late': round(float(np.mean(cpu_unique_late)), 1),
        },
        'top_count': {
            'gpu_mean_late': round(float(np.mean(gpu_top_late)), 1),
            'cpu_mean_late': round(float(np.mean(cpu_top_late)), 1),
        },
        'replicators': {
            'gpu_first_epoch': gpu['header'].get('first_replicator_epoch', None),
            'cpu_first_epoch': cpu['header'].get('first_replicator_epoch', None),
        },
        'performance': {
            'gpu_epochs_per_sec': gpu['header'].get('epochs_per_sec'),
            'cpu_epochs_per_sec': cpu['header'].get('epochs_per_sec'),
        }
    }

    # Wall-clock speedup
    gpu_eps = result['performance']['gpu_epochs_per_sec']
    cpu_eps = result['performance']['cpu_epochs_per_sec']
    if gpu_eps and cpu_eps and cpu_eps > 0:
        result['performance']['gpu_speedup'] = round(gpu_eps / cpu_eps, 2)

    return result


def main():
    results = {
        'test': 'G1',
        'description': 'Scale-Dependent Emergence',
        'timestamp': datetime.now().isoformat(),
        'parameters': {
            'lattice_size': 2,
            'stellae': 4,
            'epochs': 1000000,
            'seed': 42,
            'scales_nsub': SCALES,
        },
        'scales': [],
    }

    for nsub in SCALES:
        print(f"\n=== n-sub {nsub} ===")
        r = analyze_scale(nsub)
        results['scales'].append(r)

        if r['status'] != 'complete':
            print(f"  Status: {r['status']}")
            continue

        e = r['entropy']
        print(f"  Tiles: {r['total_tiles']} ({r['tiles_per_stella']}/stella)")
        print(f"  GPU entropy (late): {e['gpu_mean_late']:.4f} ± {e['gpu_std_late']:.4f}")
        print(f"  CPU entropy (late): {e['cpu_mean_late']:.4f} ± {e['cpu_std_late']:.4f}")
        print(f"  Entropy gap (GPU - CPU): {e['gap_late']:.4f}")
        print(f"  GPU unique (late): {r['unique_programs']['gpu_mean_late']}")
        print(f"  CPU unique (late): {r['unique_programs']['cpu_mean_late']}")
        print(f"  GPU top_ct (late): {r['top_count']['gpu_mean_late']}")
        print(f"  CPU top_ct (late): {r['top_count']['cpu_mean_late']}")

        perf = r['performance']
        if perf.get('gpu_epochs_per_sec') and perf.get('cpu_epochs_per_sec'):
            print(f"  GPU: {perf['gpu_epochs_per_sec']:.0f} epochs/s")
            print(f"  CPU: {perf['cpu_epochs_per_sec']:.0f} epochs/s")
            print(f"  Speedup: {perf.get('gpu_speedup', '?')}×")

        rep = r['replicators']
        if rep['gpu_first_epoch'] or rep['cpu_first_epoch']:
            print(f"  Replicators: GPU@{rep['gpu_first_epoch']}, CPU@{rep['cpu_first_epoch']}")
        else:
            print(f"  Replicators: none detected")

    # Cross-scale summary
    complete = [s for s in results['scales'] if s['status'] == 'complete']
    if len(complete) >= 2:
        gaps = [s['entropy']['gap_late'] for s in complete]
        tiles = [s['total_tiles'] for s in complete]
        print(f"\n=== Cross-Scale Summary ===")
        print(f"  Scale (tiles): {tiles}")
        print(f"  Entropy gaps:  {gaps}")

        gap_range = max(gaps) - min(gaps)
        gap_mean = np.mean(gaps)
        results['cross_scale'] = {
            'tiles': tiles,
            'entropy_gaps': gaps,
            'gap_mean': round(float(gap_mean), 4),
            'gap_range': round(float(gap_range), 4),
            'gap_stable': gap_range < 0.1,  # Pass criterion: gap doesn't grow unbounded
        }

        if results['cross_scale']['gap_stable']:
            print(f"  PASS: Entropy gap stable (range {gap_range:.4f} < 0.1)")
            results['passed'] = True
        else:
            print(f"  FAIL: Entropy gap varies too much (range {gap_range:.4f} >= 0.1)")
            results['passed'] = False
    else:
        print(f"\nNot enough complete scales for cross-scale analysis ({len(complete)}/3)")
        results['passed'] = None

    # Save
    out_path = os.path.join(LOG_DIR, 'g1_results.json')
    with open(out_path, 'w') as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\nResults saved to {out_path}")

    return results


if __name__ == '__main__':
    main()
