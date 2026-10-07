#!/usr/bin/env python3
"""Check the compiled Lax proof graph, including its callable algorithm chain.

Copyright 2026 Édouard Bonnet. SPDX-License-Identifier: Apache-2.0
Run after a successful full `lax build`; no source-text inference is used.
"""
import json
from pathlib import Path

root = Path(__file__).resolve().parent
build = json.loads((root / 'build-output.json').read_text())
owners = {statement['id']: concept['id'] for concept in build['concepts']
          for statement in concept['statements']}
proofs = build['proofs']
assert len(owners) == 45 and len(proofs) == 45, 'Expected the full 45-statement build'

# The same least-fixed-point criterion as the archive: circular assumptions
# cannot make an unproved statement proven.
proved = set()
while True:
    reached = {p['conclusion'] for p in proofs if set(p['assumptions']) <= proved}
    if reached <= proved:
        break
    proved |= reached
assert proved == set(owners), f'Unproved statements: {sorted(set(owners) - proved)}'

edges = {(owners[a], owners[p['conclusion']]) for p in proofs for a in p['assumptions']
         if owners[a] != owners[p['conclusion']]}
required = {
    ('SparseMatrixProduct', 'LopsidedTriangleAlgorithms'),
    ('MatrixPreprocessing', 'LopsidedTriangleAlgorithms'),
    ('AlgorithmReductions', 'LopsidedTriangleAlgorithms'),
    ('LopsidedTriangleAlgorithms', 'IntegerAlgorithmBounds'),
    ('AlgorithmReductions', 'IntegerAlgorithmBounds'),
    *[('IntegerAlgorithmBounds', endpoint) for endpoint in
      ['ExactTriangle', 'ThreeSUM', 'MinPlusProduct', 'APSP', 'WeightedCliqueAlgorithms']],
    ('WeightedCliqueAlgorithms', 'ZeroWeightClique'),
}
short_edges = {(a.removeprefix('Lax350013.'), b.removeprefix('Lax350013.')) for a, b in edges}
assert required <= short_edges, f'Missing algorithm dependencies: {sorted(required - short_edges)}'

theorem_concepts = set(owners.values())
sinks = sorted(theorem_concepts - {a for a, _ in edges})
print(f'{len(proved)}/{len(owners)} statements proven; {len(edges)} edges between theorem concepts.')
print('Sink concepts: ' + ', '.join(c.removeprefix('Lax350013.') for c in sinks))
for source, target in sorted(short_edges):
    print(f'  {source} -> {target}')
