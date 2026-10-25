#!/usr/bin/env python3
"""Check the layer structure of the RadiiPolynomial library.

Every file `RadiiPolynomial/<Layer>/<File>.lean` may import Mathlib, and from this library only
the layers listed for <Layer> below. The general part (WeightedLp, Convolution, Calculus) depends
on Mathlib alone, so it can be extracted into its own library without changes.

Usage: python3 scripts/check_layers.py   (exit status 1 if a forbidden import is found)
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
LIB = ROOT / 'RadiiPolynomial'

# layer -> layers it may import (besides Mathlib)
ALLOWED = {
    # general part: sequence spaces, convolution algebras, calculus
    'WeightedLp': {'WeightedLp'},
    'Convolution': {'WeightedLp', 'Convolution'},
    'Calculus': {'WeightedLp', 'Convolution', 'Calculus'},
    # radii polynomial part
    'Abstract': {'Abstract'},
    'BlockTail': {'WeightedLp', 'Abstract', 'BlockTail'},
    'Certificate': {'WeightedLp', 'Convolution', 'Calculus', 'Abstract', 'Certificate'},
    'Problems': {'WeightedLp', 'Convolution', 'Calculus', 'Abstract', 'BlockTail', 'Certificate',
                 'Problems'},
}

IMPORT = re.compile(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(\S+)', re.M)


def main() -> int:
    errors = []
    for path in sorted(LIB.rglob('*.lean')):
        rel = path.relative_to(LIB)
        layer = rel.parts[0] if len(rel.parts) > 1 else None
        if layer not in ALLOWED:
            errors.append(f'{rel}: unknown layer {layer!r}')
            continue
        for mod in IMPORT.findall(path.read_text()):
            top = mod.split('.')[0]
            if top in ('Mathlib', 'Batteries', 'Init', 'Lean', 'Std'):
                continue
            if top != 'RadiiPolynomial':
                errors.append(f'{rel}: imports {mod} (outside the library and Mathlib)')
                continue
            dep = mod.split('.')[1]
            if dep not in ALLOWED[layer]:
                errors.append(f'{rel}: layer {layer} may not import {mod}')
    for e in errors:
        print(e)
    print(f'{len(errors)} layer violation(s)' if errors else 'layers OK')
    return 1 if errors else 0


if __name__ == '__main__':
    sys.exit(main())
