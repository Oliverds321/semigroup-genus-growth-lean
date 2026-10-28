#!/usr/bin/env python3
"""Check the source inventory and Lean's reported axiom dependencies."""
from pathlib import Path
import re
import subprocess
import sys

root = Path(__file__).resolve().parent.parent
sources = sorted((root / 'SemigroupGrowth').glob('*.lean'))
declaration = re.compile(
    r'^(?:@\[[^\n]*?\]\s*)?(?:noncomputable\s+)?'
    r'(?:theorem|lemma|def|abbrev|instance)\s+([A-Za-z_][\w\']*)', re.M)
names = set()
for source in sources:
    text = source.read_text()
    # Remove nested block comments, then line comments, before lexical checks.
    depth = 0
    clean = []
    i = 0
    while i < len(text):
        if text[i:i+2] == '/-':
            depth += 1
            i += 2
        elif depth and text[i:i+2] == '-/':
            depth -= 1
            i += 2
        elif depth:
            if text[i] == '\n':
                clean.append('\n')
            i += 1
        elif text[i:i+2] == '--':
            end = text.find('\n', i)
            i = len(text) if end == -1 else end
        else:
            clean.append(text[i])
            i += 1
    text = ''.join(clean)
    if re.search(r'\b(sorry|admit|axiom|native_decide)\b', text):
        sys.exit(f'Forbidden proof placeholder or trust extension in {source.name}')
    names.update('SemigroupGrowth.' + name for name in declaration.findall(text))
# The one anonymous instance has this elaborated name.
names.add('SemigroupGrowth.instFintypeGrid')
audit = (root / 'Audit.lean').read_text()
inventory = re.findall(r'^#print axioms (\S+)$', audit, re.M)
if len(inventory) != len(set(inventory)) or set(inventory) != names:
    sys.exit(f'Audit inventory mismatch: missing={names - set(inventory)}, '
             f'extra={set(inventory) - names}')
result = subprocess.run(['lake', 'env', 'lean', 'Audit.lean'], cwd=root,
                        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
print(result.stdout, end='')
if result.returncode:
    sys.exit(result.returncode)
records = re.findall(
    r"'(.+?)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",
    result.stdout)
if len(records) != len(inventory) or {name for name, _ in records} != names:
    sys.exit('Incomplete or unexpected Lean axiom output')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
used = set()
for name, axioms in records:
    actual = {item.strip() for item in axioms.split(',') if item.strip()}
    if actual - allowed:
        sys.exit(f'Unexpected axioms for {name}: {actual - allowed}')
    used.update(actual)
print(f'PASS: {len(records)} declarations; axiom union: {", ".join(sorted(used))}.')
