#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
if [[ ${1:-} == --clean ]]; then
  python3 - <<'PY'
from pathlib import Path
import shutil
target = Path('.lake/build')
if Path('.lake').is_symlink() or target.is_symlink():
    raise SystemExit('Refusing to remove through a symlink at .lake or .lake/build')
print('Removing project compilation artifacts: .lake/build', flush=True)
if target.exists():
    shutil.rmtree(target)
PY
elif [[ $# != 0 ]]; then
  echo 'Usage: scripts/check.sh [--clean]' >&2
  exit 2
fi
lake build
python3 scripts/check_axioms.py
