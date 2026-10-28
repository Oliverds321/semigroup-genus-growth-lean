#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../paper"
pdflatex -interaction=nonstopmode -halt-on-error semigroup-growth.tex
pdflatex -interaction=nonstopmode -halt-on-error semigroup-growth.tex
pdflatex -interaction=nonstopmode -halt-on-error semigroup-growth.tex
