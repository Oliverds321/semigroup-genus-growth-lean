# Exponential growth bound for generalized numerical semigroups

By Oliver D'Souza. Project name: `semigroup-genus-growth-lean`.

Repository: <https://github.com/Oliverds321/semigroup-genus-growth-lean>

Lean proofs and a manuscript for an explicit exponential upper bound on the
number of cofinite additive submonoids of `ℕ^d` with a prescribed genus.
The count is of subsets of the fixed coordinate lattice.

For positive integers `d` and `g`, put `C = 4^(d+1)` and `B = 8*d^2`.
The checked result is

```text
n(g,d) ≤ Σ (0 ≤ k < C*g), B^k = (B^(C*g) - 1)/(B - 1) < B^(C*g).
```

The counted family is proved finite before `Nat.card` is used. The result is
unconditional. The genus-zero count is one in every dimension. The proof uses
reflection in origin boxes, a finite maximal-average estimate, a bound on the
entire gap downclosure, and a closed-word encoding of finite downsets.

The manuscript answers Question 49 of Sean Li using classical maximal-average
estimates. Reflection and downset enumeration have earlier sources, credited
in the paper. The constants are not claimed to be optimal.

## Build and check

Install Lean through [elan](https://github.com/leanprover/elan), then run from
this directory:

```sh
lake exe cache get
./scripts/check.sh --clean
```

`lean-toolchain` selects Lean **4.24.0**. `lakefile.toml` pins mathlib to
**f897ebcf72cd16f89ab4577d0c826cd14afaafc7**; `lake-manifest.json` records its
transitive dependencies. Keep the manifest and do not run `lake update` to
reproduce this version. The cache download is optional; without it, Lake can
compile the dependencies from source. Python 3 is needed by the audit script.

The check script removes only this project's generated `.lake/build` directory
when `--clean` is supplied, runs `lake build`, then runs the declarations in
`Audit.lean` and checks their axiom dependencies. The accepted axioms are
`propext`, `Classical.choice`, and `Quot.sound`. It also checks that the audit
inventory covers every source declaration and rejects proof placeholders or
new axiom declarations. Run `lake env lean Audit.lean` to see the raw audit.

## Manuscript and scope

The editable manuscript and rendered PDF are in `paper/`. Build it with a TeX
installation containing the standard AMS, geometry, lmodern, microtype, and hyperref
packages:

```sh
./scripts/build-paper.sh
```

[THEOREMS.md](THEOREMS.md) gives the precise correspondence. Theorem 1,
Lemmas 2 and 3, Proposition 4, and Lemma 6 have Lean proofs. **Section 5
(Lemma 7 and Corollary 8) is not yet formalized.** Remark 5 is also outside
the Lean claims. The formalization uses a common finite cube; its origin
boxes may have different side lengths.

## Author and licenses

Oliver D'Souza is the sole author of this work.

The Lean formalization, accompanying build/audit scripts, configuration,
and project documentation are licensed under the [MIT License](LICENSE).
The manuscript source and rendered PDF in `paper/` are licensed separately
under [Creative Commons Attribution 4.0 International](paper/LICENSE.md)
(CC BY 4.0). The MIT license does not apply to the manuscript.

Dependencies retain their own licenses and notices; see
[THIRD_PARTY.md](THIRD_PARTY.md). No third-party dependency source or binary
is bundled in this package.
