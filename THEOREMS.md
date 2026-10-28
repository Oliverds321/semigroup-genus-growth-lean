# Theorem correspondence and scope

All identifiers below are in namespace `SemigroupGrowth`.

| Manuscript claim | Lean declarations | Scope |
| --- | --- | --- |
| Theorem 1: finite genus count and geometric upper bound | `semigroup_family_finite`, `genusSemigroups_finite`, `unconditional_genus_count_bound` | All coordinate-labelled cofinite additive submonoids; final geometric formula assumes `0 < d` and `0 < g`. |
| Theorem 1: ordinary real quotient and strict inequality | `geometric_quotient_cast`, `genus_count_bound_real` | Natural division is explicitly identified with the real quotient. |
| Theorem 1: exponential consequence | `genus_count_lt_exponential` | Explicit bound `n(g,d) < ((8*d^2)^(4^(d+1)))^g` for positive `d,g`. |
| Theorem 1: genus zero | `genus_zero_eq_top`, `genus_count_genus_zero` | Count equals one for every `d`, including zero. |
| Lemma 2 | `prefix_certificate_energy`, `prefix_certificate_sq_bound`, `prefixMax_sq_bound` | Zero-based indexing in Lean; the maximum includes a zero baseline and agrees with the paper for nonnegative input (`prefixMax_eq_sup'`). |
| Coordinate norm estimate in Section 2 | `slice_sq_bound`, `tensorMax_sq_bound` | Squared norm factors `4` and `4^d` on an equal-side finite cube. |
| Lemma 3 | `boxAverage_le_tensorMax`, `boxAverage_eq_sum_div_card` | Origin-box domination is proved separately from the norm bound. |
| Proposition 4 | `reflection_density_gaps`, `gap_coordinate_lt_two_genus`, `downclosure_card_le` | Reflection is injective only on the origin box. The cube side is `2*G.card`; the volume theorem also handles empty gaps and zero dimension. |
| Lemma 6 | `exists_closed_word_of_nonempty`, `downsetWord_injective`, `downsets_card_le` | For `k+1` points, a closed word of length `2*k` gives at most `(2*d)^(2*k)` downsets. |
| Gap-subset count in Theorem 1 | `gapCodes_card_le`, `genusCode_injective`, `genus_count_le_sum` | Gap subsets exclude the origin. Finiteness precedes cardinal comparison. |
| Remark 5 | None | Example and sharper-constant discussion are not formalized. |
| Lemma 7 and Corollary 8 (Section 5) | None | Elementary paper proofs only; no Lean claim. |

The counted type is exactly

```lean
abbrev Point (d : ℕ) := Fin d → ℕ

abbrev GenusSemigroups (d g : ℕ) :=
  {S : AddSubmonoid (Point d) // ∃ G : Finset (Point d),
    G.card = g ∧ ∀ x, x ∈ G ↔ x ∉ S}
```

This counts submonoids as subsets, not up to isomorphism. Additive closure and
membership of zero come from `AddSubmonoid`; the finite complement of size
`g` is part of the subtype predicate. The independent finiteness proof places
all gaps in a fixed finite cube and injects submonoids into their gap sets.
Thus `Nat.card` does not rely on the convention that an infinite type has
cardinality zero.

For Lemma 6, the Lean proof deletes a maximal nonzero point, splits a word at
a visit to its predecessor, and inserts a two-step excursion. This is the
induction presented in the manuscript; it does not implement depth-first
search. The singleton is represented by the empty word. In dimension zero,
the only nonempty downset is the singleton origin, and positive genus is
impossible (`genus_count_zero_dim`).

The proof contains no complexity-theoretic hypothesis. It does not prove
convergence of genus growth roots, an optimal constant, or any priority claim.
