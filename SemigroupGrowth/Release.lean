import SemigroupGrowth.Counting
import Mathlib.Algebra.Field.GeomSum

set_option autoImplicit false

namespace SemigroupGrowth

open Finset
open scoped Classical

/-- An empty gap set determines the full additive submonoid. -/
theorem genus_zero_eq_top (d : ℕ) (S : GenusSemigroups d 0) : S.val = ⊤ := by
  have he : gaps S = ∅ := card_eq_zero.mp (gaps_card S)
  ext x
  simp only [AddSubmonoid.mem_top, iff_true]
  by_contra hx
  have hm := (mem_gaps S x).mpr hx
  simp only [he, notMem_empty] at hm

/-- There is exactly one genus-zero semigroup in every dimension. -/
theorem genus_count_genus_zero (d : ℕ) : Nat.card (GenusSemigroups d 0) = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨⟨⊤, ∅, by simp, by simp⟩, ?_⟩
  intro S
  apply Subtype.ext
  exact genus_zero_eq_top d S

/-- Natural-number division in the counting formula equals the real quotient. -/
theorem geometric_quotient_cast (B M : ℕ) (hB : 2 ≤ B) :
    (((B^M - 1) / (B - 1) : ℕ) : ℝ) =
      ((B : ℝ)^M - 1) / ((B : ℝ) - 1) := by
  rw [← Nat.geomSum_eq hB]
  push_cast
  exact geom_sum_eq (by exact_mod_cast (show B ≠ 1 by omega)) M

/-- A finite geometric sum is strictly below the next power when the base is at least two. -/
theorem geometric_sum_lt_power (B M : ℕ) (hB : 2 ≤ B) :
    (∑ k ∈ range M, B^k) < B^M := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ, pow_succ]
    have hpos : 0 < B^M := pow_pos (by omega) _
    nlinarith

/-- The displayed bound in Theorem 1, with ordinary real division and strict final inequality. -/
theorem genus_count_bound_real (d g : ℕ) (hd : 0 < d) (hg : 0 < g) :
    (Nat.card (GenusSemigroups d g) : ℝ) ≤
      ((8 * (d : ℝ)^2)^(4^(d + 1) * g) - 1) / (8 * (d : ℝ)^2 - 1) ∧
    ((8 * (d : ℝ)^2)^(4^(d + 1) * g) - 1) / (8 * (d : ℝ)^2 - 1) <
      (8 * (d : ℝ)^2)^(4^(d + 1) * g) := by
  have hB : 2 ≤ 8 * d^2 := by nlinarith
  have hcast := geometric_quotient_cast (8 * d^2) (4^(d + 1) * g) hB
  have hsum := geometric_sum_lt_power (8 * d^2) (4^(d + 1) * g) hB
  rw [Nat.geomSum_eq hB] at hsum
  constructor
  · have hc := genus_count_le_geometric d g hd hg
    have hc' : (Nat.card (GenusSemigroups d g) : ℝ) ≤
        (((8 * d^2)^(4^(d + 1) * g) - 1) / (8 * d^2 - 1) : ℕ) := by exact_mod_cast hc
    rw [hcast] at hc'
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using hc'
  · have hs : ((((8 * d^2)^(4^(d + 1) * g) - 1) / (8 * d^2 - 1) : ℕ) : ℝ) <
        ((8 * d^2 : ℕ) : ℝ)^(4^(d + 1) * g) := by exact_mod_cast hsum
    rw [hcast] at hs
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using hs

/-- Explicit fixed-dimension exponential consequence, without asymptotic notation. -/
theorem genus_count_lt_exponential (d g : ℕ) (hd : 0 < d) (hg : 0 < g) :
    Nat.card (GenusSemigroups d g) < ((8 * d^2)^(4^(d + 1)))^g := by
  rw [← pow_mul]
  exact (genus_count_le_sum d g hg).trans_lt
    (geometric_sum_lt_power _ _ (by nlinarith))

end SemigroupGrowth
