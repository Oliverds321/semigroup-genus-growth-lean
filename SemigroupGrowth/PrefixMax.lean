import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.Basic

set_option autoImplicit false

/-! Finite prefix maxima and their squared-norm bound, using only finite sums. -/
namespace SemigroupGrowth

open Finset
open scoped Classical

def prefixSum (f : ℕ → ℝ) (k : ℕ) : ℝ := ∑ j ∈ range k, f j

@[simp] theorem prefixSum_zero (f : ℕ → ℝ) : prefixSum f 0 = 0 := by
  simp [prefixSum]

theorem prefixSum_succ (f : ℕ → ℝ) (k : ℕ) :
    prefixSum f (k + 1) = prefixSum f k + f k := by
  exact sum_range_succ f k

theorem weighted_telescoping (b : ℕ → ℝ) (L : ℕ) :
    (∑ k ∈ range L, b k) =
      (∑ k ∈ range L, (k + 1 : ℝ) * (b k - b (k + 1))) + L * b L := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [sum_range_succ, sum_range_succ, ih]
    push_cast
    ring

theorem abel_identity (f a : ℕ → ℝ) (L : ℕ) :
    (∑ k ∈ range L, f k * a k) =
      (∑ k ∈ range L, prefixSum f (k + 1) * (a k - a (k + 1))) +
      prefixSum f L * a L := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [sum_range_succ, sum_range_succ, ih, prefixSum_succ]
    ring

/-- The finite certificate: monotonicity, a zero endpoint, and equality with the
prefix mean at every strict drop imply the energy inequality. -/
theorem prefix_certificate_energy (f a : ℕ → ℝ) (L : ℕ)
    (hend : a L = 0)
    (hmono : ∀ k < L, a (k + 1) ≤ a k)
    (hdrop : ∀ k < L, a (k + 1) < a k →
      (k + 1 : ℝ) * a k = prefixSum f (k + 1)) :
    (∑ k ∈ range L, (a k) ^ 2) ≤ 2 * ∑ k ∈ range L, f k * a k := by
  have hlocal : ∀ k ∈ range L,
      (k + 1 : ℝ) * ((a k)^2 - (a (k + 1))^2) ≤
      2 * (prefixSum f (k + 1) * (a k - a (k + 1))) := by
    intro k hk
    have hkL := mem_range.mp hk
    rcases (hmono k hkL).eq_or_lt with heq | hlt
    · rw [heq]
      simp
    · rw [← hdrop k hkL hlt]
      have hnonneg : 0 ≤ (k + 1 : ℝ) := by exact_mod_cast Nat.zero_le (k + 1)
      nlinarith [mul_nonneg hnonneg (sq_nonneg (a k - a (k + 1)))]
  have hsum := sum_le_sum hlocal
  have htel := weighted_telescoping (fun k => (a k)^2) L
  have habel := abel_identity f a L
  simp only [hend, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at htel habel
  rw [← mul_sum] at hsum
  rw [← htel, ← habel] at hsum
  exact hsum

/-- Squared Cauchy--Schwarz converts the energy certificate into the constant-4
squared-norm estimate. No square roots or measure theory are used. -/
theorem prefix_certificate_sq_bound (f a : ℕ → ℝ) (L : ℕ)
    (hend : a L = 0)
    (hmono : ∀ k < L, a (k + 1) ≤ a k)
    (hdrop : ∀ k < L, a (k + 1) < a k →
      (k + 1 : ℝ) * a k = prefixSum f (k + 1)) :
    (∑ k ∈ range L, (a k)^2) ≤ 4 * ∑ k ∈ range L, (f k)^2 := by
  have he := prefix_certificate_energy f a L hend hmono hdrop
  have hcs := sum_mul_sq_le_sq_mul_sq (range L) f a
  have ha : 0 ≤ ∑ k ∈ range L, (a k)^2 := sum_nonneg (fun k _ => sq_nonneg _)
  have hf : 0 ≤ ∑ k ∈ range L, (f k)^2 := sum_nonneg (fun k _ => sq_nonneg _)
  have ht : 0 ≤ 2 * ∑ k ∈ range L, f k * a k := le_trans ha he
  have hprod := mul_nonneg (sub_nonneg.mpr he) (add_nonneg ht ha)
  by_contra h
  have hgt : 4 * (∑ k ∈ range L, (f k)^2) < ∑ k ∈ range L, (a k)^2 :=
    lt_of_not_ge h
  have hapos : 0 < ∑ k ∈ range L, (a k)^2 := by linarith
  have hbad := mul_pos hapos (sub_pos.mpr hgt)
  nlinarith

noncomputable def prefixMean (f : ℕ → ℝ) (m : ℕ) : ℝ :=
  prefixSum f (m + 1) / (m + 1 : ℝ)

/-- Zero is included to define the maximum even when the suffix is empty.
For nonnegative input and `k < L`, this is exactly the maximum of the prefix
means with indices `k ≤ m < L`; see `prefixMax_eq_sup'`. -/
noncomputable def prefixMax (f : ℕ → ℝ) (L k : ℕ) : ℝ :=
  (insert 0 ((Ico k L).image (prefixMean f))).sup'
    (insert_nonempty _ _) id

theorem prefixMax_nonneg (f : ℕ → ℝ) (L k : ℕ) : 0 ≤ prefixMax f L k := by
  exact le_sup' id (mem_insert_self _ _)

theorem prefixMean_le_prefixMax (f : ℕ → ℝ) {L k m : ℕ}
    (hkm : k ≤ m) (hmL : m < L) : prefixMean f m ≤ prefixMax f L k := by
  have hm : prefixMean f m ∈ insert 0 ((Ico k L).image (prefixMean f)) :=
    mem_insert_of_mem (mem_image.mpr ⟨m, mem_Ico.mpr ⟨hkm, hmL⟩, rfl⟩)
  exact le_sup' (id : ℝ → ℝ) hm

theorem prefixMax_le (f : ℕ → ℝ) {L k : ℕ} {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ m, k ≤ m → m < L → prefixMean f m ≤ c) :
    prefixMax f L k ≤ c := by
  apply sup'_le
  intro x hx
  rcases mem_insert.mp hx with rfl | hx
  · exact hc
  · obtain ⟨m, hm, rfl⟩ := mem_image.mp hx
    exact h m (mem_Ico.mp hm).1 (mem_Ico.mp hm).2

@[simp] theorem prefixMax_end (f : ℕ → ℝ) (L : ℕ) : prefixMax f L L = 0 := by
  simp [prefixMax]

theorem prefixMax_succ_le (f : ℕ → ℝ) (L k : ℕ) :
    prefixMax f L (k + 1) ≤ prefixMax f L k := by
  apply prefixMax_le f (prefixMax_nonneg f L k)
  intro m hkm hmL
  exact prefixMean_le_prefixMax f (by omega) hmL

theorem prefixMax_eq_max (f : ℕ → ℝ) {L k : ℕ} (hk : k < L) :
    prefixMax f L k = max (prefixMean f k) (prefixMax f L (k + 1)) := by
  apply le_antisymm
  · apply prefixMax_le f ((prefixMax_nonneg f L (k + 1)).trans (le_max_right _ _))
    intro m hkm hmL
    rcases hkm.eq_or_lt with rfl | hlt
    · exact le_max_left _ _
    · exact (prefixMean_le_prefixMax f (by omega) hmL).trans (le_max_right _ _)
  · exact max_le (prefixMean_le_prefixMax f le_rfl hk) (prefixMax_succ_le f L k)

theorem prefixMax_drop (f : ℕ → ℝ) {L k : ℕ} (hk : k < L)
    (hdrop : prefixMax f L (k + 1) < prefixMax f L k) :
    (k + 1 : ℝ) * prefixMax f L k = prefixSum f (k + 1) := by
  have hmax := prefixMax_eq_max f hk
  have hmean : prefixMax f L k = prefixMean f k := by
    rcases le_total (prefixMean f k) (prefixMax f L (k + 1)) with h | h
    · rw [max_eq_right h] at hmax
      exact (hdrop.ne hmax.symm).elim
    · exact hmax.trans (max_eq_left h)
  rw [hmean, prefixMean]
  have hne : (k + 1 : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  exact mul_div_cancel₀ _ hne

theorem prefixMean_nonneg (f : ℕ → ℝ) {L m : ℕ}
    (hf : ∀ j < L, 0 ≤ f j) (hm : m < L) : 0 ≤ prefixMean f m := by
  apply div_nonneg
  · apply sum_nonneg
    intro j hj
    exact hf j (by have := mem_range.mp hj; omega)
  · exact_mod_cast Nat.zero_le (m + 1)

theorem prefixMax_eq_sup' (f : ℕ → ℝ) {L k : ℕ}
    (hf : ∀ j < L, 0 ≤ f j) (hk : k < L) :
    prefixMax f L k = (Ico k L).sup' ⟨k, mem_Ico.mpr ⟨le_rfl, hk⟩⟩ (prefixMean f) := by
  apply le_antisymm
  · apply prefixMax_le f
    · exact (prefixMean_nonneg f hf hk).trans
        (le_sup' (prefixMean f) (mem_Ico.mpr ⟨le_rfl, hk⟩))
    · intro m hkm hmL
      exact le_sup' (prefixMean f) (mem_Ico.mpr ⟨hkm, hmL⟩)
  · apply sup'_le
    intro m hm
    exact prefixMean_le_prefixMax f (mem_Ico.mp hm).1 (mem_Ico.mp hm).2

theorem prefixMax_energy (f : ℕ → ℝ) (L : ℕ) :
    (∑ k ∈ range L, (prefixMax f L k)^2) ≤
      2 * ∑ k ∈ range L, f k * prefixMax f L k := by
  apply prefix_certificate_energy f (prefixMax f L) L (prefixMax_end f L)
  · intro k _
    exact prefixMax_succ_le f L k
  · intro k hk hdrop
    exact prefixMax_drop f hk hdrop

/-- The finite one-dimensional prefix-max squared-norm bound, with constant 4.
For signed inputs the operator includes zero; for nonnegative inputs it is the
suffix maximum of the prefix means specified in `prefixMax_eq_sup'`. -/
theorem prefixMax_sq_bound (f : ℕ → ℝ) (L : ℕ) :
    (∑ k ∈ range L, (prefixMax f L k)^2) ≤
      4 * ∑ k ∈ range L, (f k)^2 := by
  apply prefix_certificate_sq_bound f (prefixMax f L) L (prefixMax_end f L)
  · intro k _
    exact prefixMax_succ_le f L k
  · intro k hk hdrop
    exact prefixMax_drop f hk hdrop

end SemigroupGrowth
