import SemigroupGrowth.PrefixMax
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Interval.Finset.Fin

set_option autoImplicit false

/-! Coordinatewise prefix maxima on finite product grids. The norm estimate and
the domination of box averages are proved separately. -/
namespace SemigroupGrowth

open Finset
open scoped Classical

def extendFin {L : ℕ} (f : Fin L → ℝ) (j : ℕ) : ℝ :=
  if h : j < L then f ⟨j, h⟩ else 0

@[simp] theorem extendFin_coe {L : ℕ} (f : Fin L → ℝ) (j : Fin L) :
    extendFin f j = f j := by simp [extendFin]

noncomputable def finPrefixMax {L : ℕ} (f : Fin L → ℝ) (i : Fin L) : ℝ :=
  prefixMax (extendFin f) L i

theorem finPrefixMax_nonneg {L : ℕ} (f : Fin L → ℝ) (i : Fin L) :
    0 ≤ finPrefixMax f i := prefixMax_nonneg _ _ _

theorem finPrefixMax_sq_bound {L : ℕ} (f : Fin L → ℝ) :
    (∑ i, (finPrefixMax f i)^2) ≤ 4 * ∑ i, (f i)^2 := by
  have h := prefixMax_sq_bound (extendFin f) L
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range] at h
  simpa only [extendFin_coe, finPrefixMax] using h

theorem prefixMean_mono {f g : ℕ → ℝ} {m : ℕ}
    (hfg : ∀ j < m + 1, f j ≤ g j) : prefixMean f m ≤ prefixMean g m := by
  apply div_le_div_of_nonneg_right
  · exact sum_le_sum (fun j hj => hfg j (mem_range.mp hj))
  · exact_mod_cast Nat.zero_le (m + 1)

theorem prefixMean_extendFin {L : ℕ} (f : Fin L → ℝ) (m : Fin L) :
    prefixMean (extendFin f) m = (∑ j ∈ Iic m, f j) / (m.val + 1 : ℝ) := by
  have hr : range (m.val + 1) = Iic m.val := by
    ext n
    simp [Nat.lt_succ_iff]
  unfold prefixMean prefixSum
  rw [hr, ← Fin.map_valEmbedding_Iic, sum_map]
  simp

/-- One coordinate changes the squared norm by at most a factor of four. -/
theorem slice_sq_bound {L : ℕ} {ι : Type*} [Fintype ι] (f : Fin L × ι → ℝ) :
    (∑ p : Fin L × ι, (finPrefixMax (fun i => f (i, p.2)) p.1)^2) ≤
      4 * ∑ p : Fin L × ι, (f p)^2 := by
  rw [Fintype.sum_prod_type_right, Fintype.sum_prod_type_right, mul_sum]
  exact sum_le_sum (fun j _ => finPrefixMax_sq_bound (fun i => f (i, j)))

/-- `Grid L d` is the iterated product of `d` copies of `Fin L`. -/
def Grid (L : ℕ) : ℕ → Type
  | 0 => Unit
  | d + 1 => Fin L × Grid L d

def gridFintype (L : ℕ) : (d : ℕ) → Fintype (Grid L d)
  | 0 => inferInstanceAs (Fintype Unit)
  | d + 1 => by
    letI := gridFintype L d
    exact inferInstanceAs (Fintype (Fin L × Grid L d))

instance (L d : ℕ) : Fintype (Grid L d) := gridFintype L d

noncomputable def tensorMax (L : ℕ) : (d : ℕ) → (Grid L d → ℝ) → Grid L d → ℝ
  | 0, f => f
  | d + 1, f => fun p =>
    finPrefixMax (fun i => tensorMax L d (fun q => f (i, q)) p.2) p.1

theorem tensorMax_nonneg (L d : ℕ) (f : Grid L d → ℝ) (hf : ∀ p, 0 ≤ f p) :
    ∀ p, 0 ≤ tensorMax L d f p := by
  cases d with
  | zero => exact hf
  | succ d => intro p; exact finPrefixMax_nonneg _ _

/-- The composition of all `d` coordinate operators has squared-norm constant
`4^d`, on a finite grid and for arbitrary real input. -/
theorem tensorMax_sq_bound (L d : ℕ) (f : Grid L d → ℝ) :
    (∑ p, (tensorMax L d f p)^2) ≤ (4 : ℝ)^d * ∑ p, (f p)^2 := by
  induction d with
  | zero => simp [tensorMax]
  | succ d ih =>
    have hs := slice_sq_bound (fun p : Fin L × Grid L d =>
      tensorMax L d (fun q => f (p.1, q)) p.2)
    change (∑ p : Fin L × Grid L d,
      (finPrefixMax (fun i => tensorMax L d (fun q => f (i, q)) p.2) p.1)^2) ≤
        (4 : ℝ)^(d + 1) * ∑ p : Fin L × Grid L d, (f p)^2
    apply hs.trans
    rw [Fintype.sum_prod_type]
    have hi := sum_le_sum (s := (univ : Finset (Fin L)))
      (fun i _ => ih (fun q => f (i, q)))
    have hi' := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 4)
    have hp : (4 : ℝ)^(d + 1) = 4 * 4^d := by rw [pow_succ, mul_comm]
    simpa only [← mul_sum, hp, Fintype.sum_prod_type, mul_assoc]
      using hi'

/-- Recursive coordinatewise comparison on the product grid. -/
def GridLE (L : ℕ) : (d : ℕ) → Grid L d → Grid L d → Prop
  | 0, _, _ => True
  | d + 1, x, h => x.1 ≤ h.1 ∧ GridLE L d x.2 h.2

/-- Iterated averaging over the coordinate prefixes determined by `h`. -/
noncomputable def boxAverage (L : ℕ) : (d : ℕ) → (Grid L d → ℝ) → Grid L d → ℝ
  | 0, f, _ => f ()
  | d + 1, f, h =>
    prefixMean (extendFin (fun i => boxAverage L d (fun q => f (i, q)) h.2)) h.1

/-- Domination of every origin-box average is independent of the norm proof.
It holds for arbitrary real input at every point in the box. -/
theorem boxAverage_le_tensorMax (L d : ℕ) (f : Grid L d → ℝ)
    (x h : Grid L d) (hxh : GridLE L d x h) :
    boxAverage L d f h ≤ tensorMax L d f x := by
  induction d with
  | zero => cases x; exact le_rfl
  | succ d ih =>
    apply le_trans (b := prefixMean
      (extendFin (fun i => tensorMax L d (fun q => f (i, q)) x.2)) h.1)
    · apply prefixMean_mono
      intro j hj
      have hjL : j < L := lt_of_lt_of_le hj h.1.isLt
      simp only [extendFin, dif_pos hjL]
      exact ih _ _ _ hxh.2
    · exact prefixMean_le_prefixMax _ hxh.1 h.1.isLt

def boxPoints (L : ℕ) : (d : ℕ) → Grid L d → Finset (Grid L d)
  | 0, _ => {()}
  | d + 1, h => (Iic h.1) ×ˢ boxPoints L d h.2

theorem mem_boxPoints (L d : ℕ) (x h : Grid L d) :
    x ∈ boxPoints L d h ↔ GridLE L d x h := by
  induction d with
  | zero => cases x; simp [boxPoints, GridLE]
  | succ d ih =>
    rcases x with ⟨i, x⟩
    change (i, x) ∈ (Iic h.1) ×ˢ boxPoints L d h.2 ↔ _
    simp only [mem_product, mem_Iic, ih, GridLE]

theorem boxPoints_card_pos (L d : ℕ) (h : Grid L d) :
    0 < (boxPoints L d h).card := by
  induction d with
  | zero => simp [boxPoints]
  | succ d ih =>
    change 0 < ((Iic h.1) ×ˢ boxPoints L d h.2 : Finset (Fin L × Grid L d)).card
    simpa only [card_product, Fin.card_Iic] using
      Nat.mul_pos (Nat.succ_pos h.1.val) (ih h.2)

/-- The iterated average is the ordinary sum over the coordinatewise origin
box divided by the number of points in that box. -/
theorem boxAverage_eq_sum_div_card (L d : ℕ) (f : Grid L d → ℝ) (h : Grid L d) :
    boxAverage L d f h = (∑ x ∈ boxPoints L d h, f x) / (boxPoints L d h).card := by
  induction d with
  | zero => simp [boxAverage, boxPoints]
  | succ d ih =>
    change prefixMean (extendFin (fun i => boxAverage L d (fun q => f (i, q)) h.2)) h.1 =
      (∑ p ∈ (Iic h.1) ×ˢ boxPoints L d h.2, f p) /
      ((Iic h.1) ×ˢ boxPoints L d h.2 : Finset (Fin L × Grid L d)).card
    simp only [prefixMean_extendFin, sum_product,
      card_product, Fin.card_Iic, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    simp_rw [ih]
    simp only [div_eq_mul_inv, ← sum_mul, mul_assoc, mul_inv_rev]

noncomputable def gapIndicator {L d : ℕ} (G : Finset (Grid L d)) (p : Grid L d) : ℝ :=
  if p ∈ G then 1 else 0

theorem sum_gapIndicator {L d : ℕ} (s G : Finset (Grid L d)) :
    (∑ p ∈ s, gapIndicator G p) = ((s ∩ G).card : ℝ) := by
  simp [gapIndicator]

/-- The finite-grid geometric consequence of a half-density box through every
point of `D`. This explicitly requires box density; it does not infer domination
from the squared-norm bound. -/
theorem finite_grid_volume_of_box_density (L d : ℕ) (D G : Finset (Grid L d))
    (hdensity : ∀ x ∈ D, ∃ h, GridLE L d x h ∧
      (boxPoints L d h).card ≤ 2 * ((boxPoints L d h) ∩ G).card) :
    D.card ≤ 4^(d + 1) * G.card := by
  let a := tensorMax L d (gapIndicator G)
  have hpoint : ∀ x ∈ D, (1 : ℝ) ≤ 4 * (a x)^2 := by
    intro x hx
    obtain ⟨h, hxh, hd⟩ := hdensity x hx
    have hpos : (0 : ℝ) < (boxPoints L d h).card := by
      exact_mod_cast boxPoints_card_pos L d h
    have hav : (1 / 2 : ℝ) ≤ boxAverage L d (gapIndicator G) h := by
      rw [boxAverage_eq_sum_div_card, sum_gapIndicator]
      apply (le_div_iff₀ hpos).mpr
      have hd' : ((boxPoints L d h).card : ℝ) ≤
          2 * (((boxPoints L d h) ∩ G).card : ℝ) := by exact_mod_cast hd
      linarith
    have ha : (1 / 2 : ℝ) ≤ a x := hav.trans
      (boxAverage_le_tensorMax L d (gapIndicator G) x h hxh)
    nlinarith
  have hD : (D.card : ℝ) ≤ 4 * ∑ x ∈ D, (a x)^2 := by
    calc
      (D.card : ℝ) = ∑ _x ∈ D, (1 : ℝ) := by simp
      _ ≤ ∑ x ∈ D, 4 * (a x)^2 := sum_le_sum hpoint
      _ = 4 * ∑ x ∈ D, (a x)^2 := (mul_sum ..).symm
  have hsubset : (∑ x ∈ D, (a x)^2) ≤ ∑ x, (a x)^2 :=
    sum_le_sum_of_subset_of_nonneg (subset_univ D) (fun x _ _ => sq_nonneg _)
  have hnorm := tensorMax_sq_bound L d (gapIndicator G)
  have hGnorm : (∑ x, (gapIndicator G x)^2) = (G.card : ℝ) := by
    simp [gapIndicator]
  rw [hGnorm] at hnorm
  have hreal : (D.card : ℝ) ≤ (4 : ℝ)^(d + 1) * (G.card : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hsubset (by norm_num : (0 : ℝ) ≤ 4)
    have h2 := mul_le_mul_of_nonneg_left hnorm (by norm_num : (0 : ℝ) ≤ 4)
    have hp : (4 : ℝ)^(d + 1) = 4 * 4^d := by rw [pow_succ, mul_comm]
    rw [hp]
    dsimp [a] at hD h1
    nlinarith
  exact_mod_cast hreal

end SemigroupGrowth
