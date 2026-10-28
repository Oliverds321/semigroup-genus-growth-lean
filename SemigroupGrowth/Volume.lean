import SemigroupGrowth.Reflection
import SemigroupGrowth.Tensor
import Mathlib.Data.Fin.Tuple.Basic

set_option autoImplicit false

/-! Transfer of the finite-grid estimate to cofinite additive submonoids. -/
namespace SemigroupGrowth

open Finset
open scoped Classical

def gridToNat (L : ℕ) : (d : ℕ) → Grid L d → (Fin d → ℕ)
  | 0, _ => Fin.elim0
  | d + 1, p => Fin.cons p.1.val (gridToNat L d p.2)

def natToGrid (L : ℕ) : (d : ℕ) → (v : Fin d → ℕ) → (∀ i, v i < L) → Grid L d
  | 0, _, _ => ()
  | d + 1, v, hv => (⟨v 0, hv 0⟩, natToGrid L d (fun i => v i.succ) (fun i => hv i.succ))

theorem gridToNat_lt (L d : ℕ) (p : Grid L d) : ∀ i, gridToNat L d p i < L := by
  induction d with
  | zero => intro i; exact Fin.elim0 i
  | succ d ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact p.1.isLt
    · exact ih p.2 j

theorem gridToNat_natToGrid (L d : ℕ) (v : Fin d → ℕ) (hv : ∀ i, v i < L) :
    gridToNat L d (natToGrid L d v hv) = v := by
  induction d with
  | zero => funext i; exact Fin.elim0 i
  | succ d ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact congrFun (ih (fun i => v i.succ) (fun i => hv i.succ)) j

theorem gridToNat_injective (L d : ℕ) : Function.Injective (gridToNat L d) := by
  induction d with
  | zero => intro x y _; cases x; cases y; rfl
  | succ d ih =>
    intro x y hxy
    apply Prod.ext
    · apply Fin.ext
      exact congrFun hxy 0
    · apply ih
      funext i
      exact congrFun hxy i.succ

theorem gridLE_iff_nat_le (L d : ℕ) (x h : Grid L d) :
    GridLE L d x h ↔ gridToNat L d x ≤ gridToNat L d h := by
  induction d with
  | zero => simp [GridLE, gridToNat]
  | succ d ih =>
    change (x.1 ≤ h.1 ∧ GridLE L d x.2 h.2) ↔
      (Fin.cons x.1.val (gridToNat L d x.2) : Fin (d + 1) → ℕ) ≤
        (Fin.cons h.1.val (gridToNat L d h.2) : Fin (d + 1) → ℕ)
    rw [Fin.cons_le_cons, ← ih]
    rfl

theorem image_boxPoints (L d : ℕ) (h : Grid L d) :
    (boxPoints L d h).image (gridToNat L d) = originBox (gridToNat L d h) := by
  ext v
  constructor
  · rintro hv
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hv
    exact mem_originBox.mpr ((gridLE_iff_nat_le L d p h).mp ((mem_boxPoints L d p h).mp hp))
  · intro hv
    have hvh := mem_originBox.mp hv
    have hbound : ∀ i, v i < L := fun i => lt_of_le_of_lt (hvh i) (gridToNat_lt L d h i)
    refine mem_image.mpr ⟨natToGrid L d v hbound, ?_, gridToNat_natToGrid L d v hbound⟩
    apply (mem_boxPoints L d _ h).mpr
    apply (gridLE_iff_nat_le L d _ h).mpr
    simpa only [gridToNat_natToGrid] using hvh

noncomputable def liftFinset (L d : ℕ) (H : Finset (Fin d → ℕ)) : Finset (Grid L d) :=
  univ.filter (fun p => gridToNat L d p ∈ H)

@[simp] theorem mem_liftFinset (L d : ℕ) (H : Finset (Fin d → ℕ)) (p : Grid L d) :
    p ∈ liftFinset L d H ↔ gridToNat L d p ∈ H := by simp [liftFinset]

theorem image_liftFinset (L d : ℕ) (H : Finset (Fin d → ℕ))
    (hH : ∀ v ∈ H, ∀ i, v i < L) :
    (liftFinset L d H).image (gridToNat L d) = H := by
  ext v
  constructor
  · intro hv
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hv
    exact (mem_liftFinset L d H p).mp hp
  · intro hv
    refine mem_image.mpr ⟨natToGrid L d v (hH v hv), ?_, gridToNat_natToGrid ..⟩
    simp only [mem_liftFinset, gridToNat_natToGrid, hv]

theorem card_liftFinset (L d : ℕ) (H : Finset (Fin d → ℕ))
    (hH : ∀ v ∈ H, ∀ i, v i < L) : (liftFinset L d H).card = H.card := by
  rw [← card_image_of_injective _ (gridToNat_injective L d), image_liftFinset L d H hH]

/-- The unconditional downclosure volume bound for a finite complement of an
additive submonoid of `ℕ^d`. No complexity-theoretic hypothesis is used. -/
theorem downclosure_card_le (d : ℕ) (S : AddSubmonoid (Fin d → ℕ))
    (G : Finset (Fin d → ℕ)) (hG : ∀ x, x ∈ G ↔ x ∉ S) :
    (gapDownclosure G).card ≤ 4^(d + 1) * G.card := by
  let L := 2 * G.card
  have hGbound : ∀ v ∈ G, ∀ i, v i < L := fun v hv i =>
    gap_coordinate_lt_two_genus S G hG hv i
  have hDbound : ∀ v ∈ gapDownclosure G, ∀ i, v i < L := by
    intro v hv i
    obtain ⟨h, hh, hvh⟩ := mem_gapDownclosure.mp hv
    exact lt_of_le_of_lt (hvh i) (hGbound h hh i)
  have hdensity : ∀ x ∈ liftFinset L d (gapDownclosure G), ∃ h, GridLE L d x h ∧
      (boxPoints L d h).card ≤ 2 * ((boxPoints L d h) ∩ liftFinset L d G).card := by
    intro x hx
    obtain ⟨v, hv, hxv⟩ := mem_gapDownclosure.mp ((mem_liftFinset L d _ x).mp hx)
    let h := natToGrid L d v (hGbound v hv)
    have hh : gridToNat L d h = v := gridToNat_natToGrid L d v (hGbound v hv)
    refine ⟨h, (gridLE_iff_nat_le L d x h).mpr (by simpa only [hh] using hxv), ?_⟩
    have hb : (boxPoints L d h).card = (originBox v).card := by
      rw [← card_image_of_injective _ (gridToNat_injective L d), image_boxPoints, hh]
    have hi : ((boxPoints L d h) ∩ liftFinset L d G).card = ((originBox v) ∩ G).card := by
      rw [← card_image_of_injective _ (gridToNat_injective L d),
        image_inter _ _ (gridToNat_injective L d), image_boxPoints, hh,
        image_liftFinset L d G hGbound]
    rw [hb, hi]
    exact reflection_density_gaps S G hG hv
  have hvol := finite_grid_volume_of_box_density L d
    (liftFinset L d (gapDownclosure G)) (liftFinset L d G) hdensity
  simpa only [card_liftFinset L d (gapDownclosure G) hDbound,
    card_liftFinset L d G hGbound] using hvol

end SemigroupGrowth
