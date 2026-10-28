import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

/-! Reflection is injective only on the coordinatewise box below the gap. -/
namespace SemigroupGrowth

open Finset
open scoped Classical

variable {d : ℕ}

def originBox (h : Fin d → ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset (fun i => range (h i + 1))

@[simp] theorem mem_originBox {h s : Fin d → ℕ} :
    s ∈ originBox h ↔ s ≤ h := by
  simp [originBox, Pi.le_def, Nat.lt_succ_iff]

theorem card_originBox (h : Fin d → ℕ) :
    (originBox h).card = ∏ i, (h i + 1) := by
  simp [originBox, Fintype.card_piFinset]

def gapDownclosure (G : Finset (Fin d → ℕ)) : Finset (Fin d → ℕ) :=
  G.biUnion originBox

@[simp] theorem mem_gapDownclosure {G : Finset (Fin d → ℕ)} {x : Fin d → ℕ} :
    x ∈ gapDownclosure G ↔ ∃ h ∈ G, x ≤ h := by
  simp [gapDownclosure]

theorem gapDownclosure_downward {G : Finset (Fin d → ℕ)} {x y : Fin d → ℕ}
    (hx : x ∈ gapDownclosure G) (hyx : y ≤ x) : y ∈ gapDownclosure G := by
  obtain ⟨h, hh, hxh⟩ := mem_gapDownclosure.mp hx
  exact mem_gapDownclosure.mpr ⟨h, hh, hyx.trans hxh⟩

theorem gaps_subset_gapDownclosure (G : Finset (Fin d → ℕ)) : G ⊆ gapDownclosure G := by
  intro h hh
  exact mem_gapDownclosure.mpr ⟨h, hh, le_rfl⟩

theorem zero_not_mem_gaps (S : AddSubmonoid (Fin d → ℕ))
    (G : Finset (Fin d → ℕ)) (hG : ∀ x, x ∈ G ↔ x ∉ S) :
    (0 : Fin d → ℕ) ∉ G := by
  intro hz
  exact ((hG 0).mp hz) S.zero_mem

theorem reflection_injective_on_box (h : Fin d → ℕ) :
    Set.InjOn (fun s : Fin d → ℕ => h - s) (originBox h : Set (Fin d → ℕ)) := by
  intro s hs t ht heq
  have hs' : s ≤ h := mem_originBox.mp hs
  have ht' : t ≤ h := mem_originBox.mp ht
  funext i
  have heqi := congrFun heq i
  have hsi : s i ≤ h i := hs' i
  have hti : t i ≤ h i := ht' i
  change h i - s i = h i - t i at heqi
  omega

theorem reflected_member_is_gap (S : AddSubmonoid (Fin d → ℕ))
    {h s : Fin d → ℕ} (hh : h ∉ S) (hs : s ∈ S) (hsh : s ≤ h) :
    h - s ∉ S := by
  intro hr
  apply hh
  have heq : s + (h - s) = h := by
    funext i
    exact Nat.add_sub_of_le (hsh i)
  simpa only [heq] using S.add_mem hs hr

theorem reflection_card_le (S : AddSubmonoid (Fin d → ℕ))
    {h : Fin d → ℕ} (hh : h ∉ S) :
    ((originBox h).filter (fun s => s ∈ S)).card ≤
      ((originBox h).filter (fun s => s ∉ S)).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun s : Fin d → ℕ => h - s)
  · intro s hs
    obtain ⟨hsbox, hsS⟩ := mem_filter.mp hs
    apply mem_filter.mpr
    exact ⟨mem_originBox.mpr (fun i => Nat.sub_le _ _),
      reflected_member_is_gap S hh hsS (mem_originBox.mp hsbox)⟩
  · exact (reflection_injective_on_box h).mono (by
      intro s hs
      exact (mem_filter.mp hs).1)

/-- Every box whose upper corner is a gap has gap density at least one half.
No cofiniteness assumption is needed for this local statement. -/
theorem reflection_density (S : AddSubmonoid (Fin d → ℕ))
    {h : Fin d → ℕ} (hh : h ∉ S) :
    (originBox h).card ≤ 2 * ((originBox h).filter (fun s => s ∉ S)).card := by
  classical
  have hinj := reflection_card_le S hh
  have hpartition := Finset.filter_card_add_filter_neg_card_eq_card
    (s := originBox h) (p := fun s => s ∈ S)
  omega

theorem reflection_density_gaps (S : AddSubmonoid (Fin d → ℕ))
    (G : Finset (Fin d → ℕ)) (hG : ∀ x, x ∈ G ↔ x ∉ S)
    {h : Fin d → ℕ} (hh : h ∈ G) :
    (originBox h).card ≤ 2 * ((originBox h) ∩ G).card := by
  classical
  have hfilter : (originBox h).filter (fun s => s ∉ S) = (originBox h) ∩ G := by
    ext s
    simp [hG]
  simpa only [hfilter] using reflection_density S ((hG h).mp hh)

theorem box_card_le_two_genus (S : AddSubmonoid (Fin d → ℕ))
    (G : Finset (Fin d → ℕ)) (hG : ∀ x, x ∈ G ↔ x ∉ S)
    {h : Fin d → ℕ} (hh : h ∈ G) :
    (originBox h).card ≤ 2 * G.card := by
  classical
  exact (reflection_density_gaps S G hG hh).trans
    (Nat.mul_le_mul_left 2 (card_le_card inter_subset_right))

/-- A coarse coordinate bound is enough to prove finiteness of the family,
before any cardinal arithmetic is used. -/
theorem gap_coordinate_lt_two_genus (S : AddSubmonoid (Fin d → ℕ))
    (G : Finset (Fin d → ℕ)) (hG : ∀ x, x ∈ G ↔ x ∉ S)
    {h : Fin d → ℕ} (hh : h ∈ G) (i : Fin d) : h i < 2 * G.card := by
  have hi : h i + 1 ≤ ∏ j, (h j + 1) :=
    Finset.single_le_prod' (f := fun j : Fin d => h j + 1)
      (s := univ) (fun j _ => Nat.succ_pos _) (mem_univ i)
  have hb := box_card_le_two_genus S G hG hh
  rw [card_originBox] at hb
  omega

def genusGrid (d g : ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset (fun _ => range (2 * g))

theorem gaps_subset_genusGrid (S : AddSubmonoid (Fin d → ℕ))
    (G : Finset (Fin d → ℕ)) (hG : ∀ x, x ∈ G ↔ x ∉ S) :
    G ⊆ genusGrid d G.card := by
  intro h hh
  apply Fintype.mem_piFinset.mpr
  intro i
  exact mem_range.mpr (gap_coordinate_lt_two_genus S G hG hh i)

/-- Finite complements of submonoids of fixed genus form a finite family.
This theorem does not invoke `Nat.card` or assume any eventual volume bound. -/
theorem gap_family_finite (d g : ℕ) :
    {G : Finset (Fin d → ℕ) | G.card = g ∧
      ∃ S : AddSubmonoid (Fin d → ℕ), ∀ x, x ∈ G ↔ x ∉ S}.Finite := by
  apply (genusGrid d g).powerset.finite_toSet.subset
  intro G hG
  obtain ⟨hcard, S, hS⟩ := hG
  apply mem_powerset.mpr
  simpa only [hcard] using gaps_subset_genusGrid S G hS

/-- The actual family of cofinite additive submonoids of fixed genus is finite,
not merely the family of their finite gap encodings. -/
theorem semigroup_family_finite (d g : ℕ) :
    {S : AddSubmonoid (Fin d → ℕ) | ∃ G : Finset (Fin d → ℕ),
      G.card = g ∧ ∀ x, x ∈ G ↔ x ∉ S}.Finite := by
  have hfinite := (gap_family_finite d g).image
    (fun G : Finset (Fin d → ℕ) => (G : Set (Fin d → ℕ))ᶜ)
  apply Set.Finite.of_injOn (f := fun S : AddSubmonoid (Fin d → ℕ) => (S : Set (Fin d → ℕ)))
      (t := (fun G : Finset (Fin d → ℕ) => (G : Set (Fin d → ℕ))ᶜ) ''
        {G | G.card = g ∧ ∃ S : AddSubmonoid (Fin d → ℕ), ∀ x, x ∈ G ↔ x ∉ S})
      ?_ ?_ hfinite
  · intro S hS
    obtain ⟨G, hcard, hG⟩ := hS
    refine ⟨G, ⟨hcard, S, hG⟩, ?_⟩
    ext x
    simp [hG]
  · intro S _ T _ hST
    exact SetLike.coe_injective hST

end SemigroupGrowth
