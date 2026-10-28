import SemigroupGrowth.Walk
import SemigroupGrowth.Volume
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Ring.GeomSum

set_option autoImplicit false

namespace SemigroupGrowth

open Finset
open scoped Classical

/-- Nonempty finite downsets with `k` nonzero points. -/
abbrev Downsets (d k : ℕ) :=
  {D : Finset (Point d) // DownClosed D ∧ (0 : Point d) ∈ D ∧ D.card = k + 1}

noncomputable def downsetWord {d k : ℕ} (D : Downsets d k) : List.Vector (Dir d) (2 * k) :=
  let hex := exists_closed_word D.val D.property.1 D.property.2.1
  ⟨hex.choose, by simpa only [D.property.2.2, Nat.add_sub_cancel] using hex.choose_spec.1⟩

theorem downsetWord_visited {d k : ℕ} (D : Downsets d k) :
    visited 0 (downsetWord D).val = D.val :=
  (exists_closed_word D.val D.property.1 D.property.2.1).choose_spec.2.2

theorem downsetWord_injective (d k : ℕ) : Function.Injective (@downsetWord d k) := by
  intro D E heq
  apply Subtype.ext
  have hw := congrArg (fun w : List.Vector (Dir d) (2 * k) => visited 0 w.val) heq
  simpa only [downsetWord_visited] using hw

instance downsets_finite (d k : ℕ) : Finite (Downsets d k) :=
  Finite.of_injective downsetWord (downsetWord_injective d k)

theorem downsets_card_le (d k : ℕ) : Nat.card (Downsets d k) ≤ (2 * d)^(2 * k) := by
  calc
    Nat.card (Downsets d k) ≤ Nat.card (List.Vector (Dir d) (2 * k)) :=
      Nat.card_le_card_of_injective downsetWord (downsetWord_injective d k)
    _ = (2 * d)^(2 * k) := by simp [Nat.card_eq_fintype_card, Dir, Nat.mul_comm]

abbrev Subsets {α : Type*} (D : Finset α) := {G : Finset α // G ⊆ D}

def subsetsEquiv {α : Type*} (D : Finset α) : Subsets D ≃ ↥D.powerset where
  toFun G := ⟨G.val, mem_powerset.mpr G.property⟩
  invFun G := ⟨G.val, mem_powerset.mp G.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance subsets_finite {α : Type*} (D : Finset α) : Finite (Subsets D) :=
  Finite.of_injective (subsetsEquiv D) (subsetsEquiv D).injective

theorem subsets_card {α : Type*} (D : Finset α) : Nat.card (Subsets D) = 2^D.card := by
  rw [Nat.card_congr (subsetsEquiv D), Nat.card_eq_fintype_card, Fintype.card_coe, card_powerset]

/-- A finite downset together with a possible gap subset, always omitting zero. -/
abbrev GapCodes (d k : ℕ) := Σ D : Downsets d k, Subsets (D.val.erase 0)

instance gapCodes_finite (d k : ℕ) : Finite (GapCodes d k) := by
  letI : Fintype (Downsets d k) := Fintype.ofFinite _
  letI (D : Downsets d k) : Fintype (Subsets (D.val.erase 0)) := Fintype.ofFinite _
  exact Finite.of_fintype (GapCodes d k)

theorem gapCodes_card_le (d k : ℕ) : Nat.card (GapCodes d k) ≤ (8 * d^2)^k := by
  letI : Fintype (Downsets d k) := Fintype.ofFinite _
  have hc : ∀ D : Downsets d k, Nat.card (Subsets (D.val.erase 0)) = 2^k := by
    intro D
    rw [subsets_card, card_erase_of_mem D.property.2.1, D.property.2.2, Nat.add_sub_cancel]
  calc
    Nat.card (GapCodes d k) = ∑ D : Downsets d k, Nat.card (Subsets (D.val.erase 0)) := Nat.card_sigma
    _ = Nat.card (Downsets d k) * 2^k := by simp [hc, Nat.card_eq_fintype_card]
    _ ≤ (2 * d)^(2 * k) * 2^k := Nat.mul_le_mul_right _ (downsets_card_le d k)
    _ = (8 * d^2)^k := by
      rw [pow_mul, ← mul_pow]
      congr 1
      ring

/-- The actual cofinite additive submonoids of fixed genus. -/
abbrev GenusSemigroups (d g : ℕ) :=
  {S : AddSubmonoid (Point d) // ∃ G : Finset (Point d), G.card = g ∧ ∀ x, x ∈ G ↔ x ∉ S}

/-- This instance uses the independently established geometric finiteness lemma,
before the counted family is passed to `Nat.card`. -/
instance genusSemigroups_finite (d g : ℕ) : Finite (GenusSemigroups d g) :=
  (semigroup_family_finite d g).to_subtype

noncomputable def gaps {d g : ℕ} (S : GenusSemigroups d g) : Finset (Point d) :=
  S.property.choose

theorem gaps_card {d g : ℕ} (S : GenusSemigroups d g) : (gaps S).card = g :=
  S.property.choose_spec.1

theorem mem_gaps {d g : ℕ} (S : GenusSemigroups d g) (x : Point d) :
    x ∈ gaps S ↔ x ∉ S.val := S.property.choose_spec.2 x

theorem gaps_injective (d g : ℕ) : Function.Injective (@gaps d g) := by
  intro S T heq
  apply Subtype.ext
  ext x
  have hm : x ∈ gaps S ↔ x ∈ gaps T := by rw [heq]
  simpa only [mem_gaps, not_iff_not] using hm

abbrev AllGapCodes (d M : ℕ) := Σ k : Fin M, GapCodes d k.val

instance allGapCodes_finite (d M : ℕ) : Finite (AllGapCodes d M) := by
  letI (k : Fin M) : Fintype (GapCodes d k.val) := Fintype.ofFinite _
  exact Finite.of_fintype (AllGapCodes d M)

theorem allGapCodes_card_le (d M : ℕ) :
    Nat.card (AllGapCodes d M) ≤ ∑ k ∈ range M, (8 * d^2)^k := by
  rw [Nat.card_sigma, ← Fin.sum_univ_eq_sum_range]
  exact sum_le_sum (fun k _ => gapCodes_card_le d k)

theorem gaps_downclosure_zero_mem {d g : ℕ} (hg : 0 < g) (S : GenusSemigroups d g) :
    (0 : Point d) ∈ gapDownclosure (gaps S) := by
  have hpos : 0 < (gaps S).card := by simpa only [gaps_card] using hg
  obtain ⟨h, hh⟩ := card_pos.mp hpos
  exact mem_gapDownclosure.mpr ⟨h, hh, fun _ => Nat.zero_le _⟩

noncomputable def genusCode {d g : ℕ} (hg : 0 < g) (S : GenusSemigroups d g) :
    AllGapCodes d (4^(d + 1) * g) := by
  let G := gaps S
  let D := gapDownclosure G
  have hz : (0 : Point d) ∈ D := gaps_downclosure_zero_mem hg S
  have hpos : 0 < D.card := card_pos.mpr ⟨0, hz⟩
  have hvol : D.card ≤ 4^(d + 1) * g := by
    simpa only [D, G, gaps_card] using downclosure_card_le d S.val G (mem_gaps S)
  have hindex : D.card - 1 < 4^(d + 1) * g := by omega
  have hsub : G ⊆ D.erase 0 := by
    intro x hx
    apply mem_erase.mpr
    refine ⟨?_, gaps_subset_gapDownclosure G hx⟩
    intro hx0
    subst x
    exact zero_not_mem_gaps S.val G (mem_gaps S) hx
  exact ⟨⟨D.card - 1, hindex⟩,
    ⟨⟨D, (fun _ hx _ hy => gapDownclosure_downward hx hy), hz,
      by change D.card = D.card - 1 + 1; omega⟩, ⟨G, hsub⟩⟩⟩

def decodeGapCode {d M : ℕ} (c : AllGapCodes d M) : Finset (Point d) := c.2.2.val

theorem decode_genusCode {d g : ℕ} (hg : 0 < g) (S : GenusSemigroups d g) :
    decodeGapCode (genusCode hg S) = gaps S := rfl

theorem genusCode_injective {d g : ℕ} (hg : 0 < g) : Function.Injective (@genusCode d g hg) := by
  intro S T heq
  apply gaps_injective d g
  have hdecode := congrArg decodeGapCode heq
  simpa only [decode_genusCode] using hdecode

/-- Unconditional exponential upper bound for the number of additive submonoids
of `ℕ^d` with exactly `g > 0` gaps. The counted type has a separately proved
`Finite` instance, so `Nat.card` is not being used on an infinite family. -/
theorem genus_count_le_sum (d g : ℕ) (hg : 0 < g) :
    Nat.card (GenusSemigroups d g) ≤ ∑ k ∈ range (4^(d + 1) * g), (8 * d^2)^k := by
  haveI : Finite (GenusSemigroups d g) := genusSemigroups_finite d g
  exact (Nat.card_le_card_of_injective (genusCode hg) (genusCode_injective hg)).trans
    (allGapCodes_card_le d (4^(d + 1) * g))

/-- The requested geometric-series form, for positive dimension and genus. -/
theorem genus_count_le_geometric (d g : ℕ) (hd : 0 < d) (hg : 0 < g) :
    Nat.card (GenusSemigroups d g) ≤
      ((8 * d^2)^(4^(d + 1) * g) - 1) / (8 * d^2 - 1) := by
  have hb : 2 ≤ 8 * d^2 := by nlinarith
  simpa only [Nat.geomSum_eq hb] using genus_count_le_sum d g hg

theorem positive_genus_zero_dim_isEmpty (g : ℕ) (hg : 0 < g) :
    IsEmpty (GenusSemigroups 0 g) := by
  refine ⟨fun S => ?_⟩
  have hpos : 0 < (gaps S).card := by simpa only [gaps_card] using hg
  obtain ⟨x, hx⟩ := card_pos.mp hpos
  have hx0 : x = (0 : Point 0) := Subsingleton.elim _ _
  subst x
  exact zero_not_mem_gaps S.val (gaps S) (mem_gaps S) hx

theorem genus_count_zero_dim (g : ℕ) (hg : 0 < g) :
    Nat.card (GenusSemigroups 0 g) = 0 := by
  letI := positive_genus_zero_dim_isEmpty g hg
  exact Nat.card_of_isEmpty

/-- Complete unconditional counting statement, including explicit finiteness
and both equivalent presentations of the upper bound. -/
theorem unconditional_genus_count_bound (d g : ℕ) (hd : 0 < d) (hg : 0 < g) :
    Finite (GenusSemigroups d g) ∧
    Nat.card (GenusSemigroups d g) ≤ ∑ k ∈ range (4^(d + 1) * g), (8 * d^2)^k ∧
    (∑ k ∈ range (4^(d + 1) * g), (8 * d^2)^k) =
      ((8 * d^2)^(4^(d + 1) * g) - 1) / (8 * d^2 - 1) := by
  refine ⟨genusSemigroups_finite d g, genus_count_le_sum d g hg, ?_⟩
  exact Nat.geomSum_eq (by nlinarith : 2 ≤ 8 * d^2) _

end SemigroupGrowth
