import SemigroupGrowth.Reflection
import Mathlib.Data.List.Scan
import Mathlib.Order.Preorder.Finite

set_option autoImplicit false

namespace SemigroupGrowth

open Finset
open scoped Classical

abbrev Point (d : ℕ) := Fin d → ℕ
abbrev Dir (d : ℕ) := Fin d × Bool

def DownClosed {d : ℕ} (D : Finset (Point d)) : Prop :=
  ∀ ⦃x⦄, x ∈ D → ∀ ⦃y⦄, y ≤ x → y ∈ D

def step {d : ℕ} (x : Point d) (a : Dir d) : Point d :=
  Function.update x a.1 (if a.2 then x a.1 + 1 else x a.1 - 1)

def endpoint {d : ℕ} (x : Point d) (w : List (Dir d)) : Point d := w.foldl step x

def visited {d : ℕ} (x : Point d) (w : List (Dir d)) : Finset (Point d) :=
  (w.scanl step x).toFinset

@[simp] theorem endpoint_nil {d : ℕ} (x : Point d) : endpoint x [] = x := rfl
@[simp] theorem endpoint_cons {d : ℕ} (x : Point d) (a : Dir d) (w : List (Dir d)) :
    endpoint x (a :: w) = endpoint (step x a) w := rfl
@[simp] theorem endpoint_append {d : ℕ} (x : Point d) (u v : List (Dir d)) :
    endpoint x (u ++ v) = endpoint (endpoint x u) v := List.foldl_append

@[simp] theorem visited_nil {d : ℕ} (x : Point d) : visited x [] = {x} := rfl
@[simp] theorem visited_cons {d : ℕ} (x : Point d) (a : Dir d) (w : List (Dir d)) :
    visited x (a :: w) = insert x (visited (step x a) w) := by simp [visited]

theorem start_mem_visited {d : ℕ} (x : Point d) (w : List (Dir d)) : x ∈ visited x w := by
  cases w <;> simp

theorem visited_append {d : ℕ} (x : Point d) (u v : List (Dir d)) :
    visited x (u ++ v) = visited x u ∪ visited (endpoint x u) v := by
  induction u generalizing x with
  | nil => simp [insert_eq_of_mem (start_mem_visited x v)]
  | cons a u ih => simp [ih, insert_union]

/-- Any visited point occurs as the endpoint of a prefix, including the empty
prefix and the complete word. -/
theorem split_at_visit {d : ℕ} (x y : Point d) (w : List (Dir d))
    (hy : y ∈ visited x w) : ∃ u v, w = u ++ v ∧ endpoint x u = y := by
  induction w generalizing x with
  | nil =>
    have hyx : y = x := by simpa using hy
    exact ⟨[], [], rfl, hyx.symm⟩
  | cons a w ih =>
    rw [visited_cons, mem_insert] at hy
    rcases hy with rfl | hy
    · exact ⟨[], a :: w, rfl, rfl⟩
    · obtain ⟨u, v, hw, hu⟩ := ih (step x a) hy
      exact ⟨a :: u, v, by simp [hw], hu⟩

theorem visited_excursion {d : ℕ} (x u v : Point d) (a b : Dir d)
    (p q : List (Dir d)) (hp : endpoint x p = u)
    (ha : step u a = v) (hb : step v b = u) :
    visited x (p ++ a :: b :: q) = insert v (visited x (p ++ q)) := by
  rw [visited_append, visited_append, hp, visited_cons, ha, visited_cons, hb]
  ext z
  simp only [mem_union, mem_insert]
  have hu := start_mem_visited u q
  have hu' : z = u → z ∈ visited u q := by intro h; simpa only [h] using hu
  tauto

theorem endpoint_excursion {d : ℕ} (x u v : Point d) (a b : Dir d)
    (p q : List (Dir d)) (hp : endpoint x p = u)
    (ha : step u a = v) (hb : step v b = u) :
    endpoint x (p ++ a :: b :: q) = endpoint x (p ++ q) := by
  simp [hp, ha, hb]

theorem erase_max_downclosed {d : ℕ} (D : Finset (Point d)) (hD : DownClosed D)
    {v : Point d} (hv : Maximal (· ∈ D) v) : DownClosed (D.erase v) := by
  intro x hx y hyx
  obtain ⟨hxv, hxD⟩ := mem_erase.mp hx
  apply mem_erase.mpr
  refine ⟨?_, hD hxD hyx⟩
  intro hyv
  subst y
  exact hxv (le_antisymm (hv.2 hxD hyx) hyx)

/-- Every nonempty finite coordinatewise downset admits a closed direction word
with exactly twice as many steps as nonzero points. -/
theorem exists_closed_word {d : ℕ} (D : Finset (Point d)) (hD : DownClosed D)
    (hzero : (0 : Point d) ∈ D) :
    ∃ w : List (Dir d), w.length = 2 * (D.card - 1) ∧
      endpoint 0 w = 0 ∧ visited 0 w = D := by
  induction D using Finset.strongInductionOn with
  | _ D ih =>
    by_cases hsingle : D = {0}
    · exact ⟨[], by simp [hsingle], rfl, by simp [hsingle]⟩
    have hex : ∃ a ∈ D, a ≠ (0 : Point d) := by
      by_contra! hn
      apply hsingle
      ext x
      simp only [mem_singleton]
      exact ⟨fun hx => hn x hx, fun hx => hx ▸ hzero⟩
    obtain ⟨a, ha, ha0⟩ := hex
    obtain ⟨v, hav, hv⟩ := D.exists_le_maximal ha
    have hv0 : v ≠ (0 : Point d) := by
      intro heq
      apply ha0
      apply le_antisymm
      · simpa only [heq] using hav
      · exact fun _ => Nat.zero_le _
    have hzero' : (0 : Point d) ∈ D.erase v := mem_erase.mpr ⟨Ne.symm hv0, hzero⟩
    obtain ⟨w, hwlen, hwend, hwvis⟩ := ih (D.erase v) (erase_ssubset hv.1)
      (erase_max_downclosed D hD hv) hzero'
    have hpos : ∃ i, 0 < v i := by
      by_contra! hn
      apply hv0
      funext i
      exact Nat.eq_zero_of_le_zero (hn i)
    obtain ⟨i, hi⟩ := hpos
    let u := Function.update v i (v i - 1)
    have huv : u ≤ v := by
      intro j
      by_cases hji : j = i
      · subst j; simp [u]
      · simp [u, hji]
    have hune : u ≠ v := by
      intro heq
      have heqi := congrFun heq i
      simp [u] at heqi
      omega
    have hu : u ∈ D.erase v := mem_erase.mpr ⟨hune, hD hv.1 huv⟩
    have hup : step u (i, true) = v := by
      funext j
      by_cases hji : j = i
      · subst j; simp [step, u]; omega
      · simp [step, u, hji]
    have hdown : step v (i, false) = u := rfl
    obtain ⟨p, q, hpq, hp⟩ := split_at_visit 0 u w (by simpa only [hwvis] using hu)
    refine ⟨p ++ (i, true) :: (i, false) :: q, ?_, ?_, ?_⟩
    · have hc := card_erase_add_one hv.1
      have hcpos := card_pos.mpr ⟨0, hzero'⟩
      simp only [hpq, List.length_append] at hwlen
      simp only [List.length_append, List.length_cons]
      omega
    · rw [endpoint_excursion 0 u v (i, true) (i, false) p q hp hup hdown, ← hpq]
      exact hwend
    · rw [visited_excursion 0 u v (i, true) (i, false) p q hp hup hdown,
        ← hpq, hwvis, insert_erase hv.1]

theorem downset_zero_dim_eq_singleton (D : Finset (Point 0)) (hzero : (0 : Point 0) ∈ D) :
    D = {0} := by
  ext x
  have hx : x = (0 : Point 0) := Subsingleton.elim _ _
  simp [hx, hzero]

theorem singleton_closed_word (d : ℕ) :
    ([] : List (Dir d)).length = 2 * (({0} : Finset (Point d)).card - 1) ∧
      endpoint (0 : Point d) [] = 0 ∧ visited 0 [] = ({0} : Finset (Point d)) := by
  simp

theorem exists_closed_word_of_nonempty {d : ℕ} (D : Finset (Point d))
    (hD : DownClosed D) (hne : D.Nonempty) :
    ∃ w : List (Dir d), w.length = 2 * (D.card - 1) ∧
      endpoint 0 w = 0 ∧ visited 0 w = D := by
  obtain ⟨x, hx⟩ := hne
  exact exists_closed_word D hD (hD hx (fun _ => Nat.zero_le _))

end SemigroupGrowth
