/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Darts
public import PartitionedTriangleAbsorption.BlowupB.LinearExtras

/-! # BlowupB.Family001 — absorbers for the type `{0, 0, 1}`

The family `F001 = {{0, 0, 1}}` (two vertices in class `0`, one in class `1`) is neither linear
(`not_isLinearFam_001`) nor satisfies `ThreeStepLinks` (`not_threeStepLinks_001`: the link of
class `0` is the single edge `0 — 1`, bipartite). It is covered here by the dart construction:

* integral divisibility gives, at a class-`0` vertex, as many class-`0` as class-`1` neighbours,
  and at a class-`1` vertex an even number of (class-`0`) neighbours;
* pair them (`0`-edges with `1`-edges, resp. arbitrarily) and follow the darts: the classes along
  a trail read `0, 0, 1, 0, 0, 1, …` in one direction or the other; the phase of a dart is read
  off its two classes, the centre class is `0`;
* `phasedTrail_of_pairing` gives phased trail systems (`phasedDiv_001`), and
  `phased_terminal_absorber` the terminal absorber (`terminal_absorber_001`).
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset Equiv TypedTransformer

universe u

section Count

variable {V : Type u} [Fintype V] [DecidableEq V] {t : ℕ}

theorem sum_ite_sym2_eq' (p : V → Fin t) (v : V) (j : Fin t) {e : Sym2 V} (he : ¬ e.IsDiag) :
    ∑ u, (if e = s(v, u) ∧ p u = j then (1 : ℤ) else 0) = degContrib p v e j := by
  induction e using Sym2.ind with
  | _ a b =>
    have hab : a ≠ b := fun h => he (Sym2.mk_isDiag_iff.mpr h)
    simp only [degContrib, Sym2.lift_mk]
    by_cases ha : a = v <;> by_cases hb : b = v
    · exact absurd (ha.trans hb.symm) hab
    · subst ha
      rw [Finset.sum_eq_single b]
      · simp [hb]
      · intro u _ hu
        rw [if_neg]
        rintro ⟨h1, _⟩
        rcases Sym2.eq_iff.mp h1 with ⟨_, h3⟩ | ⟨_, h3⟩
        · exact hu h3.symm
        · exact hb h3
      · intro h; exact absurd (mem_univ _) h
    · subst hb
      rw [Finset.sum_eq_single a]
      · simp [ha, Sym2.eq_swap]
      · intro u _ hu
        rw [if_neg]
        rintro ⟨h1, _⟩
        rcases Sym2.eq_iff.mp h1 with ⟨h3, _⟩ | ⟨h3, _⟩
        · exact ha h3
        · exact hu h3.symm
      · intro h; exact absurd (mem_univ _) h
    · rw [Finset.sum_eq_zero]
      · simp [Ne.symm ha, Ne.symm hb, ha, hb]
      · intro u _
        rw [if_neg]
        rintro ⟨h1, _⟩
        rcases Sym2.eq_iff.mp h1 with ⟨h3, _⟩ | ⟨_, h3⟩
        · exact ha h3
        · exact hb h3

/-- For loopless edge sets, degree vectors count neighbours in every class. -/
theorem degVec_eq_card' (p : V → Fin t) {E : Finset (Sym2 V)} (hE : ∀ e ∈ E, ¬ e.IsDiag)
    (v : V) (j : Fin t) :
    degVec p E v j = ((univ.filter fun u => s(v, u) ∈ E ∧ p u = j).card : ℤ) := by
  rw [degVec, Finset.sum_apply, card_eq_sum_ones, Nat.cast_sum, sum_filter]
  have h : ∀ u, (if s(v, u) ∈ E ∧ p u = j then ((1 : ℕ) : ℤ) else 0) =
      ∑ e ∈ E, (if e = s(v, u) ∧ p u = j then (1 : ℤ) else 0) := by
    intro u
    simp only [ite_and, Finset.sum_ite_eq', Nat.cast_one]
  rw [sum_congr rfl fun u _ => h u, sum_comm]
  exact sum_congr rfl fun e he => (sum_ite_sym2_eq' p v j (hE e he)).symm

end Count

section Involutions

variable {V : Type u} [DecidableEq V]

/-- Two disjoint finsets of equal size are swapped by an involution. -/
theorem exists_swap_invol (A B : Finset V) (hAB : Disjoint A B) (hc : A.card = B.card) :
    ∃ f : V → V, (∀ w ∈ A, f w ∈ B ∧ f (f w) = w) ∧ (∀ w ∈ B, f w ∈ A ∧ f (f w) = w) := by
  have e : {x // x ∈ A} ≃ {x // x ∈ B} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hc])
  refine ⟨fun w => if h : w ∈ A then (e ⟨w, h⟩).1 else if h' : w ∈ B then (e.symm ⟨w, h'⟩).1
    else w, ?_, ?_⟩
  · intro w hw
    have hB : (e ⟨w, hw⟩).1 ∈ B := (e ⟨w, hw⟩).2
    have hnA : (e ⟨w, hw⟩).1 ∉ A := fun h => disjoint_left.mp hAB h hB
    refine ⟨by simp only [dif_pos hw]; exact hB, ?_⟩
    simp only [dif_pos hw, dif_neg hnA, dif_pos hB, Subtype.coe_eta, Equiv.symm_apply_apply]
  · intro w hw
    have hnA : w ∉ A := fun h => disjoint_left.mp hAB h hw
    have hA : (e.symm ⟨w, hw⟩).1 ∈ A := (e.symm ⟨w, hw⟩).2
    refine ⟨by simp only [dif_neg hnA, dif_pos hw]; exact hA, ?_⟩
    simp only [dif_neg hnA, dif_pos hw, dif_pos hA, Subtype.coe_eta, Equiv.apply_symm_apply]

/-- A finset of even size carries an involution without fixed points. -/
theorem exists_even_invol (S : Finset V) (hS : Even S.card) :
    ∃ f : V → V, ∀ w ∈ S, f w ∈ S ∧ f (f w) = w ∧ f w ≠ w := by
  obtain ⟨A, hAS, hAc⟩ := exists_subset_card_eq (s := S) (Nat.div_le_self S.card 2)
  have hBc : (S \ A).card = A.card := by
    rw [card_sdiff_of_subset hAS, hAc]
    obtain ⟨k, hk⟩ := hS
    omega
  obtain ⟨f, hfA, hfB⟩ := exists_swap_invol A (S \ A) disjoint_sdiff hBc.symm
  refine ⟨f, fun w hw => ?_⟩
  by_cases hwA : w ∈ A
  · obtain ⟨h1, h2⟩ := hfA w hwA
    exact ⟨(mem_sdiff.mp h1).1, h2, fun h => (mem_sdiff.mp h1).2 (by rw [h]; exact hwA)⟩
  · have hwB : w ∈ S \ A := mem_sdiff.mpr ⟨hw, hwA⟩
    obtain ⟨h1, h2⟩ := hfB w hwB
    exact ⟨hAS h1, h2, fun h => hwA (by rw [← h]; exact h1)⟩

end Involutions

/-- The family `{{0, 0, 1}}`. -/
def F001 : Finset (Multiset (Fin 2)) := {{0, 0, 1}}

theorem not_threeStepLinks_001 : ¬ ThreeStepLinks F001 := by
  unfold ThreeStepLinks Link F001
  decide

theorem not_isLinearFam_001 : ¬ IsLinearFam F001 := by
  intro h
  have := h.nodup _ (mem_singleton_self _)
  revert this
  decide

theorem not_allowed_11 : ¬ AllowedPair F001 1 1 := by
  rintro ⟨τ, hτ, _, hle⟩
  rw [F001, mem_singleton] at hτ
  subst hτ
  revert hle
  decide

theorem fin2_cases (c : Fin 2) : c = 0 ∨ c = 1 := by revert c; decide

theorem typeDegVec_001_0 :
    typeDegVec ({0, 0, 1} : Multiset (Fin 2)) 0 = fun i => (1 : ℤ) := by
  funext i; rcases fin2_cases i with rfl | rfl <;> decide

theorem typeDegVec_001_1 :
    typeDegVec ({0, 0, 1} : Multiset (Fin 2)) 1 = fun i => if i = 0 then (2 : ℤ) else 0 := by
  funext i; rcases fin2_cases i with rfl | rfl <;> decide

section Pairing001

variable {V : Type u} [Fintype V] [DecidableEq V] {p : V → Fin 2} {P : Finset (Sym2 V)}

/-- The degree vector of a vertex is a multiple of the degree vector of its part in `{0, 0, 1}`. -/
theorem degVec_001 (hdiv : IsIntDiv p F001 P) (v : V) :
    ∃ c : ℤ, degVec p P v = c • typeDegVec ({0, 0, 1} : Multiset (Fin 2)) (p v) := by
  obtain ⟨c, hc⟩ := hdiv.2 v
  refine ⟨c {0, 0, 1}, ?_⟩
  rw [hc, filter_true_of_mem, F001, sum_singleton]
  intro τ hτ
  rw [F001, mem_singleton] at hτ
  subst hτ
  rcases fin2_cases (p v) with h | h <;> rw [h] <;> decide

/-- Neighbours of `v` in `P` in class `j`. -/
def nbr (p : V → Fin 2) (P : Finset (Sym2 V)) (v : V) (j : Fin 2) : Finset V :=
  univ.filter fun u => s(v, u) ∈ P ∧ p u = j

theorem local_pairing_001 (hsubP : ∀ u v, s(u, v) ∈ P → AllowedPair F001 (p u) (p v))
    (hloop : ∀ e ∈ P, ¬ e.IsDiag) (hdiv : IsIntDiv p F001 P) (v : V) :
    ∃ f : V → V, ∀ w, s(v, w) ∈ P → s(v, f w) ∈ P ∧ f (f w) = w ∧ f w ≠ w ∧
      (p v = 0 → (p (f w) = 0 ↔ p w = 1)) ∧ (p v = 1 → p (f w) = 0) := by
  obtain ⟨c, hc⟩ := degVec_001 hdiv v
  have hcard : ∀ j, degVec p P v j = ((nbr p P v j).card : ℤ) :=
    fun j => degVec_eq_card' p hloop v j
  rcases fin2_cases (p v) with hv | hv
  · -- class 0: swap class-0 and class-1 neighbours
    have h0 := congrFun hc 0
    have h1 := congrFun hc 1
    rw [hv, typeDegVec_001_0, hcard] at h0 h1
    simp only [Pi.smul_apply, smul_eq_mul, mul_one] at h0 h1
    have heq : (nbr p P v 0).card = (nbr p P v 1).card := by omega
    have hdisj : Disjoint (nbr p P v 0) (nbr p P v 1) := by
      rw [disjoint_left]
      intro u hu hu'
      have a := (mem_filter.mp hu).2.2
      have b := (mem_filter.mp hu').2.2
      rw [a] at b
      exact absurd b (by decide)
    obtain ⟨f, hfA, hfB⟩ := exists_swap_invol _ _ hdisj heq
    refine ⟨f, fun w hw => ?_⟩
    rcases fin2_cases (p w) with hw0 | hw1
    · have hwA : w ∈ nbr p P v 0 := mem_filter.mpr ⟨mem_univ _, hw, hw0⟩
      obtain ⟨h1, h2⟩ := hfA w hwA
      have hf := (mem_filter.mp h1).2
      refine ⟨hf.1, h2, fun h => by rw [h, hw0] at hf; exact absurd hf.2 (by decide), ?_, ?_⟩
      · intro _; rw [hf.2, hw0]; decide
      · intro h; rw [hv] at h; exact absurd h (by decide)
    · have hwB : w ∈ nbr p P v 1 := mem_filter.mpr ⟨mem_univ _, hw, hw1⟩
      obtain ⟨h1, h2⟩ := hfB w hwB
      have hf := (mem_filter.mp h1).2
      refine ⟨hf.1, h2, fun h => by rw [h, hw1] at hf; exact absurd hf.2 (by decide), ?_, ?_⟩
      · intro _; rw [hf.2, hw1]; decide
      · intro h; rw [hv] at h; exact absurd h (by decide)
  · -- class 1: all neighbours are in class 0, and there is an even number of them
    have h0 := congrFun hc 0
    rw [hv, typeDegVec_001_1, hcard] at h0
    simp only [Pi.smul_apply, smul_eq_mul, if_pos] at h0
    have hev : Even (nbr p P v 0).card := ⟨c.toNat, by omega⟩
    have hall : ∀ w, s(v, w) ∈ P → p w = 0 := by
      intro w hw
      rcases fin2_cases (p w) with h | h
      · exact h
      · have := hsubP v w hw
        rw [hv, h] at this
        exact absurd this not_allowed_11
    obtain ⟨f, hf⟩ := exists_even_invol _ hev
    refine ⟨f, fun w hw => ?_⟩
    have hwS : w ∈ nbr p P v 0 := mem_filter.mpr ⟨mem_univ _, hw, hall w hw⟩
    obtain ⟨h1, h2, h3⟩ := hf w hwS
    have hf' := (mem_filter.mp h1).2
    refine ⟨hf'.1, h2, h3, fun h => ?_, fun _ => hf'.2⟩
    rw [hv] at h; exact absurd h (by decide)

/-- **Phased trail systems for `{0, 0, 1}`.** -/
theorem phasedDiv_001 (hsubP : ∀ u v, s(u, v) ∈ P → AllowedPair F001 (p u) (p v))
    (hloop : ∀ e ∈ P, ¬ e.IsDiag) (hdiv : IsIntDiv p F001 P) :
    ∃ (I : Type u) (_ : Fintype I) (_ : DecidableEq I), Nonempty (PhasedTrail p F001 P I) := by
  choose π hπ using local_pairing_001 hsubP hloop hdiv
  have hP : Pairing P π := ⟨fun v w h => (hπ v w h).1, fun v w h => (hπ v w h).2.1,
    fun v w h => (hπ v w h).2.2.1⟩
  have h0 : ∀ v w, s(v, w) ∈ P → p v = 0 → (p (π v w) = 0 ↔ p w = 1) :=
    fun v w h => (hπ v w h).2.2.2.1
  have h1 : ∀ v w, s(v, w) ∈ P → p v = 1 → p (π v w) = 0 :=
    fun v w h => (hπ v w h).2.2.2.2
  have hno11 : ∀ u v, s(u, v) ∈ P → p u = 1 → p v = 1 → False := by
    intro u v h hu hv
    have := hsubP u v h
    rw [hu, hv] at this
    exact not_allowed_11 this
  refine phasedTrail_of_pairing hloop hP
    (fun u v => if p u = 0 ∧ p v = 0 then 0 else if p u = 0 then 1 else 2) ?_
    (fun _ _ => 0) (fun _ _ _ => rfl) ?_ ?_
  · intro u v huv
    have hvu : s(v, u) ∈ P := mem_swap' huv
    rcases fin2_cases (p u) with hu | hu <;> rcases fin2_cases (p v) with hv | hv
    · have hw : p (π v u) = 1 := by
        rcases fin2_cases (p (π v u)) with h | h
        · exact absurd ((h0 v u hvu hv).mp h) (by rw [hu]; decide)
        · exact h
      simp [hu, hv, hw] <;> decide
    · simp [hu, hv] <;> decide
    · have hw : p (π v u) = 0 := (h0 v u hvu hv).mpr hu
      simp [hu, hv, hw] <;> decide
    · exact absurd (hno11 u v huv hu hv) id
  · intro u v _ h
    rcases fin2_cases (p u) with hu | hu
    · exact hu
    · simp [hu] at h
  · intro u v huv
    have hvu : s(v, u) ∈ P := mem_swap' huv
    rcases fin2_cases (p u) with hu | hu <;> rcases fin2_cases (p v) with hv | hv
    · have hw : p (π v u) = 1 := by
        rcases fin2_cases (p (π v u)) with h | h
        · exact absurd ((h0 v u hvu hv).mp h) (by rw [hu]; decide)
        · exact h
      rw [hu, hv, hw]; decide
    · rw [hu, hv, h1 v u hvu hv]; decide
    · rw [hu, hv, (h0 v u hvu hv).mpr hu]; decide
    · exact absurd (hno11 u v huv hu hv) id

end Pairing001

/-- **Terminal absorber for `{0, 0, 1}`** (no `ThreeStepLinks`, not linear). -/
theorem terminal_absorber_001 {V : Type u} [Fintype V] [DecidableEq V] {p : V → Fin 2}
    {G : SimpleGraph V} [DecidableRel G.Adj] {d K : ℕ}
    (hsub : ∀ u v, G.Adj u v → AllowedPair F001 (p u) (p v))
    (hmiss : ∀ v, missDeg p F001 G v ≤ d)
    (X : Finset (Sym2 V)) (Z : Finset V) (hXG : X ⊆ G.edgeFinset) (hK : X.card ≤ K)
    (hcls : ∀ c, Z.card + 4 * K * 2 ^ K + 2 * K + 6 * K + (4 * K + 2) * (d + 1) <
      (univ.filter fun v => p v = c).card) :
    ∃ A ⊆ G.edgeFinset, Disjoint A X ∧ HasDecomp p F001 A ∧
      (∀ L ⊆ X, IsIntDiv p F001 L → HasDecomp p F001 (A ∪ L)) ∧
      ∃ U : Finset V, U.card ≤ 4 * K * 2 ^ K ∧ Disjoint U (Z ∪ vertsOf X) ∧
        ∀ e ∈ A, ∀ v ∈ e, v ∈ vertsOf X ∨ v ∈ U := by
  refine phased_terminal_absorber hmiss X Z hXG hK (fun L hLX hLdiv => ?_) hcls
  refine phasedDiv_001 (fun u v h => hsub u v ?_) (fun e he => ?_) hLdiv
  · exact SimpleGraph.mem_edgeFinset.mp (hXG (hLX h))
  · exact G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (hXG (hLX he)))

end PartitionedTriangleAbsorption.BlowupB
