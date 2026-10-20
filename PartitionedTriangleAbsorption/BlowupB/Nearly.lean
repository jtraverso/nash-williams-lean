/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Deletions

/-! # BlowupB.Nearly — nearly complete blowups

If every edge of `G` is an allowed pair and every vertex misses at most `d` of its allowed
neighbours (`missDeg ≤ d`), then for any set `S` of vertices, as soon as every class has more than
`(|S| + 5t)(d + 1)` vertices, `5` representatives per class can be chosen greedily so that the
local hypothesis `LocalHyp` holds with respect to `S` (`exists_reps_local`).

**Corollary** (`physDivCost_nearly`). For every family `F` and every `K` there is `C = C(F, K)`
such that in every such `G` (any `d`) whose classes have more than `(2K + 5t)(d + 1)` vertices,
every integrally `F`-divisible `E ⊆ E(G)` with `|E| ≤ K` has a physical certificate of cost
at most `C`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset

instance instDecidableAllowedPair {t : ℕ} (F : Finset (Multiset (Fin t))) (i j : Fin t) :
    Decidable (AllowedPair F i j) := by
  unfold AllowedPair; infer_instance

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}
  {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The allowed non-neighbours of `v`. -/
def missSet (p : V → Fin t) (F : Finset (Multiset (Fin t))) (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) : Finset V :=
  univ.filter fun r => v ≠ r ∧ AllowedPair F (p v) (p r) ∧ ¬ G.Adj v r

/-- The number of allowed non-neighbours of `v`. -/
def missDeg (p : V → Fin t) (F : Finset (Multiset (Fin t))) (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) : ℕ := (missSet p F G v).card

theorem adj_of_not_mem_missSet {v r : V} (h : r ∉ missSet p F G v) (hne : v ≠ r)
    (hA : AllowedPair F (p v) (p r)) : G.Adj v r := by
  by_contra hadj
  exact h (mem_filter.mpr ⟨mem_univ _, hne, hA, hadj⟩)

/-- Greedy choice of the slots in a finite set `A ⊆ Fin t × Fin 5`. -/
theorem exists_slots {d : ℕ} (hmiss : ∀ v, missDeg p F G v ≤ d) (S : Finset V)
    (hcls : ∀ i, (S.card + 5 * t) * (d + 1) < (univ.filter fun v => p v = i).card)
    (A : Finset (Fin t × Fin 5)) : ∃ f : Fin t × Fin 5 → V,
      (∀ s ∈ A, p (f s) = s.1) ∧ Set.InjOn f A ∧
      ∀ s ∈ A, ∀ v, (v ∈ S ∨ ∃ s' ∈ A, f s' = v) → v ≠ f s →
        AllowedPair F (p v) (p (f s)) → G.Adj v (f s) := by
  induction A using Finset.induction_on with
  | empty =>
    refine ⟨fun s => (Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) (hcls s.1))).choose,
      fun s hs => absurd hs (notMem_empty s), by simp, fun s hs => absurd hs (notMem_empty s)⟩
  | insert s0 A hs0 ih =>
    obtain ⟨f, hcl, hinj, hadj⟩ := ih
    set i := s0.1 with hi
    set bad : Finset V := A.image f ∪ (S ∪ A.image f).biUnion (missSet p F G) with hbad
    have hA5 : A.card ≤ 5 * t := by
      have := card_le_univ A
      rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at this
      omega
    have hbadc : bad.card < (univ.filter fun v => p v = i).card := by
      have h1 : bad.card ≤ A.card + (S.card + A.card) * d := by
        refine (card_union_le _ _).trans (add_le_add card_image_le ?_)
        refine card_biUnion_le.trans ?_
        calc ∑ v ∈ S ∪ A.image f, (missSet p F G v).card ≤ ∑ _v ∈ S ∪ A.image f, d :=
              sum_le_sum fun v _ => hmiss v
          _ = (S ∪ A.image f).card * d := by rw [sum_const, smul_eq_mul]
          _ ≤ (S.card + A.card) * d :=
              Nat.mul_le_mul_right _ ((card_union_le _ _).trans (add_le_add le_rfl card_image_le))
      have h2 := hcls i
      have h3 : A.card + (S.card + A.card) * d ≤ (S.card + 5 * t) * (d + 1) := by
        have : (S.card + A.card) * d ≤ (S.card + 5 * t) * d :=
          Nat.mul_le_mul_right _ (by omega)
        nlinarith
      omega
    obtain ⟨r, hr, hrb⟩ := exists_mem_notMem_of_card_lt_card hbadc
    have hpr : p r = i := (mem_filter.mp hr).2
    have hrA : r ∉ A.image f := fun h => hrb (mem_union_left _ h)
    have hrM : ∀ v ∈ S ∪ A.image f, r ∉ missSet p F G v := fun v hv h =>
      hrb (mem_union_right _ (mem_biUnion.mpr ⟨v, hv, h⟩))
    have hne_s : ∀ s ∈ A, s ≠ s0 := fun s hs h => hs0 (h ▸ hs)
    refine ⟨Function.update f s0 r, ?_, ?_, ?_⟩
    · intro s hs
      rcases mem_insert.mp hs with rfl | hs
      · rw [Function.update_self]; exact hpr
      · rw [Function.update_of_ne (hne_s s hs)]; exact hcl s hs
    · intro s hs s' hs' h
      simp only [coe_insert, Set.mem_insert_iff, mem_coe] at hs hs'
      rcases hs with rfl | hs <;> rcases hs' with rfl | hs'
      · rfl
      · rw [Function.update_self, Function.update_of_ne (hne_s s' hs')] at h
        exact absurd (mem_image.mpr ⟨s', hs', h.symm⟩) hrA
      · rw [Function.update_self, Function.update_of_ne (hne_s s hs)] at h
        exact absurd (mem_image.mpr ⟨s, hs, h⟩) hrA
      · rw [Function.update_of_ne (hne_s s hs), Function.update_of_ne (hne_s s' hs')] at h
        exact hinj hs hs' h
    · intro s hs v hv hne hA
      rcases mem_insert.mp hs with rfl | hs
      · rw [Function.update_self] at hne hA ⊢
        have hv' : v ∈ S ∪ A.image f := by
          rcases hv with hv | ⟨s', hs', rfl⟩
          · exact mem_union_left _ hv
          · rcases mem_insert.mp hs' with h0 | hsA'
            · rw [h0, Function.update_self] at hne; exact absurd rfl hne
            · rw [Function.update_of_ne (hne_s s' hsA')]
              exact mem_union_right _ (mem_image.mpr ⟨s', hsA', rfl⟩)
        exact adj_of_not_mem_missSet (hrM v hv') hne hA
      · rw [Function.update_of_ne (hne_s s hs)] at hne hA ⊢
        rcases hv with hv | ⟨s', hs', hfv⟩
        · exact hadj s hs v (Or.inl hv) hne hA
        · rcases mem_insert.mp hs' with h0 | hsA'
          · rw [← hfv, h0, Function.update_self] at hne hA ⊢
            have hfs : f s ∈ S ∪ A.image f := mem_union_right _ (mem_image.mpr ⟨s, hs, rfl⟩)
            exact (adj_of_not_mem_missSet (hrM (f s) hfs) (Ne.symm hne) hA.symm).symm
          · rw [← hfv, Function.update_of_ne (hne_s s' hsA')] at hne hA ⊢
            exact hadj s hs _ (Or.inr ⟨s', hsA', rfl⟩) hne hA

/-- **Greedy representatives.** -/
theorem exists_reps_local (hsub : ∀ u v, G.Adj u v → AllowedPair F (p u) (p v)) {d : ℕ}
    (hmiss : ∀ v, missDeg p F G v ≤ d) (S : Finset V)
    (hcls : ∀ i, (S.card + 5 * t) * (d + 1) < (univ.filter fun v => p v = i).card) :
    ∃ R : Reps p 5, LocalHyp p F G R (· ∈ S) := by
  obtain ⟨f, hcl, hinj, hadj⟩ := exists_slots hmiss S hcls univ
  refine ⟨⟨fun i a => f (i, a), fun i a i' a' h => ?_, fun i a => hcl (i, a) (mem_univ _)⟩,
    ⟨hsub, ?_⟩⟩
  · have := hinj (by simp) (by simp) h
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  · intro v r hv hr hne hA
    obtain ⟨i, a, rfl⟩ := (Reps.mem_set_iff _).mp hr
    refine hadj (i, a) (mem_univ _) v ?_ hne hA
    rcases hv with hv | hv
    · exact Or.inl hv
    · obtain ⟨i', a', rfl⟩ := (Reps.mem_set_iff _).mp hv
      exact Or.inr ⟨(i', a'), mem_univ _, rfl⟩

omit [Fintype V] in
theorem card_filter_mem_sym2_le [Fintype V] (e : Sym2 V) :
    (univ.filter fun v => v ∈ e).card ≤ 2 := by
  induction e using Sym2.ind with
  | _ a b =>
    refine (card_le_card fun v hv => ?_).trans (card_le_two (a := a) (b := b))
    rcases Sym2.mem_iff.mp (mem_filter.mp hv).2 with rfl | rfl <;> simp

/-- **Bounded certificates in nearly complete blowups.** The constant depends only on `F` and
`K` (not on the host, nor on the missing degree `d`). -/
theorem physDivCost_nearly (F : Finset (Multiset (Fin t)))
    (hF3 : ∀ τ ∈ F, Multiset.card τ = 3) (K : ℕ) :
    ∃ C : ℤ, ∀ {V : Type} [Fintype V] [DecidableEq V] {p : V → Fin t} {G : SimpleGraph V}
      [DecidableRel G.Adj] {d : ℕ}, (∀ u v, G.Adj u v → AllowedPair F (p u) (p v)) →
      (∀ v, missDeg p F G v ≤ d) →
      (∀ i, (2 * K + 5 * t) * (d + 1) < (univ.filter fun v => p v = i).card) →
      ∀ {E : Finset (Sym2 V)}, E ⊆ G.edgeFinset → IsIntDiv p F E → E.card ≤ K →
        PhysDivCost p F G E C := by
  obtain ⟨C, hC⟩ := physDivCost_local F hF3 K
  refine ⟨C, ?_⟩
  intro V _ _ p G _ d hsub hmiss hcls E hE hdiv hK
  set S : Finset V := E.biUnion fun e => univ.filter fun v => v ∈ e with hS
  have hSc : S.card ≤ 2 * K := by
    refine card_biUnion_le.trans ?_
    calc ∑ e ∈ E, (univ.filter fun v => v ∈ e).card ≤ ∑ _e ∈ E, 2 :=
          sum_le_sum fun e _ => card_filter_mem_sym2_le e
      _ = 2 * E.card := by rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ 2 * K := by omega
  have hcls' : ∀ i, (S.card + 5 * t) * (d + 1) < (univ.filter fun v => p v = i).card :=
    fun i => lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) (hcls i)
  obtain ⟨R, hL⟩ := exists_reps_local hsub hmiss S hcls'
  exact hC hL hE (fun e he x hx => mem_biUnion.mpr ⟨e, he, mem_filter.mpr ⟨mem_univ _, hx⟩⟩)
    hdiv hK

end PartitionedTriangleAbsorption.BlowupB
