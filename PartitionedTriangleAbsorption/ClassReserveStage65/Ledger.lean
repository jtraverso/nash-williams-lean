/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ClassReserveStage65.Main

/-! # Survival of the reserve's hinge supply under a bounded-degree deletion ledger

The count of `Main` is a count of actual physical edge sets inside the reserve. Here an
arbitrary edge set `D` (the *deletion ledger*) of maximum degree at most `δ n` is removed
from the reserve **after** the reserve has been chosen. A hinge `hingeEdges u v w z x y` is
destroyed only if one of its seven edges lies in `D`; the destroyed pairs `(x, y)` are covered
by seven sets, each of size at most `n · δ n`:

* `uy ∈ D`, `yw ∈ D`, `yz ∈ D`: `y` is a `D`-neighbour of `u`, `w` or `z`;
* `vx ∈ D`, `xw ∈ D`, `xz ∈ D`: `x` is a `D`-neighbour of `v`, `w` or `z`;
* `xy ∈ D`: at most `∑ₓ deg_D x ≤ n · δ n` pairs.

Hence at least `γ² ρ⁷ n² / 32 - 7 δ n²` distinct six-vertex hinges survive inside `X \ D`,
for every original root pair, every labelling constant on fibres and every family `F`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ClassReserveStage65

open Finset BernoulliBlocks ClassAwareHingesStage64 PhysicalHingeSupply SignedHinge

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `D`-neighbours of `a`. -/
def nbrD (D : Finset (Sym2 V)) (a : V) : Finset V := univ.filter (fun y => s(a, y) ∈ D)

theorem card_nbrD_le (D : Finset (Sym2 V)) (a : V) :
    (nbrD D a).card ≤ (D.filter (fun e => a ∈ e)).card := by
  refine card_le_card_of_injOn (fun y => s(a, y)) ?_ ?_
  · intro y hy
    simp only [nbrD, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy
    simp [hy]
  · intro y _ y' _ h
    simp only [Sym2.eq_iff] at h
    rcases h with ⟨-, h⟩ | ⟨h1, h2⟩
    · exact h
    · exact h2.trans h1

theorem card_nbrD_le_real {D : Finset (Sym2 V)} {d : ℝ} (hD : DegBounded D d) (a : V) :
    ((nbrD D a).card : ℝ) ≤ d :=
  (by exact_mod_cast card_nbrD_le D a : ((nbrD D a).card : ℝ) ≤ _).trans (hD a)

/-- Pairs `(x, y)` whose hinge meets `D` lie in seven explicit sets. -/
def badPairs (D : Finset (Sym2 V)) (u v w z : V) : Finset (V × V) :=
  (univ ×ˢ nbrD D u) ∪ (nbrD D v ×ˢ univ) ∪ (nbrD D w ×ˢ univ) ∪ (univ ×ˢ nbrD D w) ∪
    (nbrD D z ×ˢ univ) ∪ (univ ×ˢ nbrD D z) ∪ univ.filter (fun q : V × V => s(q.1, q.2) ∈ D)

theorem mem_badPairs_of_meets {D : Finset (Sym2 V)} {u v w z : V} {q : V × V}
    (h : ¬ Disjoint (hingeEdges u v w z q.1 q.2) D) : q ∈ badPairs D u v w z := by
  obtain ⟨e, he, heD⟩ := not_disjoint_iff.mp h
  simp only [hingeEdges, mem_insert, mem_singleton] at he
  simp only [badPairs, mem_union, mem_product, mem_univ, true_and, and_true, nbrD,
    mem_filter]
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · tauto
  · tauto
  · rw [Sym2.eq_swap] at heD; tauto
  · rw [Sym2.eq_swap] at heD; tauto
  · rw [Sym2.eq_swap] at heD; tauto
  · rw [Sym2.eq_swap] at heD; tauto
  · tauto

theorem card_badPairs_le {D : Finset (Sym2 V)} {d : ℝ} (hD : DegBounded D d) (u v w z : V) :
    ((badPairs D u v w z).card : ℝ) ≤ 7 * (Fintype.card V * d) := by
  set n := Fintype.card V
  have hd : 0 ≤ d := le_trans (by positivity) (hD u)
  have hl : ∀ a, (((univ : Finset V) ×ˢ nbrD D a).card : ℝ) ≤ n * d := by
    intro a
    rw [card_product, card_univ]; push_cast
    exact mul_le_mul_of_nonneg_left (card_nbrD_le_real hD a) (by positivity)
  have hr : ∀ a, ((nbrD D a ×ˢ (univ : Finset V)).card : ℝ) ≤ n * d := by
    intro a
    rw [card_product, card_univ, mul_comm]; push_cast
    exact mul_le_mul_of_nonneg_left (card_nbrD_le_real hD a) (by positivity)
  have hc : ((univ.filter (fun q : V × V => s(q.1, q.2) ∈ D)).card : ℝ) ≤ n * d := by
    have he : (univ.filter (fun q : V × V => s(q.1, q.2) ∈ D)).card =
        ∑ x : V, (nbrD D x).card := by
      rw [card_filter, ← univ_product_univ, sum_product]
      simp only [nbrD, card_filter]
    rw [he]; push_cast
    calc (∑ x : V, ((nbrD D x).card : ℝ)) ≤ ∑ _x : V, d :=
          sum_le_sum (fun x _ => card_nbrD_le_real hD x)
      _ = n * d := by simp [n]
  have hu := card_union_le (s := (univ ×ˢ nbrD D u) ∪ (nbrD D v ×ˢ univ) ∪
    (nbrD D w ×ˢ univ) ∪ (univ ×ˢ nbrD D w) ∪ (nbrD D z ×ˢ univ) ∪ (univ ×ˢ nbrD D z))
    (t := univ.filter (fun q : V × V => s(q.1, q.2) ∈ D))
  have h6 := card_union_le (s := (univ ×ˢ nbrD D u) ∪ (nbrD D v ×ˢ univ) ∪
    (nbrD D w ×ˢ univ) ∪ (univ ×ˢ nbrD D w) ∪ (nbrD D z ×ˢ univ)) (t := univ ×ˢ nbrD D z)
  have h5 := card_union_le (s := (univ ×ˢ nbrD D u) ∪ (nbrD D v ×ˢ univ) ∪
    (nbrD D w ×ˢ univ) ∪ (univ ×ˢ nbrD D w)) (t := nbrD D z ×ˢ univ)
  have h4 := card_union_le (s := (univ ×ˢ nbrD D u) ∪ (nbrD D v ×ˢ univ) ∪
    (nbrD D w ×ˢ univ)) (t := univ ×ˢ nbrD D w)
  have h3 := card_union_le (s := (univ ×ˢ nbrD D u) ∪ (nbrD D v ×ˢ univ))
    (t := nbrD D w ×ˢ univ)
  have h2 := card_union_le (s := univ ×ˢ nbrD D u) (t := nbrD D v ×ˢ univ)
  have hreal : ((badPairs D u v w z).card : ℝ) ≤
      (((univ : Finset V) ×ˢ nbrD D u).card : ℝ) + (nbrD D v ×ˢ (univ : Finset V)).card +
      (nbrD D w ×ˢ (univ : Finset V)).card + ((univ : Finset V) ×ˢ nbrD D w).card +
      (nbrD D z ×ˢ (univ : Finset V)).card + ((univ : Finset V) ×ˢ nbrD D z).card +
      (univ.filter (fun q : V × V => s(q.1, q.2) ∈ D)).card := by
    have hnat : (badPairs D u v w z).card ≤
        ((univ : Finset V) ×ˢ nbrD D u).card + (nbrD D v ×ˢ (univ : Finset V)).card +
        (nbrD D w ×ˢ (univ : Finset V)).card + ((univ : Finset V) ×ˢ nbrD D w).card +
        (nbrD D z ×ˢ (univ : Finset V)).card + ((univ : Finset V) ×ˢ nbrD D z).card +
        (univ.filter (fun q : V × V => s(q.1, q.2) ∈ D)).card := by
      unfold badPairs
      omega
    exact_mod_cast hnat
  linarith [hl u, hr v, hr w, hl w, hr z, hl z]

open Classical in
/-- **Ledger survival in a good reserve.** -/
theorem hinge_supply_after_deletion (G : SimpleGraph V) [DecidableRel G.Adj] (cls : V → Fin 4)
    (hG : ∀ a b, G.Adj a b ↔ cls a ≠ cls b) {γ ρ : ℝ} (hρ : 0 < ρ)
    (hsize : ∀ v, γ * Fintype.card V ≤ ((fibre cls v).card : ℝ))
    (h2 : 2 ≤ γ * Fintype.card V) (ω : Sym2 V → Bool)
    (hω : ∀ i, ω ∉ badEvent G cls γ ρ i)
    {t : ℕ} (p : V → Fin t) (hp : ∀ a b, cls a = cls b → p a = p b)
    (F : Finset (Multiset (Fin t))) (S S' : Finset V)
    (hS : IsCopy p F G S) (hS' : IsCopy p F G S') (h1 : (triEdges S ∩ triEdges S').card = 1)
    (D : Finset (Sym2 V)) {δ : ℝ} (hD : DegBounded D (δ * Fintype.card V)) :
    γ ^ 2 * ρ ^ 7 * (Fintype.card V : ℝ) ^ 2 / 32 - 7 * δ * (Fintype.card V : ℝ) ^ 2 ≤
      (((sampledEdges G ω \ D).powerset.filter
        (fun H => IsHinge p F S S' H ∧ (vertSet H).card = 6)).card : ℝ) := by
  obtain ⟨u, v, w, z, -, -, -, -, -, hwz, rfl, rfl⟩ :=
    roots_of_shared_edge hS.1.card_eq hS'.1.card_eq h1
  obtain ⟨huv, huw, hvw⟩ := SimpleGraph.is3Clique_triple_iff.mp hS.1
  obtain ⟨-, huz, hvz⟩ := SimpleGraph.is3Clique_triple_iff.mp hS'.1
  set n := Fintype.card V
  set Mx := marked (xCand cls u) {v, w, z} ω
  set My := marked (xCand cls v) {u, w, z} ω
  set P := crossSampled Mx My ω
  set K := (sampledEdges G ω).powerset.filter (fun H =>
    IsHinge p F {u, v, w} {u, v, z} H ∧ (vertSet H).card = 6)
  set K' := (sampledEdges G ω \ D).powerset.filter (fun H =>
    IsHinge p F {u, v, w} {u, v, z} H ∧ (vertSet H).card = 6)
  have hP : γ ^ 2 * ρ ^ 7 * (n : ℝ) ^ 2 / 32 ≤ P.card :=
    cross_count_of_good G cls hG hρ hsize h2 ω hω huv huw huz hvw hvz
  -- surviving pairs inject into hinges of `X \ D`
  have hsurv : (P.filter (fun q => Disjoint (hingeEdges u v w z q.1 q.2) D)).card ≤
      K'.card := by
    have h := fun q (hq : q ∈ P) =>
      cross_pair_hinge (p := p) (F := F) cls hG hp huv huw huz hvw hvz hwz hS.2 hS'.2 ω hq
    have hmapsK : ∀ q ∈ P, hingeEdges u v w z q.1 q.2 ∈ K := fun q hq => (h q hq).2
    have hsixP : ∀ q ∈ P, SixDistinct u v w z q.1 q.2 := fun q hq => (h q hq).1
    refine card_le_card_of_injOn (fun q => hingeEdges u v w z q.1 q.2) ?_ ?_
    · intro q hq
      obtain ⟨hqP, hqD⟩ := mem_filter.mp hq
      obtain ⟨hpow, hH⟩ := mem_filter.mp (hmapsK q hqP)
      refine mem_filter.mpr ⟨mem_powerset.mpr ?_, hH⟩
      intro e he
      exact mem_sdiff.mpr ⟨mem_powerset.mp hpow he, disjoint_left.mp hqD he⟩
    · intro q hq q' hq' heq
      obtain ⟨hx, hy⟩ := hingeEdges_inj (hsixP q (mem_filter.mp hq).1)
        (hsixP q' (mem_filter.mp hq').1) heq
      exact Prod.ext hx hy
  -- destroyed pairs are few
  have hsplit := card_filter_add_card_filter_not
    (s := P) (fun q => Disjoint (hingeEdges u v w z q.1 q.2) D)
  have hbad : (P.filter (fun q => ¬ Disjoint (hingeEdges u v w z q.1 q.2) D)).card ≤
      (badPairs D u v w z).card :=
    card_le_card (fun q hq => mem_badPairs_of_meets (mem_filter.mp hq).2)
  have hbadR := card_badPairs_le hD u v w z
  have hsplitR : (P.card : ℝ) =
      (P.filter (fun q => Disjoint (hingeEdges u v w z q.1 q.2) D)).card +
      (P.filter (fun q => ¬ Disjoint (hingeEdges u v w z q.1 q.2) D)).card := by
    exact_mod_cast hsplit.symm
  have hsurvR : ((P.filter (fun q => Disjoint (hingeEdges u v w z q.1 q.2) D)).card : ℝ) ≤
      K'.card := by exact_mod_cast hsurv
  have hbadR' : ((P.filter (fun q => ¬ Disjoint (hingeEdges u v w z q.1 q.2) D)).card : ℝ) ≤
      (badPairs D u v w z).card := by exact_mod_cast hbad
  have : 7 * (n * (δ * n)) = 7 * δ * (n : ℝ) ^ 2 := by ring
  linarith

universe u

/-- **Reserve existence together with ledger survival.** The same reserve `X` as in
`exists_class_aware_hinge_reserve` (degree at most `2 ρ n`, chosen before all roots, labels,
families and ledgers) keeps at least `γ² ρ⁷ n² / 32 - 7 δ n²` distinct six-vertex physical
hinges inside `X \ D`, for every edge set `D` of maximum degree at most `δ n`. -/
theorem exists_class_aware_hinge_reserve_with_ledger (γ ρ : ℝ) (hγ : 0 < γ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) :
    ∃ N : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W] (cls : W → Fin 4)
      (G : SimpleGraph W) [DecidableRel G.Adj], N ≤ Fintype.card W →
      (∀ v, γ * Fintype.card W ≤ ((fibre cls v).card : ℝ)) →
      (∀ a b, G.Adj a b ↔ cls a ≠ cls b) →
      ∃ X : Finset (Sym2 W), X ⊆ G.edgeFinset ∧ DegBounded X (2 * ρ * Fintype.card W) ∧
        ∀ {t : ℕ} (p : W → Fin t), (∀ a b, cls a = cls b → p a = p b) →
          ∀ (F : Finset (Multiset (Fin t))) (S S' : Finset W),
            IsCopy p F G S → IsCopy p F G S' → (triEdges S ∩ triEdges S').card = 1 →
            ∀ (D : Finset (Sym2 W)) (δ : ℝ), DegBounded D (δ * Fintype.card W) →
            open Classical in
            γ ^ 2 * ρ ^ 7 * (Fintype.card W : ℝ) ^ 2 / 32 - 7 * δ * (Fintype.card W : ℝ) ^ 2 ≤
              (((X \ D).powerset.filter
                (fun H => IsHinge p F S S' H ∧ (vertSet H).card = 6)).card : ℝ) := by
  obtain ⟨N, hN⟩ := exists_uniform_threshold γ ρ hγ hρ
  refine ⟨N, ?_⟩
  intro W _ _ cls G _ hn hsize hG
  obtain ⟨h2, hb⟩ := hN (Fintype.card W) hn
  have hn0 : 0 < Fintype.card W := by
    by_contra h
    have : Fintype.card W = 0 := by omega
    rw [this] at h2
    norm_num at h2
  obtain ⟨ω, hω⟩ := exists_good_outcome G cls hγ hρ hρ1 hn0 hb
  refine ⟨sampledEdges G ω, sampledEdges_subset G ω, ?_, ?_⟩
  · intro v
    have h := hω (Sum.inl v)
    simp only [badEvent, Set.mem_ofPred_eq, not_le] at h
    exact h.le
  · intro t p hp F S S' hS hS' h1 D δ hD
    exact hinge_supply_after_deletion G cls hG hρ hsize h2 ω hω p hp F S S' hS hS' h1 D hD

end PartitionedTriangleAbsorption.ClassReserveStage65
