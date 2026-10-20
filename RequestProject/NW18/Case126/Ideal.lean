/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case125.Theorem146
import RequestProject.NW18.Case125.F0HingeCount

/-!
# Idealized `F`-blowups (towards Theorem 14.7)

Notation for a `t`-partitioned graph `G` (partition `p : V → Fin t`) and a family `F` of
partitioned triangles:

* `clsT p i` — the part `V_i`; `degT G p v i = |N(v) ∩ V_i|`;
* `comNbT G p u v k` — the common neighbours of `u, v` in `V_k`;
* `AllowedT F i j` — some type of `F` contains the pair `i, j`, i.e. `j ∈ N_F(i)`;
* `thirdsT F i j` — the classes `l` with `T_{ijl} ∈ F`;
* `IsIdealizedT F ε G p` — `G` is an `ε`-balanced, `ε`-nearly-complete `F`-blowup: every part
  has at least `(1 − ε) n / t` vertices, every edge joins an allowed pair of parts, and every
  vertex `v` misses at most `ε n` vertices of every part `V_j` with `j ∈ N_F(p v)`.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

/-- The part `V_i`. -/
def clsT (p : V → Fin t) (i : Fin t) : Finset V := univ.filter (fun v => p v = i)

/-- `|N(v) ∩ V_i|`. -/
def degT (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin t) (v : V) (i : Fin t) : ℕ :=
  (univ.filter (fun w => G.Adj v w ∧ p w = i)).card

/-- Common neighbours of `u, v` in `V_k`. -/
def comNbT (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin t) (u v : V) (k : Fin t) :
    Finset V :=
  univ.filter (fun w => G.Adj u w ∧ G.Adj w v ∧ p w = k)

/-- The pair of parts `i, j` occurs in some type of `F`. -/
def AllowedT (F : Finset (Multiset (Fin t))) (i j : Fin t) : Prop :=
  ∃ l, ({i, j, l} : Multiset (Fin t)) ∈ F

instance (F : Finset (Multiset (Fin t))) (i j : Fin t) : Decidable (AllowedT F i j) := by
  unfold AllowedT; infer_instance

/-- The classes `l` with `T_{ijl} ∈ F`. -/
def thirdsT (F : Finset (Multiset (Fin t))) (i j : Fin t) : Finset (Fin t) :=
  univ.filter (fun l => ({i, j, l} : Multiset (Fin t)) ∈ F)

/-- `G` is an `ε`-balanced `ε`-nearly-complete `F`-blowup. -/
def IsIdealizedT (F : Finset (Multiset (Fin t))) (ε : ℝ) (G : SimpleGraph V)
    [DecidableRel G.Adj] (p : V → Fin t) : Prop :=
  (∀ i, (1 - ε) * Fintype.card V / t ≤ ((clsT p i).card : ℝ)) ∧
  (∀ u v, G.Adj u v → AllowedT F (p u) (p v)) ∧
  (∀ v j, AllowedT F (p v) j → ((clsT p j).card : ℝ) - ε * Fintype.card V ≤ (degT G p v j : ℝ))

/-- Every allowed pair has exactly two third classes. -/
def TwoThirds (F : Finset (Multiset (Fin t))) : Prop :=
  ∀ i j, AllowedT F i j → (thirdsT F i j).card = 2

lemma triple_swap12 (i j l : Fin t) : ({i, j, l} : Multiset (Fin t)) = {j, i, l} := by
  simp only [Multiset.insert_eq_cons]; exact Multiset.cons_swap _ _ _

lemma triple_swap23 (i j l : Fin t) : ({i, j, l} : Multiset (Fin t)) = {i, l, j} := by
  simp only [Multiset.insert_eq_cons]
  congr 1
  exact (Multiset.pair_comm l j).symm

lemma allowedT_symm {F : Finset (Multiset (Fin t))} {i j : Fin t} (h : AllowedT F i j) :
    AllowedT F j i := by
  obtain ⟨l, hl⟩ := h
  exact ⟨l, by rwa [triple_swap12]⟩

lemma allowedT_of_mem {F : Finset (Multiset (Fin t))} {i j l : Fin t}
    (h : ({i, j, l} : Multiset (Fin t)) ∈ F) : AllowedT F i l :=
  ⟨j, by rwa [triple_swap23]⟩

lemma allowedT_of_mem' {F : Finset (Multiset (Fin t))} {i j l : Fin t}
    (h : ({i, j, l} : Multiset (Fin t)) ∈ F) : AllowedT F j l :=
  allowedT_of_mem (j := i) (by rwa [triple_swap12])

/-! ### Elementary counting -/

omit [DecidableEq V] in
lemma sum_card_clsT (p : V → Fin t) : ∑ i, (clsT p i).card = Fintype.card V := by
  rw [← card_univ (α := V)]
  exact (card_eq_sum_card_fiberwise (f := p) (t := univ) (fun _ _ => by simp)).symm

lemma card_comNbT_ge (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin t) (u v : V)
    (k : Fin t) :
    (degT G p u k : ℝ) + degT G p v k - (clsT p k).card ≤ ((comNbT G p u v k).card : ℝ) := by
  set A := univ.filter (fun w => G.Adj u w ∧ p w = k)
  set B := univ.filter (fun w => G.Adj v w ∧ p w = k)
  have hAB : A ∩ B = comNbT G p u v k := by
    ext w; simp only [A, B, comNbT, mem_inter, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, -⟩; exact ⟨h1, h3.symm, h2⟩
    · rintro ⟨h1, h3, h2⟩; exact ⟨⟨h1, h2⟩, h3.symm, h2⟩
  have hU : A ∪ B ⊆ clsT p k := by
    intro w hw
    simp only [A, B, mem_union, mem_filter, mem_univ, true_and] at hw
    simp only [clsT, mem_filter, mem_univ, true_and]
    rcases hw with h | h <;> exact h.2
  have h1 := card_union_add_card_inter A B
  have h2 := card_le_card hU
  have e1 : (degT G p u k : ℝ) = A.card := rfl
  have e2 : (degT G p v k : ℝ) = B.card := rfl
  rw [← hAB, e1, e2]
  have h1' : ((A ∪ B).card : ℝ) + (A ∩ B).card = A.card + B.card := by exact_mod_cast h1
  have h2' : ((A ∪ B).card : ℝ) ≤ (clsT p k).card := by exact_mod_cast h2
  linarith

omit [DecidableEq V] in
lemma card_comNbT_le_class (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin t)
    (u v : V) (k : Fin t) : (comNbT G p u v k).card ≤ (clsT p k).card :=
  card_le_card fun w hw => by
    simp only [comNbT, mem_filter, mem_univ, true_and] at hw
    simp only [clsT, mem_filter, mem_univ, true_and]; exact hw.2.2

omit [DecidableEq V] in
lemma degT_le_class (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin t) (v : V)
    (k : Fin t) : degT G p v k ≤ (clsT p k).card :=
  card_le_card fun w hw => by
    simp only [mem_filter, mem_univ, true_and] at hw
    simp only [clsT, mem_filter, mem_univ, true_and]; exact hw.2

omit [DecidableEq V] in
/-- Upper bound on a part of a balanced four-partition. -/
lemma card_clsT_le_four {ε : ℝ} (p : V → Fin 4)
    (h : ∀ i, (1 - ε) * Fintype.card V / 4 ≤ ((clsT p i).card : ℝ)) (i : Fin 4) :
    ((clsT p i).card : ℝ) ≤ (1 + 3 * ε) * Fintype.card V / 4 := by
  have hs : ((clsT p 0).card : ℝ) + (clsT p 1).card + (clsT p 2).card + (clsT p 3).card =
      Fintype.card V := by
    have := sum_card_clsT p
    rw [Fin.sum_univ_four] at this
    exact_mod_cast this
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  fin_cases i <;> simp <;> linarith

/-! ### Copies through an edge -/

/-- The `F`-copies through an edge `uv` correspond to the common neighbours `w` of `u, v` with
`T_{p u, p v, p w} ∈ F`. -/
lemma card_copies_through_gen (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V} (huv : G.Adj u v) :
    ((copies p F G).filter (fun s => s(u, v) ∈ triEdges s)).card =
      (univ.filter (fun w => G.Adj u w ∧ G.Adj w v ∧
        ({p u, p v, p w} : Multiset (Fin t)) ∈ F)).card := by
  symm
  refine card_bij (fun w _ => ({u, v, w} : Finset V)) ?_ ?_ ?_
  · intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw
    obtain ⟨huw, hwv, hty⟩ := hw
    have h1 : u ≠ v := G.ne_of_adj huv
    have h2 : u ≠ w := G.ne_of_adj huw
    have h3 : v ≠ w := (G.ne_of_adj hwv).symm
    refine mem_filter.mpr ⟨mem_copies_iff'.mpr ⟨SimpleGraph.is3Clique_triple_iff.mpr
      ⟨huv, huw, hwv.symm⟩, ?_⟩, mk_mem_triEdges.mpr ⟨by simp, by simp, h1⟩⟩
    rw [triple_val_map p h1 h2 h3]
    exact hty
  · intro w hw w' hw' h
    simp only [mem_filter, mem_univ, true_and] at hw hw'
    have h' : ({u, v, w} : Finset V) = {u, v, w'} := h
    have hw_mem : w ∈ ({u, v, w'} : Finset V) := by
      rw [← h']; simp
    simp only [mem_insert, mem_singleton] at hw_mem
    rcases hw_mem with rfl | rfl | rfl
    · exact absurd hw.1 (SimpleGraph.irrefl G)
    · exact absurd hw.2.1 (SimpleGraph.irrefl G)
    · rfl
  · intro s hs
    obtain ⟨hsC, hes⟩ := mem_filter.mp hs
    obtain ⟨hcl, hty⟩ := mem_copies_iff'.mp hsC
    obtain ⟨hus, hvs, huv'⟩ := mk_mem_triEdges.mp hes
    have hsub : ({u, v} : Finset V) ⊆ s := by
      intro x hx; simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption
    have hcard : (s \ {u, v}).card = 1 := by
      rw [card_sdiff_of_subset hsub, hcl.card_eq, card_pair huv']
    obtain ⟨w, hw⟩ := card_eq_one.mp hcard
    have hws : w ∈ s \ {u, v} := by rw [hw]; simp
    simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at hws
    obtain ⟨hws, hwu, hwv⟩ := hws
    have hseq : s = {u, v, w} := by
      ext x
      constructor
      · intro hx
        by_cases hxu : x = u
        · simp [hxu]
        by_cases hxv : x = v
        · simp [hxv]
        have : x ∈ s \ {u, v} := by simp [hx, hxu, hxv]
        rw [hw] at this
        simp at this; simp [this]
      · intro hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
    have hadj := hcl.1
    have huw : G.Adj u w := hadj hus hws (Ne.symm hwu)
    have hvw : G.Adj v w := hadj hvs hws (Ne.symm hwv)
    refine ⟨w, ?_, hseq.symm⟩
    simp only [mem_filter, mem_univ, true_and]
    refine ⟨huw, hvw.symm, ?_⟩
    rw [hseq, triple_val_map p huv' (Ne.symm hwu) (Ne.symm hwv)] at hty
    exact hty

/-- The number of copies through `uv` is the sum, over the third classes `l`, of the common
neighbours in `V_l`. -/
lemma card_copies_through_eq_sum (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V} (huv : G.Adj u v) :
    ((copies p F G).filter (fun s => s(u, v) ∈ triEdges s)).card =
      ∑ l ∈ thirdsT F (p u) (p v), (comNbT G p u v l).card := by
  rw [card_copies_through_gen p F G huv]
  rw [card_eq_sum_card_fiberwise (f := p) (t := thirdsT F (p u) (p v))]
  · refine sum_congr rfl fun l hl => ?_
    congr 1
    ext w
    simp only [comNbT, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨⟨h1, h2, -⟩, h3⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨h1, h2, ?_⟩, h3⟩
      rw [h3]
      exact (mem_filter.mp hl).2
  · intro w hw
    have hw' := (mem_filter.mp (mem_coe.mp hw)).2
    exact mem_coe.mpr (mem_filter.mpr ⟨mem_univ _, hw'.2.2⟩)

end NashWilliams18
