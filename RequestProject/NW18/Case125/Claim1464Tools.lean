/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case125.SideStab

/-!
# Tools for Claim 14.6.4: degrees in an idealized two-partitioned host

For a host satisfying (a), (b) of Theorem 14.6 (`IsF0Idealized ε₀ G p`), a vertex misses at most
`(3/2) ε₀ n` vertices of the other part (`miss_cross_le`), and has at least `(1/4 − ε₀) n`
neighbours in its own part.  Consequently a set `D` obtained from a part `V_j` by deleting at
most `3 ε₀ n` vertices induces a graph of minimum degree at least `(1/2 − 9 ε₀) |D|`
(`hdeg_of_large`), and if `V_j` is not `θ`-close to `T₂` or `T̄₂` then any two vertices of `D`
are joined by many walks of length four inside `D` (`many_walks_of_not_sideClose`).
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of vertices of the part `j` which are not neighbours of `v`. -/
def missIn (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2) (v : V) (j : Fin 2) : ℝ :=
  ((partClass p j).card : ℝ) - partDeg G p v j

omit [DecidableEq V] in
lemma partDeg_eq_card_filter (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2) (v : V)
    (j : Fin 2) : partDeg G p v j = ((partClass p j).filter (G.Adj v)).card := by
  unfold partDeg partClass
  rw [filter_filter]
  congr 1
  ext w
  simp [and_comm]

omit [DecidableEq V] in
/-- Removing the non-neighbours of `v` from a subset of `V_j` loses at most `missIn v j`
vertices. -/
lemma card_filter_adj_ge (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2) {j : Fin 2}
    {S : Finset V} (hS : S ⊆ partClass p j) (v : V) :
    (S.card : ℝ) - missIn G p v j ≤ (S.filter (G.Adj v)).card := by
  unfold missIn
  rw [partDeg_eq_card_filter]
  have h1 := card_filter_add_card_filter_not (s := S) (G.Adj v)
  have h2 := card_filter_add_card_filter_not (s := partClass p j) (G.Adj v)
  have h3 : (S.filter (fun x => ¬ G.Adj v x)).card ≤
      ((partClass p j).filter (fun x => ¬ G.Adj v x)).card :=
    card_le_card (filter_subset_filter _ hS)
  have h1' : ((S.filter (G.Adj v)).card : ℝ) + (S.filter (fun x => ¬ G.Adj v x)).card = S.card := by
    exact_mod_cast h1
  have h2' : (((partClass p j).filter (G.Adj v)).card : ℝ) +
      ((partClass p j).filter (fun x => ¬ G.Adj v x)).card = (partClass p j).card := by
    exact_mod_cast h2
  have h3' : ((S.filter (fun x => ¬ G.Adj v x)).card : ℝ) ≤
      ((partClass p j).filter (fun x => ¬ G.Adj v x)).card := by exact_mod_cast h3
  linarith

omit [DecidableEq V] in
lemma card_partClass_add' (p : V → Fin 2) {j j' : Fin 2} (h : j ≠ j') :
    (partClass p j).card + (partClass p j').card = Fintype.card V := by
  have hj' : ∀ v, p v = j' ↔ ¬ p v = j := by
    intro v; constructor
    · rintro rfl; exact fun h' => h h'.symm
    · intro hv; fin_cases j <;> fin_cases j' <;> simp_all <;> omega
  unfold partClass
  rw [show (univ.filter (fun v => p v = j')) = univ.filter (fun v => ¬ p v = j) from
    filter_congr fun v _ => hj' v]
  exact card_filter_add_card_filter_not _

/-- Basic facts on an idealized host. -/
structure IdFacts (e0 : ℝ) (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2) : Prop where
  lo : ∀ j, (1 - e0) * Fintype.card V / 2 ≤ ((partClass p j).card : ℝ)
  hi : ∀ j, ((partClass p j).card : ℝ) ≤ (1 + e0) * Fintype.card V / 2
  cross : ∀ v j, p v ≠ j → missIn G p v j ≤ 3 / 2 * e0 * Fintype.card V
  int : ∀ v, missIn G p v (p v) ≤ ((partClass p (p v)).card : ℝ) - (1 / 4 - e0) * Fintype.card V
  nonneg : ∀ v j, 0 ≤ missIn G p v j

omit [DecidableEq V] in
lemma idFacts_of (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2) {e0 : ℝ}
    (hid : IsF0Idealized e0 G p) : IdFacts e0 G p := by
  obtain ⟨hsz, hint, hcr⟩ := hid
  have hi : ∀ j, ((partClass p j).card : ℝ) ≤ (1 + e0) * Fintype.card V / 2 := by
    intro j
    have hne : j ≠ (if j = 0 then 1 else 0) := by fin_cases j <;> simp
    have h := card_partClass_add' p hne
    have h' : ((partClass p j).card : ℝ) + (partClass p (if j = 0 then 1 else 0)).card =
        Fintype.card V := by exact_mod_cast h
    have := hsz (if j = 0 then 1 else 0)
    linarith
  refine ⟨hsz, hi, fun v j hvj => ?_, fun v => ?_, fun v j => ?_⟩
  · unfold missIn
    have := hcr v j (Ne.symm hvj)
    have := hi j
    linarith
  · unfold missIn
    linarith [(hint v).1]
  · unfold missIn
    rw [partDeg_eq_card_filter, sub_nonneg]
    exact_mod_cast card_le_card (filter_subset _ _)

omit [DecidableEq V] in
/-- A large subset of a part induces a graph of large minimum degree. -/
lemma hdeg_of_large (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2) {e0 : ℝ}
    (hf : IdFacts e0 G p) (he0 : 0 ≤ e0) (he1 : e0 ≤ 1 / 100) {j : Fin 2} {D : Finset V}
    (hDC : D ⊆ partClass p j)
    (hD : ((partClass p j).card : ℝ) - 3 * e0 * Fintype.card V ≤ D.card) :
    ∀ y ∈ D, (1 / 2 - 9 * e0) * D.card ≤ (nbIn G D y).card := by
  intro y hy
  have hpy : p y = j := (mem_filter.mp (hDC hy)).2
  have h1 := card_filter_adj_ge G p hDC y
  have h2 := hf.int y
  rw [hpy] at h2
  have hDle : (D.card : ℝ) ≤ (partClass p j).card := by exact_mod_cast card_le_card hDC
  have h3 := hf.hi j
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hnb : (nbIn G D y).card = (D.filter (G.Adj y)).card := rfl
  rw [hnb]
  have h4 : (1 / 2 - 9 * e0) * D.card ≤ (1 / 2 - 9 * e0) * ((1 + e0) * Fintype.card V / 2) :=
    mul_le_mul_of_nonneg_left (hDle.trans h3) (by linarith)
  nlinarith

omit [Fintype V] in
/-- Few walks in a large subset of a part make the part close to `T₂` or `T̄₂`. -/
lemma isSideClose_of_few_walks (G : SimpleGraph V) [DecidableRel G.Adj] {C D : Finset V}
    (hDC : D ⊆ C) {s t : V} (hs : s ∈ D) (ht : t ∈ D) {σ ε δ θ : ℝ} (hσ0 : 0 < σ)
    (hσ : σ ≤ 1 / 100) (hε0 : 0 ≤ ε) (hε : ε ≤ σ ^ 2)
    (hdeg : ∀ y ∈ D, (1 / 2 - ε) * D.card ≤ (nbIn G D y).card)
    (hW : (walk4 G D s t : ℝ) ≤ σ ^ 6 * D.card ^ 3)
    (hCD : ((C \ D).card : ℝ) ≤ δ * C.card) (hθ : 100 * σ + 4 * δ ≤ θ)
    (hC : 6 ≤ θ * C.card) : IsSideClose θ G C := by
  obtain ⟨X, hX, hXc, b, hcost⟩ := sideCost_small_of_few_walks G D hs ht hσ0 hσ hε0 hε hdeg hW
  obtain ⟨X', hX', hX'c, hX'cost⟩ := exists_sideCost_superset G hDC hX hXc b
  refine ⟨X', hX', hX'c, b, ?_⟩
  have hc : (sideCost G C X' b : ℝ) ≤ sideCost G D X b + 4 * (C \ D).card * C.card + 2 * C.card := by
    exact_mod_cast hX'cost
  have hDC' : (D.card : ℝ) ≤ C.card := by exact_mod_cast card_le_card hDC
  have hD0 : (0 : ℝ) ≤ D.card := Nat.cast_nonneg _
  have hC0 : (0 : ℝ) ≤ C.card := Nat.cast_nonneg _
  have h1 : 100 * σ * (D.card : ℝ) ^ 2 ≤ 100 * σ * (C.card : ℝ) ^ 2 := by
    have : (D.card : ℝ) ^ 2 ≤ (C.card : ℝ) ^ 2 := pow_le_pow_left₀ hD0 hDC' 2
    nlinarith
  have h2 : 4 * ((C \ D).card : ℝ) * C.card ≤ 4 * δ * (C.card : ℝ) ^ 2 := by nlinarith
  have h3 : 6 * (C.card : ℝ) ≤ θ * C.card * C.card := by nlinarith
  nlinarith

/-- **Many walks.**  If the part `V_j` is not `θ`-close to `T₂` or `T̄₂`, then any two vertices
of a subset `D ⊆ V_j` missing at most `3 ε₀ n` vertices of `V_j` are joined by more than
`σ⁶ |D|³` walks of length four inside `D`. -/
lemma many_walks_of_not_sideClose (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2)
    {e0 σ θ : ℝ} (hf : IdFacts e0 G p) (he0 : 0 ≤ e0) (he0σ : 9 * e0 ≤ σ ^ 2) (hσ0 : 0 < σ)
    (hσ : σ ≤ 1 / 100) (hθ : 100 * σ + 36 * e0 ≤ θ) (hn : 18 ≤ θ * Fintype.card V)
    {j : Fin 2} (hnc : ¬ IsSideClose θ G (partClass p j)) {D : Finset V}
    (hDC : D ⊆ partClass p j)
    (hD : ((partClass p j).card : ℝ) - 3 * e0 * Fintype.card V ≤ D.card) {s t : V}
    (hs : s ∈ D) (ht : t ∈ D) : σ ^ 6 * (D.card : ℝ) ^ 3 < walk4 G D s t := by
  have he1 : e0 ≤ 1 / 100 := by nlinarith
  by_contra hW
  push_neg at hW
  apply hnc
  have hlo := hf.lo j
  have hn0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hC3 : (Fintype.card V : ℝ) / 3 ≤ (partClass p j).card := by nlinarith
  refine isSideClose_of_few_walks G hDC hs ht hσ0 hσ (by linarith) he0σ
    (hdeg_of_large G p hf he0 he1 hDC hD) hW (δ := 9 * e0) ?_ (by linarith) ?_
  · have hcs := card_sdiff_add_card_eq_card hDC
    have hcs' : ((partClass p j \ D).card : ℝ) + D.card = (partClass p j).card := by
      exact_mod_cast hcs
    nlinarith
  · have hθ0 : 0 ≤ θ := by nlinarith
    nlinarith

end NashWilliams18
