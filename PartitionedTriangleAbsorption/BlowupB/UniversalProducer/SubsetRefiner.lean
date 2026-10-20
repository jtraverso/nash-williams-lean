/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.UniversalProducer.ClassRefiner

/-!
# The existing heap refiner, run on a vertex subset and lifted back to the host

`subset_refiner`: if the host restricted to a vertex set `W` is anti-edgeful for the one-part
triangle family, then `exists_universal_refiner_alpha` on the subtype `↥W` (with the rescaled
parameters `λ n / |W|`, `ρ n / |W|`) gives, on the host, a fixed remainder and a fixed library
of loopless even pieces with at most `42` edges, all inside `W`, refining every leftover
`L ⊆ X` inside `W` with even degrees and `3 ∣ |L|`, with host budgets
`Δ(R) ≤ 4 λ n`, `#library ≤ 1224 ρ n²`, total library load `≤ 4096 λ n`.
-/

namespace PartitionedTriangleAbsorption.BlowupB.UniversalProducer

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.StructuralF3General PartitionedTriangleAbsorption.OnePart

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The library index type of the heap refiner. -/
abbrev HeapIdx := ℕ × Bool × Fin 3 × Fin 3

theorem liftE_subset_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V)
    [DecidableRel (G.comap (Subtype.val : W → V)).Adj] {E : Finset (Sym2 W)}
    (hE : E ⊆ (G.comap (Subtype.val : W → V)).edgeFinset) : liftE W E ⊆ G.edgeFinset := by
  intro e he
  obtain ⟨e', he', rfl⟩ := mem_image.mp he
  have := hE he'
  induction e' using Sym2.ind with
  | _ a b =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this
    rw [Sym2.map_mk, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact this

theorem restrE_subset_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V)
    [DecidableRel (G.comap (Subtype.val : W → V)).Adj] {X : Finset (Sym2 V)}
    (hX : X ⊆ G.edgeFinset) : restrE W X ⊆ (G.comap (Subtype.val : W → V)).edgeFinset := by
  classical
  intro e he
  have hmem : Sym2.map Subtype.val e ∈ X := by unfold restrE at he; exact (mem_filter.mp he).2
  have := hX hmem
  induction e using Sym2.ind with
  | _ a b =>
    rw [Sym2.map_mk, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact this

omit [Fintype V] in
theorem incidentLoad_liftE_real_le (W : Finset V) (E : Finset (Sym2 W)) {d : ℝ} (hd : 0 ≤ d)
    (h : ∀ w, (incidentLoad E w : ℝ) ≤ d) (v : V) : (incidentLoad (liftE W E) v : ℝ) ≤ d := by
  by_cases hv : v ∈ W
  · rw [show v = (⟨v, hv⟩ : W).1 from rfl, incidentLoad_liftE_of_mem]; exact h _
  · rw [incidentLoad_liftE_of_not E hv]; simpa using hd

/-- **The heap refiner on a vertex subset.** -/
theorem subset_refiner (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V)
    [DecidableRel (G.comap (Subtype.val : W → V)).Adj]
    (hWpos : 0 < Fintype.card W) (lam rho beta : ℝ) (hlam : 0 < lam) (hrho : 0 < rho)
    (hnW : 64 * lam * Fintype.card V ≤ Fintype.card W)
    (hscale : 2 ^ 24 * rho ≤ lam ^ 2) (hn1 : 1 ≤ rho * Fintype.card V)
    (hn2 : 256 ≤ lam * Fintype.card V)
    (hbeta : 8 * (lam * Fintype.card V / Fintype.card W) ≤ beta)
    (hanti : AntiEdgeful part1 triFam (G.comap (Subtype.val : W → V)) beta)
    (X : Finset (Sym2 V)) (hXG : X ⊆ G.edgeFinset) (hX : DegBounded X (2 * rho * Fintype.card V)) :
    ∃ (ind : Finset HeapIdx) (P : HeapIdx → Finset (Sym2 V)) (R : Finset (Sym2 V)),
      R ⊆ G.edgeFinset ∧ (∀ e ∈ R, ∀ v ∈ e, v ∈ W) ∧ Disjoint R X ∧
      (∀ j ∈ ind, P j ⊆ X ∪ R ∧ (∀ e ∈ P j, ¬ e.IsDiag) ∧ (∀ v, Even (incidentLoad (P j) v)) ∧
        (P j).card ≤ 42 ∧ ∀ e ∈ P j, ∀ v ∈ e, v ∈ W) ∧
      (∀ L ⊆ X, (∀ e ∈ L, ∀ v ∈ e, v ∈ W) → Even3 L →
        ∃ s ⊆ ind, (s : Set HeapIdx).PairwiseDisjoint P ∧ s.biUnion P = R ∪ L) ∧
      (∀ v, (incidentLoad R v : ℝ) ≤ 4 * lam * Fintype.card V) ∧
      (ind.card : ℝ) ≤ 1224 * rho * (Fintype.card V : ℝ) ^ 2 ∧
      ∀ v, ((∑ j ∈ ind, incidentLoad (P j) v : ℕ) : ℝ) ≤ 4096 * lam * Fintype.card V := by
  classical
  have hnWr : (0 : ℝ) < Fintype.card W := by exact_mod_cast hWpos
  have hWle : (Fintype.card W : ℝ) ≤ Fintype.card V := by
    have : Fintype.card W ≤ Fintype.card V := Fintype.card_subtype_le _
    exact_mod_cast this
  have hn0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  set n : ℝ := (Fintype.card V : ℝ) with hn
  set nW : ℝ := (Fintype.card W : ℝ) with hnWdef
  have hlW : lam * n / nW * nW = lam * n := div_mul_cancel₀ _ hnWr.ne'
  have hrW : rho * n / nW * nW = rho * n := div_mul_cancel₀ _ hnWr.ne'
  have hlamW : 0 < lam * n / nW := by
    have : 0 < lam * n := by nlinarith
    positivity
  have hrhoW : 0 < rho * n / nW := by
    have : 0 < rho * n := by linarith
    positivity
  have hlam64 : lam * n / nW ≤ 1 / 64 := by
    rw [div_le_iff₀ hnWr]; linarith
  have hscaleW : 2 ^ 24 * (rho * n / nW) ≤ (lam * n / nW) ^ 2 := by
    rw [div_pow, mul_div_assoc', div_le_div_iff₀ hnWr (by positivity)]
    have h1 : 2 ^ 24 * rho * n * nW ≤ lam ^ 2 * n * n := by
      have := mul_le_mul_of_nonneg_right hscale (mul_nonneg hn0 hnWr.le)
      have h2 : lam ^ 2 * (n * nW) ≤ lam ^ 2 * (n * n) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hWle hn0) (sq_nonneg _)
      nlinarith
    nlinarith
  have hn1W : 1 ≤ rho * n / nW * nW := by rw [hrW]; exact hn1
  have hn2W : 256 ≤ lam * n / nW * nW := by rw [hlW]; exact hn2
  have hXW : DegBounded (restrE W X) (2 * (rho * n / nW) * nW) := by
    intro w
    have h1 := incidentLoad_restrE_le X w
    have h2 := hX w.1
    have : 2 * (rho * n / nW) * nW = 2 * rho * n := by rw [mul_assoc, hrW]; ring
    rw [this]
    change (incidentLoad (restrE W X) w : ℝ) ≤ _
    have h1' : (incidentLoad (restrE W X) w : ℝ) ≤ incidentLoad X w.1 := by exact_mod_cast h1
    exact h1'.trans h2
  obtain ⟨ind, PW, RW, hRG, hRX, hrefW, hPW, hRdeg, hcard, hload⟩ :=
    exists_universal_refiner_alpha (G.comap (Subtype.val : W → V)) (restrE W X)
      (restrE_subset_edgeFinset G W hXG) (lam * n / nW) (rho * n / nW) hlamW hlam64 hrhoW
      hscaleW hn1W hn2W hXW beta hbeta hanti
  refine ⟨ind, fun j => liftE W (PW j), liftE W RW, liftE_subset_edgeFinset G W hRG,
    fun e he => mem_W_of_mem_liftE he, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [disjoint_left]
    intro e he heX
    obtain ⟨e', he', rfl⟩ := mem_image.mp he
    have : e' ∈ restrE W X := by unfold restrE; exact mem_filter.mpr ⟨mem_univ _, heX⟩
    exact disjoint_left.mp hRX he' this
  · intro j hj
    obtain ⟨hsub, hloop, heven, -, hc⟩ := hPW j hj
    refine ⟨?_, loopless_liftE hloop, even_liftE heven, (card_liftE _).trans_le hc,
      fun e he => mem_W_of_mem_liftE he⟩
    refine (liftE_mono hsub).trans ?_
    rw [liftE_union, liftE_restrE]
    exact union_subset_union (filter_subset _ _) subset_rfl
  · intro L hLX hLW hL3
    set LW := restrE W L with hLWdef
    have hlift : liftE W LW = L := by
      rw [hLWdef, liftE_restrE]
      exact filter_true_of_mem hLW
    have hLWX : LW ⊆ restrE W X := restrE_mono hLX
    have hloopL : ∀ e ∈ LW, ¬ e.IsDiag := by
      intro e he hd
      have hmem : Sym2.map Subtype.val e ∈ liftE W LW := mem_liftE.mpr he
      rw [hlift] at hmem
      have hG := hXG (hLX hmem)
      induction e using Sym2.ind with
      | _ a b =>
        rw [Sym2.mk_isDiag_iff] at hd
        subst hd
        rw [Sym2.map_mk, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hG
        exact G.irrefl hG
    have hdivW : IsIntDiv part1 triFam LW := by
      rw [isIntDiv_part1_iff LW hloopL]
      refine ⟨?_, ?_⟩
      · rw [← card_liftE, hlift]; exact hL3.1
      · intro w
        rw [← incidentLoad_liftE_of_mem, hlift]
        exact hL3.2 w.1
    obtain ⟨s, hs, hdisj, hbu⟩ := hrefW LW hLWX hdivW
    refine ⟨s, hs, ?_, ?_⟩
    · intro a ha b hb hab
      exact disjoint_liftE (hdisj ha hb hab)
    · change s.biUnion (fun j => liftE W (PW j)) = liftE W RW ∪ L
      rw [← liftE_biUnion, hbu, liftE_union, hlift]
  · intro v
    refine incidentLoad_liftE_real_le W RW (by positivity) (fun w => ?_) v
    have := hRdeg w
    have h : 4 * (lam * n / nW) * nW = 4 * lam * n := by rw [mul_assoc, hlW]; ring
    rw [h] at this
    exact this
  · refine hcard.trans ?_
    have h : 1224 * (rho * n / nW) * nW ^ 2 = 1224 * rho * n * nW := by
      field_simp
    rw [h]
    have := mul_le_mul_of_nonneg_left hWle (by positivity : (0 : ℝ) ≤ 1224 * rho * n)
    nlinarith
  · intro v
    have h4 : 4096 * (lam * n / nW) * nW = 4096 * lam * n := by rw [mul_assoc, hlW]; ring
    by_cases hv : v ∈ W
    · have heq : ∑ j ∈ ind, incidentLoad (liftE W (PW j)) v =
          ∑ j ∈ ind, incidentLoad (PW j) ⟨v, hv⟩ :=
        sum_congr rfl fun j _ => incidentLoad_liftE_of_mem (PW j) ⟨v, hv⟩
      change ((∑ j ∈ ind, incidentLoad (liftE W (PW j)) v : ℕ) : ℝ) ≤ _
      rw [heq]
      have := hload ⟨v, hv⟩
      rw [h4] at this
      exact this
    · have heq : ∑ j ∈ ind, incidentLoad (liftE W (PW j)) v = 0 :=
        sum_eq_zero fun j _ => incidentLoad_liftE_of_not (PW j) hv
      change ((∑ j ∈ ind, incidentLoad (liftE W (PW j)) v : ℕ) : ℝ) ≤ _
      rw [heq]
      simp only [Nat.cast_zero]
      positivity

end PartitionedTriangleAbsorption.BlowupB.UniversalProducer
