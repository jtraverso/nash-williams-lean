/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedNoCommon.Physical

/-!
# Universal absorbers for trivial-lattice families WITHOUT common neighbour classes

`GuardedSupply.to_ordinaryAntiEdgeful` needs a common allowed partner for every two classes,
because the ordinary refiner `exists_universal_refiner_alpha` asks for `γ n` common neighbours of
every two vertices. Here we avoid that hypothesis:

1. run the ordinary refiner in the COMPLETE graph `⊤` on `V` (every two vertices have `n - 2`
   common neighbours there), obtaining virtual edges `R` and pieces of at most `42` edges;
2. replace every virtual edge by a physical path of length four in `G`
   (`exists_path_system`, needing only `Walk4` of the allowed-pair graph and guarded supply of
   order `2`), weighting each virtual edge by the number of pieces that use it;
3. the physical pieces (`physPiece`) refine every divisible `L ⊆ X` into `Even3` pieces of at most
   `168` edges, which are `F`-divisible by the trivial lattice;
4. terminal absorbers for `168`-edge pieces and the finite-library assembly finish as before.

The quantifier order is unchanged: `R`, the paths and the absorber are fixed before `L`.
-/

namespace PaddedNoCommon

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.StructuralF3General.PrivateFamily
open PaddedF12 PaddedGeneral

/-- Explicit witness bound `B` for pieces of at most `K` edges. -/
def WitnessBoundK (F : Finset (Multiset (Fin 4))) (K B : ℕ) : Prop :=
  ∀ {W : Type} [DecidableEq W] (p : W → Fin 4) (P : Finset (Sym2 W)),
    P.card ≤ K → IsIntDiv p F P → ∃ c : Multiset (Fin 4) → ℤ,
      edgeVec p P = ∑ τ ∈ F, c τ • typeEdgeVec τ ∧ negativeMass F c ≤ B

variable {V : Type} [Fintype V] [DecidableEq V]

theorem card_le_sum_incidentLoad (E : Finset (Sym2 V)) :
    E.card ≤ ∑ w, incidentLoad E w := by
  simp only [incidentLoad_eq_sum]
  rw [sum_comm, card_eq_sum_ones]
  refine sum_le_sum fun e _ => ?_
  induction e using Sym2.ind with
  | _ a b =>
    calc 1 = (if a ∈ s(a, b) then 1 else 0) := by simp
      _ ≤ ∑ w, (if w ∈ s(a, b) then 1 else 0) :=
        single_le_sum (f := fun w => if w ∈ s(a, b) then 1 else 0) (fun _ _ => Nat.zero_le _)
          (mem_univ a)

theorem antiEdgeful_top (hn : 4 ≤ Fintype.card V) :
    AntiEdgeful OnePart.part1 OnePart.triFam (⊤ : SimpleGraph V) (1 / 2) := by
  intro τ _ i j k _ u v huv _ _
  have hsub : (univ \ {u, v} : Finset V) ⊆
      univ.filter (fun w => (⊤ : SimpleGraph V).Adj u w ∧ (⊤ : SimpleGraph V).Adj w v ∧
        OnePart.part1 w = k) := by
    intro w hw
    simp only [mem_sdiff, mem_univ, mem_insert, mem_singleton, true_and, not_or] at hw
    exact mem_filter.mpr ⟨mem_univ _, by simpa using Ne.symm hw.1, by simpa using hw.2,
      Subsingleton.elim _ _⟩
  set S := univ.filter (fun w => (⊤ : SimpleGraph V).Adj u w ∧ (⊤ : SimpleGraph V).Adj w v ∧
        OnePart.part1 w = k) with hS
  have hc := card_le_card hsub
  have hc2 : (univ \ {u, v} : Finset V).card = Fintype.card V - 2 := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, card_pair huv]
  rw [hc2] at hc
  have hcR : ((Fintype.card V - 2 : ℕ) : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hc
  have h4 : (4 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  rw [Nat.cast_sub (by omega)] at hcR
  push_cast at hcR
  linarith

/-- The number of pieces containing a virtual edge is bounded by the incidence at an end. -/
theorem multiplicity_le_incidence {I : Type*} (P : I → Finset (Sym2 V)) (s : Finset I)
    (e : Sym2 V) : (∑ i ∈ s, if e ∈ P i then 1 else 0) ≤ ∑ i ∈ s, incidentLoad (P i) (endU e) := by
  refine sum_le_sum fun i _ => ?_
  split_ifs with he
  · refine card_pos.mpr ⟨e, mem_filter.mpr ⟨he, ?_⟩⟩
    have hm := Sym2.mem_mk_left (endU e) (endV e)
    rwa [mk_ends] at hm
  · exact Nat.zero_le _

theorem sum_multiplicity_le {I : Type*} (P : I → Finset (Sym2 V)) (s : Finset I)
    (R : Finset (Sym2 V)) :
    (∑ e ∈ R, ∑ i ∈ s, if e ∈ P i then 1 else 0) ≤ ∑ w, ∑ i ∈ s, incidentLoad (P i) w := by
  rw [sum_comm, sum_comm (s := univ)]
  refine sum_le_sum fun i _ => ?_
  calc (∑ e ∈ R, if e ∈ P i then 1 else 0) = (R.filter (· ∈ P i)).card := by
        rw [card_filter]
    _ ≤ (P i).card := card_le_card fun e he => (mem_filter.mp he).2
    _ ≤ _ := card_le_sum_incidentLoad (P i)

/-- **The universal absorber budget for a trivial-lattice family with `Walk4`.** -/
theorem universal_budget_walk (F : Finset (Multiset (Fin 4)))
    (hcard : ∀ τ ∈ F, Multiset.card τ = 3) (hthree : ThreeStepLinks F)
    (hwalk : Walk4 (fun i j : Fin 4 => ∃ k, Link F i j k))
    (htriv : TrivialLattice F) (B : ℕ) (hB : WitnessBoundK F 168 B)
    (hord : terminalOrder 168 B 4 ≤ 2 ^ 21) (hsize : terminalSize 168 B ≤ 2 ^ 21)
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (γ lam rho δ Q : ℝ)
    (hG : ∀ a b, G.Adj a b → ∃ k, Link F (p a) (p b) k)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) (2 ^ 21) (γ * Fintype.card V))
    (hlam : 0 < lam) (hlam64 : lam ≤ 1 / 64) (hrho : 0 < rho) (hscale : 2 ^ 24 * rho ≤ lam ^ 2)
    (hn1 : 1 ≤ rho * Fintype.card V) (hn2 : 256 ≤ lam * Fintype.card V) (hδ : 0 < δ)
    (hQ : 0 < Q)
    (hpathB : 3 * (4100 * lam * (Fintype.card V : ℝ) ^ 2) / Q + 3 +
      2 * (2 * rho * Fintype.card V + 4 * lam * Fintype.card V +
        2 * (Q + (4096 * lam * Fintype.card V + 1)) + 2) < γ * Fintype.card V)
    (hembed : (2 ^ 21 : ℝ) + (2 ^ 21 : ℝ) * (2 * δ * Fintype.card V) < γ * Fintype.card V / 2)
    (hfixed : (2 ^ 21 : ℝ) ≤ δ * Fintype.card V / 4)
    (hledgerB : 2 * rho * Fintype.card V + 4 * lam * Fintype.card V +
      2 * (Q + (4096 * lam * Fintype.card V + 1)) ≤ δ * Fintype.card V)
    (hrootB : (2 ^ 21 : ℝ) * (4096 * lam * Fintype.card V +
      2 * (Q + (4096 * lam * Fintype.card V + 1))) ≤ δ * Fintype.card V / 2)
    (hcountB : 4 * (2 * rho + 16 * lam + 1224 * rho * 2 ^ 21) ≤ δ * γ) :
    UniversalAbsorbers p F G rho δ := by
  classical
  set n : ℝ := (Fintype.card V : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hnpos : 0 < n := by
    by_contra h
    have heq : n = 0 := le_antisymm (le_of_not_gt h) hn0
    rw [heq, mul_zero] at hn1
    norm_num at hn1
  have hn4 : 4 ≤ Fintype.card V := by
    have h1 : (2 ^ 14 : ℝ) ≤ n := by
      have := mul_le_mul_of_nonneg_right hlam64 hn0
      nlinarith
    have : ((4 : ℕ) : ℝ) ≤ (Fintype.card V : ℝ) := by rw [← hn]; push_cast; linarith
    exact_mod_cast this
  obtain ⟨C, hCdef⟩ : ∃ C : ℕ, C = 2 ^ 21 := ⟨_, rfl⟩
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  have hCR : (C : ℝ) = 2 ^ 21 := by rw [hCdef]; norm_num
  -- the terminal step for pieces of at most 168 edges
  have hterminal : ∀ (a d : ℝ) (L : Finset (Sym2 V)) (Z : Finset V),
      GuardedSupply p G (fun i j => ∃ k, Link F i j k) (2 ^ 21) a →
      DegBounded L d → 0 ≤ d → (2 ^ 21 : ℝ) + Z.card + (2 ^ 21 : ℝ) * d < a →
      ∀ P : Finset (Sym2 V), P.card ≤ 168 → (∀ e ∈ P, ¬ e.IsDiag) → IsIntDiv p F P →
      ∃ A : Finset (Sym2 V), TerminalAbsorber p F G P L Z (2 ^ 21) A := by
    intro a d L Z hsa hL hd hbudget P hK hloop hdiv
    have hqR : (terminalOrder 168 B 4 : ℝ) ≤ (2 ^ 21 : ℝ) := by exact_mod_cast hord
    have hbudget' : (terminalOrder 168 B 4 : ℝ) + Z.card + terminalOrder 168 B 4 * d < a := by
      have hm := mul_le_mul_of_nonneg_right hqR hd
      linarith
    obtain ⟨A, hA⟩ := guarded_terminal_absorber_of_mass F hcard hthree 168 B
      (fun pW PW hKW hdivW => hB pW PW hKW hdivW)
      p G a d L Z (hsa.mono hord le_rfl) hL hd hbudget' P hK hloop hdiv
    exact ⟨A, { hA with card_le := hA.card_le.trans hsize }⟩
  -- this `hs` is for the terminal step; guarded supply for the terminal uses `a`
  have hstep : PrivateStep p F G 168 C (δ * n) (2 * δ * n) (γ * n) := by
    rw [hCdef]
    intro L hL hLc P hPG hm hdiv
    let High : Finset V := univ.filter fun v => (δ * n) < (incidentLoad L v : ℝ)
    have hHigh : (High.card : ℝ) ≤ γ * n / 2 := by
      have hc := card_highLoad_le L (δ * n)
      change (High.card : ℝ) * (δ * n) ≤ 2 * L.card at hc
      have hδn : 0 < δ * n := by positivity
      nlinarith
    have hbudget' : (2 ^ 21 : ℝ) + High.card + (2 ^ 21 : ℝ) * (2 * δ * n) < γ * n := by
      linarith
    have hloop : ∀ e ∈ P, ¬ e.IsDiag := by
      intro e he
      induction e using Sym2.ind with
      | _ x y =>
        have hxy : G.Adj x y := SimpleGraph.mem_edgeFinset.mp (hPG he)
        intro hd
        exact G.ne_of_adj hxy (by simpa using hd)
    obtain ⟨A, hA⟩ := hterminal (γ * n) (2 * δ * n) L High hs hL (by positivity) hbudget' P hm
      hloop hdiv
    refine ⟨A, hA.subgraph, hA.avoidLedger, hA.decomp, hA.decomp_union, hA.card_le, ?_⟩
    intro v hv
    rcases hA.vertices v hv with hp | hz
    · exact Or.inl hp
    · exact Or.inr (le_of_not_gt fun h => hz (mem_filter.mpr ⟨mem_univ _, h⟩))
  intro X hXG hX
  have hloopG : ∀ P ⊆ G.edgeFinset, ∀ e ∈ P, ¬ e.IsDiag :=
    fun P hP e he => G.not_isDiag_of_mem_edgeFinset (hP he)
  have hactG : ∀ P ⊆ G.edgeFinset, ActiveEdges F p P := fun P hP a b hab =>
    hG a b (SimpleGraph.mem_edgeFinset.mp (hP hab))
  -- 1. the virtual refiner in the complete graph
  have hXtop : X ⊆ (⊤ : SimpleGraph V).edgeFinset := by
    intro e he
    have hnd := hloopG X hXG e he
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.top_adj]
      intro hab; exact hnd (by simp [hab])
  obtain ⟨indices, P, R, hRtop, hRX, href, hpieces, hRdeg, hcardI, hinc⟩ :=
    exists_universal_refiner_alpha (⊤ : SimpleGraph V) X hXtop lam rho hlam hlam64 hrho
      (by nlinarith only [hscale, hrho.le]) hn1 hn2 hX (1 / 2) (by linarith)
      (antiEdgeful_top hn4)
  have hRloop : ∀ e ∈ R, ¬ e.IsDiag := fun e he =>
    (⊤ : SimpleGraph V).not_isDiag_of_mem_edgeFinset (hRtop he)
  -- 2. weights and the physical paths
  let wt : Sym2 V → ℕ := fun e => (∑ i ∈ indices, if e ∈ P i then 1 else 0) + 1
  have hwt1 : ∀ e ∈ R, 1 ≤ wt e := fun e _ => Nat.le_add_left _ _
  have hwtM : ∀ e ∈ R, (wt e : ℝ) ≤ 4096 * lam * n + 1 := by
    intro e _
    have h1 := multiplicity_le_incidence P indices e
    have h2 : ((∑ i ∈ indices, incidentLoad (P i) (endU e) : ℕ) : ℝ) ≤ 4096 * lam * n :=
      hinc (endU e)
    have h3 : ((∑ i ∈ indices, if e ∈ P i then 1 else 0 : ℕ) : ℝ) ≤ 4096 * lam * n :=
      le_trans (by exact_mod_cast h1) h2
    change (((∑ i ∈ indices, if e ∈ P i then 1 else 0) + 1 : ℕ) : ℝ) ≤ _
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  have hW : ∑ e ∈ R, (wt e : ℝ) ≤ 4100 * lam * n ^ 2 := by
    have h1 := sum_multiplicity_le P indices R
    have h2 : ((∑ w, ∑ i ∈ indices, incidentLoad (P i) w : ℕ) : ℝ) ≤ n * (4096 * lam * n) := by
      calc ((∑ w, ∑ i ∈ indices, incidentLoad (P i) w : ℕ) : ℝ)
          = ∑ w, ((∑ i ∈ indices, incidentLoad (P i) w : ℕ) : ℝ) := Nat.cast_sum _ _
        _ ≤ ∑ _w : V, 4096 * lam * n := sum_le_sum fun w _ => hinc w
        _ = n * (4096 * lam * n) := by rw [sum_const, card_univ, nsmul_eq_mul]
    have h3 := FiniteLibrary.card_le_order_mul_degree R _ hRdeg
    have hsum : ∑ e ∈ R, (wt e : ℝ) =
        ((∑ e ∈ R, ∑ i ∈ indices, if e ∈ P i then 1 else 0 : ℕ) : ℝ) + R.card := by
      simp only [wt]
      push_cast
      rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_one]
    have h1' : ((∑ e ∈ R, ∑ i ∈ indices, if e ∈ P i then 1 else 0 : ℕ) : ℝ) ≤
        ((∑ w, ∑ i ∈ indices, incidentLoad (P i) w : ℕ) : ℝ) := by exact_mod_cast h1
    rw [hsum]
    change _ ≤ n * (4 * lam * n) at h3
    nlinarith
  obtain ⟨x, y, z, hpath, havoid, hdisj, hint⟩ := exists_path_system p G _ (γ * n)
    (hs.mono (by norm_num) le_rfl) hwalk X R hRloop (2 * rho * n) (4 * lam * n) hX hRdeg wt
    (4096 * lam * n + 1) (4100 * lam * n ^ 2) Q hwt1 hwtM hW (by positivity) (by positivity)
    (by positivity) hQ hpathB
  have hsys : PathSystem G X R x y z := ⟨hRX, hRloop, hpath, havoid, hdisj⟩
  -- 3. the physical pieces
  set R' := R.biUnion (physPath x y z) with hR'
  let P' : ℕ × Bool × Fin 3 × Fin 3 → Finset (Sym2 V) := fun i => physPiece X x y z (P i)
  have hR'G : R' ⊆ G.edgeFinset :=
    biUnion_subset.mpr fun e he => pathEdges_subset (hpath e he)
  have hR'X : Disjoint R' X := (disjoint_biUnion_left _ _ _).mpr fun e he => havoid e he
  have hPsub : ∀ i ∈ indices, P i ⊆ X ∪ R := fun i hi => (hpieces i hi).1
  have href' : RefinerAssembly.RefinesReserve (p := p) (F := F) indices P' X R' := by
    intro L hL hdivL
    have hloop := hloopG L (hL.trans hXG)
    have h3 : OnePart.Even3 L := ((htriv p L hloop).mp hdivL).2
    obtain ⟨s, hs_sub, hsdis, hsU⟩ := href L hL ((OnePart.isIntDiv_part1_iff L hloop).mpr h3)
    exact ⟨s, hs_sub, (hsys.physPiece_refines P s (fun i hi => hPsub i (hs_sub hi)) hsdis L hL
      hsU).1, (hsys.physPiece_refines P s (fun i hi => hPsub i (hs_sub hi)) hsdis L hL hsU).2⟩
  have hP'G : ∀ i ∈ indices, P' i ⊆ G.edgeFinset := fun i hi =>
    hsys.physPiece_subset_G hXG (hPsub i hi)
  have hP'sub : ∀ i ∈ indices, P' i ⊆ X ∪ R' := fun i hi => hsys.physPiece_subset (hPsub i hi)
  have hP'card : ∀ i ∈ indices, (P' i).card ≤ 168 := fun i hi =>
    (hsys.physPiece_card_le (hPsub i hi)).trans (by have := (hpieces i hi).2.2.2.2; omega)
  have hP'div : ∀ i ∈ indices, IsIntDiv p F (P' i) := by
    intro i hi
    have hE3 : OnePart.Even3 (P i) := ⟨(hpieces i hi).2.2.2.1, (hpieces i hi).2.2.1⟩
    exact (htriv p (P' i) (hloopG _ (hP'G i hi))).mpr
      ⟨hactG _ (hP'G i hi), hsys.physPiece_even3 (hPsub i hi) hE3⟩
  -- loads
  set Λ : ℝ := 4096 * lam * n + 2 * (Q + (4096 * lam * n + 1)) with hΛ
  have hload : ∀ v, ((∑ i ∈ indices, incidentLoad (P' i) v : ℕ) : ℝ) ≤ Λ := by
    intro v
    have h1 := hsys.sum_physPiece_incidentLoad P indices hPsub wt
      (fun e _ => Nat.le_succ _) v
    have h1' : ((∑ i ∈ indices, incidentLoad (P' i) v : ℕ) : ℝ) ≤
        ((∑ i ∈ indices, incidentLoad (P i) v : ℕ) : ℝ) + 2 * (intLoad wt R x y z v : ℝ) := by
      exact_mod_cast h1
    have h2 := hinc v
    have h3 := hint v
    linarith
  set ρL : ℝ := 2 * rho * n + 4 * lam * n + 2 * (Q + (4096 * lam * n + 1)) with hρL
  have hledger : DegBounded (X ∪ R') ρL := by
    have hR'deg : DegBounded R' (4 * lam * n + 2 * (Q + (4096 * lam * n + 1))) := by
      intro v
      have h1 := incidentLoad_biUnion_physPath_le R x y z hRloop hpath wt hwt1 v
      have h1' : ((incidentLoad R' v : ℕ) : ℝ) ≤
          (incidentLoad R v : ℝ) + 2 * (intLoad wt R x y z v : ℝ) := by exact_mod_cast h1
      have h2 := hRdeg v
      have h3 := hint v
      change ((incidentLoad R' v : ℕ) : ℝ) ≤ _
      change ((incidentLoad R v : ℕ) : ℝ) ≤ _ at h2
      linarith
    have := degBounded_union hX hR'deg
    rw [hρL, show 2 * rho * n + 4 * lam * n + 2 * (Q + (4096 * lam * n + 1)) =
      2 * rho * n + (4 * lam * n + 2 * (Q + (4096 * lam * n + 1))) by ring]
    exact this
  have hdegree : max ρL (δ * n + C) + C * Λ ≤ 2 * δ * n := by
    have hmax : max ρL (δ * n + C) ≤ δ * n + C := max_le (by rw [hρL]; linarith) le_rfl
    rw [hCR] at hmax ⊢
    linarith
  have hcount : 4 * (((X ∪ R').card : ℝ) + indices.card * C) ≤ (δ * n) * (γ * n) := by
    have hXc := FiniteLibrary.card_le_order_mul_degree X _ hX
    have hRc := FiniteLibrary.card_le_order_mul_degree R _ hRdeg
    have hR'c : (R'.card : ℝ) ≤ 4 * R.card := by
      have : R'.card ≤ ∑ e ∈ R, (physPath x y z e).card := card_biUnion_le
      have h4 : ∑ e ∈ R, (physPath x y z e).card = ∑ _e ∈ R, 4 :=
        sum_congr rfl fun e he => pathEdges_card (ends_ne (hRloop e he)) (hpath e he)
      rw [h4, sum_const, smul_eq_mul] at this
      exact_mod_cast (this.trans (by rw [mul_comm]))
    have hU : ((X ∪ R').card : ℝ) ≤ X.card + R'.card := by exact_mod_cast card_union_le X R'
    change (X.card : ℝ) ≤ n * (2 * rho * n) at hXc
    change (R.card : ℝ) ≤ n * (4 * lam * n) at hRc
    rw [hCR]
    have hI : (indices.card : ℝ) * 2 ^ 21 ≤ 1224 * rho * n ^ 2 * 2 ^ 21 :=
      mul_le_mul_of_nonneg_right hcardI (by norm_num)
    have hgoal : 4 * (2 * rho + 16 * lam + 1224 * rho * 2 ^ 21) * n ^ 2 ≤ δ * γ * n ^ 2 :=
      mul_le_mul_of_nonneg_right hcountB (sq_nonneg n)
    nlinarith
  exact FiniteLibrary.universal_from_finite_library p F G 168 C (δ * n) (2 * δ * n)
    Λ ρL (γ * n) hstep X R' hR'X hXG hR'G hledger hdegree indices P' href' hP'sub hP'card
    hP'div hload hcount

end PaddedNoCommon
