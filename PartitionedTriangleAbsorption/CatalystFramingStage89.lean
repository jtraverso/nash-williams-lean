/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CatalystSelectionStage89

/-! # Reserving catalysts after deployment and framing them retrospectively

The deployment trace is run first. From its terminal ledger `L` we select the
catalysts outside `B ∪ L`, then carry them unchanged through the whole
deployment. Unlike `MoveLedgerStage88.ledger_with_catalysts`, the theorem
`padded_ledger` below also keeps the continuation property: any later trace
starting from the padded ledger `L ∪ D` and the padded terminal configuration
`Y ∪ D` can be prepended by the padded deployment. This is what lets the
catalyst insertion be appended to the deployment.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CatalystFramingStage89

open Finset AntiEdgeSelection TypedTransformer PhysicalMovesStage86 CatalystSelectionStage89

variable {V : Type*} [DecidableEq V] {t : ℕ}
variable {p : V → Fin t} {F : Finset (Multiset (Fin t))}

/-- A terminal ledger `L` of an actual trace such that, for every edge set `D`
disjoint from `L`, the trace padded by `D` can be continued by any trace
starting from history `L ∪ D` and configuration `Y ∪ D`. -/
theorem padded_ledger {E B U X Y : Finset (Sym2 V)} {n : ℕ}
    (h : PhysicalMoves p F E B U X Y n) (hX : X ⊆ U) :
    ∃ L : Finset (Sym2 V), U ⊆ L ∧ Y ⊆ L ∧ L.card ≤ U.card + 9 * n ∧
      ∀ D : Finset (Sym2 V), Disjoint D L → ∀ W m,
        PhysicalMoves p F E B (L ∪ D) (Y ∪ D) W m →
        PhysicalMoves p F E B (U ∪ D) (X ∪ D) W (n + m) := by
  induction h with
  | stop U X =>
    refine ⟨U, Subset.refl _, hX, by simp, ?_⟩
    intro D _ W m hm
    simpa using hm
  | @step U X Y Q R H n hx hq hf hphys hm hH hR ht ih =>
    have hnext : (X \ Q) ∪ R ⊆ U ∪ H ∪ R := by
      intro e he
      simp only [mem_union, mem_sdiff] at he ⊢
      rcases he with ⟨he, _⟩ | he
      · exact Or.inl (Or.inl (hx he))
      · exact Or.inr he
    obtain ⟨L, hUL, hYL, hc, hcont⟩ := ih hnext
    have hUL' : U ⊆ L := fun e he =>
      hUL (mem_union.mpr (Or.inl (mem_union.mpr (Or.inl he))))
    have hHRL : H ∪ R ⊆ L := by
      intro e he
      rcases mem_union.mp he with he | he
      · exact hUL (mem_union.mpr (Or.inl (mem_union.mpr (Or.inr he))))
      · exact hUL (mem_union.mpr (Or.inr he))
    refine ⟨L, hUL', hYL, ?_, ?_⟩
    · have h1 := card_union_le (U ∪ H) R
      have h2 := card_union_le U H
      omega
    · intro D hDL W m hW
      have htail := hcont D hDL W m hW
      have hQD : Disjoint Q D := (hDL.mono_right ((hq.trans hx).trans hUL')).symm
      have hcfg : (X ∪ D) \ Q ∪ R = ((X \ Q) ∪ R) ∪ D := by
        ext e
        simp only [mem_union, mem_sdiff]
        constructor
        · rintro (⟨he | he, hq'⟩ | he) <;> tauto
        · rintro ((⟨he, hq'⟩ | he) | he)
          · exact Or.inl ⟨Or.inl he, hq'⟩
          · exact Or.inr he
          · exact Or.inl ⟨Or.inr he, fun hq' => disjoint_left.mp hQD hq' he⟩
      have hhist : U ∪ D ∪ H ∪ R = (U ∪ H ∪ R) ∪ D := by
        ext e
        simp only [mem_union]
        tauto
      have hfresh : Disjoint (H ∪ R) (B ∪ (U ∪ D)) := by
        rw [disjoint_left]
        intro e he hb
        simp only [mem_union] at hb
        rcases hb with hb | hb | hb
        · exact disjoint_left.mp hf he (mem_union.mpr (Or.inl hb))
        · exact disjoint_left.mp hf he (mem_union.mpr (Or.inr hb))
        · exact disjoint_left.mp hDL hb (hHRL he)
      have hstep := PhysicalMoves.step (union_subset_union hx (Subset.refl D))
        (hq.trans subset_union_left) hfresh hphys hm hH hR
        (by rw [hcfg, hhist]; exact htail)
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep

/-- Every edge of an allowed decomposition has an allowed label type. -/
theorem link_of_hasDecomp {E : Finset (Sym2 V)} (hE : HasDecomp p F E) {u v : V}
    (he : s(u, v) ∈ E) : ∃ k, Link F (p u) (p v) k := by
  obtain ⟨D, hT, -, hcov⟩ := hE
  rw [← hcov] at he
  obtain ⟨T, hTD, heT⟩ := mem_biUnion.mp he
  simp only [triEdges, mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff] at heT
  obtain ⟨⟨hu, hv⟩, huv⟩ := heT
  obtain ⟨hc, hF⟩ := hT T hTD
  have hu' : u ∈ T.val := hu
  have hv' : v ∈ T.val.erase u := (Multiset.mem_erase_of_ne (Ne.symm huv)).mpr hv
  have h1 : T.val = u ::ₘ v ::ₘ (T.val.erase u).erase v := by
    rw [Multiset.cons_erase hv', Multiset.cons_erase hu']
  have hcard : Multiset.card ((T.val.erase u).erase v) = 1 := by
    have := congrArg Multiset.card h1
    simp only [Multiset.card_cons, Finset.card_val] at this
    rw [hc] at this
    omega
  obtain ⟨w, hw⟩ := Multiset.card_eq_one.mp hcard
  refine ⟨p w, ?_⟩
  rw [h1, hw] at hF
  simpa [Link] using hF

/-- Active edge types persist along any actual trace: surviving edges keep
theirs, and every added edge lies in a decomposed set `H ∪ R`. -/
theorem links_of_trace {E B U X Y : Finset (Sym2 V)} {n : ℕ}
    (h : PhysicalMoves p F E B U X Y n)
    (hX : ∀ u v, s(u, v) ∈ X → ∃ k, Link F (p u) (p v) k) :
    ∀ u v, s(u, v) ∈ Y → ∃ k, Link F (p u) (p v) k := by
  induction h with
  | stop U X => exact hX
  | step _ _ _ _ hm _ _ _ ih =>
    apply ih
    intro u v huv
    rcases mem_union.mp huv with huv | huv
    · exact hX u v (mem_sdiff.mp huv).1
    · exact link_of_hasDecomp hm.2.2 (mem_union.mpr (Or.inr huv))

variable [Fintype V]

/-- **Deployment, catalyst reservation and retrospective framing.** Deploy the
even configuration `X` to a `0`/`2`-configuration `Y` with terminal ledger `L`;
select the catalysts `D` outside `B ∪ L` and outside the active vertices and
the caller's forbidden set `Z`; frame `D` through the deployment, keeping the
continuation from the padded ledger `L ∪ D`. Explicit budget:
`|Z| + 52|X| + 4(d + |U|) < a`; deployment alone uses `37|X|` and the
selection `|Z| + |X| + 15|X| + 4(d + |U| + 9|X|)`. -/
theorem deploy_reserve_frame (G : SimpleGraph V) [DecidableRel G.Adj]
    (a d : ℝ) (hF : ThreeStepLinks F)
    (hs : PairMoveSelectionStage85.CompatibleSupply p F G a)
    (B U X : Finset (Sym2 V)) (Z : Finset V)
    (hB : DegBounded B d) (hd : 0 ≤ d)
    (hXU : X ⊆ U) (hXG : X ⊆ G.edgeFinset) (hXB : Disjoint X B)
    (hZ : ∀ e ∈ X, ∀ v ∈ e, v ∈ Z)
    (hact : ∀ u v, s(u, v) ∈ X → ∃ k, Link F (p u) (p v) k)
    (heven : ∀ v, Even (incidentLoad X v))
    (hb : (Z.card : ℝ) + 52 * X.card + 4 * (d + U.card) < a) :
    ∃ (Y L : Finset (Sym2 V)) (m : ℕ) (co cs ct : V → V), m ≤ X.card ∧
      (∀ v, incidentLoad Y v = 0 ∨ incidentLoad Y v = 2) ∧
      Y ⊆ G.edgeFinset ∧ Disjoint Y B ∧ Y.card = X.card ∧
      (∀ u v, s(u, v) ∈ Y → ∃ k, Link F (p u) (p v) k) ∧
      U ⊆ L ∧ Y ⊆ L ∧ L.card ≤ U.card + 9 * X.card ∧
      Catalysts p F G B L (Z ∪ active Y) (active Y) co cs ct ∧
      (active Y).card = Y.card ∧
      HasDecomp p F (catUnion (active Y) co cs ct) ∧
      catUnion (active Y) co cs ct ⊆ G.edgeFinset ∧
      Disjoint (catUnion (active Y) co cs ct) (B ∪ L) ∧
      (catUnion (active Y) co cs ct).card ≤ 3 * Y.card ∧
      PhysicalMoves p F G.edgeFinset B (U ∪ catUnion (active Y) co cs ct)
        (X ∪ catUnion (active Y) co cs ct) (Y ∪ catUnion (active Y) co cs ct) m ∧
      (∀ W k, PhysicalMoves p F G.edgeFinset B (L ∪ catUnion (active Y) co cs ct)
          (Y ∪ catUnion (active Y) co cs ct) W k →
        PhysicalMoves p F G.edgeFinset B (U ∪ catUnion (active Y) co cs ct)
          (X ∪ catUnion (active Y) co cs ct) W (m + k)) := by
  have hb37 : (Z.card : ℝ) + 37 * X.card + 4 * (d + U.card) < a := by
    have : (0 : ℝ) ≤ X.card := Nat.cast_nonneg _
    linarith
  obtain ⟨Y, m, hm, ht, hdeg, hYG, hYB, hYc⟩ :=
    PairSplitDeploymentStage87.deploy p F hF G a d hs B U X Z hB hd hXU hXG hXB hZ hact
      heven hb37
  obtain ⟨L, hUL, hYL, hLc, hcont⟩ := padded_ledger ht hXU
  have hactY := links_of_trace ht hact
  have hZY : ∀ e ∈ Y, ∀ v ∈ e, v ∈ Z ∪ active Y := fun e he v hv =>
    mem_union.mpr (Or.inr (mem_active_of_mem hdeg he hv))
  have hZc : ((Z ∪ active Y).card : ℝ) ≤ Z.card + (active Y).card := by
    exact_mod_cast card_union_le _ _
  have hloop : ∀ e ∈ Y, ¬ e.IsDiag := fun e he =>
    G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (hYG he))
  have hAc := active_card hloop hdeg
  have hLc' : (L.card : ℝ) ≤ U.card + 9 * X.card := by
    have : L.card ≤ U.card + 9 * X.card :=
      hLc.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 9 hm) _)
    exact_mod_cast this
  have hYc' : (Y.card : ℝ) = X.card := by exact_mod_cast hYc
  have hAc' : ((active Y).card : ℝ) = X.card := by rw [hAc]; exact hYc'
  obtain ⟨co, cs, ct, hc, -, -, hdec, hDG, hDBL, hDc⟩ :=
    select_catalysts p F G a d hs B L Y (Z ∪ active Y) hB hd hYG hdeg hactY hZY
      (by rw [hYc']; linarith)
  have hDL : Disjoint (catUnion (active Y) co cs ct) L :=
    hDBL.mono_right subset_union_right
  refine ⟨Y, L, m, co, cs, ct, hm, hdeg, hYG, hYB, hYc, hactY, hUL, hYL,
    hLc.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 9 hm) _), hc, hAc, hdec, hDG, hDBL,
    hDc, ?_, fun W k hW => hcont _ hDL W k hW⟩
  simpa using hcont _ hDL _ 0 (.stop _ _)

end PartitionedTriangleAbsorption.CatalystFramingStage89
