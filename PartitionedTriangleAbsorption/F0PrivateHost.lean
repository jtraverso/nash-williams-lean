/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.IntegerCertificate.Absorber
public import PartitionedTriangleAbsorption.PrivateTemplateStage69.DeletedHost

/-! # Common-neighbour geometry on the actual domain used for private absorbers. -/

@[expose] public section

namespace PartitionedTriangleAbsorption.F0PrivateHost

open Finset F0Geometric SignedCertificate TypedApplicationLinks
open PhysicalHingeSupply SparseReserveGeometry AntiEdgeSelection

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Restricting the vertex domain loses at most the number of excluded vertices. -/
theorem induced_common_loss (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Finset V) (R : Finset K) (i : Fin 2) :
    (univ.filter (fun w => p w = i ∧ ∀ u ∈ R.image Subtype.val, G.Adj u w)).card ≤
      (univ.filter (fun w : K => p w.val = i ∧ ∀ u ∈ R, G.Adj u.val w.val)).card +
        (univ \ K).card := by
  classical
  let C := univ.filter (fun w => p w = i ∧ ∀ u ∈ R.image Subtype.val, G.Adj u w)
  let Q := univ.filter (fun w : K => p w.val = i ∧ ∀ u ∈ R, G.Adj u.val w.val)
  have hsub : C ⊆ Q.image Subtype.val ∪ (univ \ K) := by
    intro w hw
    obtain ⟨hp, hroot⟩ := (mem_filter.mp hw).2
    by_cases hwK : w ∈ K
    · apply mem_union_left
      refine mem_image.mpr ⟨⟨w, hwK⟩, ?_, rfl⟩
      exact mem_filter.mpr ⟨mem_univ _, hp, fun u hu =>
        hroot u.val (mem_image.mpr ⟨u, hu, rfl⟩)⟩
    · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_univ _, hwK⟩)
  have hcount := (card_le_card hsub).trans (card_union_le _ _)
  rw [card_image_of_injective _ Subtype.val_injective] at hcount
  exact hcount

/-- Edge deletion and vertex restriction are charged to the same original query. -/
theorem commonNbrRich_deleted_induced {r : ℕ} (p : V → Fin 2) (G J : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel J.Adj] (K : Finset V) (β β' d : ℝ)
    (hβ' : 0 ≤ β') (hd : 0 ≤ d) (hG : CommonNbrRich r p G β)
    (hdel : ∀ v, ((univ.filter (fun w => G.Adj v w ∧ ¬ J.Adj v w)).card : ℝ) ≤ d)
    (hbudget : (univ \ K).card + r * d ≤ (β - β') * Fintype.card V) :
    CommonNbrRich r (fun w : K => p w.val) (J.induce (↑K : Set V)) β' := by
  classical
  intro R hR i
  have hmap : (R.image Subtype.val).card ≤ r := (card_image_le).trans hR
  have h1 := hG (R.image Subtype.val) hmap i
  have h2 := card_common_delete p G J d hdel (R.image Subtype.val) i
  have h3 : ((univ.filter
      (fun w => p w = i ∧ ∀ u ∈ R.image Subtype.val, J.Adj u w)).card : ℝ) ≤
      (univ.filter (fun w : K => p w.val = i ∧ ∀ u ∈ R, J.Adj u.val w.val)).card +
        (univ \ K).card := by
    exact_mod_cast induced_common_loss p J K R i
  have hrd : ((R.image Subtype.val).card : ℝ) * d ≤ r * d :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hmap) hd
  have horder : (Fintype.card K : ℝ) ≤ Fintype.card V := by
    exact_mod_cast Fintype.card_subtype_le (fun v => v ∈ K)
  have hscale := mul_le_mul_of_nonneg_left horder hβ'
  change β' * Fintype.card K ≤
    ((univ.filter (fun w : K => p w.val = i ∧ ∀ u ∈ R, J.Adj u.val w.val)).card : ℝ)
  linarith only [h1, h2, h3, hrd, hscale, hbudget]

/-- The source on a retained domain, with its original physical edges. -/
noncomputable def source (K : Finset V) (P : Finset (Sym2 V)) : Finset (Sym2 K) :=
  univ.filter (fun e => Sym2.map Subtype.val e ∈ P)

omit [Fintype V] in
/-- Retaining every source endpoint gives exactly the original source on mapping back. -/
theorem source_map (K : Finset V) (P : Finset (Sym2 V))
    (hkeep : ∀ e ∈ P, ∀ v ∈ e, v ∈ K) :
    (source K P).map (edgeEmb ⟨Subtype.val, Subtype.val_injective⟩) = P := by
  classical
  ext e
  simp only [mem_map, source, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨e', he', rfl⟩
    exact he'
  · intro he
    induction e using Sym2.ind with
    | _ a b =>
      have ha := hkeep s(a, b) he a (Sym2.mem_mk_left _ _)
      have hb := hkeep s(a, b) he b (Sym2.mem_mk_right _ _)
      exact ⟨s(⟨a, ha⟩, ⟨b, hb⟩), he, rfl⟩

/-- An actual typed private absorber avoids occupied edges and saturated non-root vertices. -/
theorem exists_private_avoiding (β : ℝ) (hβ : 0 < β) (m : ℕ) :
    ∃ b N : ℕ, 0 < b ∧ ∀ (V : Type) [Fintype V] [DecidableEq V]
      (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
      (P B : Finset (Sym2 V)) (Z : Finset V) (d : ℝ),
        2 * N ≤ Fintype.card V → 2 * Z.card ≤ Fintype.card V → 0 ≤ d →
        CN6 p G β → DegBounded B d →
        (Z.card : ℝ) + 6 * d ≤ β * Fintype.card V / 2 →
        (∀ e ∈ P, e ∈ G.edgeSet) → P.card ≤ m → IsIntDiv p F0 P →
        ∃ A : Finset (Sym2 V),
          (∀ e ∈ A, e ∈ G.edgeSet) ∧ Disjoint A B ∧
          HasDecomp p F0 A ∧ HasDecomp p F0 (A ∪ P) ∧
          A.card ≤ b ∧ (vertSet A).card ≤ b ∧
          ∀ e ∈ A, ∀ v ∈ e, v ∉ vertSet P → v ∉ Z := by
  obtain ⟨C, N, hprod⟩ := IntegerCertificate.cn6_signed_absorber
    (β / 2) (by positivity) m
  refine ⟨max 1 (2 * (C * m)), N, by omega, ?_⟩
  intro V _ _ p G _ P B Z d hn hZ hd hG hB hbudget hPG hm hdiv
  classical
  let K := univ \ (Z \ vertSet P)
  let f : K ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let J := withoutEdges G (B \ P)
  let JK := J.induce (↑K : Set V)
  have hkeep : ∀ e ∈ P, ∀ v ∈ e, v ∈ K := by
    intro e he v hv
    have hvP : v ∈ vertSet P := mem_filter.mpr ⟨mem_univ _, e, he, hv⟩
    simp [K, hvP]
  have hback : (source K P).map (edgeEmb f) = P := source_map K P hkeep
  have hexclude : univ \ K ⊆ Z := by
    intro v hv
    have hvK := (mem_sdiff.mp hv).2
    by_contra hvZ
    exact hvK (by simp [K, hvZ])
  have hexcard := card_le_card hexclude
  have hKN : N ≤ Fintype.card K := by
    have hpart := card_sdiff_add_card_eq_card (subset_univ K)
    rw [card_univ] at hpart
    rw [Fintype.card_coe]
    omega
  have hdel : ∀ v,
      ((univ.filter (fun w => G.Adj v w ∧ ¬ J.Adj v w)).card : ℝ) ≤ d := by
    intro v
    have h1 := PrivateTemplateStage69.deleted_card_le G (B \ P) v
    have h2 : ((B \ P).filter (fun e => v ∈ e)).card ≤
        (B.filter (fun e => v ∈ e)).card :=
      card_le_card (filter_subset_filter _ sdiff_subset)
    have h3 : ((univ.filter (fun w => G.Adj v w ∧ ¬ J.Adj v w)).card : ℝ) ≤
        incidentLoad B v := by exact_mod_cast h1.trans h2
    exact h3.trans (hB v)
  have hJK : CN6 (fun w : K => p w.val) JK (β / 2) :=
    commonNbrRich_deleted_induced p G J K β (β / 2) d (by positivity) hd hG hdel
      (by have h : ((univ \ K).card : ℝ) ≤ Z.card := by exact_mod_cast hexcard
          linarith only [hbudget, h])
  have hPK : source K P ⊆ JK.edgeFinset := by
    intro e he
    have horig : Sym2.map Subtype.val e ∈ P := (mem_filter.mp he).2
    induction e using Sym2.ind with
    | _ a b =>
      have hGorig := hPG _ horig
      change G.Adj a.val b.val at hGorig
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      change J.Adj a.val b.val
      exact (withoutEdges_adj G (B \ P) a.val b.val).mpr
        ⟨hGorig, fun h => (mem_sdiff.mp h).2 horig⟩
  have hdivK : IsIntDiv (fun w : K => p w.val) F0 (source K P) := by
    apply PrivateTemplateStage69.isIntDiv_comap f
    rw [hback]
    exact hdiv
  have hcardK : (source K P).card ≤ m := by
    have hc := congrArg Finset.card hback
    rw [card_map] at hc
    exact hc.trans_le hm
  obtain ⟨Ak, Qk, hAk, -, hPA, -, -, -, -, hdec, habs, -, hc, -, -, -, -, -⟩ :=
    hprod K hKN (fun w => p w.val) JK hJK (source K P) hPK hcardK hdivK
  let A := Ak.map (edgeEmb f)
  have hAP : Disjoint A P := by
    rw [← hback]
    exact (disjoint_map _).mpr hPA.symm
  have hAJ : ∀ e ∈ A, e ∈ J.edgeSet := by
    intro e he
    obtain ⟨e', he', rfl⟩ := mem_map.mp he
    have h := SimpleGraph.mem_edgeFinset.mp (hAk he')
    induction e' using Sym2.ind with
    | _ a b =>
      change J.Adj a.val b.val
      exact h
  have hhost : ∀ e ∈ A, e ∈ G.edgeSet ∧ e ∉ B := by
    intro e he
    have h := hAJ e he
    have hnP := disjoint_left.mp hAP he
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at h ⊢
      obtain ⟨hGedge, hfree⟩ := (withoutEdges_adj G (B \ P) a b).mp h
      exact ⟨hGedge, fun hBedge => hfree (mem_sdiff.mpr ⟨hBedge, hnP⟩)⟩
  have hAc : A.card ≤ C * m := by simpa only [A, card_map] using hc
  refine ⟨A, fun e he => (hhost e he).1, disjoint_left.mpr (fun e he => (hhost e he).2),
    PhysicalHingeSupply.hasDecomp_map f (pV := p) (fun _ => rfl) hdec,
    ?_, by omega, ?_, ?_⟩
  · have h := PhysicalHingeSupply.hasDecomp_map f (pV := p) (fun _ => rfl) habs
    rw [map_union, hback] at h
    exact h
  · exact (SignedHinge.card_vertSet_le A).trans (by omega)
  · intro e he v hv hvP hvZ
    obtain ⟨e', he', rfl⟩ := mem_map.mp he
    have hv' : v ∈ Sym2.map Subtype.val e' := hv
    obtain ⟨w, -, hw⟩ := Sym2.mem_map.mp hv'
    have hwK : v ∈ K := hw ▸ w.property
    exact (mem_sdiff.mp hwK).2 (mem_sdiff.mpr ⟨hvZ, hvP⟩)

end PartitionedTriangleAbsorption.F0PrivateHost
