/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case124.BoundedCore.Rounds
public import PartitionedTriangleAbsorption.PhysicalHingeSupply.Template

@[expose] public section

/-!
# The protected round on an induced host (transport to the parent subtype)

`RoundUnivSpec124` is `RoundSpec124` in the special case where the parent is the whole vertex
type, without the two premises `β ≤ 1` and `F ⊆ E(G)` (the protected round never uses them).  `roundSpec124_of_univ` (proved) transports it to an arbitrary parent `U` through the
induced graph `G[U]` on the subtype `↥U`: edges inside `U` are exactly the images of the edges of
`G[U]`, so the damage, the child, the grandchild, the parity hypotheses and the conclusions
correspond one to one (`Sym2.map Subtype.val` is injective).
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.PhysicalHingeSupply

/-- **The protected round with parent = whole vertex type** (residual proposition). -/
def RoundUnivSpec124 : Prop :=
  ∀ β : ℝ, 0 < β → ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ ∃ q₀ : ℝ, 0 < q₀ ∧
    ∀ q : ℝ, 0 < q → q ≤ q₀ → ∃ κ : ℝ, 0 < κ ∧ ∃ N₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (W Z : Finset V) (F : Finset (Sym2 V)),
        N₀ ≤ Fintype.card V → Z ⊆ W →
        7 * q / 8 * (Fintype.card V : ℝ) ≤ W.card →
        (W.card : ℝ) ≤ 9 * q / 8 * Fintype.card V →
        (Z.card : ℝ) ≤ 9 * q / 8 * W.card →
        (3 / 4 - θ) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        ¬ IsExtremal (β / 4) G →
        (∀ v, (3 / 4 - θ) * (W.card : ℝ) ≤ ((W.filter (G.Adj v)).card : ℝ)) →
        Disjoint F (insideEdges G W) → DegBounded F (κ * Fintype.card V) →
        (∀ x, x ∉ W → Even (((G.edgeFinset \ F).filter fun e => x ∈ e).card)) →
        ∃ Q ⊆ G.edgeFinset \ F, HasDecomp onePart K3fam Q ∧
          ((G.edgeFinset \ F) \ insideEdges G W) ⊆ Q ∧ Disjoint Q (insideEdges G Z) ∧
          DegBounded (Q ∩ insideEdges G W) (κ * W.card)

section Transport

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
lemma mem_map_edgeEmb_iff {U : Finset V} (E : Finset (Sym2 (U : Set V))) (e : Sym2 V) :
    e ∈ E.map (edgeEmb (Function.Embedding.subtype (· ∈ (U : Set V)))) ↔
      ∃ e' ∈ E, Sym2.map Subtype.val e' = e := by
  simp only [edgeEmb, mem_map, Function.Embedding.coeFn_mk]
  exact Iff.rfl

omit [Fintype V] in
lemma filter_map_edgeEmb {U : Finset V} (E : Finset (Sym2 (U : Set V))) (v : (U : Set V)) :
    (E.map (edgeEmb (Function.Embedding.subtype (· ∈ (U : Set V))))).filter
        (fun e => v.1 ∈ e) =
      (E.filter fun e => v ∈ e).map
        (edgeEmb (Function.Embedding.subtype (· ∈ (U : Set V)))) := by
  ext e
  simp only [mem_filter, mem_map_edgeEmb_iff]
  constructor
  · rintro ⟨⟨e', he', rfl⟩, hv⟩
    refine ⟨e', ⟨he', ?_⟩, rfl⟩
    obtain ⟨a, ha, hav⟩ := Sym2.mem_map.mp hv
    rwa [← Subtype.ext hav]
  · rintro ⟨e', ⟨he', hv⟩, rfl⟩
    exact ⟨⟨e', he', rfl⟩, Sym2.mem_map.mpr ⟨v, hv, rfl⟩⟩

lemma insideEdges_eq_map (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V)
    (hW : W ⊆ U) [DecidableRel (G.induce (U : Set V)).Adj] :
    insideEdges G W = (insideEdges (G.induce (U : Set V))
      (univ.filter fun x : (U : Set V) => x.1 ∈ W)).map
        (edgeEmb (Function.Embedding.subtype (· ∈ (U : Set V)))) := by
  ext e
  rw [mem_map_edgeEmb_iff]
  induction e using Sym2.ind with
  | _ x y =>
    simp only [insideEdges, mem_inter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      triEdges, mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff]
    constructor
    · rintro ⟨hxy, ⟨hx, hy⟩, hne⟩
      refine ⟨s(⟨x, hW hx⟩, ⟨y, hW hy⟩), ?_, rfl⟩
      simp only [SimpleGraph.mem_edgeSet, SimpleGraph.comap_adj, Function.Embedding.subtype_apply,
        SimpleGraph.induce, mem_filter, mem_univ, true_and, Finset.mk_mem_sym2_iff,
        Sym2.mk_isDiag_iff, Subtype.mk.injEq]
      exact ⟨hxy, ⟨hx, hy⟩, hne⟩
    · rintro ⟨e', he', hmap⟩
      induction e' using Sym2.ind with
      | _ a b =>
        simp only [Sym2.map_mk] at hmap
        simp only [SimpleGraph.mem_edgeSet, SimpleGraph.comap_adj,
          Function.Embedding.subtype_apply, SimpleGraph.induce, mem_filter, mem_univ, true_and,
          Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff] at he'
        rcases Sym2.eq_iff.mp hmap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨he'.1, he'.2.1, fun h => he'.2.2 (Subtype.ext h)⟩
        · exact ⟨he'.1.symm, ⟨he'.2.1.2, he'.2.1.1⟩, fun h => he'.2.2 (Subtype.ext h.symm)⟩

lemma insideEdges_self_eq_map (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    [DecidableRel (G.induce (U : Set V)).Adj] :
    insideEdges G U = (G.induce (U : Set V)).edgeFinset.map
        (edgeEmb (Function.Embedding.subtype (· ∈ (U : Set V)))) := by
  rw [insideEdges_eq_map G U U subset_rfl]
  congr 1
  have : (univ.filter fun x : (U : Set V) => x.1 ∈ U) = univ := by
    ext x; simp only [mem_filter, mem_univ, true_and, iff_true]; exact x.2
  rw [this, insideEdges_univ]

end Transport

/-- **The round for an arbitrary parent from the round on the whole type** (proved). -/
theorem roundSpec124_of_univ (hR : RoundUnivSpec124) : RoundSpec124 := by
  intro β hβ _
  obtain ⟨θ, hθ0, hθ1, q₀, hq₀, hR'⟩ := hR β hβ
  refine ⟨θ, hθ0, hθ1, q₀, hq₀, fun q hq hqq₀ => ?_⟩
  obtain ⟨κ, hκ, N₀, hround⟩ := hR' q hq hqq₀
  refine ⟨κ, hκ, N₀, fun V _ _ G _ U W Z F hN hWU hZW hW1 hW2 hZ hdeg hnx hpar hFU hFW hFd
    heven => ?_⟩
  classical
  set f : (U : Set V) ↪ V := Function.Embedding.subtype (· ∈ (U : Set V)) with hf
  set H := G.induce (U : Set V) with hH
  set W' : Finset (U : Set V) := univ.filter fun x => x.1 ∈ W with hW'
  set Z' : Finset (U : Set V) := univ.filter fun x => x.1 ∈ Z with hZ'
  set F' : Finset (Sym2 (U : Set V)) := H.edgeFinset.filter fun e => Sym2.map Subtype.val e ∈ F
    with hF'
  have hmapW : ∀ {T : Finset V}, T ⊆ U →
      (univ.filter fun x : (U : Set V) => x.1 ∈ T).map f = T := by
    intro T hT
    ext x
    simp only [mem_map, mem_filter, mem_univ, true_and, hf, Function.Embedding.subtype_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨⟨x, hT hx⟩, hx, rfl⟩
  have hcardW : W'.card = W.card := by rw [← card_map f, hmapW hWU]
  have hcardZ : Z'.card = Z.card := by rw [← card_map f, hmapW (hZW.trans hWU)]
  have hcardV : Fintype.card (U : Set V) = U.card := by simp
  have hinU := insideEdges_self_eq_map G U
  have hinW := insideEdges_eq_map G U W hWU
  have hinZ := insideEdges_eq_map G U Z (hZW.trans hWU)
  -- hypotheses on the subtype
  have hZW' : Z' ⊆ W' := fun x hx => by
    simp only [hZ', hW', mem_filter, mem_univ, true_and] at hx ⊢; exact hZW hx
  have hpar' : ∀ v : (U : Set V), (3 / 4 - θ) * (W'.card : ℝ) ≤ ((W'.filter (H.Adj v)).card : ℝ) := by
    intro v
    have h := hpar v.1 v.2
    have hc : (W'.filter (H.Adj v)).card = (W.filter (G.Adj v.1)).card := by
      rw [← card_map f]
      congr 1
      ext x
      simp only [mem_map, mem_filter, mem_univ, true_and, hW', hf,
        Function.Embedding.subtype_apply, hH, SimpleGraph.comap_adj, SimpleGraph.induce]
      constructor
      · rintro ⟨y, ⟨hy, hadj⟩, rfl⟩; exact ⟨hy, hadj⟩
      · rintro ⟨hx, hadj⟩; exact ⟨⟨x, hWU hx⟩, ⟨hx, hadj⟩, rfl⟩
    rw [hcardW, hc]; exact h
  have hmapF : F'.map (edgeEmb f) = F := by
    ext e
    rw [mem_map_edgeEmb_iff]
    constructor
    · rintro ⟨e', he', rfl⟩; exact (mem_filter.mp he').2
    · intro he
      have := hFU he
      rw [hinU, mem_map_edgeEmb_iff] at this
      obtain ⟨e', he', rfl⟩ := this
      exact ⟨e', mem_filter.mpr ⟨he', he⟩, rfl⟩
  have hFW' : Disjoint F' (insideEdges H W') := by
    rw [disjoint_left]
    intro e he hin
    have h1 : Sym2.map Subtype.val e ∈ F := (mem_filter.mp he).2
    have h2 : Sym2.map Subtype.val e ∈ insideEdges G W := by
      rw [hinW, mem_map_edgeEmb_iff]; exact ⟨e, hin, rfl⟩
    exact disjoint_left.mp hFW h1 h2
  have hFd' : DegBounded F' (κ * Fintype.card (U : Set V)) := by
    intro v
    have h := hFd v.1
    rw [← hmapF, filter_map_edgeEmb, card_map] at h
    rw [hcardV]; exact h
  have hsdiff : (H.edgeFinset \ F').map (edgeEmb f) = insideEdges G U \ F := by
    rw [Finset.map_sdiff, hmapF, ← hinU]
  have heven' : ∀ x : (U : Set V), x ∉ W' →
      Even (((H.edgeFinset \ F').filter fun e => x ∈ e).card) := by
    intro x hx
    have hxW : x.1 ∉ W := fun h => hx (by simp [hW', h])
    have h := heven x.1 (mem_sdiff.mpr ⟨x.2, hxW⟩)
    rw [← hsdiff, filter_map_edgeEmb, card_map] at h
    exact h
  obtain ⟨Q', hQ'sub, hQ'dec, hQ'cov, hQ'Z, hQ'deg⟩ := hround (U : Set V) H W' Z' F'
    (by rw [hcardV]; exact hN) hZW' (by rw [hcardW, hcardV]; exact hW1)
    (by rw [hcardW, hcardV]; exact hW2) (by rw [hcardZ, hcardW]; exact hZ)
    (by rw [hcardV]; convert hdeg using 3) (by convert hnx using 1) hpar' hFW' hFd' heven'
  refine ⟨Q'.map (edgeEmb f), ?_, hasDecomp_map f (fun _ => rfl) hQ'dec, ?_, ?_, ?_⟩
  · rw [← hsdiff]; exact map_subset_map.mpr hQ'sub
  · intro e he
    rw [← hsdiff, hinW, ← Finset.map_sdiff] at he
    obtain ⟨e', he', rfl⟩ := (mem_map_edgeEmb_iff _ _).mp he
    exact mem_map_of_mem _ (hQ'cov he')
  · rw [hinZ]; exact (disjoint_map _).mpr hQ'Z
  · intro v
    by_cases hv : v ∈ U
    · have h := hQ'deg ⟨v, hv⟩
      rw [hinW, ← map_inter, show v = (⟨v, hv⟩ : (U : Set V)).1 from rfl, filter_map_edgeEmb,
        card_map]
      rw [hcardW] at h
      exact h
    · have : ((Q'.map (edgeEmb f) ∩ insideEdges G W).filter fun e => v ∈ e) = ∅ := by
        rw [filter_eq_empty_iff]
        intro e he hve
        exact hv (hWU (mem_of_mem_insideEdges (mem_inter.mp he).2 hve))
      rw [this, card_empty, Nat.cast_zero]
      positivity

end NashWilliams18
