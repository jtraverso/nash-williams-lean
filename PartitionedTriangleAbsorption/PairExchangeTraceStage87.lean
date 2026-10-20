/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PairExchangeProducerStage87

/-! # The framed, physically supported three-move exchange trace

The selected embedding gives the three typed modes through
`PairMoveStage85.physical_transformer`; the finite skeleton trace
`PairExchangeStage86.exchange_trace` is restricted to its new edges,
transported by `PhysicalMoves.map`, and framed so that the untouched part
`X \ Q` of the ambient configuration is carried along unchanged.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PairExchangeTraceStage87

open Finset AntiEdgeSelection TypedTransformer PhysicalHingeSupply PhysicalMovesStage86
  PairExchangeStage86 PairExchangeTemplateStage87 PairExchangeProducerStage87
  PairMoveAssemblyStage85

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

theorem final_subset_added : final ⊆ added := by
  unfold final added H₁ H₂ H₃ R₁ R₂ R₃ PairMoveStage85.gadget PairMoveStage85.target
    first second third edgeEmb
  decide

/-- The four destination edges `z a₀, z c₀, z' b₀, z' d₀` of the exchange. -/
def finalEdges (r : Fin 6 ↪ V) (f : Fin 14 ↪ V) : Finset (Sym2 V) :=
  {s(f 6, r 2), s(f 6, r 4), s(f 7, r 3), s(f 7, r 5)}

section

variable {p : V → Fin t} {F : Finset (Multiset (Fin t))}
  {G : SimpleGraph V} [DecidableRel G.Adj] {a d : ℝ} {B U : Finset (Sym2 V)}
  {Z : Finset V} {X : Finset (Sym2 V)} {r : Fin 6 ↪ V} {f : Fin 14 ↪ V}

theorem roots_eq (hf : ExchangeEmbedding p F G B U Z X r f) :
    f 0 = r 0 ∧ f 1 = r 1 ∧ f 2 = r 2 ∧ f 3 = r 3 ∧ f 4 = r 4 ∧ f 5 = r 5 :=
  ⟨hf.roots 0, hf.roots 1, hf.roots 2, hf.roots 3, hf.roots 4, hf.roots 5⟩

theorem initial_map (hf : ExchangeEmbedding p F G B U Z X r f) :
    initial.map (edgeEmb f) = sourceEdges r := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := roots_eq hf
  rw [initial_eq]
  simp [edgeEmb, sourceEdges, h0, h1, h2, h3, h4, h5]

theorem final_map (hf : ExchangeEmbedding p F G B U Z X r f) :
    final.map (edgeEmb f) = finalEdges r f := by
  obtain ⟨-, -, h2, h3, h4, h5⟩ := roots_eq hf
  simp [final, edgeEmb, finalEdges, h2, h3, h4, h5]

/-- The three exact typed modes of the selected exchange, on the skeleton
with transported labels `p ∘ f`. -/
theorem typed_moves (hf : ExchangeEmbedding p F G B U Z X r f)
    (hlab : p (r 1) = p (r 0)) :
    IsTransformer (p := p ∘ f) (F := F) H₁ Q₁ R₁ ∧
      IsTransformer (p := p ∘ f) (F := F) H₂ Q₂ R₂ ∧
      IsTransformer (p := p ∘ f) (F := F) H₃ Q₃ R₃ := by
  obtain ⟨h0, h1, -, -, -, -⟩ := roots_eq hf
  obtain ⟨c6, c7⟩ := hf.carrier_labels
  have e60 : p (f 6) = p (f 0) := by rw [c6, h0]
  have e61 : p (f 6) = p (f 1) := by rw [c6, h1, hlab]
  have e76 : p (f 7) = p (f 6) := by rw [c6, c7]
  exact ⟨(PairMoveStage85.physical_transformer first (p ∘ f) e60
      hf.links₁.1 hf.links₁.2.1 hf.links₁.2.2).1,
    (PairMoveStage85.physical_transformer second (p ∘ f) e61
      hf.links₂.1 hf.links₂.2.1 hf.links₂.2.2).1,
    (PairMoveStage85.physical_transformer third (p ∘ f) e76
      hf.links₃.1 hf.links₃.2.1 hf.links₃.2.2).1⟩

/-- **Second output, for a selected embedding.** The physical trace of three
moves from `X` (history `U`) to `(X \ Q) ∪ {z a₀, z c₀, z' b₀, z' d₀}`, inside
`E(G)`, avoiding `B` and the cumulative history; no other edge of `X` moves. -/
theorem framed_trace_of_embedding (h : ExchangeData p F G a d B U Z X r)
    (hf : ExchangeEmbedding p F G B U Z X r f) :
    PhysicalMoves p F G.edgeFinset B U X ((X \ sourceEdges r) ∪ finalEdges r f) 3 := by
  obtain ⟨t₁, t₂, t₃⟩ := typed_moves hf h.label_eq
  have h₀ := (exchange_trace t₁ t₂ t₃).restrict (U₀ := initial) (Subset.refl _)
  have h₁ := h₀.map f (q := p) (fun _ => rfl)
  have hsub : (host \ initial).map (edgeEmb f) ⊆ added.map (edgeEmb f) :=
    map_subset_map.mpr host_sdiff_initial
  have hSX := h.source_sub
  have h₂ := h₁.frame (E' := G.edgeFinset) (B' := B) (U' := U)
    (W := X \ sourceEdges r) (hsub.trans hf.real) (hf.fresh_edges.mono_left hsub)
    (sdiff_subset.trans h.config_history) (by
      rw [initial_map hf]
      exact disjoint_sdiff)
  rw [initial_map hf, final_map hf, map_empty, empty_union,
    union_eq_right.mpr (hSX.trans h.config_history), union_sdiff_of_subset hSX,
    union_comm] at h₂
  exact h₂

/-- The resulting configuration is again real and avoids `B`. -/
theorem final_config_real (h : ExchangeData p F G a d B U Z X r)
    (hf : ExchangeEmbedding p F G B U Z X r f) :
    (X \ sourceEdges r) ∪ finalEdges r f ⊆ G.edgeFinset ∧
      Disjoint ((X \ sourceEdges r) ∪ finalEdges r f) B := by
  have hfin : finalEdges r f ⊆ added.map (edgeEmb f) := by
    rw [← final_map hf]
    exact map_subset_map.mpr final_subset_added
  refine ⟨union_subset (sdiff_subset.trans h.config_real) (hfin.trans hf.real), ?_⟩
  refine disjoint_union_left.mpr ⟨h.config_forbidden.mono_left sdiff_subset, ?_⟩
  exact (hf.fresh_edges.mono_left hfin).mono_right subset_union_left

end

/-- **Headline: selected, framed, physically supported exchange.** From the
exact supplied hypotheses, there is a selected fourteen-position embedding
and an actual three-move physical trace
`PhysicalMoves p F E(G) B U X ((X \ Q) ∪ {z a₀, z c₀, z' b₀, z' d₀}) 3`,
whose final configuration is real and avoids `B`. -/
theorem exists_framed_exchange {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G : SimpleGraph V} [DecidableRel G.Adj] {a d : ℝ} {B U : Finset (Sym2 V)}
    {Z : Finset V} {X : Finset (Sym2 V)} {r : Fin 6 ↪ V}
    (h : ExchangeData p F G a d B U Z X r) :
    ∃ f : Fin 14 ↪ V, ExchangeEmbedding p F G B U Z X r f ∧
      PhysicalMoves p F G.edgeFinset B U X ((X \ sourceEdges r) ∪ finalEdges r f) 3 ∧
      (X \ sourceEdges r) ∪ finalEdges r f ⊆ G.edgeFinset ∧
      Disjoint ((X \ sourceEdges r) ∪ finalEdges r f) B := by
  obtain ⟨f, hf⟩ := exists_exchange_embedding h
  exact ⟨f, hf, framed_trace_of_embedding h hf, final_config_real h hf⟩

/-- How the exchange feeds a private producer: if the exchanged configuration
decomposes, the original configuration `X` has a two-mode absorber inside
`E(G)`, avoiding `B` and the history `U`, with at most `27` edges. -/
theorem exchange_absorber {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G : SimpleGraph V} [DecidableRel G.Adj] {a d : ℝ} {B U : Finset (Sym2 V)}
    {Z : Finset V} {X : Finset (Sym2 V)} {r : Fin 6 ↪ V}
    (h : ExchangeData p F G a d B U Z X r) {f : Fin 14 ↪ V}
    (hf : ExchangeEmbedding p F G B U Z X r f)
    (hY : HasDecomp p F ((X \ sourceEdges r) ∪ finalEdges r f)) :
    ∃ A, Absorbs (p := p) (F := F) A X ∧ Disjoint A (B ∪ U) ∧
      A.card ≤ 27 ∧ A ⊆ G.edgeFinset := by
  obtain ⟨A, hA, hd, hc, hE⟩ := (framed_trace_of_embedding h hf).exists_absorber hY
  exact ⟨A, hA, hd, by omega, hE⟩

end PartitionedTriangleAbsorption.PairExchangeTraceStage87
