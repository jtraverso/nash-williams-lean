/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CompatibleRootedEmbeddingStage87
public import PartitionedTriangleAbsorption.PairExchangeTemplateStage87
public import PartitionedTriangleAbsorption.PhysicalMovesFrameStage87

/-! # Producer of the compatible physical pair exchange

From the exact supplied hypotheses (`ExchangeData`) we select a real
fourteen-position embedding of the Stage86 exchange skeleton: labels are chosen
by the pair-move condition `ThreeStepLinks` before embedding, every nonroot is
selected from the compatible four-root supply, and all 27 new edges are real
edges outside `B ∪ U`. Then the three typed modes are obtained from
`PairMoveStage85.physical_transformer`, the finite trace from
`PairExchangeStage86.exchange_trace`, and the trace is transported and framed
inside the ambient configuration `X`.

The roots are `x₁ x₂ a₀ b₀ c₀ d₀ = r 0, …, r 5`; positions `6, 7` are the new
carriers `z, z'`; positions `8–13` are the gadget auxiliaries.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PairExchangeProducerStage87

open Finset AntiEdgeSelection RootedTemplateEmbedding TypedTransformer
  PairMoveSelectionStage85 PhysicalHingeSupply PhysicalMovesStage86
  PairExchangeStage86 PairExchangeTemplateStage87

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

/-- The four initial source edges `x₁a₀, x₁b₀, x₂c₀, x₂d₀`. -/
def sourceEdges (r : Fin 6 ↪ V) : Finset (Sym2 V) :=
  {s(r 0, r 2), s(r 0, r 3), s(r 1, r 4), s(r 1, r 5)}

/-- The exact supplied hypotheses of the exchange producer.
`roots_mem` and `source_real` are implied by `support`, `source_sub` and
`config_real`; they are kept because they are part of the stated input. -/
structure ExchangeData (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (a d : ℝ)
    (B U : Finset (Sym2 V)) (Z : Finset V) (X : Finset (Sym2 V))
    (r : Fin 6 ↪ V) : Prop where
  /-- The pair-move condition M. -/
  threeStep : ThreeStepLinks F
  /-- Compatible four-root supply. -/
  supply : CompatibleSupply p F G a
  d_nonneg : 0 ≤ d
  forbidden : DegBounded B d
  /-- `14 + |Z| + 4 (d + |U|) < a`. -/
  budget : 14 + (Z.card : ℝ) + 4 * (d + U.card) < a
  roots_mem : ∀ i, r i ∈ Z
  label_eq : p (r 1) = p (r 0)
  source_real : sourceEdges r ⊆ G.edgeFinset
  /-- The four initial label types are active. -/
  active : (∃ k, Link F (p (r 0)) (p (r 2)) k) ∧ (∃ k, Link F (p (r 0)) (p (r 3)) k) ∧
    (∃ k, Link F (p (r 1)) (p (r 4)) k) ∧ (∃ k, Link F (p (r 1)) (p (r 5)) k)
  source_sub : sourceEdges r ⊆ X
  config_history : X ⊆ U
  config_real : X ⊆ G.edgeFinset
  config_forbidden : Disjoint X B
  /-- `Z` contains every vertex incident with the configuration. -/
  support : ∀ e ∈ X, ∀ v ∈ e, v ∈ Z

/-- The selected physical embedding of the fourteen-position exchange. -/
structure ExchangeEmbedding (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (B U : Finset (Sym2 V)) (Z : Finset V)
    (X : Finset (Sym2 V)) (r : Fin 6 ↪ V) (f : Fin 14 ↪ V) : Prop where
  roots : ∀ i : Fin 6, f ⟨i.val, by omega⟩ = r i
  carrier_labels : p (f 6) = p (r 0) ∧ p (f 7) = p (r 0)
  fresh_vertices : ∀ i : Fin 14, 6 ≤ i.val → f i ∉ Z
  avoids_support : ∀ i : Fin 14, 6 ≤ i.val → ∀ e ∈ X, f i ∉ e
  real : added.map (edgeEmb f) ⊆ G.edgeFinset
  fresh_edges : Disjoint (added.map (edgeEmb f)) (B ∪ U)
  /-- Move `(0,6,2,3,8,9)`. -/
  links₁ : Link F (p (f 0)) (p (f 2)) (p (f 8)) ∧ Link F (p (f 0)) (p (f 3)) (p (f 9)) ∧
    Link F (p (f 0)) (p (f 8)) (p (f 9))
  /-- Move `(1,6,4,5,10,11)`. -/
  links₂ : Link F (p (f 1)) (p (f 4)) (p (f 10)) ∧ Link F (p (f 1)) (p (f 5)) (p (f 11)) ∧
    Link F (p (f 1)) (p (f 10)) (p (f 11))
  /-- Move `(6,7,3,5,12,13)`. -/
  links₃ : Link F (p (f 6)) (p (f 3)) (p (f 12)) ∧ Link F (p (f 6)) (p (f 5)) (p (f 13)) ∧
    Link F (p (f 6)) (p (f 12)) (p (f 13))

/-- Labels of the fourteen positions, chosen before embedding. -/
def exLabel (x a b c d k₀ k₁ k₂ k₃ k₄ k₅ : Fin t) : Fin 14 → Fin t :=
  ![x, x, a, b, c, d, x, x, k₀, k₁, k₂, k₃, k₄, k₅]

theorem link_exists_all {F : Finset (Multiset (Fin t))} {a b c : Fin t}
    (h : Link F a b c) :
    (∃ x, Link F a b x) ∧ (∃ x, Link F b a x) ∧ (∃ x, Link F a c x) ∧
      (∃ x, Link F c a x) ∧ (∃ x, Link F b c x) ∧ (∃ x, Link F c b x) := by
  have h1 : Link F a c b := (link_swap F a b c).mp h
  have h2 : Link F b a c := (link_root_swap F a b c).mp h
  have h3 : Link F c a b := rotate_link h
  have h4 : Link F b c a := (link_swap F b a c).mp h2
  have h5 : Link F c b a := (link_swap F c a b).mp h3
  exact ⟨⟨_, h⟩, ⟨_, h2⟩, ⟨_, h1⟩, ⟨_, h3⟩, ⟨_, h4⟩, ⟨_, h5⟩⟩

/-- Every parent label of every nonroot is link-compatible with the label of
that nonroot; this is where the selected links are used. -/
theorem exLabel_compatible {F : Finset (Multiset (Fin t))}
    {x a b c d k₀ k₁ k₂ k₃ k₄ k₅ : Fin t}
    (l₀ : Link F x a k₀) (l₁ : Link F x b k₁) (l₂ : Link F x k₀ k₁)
    (l₃ : Link F x c k₂) (l₄ : Link F x d k₃) (l₅ : Link F x k₂ k₃)
    (l₆ : Link F x b k₄) (l₇ : Link F x d k₅) (l₈ : Link F x k₄ k₅) :
    ∀ j : Fin 14, 6 ≤ j.val → ∀ i : Fin 14, i.val < j.val → tmpl.Adj i j →
      ∃ k, Link F (exLabel x a b c d k₀ k₁ k₂ k₃ k₄ k₅ j)
        (exLabel x a b c d k₀ k₁ k₂ k₃ k₄ k₅ i) k := by
  intro j _ i hij hadj
  have hp := parent_pairs i j hij hadj
  obtain ⟨_, _, _, _, _, _⟩ := link_exists_all l₀
  obtain ⟨_, _, _, _, _, _⟩ := link_exists_all l₁
  obtain ⟨_, _, _, _, _, _⟩ := link_exists_all l₂
  obtain ⟨_, _, _, _, _, _⟩ := link_exists_all l₃
  obtain ⟨_, _, _, _, _, _⟩ := link_exists_all l₄
  obtain ⟨_, _, _, _, _, _⟩ := link_exists_all l₅
  obtain ⟨_, _, _, _, _, _⟩ := link_exists_all l₆
  obtain ⟨_, _, _, _, _, _⟩ := link_exists_all l₇
  obtain ⟨_, _, _, _, _, _⟩ := link_exists_all l₈
  simp only [mem_insert, mem_singleton, Prod.mk.injEq] at hp
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals assumption


/-- **First output: the producer.** From the supplied hypotheses only, select
an injective fourteen-position embedding fixing the six roots, whose two
carriers have label `p x₁`, whose eight new vertices avoid `Z` (hence every
vertex of the configuration `X`), whose 27 new edges are real edges of `G`
outside `B ∪ U`, and whose labels satisfy the nine move links. -/
theorem exists_exchange_embedding {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G : SimpleGraph V} [DecidableRel G.Adj] {a d : ℝ} {B U : Finset (Sym2 V)}
    {Z : Finset V} {X : Finset (Sym2 V)} {r : Fin 6 ↪ V}
    (h : ExchangeData p F G a d B U Z X r) :
    ∃ f : Fin 14 ↪ V, ExchangeEmbedding p F G B U Z X r f := by
  obtain ⟨h02, h03, h14, h15⟩ := h.active
  rw [h.label_eq] at h14 h15
  obtain ⟨k₀, k₁, l₀, l₁, l₂⟩ := PairMoveStage85.move_types h.threeStep _ _ _ h02 h03
  obtain ⟨k₂, k₃, l₃, l₄, l₅⟩ := PairMoveStage85.move_types h.threeStep _ _ _ h14 h15
  obtain ⟨k₄, k₅, l₆, l₇, l₈⟩ := PairMoveStage85.move_types h.threeStep _ _ _ h03 h15
  let label := exLabel (p (r 0)) (p (r 2)) (p (r 3)) (p (r 4)) (p (r 5))
    k₀ k₁ k₂ k₃ k₄ k₅
  let rootMap : Fin 14 → V := fun i => if hi : i.val < 6 then r ⟨i.val, hi⟩ else r 0
  have hrootMap : ∀ i : Fin 6, rootMap ⟨i.val, by omega⟩ = r i := by
    intro i
    simp [rootMap]
  have hroot : PrefixEmbedding tmpl G (B ∪ U) 6 rootMap := by
    refine ⟨?_, ?_⟩
    · intro i j hi hj hij
      have hv : i.val = j.val := by simpa [rootMap, hi, hj] using hij
      exact Fin.ext hv
    · intro i j hi hj hadj
      exact absurd hadj (roots_independent i j hi hj)
  have hlabel : ∀ i : Fin 14, i.val < 6 → p (rootMap i) = label i := by
    intro i hi
    have hl := h.label_eq
    fin_cases i <;> simp_all [rootMap, label, exLabel]
  have hbud : ((14 : ℕ) : ℝ) + Z.card + 4 * (d + U.card) < a := by
    have := h.budget
    push_cast
    linarith
  obtain ⟨f, hf, hp, hfix, havoid⟩ :=
    CompatibleRootedEmbeddingStage87.exists_embedding tmpl G p F label a (d + U.card)
      h.supply (B ∪ U) Z (blocked_union_degree B U d h.forbidden)
      (by have := h.d_nonneg; positivity) hbud 6 (by norm_num) rootMap hroot hlabel
      order_budget (exLabel_compatible l₀ l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈)
  let fE : Fin 14 ↪ V := ⟨f, fun i j hij => hf.injective i j i.isLt j.isLt hij⟩
  have hedge : ∀ e ∈ added.map (edgeEmb fE), e ∈ G.edgeFinset ∧ e ∉ B ∪ U := by
    intro e he
    obtain ⟨e₀, he₀, rfl⟩ := mem_map.mp he
    induction e₀ using Sym2.ind with
    | h i j =>
      have hadj := (mem_added_iff i j).mp he₀
      obtain ⟨hG, hB⟩ := hf.edges i j i.isLt j.isLt hadj
      change s(f i, f j) ∈ G.edgeFinset ∧ s(f i, f j) ∉ B ∪ U
      exact ⟨SimpleGraph.mem_edgeFinset.mpr hG, hB⟩
  refine ⟨fE, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i
    change f _ = r i
    rw [hfix _ (by simp), hrootMap]
  · change p (f 6) = p (r 0) ∧ p (f 7) = p (r 0)
    rw [hp, hp]
    exact ⟨rfl, rfl⟩
  · exact havoid
  · intro i hi e he hv
    exact havoid i hi (h.support e he _ hv)
  · exact fun e he => (hedge e he).1
  · rw [disjoint_left]
    exact fun e he => (hedge e he).2
  · change Link F (p (f 0)) (p (f 2)) (p (f 8)) ∧ Link F (p (f 0)) (p (f 3)) (p (f 9)) ∧
      Link F (p (f 0)) (p (f 8)) (p (f 9))
    simp only [hp]
    exact ⟨l₀, l₁, l₂⟩
  · change Link F (p (f 1)) (p (f 4)) (p (f 10)) ∧ Link F (p (f 1)) (p (f 5)) (p (f 11)) ∧
      Link F (p (f 1)) (p (f 10)) (p (f 11))
    simp only [hp]
    exact ⟨l₃, l₄, l₅⟩
  · change Link F (p (f 6)) (p (f 3)) (p (f 12)) ∧ Link F (p (f 6)) (p (f 5)) (p (f 13)) ∧
      Link F (p (f 6)) (p (f 12)) (p (f 13))
    simp only [hp]
    exact ⟨l₆, l₇, l₈⟩

end PartitionedTriangleAbsorption.PairExchangeProducerStage87
