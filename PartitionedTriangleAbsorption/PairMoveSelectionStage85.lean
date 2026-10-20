/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedEmbeddingSelection
public import PartitionedTriangleAbsorption.PairMoveStage85

/-! # Selection from compatible four-root supply

Unlike the older `Supply`, this hypothesis only queries compatible labels.
All forbidden vertices, including every active vertex, are explicitly excluded.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PairMoveSelectionStage85

open Finset RootedEmbeddingSelection AntiEdgeSelection TypedEmbeddingSelection
open TypedTransformer

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

def Compatible (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (S : Finset V) (i : Fin t) : Prop :=
  ∀ v ∈ S, ∃ k, Link F i (p v) k

/-- The proposed hypothesis R, with its count expressed as a single real `a`. -/
def CompatibleSupply (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (a : ℝ) : Prop :=
  ∀ S : Finset V, S.card ≤ 4 → ∀ i, Compatible p F S i →
    a ≤ ((typedNeighbours p G S i).card : ℝ)

/-- Select the real auxiliary from the stated compatible supply, not from an
uninterpreted oracle. Choosing Z to contain the configuration support fixes
the future-edge collision in the originally supplied exchange proof. -/
theorem exists_fresh (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (a d : ℝ)
    (hs : CompatibleSupply p F G a) (S Z : Finset V) (i : Fin t)
    (hS : S.card ≤ 4) (hi : Compatible p F S i)
    (B : Finset (Sym2 V)) (hB : DegBounded B d) (hd : 0 ≤ d)
    (hb : (Z.card : ℝ) + 4 * d < a) :
    ∃ w, p w = i ∧ (∀ u ∈ S, G.Adj u w) ∧ w ∉ Z ∧
      ∀ u ∈ S, s(u, w) ∉ B := by
  let W := typedNeighbours p G S i
  have hsum : (∑ u ∈ S, (incidentLoad B u : ℝ)) ≤ 4 * d := by
    calc
      _ ≤ (S.card : ℝ) * d := by
        simpa only [incidentLoad, sum_const, nsmul_eq_mul] using
          (sum_le_sum (s := S) fun u _ => hB u)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hS) hd
  have hcount := available_card_budget W Z S B
  have hpos : 0 < (W \ (Z ∪ blockedMany B S)).card := by
    by_contra h
    have hz : (W \ (Z ∪ blockedMany B S)).card = 0 := by omega
    rw [hz, Nat.zero_add] at hcount
    have hr : (W.card : ℝ) ≤ Z.card + ∑ u ∈ S, (incidentLoad B u : ℝ) := by
      exact_mod_cast hcount
    have hsupply := hs S hS i hi
    change a ≤ (W.card : ℝ) at hsupply
    linarith
  obtain ⟨w, hw⟩ := card_pos.mp hpos
  obtain ⟨hw, hbad⟩ := mem_sdiff.mp hw
  have htyped := (mem_filter.mp hw).2
  refine ⟨w, htyped.1, htyped.2, ?_, ?_⟩
  · intro hz
    exact hbad (mem_union.mpr (Or.inl hz))
  · intro u hu he
    exact hbad (mem_union.mpr (Or.inr (mem_biUnion.mpr
      ⟨u, hu, mem_filter.mpr ⟨mem_univ _, he⟩⟩)))

omit [Fintype V] in
/-- Combine forbidden and previously used edges without assuming sparsity of U. -/
theorem blocked_union_degree (B U : Finset (Sym2 V)) (d : ℝ)
    (hB : DegBounded B d) : DegBounded (B ∪ U) (d + U.card) := by
  intro v
  have hc : ((B ∪ U).filter (fun e => v ∈ e)).card ≤
      (B.filter (fun e => v ∈ e)).card + U.card := by
    rw [filter_union]
    exact (card_union_le _ _).trans
      (Nat.add_le_add_left (card_le_card (filter_subset _ _)) _)
  have hcr : (((B ∪ U).filter (fun e => v ∈ e)).card : ℝ) ≤
      ((B.filter (fun e => v ∈ e)).card : ℝ) + U.card := by exact_mod_cast hc
  linarith [hB v]

/-- Union-bound selection in exactly the resource regime of the supplied proof. -/
theorem exists_fresh_with_history (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (a d : ℝ)
    (hs : CompatibleSupply p F G a) (S Z : Finset V) (i : Fin t)
    (hS : S.card ≤ 4) (hi : Compatible p F S i)
    (B U : Finset (Sym2 V)) (hB : DegBounded B d) (hd : 0 ≤ d)
    (hb : (Z.card : ℝ) + 4 * d + 4 * U.card < a) :
    ∃ w, p w = i ∧ (∀ u ∈ S, G.Adj u w) ∧ w ∉ Z ∧
      ∀ u ∈ S, s(u, w) ∉ B ∪ U := by
  apply exists_fresh p F G a (d + U.card) hs S Z i hS hi (B ∪ U)
    (blocked_union_degree B U d hB) (by positivity)
  linarith

theorem rotate_link {i j k : Fin t} {F : Finset (Multiset (Fin t))}
    (h : Link F i j k) : Link F k i j :=
  (link_root_swap F i k j).mp ((link_swap F i j k).mp h)

/-- Construct the two real auxiliaries for a prescribed destination x'.
The four old vertices are in Z, and both auxiliaries stay outside Z.
The only geometric input is compatible four-root supply and the strict budget.
Every one of the seven gadget edges is present and avoids B and the full history U. -/
theorem exists_move_auxiliaries (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (a d : ℝ)
    (hs : CompatibleSupply p F G a) (r : Fin 4 ↪ V) (Z : Finset V)
    (hZ : ∀ i, r i ∈ Z) (hlabel : p (r 1) = p (r 0))
    (k₁ k₂ : Fin t) (h₁ : Link F (p (r 0)) (p (r 2)) k₁)
    (h₂ : Link F (p (r 0)) (p (r 3)) k₂)
    (h₃ : Link F (p (r 0)) k₁ k₂)
    (B U : Finset (Sym2 V)) (hB : DegBounded B d) (hd : 0 ≤ d)
    (hb : (Z.card : ℝ) + 4 * d + 4 * U.card < a) :
    ∃ w₁ w₂,
      PhysicalHingeSupply.SixDistinct (r 0) (r 1) (r 2) (r 3) w₁ w₂ ∧
      p w₁ = k₁ ∧ p w₂ = k₂ ∧ w₁ ∉ Z ∧ w₂ ∉ Z ∧
      ∀ e ∈ ({s(r 0, w₁), s(r 1, w₁), s(r 2, w₁),
        s(r 0, w₂), s(r 1, w₂), s(r 3, w₂), s(w₁, w₂)} : Finset (Sym2 V)),
        e ∈ G.edgeFinset ∧ e ∉ B ∪ U := by
  let S₁ : Finset V := {r 0, r 1, r 2}
  have hS₁ : S₁.card ≤ 4 := by
    have h := card_insert_le (r 0) ({r 1, r 2} : Finset V)
    have h' := card_insert_le (r 1) ({r 2} : Finset V)
    simp only [card_singleton] at h'
    dsimp [S₁]
    omega
  have hc₁ : Compatible p F S₁ k₁ := by
    intro v hv
    simp only [S₁, mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact ⟨p (r 2), rotate_link h₁⟩
    · rw [hlabel]
      exact ⟨p (r 2), rotate_link h₁⟩
    · exact ⟨p (r 0), (link_swap F k₁ (p (r 0)) (p (r 2))).mp (rotate_link h₁)⟩
  obtain ⟨w₁, hp₁, hn₁, hz₁, he₁⟩ :=
    exists_fresh_with_history p F G a d hs S₁ Z k₁ hS₁ hc₁ B U hB hd hb
  let S₂ : Finset V := {r 0, r 1, r 3, w₁}
  have hS₂ : S₂.card ≤ 4 := by
    have h := card_insert_le (r 0) ({r 1, r 3, w₁} : Finset V)
    have h' := card_insert_le (r 1) ({r 3, w₁} : Finset V)
    have h'' := card_insert_le (r 3) ({w₁} : Finset V)
    simp only [card_singleton] at h''
    dsimp [S₂]
    omega
  have hc₂ : Compatible p F S₂ k₂ := by
    intro v hv
    simp only [S₂, mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact ⟨p (r 3), rotate_link h₂⟩
    · rw [hlabel]
      exact ⟨p (r 3), rotate_link h₂⟩
    · exact ⟨p (r 0), (link_swap F k₂ (p (r 0)) (p (r 3))).mp (rotate_link h₂)⟩
    · rw [hp₁]
      exact ⟨p (r 0), (link_swap F k₂ (p (r 0)) k₁).mp (rotate_link h₃)⟩
  obtain ⟨w₂, hp₂, hn₂, hz₂, he₂⟩ :=
    exists_fresh_with_history p F G a d hs S₂ Z k₂ hS₂ hc₂ B U hB hd hb
  have hneq₁ : ∀ i : Fin 4, r i ≠ w₁ := by
    intro i h
    exact hz₁ (h ▸ hZ i)
  have hneq₂ : ∀ i : Fin 4, r i ≠ w₂ := by
    intro i h
    exact hz₂ (h ▸ hZ i)
  have h12 : w₁ ≠ w₂ := (hn₂ w₁ (by simp [S₂])).ne
  have hdist : PhysicalHingeSupply.SixDistinct (r 0) (r 1) (r 2) (r 3) w₁ w₂ :=
    ⟨r.injective.ne (by decide), r.injective.ne (by decide),
      r.injective.ne (by decide), hneq₁ 0, hneq₂ 0,
      r.injective.ne (by decide), r.injective.ne (by decide), hneq₁ 1, hneq₂ 1,
      r.injective.ne (by decide), hneq₁ 2, hneq₂ 2, hneq₁ 3, hneq₂ 3, h12⟩
  have hphys₁ : ∀ u ∈ S₁, s(u, w₁) ∈ G.edgeFinset ∧ s(u, w₁) ∉ B ∪ U := by
    intro u hu
    exact ⟨by simpa using hn₁ u hu, he₁ u hu⟩
  have hphys₂ : ∀ u ∈ S₂, s(u, w₂) ∈ G.edgeFinset ∧ s(u, w₂) ∉ B ∪ U := by
    intro u hu
    exact ⟨by simpa using hn₂ u hu, he₂ u hu⟩
  refine ⟨w₁, w₂, hdist, hp₁, hp₂, hz₁, hz₂, ?_⟩
  intro e he
  simp only [mem_insert, mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hphys₁ _ (by simp [S₁])
  · exact hphys₁ _ (by simp [S₁])
  · exact hphys₁ _ (by simp [S₁])
  · exact hphys₂ _ (by simp [S₂])
  · exact hphys₂ _ (by simp [S₂])
  · exact hphys₂ _ (by simp [S₂])
  · exact hphys₂ _ (by simp [S₂])

/-- Join label selection, real auxiliary selection, and the two positive modes.
The source and destination root edges are prescribed by r; their presence and
destination freshness must be checked by the calling move-sequence producer. -/
theorem exists_physical_gadget (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (hF : ThreeStepLinks F) (G : SimpleGraph V) [DecidableRel G.Adj] (a d : ℝ)
    (hs : CompatibleSupply p F G a) (r : Fin 4 ↪ V) (Z : Finset V)
    (hZ : ∀ i, r i ∈ Z) (hlabel : p (r 1) = p (r 0))
    (h₁ : ∃ k, Link F (p (r 0)) (p (r 2)) k)
    (h₂ : ∃ k, Link F (p (r 0)) (p (r 3)) k)
    (B U : Finset (Sym2 V)) (hB : DegBounded B d) (hd : 0 ≤ d)
    (hb : (Z.card : ℝ) + 4 * d + 4 * U.card < a) :
    ∃ f : Fin 6 ↪ V,
      (∀ i : Fin 4, f ⟨i.val, by omega⟩ = r i) ∧ f 4 ∉ Z ∧ f 5 ∉ Z ∧
      IsTransformer (p := p) (F := F)
        (PairMoveStage85.gadget.map (PhysicalHingeSupply.edgeEmb f))
        (PairMoveStage85.source.map (PhysicalHingeSupply.edgeEmb f))
        (PairMoveStage85.target.map (PhysicalHingeSupply.edgeEmb f)) ∧
      (PairMoveStage85.gadget.map (PhysicalHingeSupply.edgeEmb f)).card = 7 ∧
      (PairMoveStage85.gadget.map (PhysicalHingeSupply.edgeEmb f)) ⊆ G.edgeFinset ∧
      Disjoint (PairMoveStage85.gadget.map (PhysicalHingeSupply.edgeEmb f)) (B ∪ U) := by
  obtain ⟨k₁, k₂, ht₁, ht₂, ht₃⟩ :=
    PairMoveStage85.move_types hF (p (r 0)) (p (r 2)) (p (r 3)) h₁ h₂
  obtain ⟨w₁, w₂, hd6, hp₁, hp₂, hz₁, hz₂, he⟩ :=
    exists_move_auxiliaries p F G a d hs r Z hZ hlabel k₁ k₂ ht₁ ht₂ ht₃
      B U hB hd hb
  let f : Fin 6 ↪ V := PhysicalHingeSupply.sixEmb hd6
  have hfix : ∀ i : Fin 4, f ⟨i.val, by omega⟩ = r i := by
    intro i
    fin_cases i <;> rfl
  have htrans := PairMoveStage85.physical_transformer f p
    (by simpa [f, PhysicalHingeSupply.sixEmb, PhysicalHingeSupply.sixMap] using hlabel)
    (by simpa [f, PhysicalHingeSupply.sixEmb, PhysicalHingeSupply.sixMap, hp₁] using ht₁)
    (by simpa [f, PhysicalHingeSupply.sixEmb, PhysicalHingeSupply.sixMap, hp₂] using ht₂)
    (by simpa [f, PhysicalHingeSupply.sixEmb, PhysicalHingeSupply.sixMap, hp₁, hp₂] using ht₃)
  have hmap : PairMoveStage85.gadget.map (PhysicalHingeSupply.edgeEmb f) =
      ({s(r 0, w₁), s(r 1, w₁), s(r 2, w₁), s(r 0, w₂), s(r 1, w₂),
        s(r 3, w₂), s(w₁, w₂)} : Finset (Sym2 V)) := by
    simp [PairMoveStage85.gadget, PhysicalHingeSupply.edgeEmb, f,
      PhysicalHingeSupply.sixEmb, PhysicalHingeSupply.sixMap]
  refine ⟨f, hfix, hz₁, hz₂, htrans.1, htrans.2, ?_, ?_⟩
  · rw [hmap]
    exact fun e he' => (he e he').1
  · rw [hmap, disjoint_left]
    exact fun e he' hb' => (he e he').2 hb'

end PartitionedTriangleAbsorption.PairMoveSelectionStage85
