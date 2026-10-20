/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PairMoveSelectionStage85

/-! # Rooted prefix embedding from compatible four-root supply

This adapts the induction of `TypedRootedEmbedding.exists_embedding` to the
compatible supply of Stage85. Each new vertex is selected by
`PairMoveSelectionStage85.exists_fresh`, so its query set only consists of the
images of its already embedded parents, and the only geometric premise is that
the prescribed label of the new vertex is link-compatible with the prescribed
label of every parent. The prefix update reuses
`CongestionRootedEmbedding.update_prefix`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CompatibleRootedEmbeddingStage87

open Finset AntiEdgeSelection RootedTemplateEmbedding CongestionRootedEmbedding
  TypedTransformer PairMoveSelectionStage85

variable {V : Type*} [Fintype V] [DecidableEq V] {m t : ℕ}

/-- One greedy step: the new vertex has the prescribed label, is adjacent to
the images of its parents through edges outside `B`, avoids every earlier
image, and avoids the external exclusion set `Z`. -/
theorem extend_prefix (T : SimpleGraph (Fin m)) [DecidableRel T.Adj]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (label : Fin m → Fin t) (a d : ℝ)
    (hs : CompatibleSupply p F G a) (B : Finset (Sym2 V)) (Z : Finset V)
    (hB : DegBounded B d) (hd : 0 ≤ d)
    (hbudget : (m : ℝ) + Z.card + 4 * d < a)
    (k : ℕ) (hk : k < m) (f : Fin m → V) (hf : PrefixEmbedding T G B k f)
    (hp : ∀ i, i.val < k → p (f i) = label i)
    (hparents : (univ.filter (fun i : Fin m => i.val < k ∧ T.Adj i ⟨k, hk⟩)).card ≤ 4)
    (hcompat : ∀ i : Fin m, i.val < k → T.Adj i ⟨k, hk⟩ →
      ∃ c, Link F (label ⟨k, hk⟩) (label i) c) :
    ∃ g, PrefixEmbedding T G B (k + 1) g ∧
      (∀ i, i.val < k + 1 → p (g i) = label i) ∧
      (∀ i, i.val < k → g i = f i) ∧ g ⟨k, hk⟩ ∉ Z := by
  let j : Fin m := ⟨k, hk⟩
  let parents := univ.filter (fun i : Fin m => i.val < k ∧ T.Adj i j)
  let S := parents.image f
  let used := (univ.filter (fun i : Fin m => i.val < k)).image f
  have hS : S.card ≤ 4 := card_image_le.trans hparents
  have hu : used.card ≤ m := card_image_le.trans (by
    simpa using (card_filter_le (univ : Finset (Fin m)) (fun i => i.val < k)))
  have huz : ((used ∪ Z).card : ℝ) ≤ (m : ℝ) + Z.card := by
    exact_mod_cast (card_union_le used Z).trans (Nat.add_le_add_right hu _)
  have hc : Compatible p F S (label j) := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hv
    obtain ⟨-, hik, hij⟩ := mem_filter.mp hi
    rw [hp i hik]
    exact hcompat i hik hij
  obtain ⟨w, hpw, hw, hn, hb⟩ :=
    exists_fresh p F G a d hs S (used ∪ Z) (label j) hS hc B hB hd (by linarith)
  have hneq : ∀ i, i.val < k → f i ≠ w := by
    intro i hi he
    exact hn (mem_union.mpr (Or.inl
      (mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩, he⟩)))
  have hparent : ∀ i, i.val < k → T.Adj i j → G.Adj (f i) w ∧ s(f i, w) ∉ B := by
    intro i hi hij
    have hmem : f i ∈ S := mem_image.mpr
      ⟨i, mem_filter.mpr ⟨mem_univ _, hi, hij⟩, rfl⟩
    exact ⟨hw _ hmem, hb _ hmem⟩
  let g := Function.update f j w
  have hkeep : ∀ i, i.val < k → g i = f i := by
    intro i hi
    exact Function.update_of_ne
      (show i ≠ j by intro h; subst i; exact (lt_irrefl k) hi) w f
  have hnew : g j = w := Function.update_self _ _ _
  refine ⟨g, update_prefix T G B k hk f hf w hneq hparent, ?_, hkeep, ?_⟩
  · intro i hi
    by_cases hold : i.val < k
    · rw [hkeep i hold]; exact hp i hold
    · have hij : i = j := Fin.ext (by dsimp [j]; omega)
      simpa only [hij, hnew] using hpw
  · rw [hnew]
    exact fun hz => hn (mem_union.mpr (Or.inr hz))

/-- Full rooted embedding: roots are fixed, nonroots receive their prescribed
labels, avoid `Z`, and every template edge is a real edge of `G` outside `B`.
The parent compatibilities are explicit hypotheses about the label map only. -/
theorem exists_embedding (T : SimpleGraph (Fin m)) [DecidableRel T.Adj]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (label : Fin m → Fin t) (a d : ℝ)
    (hs : CompatibleSupply p F G a) (B : Finset (Sym2 V)) (Z : Finset V)
    (hB : DegBounded B d) (hd : 0 ≤ d)
    (hbudget : (m : ℝ) + Z.card + 4 * d < a)
    (r : ℕ) (hr : r ≤ m) (rootMap : Fin m → V)
    (hroot : PrefixEmbedding T G B r rootMap)
    (hlabel : ∀ i, i.val < r → p (rootMap i) = label i)
    (horder : ∀ j : Fin m, r ≤ j.val →
      (univ.filter (fun i : Fin m => i.val < j.val ∧ T.Adj i j)).card ≤ 4)
    (hcompat : ∀ j : Fin m, r ≤ j.val → ∀ i : Fin m, i.val < j.val → T.Adj i j →
      ∃ c, Link F (label j) (label i) c) :
    ∃ f, PrefixEmbedding T G B m f ∧ (∀ i, p (f i) = label i) ∧
      (∀ i, i.val < r → f i = rootMap i) ∧ (∀ i, r ≤ i.val → f i ∉ Z) := by
  have h : ∀ l, r + l ≤ m → ∃ f, PrefixEmbedding T G B (r + l) f ∧
      (∀ i, i.val < r + l → p (f i) = label i) ∧
      (∀ i, i.val < r → f i = rootMap i) ∧
      (∀ i, r ≤ i.val → i.val < r + l → f i ∉ Z) := by
    intro l
    induction l with
    | zero => intro _; exact ⟨rootMap, hroot, hlabel, fun _ _ => rfl, by intros; omega⟩
    | succ l ih =>
      intro hbound
      obtain ⟨f, hf, hp, hfix, havoid⟩ := ih (by omega)
      have hlt : r + l < m := by omega
      obtain ⟨g, hg, hgp, hkeep, hnew⟩ := extend_prefix T G p F label a d hs B Z hB hd
        hbudget (r + l) hlt f hf hp (horder ⟨r + l, hlt⟩ (by simp))
        (fun i hi hij => hcompat ⟨r + l, hlt⟩ (by simp) i hi hij)
      refine ⟨g, by simpa only [Nat.add_succ] using hg,
        by simpa only [Nat.add_succ] using hgp, ?_, ?_⟩
      · intro i hi; exact (hkeep i (by omega)).trans (hfix i hi)
      · intro i hi hj
        by_cases hold : i.val < r + l
        · rw [hkeep i hold]; exact havoid i hi hold
        · have heq : i = ⟨r + l, hlt⟩ := Fin.ext (by change i.val = r + l; omega)
          simpa only [heq] using hnew
  obtain ⟨f, hf, hp, hfix, havoid⟩ := h (m - r) (by omega)
  refine ⟨f, by simpa only [Nat.add_sub_of_le hr] using hf, ?_, hfix, ?_⟩
  · intro i
    exact hp i (by simpa only [Nat.add_sub_of_le hr] using i.isLt)
  · intro i hi
    exact havoid i hi (by simpa only [Nat.add_sub_of_le hr] using i.isLt)

end PartitionedTriangleAbsorption.CompatibleRootedEmbeddingStage87
