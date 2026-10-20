/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.RootedTemplateEmbedding
public import Mathlib.Data.Fintype.Fin

/-! # Rooted embeddings avoiding external auxiliary congestion

Roots may belong to the excluded set. Only newly embedded nonroots avoid it.
The exclusion is fixed during one template, since injectivity prevents a vertex
from receiving two auxiliary uses in that template. This is not yet the
simultaneous edge-degree induction for a whole family of private absorbers.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CongestionRootedEmbedding

open Finset RootedEmbeddingSelection RootedTemplateEmbedding AntiEdgeSelection

variable {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ}

omit [Fintype V] [DecidableEq V] in
/-- Verification of a prefix update, independently of how the new image was selected. -/
theorem update_prefix (T : SimpleGraph (Fin m)) (G : SimpleGraph V)
    (B : Finset (Sym2 V)) (k : ℕ) (hk : k < m) (f : Fin m → V)
    (hf : PrefixEmbedding T G B k f) (w : V)
    (hneq : ∀ i, i.val < k → f i ≠ w)
    (hparent : ∀ i, i.val < k → T.Adj i ⟨k, hk⟩ →
      G.Adj (f i) w ∧ s(f i, w) ∉ B) :
    PrefixEmbedding T G B (k + 1) (Function.update f ⟨k, hk⟩ w) := by
  let j : Fin m := ⟨k, hk⟩
  let g := Function.update f j w
  have hkeep : ∀ i, i.val < k → g i = f i := by
    intro i hi
    have hij : i ≠ j := by intro h; subst i; exact (lt_irrefl k) hi
    exact Function.update_of_ne hij w f
  have hnew : g j = w := Function.update_self _ _ _
  change PrefixEmbedding T G B (k + 1) g
  refine ⟨?_, ?_⟩
  · intro i l hi hl hil
    by_cases hiold : i.val < k
    · by_cases hlold : l.val < k
      · exact hf.injective i l hiold hlold (by simpa [hkeep i hiold, hkeep l hlold] using hil)
      · have hlj : l = j := Fin.ext (by dsimp [j]; omega)
        subst l
        exact False.elim (hneq i hiold (by simpa [hkeep i hiold, hnew] using hil))
    · have hij : i = j := Fin.ext (by dsimp [j]; omega)
      subst i
      by_cases hlold : l.val < k
      · exact False.elim (hneq l hlold (by simpa [hkeep l hlold, hnew] using hil.symm))
      · exact (Fin.ext (by dsimp [j]; omega) : l = j).symm
  · intro i l hi hl hil
    by_cases hiold : i.val < k
    · by_cases hlold : l.val < k
      · simpa [hkeep i hiold, hkeep l hlold] using hf.edges i l hiold hlold hil
      · have hlj : l = j := Fin.ext (by dsimp [j]; omega)
        subst l
        simpa [hkeep i hiold, hnew] using hparent i hiold hil
    · have hij : i = j := Fin.ext (by dsimp [j]; omega)
      subst i
      have hlold : l.val < k := by
        by_contra h
        have hlj : l = j := Fin.ext (by dsimp [j]; omega)
        exact T.irrefl (hlj ▸ hil)
      obtain ⟨he, hb⟩ := hparent l hlold hil.symm
      refine ⟨?_, ?_⟩
      · simpa [hnew, hkeep l hlold] using he.symm
      · simpa [hnew, hkeep l hlold, Sym2.eq_swap] using hb

theorem extend_prefix_avoiding (T : SimpleGraph (Fin m)) [DecidableRel T.Adj]
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset (Sym2 V)) (Z : Finset V)
    (eps d : ℝ) (heps : eps ≤ 1 / 4)
    (hmin : ∀ u, (3 / 4 + eps) * (Fintype.card V : ℝ) ≤
      ((univ.filter (fun w => G.Adj u w)).card : ℝ))
    (hB : DegBounded B d) (hd : 0 ≤ d)
    (hbudget : (m : ℝ) + Z.card + 4 * d < 4 * eps * (Fintype.card V : ℝ))
    (k : ℕ) (hk : k < m) (f : Fin m → V) (hf : PrefixEmbedding T G B k f)
    (hparents : (univ.filter (fun i : Fin m => i.val < k ∧ T.Adj i ⟨k, hk⟩)).card ≤ 4) :
    ∃ g, PrefixEmbedding T G B (k + 1) g ∧
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
  obtain ⟨w, hw, hn, hb⟩ := exists_avoiding_four G S (used ∪ Z) B eps d
    heps hS hmin hB hd (by linarith)
  have hnused : w ∉ used := fun h => hn (mem_union.mpr (Or.inl h))
  have hnZ : w ∉ Z := fun h => hn (mem_union.mpr (Or.inr h))
  have hneq : ∀ i, i.val < k → f i ≠ w := by
    intro i hi he
    exact hnused (mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩, he⟩)
  have hparent : ∀ i, i.val < k → T.Adj i j → G.Adj (f i) w ∧ s(f i, w) ∉ B := by
    intro i hi hij
    have hiS : f i ∈ S := mem_image.mpr
      ⟨i, mem_filter.mpr ⟨mem_univ _, hi, hij⟩, rfl⟩
    exact ⟨hw _ hiS, hb _ hiS⟩
  refine ⟨Function.update f j w, update_prefix T G B k hk f hf w hneq hparent, ?_, ?_⟩
  · intro i hi
    have hij : i ≠ j := by intro h; subst i; exact (lt_irrefl k) hi
    exact Function.update_of_ne hij w f
  · simpa only [j, Function.update_self] using hnZ

/-- An entire template avoids `Z` on its nonroots, without imposing that on the roots. -/
theorem exists_rooted_embedding_avoiding (T : SimpleGraph (Fin m)) [DecidableRel T.Adj]
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset (Sym2 V)) (Z : Finset V)
    (eps d : ℝ) (heps : eps ≤ 1 / 4)
    (hmin : ∀ u, (3 / 4 + eps) * (Fintype.card V : ℝ) ≤
      ((univ.filter (fun w => G.Adj u w)).card : ℝ))
    (hB : DegBounded B d) (hd : 0 ≤ d)
    (hbudget : (m : ℝ) + Z.card + 4 * d < 4 * eps * (Fintype.card V : ℝ))
    (r : ℕ) (hr : r ≤ m) (rootMap : Fin m → V)
    (hroot : PrefixEmbedding T G B r rootMap)
    (horder : ∀ j : Fin m, r ≤ j.val →
      (univ.filter (fun i : Fin m => i.val < j.val ∧ T.Adj i j)).card ≤ 4) :
    ∃ f, PrefixEmbedding T G B m f ∧
      (∀ i, i.val < r → f i = rootMap i) ∧ (∀ i, r ≤ i.val → f i ∉ Z) := by
  have h : ∀ t, r + t ≤ m → ∃ f, PrefixEmbedding T G B (r + t) f ∧
      (∀ i, i.val < r → f i = rootMap i) ∧
      (∀ i, r ≤ i.val → i.val < r + t → f i ∉ Z) := by
    intro t
    induction t with
    | zero => intro _; exact ⟨rootMap, hroot, fun _ _ => rfl, by intros; omega⟩
    | succ t ih =>
      intro hbound
      obtain ⟨f, hf, hfix, havoid⟩ := ih (by omega)
      have hlt : r + t < m := by omega
      obtain ⟨g, hg, hkeep, hnew⟩ := extend_prefix_avoiding T G B Z eps d heps hmin hB hd
        hbudget (r + t) hlt f hf (horder ⟨r + t, hlt⟩ (by simp))
      refine ⟨g, by simpa only [Nat.add_succ] using hg, ?_, ?_⟩
      · intro i hi; exact (hkeep i (by omega)).trans (hfix i hi)
      · intro i hi hj
        by_cases hold : i.val < r + t
        · rw [hkeep i hold]; exact havoid i hi hold
        · have heq : i = ⟨r + t, hlt⟩ := Fin.ext (by change i.val = r + t; omega)
          simpa only [heq] using hnew
  obtain ⟨f, hf, hfix, havoid⟩ := h (m - r) (by omega)
  refine ⟨f, by simpa only [Nat.add_sub_of_le hr] using hf, hfix, ?_⟩
  intro i hi
  exact havoid i hi (by simpa only [Nat.add_sub_of_le hr] using i.isLt)

/-- Saturation is an external forbidden set, charged by the total auxiliary load. -/
theorem exists_rooted_embedding_unsaturated (T : SimpleGraph (Fin m)) [DecidableRel T.Adj]
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset (Sym2 V)) (Z : Finset V)
    (eps d : ℝ) (heps : eps ≤ 1 / 4)
    (hmin : ∀ u, (3 / 4 + eps) * (Fintype.card V : ℝ) ≤
      ((univ.filter (fun w => G.Adj u w)).card : ℝ))
    (hB : DegBounded B d) (hd : 0 ≤ d) (load : V → ℕ) (q : ℕ) (hq : 0 < q)
    (hbudget : (m : ℝ) + Z.card + ((∑ v, load v : ℕ) : ℝ) / q + 4 * d <
      4 * eps * (Fintype.card V : ℝ))
    (r : ℕ) (hr : r ≤ m) (rootMap : Fin m → V)
    (hroot : PrefixEmbedding T G B r rootMap)
    (horder : ∀ j : Fin m, r ≤ j.val →
      (univ.filter (fun i : Fin m => i.val < j.val ∧ T.Adj i j)).card ≤ 4) :
    ∃ f, PrefixEmbedding T G B m f ∧ (∀ i, i.val < r → f i = rootMap i) ∧
      (∀ i, r ≤ i.val → f i ∉ Z ∧ load (f i) < q) := by
  let saturated := univ.filter (fun v => q ≤ load v)
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hsat : (saturated.card : ℝ) ≤ ((∑ v, load v : ℕ) : ℝ) / q := by
    apply (le_div_iff₀ hqr).mpr
    exact_mod_cast (by simpa only [Nat.mul_comm] using saturated_card_budget load q)
  have hZ : ((Z ∪ saturated).card : ℝ) ≤ (Z.card : ℝ) + saturated.card := by
    exact_mod_cast card_union_le Z saturated
  obtain ⟨f, hf, hfix, havoid⟩ := exists_rooted_embedding_avoiding T G B (Z ∪ saturated)
    eps d heps hmin hB hd (by linarith) r hr rootMap hroot horder
  refine ⟨f, hf, hfix, ?_⟩
  intro i hi
  have hn := havoid i hi
  refine ⟨fun hz => hn (mem_union.mpr (Or.inl hz)), ?_⟩
  have hs : f i ∉ saturated := fun hs => hn (mem_union.mpr (Or.inr hs))
  simpa only [saturated, mem_filter, mem_univ, true_and, not_le] using hs

def auxiliaryImages (f : Fin m → V) (r : ℕ) : Finset V :=
  (univ.filter (fun i => r ≤ i.val)).image f

def addAuxiliaryUses (load : V → ℕ) (A : Finset V) (v : V) : ℕ :=
  load v + if v ∈ A then 1 else 0

omit [Fintype V] in
/-- One injective template uses each of its auxiliary images exactly once. -/
theorem auxiliaryImages_card (f : Fin m → V) (hf : Function.Injective f)
    (r : ℕ) : (auxiliaryImages f r).card = m - r := by
  rw [auxiliaryImages, card_image_of_injective _ hf]
  have hp := card_filter_add_card_filter_not (s := (univ : Finset (Fin m)))
    (fun i => i.val < r)
  rw [Fin.card_filter_val_lt] at hp
  have hn : (univ.filter (fun i : Fin m => ¬ i.val < r)) =
      univ.filter (fun i : Fin m => r ≤ i.val) := by ext i; simp
  rw [hn] at hp
  simp only [card_univ, Fintype.card_fin] at hp
  omega

omit [Fintype V] in
theorem addAuxiliaryUses_le (load : V → ℕ) (A : Finset V) (q : ℕ)
    (hload : ∀ v, load v ≤ q) (hA : ∀ v ∈ A, load v < q) :
    ∀ v, addAuxiliaryUses load A v ≤ q := by
  intro v
  by_cases hv : v ∈ A
  · simp only [addAuxiliaryUses, ite_eq_left hv]; exact Nat.succ_le_of_lt (hA v hv)
  · simpa only [addAuxiliaryUses, ite_eq_right hv, Nat.add_zero] using hload v

theorem addAuxiliaryUses_sum (load : V → ℕ) (A : Finset V) :
    ∑ v, addAuxiliaryUses load A v = (∑ v, load v) + A.card := by
  simp [addAuxiliaryUses, sum_add_distrib]

/-- The same chosen physical embedding preserves the cap and increments total use exactly.
No claim about the accumulated physical edge degrees of an entire family is made here. -/
theorem exists_congestion_safe_embedding (T : SimpleGraph (Fin m)) [DecidableRel T.Adj]
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset (Sym2 V)) (Z : Finset V)
    (eps d : ℝ) (heps : eps ≤ 1 / 4)
    (hmin : ∀ u, (3 / 4 + eps) * (Fintype.card V : ℝ) ≤
      ((univ.filter (fun w => G.Adj u w)).card : ℝ))
    (hB : DegBounded B d) (hd : 0 ≤ d) (load : V → ℕ) (q : ℕ) (hq : 0 < q)
    (hload : ∀ v, load v ≤ q)
    (hbudget : (m : ℝ) + Z.card + ((∑ v, load v : ℕ) : ℝ) / q + 4 * d <
      4 * eps * (Fintype.card V : ℝ))
    (r : ℕ) (hr : r ≤ m) (rootMap : Fin m → V)
    (hroot : PrefixEmbedding T G B r rootMap)
    (horder : ∀ j : Fin m, r ≤ j.val →
      (univ.filter (fun i : Fin m => i.val < j.val ∧ T.Adj i j)).card ≤ 4) :
    ∃ f, PrefixEmbedding T G B m f ∧ (∀ i, i.val < r → f i = rootMap i) ∧
      (∀ i, r ≤ i.val → f i ∉ Z ∧ load (f i) < q) ∧
      (∀ v, addAuxiliaryUses load (auxiliaryImages f r) v ≤ q) ∧
      (∑ v, addAuxiliaryUses load (auxiliaryImages f r) v) =
        (∑ v, load v) + (m - r) := by
  obtain ⟨f, hf, hfix, havoid⟩ := exists_rooted_embedding_unsaturated T G B Z eps d
    heps hmin hB hd load q hq hbudget r hr rootMap hroot horder
  have hfi : Function.Injective f := fun i j h => hf.injective i j i.isLt j.isLt h
  refine ⟨f, hf, hfix, havoid, addAuxiliaryUses_le load _ q hload ?_, ?_⟩
  · intro v hv
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hv
    exact (havoid i (mem_filter.mp hi).2).2
  · rw [addAuxiliaryUses_sum, auxiliaryImages_card f hfi]

end PartitionedTriangleAbsorption.CongestionRootedEmbedding
