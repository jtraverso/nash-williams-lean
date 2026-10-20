/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.RootedEmbeddingSelection

/-! # Extending a supplied rooted 4-degenerate template

This is a complete finite induction, with the roots fixed in advance. The template
is a supplied finite simple graph; no existence of an absorber template is assumed
or concluded. Used physical edges are avoided, and injectivity is retained.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.RootedTemplateEmbedding

open Finset RootedEmbeddingSelection

variable {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ}

structure PrefixEmbedding (T : SimpleGraph (Fin m)) (G : SimpleGraph V)
    (B : Finset (Sym2 V)) (k : ℕ) (f : Fin m → V) : Prop where
  injective : ∀ i j, i.val < k → j.val < k → f i = f j → i = j
  edges : ∀ i j, i.val < k → j.val < k → T.Adj i j →
    G.Adj (f i) (f j) ∧ s(f i, f j) ∉ B

theorem extend_prefix (T : SimpleGraph (Fin m)) [DecidableRel T.Adj]
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset (Sym2 V))
    (eps d : ℝ) (heps : eps ≤ 1 / 4)
    (hmin : ∀ u, (3 / 4 + eps) * (Fintype.card V : ℝ) ≤
      ((univ.filter (fun w => G.Adj u w)).card : ℝ))
    (hB : DegBounded B d) (hd : 0 ≤ d)
    (hbudget : (m : ℝ) + 4 * d < 4 * eps * (Fintype.card V : ℝ))
    (k : ℕ) (hk : k < m) (f : Fin m → V) (hf : PrefixEmbedding T G B k f)
    (hparents : (univ.filter (fun i : Fin m => i.val < k ∧ T.Adj i ⟨k, hk⟩)).card ≤ 4) :
    ∃ g, PrefixEmbedding T G B (k + 1) g ∧ ∀ i, i.val < k → g i = f i := by
  let j : Fin m := ⟨k, hk⟩
  let parents := univ.filter (fun i : Fin m => i.val < k ∧ T.Adj i j)
  let S := parents.image f
  let Z := (univ.filter (fun i : Fin m => i.val < k)).image f
  have hS : S.card ≤ 4 := card_image_le.trans hparents
  have hZ : Z.card ≤ m := card_image_le.trans (by
    simpa using (card_filter_le (univ : Finset (Fin m)) (fun i => i.val < k)))
  have hZr : (Z.card : ℝ) ≤ m := by exact_mod_cast hZ
  obtain ⟨w, hw, hnZ, hb⟩ := exists_avoiding_four G S Z B eps d
    heps hS hmin hB hd (by linarith)
  let g := Function.update f j w
  have hkeep : ∀ i, i.val < k → g i = f i := by
    intro i hi
    have hij : i ≠ j := by intro h; subst i; exact (lt_irrefl k) hi
    exact Function.update_of_ne hij w f
  have hnew : g j = w := Function.update_self _ _ _
  have hneq : ∀ i, i.val < k → f i ≠ w := by
    intro i hi he
    apply hnZ
    exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩, he⟩
  have hparent : ∀ i, i.val < k → T.Adj i j → G.Adj (f i) w ∧ s(f i, w) ∉ B := by
    intro i hi hij
    have hiS : f i ∈ S := mem_image.mpr
      ⟨i, mem_filter.mpr ⟨mem_univ _, hi, hij⟩, rfl⟩
    exact ⟨hw _ hiS, hb _ hiS⟩
  refine ⟨g, ⟨?_, ?_⟩, hkeep⟩
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
      obtain ⟨he, hb'⟩ := hparent l hlold hil.symm
      refine ⟨?_, ?_⟩
      · simpa [hnew, hkeep l hlold] using he.symm
      · simpa [hnew, hkeep l hlold, Sym2.eq_swap] using hb'

/-- All nonroots are embedded by finite induction; the initial root map is unchanged. -/
theorem exists_rooted_embedding (T : SimpleGraph (Fin m)) [DecidableRel T.Adj]
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset (Sym2 V))
    (eps d : ℝ) (heps : eps ≤ 1 / 4)
    (hmin : ∀ u, (3 / 4 + eps) * (Fintype.card V : ℝ) ≤
      ((univ.filter (fun w => G.Adj u w)).card : ℝ))
    (hB : DegBounded B d) (hd : 0 ≤ d)
    (hbudget : (m : ℝ) + 4 * d < 4 * eps * (Fintype.card V : ℝ))
    (r : ℕ) (hr : r ≤ m) (rootMap : Fin m → V)
    (hroot : PrefixEmbedding T G B r rootMap)
    (horder : ∀ j : Fin m, r ≤ j.val →
      (univ.filter (fun i : Fin m => i.val < j.val ∧ T.Adj i j)).card ≤ 4) :
    ∃ f, PrefixEmbedding T G B m f ∧ ∀ i, i.val < r → f i = rootMap i := by
  have h : ∀ t, r + t ≤ m → ∃ f, PrefixEmbedding T G B (r + t) f ∧
      ∀ i, i.val < r → f i = rootMap i := by
    intro t
    induction t with
    | zero => intro _; exact ⟨rootMap, hroot, fun _ _ => rfl⟩
    | succ t ih =>
      intro hbound
      obtain ⟨f, hf, hfix⟩ := ih (by omega)
      have hlt : r + t < m := by omega
      obtain ⟨g, hg, hkeep⟩ := extend_prefix T G B eps d heps hmin hB hd
        hbudget (r + t) hlt f hf (horder ⟨r + t, hlt⟩ (by simp))
      refine ⟨g, by simpa only [Nat.add_succ] using hg, ?_⟩
      intro i hi
      exact (hkeep i (by omega)).trans (hfix i hi)
  simpa only [Nat.add_sub_of_le hr] using h (m - r) (by omega)

end PartitionedTriangleAbsorption.RootedTemplateEmbedding
