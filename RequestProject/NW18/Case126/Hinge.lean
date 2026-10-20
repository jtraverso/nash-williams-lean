/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case126.Ideal
public import RequestProject.NW18.Case125.Claim1464Case2

@[expose] public section

/-!
# Six-vertex hinges in an idealized `F`-blowup (Claim 14.7.4)

For two `F`-copies `S = u₁u₂v₁`, `S' = u₁u₂v₂` and two new vertices `x ∈ V_{p u₂}`,
`y ∈ V_{p u₁}` with `x ~ u₁, v₁, v₂, y` and `y ~ u₂, v₁, v₂`, the seven edges
`xu₁, yu₂, xv₁, yv₁, xv₂, yv₂, xy` form an `F`-hinge: `H ∪ {u₁v₁, u₂v₁}` decomposes into
`v₁u₁x, v₁u₂y, v₂xy` and `H ∪ {u₁v₂, u₂v₂}` into `v₂u₁x, v₂u₂y, v₁xy`, all of the types of
`S` and `S'`.  In an `ε`-nearly-complete balanced `F`-blowup there are `Ω(n²)` such pairs.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

/-- The six-vertex model hinge for an arbitrary family. -/
lemma model_hinge6_gen (F : Finset (Multiset (Fin t))) (a₁ a₂ b₁ b₂ c d : Fin t)
    (h1 : ({b₁, a₁, c} : Multiset (Fin t)) ∈ F) (h2 : ({b₁, a₂, d} : Multiset (Fin t)) ∈ F)
    (h3 : ({b₂, c, d} : Multiset (Fin t)) ∈ F) (h4 : ({b₂, a₁, c} : Multiset (Fin t)) ∈ F)
    (h5 : ({b₂, a₂, d} : Multiset (Fin t)) ∈ F) (h6 : ({b₁, c, d} : Multiset (Fin t)) ∈ F) :
    IsHinge (![a₁, a₂, b₁, b₂, c, d] : Fin 6 → Fin t) F mS1 mS2 mH6 := by
  set q : Fin 6 → Fin t := ![a₁, a₂, b₁, b₂, c, d]
  have tt : ∀ (i j k : Fin 6), i ≠ j → i ≠ k → j ≠ k → ({q i, q j, q k} : Multiset (Fin t)) ∈ F →
      IsTypedTri q F {i, j, k} := by
    intro i j k hij hik hjk h
    refine ⟨?_, ?_⟩
    · rw [card_insert_of_notMem (by simp [hij, hik]), card_pair hjk]
    · rw [triple_val_map q hij hik hjk]; exact h
  refine ⟨by decide +kernel, ⟨{{2, 0, 4}, {2, 1, 5}, {3, 4, 5}},
    isDecomp_of_typed _ _ _ _ ?_ (by decide +kernel) (by decide +kernel)⟩,
    ⟨{{3, 0, 4}, {3, 1, 5}, {2, 4, 5}},
    isDecomp_of_typed _ _ _ _ ?_ (by decide +kernel) (by decide +kernel)⟩⟩
  · intro s hs
    simp only [mem_insert, mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact tt 2 0 4 (by decide) (by decide) (by decide) h1
    · exact tt 2 1 5 (by decide) (by decide) (by decide) h2
    · exact tt 3 4 5 (by decide) (by decide) (by decide) h3
  · intro s hs
    simp only [mem_insert, mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact tt 3 0 4 (by decide) (by decide) (by decide) h4
    · exact tt 3 1 5 (by decide) (by decide) (by decide) h5
    · exact tt 2 4 5 (by decide) (by decide) (by decide) h6

/-- An admissible pair `(x, y)` gives an `F`-hinge on six vertices. -/
lemma isHinge6_of_gen (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin t)
    (F : Finset (Multiset (Fin t)))
    {u₁ u₂ v₁ v₂ x y : V} (hinj : Function.Injective (vec6 u₁ u₂ v₁ v₂ x y))
    (a1 : G.Adj u₁ x) (a2 : G.Adj u₂ y) (a3 : G.Adj v₁ x) (a4 : G.Adj v₁ y) (a5 : G.Adj v₂ x)
    (a6 : G.Adj v₂ y) (a7 : G.Adj x y)
    (h1 : ({p v₁, p u₁, p x} : Multiset (Fin t)) ∈ F)
    (h2 : ({p v₁, p u₂, p y} : Multiset (Fin t)) ∈ F)
    (h3 : ({p v₂, p x, p y} : Multiset (Fin t)) ∈ F)
    (h4 : ({p v₂, p u₁, p x} : Multiset (Fin t)) ∈ F)
    (h5 : ({p v₂, p u₂, p y} : Multiset (Fin t)) ∈ F)
    (h6 : ({p v₁, p x, p y} : Multiset (Fin t)) ∈ F) :
    mH6.image (Sym2.map (vec6 u₁ u₂ v₁ v₂ x y)) ⊆ G.edgeFinset ∧
    IsHinge p F {u₁, u₂, v₁} {u₁, u₂, v₂} (mH6.image (Sym2.map (vec6 u₁ u₂ v₁ v₂ x y))) ∧
    (vertSet (mH6.image (Sym2.map (vec6 u₁ u₂ v₁ v₂ x y)))).card = 6 := by
  set f : Fin 6 ↪ V := ⟨vec6 u₁ u₂ v₁ v₂ x y, hinj⟩
  have himg : mH6.image (Sym2.map (vec6 u₁ u₂ v₁ v₂ x y)) = mH6.map f.sym2Map := by
    rw [map_eq_image]; rfl
  refine ⟨fun e he => ?_, ?_, ?_⟩
  · obtain ⟨i, j, hij, rfl⟩ := mem_image_sym2_map6.mp he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    have hc := mH6_cases i j hij
    simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hc
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ <;>
    simp only [vec6, Matrix.cons_val] <;>
    first
      | exact a1 | exact a2 | exact a3 | exact a4 | exact a5 | exact a6 | exact a7
      | exact SimpleGraph.Adj.symm a1 | exact SimpleGraph.Adj.symm a2 | exact SimpleGraph.Adj.symm a3 | exact SimpleGraph.Adj.symm a4
      | exact SimpleGraph.Adj.symm a5 | exact SimpleGraph.Adj.symm a6 | exact SimpleGraph.Adj.symm a7
  · have e1 : mS1.map f = {u₁, u₂, v₁} := by simp [mS1, f, vec6]
    have e2 : mS2.map f = {u₁, u₂, v₂} := by simp [mS2, f, vec6]
    rw [himg, ← e1, ← e2]
    refine isHinge_map_typed f (q := ![p u₁, p u₂, p v₁, p v₂, p x, p y]) ?_
      (model_hinge6_gen F _ _ _ _ _ _ h1 h2 h3 h4 h5 h6)
    intro w; fin_cases w <;> rfl
  · rw [himg]
    have : vertSet (mH6.map f.sym2Map) = (vertSet mH6).map f := by
      ext v
      simp only [vertSet, mem_filter, mem_univ, true_and, mem_map,
        Function.Embedding.sym2Map_apply]
      constructor
      · rintro ⟨_, ⟨e, he, rfl⟩, hv⟩
        rw [Sym2.mem_map] at hv
        obtain ⟨w, hw, rfl⟩ := hv
        exact ⟨w, ⟨e, he, hw⟩, rfl⟩
      · rintro ⟨w, ⟨e, he, hw⟩, rfl⟩
        exact ⟨_, ⟨e, he, rfl⟩, Sym2.mem_map.mpr ⟨w, hw, rfl⟩⟩
    rw [this, vertSet_mH6, card_map, card_univ, Fintype.card_fin]

/-! ### Counting -/

omit [DecidableEq V] in
lemma filter_forall_insert_gen (p : V → Fin t) (G : SimpleGraph V) [DecidableRel G.Adj]
    (j : Fin t) (a : V) (s : Finset V) [DecidableEq V] :
    (clsT p j).filter (fun x => ∀ z ∈ insert a s, G.Adj z x) =
      ((clsT p j).filter (fun x => ∀ z ∈ s, G.Adj z x)).filter (G.Adj a) := by
  ext x
  simp only [mem_filter, forall_mem_insert]
  tauto

omit [DecidableEq V] in
lemma card_filter_adj_ge_gen (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin t)
    {j : Fin t} {S : Finset V} (hS : S ⊆ clsT p j) (v : V) :
    (S.card : ℝ) - ((clsT p j).card - degT G p v j) ≤ (S.filter (G.Adj v)).card := by
  have hdeg : degT G p v j = ((clsT p j).filter (G.Adj v)).card := by
    unfold degT clsT; rw [filter_filter]; congr 1; ext w; simp [and_comm]
  rw [hdeg]
  have h1 := card_filter_add_card_filter_not (s := S) (G.Adj v)
  have h2 := card_filter_add_card_filter_not (s := clsT p j) (G.Adj v)
  have h3 : (S.filter (fun x => ¬ G.Adj v x)).card ≤
      ((clsT p j).filter (fun x => ¬ G.Adj v x)).card :=
    card_le_card (filter_subset_filter _ hS)
  have h1' : ((S.filter (G.Adj v)).card : ℝ) + (S.filter (fun x => ¬ G.Adj v x)).card =
      S.card := by exact_mod_cast h1
  have h2' : (((clsT p j).filter (G.Adj v)).card : ℝ) +
      ((clsT p j).filter (fun x => ¬ G.Adj v x)).card = (clsT p j).card := by exact_mod_cast h2
  have h3' : ((S.filter (fun x => ¬ G.Adj v x)).card : ℝ) ≤
      ((clsT p j).filter (fun x => ¬ G.Adj v x)).card := by exact_mod_cast h3
  linarith

/-- A common neighbourhood inside a part misses at most the sum of the individual misses. -/
lemma card_commonNbT_ge (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin t) (j : Fin t)
    (Z : Finset V) :
    ((clsT p j).card : ℝ) - ∑ z ∈ Z, (((clsT p j).card : ℝ) - degT G p z j) ≤
      ((clsT p j).filter (fun x => ∀ z ∈ Z, G.Adj z x)).card := by
  induction Z using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    rw [filter_forall_insert_gen, sum_insert has]
    have := card_filter_adj_ge_gen G p (j := j)
      (S := (clsT p j).filter (fun x => ∀ z ∈ s, G.Adj z x)) (filter_subset _ _) a
    linarith

/-- The candidates in `V_j`: common neighbours of `Z` avoiding `Bd`. -/
def candT (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin t) (j : Fin t)
    (Z Bd : Finset V) : Finset V :=
  ((clsT p j).filter (fun x => ∀ z ∈ Z, G.Adj z x)) \ Bd

lemma mem_candT {G : SimpleGraph V} [DecidableRel G.Adj] {p : V → Fin t} {j : Fin t}
    {Z Bd : Finset V} {x : V} :
    x ∈ candT G p j Z Bd ↔ (p x = j ∧ ∀ z ∈ Z, G.Adj z x) ∧ x ∉ Bd := by
  simp [candT, clsT]

lemma card_candT_ge (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin t) (j : Fin t)
    (Z Bd : Finset V) {m : ℝ} (hm : ∀ z ∈ Z, ((clsT p j).card : ℝ) - degT G p z j ≤ m) :
    ((clsT p j).card : ℝ) - Z.card * m - Bd.card ≤ (candT G p j Z Bd).card := by
  have h1 := card_commonNbT_ge G p j Z
  have h3 : ∑ z ∈ Z, (((clsT p j).card : ℝ) - degT G p z j) ≤ Z.card • m :=
    sum_le_card_nsmul _ _ _ hm
  rw [nsmul_eq_mul] at h3
  have h6 : ((clsT p j).filter (fun x => ∀ z ∈ Z, G.Adj z x)).card ≤
      (((clsT p j).filter (fun x => ∀ z ∈ Z, G.Adj z x)) \ Bd).card + Bd.card :=
    card_le_card_sdiff_add_card
  have h6' : (((clsT p j).filter (fun x => ∀ z ∈ Z, G.Adj z x)).card : ℝ) ≤
      ((((clsT p j).filter (fun x => ∀ z ∈ Z, G.Adj z x)) \ Bd).card : ℝ) + Bd.card := by
    exact_mod_cast h6
  unfold candT
  linarith

open Classical in
/-- Pairs from a nested choice give six-vertex `F`-hinges. -/
lemma hinge6_count_gen (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin t)
    (F : Finset (Multiset (Fin t)))
    (u₁ u₂ v₁ v₂ : V) (A : Finset V) (B : V → Finset V) {r : ℝ} (hr : 0 ≤ r)
    (hA : r ≤ A.card) (hB : ∀ x ∈ A, r ≤ (B x).card)
    (hP : ∀ x ∈ A, ∀ y ∈ B x, Function.Injective (vec6 u₁ u₂ v₁ v₂ x y) ∧
      G.Adj u₁ x ∧ G.Adj u₂ y ∧ G.Adj v₁ x ∧ G.Adj v₁ y ∧ G.Adj v₂ x ∧ G.Adj v₂ y ∧
      G.Adj x y ∧
      ({p v₁, p u₁, p x} : Multiset (Fin t)) ∈ F ∧ ({p v₁, p u₂, p y} : Multiset (Fin t)) ∈ F ∧
      ({p v₂, p x, p y} : Multiset (Fin t)) ∈ F ∧ ({p v₂, p u₁, p x} : Multiset (Fin t)) ∈ F ∧
      ({p v₂, p u₂, p y} : Multiset (Fin t)) ∈ F ∧ ({p v₁, p x, p y} : Multiset (Fin t)) ∈ F) :
    r * r ≤ ((G.edgeFinset.powerset.filter (fun H => IsHinge p F {u₁, u₂, v₁} {u₁, u₂, v₂} H ∧
        (vertSet H).card = 6)).card : ℝ) := by
  set P := (A.sigma B).image (fun z => (z.1, z.2)) with hPdef
  have hPc : (P.card : ℝ) = ∑ x ∈ A, ((B x).card : ℝ) := by
    rw [hPdef, card_image_of_injective]
    · rw [card_sigma]; push_cast; rfl
    · rintro ⟨x, y⟩ ⟨x', y'⟩ h
      have h1 : x = x' := congrArg Prod.fst h
      have h2 : y = y' := congrArg Prod.snd h
      subst h1; subst h2; rfl
  have hsum : r * r ≤ ∑ x ∈ A, ((B x).card : ℝ) := by
    calc r * r ≤ A.card * r := mul_le_mul_of_nonneg_right hA hr
      _ = ∑ x ∈ A, r := by rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := sum_le_sum hB
  refine le_trans (hsum.trans hPc.symm.le) ?_
  exact_mod_cast card_le_card_of_injOn
    (fun z : V × V => mH6.image (Sym2.map (vec6 u₁ u₂ v₁ v₂ z.1 z.2)))
    (fun z hz => by
      rw [hPdef, coe_image] at hz
      obtain ⟨⟨x, y⟩, hxy, rfl⟩ := hz
      rw [mem_coe, mem_sigma] at hxy
      obtain ⟨hi, a1, a2, a3, a4, a5, a6, a7, h1, h2, h3, h4, h5, h6⟩ := hP x hxy.1 y hxy.2
      obtain ⟨e1, e2, e3⟩ := isHinge6_of_gen G p F hi a1 a2 a3 a4 a5 a6 a7 h1 h2 h3 h4 h5 h6
      rw [coe_filter]
      exact ⟨mem_powerset.mpr e1, e2, e3⟩)
    (fun z hz w hw hzw => by
      rw [hPdef, coe_image] at hw
      obtain ⟨⟨x, y⟩, hxy, rfl⟩ := hw
      rw [mem_coe, mem_sigma] at hxy
      obtain ⟨h1, h2⟩ := vec6_pair_eq (hP x hxy.1 y hxy.2).1 hzw
      exact Prod.ext h1 h2)

end NashWilliams18
