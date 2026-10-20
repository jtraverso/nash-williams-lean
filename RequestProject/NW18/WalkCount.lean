/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.HingeCfg
import RequestProject.NW18.Stab4

/-!
# Configurations versus walks

The number of configurations of a model hinge differs from the number of homomorphic copies
(where the four new vertices need not be distinct) by `O(n³)`.  The homomorphic copies of the
two model hinges are counted through walks of length four (`walk4`).
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Homomorphic copies of the model hinge `M` on `u₁, u₂, v₁, v₂` (the four new vertices need
not be distinct). -/
noncomputable def homCount (M : Finset (Sym2 (Fin 8))) (G : SimpleGraph V) [DecidableRel G.Adj]
    (u₁ u₂ v₁ v₂ : V) : ℕ :=
  ((univ : Finset (V × V × V × V)).filter (fun x =>
    ∀ i j : Fin 8, s(i, j) ∈ M → G.Adj (cfgVec u₁ u₂ v₁ v₂ x i) (cfgVec u₁ u₂ v₁ v₂ x j))).card

omit [Fintype V] [DecidableEq V] in
lemma cfgVec_injective_of {u₁ u₂ v₁ v₂ x₁ x₂ x₃ x₄ : V}
    (h4 : Function.Injective ![u₁, u₂, v₁, v₂])
    (h1 : x₁ ∉ ({u₁, u₂, v₁, v₂} : Set V)) (h2 : x₂ ∉ ({u₁, u₂, v₁, v₂} : Set V))
    (h3 : x₃ ∉ ({u₁, u₂, v₁, v₂} : Set V)) (h5 : x₄ ∉ ({u₁, u₂, v₁, v₂} : Set V))
    (d12 : x₁ ≠ x₂) (d13 : x₁ ≠ x₃) (d14 : x₁ ≠ x₄) (d23 : x₂ ≠ x₃) (d24 : x₂ ≠ x₄)
    (d34 : x₃ ≠ x₄) :
    Function.Injective (cfgVec u₁ u₂ v₁ v₂ (x₁, x₂, x₃, x₄)) := by
  have e01 : u₁ ≠ u₂ := fun h => absurd (h4 (a₁ := 0) (a₂ := 1) (by simpa using h)) (by decide)
  have e02 : u₁ ≠ v₁ := fun h => absurd (h4 (a₁ := 0) (a₂ := 2) (by simpa using h)) (by decide)
  have e03 : u₁ ≠ v₂ := fun h => absurd (h4 (a₁ := 0) (a₂ := 3) (by simpa using h)) (by decide)
  have e12 : u₂ ≠ v₁ := fun h => absurd (h4 (a₁ := 1) (a₂ := 2) (by simpa using h)) (by decide)
  have e13 : u₂ ≠ v₂ := fun h => absurd (h4 (a₁ := 1) (a₂ := 3) (by simpa using h)) (by decide)
  have e23 : v₁ ≠ v₂ := fun h => absurd (h4 (a₁ := 2) (a₂ := 3) (by simpa using h)) (by decide)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h1 h2 h3 h5
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [cfgVec] at h ⊢ <;> tauto

/-- Homomorphic copies exceed configurations by at most `22 n³`. -/
lemma homCount_le (M : Finset (Sym2 (Fin 8))) (G : SimpleGraph V) [DecidableRel G.Adj]
    {u₁ u₂ v₁ v₂ : V} (h4 : Function.Injective ![u₁, u₂, v₁, v₂]) :
    homCount M G u₁ u₂ v₁ v₂ ≤ cfgCount M G u₁ u₂ v₁ v₂ + 22 * Fintype.card V ^ 3 := by
  classical
  set S : Finset V := {u₁, u₂, v₁, v₂}
  -- the "bad" tuples
  let B : Finset (V × V × V × V) :=
    (S ×ˢ univ ×ˢ univ ×ˢ univ) ∪ (univ ×ˢ S ×ˢ univ ×ˢ univ) ∪ (univ ×ˢ univ ×ˢ S ×ˢ univ) ∪
    (univ ×ˢ univ ×ˢ univ ×ˢ S) ∪
    ((univ : Finset (V × V × V)).image (fun y => (y.1, y.1, y.2.1, y.2.2))) ∪
    ((univ : Finset (V × V × V)).image (fun y => (y.1, y.2.1, y.1, y.2.2))) ∪
    ((univ : Finset (V × V × V)).image (fun y => (y.1, y.2.1, y.2.2, y.1))) ∪
    ((univ : Finset (V × V × V)).image (fun y => (y.1, y.2.1, y.2.1, y.2.2))) ∪
    ((univ : Finset (V × V × V)).image (fun y => (y.1, y.2.1, y.2.2, y.2.1))) ∪
    ((univ : Finset (V × V × V)).image (fun y => (y.1, y.2.1, y.2.2, y.2.2)))
  have hS : S.card ≤ 4 := card_le_four
  have hB : B.card ≤ 22 * Fintype.card V ^ 3 := by
    have hi : ∀ g : V × V × V → V × V × V × V,
        ((univ : Finset (V × V × V)).image g).card ≤ Fintype.card V ^ 3 := fun g => by
      refine card_image_le.trans ?_
      simp [card_univ, Fintype.card_prod]; ring_nf; rfl
    have hp1 : (S ×ˢ (univ : Finset V) ×ˢ (univ : Finset V) ×ˢ (univ : Finset V)).card ≤
        4 * Fintype.card V ^ 3 := by
      simp only [card_product, card_univ]
      calc _ ≤ 4 * (Fintype.card V * (Fintype.card V * Fintype.card V)) :=
            Nat.mul_le_mul_right _ hS
        _ = _ := by ring
    have hp2 : ((univ : Finset V) ×ˢ S ×ˢ (univ : Finset V) ×ˢ (univ : Finset V)).card ≤
        4 * Fintype.card V ^ 3 := by
      simp only [card_product, card_univ]
      calc _ ≤ Fintype.card V * (4 * (Fintype.card V * Fintype.card V)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hS)
        _ = _ := by ring
    have hp3 : ((univ : Finset V) ×ˢ (univ : Finset V) ×ˢ S ×ˢ (univ : Finset V)).card ≤
        4 * Fintype.card V ^ 3 := by
      simp only [card_product, card_univ]
      calc _ ≤ Fintype.card V * (Fintype.card V * (4 * Fintype.card V)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hS))
        _ = _ := by ring
    have hp4 : ((univ : Finset V) ×ˢ (univ : Finset V) ×ˢ (univ : Finset V) ×ˢ S).card ≤
        4 * Fintype.card V ^ 3 := by
      simp only [card_product, card_univ]
      calc _ ≤ Fintype.card V * (Fintype.card V * (Fintype.card V * 4)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hS))
        _ = _ := by ring
    refine (card_union_le _ _).trans ?_
    refine (Nat.add_le_add_right (card_union_le _ _) _).trans ?_
    refine (Nat.add_le_add_right (Nat.add_le_add_right (card_union_le _ _) _) _).trans ?_
    refine (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (card_union_le _ _) _) _) _).trans ?_
    refine (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add_right (card_union_le _ _) _) _) _) _).trans ?_
    refine (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add_right (Nat.add_le_add_right (card_union_le _ _) _) _) _) _) _).trans ?_
    refine (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (card_union_le _ _) _) _) _) _) _) _).trans ?_
    refine (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add_right (card_union_le _ _) _) _) _) _) _) _) _).trans ?_
    refine (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add_right (Nat.add_le_add_right (card_union_le _ _) _) _) _) _) _) _) _)
      _).trans ?_
    have := hi (fun y => (y.1, y.1, y.2.1, y.2.2))
    have := hi (fun y => (y.1, y.2.1, y.1, y.2.2))
    have := hi (fun y => (y.1, y.2.1, y.2.2, y.1))
    have := hi (fun y => (y.1, y.2.1, y.2.1, y.2.2))
    have := hi (fun y => (y.1, y.2.1, y.2.2, y.2.1))
    have := hi (fun y => (y.1, y.2.1, y.2.2, y.2.2))
    omega
  -- every non-injective homomorphic copy is bad
  have hsub : (univ.filter (fun x : V × V × V × V =>
      ∀ i j : Fin 8, s(i, j) ∈ M → G.Adj (cfgVec u₁ u₂ v₁ v₂ x i) (cfgVec u₁ u₂ v₁ v₂ x j))) ⊆
      (univ.filter (fun x => IsCfg M G u₁ u₂ v₁ v₂ x)) ∪ B := by
    intro x hx
    rw [mem_filter] at hx
    by_cases hinj : Function.Injective (cfgVec u₁ u₂ v₁ v₂ x)
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hinj, hx.2⟩)
    · refine mem_union_right _ ?_
      obtain ⟨x₁, x₂, x₃, x₄⟩ := x
      by_contra hxB
      apply hinj
      have hmem : ∀ y : V, y ∈ ({u₁, u₂, v₁, v₂} : Set V) ↔ y ∈ S := fun y => by
        simp [S]
      simp only [B, mem_union, mem_product, mem_univ, and_true, true_and, mem_image,
        Prod.mk.injEq, Prod.exists, not_or, not_exists, not_and] at hxB
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h5⟩, d12⟩, d13⟩, d14⟩, d23⟩, d24⟩, d34⟩ := hxB
      refine cfgVec_injective_of h4 (by rwa [hmem]) (by rwa [hmem]) (by rwa [hmem])
        (by rwa [hmem]) ?_ ?_ ?_ ?_ ?_ ?_
      · intro h; exact d12 x₁ x₃ x₄ rfl h rfl rfl
      · intro h; exact d13 x₁ x₂ x₄ rfl rfl h rfl
      · intro h; exact d14 x₁ x₂ x₃ rfl rfl rfl h
      · intro h; exact d23 x₁ x₂ x₄ rfl rfl h rfl
      · intro h; exact d24 x₁ x₂ x₃ rfl rfl rfl h
      · intro h; exact d34 x₁ x₂ x₃ rfl rfl rfl h
  unfold homCount cfgCount
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ ≤ _ := by convert Nat.add_le_add_left hB _

/-- Counting quadruples given by nested choices. -/
lemma sum4_le_card {α β : Type*} [DecidableEq β] (A : Finset α) (B : α → Finset α)
    (C : α → α → Finset α) (S : α → α → α → Finset α) (T : Finset β)
    (F : α → α → α → α → β)
    (hF : ∀ d ∈ A, ∀ a ∈ B d, ∀ c ∈ C d a, ∀ b ∈ S d a c, F d a c b ∈ T)
    (hinj : ∀ d a c b d' a' c' b', F d a c b = F d' a' c' b' → d = d' ∧ a = a' ∧ c = c' ∧ b = b') :
    ∑ d ∈ A, ∑ a ∈ B d, ∑ c ∈ C d a, (S d a c).card ≤ T.card := by
  have : ∑ d ∈ A, ∑ a ∈ B d, ∑ c ∈ C d a, (S d a c).card =
      (A.sigma fun d => (B d).sigma fun a => (C d a).sigma fun c => S d a c).card := by
    simp [card_sigma]
  rw [this]
  refine card_le_card_of_injOn (fun p => F p.1 p.2.1 p.2.2.1 p.2.2.2) ?_ ?_
  · rintro ⟨d, a, c, b⟩ hp
    simp only [coe_sigma, Set.mem_sigma_iff, mem_coe] at hp
    exact hF d hp.1 a hp.2.1 c hp.2.2.1 b hp.2.2.2
  · rintro ⟨d, a, c, b⟩ _ ⟨d', a', c', b'⟩ _ h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hinj d a c b d' a' c' b' h
    rfl

variable (G : SimpleGraph V) [DecidableRel G.Adj]

lemma mH1_cases (i j : Fin 8) (h : s(i, j) ∈ mH1) :
    (i, j) ∈ ([(2, 4), (4, 2), (2, 5), (5, 2), (2, 6), (6, 2), (2, 7), (7, 2), (3, 4), (4, 3),
      (3, 5), (5, 3), (3, 6), (6, 3), (3, 7), (7, 3), (0, 4), (4, 0), (4, 5), (5, 4), (5, 6),
      (6, 5), (6, 7), (7, 6), (7, 1), (1, 7)] : List (Fin 8 × Fin 8)) := by
  revert i j h; decide +kernel

lemma mH2_cases (i j : Fin 8) (h : s(i, j) ∈ mH2) :
    (i, j) ∈ ([(1, 5), (5, 1), (1, 6), (6, 1), (1, 7), (7, 1), (4, 0), (0, 4), (4, 2), (2, 4),
      (4, 5), (5, 4), (4, 6), (6, 4), (4, 7), (7, 4), (4, 3), (3, 4), (2, 5), (5, 2), (5, 6),
      (6, 5), (6, 7), (7, 6), (7, 3), (3, 7)] : List (Fin 8 × Fin 8)) := by
  revert i j h; decide +kernel

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma hom_mH1_of {u₁ u₂ v₁ v₂ x₁ x₂ x₃ x₄ : V}
    (h1 : G.Adj v₁ x₁ ∧ G.Adj v₂ x₁) (h2 : G.Adj v₁ x₂ ∧ G.Adj v₂ x₂)
    (h3 : G.Adj v₁ x₃ ∧ G.Adj v₂ x₃) (h4 : G.Adj v₁ x₄ ∧ G.Adj v₂ x₄)
    (a1 : G.Adj u₁ x₁) (a2 : G.Adj x₁ x₂) (a3 : G.Adj x₂ x₃) (a4 : G.Adj x₃ x₄)
    (a5 : G.Adj x₄ u₂) :
    ∀ i j : Fin 8, s(i, j) ∈ mH1 →
      G.Adj (cfgVec u₁ u₂ v₁ v₂ (x₁, x₂, x₃, x₄) i) (cfgVec u₁ u₂ v₁ v₂ (x₁, x₂, x₃, x₄) j) := by
  intro i j h
  have hc := mH1_cases i j h
  simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hc
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  simp only [cfgVec_0, cfgVec_1, cfgVec_2, cfgVec_3, cfgVec_4, cfgVec_5, cfgVec_6, cfgVec_7] <;>
  first
    | exact h1.1 | exact h1.2 | exact h2.1 | exact h2.2 | exact h3.1 | exact h3.2
    | exact h4.1 | exact h4.2 | exact SimpleGraph.Adj.symm h1.1 | exact SimpleGraph.Adj.symm h1.2 | exact SimpleGraph.Adj.symm h2.1
    | exact SimpleGraph.Adj.symm h2.2 | exact SimpleGraph.Adj.symm h3.1 | exact SimpleGraph.Adj.symm h3.2 | exact SimpleGraph.Adj.symm h4.1
    | exact SimpleGraph.Adj.symm h4.2 | exact a1 | exact a2 | exact a3 | exact a4 | exact a5
    | exact SimpleGraph.Adj.symm a1 | exact SimpleGraph.Adj.symm a2 | exact SimpleGraph.Adj.symm a3 | exact SimpleGraph.Adj.symm a4 | exact SimpleGraph.Adj.symm a5

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma hom_mH2_of {u₁ u₂ v₁ v₂ w a b c : V}
    (w1 : G.Adj w u₁) (w2 : G.Adj w v₁) (w3 : G.Adj w v₂) (wa : G.Adj w a) (wb : G.Adj w b)
    (wc : G.Adj w c) (ua : G.Adj u₂ a) (ub : G.Adj u₂ b) (uc : G.Adj u₂ c)
    (a1 : G.Adj v₁ a) (a2 : G.Adj a b) (a3 : G.Adj b c) (a4 : G.Adj c v₂) :
    ∀ i j : Fin 8, s(i, j) ∈ mH2 →
      G.Adj (cfgVec u₁ u₂ v₁ v₂ (w, a, b, c) i) (cfgVec u₁ u₂ v₁ v₂ (w, a, b, c) j) := by
  intro i j h
  have hc := mH2_cases i j h
  simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hc
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  simp only [cfgVec_0, cfgVec_1, cfgVec_2, cfgVec_3, cfgVec_4, cfgVec_5, cfgVec_6, cfgVec_7] <;>
  first
    | exact w1 | exact w2 | exact w3 | exact wa | exact wb | exact wc | exact ua | exact ub
    | exact uc | exact a1 | exact a2 | exact a3 | exact a4
    | exact SimpleGraph.Adj.symm w1 | exact SimpleGraph.Adj.symm w2 | exact SimpleGraph.Adj.symm w3 | exact SimpleGraph.Adj.symm wa | exact SimpleGraph.Adj.symm wb
    | exact SimpleGraph.Adj.symm wc | exact SimpleGraph.Adj.symm ua | exact SimpleGraph.Adj.symm ub | exact SimpleGraph.Adj.symm uc | exact SimpleGraph.Adj.symm a1
    | exact SimpleGraph.Adj.symm a2 | exact SimpleGraph.Adj.symm a3 | exact SimpleGraph.Adj.symm a4


/-- The common neighbourhood of `v₁, v₂`. -/
def comNb (v₁ v₂ : V) : Finset V := univ.filter (fun x => G.Adj v₁ x ∧ G.Adj v₂ x)

/-- Walks of length five `u₁ x₁ x₂ x₃ x₄ u₂` in `N(v₁) ∩ N(v₂)` give homomorphic copies of the
type-1 hinge. -/
lemma walk_le_hom1 (u₁ u₂ v₁ v₂ : V) :
    ∑ d ∈ nbIn G (comNb G v₁ v₂) u₂, walk4 G (comNb G v₁ v₂) u₁ d ≤
      homCount mH1 G u₁ u₂ v₁ v₂ := by
  unfold walk4 homCount
  set N := comNb G v₁ v₂
  refine sum4_le_card (nbIn G N u₂) (fun _ => nbIn G N u₁) (fun d _ => nbIn G N d)
    (fun _ a c => nbIn G N a ∩ nbIn G N c) _ (fun d a c b => (a, b, c, d)) ?_ ?_
  · intro d hd a ha c hc b hb
    rw [mem_nbIn] at hd ha hc
    rw [mem_inter, mem_nbIn, mem_nbIn] at hb
    have mN : ∀ {x}, x ∈ N → G.Adj v₁ x ∧ G.Adj v₂ x := fun hx => (mem_filter.mp hx).2
    rw [mem_filter]
    exact ⟨mem_univ _, hom_mH1_of G (mN ha.1) (mN hb.1.1) (mN hc.1) (mN hd.1) ha.2 hb.1.2
      (SimpleGraph.Adj.symm hb.2.2) (SimpleGraph.Adj.symm hc.2) hd.2.symm⟩
  · intro d a c b d' a' c' b' h
    simp only [Prod.mk.injEq] at h
    tauto

/-- Walks `v₁ a b c v₂` inside `D w ⊆ N(w) ∩ N(u₂)`, for `w ∈ L ⊆ N(u₁) ∩ N(v₁) ∩ N(v₂)`, give
homomorphic copies of the type-2 hinge. -/
lemma walk_le_hom2 (u₁ u₂ v₁ v₂ : V) (L : Finset V) (D : V → Finset V)
    (hL : ∀ w ∈ L, G.Adj w u₁ ∧ G.Adj w v₁ ∧ G.Adj w v₂)
    (hD : ∀ w ∈ L, ∀ y ∈ D w, G.Adj w y ∧ G.Adj u₂ y) :
    ∑ w ∈ L, walk4 G (D w) v₁ v₂ ≤ homCount mH2 G u₁ u₂ v₁ v₂ := by
  unfold walk4 homCount
  refine sum4_le_card L (fun w => nbIn G (D w) v₁) (fun w _ => nbIn G (D w) v₂)
    (fun w a c => nbIn G (D w) a ∩ nbIn G (D w) c) _ (fun w a c b => (w, a, b, c)) ?_ ?_
  · intro w hw a ha c hc b hb
    rw [mem_nbIn] at ha hc
    rw [mem_inter, mem_nbIn, mem_nbIn] at hb
    obtain ⟨w1, w2, w3⟩ := hL w hw
    rw [mem_filter]
    exact ⟨mem_univ _, hom_mH2_of G w1 w2 w3 (hD w hw a ha.1).1 (hD w hw b hb.1.1).1
      (hD w hw c hc.1).1 (hD w hw a ha.1).2 (hD w hw b hb.1.1).2 (hD w hw c hc.1).2 ha.2
      hb.1.2 (SimpleGraph.Adj.symm hb.2.2) (SimpleGraph.Adj.symm hc.2)⟩
  · intro d a c b d' a' c' b' h
    simp only [Prod.mk.injEq] at h
    tauto

end NashWilliams18
