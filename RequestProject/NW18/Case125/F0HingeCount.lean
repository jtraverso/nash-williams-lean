/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case125.F0Hinge

@[expose] public section

/-!
# Counting `F₀`-hinges

* Eight-vertex hinges: *typed configurations* (configurations of `HingeCfg.lean` whose
  vertices lie in prescribed parts) give distinct `F₀`-hinges (`tcfgCount_le_hingeCount`);
  typed homomorphic copies exceed typed configurations by `O(n³)` (`thomCount_le`); and walks
  of length five (type 1) or four (type 2) in suitable common neighbourhoods inside one part
  give typed homomorphic copies (`walk_le_thom1`, `walk_le_thom2`).
* Six-vertex hinges: every admissible pair `(x, y)` gives a distinct `F₀`-hinge
  (`pairs_le_hingeCount6`).
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks (F0)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Typed configurations -/

/-- A configuration of type `M` all of whose eight vertices lie in the parts prescribed by
`q`. -/
def IsTCfg (M : Finset (Sym2 (Fin 8))) (q : Fin 8 → Fin 2) (G : SimpleGraph V)
    (p : V → Fin 2) (u₁ u₂ v₁ v₂ : V) (x : V × V × V × V) : Prop :=
  IsCfg M G u₁ u₂ v₁ v₂ x ∧ ∀ i, p (cfgVec u₁ u₂ v₁ v₂ x i) = q i

open Classical in
/-- The number of typed configurations. -/
noncomputable def tcfgCount (M : Finset (Sym2 (Fin 8))) (q : Fin 8 → Fin 2) (G : SimpleGraph V)
    (p : V → Fin 2) (u₁ u₂ v₁ v₂ : V) : ℕ :=
  ((univ : Finset (V × V × V × V)).filter (fun x => IsTCfg M q G p u₁ u₂ v₁ v₂ x)).card

/-- The number of typed homomorphic copies (not necessarily injective). -/
def thomCount (M : Finset (Sym2 (Fin 8))) (q : Fin 8 → Fin 2) (G : SimpleGraph V)
    [DecidableRel G.Adj] (p : V → Fin 2) (u₁ u₂ v₁ v₂ : V) : ℕ :=
  ((univ : Finset (V × V × V × V)).filter (fun x =>
    (∀ i j : Fin 8, s(i, j) ∈ M → G.Adj (cfgVec u₁ u₂ v₁ v₂ x i) (cfgVec u₁ u₂ v₁ v₂ x j)) ∧
      ∀ i, p (cfgVec u₁ u₂ v₁ v₂ x i) = q i)).card

/-- Typed homomorphic copies exceed typed configurations by at most `22 n³`. -/
lemma thomCount_le (M : Finset (Sym2 (Fin 8))) (q : Fin 8 → Fin 2) (G : SimpleGraph V)
    [DecidableRel G.Adj] (p : V → Fin 2) {u₁ u₂ v₁ v₂ : V}
    (h4 : Function.Injective ![u₁, u₂, v₁, v₂]) :
    thomCount M q G p u₁ u₂ v₁ v₂ ≤ tcfgCount M q G p u₁ u₂ v₁ v₂ + 22 * Fintype.card V ^ 3 := by
  classical
  have hle := homCount_le M G h4
  unfold homCount cfgCount at hle
  unfold thomCount tcfgCount
  set Hm := (univ : Finset (V × V × V × V)).filter (fun x =>
    ∀ i j : Fin 8, s(i, j) ∈ M → G.Adj (cfgVec u₁ u₂ v₁ v₂ x i) (cfgVec u₁ u₂ v₁ v₂ x j))
  set Cf := (univ : Finset (V × V × V × V)).filter (fun x => IsCfg M G u₁ u₂ v₁ v₂ x)
  have hsub : Cf ⊆ Hm := by
    intro x hx
    simp only [Cf, Hm, mem_filter, mem_univ, true_and] at hx ⊢
    exact hx.2
  have hcs : (Hm \ Cf).card + Cf.card = Hm.card := card_sdiff_add_card_eq_card hsub
  refine (card_le_card (t := ((univ : Finset (V × V × V × V)).filter
    (fun x => IsTCfg M q G p u₁ u₂ v₁ v₂ x)) ∪ (Hm \ Cf)) ?_).trans
    ((card_union_le _ _).trans ?_)
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    by_cases hinj : Function.Injective (cfgVec u₁ u₂ v₁ v₂ x)
    · exact mem_union_left _ (by simp only [mem_filter, mem_univ, true_and]
                                 exact ⟨⟨hinj, hx.1⟩, hx.2⟩)
    · refine mem_union_right _ (mem_sdiff.mpr ⟨?_, ?_⟩)
      · simp only [Hm, mem_filter, mem_univ, true_and]; exact hx.1
      · simp only [Cf, mem_filter, mem_univ, true_and]; exact fun h => hinj h.1
  · omega

/-- Every typed configuration yields an `F₀`-hinge on eight vertices. -/
lemma isHinge_of_tcfg {M : Finset (Sym2 (Fin 8))} {q : Fin 8 → Fin 2}
    (hM : IsHinge q F0 mT1 mT2 M) (hMV : vertSet M = univ) {G : SimpleGraph V}
    [DecidableRel G.Adj] {p : V → Fin 2} {u₁ u₂ v₁ v₂ : V}
    {x : V × V × V × V} (hx : IsTCfg M q G p u₁ u₂ v₁ v₂ x) :
    M.image (Sym2.map (cfgVec u₁ u₂ v₁ v₂ x)) ⊆ G.edgeFinset ∧
    IsHinge p F0 {u₁, u₂, v₁} {u₁, u₂, v₂}
      (M.image (Sym2.map (cfgVec u₁ u₂ v₁ v₂ x))) ∧
    (vertSet (M.image (Sym2.map (cfgVec u₁ u₂ v₁ v₂ x)))).card = 8 := by
  obtain ⟨⟨hinj, hadj⟩, hpart⟩ := hx
  set f : Fin 8 ↪ V := ⟨cfgVec u₁ u₂ v₁ v₂ x, hinj⟩
  have himg : M.image (Sym2.map (cfgVec u₁ u₂ v₁ v₂ x)) = M.map f.sym2Map := by
    rw [map_eq_image]; rfl
  refine ⟨fun e he => ?_, ?_, ?_⟩
  · obtain ⟨i, j, hij, rfl⟩ := mem_image_sym2_map.mp he
    simpa using hadj i j hij
  · have h1 : mT1.map f = {u₁, u₂, v₁} := by simp [mT1, f, cfgVec]
    have h2 : mT2.map f = {u₁, u₂, v₂} := by simp [mT2, f, cfgVec]
    rw [himg, ← h1, ← h2]
    exact isHinge_map_typed f (fun w => hpart w) hM
  · rw [himg, vertSet_map, hMV, card_map, card_univ, Fintype.card_fin]

open Classical in
/-- Distinct typed configurations give distinct `F₀`-hinges. -/
lemma tcfgCount_le_hingeCount {M : Finset (Sym2 (Fin 8))} {q : Fin 8 → Fin 2}
    (hM : IsHinge q F0 mT1 mT2 M) (hMV : vertSet M = univ) (G : SimpleGraph V)
    [DecidableRel G.Adj] (p : V → Fin 2) (u₁ u₂ v₁ v₂ : V)
    (hinj : ∀ x y : V × V × V × V, Function.Injective (cfgVec u₁ u₂ v₁ v₂ x) →
      Function.Injective (cfgVec u₁ u₂ v₁ v₂ y) →
      M.image (Sym2.map (cfgVec u₁ u₂ v₁ v₂ x)) = M.image (Sym2.map (cfgVec u₁ u₂ v₁ v₂ y)) →
      x = y) :
    (tcfgCount M q G p u₁ u₂ v₁ v₂ : ℝ) ≤
      ((G.edgeFinset.powerset.filter (fun H => IsHinge p F0 {u₁, u₂, v₁} {u₁, u₂, v₂} H ∧
        (vertSet H).card = 8)).card : ℝ) := by
  unfold tcfgCount
  exact_mod_cast card_le_card_of_injOn (fun x => M.image (Sym2.map (cfgVec u₁ u₂ v₁ v₂ x)))
    (fun x hx => by
      rw [coe_filter] at hx
      obtain ⟨h1, h2, h3⟩ := isHinge_of_tcfg hM hMV hx.2
      rw [coe_filter]
      exact ⟨mem_powerset.mpr h1, h2, h3⟩)
    (fun x hx y hy hxy => by
      rw [coe_filter] at hx hy
      exact hinj x y hx.2.1.1 hy.2.1.1 hxy)

/-! ### Walks give typed homomorphic copies -/

/-- Walks of length five `u₁ x₁ x₂ x₃ x₄ u₂` in a set `D` of common neighbours of `v₁, v₂`
inside the part `a` give typed homomorphic copies of the type-1 hinge. -/
lemma walk_le_thom1 (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2)
    {u₁ u₂ v₁ v₂ : V} {a b : Fin 2} (D : Finset V)
    (hD : ∀ x ∈ D, G.Adj v₁ x ∧ G.Adj v₂ x ∧ p x = a)
    (hu₁ : p u₁ = a) (hu₂ : p u₂ = a) (hv₁ : p v₁ = b) (hv₂ : p v₂ = b) :
    ∑ d ∈ nbIn G D u₂, walk4 G D u₁ d ≤ thomCount mH1 (q1 a b) G p u₁ u₂ v₁ v₂ := by
  unfold walk4 thomCount
  refine sum4_le_card (nbIn G D u₂) (fun _ => nbIn G D u₁) (fun d _ => nbIn G D d)
    (fun _ a c => nbIn G D a ∩ nbIn G D c) _ (fun d a c b => (a, b, c, d)) ?_ ?_
  · intro d hd x hx c hc y hy
    rw [mem_nbIn] at hd hx hc
    rw [mem_inter, mem_nbIn, mem_nbIn] at hy
    have mN : ∀ {z}, z ∈ D → G.Adj v₁ z ∧ G.Adj v₂ z := fun hz => ⟨(hD _ hz).1, (hD _ hz).2.1⟩
    rw [mem_filter]
    refine ⟨mem_univ _, hom_mH1_of G (mN hx.1) (mN hy.1.1) (mN hc.1) (mN hd.1) hx.2 hy.1.2
      (SimpleGraph.Adj.symm hy.2.2) (SimpleGraph.Adj.symm hc.2) hd.2.symm, ?_⟩
    have px := (hD _ hx.1).2.2
    have py := (hD _ hy.1.1).2.2
    have pc := (hD _ hc.1).2.2
    have pd := (hD _ hd.1).2.2
    intro i
    fin_cases i <;> simp [cfgVec, q1, *]
  · intro d a c b d' a' c' b' h
    simp only [Prod.mk.injEq] at h
    tauto

/-- Walks `v₁ a b c v₂` inside `D w ⊆ N(w) ∩ N(u₂) ∩ V_b`, for `w ∈ L ⊆ N(u₁) ∩ N(v₁) ∩ N(v₂) ∩
V_a`, give typed homomorphic copies of the type-2 hinge. -/
lemma walk_le_thom2 (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2)
    {u₁ u₂ v₁ v₂ : V} {a b : Fin 2} (L : Finset V) (D : V → Finset V)
    (hL : ∀ w ∈ L, G.Adj w u₁ ∧ G.Adj w v₁ ∧ G.Adj w v₂ ∧ p w = a)
    (hD : ∀ w ∈ L, ∀ y ∈ D w, G.Adj w y ∧ G.Adj u₂ y ∧ p y = b)
    (hu₁ : p u₁ = a) (hu₂ : p u₂ = a) (hv₁ : p v₁ = b) (hv₂ : p v₂ = b) :
    ∑ w ∈ L, walk4 G (D w) v₁ v₂ ≤ thomCount mH2 (q2 a b) G p u₁ u₂ v₁ v₂ := by
  unfold walk4 thomCount
  refine sum4_le_card L (fun w => nbIn G (D w) v₁) (fun w _ => nbIn G (D w) v₂)
    (fun w a c => nbIn G (D w) a ∩ nbIn G (D w) c) _ (fun w a c b => (w, a, b, c)) ?_ ?_
  · intro w hw x hx c hc y hy
    rw [mem_nbIn] at hx hc
    rw [mem_inter, mem_nbIn, mem_nbIn] at hy
    obtain ⟨w1, w2, w3, pw⟩ := hL w hw
    rw [mem_filter]
    refine ⟨mem_univ _, hom_mH2_of G w1 w2 w3 (hD w hw x hx.1).1 (hD w hw y hy.1.1).1
      (hD w hw c hc.1).1 (hD w hw x hx.1).2.1 (hD w hw y hy.1.1).2.1 (hD w hw c hc.1).2.1 hx.2
      hy.1.2 (SimpleGraph.Adj.symm hy.2.2) (SimpleGraph.Adj.symm hc.2), ?_⟩
    have px := (hD w hw x hx.1).2.2
    have py := (hD w hw y hy.1.1).2.2
    have pc := (hD w hw c hc.1).2.2
    intro i
    fin_cases i <;> simp [cfgVec, q2, *]
  · intro d a c b d' a' c' b' h
    simp only [Prod.mk.injEq] at h
    tauto

/-! ### Six-vertex hinges -/

/-- The six vertices `u₁, u₂, v₁, v₂, x, y`. -/
def vec6 (u₁ u₂ v₁ v₂ x y : V) : Fin 6 → V := ![u₁, u₂, v₁, v₂, x, y]

omit [Fintype V] in
lemma mem_image_sym2_map6 {M : Finset (Sym2 (Fin 6))} {g : Fin 6 → V} {z : Sym2 V} :
    z ∈ M.image (Sym2.map g) ↔ ∃ i j, s(i, j) ∈ M ∧ z = s(g i, g j) := by
  constructor
  · intro h
    obtain ⟨e, he, rfl⟩ := mem_image.mp h
    induction e using Sym2.ind with
    | _ i j => exact ⟨i, j, he, rfl⟩
  · rintro ⟨i, j, h, rfl⟩
    exact mem_image.mpr ⟨s(i, j), h, rfl⟩

lemma mH6_cases (i j : Fin 6) (h : s(i, j) ∈ mH6) :
    (i, j) ∈ ([(0, 4), (4, 0), (1, 5), (5, 1), (2, 4), (4, 2), (2, 5), (5, 2), (3, 4), (4, 3),
      (3, 5), (5, 3), (4, 5), (5, 4)] : List (Fin 6 × Fin 6)) := by
  revert i j h; decide +kernel

lemma mH6_nb0 (j : Fin 6) (h : s(0, j) ∈ mH6) : j = 4 := by revert j h; decide +kernel
lemma mH6_nb1 (j : Fin 6) (h : s(1, j) ∈ mH6) : j = 5 := by revert j h; decide +kernel

/-- An admissible pair `(x, y)` (all six vertices distinct, `x ~ u₁, v₁, v₂, y`,
`y ~ u₂, v₁, v₂`, and the six triangles of the two decompositions are `F₀`-copies) gives an
`F₀`-hinge on six vertices. -/
lemma isHinge6_of (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2)
    {u₁ u₂ v₁ v₂ x y : V} (hinj : Function.Injective (vec6 u₁ u₂ v₁ v₂ x y))
    (a1 : G.Adj u₁ x) (a2 : G.Adj u₂ y) (a3 : G.Adj v₁ x) (a4 : G.Adj v₁ y) (a5 : G.Adj v₂ x)
    (a6 : G.Adj v₂ y) (a7 : G.Adj x y)
    (h1 : ¬ (p v₁ = p u₁ ∧ p u₁ = p x)) (h2 : ¬ (p v₁ = p u₂ ∧ p u₂ = p y))
    (h3 : ¬ (p v₂ = p x ∧ p x = p y)) (h4 : ¬ (p v₂ = p u₁ ∧ p u₁ = p x))
    (h5 : ¬ (p v₂ = p u₂ ∧ p u₂ = p y)) (h6 : ¬ (p v₁ = p x ∧ p x = p y)) :
    mH6.image (Sym2.map (vec6 u₁ u₂ v₁ v₂ x y)) ⊆ G.edgeFinset ∧
    IsHinge p F0 {u₁, u₂, v₁} {u₁, u₂, v₂} (mH6.image (Sym2.map (vec6 u₁ u₂ v₁ v₂ x y))) ∧
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
    refine isHinge_map_typed f (q := q6 (p u₁) (p u₂) (p v₁) (p v₂) (p x) (p y)) ?_
      (model_hinge6_F0 _ _ _ _ _ _ h1 h2 h3 h4 h5 h6)
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

omit [Fintype V] in
/-- The six-vertex hinge determines the pair `(x, y)`. -/
lemma vec6_pair_eq {u₁ u₂ v₁ v₂ x y x' y' : V}
    (hinj' : Function.Injective (vec6 u₁ u₂ v₁ v₂ x' y'))
    (h : mH6.image (Sym2.map (vec6 u₁ u₂ v₁ v₂ x y)) =
      mH6.image (Sym2.map (vec6 u₁ u₂ v₁ v₂ x' y'))) : x = x' ∧ y = y' := by
  have key : ∀ (k m : Fin 6), (∀ j, s(k, j) ∈ mH6 → j = m) → s(k, m) ∈ mH6 →
      vec6 u₁ u₂ v₁ v₂ x y m = vec6 u₁ u₂ v₁ v₂ x' y' m ∨
        vec6 u₁ u₂ v₁ v₂ x y k ≠ vec6 u₁ u₂ v₁ v₂ x' y' k := by
    intro k m hk hkm
    by_cases hkk : vec6 u₁ u₂ v₁ v₂ x y k = vec6 u₁ u₂ v₁ v₂ x' y' k
    · left
      have hmem : s(vec6 u₁ u₂ v₁ v₂ x y k, vec6 u₁ u₂ v₁ v₂ x y m) ∈
          mH6.image (Sym2.map (vec6 u₁ u₂ v₁ v₂ x' y')) := by
        rw [← h]; exact mem_image_sym2_map6.mpr ⟨k, m, hkm, rfl⟩
      obtain ⟨i, j, hij, he⟩ := mem_image_sym2_map6.mp hmem
      rw [hkk] at he
      rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have := hinj' h1; subst this
        rw [h2, hk j hij]
      · have := hinj' h1; subst this
        rw [Sym2.eq_swap] at hij
        rw [h2, hk i hij]
    · right; exact hkk
  have hx := key 0 4 mH6_nb0 (by decide +kernel)
  have hy := key 1 5 mH6_nb1 (by decide +kernel)
  simp only [vec6, Matrix.cons_val, ne_eq, not_true_eq_false, or_false] at hx hy
  exact ⟨hx, hy⟩

open Classical in
/-- A set of admissible pairs gives as many six-vertex `F₀`-hinges. -/
lemma pairs_le_hingeCount6 (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2)
    (u₁ u₂ v₁ v₂ : V) (P : Finset (V × V))
    (hP : ∀ z ∈ P, Function.Injective (vec6 u₁ u₂ v₁ v₂ z.1 z.2) ∧
      G.Adj u₁ z.1 ∧ G.Adj u₂ z.2 ∧ G.Adj v₁ z.1 ∧ G.Adj v₁ z.2 ∧ G.Adj v₂ z.1 ∧
      G.Adj v₂ z.2 ∧ G.Adj z.1 z.2 ∧
      ¬ (p v₁ = p u₁ ∧ p u₁ = p z.1) ∧ ¬ (p v₁ = p u₂ ∧ p u₂ = p z.2) ∧
      ¬ (p v₂ = p z.1 ∧ p z.1 = p z.2) ∧ ¬ (p v₂ = p u₁ ∧ p u₁ = p z.1) ∧
      ¬ (p v₂ = p u₂ ∧ p u₂ = p z.2) ∧ ¬ (p v₁ = p z.1 ∧ p z.1 = p z.2)) :
    (P.card : ℝ) ≤
      ((G.edgeFinset.powerset.filter (fun H => IsHinge p F0 {u₁, u₂, v₁} {u₁, u₂, v₂} H ∧
        (vertSet H).card = 6)).card : ℝ) := by
  exact_mod_cast card_le_card_of_injOn (fun z : V × V => mH6.image (Sym2.map (vec6 u₁ u₂ v₁ v₂ z.1 z.2)))
    (fun z hz => by
      obtain ⟨hi, a1, a2, a3, a4, a5, a6, a7, h1, h2, h3, h4, h5, h6⟩ := hP z hz
      obtain ⟨e1, e2, e3⟩ := isHinge6_of G p hi a1 a2 a3 a4 a5 a6 a7 h1 h2 h3 h4 h5 h6
      rw [coe_filter]
      exact ⟨mem_powerset.mpr e1, e2, e3⟩)
    (fun z hz w hw hzw => by
      obtain ⟨h1, h2⟩ := vec6_pair_eq (hP w hw).1 hzw
      exact Prod.ext h1 h2)

end NashWilliams18
