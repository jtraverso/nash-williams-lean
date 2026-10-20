/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case125.LinkPairing
import RequestProject.NW18.Case125.Cleaning

/-!
# One step of Claim 15.9.4: decomposing the remaining edges at one oddball

Given a set `U` of already used edges, the edges at a vertex `z` not yet used are decomposed
into triangles `{z, x, y}` whose third edge `xy` is also unused (this is the One Oddball
Cleaning Lemma 15.7 applied to `z`).  The available link of `z` is paired by `link_pairing`;
at most `0.01 n` of the triangles are interior, and none when `IntDeg(z) < 0.371 n`.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The graph of edges of `G` not in `U`. -/
def availGraph (G : SimpleGraph V) (U : Finset (Sym2 V)) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ s(x, y) ∉ U
  symm := ⟨fun x y h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

instance (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset (Sym2 V)) :
    DecidableRel (availGraph G U).Adj := fun x y =>
  inferInstanceAs (Decidable (G.Adj x y ∧ s(x, y) ∉ U))

omit [Fintype V] [DecidableEq V] in
lemma availGraph_le (G : SimpleGraph V) (U : Finset (Sym2 V)) : availGraph G U ≤ G :=
  fun _ _ h => h.1

omit [Fintype V] in
lemma card_filter_mk_mem_le (U : Finset (Sym2 V)) (x : V) (Y : Finset V) :
    (Y.filter (fun y => s(x, y) ∈ U)).card ≤ (U.filter (fun e => x ∈ e)).card :=
  card_le_card_of_injOn (fun y => s(x, y))
    (fun y hy => by
      simp only [coe_filter, Set.mem_setOf_eq] at hy ⊢
      exact ⟨hy.2, Sym2.mem_mk_left x y⟩)
    (fun y _ y' _ h => Sym2.congr_right.mp h)

lemma partDeg_add_partDeg_ne (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2) (v : V)
    {i : Fin 2} (hi : i ≠ p v) : partDeg G p v (p v) + partDeg G p v i = G.degree v := by
  have h := partDeg_add_partDeg G p v
  rcases fin2_cases (p v) with h1 | h1 <;> rw [h1] at hi ⊢ <;>
    rcases fin2_cases i with h2 | h2 <;> subst h2 <;> first | exact absurd rfl hi | omega

/-- Non-neighbours in the available graph inside a part. -/
lemma nonadj_avail_card (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2)
    (U : Finset (Sym2 V)) (i : Fin 2) (x : V) (Y : Finset V) (hY : Y ⊆ partClass p i) :
    (Y.filter fun y => ¬ (availGraph G U).Adj x y).card + partDeg G p x i ≤
      (partClass p i).card + (U.filter (fun e => x ∈ e)).card := by
  have h1 : Y.filter (fun y => ¬ (availGraph G U).Adj x y) ⊆
      (partClass p i).filter (fun y => ¬ G.Adj x y) ∪ Y.filter (fun y => s(x, y) ∈ U) := by
    intro y hy
    obtain ⟨hyY, hy⟩ := mem_filter.mp hy
    simp only [availGraph, not_and, not_not] at hy
    simp only [mem_union, mem_filter]
    by_cases hxy : G.Adj x y
    · exact Or.inr ⟨hyY, hy hxy⟩
    · exact Or.inl ⟨hY hyY, hxy⟩
  have h2 := card_filter_mk_mem_le U x Y
  have h3 : ((partClass p i).filter (fun y => ¬ G.Adj x y)).card + partDeg G p x i =
      (partClass p i).card := by
    rw [partDeg_eq_card_filter, add_comm]
    exact card_filter_add_card_filter_not _
  have h4 := card_le_card h1
  have h5 := card_union_le ((partClass p i).filter (fun y => ¬ G.Adj x y))
    (Y.filter (fun y => s(x, y) ∈ U))
  omega

omit [Fintype V] in
/-- The edges of a clique of the available graph avoid `U`. -/
lemma triEdges_disjoint_of_avail {G : SimpleGraph V} {U : Finset (Sym2 V)} {t : Finset V}
    (ht : (availGraph G U).IsNClique 3 t) : Disjoint (triEdges t) U := by
  refine disjoint_left.mpr fun e he heU => ?_
  induction e using Sym2.ind with
  | _ a b =>
    obtain ⟨ha, hb, hab⟩ := mk_mem_triEdges.mp he
    exact (ht.1 ha hb hab).2 heU

/-- The available link of `z` has `deg(z) − |U_z|` vertices. -/
lemma card_link_add (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset (Sym2 V))
    (hUG : U ⊆ G.edgeFinset) (z : V) :
    ((G.neighborFinset z).filter (fun w => s(z, w) ∉ U)).card +
      (U.filter (fun e => z ∈ e)).card = G.degree z := by
  have h1 : ((G.neighborFinset z).filter (fun w => s(z, w) ∈ U)).card =
      (U.filter (fun e => z ∈ e)).card := by
    refine card_bij (fun w _ => s(z, w)) (fun w hw => ?_) (fun w _ w' _ h => ?_) (fun e he => ?_)
    · obtain ⟨-, hw⟩ := mem_filter.mp hw
      exact mem_filter.mpr ⟨hw, Sym2.mem_mk_left z w⟩
    · exact Sym2.congr_right.mp h
    · obtain ⟨heU, hze⟩ := mem_filter.mp he
      obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hze
      have hadj : G.Adj z w := SimpleGraph.mem_edgeFinset.mp (hUG heU)
      exact ⟨w, mem_filter.mpr ⟨(G.mem_neighborFinset z w).mpr hadj, heU⟩, rfl⟩
  rw [← h1, add_comm, card_filter_add_card_filter_not, G.card_neighborFinset_eq_degree]

lemma fin2_exists_ne (j : Fin 2) : ∃ i : Fin 2, i ≠ j ∧ ∀ k, k ≠ j → k = i := by
  rcases fin2_cases j with rfl | rfl
  · exact ⟨1, by decide, fun k hk => by rcases fin2_cases k with h | h <;> simp_all⟩
  · exact ⟨0, by decide, fun k hk => by rcases fin2_cases k with h | h <;> simp_all⟩

/-- **One oddball step** (the One Oddball Cleaning Lemma 15.7, in the form used for
Claim 15.9.4).  `U` is the set of used edges, `Astar` the set of vertices of very large internal
degree.  The unused edges at `z` are decomposed into triangles through `z` whose third edge is
unused; every other vertex lies in at most one of them; at most `0.01 n` of them are interior,
none if `IntDeg(z) < 0.371 n`. -/
theorem oddball_step (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2)
    (U : Finset (Sym2 V)) (z : V) (Astar : Finset V) {γ r : ℝ}
    (hr0 : 0 < r) (hr1 : r ≤ 1 / 1000) (hγ : γ = r * r) (hrn : 100 ≤ r * Fintype.card V)
    (hδ : 3 * Fintype.card V ≤ 4 * G.minDegree) (hbal : IsCrossBalanced γ G p)
    (hV : ∀ i, ((partClass p i).card : ℝ) ≤ (1 + r) * Fintype.card V / 2)
    (hnorm : ∀ v, v ∉ Astar → (1 / 4 - r) * Fintype.card V ≤ (partDeg G p v (p v) : ℝ) ∧
      ∀ i, i ≠ p v → (1 / 2 - 2 * r) * Fintype.card V ≤ (partDeg G p v i : ℝ))
    (hAc : (Astar.card : ℝ) ≤ 2 * r * Fintype.card V)
    (hUG : U ⊆ G.edgeFinset) (hdz : Even (G.degree z))
    (hUz : ((U.filter (fun e => z ∈ e)).card : ℝ) ≤ 4 * r * Fintype.card V)
    (hUzev : Even (U.filter (fun e => z ∈ e)).card)
    (hUx : ∀ x, G.Adj z x → s(z, x) ∉ U →
      ((U.filter (fun e => x ∈ e)).card : ℝ) ≤ 5 * r * Fintype.card V) :
    ∃ D : Finset (Finset V),
      (∀ t ∈ D, G.IsNClique 3 t ∧ z ∈ t ∧ Disjoint (triEdges t) U) ∧
      (D : Set (Finset V)).PairwiseDisjoint triEdges ∧
      (∀ w, G.Adj z w → s(z, w) ∉ U → s(z, w) ∈ D.biUnion triEdges) ∧
      (∀ w, w ≠ z → (D.filter (fun t => w ∈ t)).card ≤ 1) ∧
      ((partDeg G p z (p z) : ℝ) < 0.371 * Fintype.card V →
        (D.filter (fun t => IsInteriorTri p t)).card = 0) ∧
      ((D.filter (fun t => IsInteriorTri p t)).card : ℝ) ≤ 0.01 * Fintype.card V := by
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hrn0 : 0 ≤ r * n := by positivity
  have hrn1 : r * n ≤ n / 1000 := by nlinarith
  have hγn : γ * n ≤ r * n / 1000 := by rw [hγ]; nlinarith
  obtain ⟨o, ho, hoo⟩ := fin2_exists_ne (p z)
  have hdeg : ∀ v, 3 * n ≤ 4 * (G.degree v : ℝ) := fun v => by
    have h1 := G.minDegree_le_degree v
    have h2 : 3 * Fintype.card V ≤ 4 * G.degree v := hδ.trans (by omega)
    rw [hndef]; exact_mod_cast h2
  have hsum : ∀ v i, i ≠ p v → (partDeg G p v (p v) : ℝ) + partDeg G p v i = G.degree v :=
    fun v i hi => by exact_mod_cast partDeg_add_partDeg_ne G p v hi
  have hcls : ∀ v i, (partDeg G p v i : ℝ) ≤ (1 + r) * n / 2 := fun v i =>
    (Nat.cast_le.mpr (partDeg_le_card_partClass G p v i)).trans (hV i)
  have hint_all : ∀ v, n / 4 - r * n / 2 ≤ (partDeg G p v (p v) : ℝ) := by
    intro v
    obtain ⟨i, hi, -⟩ := fin2_exists_ne (p v)
    have := hsum v i hi; have := hcls v i; have := hdeg v
    linarith
  have hcross_all : ∀ v i, i ≠ p v → (3 / 4 * n - γ * n) / 2 ≤ (partDeg G p v i : ℝ) := by
    intro v i hi
    have := hbal v i hi; have := hsum v i hi; have := hdeg v
    linarith
  -- the available link and its parts
  set W := (G.neighborFinset z).filter (fun w => s(z, w) ∉ U) with hW
  set P := W.filter (fun w => p w = p z) with hP
  set Q := W.filter (fun w => p w = o) with hQ
  set S := W.filter (fun w => w ∈ Astar) with hS
  set uz := (U.filter (fun e => z ∈ e)).card with huz
  have hmemW : ∀ w, w ∈ W ↔ G.Adj z w ∧ s(z, w) ∉ U := fun w => by
    simp [hW, SimpleGraph.mem_neighborFinset]
  have hPQ : Disjoint P Q :=
    disjoint_filter.mpr fun w _ h1 h2 => ho (h2.symm.trans h1)
  have hPQW : P ∪ Q = W := by
    ext w
    simp only [hP, hQ, mem_union, mem_filter]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact h.1
    · intro h
      by_cases hpw : p w = p z
      · exact Or.inl ⟨h, hpw⟩
      · exact Or.inr ⟨h, hoo _ hpw⟩
  have hWc : P.card + Q.card = W.card := by rw [← card_union_of_disjoint hPQ, hPQW]
  have hSPQ : S ⊆ P ∪ Q := hPQW ▸ filter_subset _ _
  have hSc : (S.card : ℝ) ≤ 2 * r * n :=
    (Nat.cast_le.mpr (card_le_card (show S ⊆ Astar from fun w hw => (mem_filter.mp hw).2))).trans
      hAc
  have hWeven : Even W.card := by
    have h : W.card + uz = G.degree z := card_link_add G U hUG z
    obtain ⟨a, ha⟩ := hdz
    obtain ⟨b, hb⟩ := hUzev
    exact ⟨a - b, by omega⟩
  have hPsub : P ⊆ partClass p (p z) := fun w hw => by
    simp only [partClass, mem_filter, mem_univ, true_and]; exact (mem_filter.mp hw).2
  have hQsub : Q ⊆ partClass p o := fun w hw => by
    simp only [partClass, mem_filter, mem_univ, true_and]; exact (mem_filter.mp hw).2
  have hlink_lo : ∀ (i : Fin 2), ((partClass p i).filter (G.Adj z)).card ≤
      (W.filter (fun w => p w = i)).card + uz := by
    intro i
    have hsub : (partClass p i).filter (G.Adj z) ⊆
        W.filter (fun w => p w = i) ∪ univ.filter (fun w => s(z, w) ∈ U) := by
      intro w hw
      simp only [partClass, mem_filter, mem_univ, true_and] at hw
      by_cases hU : s(z, w) ∈ U
      · exact mem_union_right _ (by simp [hU])
      · exact mem_union_left _ (mem_filter.mpr ⟨(hmemW w).mpr ⟨hw.2, hU⟩, hw.1⟩)
    have h1 := (card_le_card hsub).trans (card_union_le _ _)
    have h2 := card_filter_mk_mem_le U z univ
    omega
  have hPlo : (partDeg G p z (p z) : ℝ) ≤ P.card + uz := by
    have := hlink_lo (p z); rw [← partDeg_eq_card_filter] at this; exact_mod_cast this
  have hQlo : (partDeg G p z o : ℝ) ≤ Q.card + uz := by
    have := hlink_lo o; rw [← partDeg_eq_card_filter] at this; exact_mod_cast this
  have hPhi : (P.card : ℝ) ≤ partDeg G p z (p z) := by
    rw [partDeg_eq_card_filter]
    exact_mod_cast card_le_card fun w hw =>
      mem_filter.mpr ⟨hPsub hw, ((hmemW w).mp (mem_filter.mp hw).1).1⟩
  have hsz := hsum z o ho
  have hbz := hbal z o ho
  have hdz' := hdeg z
  have hcz := hcls z o
  have hczlo := hcross_all z o ho
  have hizlo := hint_all z
  have huzR : (uz : ℝ) ≤ 4 * r * n := hUz
  set e := ⌈8 * r * n⌉₊ with he
  set c := ⌈n / 4 + 7 * r * n⌉₊ with hc
  have he1 : 8 * r * n ≤ (e : ℝ) := Nat.le_ceil _
  have he2 : (e : ℝ) < 8 * r * n + 1 := Nat.ceil_lt_add_one (by positivity)
  have hc1 : n / 4 + 7 * r * n ≤ (c : ℝ) := Nat.le_ceil _
  have hc2 : (c : ℝ) < n / 4 + 7 * r * n + 1 := Nat.ceil_lt_add_one (by positivity)
  have hWx : ∀ x ∈ W, ((U.filter (fun e => x ∈ e)).card : ℝ) ≤ 5 * r * n := fun x hx =>
    hUx x ((hmemW x).mp hx).1 ((hmemW x).mp hx).2
  have hnS : ∀ x ∈ W, x ∉ S → x ∉ Astar := fun x hx hxS h => hxS (mem_filter.mpr ⟨hx, h⟩)
  have hPQe : ∀ x ∈ P \ S, (Q.filter fun y => ¬ (availGraph G U).Adj x y).card ≤ e := by
    intro x hx
    obtain ⟨hxP', hxS⟩ := mem_sdiff.mp hx
    obtain ⟨hxW, hpx⟩ := mem_filter.mp hxP'
    have h1 := nonadj_avail_card G p U o x Q hQsub
    have h2 := hWx x hxW
    have h3 := (hnorm x (hnS x hxW hxS)).2 o (by rw [hpx]; exact ho)
    have h4 := hV o
    have : ((Q.filter fun y => ¬ (availGraph G U).Adj x y).card : ℝ) ≤ e := by
      have h1' : ((Q.filter fun y => ¬ (availGraph G U).Adj x y).card : ℝ) + partDeg G p x o ≤
          (partClass p o).card + (U.filter (fun e => x ∈ e)).card := by exact_mod_cast h1
      linarith
    exact_mod_cast this
  have hQPe : ∀ y ∈ Q \ S, (P.filter fun x => ¬ (availGraph G U).Adj y x).card ≤ e := by
    intro y hy
    obtain ⟨hyQ, hyS⟩ := mem_sdiff.mp hy
    obtain ⟨hyW, hpy⟩ := mem_filter.mp hyQ
    have h1 := nonadj_avail_card G p U (p z) y P hPsub
    have h2 := hWx y hyW
    have h3 := (hnorm y (hnS y hyW hyS)).2 (p z) (by rw [hpy]; exact Ne.symm ho)
    have h4 := hV (p z)
    have : ((P.filter fun x => ¬ (availGraph G U).Adj y x).card : ℝ) ≤ e := by
      have h1' : ((P.filter fun x => ¬ (availGraph G U).Adj y x).card : ℝ) + partDeg G p y (p z) ≤
          (partClass p (p z)).card + (U.filter (fun e => y ∈ e)).card := by exact_mod_cast h1
      linarith
    exact_mod_cast this
  have hPPc : ∀ x ∈ P \ S, (P.filter fun w => ¬ (availGraph G U).Adj x w).card ≤ c := by
    intro x hx
    obtain ⟨hxP', hxS⟩ := mem_sdiff.mp hx
    obtain ⟨hxW, hpx⟩ := mem_filter.mp hxP'
    have h1 := nonadj_avail_card G p U (p z) x P hPsub
    have h2 := hWx x hxW
    have h3 := (hnorm x (hnS x hxW hxS)).1
    rw [hpx] at h3
    have h4 := hV (p z)
    have : ((P.filter fun w => ¬ (availGraph G U).Adj x w).card : ℝ) ≤ c := by
      have h1' : ((P.filter fun w => ¬ (availGraph G U).Adj x w).card : ℝ) + partDeg G p x (p z) ≤
          (partClass p (p z)).card + (U.filter (fun e => x ∈ e)).card := by exact_mod_cast h1
      linarith
    exact_mod_cast this
  have hQQc : ∀ y ∈ Q \ S, (Q.filter fun w => ¬ (availGraph G U).Adj y w).card ≤ c := by
    intro y hy
    obtain ⟨hyQ, hyS⟩ := mem_sdiff.mp hy
    obtain ⟨hyW, hpy⟩ := mem_filter.mp hyQ
    have h1 := nonadj_avail_card G p U o y Q hQsub
    have h2 := hWx y hyW
    have h3 := (hnorm y (hnS y hyW hyS)).1
    rw [hpy] at h3
    have h4 := hV o
    have : ((Q.filter fun w => ¬ (availGraph G U).Adj y w).card : ℝ) ≤ c := by
      have h1' : ((Q.filter fun w => ¬ (availGraph G U).Adj y w).card : ℝ) + partDeg G p y o ≤
          (partClass p o).card + (U.filter (fun e => y ∈ e)).card := by exact_mod_cast h1
      linarith
    exact_mod_cast this
  have hSdeg : ∀ a ∈ S, S.card ≤ ((Q \ S).filter ((availGraph G U).Adj a)).card := by
    intro a ha
    obtain ⟨haW, -⟩ := mem_filter.mp ha
    have h1 := nonadj_avail_card G p U o a Q hQsub
    have h2 := hWx a haW
    have h3 : n / 4 - r * n / 2 ≤ (partDeg G p a o : ℝ) := by
      by_cases hpa : p a = o
      · have := hint_all a; rw [hpa] at this; exact this
      · have := hcross_all a o (Ne.symm hpa); linarith
    have h4 := hV o
    have h5 : Q.filter ((availGraph G U).Adj a) ⊆
        (Q \ S).filter ((availGraph G U).Adj a) ∪ S := by
      intro w hw
      obtain ⟨hwQ, hwa⟩ := mem_filter.mp hw
      by_cases hwS : w ∈ S
      · exact mem_union_right _ hwS
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨hwQ, hwS⟩, hwa⟩)
    have h6 := (card_le_card h5).trans (card_union_le _ _)
    have h7 := card_filter_add_card_filter_not (s := Q) (p := (availGraph G U).Adj a)
    have : (S.card : ℝ) ≤ ((Q \ S).filter ((availGraph G U).Adj a)).card := by
      have h1' : ((Q.filter fun y => ¬ (availGraph G U).Adj a y).card : ℝ) + partDeg G p a o ≤
          (partClass p o).card + (U.filter (fun e => a ∈ e)).card := by exact_mod_cast h1
      have h6' : ((Q.filter ((availGraph G U).Adj a)).card : ℝ) ≤
          ((Q \ S).filter ((availGraph G U).Adj a)).card + S.card := by exact_mod_cast h6
      have h7' : ((Q.filter ((availGraph G U).Adj a)).card : ℝ) +
          (Q.filter fun y => ¬ (availGraph G U).Adj a y).card = Q.card := by exact_mod_cast h7
      linarith
    exact_mod_cast this
  have hPsz : 2 * e + 1 + 2 * S.card ≤ P.card := by
    have : (2 * e + 1 + 2 * S.card : ℝ) ≤ P.card := by linarith
    exact_mod_cast this
  have hQsz : 2 * e + 1 + 2 * S.card ≤ Q.card := by
    have : (2 * e + 1 + 2 * S.card : ℝ) ≤ Q.card := by linarith
    exact_mod_cast this
  have hcsz : 2 * c + 2 * S.card ≤ P.card + Q.card := by
    have : (2 * c + 2 * S.card : ℝ) ≤ P.card + Q.card := by linarith
    exact_mod_cast this
  obtain ⟨M, hM, hMv, hMint⟩ := link_pairing (availGraph G U) P Q S e c hPQ hSPQ
    (hWc ▸ hWeven) hSdeg hPQe hQPe hPPc hQQc hPsz hQsz hcsz
  have hvM : verts M = W := hMv.trans hPQW
  have hzM : ∀ w ∈ verts M, (availGraph G U).Adj z w := fun w hw =>
    (hmemW w).mp (hvM ▸ hw)
  obtain ⟨hcl, hpd, hedges, hzt, hone, -⟩ := starTris_spec (availGraph G U) z M hM hzM
  have hintsub : ((starTris z M).filter (fun t => IsInteriorTri p t)).card ≤
      (M.filter fun q => q.1 ∈ P ∧ q.2 ∈ P).card := by
    have : (starTris z M).filter (fun t => IsInteriorTri p t) ⊆
        (M.filter fun q => q.1 ∈ P ∧ q.2 ∈ P).image (fun q => ({z, q.1, q.2} : Finset V)) := by
      intro t ht
      obtain ⟨htD, i, hi⟩ := mem_filter.mp ht
      obtain ⟨q, hq, rfl⟩ := mem_image.mp htD
      have h1 : q.1 ∈ W := hvM ▸ mem_verts.mpr ⟨q, hq, Or.inl rfl⟩
      have h2 : q.2 ∈ W := hvM ▸ mem_verts.mpr ⟨q, hq, Or.inr rfl⟩
      have hz := hi z (by simp)
      have hq1 := hi q.1 (by simp)
      have hq2 := hi q.2 (by simp)
      exact mem_image.mpr ⟨q, mem_filter.mpr ⟨hq, mem_filter.mpr ⟨h1, hq1.trans hz.symm⟩,
        mem_filter.mpr ⟨h2, hq2.trans hz.symm⟩⟩, rfl⟩
    exact (card_le_card this).trans card_image_le
  refine ⟨starTris z M, fun t ht => ⟨(hcl t ht).mono (availGraph_le G U), hzt t ht,
    triEdges_disjoint_of_avail (hcl t ht)⟩, hpd, fun w hw hwU => ?_, hone, fun hlt => ?_, ?_⟩
  · exact (hedges _).mpr (Or.inl ⟨w, hvM ▸ (hmemW w).mpr ⟨hw, hwU⟩, rfl⟩)
  · have hsm : P.card + 2 * S.card ≤ Q.card := by
      have : (P.card + 2 * S.card : ℝ) ≤ Q.card := by linarith
      exact_mod_cast this
    omega
  · rcases le_or_gt (P.card + 2 * S.card) Q.card with hsm | hbig
    · have : ((starTris z M).filter (fun t => IsInteriorTri p t)).card = 0 := by omega
      rw [this, Nat.cast_zero]; positivity
    · have h2 : 2 * ((starTris z M).filter (fun t => IsInteriorTri p t)).card + Q.card ≤
          P.card + 2 * S.card := by omega
      have h2' : (2 * ((starTris z M).filter (fun t => IsInteriorTri p t)).card + Q.card : ℝ) ≤
          P.card + 2 * S.card := by exact_mod_cast h2
      linarith

end NashWilliams18
