/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case125.Residual
import RequestProject.NW18.Sampling.Glue

/-!
# Max-cut bipartitions and Lemma 15.6

* `exists_maxcut_partition`: a bipartition maximising `e(V₁, V₂)`; for it the graph is
  `β`-extremal as a 2-partitioned graph whenever it is `β`-extremal (Definition 12.2), and
  `IntDeg(v) ≤ CrossDeg(v)` for every vertex (first paragraph of the proof of Theorem 12.5).
* `lemma_15_6`: properties of an extremal 2-partitioned graph with `δ(G) ≥ 3n/4`.
  In (b) we prove the lower bound `CrossDeg(v) ≥ (1/2 − 2√γ) n`; the printed bound
  `(1/2 − γ) n` does not follow from the argument (and is not needed).
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Cut edges -/

/-- The edges of the cut `(T, V ∖ T)`. -/
def cutEdges (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => ∃ u v, e = s(u, v) ∧ u ∈ T ∧ v ∉ T)

lemma cutSize_eq_card_cutEdges (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) :
    cutSize G T = (cutEdges G T).card := rfl

lemma mem_cutEdges_mk (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) (x y : V) :
    s(x, y) ∈ cutEdges G T ↔ G.Adj x y ∧ (x ∈ T ↔ y ∉ T) := by
  simp only [cutEdges, mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  constructor
  · rintro ⟨h, u, v, he, hu, hv⟩
    refine ⟨h, ?_⟩
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨fun _ => hv, fun _ => hu⟩
    · exact ⟨fun h' => absurd h' hv, fun h' => absurd hu h'⟩
  · rintro ⟨h, hiff⟩
    refine ⟨h, ?_⟩
    by_cases hx : x ∈ T
    · exact ⟨x, y, rfl, hx, hiff.mp hx⟩
    · have hy : y ∈ T := by by_contra hy; exact hx (hiff.mpr hy)
      exact ⟨y, x, Sym2.eq_swap, hy, hx⟩

lemma card_cutEdges_at (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) (v : V) :
    ((cutEdges G T).filter (fun e => v ∈ e)).card =
      (univ.filter (fun w => G.Adj v w ∧ (w ∈ T ↔ v ∉ T))).card := by
  symm
  refine card_bij (fun w _ => s(v, w)) ?_ ?_ ?_
  · intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw
    refine mem_filter.mpr ⟨(mem_cutEdges_mk G T v w).mpr ⟨hw.1, ?_⟩, Sym2.mem_mk_left _ _⟩
    have := hw.2; tauto
  · intro w _ w' _ h
    rcases Sym2.eq_iff.mp h with ⟨_, h'⟩ | ⟨h1, h2⟩
    · exact h'
    · exact h2.trans h1
  · intro e he
    obtain ⟨heC, hve⟩ := mem_filter.mp he
    induction e using Sym2.ind with
    | _ x y =>
      rcases Sym2.mem_iff.mp hve with rfl | rfl
      · obtain ⟨hadj, hiff⟩ := (mem_cutEdges_mk G T _ y).mp heC
        refine ⟨y, ?_, rfl⟩
        simp only [mem_filter, mem_univ, true_and]
        exact ⟨hadj, by tauto⟩
      · obtain ⟨hadj, hiff⟩ := (mem_cutEdges_mk G T x _).mp heC
        refine ⟨x, ?_, Sym2.eq_swap⟩
        simp only [mem_filter, mem_univ, true_and]
        exact ⟨hadj.symm, hiff⟩

lemma cutEdges_filter_not_mem (G : SimpleGraph V) [DecidableRel G.Adj] {T T' : Finset V} {v : V}
    (h : ∀ x, x ≠ v → (x ∈ T ↔ x ∈ T')) :
    (cutEdges G T).filter (fun e => v ∉ e) = (cutEdges G T').filter (fun e => v ∉ e) := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [mem_filter, mem_cutEdges_mk, Sym2.mem_iff, not_or]
    constructor
    · rintro ⟨⟨ha, hi⟩, hx, hy⟩
      refine ⟨⟨ha, ?_⟩, hx, hy⟩
      rw [← h x (Ne.symm hx), ← h y (Ne.symm hy)]; exact hi
    · rintro ⟨⟨ha, hi⟩, hx, hy⟩
      refine ⟨⟨ha, ?_⟩, hx, hy⟩
      rw [h x (Ne.symm hx), h y (Ne.symm hy)]; exact hi

lemma cutSize_split (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) (v : V) :
    cutSize G T = ((cutEdges G T).filter (fun e => v ∉ e)).card +
      (univ.filter (fun w => G.Adj v w ∧ (w ∈ T ↔ v ∉ T))).card := by
  rw [← card_cutEdges_at, cutSize_eq_card_cutEdges, add_comm]
  exact (card_filter_add_card_filter_not _).symm

/-- A max-cut bipartition. -/
theorem exists_maxcut_partition (G : SimpleGraph V) [DecidableRel G.Adj] {β : ℝ}
    (hβ : IsExtremal β G) :
    ∃ p : V → Fin 2, IsTwoExtremal β G p ∧
      ∀ v i, i ≠ p v → partDeg G p v (p v) ≤ partDeg G p v i := by
  obtain ⟨S, -, hS⟩ := exists_max_image (univ : Finset (Finset V)) (cutSize G) univ_nonempty
  set p : V → Fin 2 := fun v => if v ∈ S then 0 else 1 with hpdef
  have hcl : partClass p 0 = S := by
    ext v; simp only [partClass, mem_filter, mem_univ, true_and, hpdef]
    by_cases hv : v ∈ S <;> simp [hv]
  have hpd0 : ∀ v, partDeg G p v 0 = (univ.filter (fun w => G.Adj v w ∧ w ∈ S)).card := by
    intro v; unfold partDeg; congr 1; ext w
    simp only [mem_filter, mem_univ, true_and, hpdef]
    by_cases hw : w ∈ S <;> simp [hw]
  have hpd1 : ∀ v, partDeg G p v 1 = (univ.filter (fun w => G.Adj v w ∧ w ∉ S)).card := by
    intro v; unfold partDeg; congr 1; ext w
    simp only [mem_filter, mem_univ, true_and, hpdef]
    by_cases hw : w ∈ S <;> simp [hw]
  refine ⟨p, ⟨hβ.1, ?_⟩, fun v i hi => ?_⟩
  · obtain ⟨S', hS'⟩ := hβ.2
    rw [hcl]
    exact hS'.trans (by exact_mod_cast hS S' (mem_univ _))
  · by_cases hv : v ∈ S
    · -- move `v` out of `S`
      have hpv : p v = 0 := by simp [hpdef, hv]
      have hi1 : i = 1 := by
        rcases fin2_cases i with h | h
        · exact absurd (h.trans hpv.symm) hi
        · exact h
      rw [hpv, hi1, hpd0, hpd1]
      have hmax := hS (S.erase v) (mem_univ _)
      rw [cutSize_split G S v, cutSize_split G (S.erase v) v,
        cutEdges_filter_not_mem G (T := S.erase v) (T' := S) (v := v)
          (fun x hx => by simp [hx])] at hmax
      have e1 : univ.filter (fun w => G.Adj v w ∧ (w ∈ S.erase v ↔ v ∉ S.erase v)) =
          univ.filter (fun w => G.Adj v w ∧ w ∈ S) := by
        ext w; simp only [mem_filter, mem_univ, true_and, mem_erase, ne_eq, not_true_eq_false,
          false_and, not_false_eq_true, iff_true]
        constructor
        · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, (G.ne_of_adj h1).symm, h2⟩
      have e2 : univ.filter (fun w => G.Adj v w ∧ (w ∈ S ↔ v ∉ S)) =
          univ.filter (fun w => G.Adj v w ∧ w ∉ S) := by
        ext w; simp only [mem_filter, mem_univ, true_and, hv, not_true_eq_false, iff_false]
      rw [e1, e2] at hmax
      omega
    · -- move `v` into `S`
      have hpv : p v = 1 := by simp [hpdef, hv]
      have hi0 : i = 0 := by
        rcases fin2_cases i with h | h
        · exact h
        · exact absurd (h.trans hpv.symm) hi
      rw [hpv, hi0, hpd0, hpd1]
      have hmax := hS (insert v S) (mem_univ _)
      rw [cutSize_split G S v, cutSize_split G (insert v S) v,
        cutEdges_filter_not_mem G (T := insert v S) (T' := S) (v := v)
          (fun x hx => by simp [hx])] at hmax
      have e1 : univ.filter (fun w => G.Adj v w ∧ (w ∈ insert v S ↔ v ∉ insert v S)) =
          univ.filter (fun w => G.Adj v w ∧ w ∉ S) := by
        ext w; simp only [mem_filter, mem_univ, true_and, mem_insert, true_or,
          not_true_eq_false, iff_false, not_or]
        constructor
        · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, (G.ne_of_adj h1).symm, h2⟩
      have e2 : univ.filter (fun w => G.Adj v w ∧ (w ∈ S ↔ v ∉ S)) =
          univ.filter (fun w => G.Adj v w ∧ w ∈ S) := by
        ext w; simp only [mem_filter, mem_univ, true_and, hv, not_false_eq_true, iff_true]
      rw [e1, e2] at hmax
      omega

omit [Fintype V] in
lemma sum_card_filter_mem (U : Finset V) (E : Finset (Sym2 V)) :
    ∑ v ∈ U, (E.filter (fun e => v ∈ e)).card = ∑ e ∈ E, (U.filter (fun v => v ∈ e)).card := by
  simp only [card_filter]
  exact sum_comm

lemma cut_endpoint_card (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) {e : Sym2 V}
    (he : e ∈ cutEdges G T) :
    (T.filter (fun v => v ∈ e)).card = 1 ∧ ((univ \ T).filter (fun v => v ∈ e)).card = 1 := by
  simp only [cutEdges, mem_filter] at he
  obtain ⟨-, u, w, rfl, hu, hw⟩ := he
  have huw : u ≠ w := fun h => hw (h ▸ hu)
  constructor
  · rw [card_eq_one]; refine ⟨u, ?_⟩
    ext x; simp only [mem_filter, Sym2.mem_iff, mem_singleton]
    constructor
    · rintro ⟨hx, rfl | rfl⟩
      · rfl
      · exact absurd hx hw
    · rintro rfl; exact ⟨hu, Or.inl rfl⟩
  · rw [card_eq_one]; refine ⟨w, ?_⟩
    ext x; simp only [mem_filter, mem_sdiff, mem_univ, true_and, Sym2.mem_iff, mem_singleton]
    constructor
    · rintro ⟨hx, rfl | rfl⟩
      · exact absurd hu hx
      · rfl
    · rintro rfl; exact ⟨hw, Or.inr rfl⟩

/-- `e(V₀, V₁) = ∑_{v ∈ V₀} d₁(v) = ∑_{v ∈ V₁} d₀(v)`. -/
lemma cutSize_eq_sum_partDeg (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2) :
    cutSize G (partClass p 0) = ∑ v ∈ partClass p 0, partDeg G p v 1 ∧
    cutSize G (partClass p 0) = ∑ v ∈ partClass p 1, partDeg G p v 0 := by
  set T := partClass p 0
  have hT1 : partClass p 1 = univ \ T := by
    ext v; simp only [T, partClass, mem_filter, mem_univ, true_and, mem_sdiff]
    rcases fin2_cases (p v) with h | h <;> simp [h]
  have hat : ∀ v, ((cutEdges G T).filter (fun e => v ∈ e)).card =
      (univ.filter (fun w => G.Adj v w ∧ (w ∈ T ↔ v ∉ T))).card := card_cutEdges_at G T
  constructor
  · rw [cutSize_eq_card_cutEdges]
    have h1 : ∑ v ∈ T, ((cutEdges G T).filter (fun e => v ∈ e)).card = (cutEdges G T).card := by
      rw [sum_card_filter_mem, card_eq_sum_ones]
      exact sum_congr rfl fun e he => (cut_endpoint_card G T he).1
    rw [← h1]
    refine sum_congr rfl fun v hv => ?_
    rw [hat]; unfold partDeg; congr 1; ext w
    have hpv : p v = 0 := by simpa [T, partClass] using hv
    simp only [mem_filter, mem_univ, true_and, T, partClass, hpv]
    rcases fin2_cases (p w) with h | h <;> simp [h]
  · rw [cutSize_eq_card_cutEdges, hT1]
    have h1 : ∑ v ∈ univ \ T, ((cutEdges G T).filter (fun e => v ∈ e)).card =
        (cutEdges G T).card := by
      rw [sum_card_filter_mem, card_eq_sum_ones]
      exact sum_congr rfl fun e he => (cut_endpoint_card G T he).2
    rw [← h1]
    refine sum_congr rfl fun v hv => ?_
    rw [hat]; unfold partDeg; congr 1; ext w
    have hpv : p v = 1 := by
      rw [← hT1] at hv; simpa [partClass] using hv
    simp only [mem_filter, mem_univ, true_and, T, partClass, hpv]
    rcases fin2_cases (p w) with h | h <;> simp [h]

set_option maxHeartbeats 1600000 in
/-- **Lemma 15.6.** Let `G` be a 2-partitioned graph on `n` vertices with `δ(G) ≥ 3n/4` which
is `γ`-extremal, and `A = {v : IntDeg(v) ≥ (1/4 + 2√γ) n}`.  Then `|A| ≤ 2√γ n`,
(a) `|V_i| ≥ (1 − √γ) n/2`, and (b) every `v ∉ A` has
`(1/4 − √γ) n ≤ IntDeg(v) ≤ (1/4 + 2√γ) n` and `CrossDeg(v) ≥ (1/2 − 2√γ) n`. -/
theorem lemma_15_6 {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 100) (G : SimpleGraph V)
    [DecidableRel G.Adj] (p : V → Fin 2) (hδ : 3 * Fintype.card V ≤ 4 * G.minDegree)
    (hext : IsTwoExtremal γ G p) :
    ((univ.filter (fun v => (1 / 4 + 2 * Real.sqrt γ) * Fintype.card V ≤
        (partDeg G p v (p v) : ℝ))).card : ℝ) ≤ 2 * Real.sqrt γ * Fintype.card V ∧
    (∀ i, (1 - Real.sqrt γ) * Fintype.card V / 2 ≤ ((partClass p i).card : ℝ)) ∧
    (∀ v, (partDeg G p v (p v) : ℝ) < (1 / 4 + 2 * Real.sqrt γ) * Fintype.card V →
      (1 / 4 - Real.sqrt γ) * Fintype.card V ≤ (partDeg G p v (p v) : ℝ) ∧
      ∀ i, i ≠ p v → (1 / 2 - 2 * Real.sqrt γ) * Fintype.card V ≤ (partDeg G p v i : ℝ)) := by
  set s := Real.sqrt γ with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s * s = γ := Real.mul_self_sqrt hγ.le
  have hs1 : s ≤ 1 / 10 := by
    rw [hsdef, show (1 / 10 : ℝ) = Real.sqrt (1 / 100) by
      rw [show (1 / 100 : ℝ) = (1 / 10) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hγ1
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  set a : ℝ := ((partClass p 0).card : ℝ)
  set b : ℝ := ((partClass p 1).card : ℝ)
  have hab : a + b = n := by
    have := card_partClass_add p
    simp only [a, b, hndef]; exact_mod_cast this
  obtain ⟨hc0, hc1⟩ := cutSize_eq_sum_partDeg G p
  set c : ℝ := (cutSize G (partClass p 0) : ℝ)
  have hcut := hext.2
  -- `c ≤ a b`
  have hcab : c ≤ a * b := by
    have : cutSize G (partClass p 0) ≤ (partClass p 0).card * (partClass p 1).card := by
      rw [hc0]
      calc ∑ v ∈ partClass p 0, partDeg G p v 1 ≤ ∑ _v ∈ partClass p 0, (partClass p 1).card :=
            sum_le_sum fun v _ => partDeg_le_card_partClass G p v 1
        _ = _ := by rw [sum_const, smul_eq_mul]
    simp only [c, a, b]; exact_mod_cast this
  -- (a)
  have hsq : (a - n / 2) ^ 2 ≤ (s * n / 2) ^ 2 := by
    have : a * b = n ^ 2 / 4 - (a - n / 2) ^ 2 := by rw [← hab]; ring
    have h2 : (s * n / 2) ^ 2 = γ * n ^ 2 / 4 := by rw [← hss]; ring
    nlinarith
  have habs : |a - n / 2| ≤ s * n / 2 := abs_le_of_sq_le_sq' hsq (by positivity) |> fun h =>
    abs_le.mpr ⟨h.1, h.2⟩
  have ha : (1 - s) * n / 2 ≤ a := by have := (abs_le.mp habs).1; linarith
  have hb : (1 - s) * n / 2 ≤ b := by have := (abs_le.mp habs).2; linarith
  have hpart : ∀ i, (1 - s) * n / 2 ≤ ((partClass p i).card : ℝ) := by
    intro i; rcases fin2_cases i with rfl | rfl
    · exact ha
    · exact hb
  -- degrees
  have hdeg : ∀ v, (3 / 4) * n ≤ (partDeg G p v 0 : ℝ) + partDeg G p v 1 := by
    intro v
    have h1 : (partDeg G p v 0 : ℝ) + partDeg G p v 1 = G.degree v := by
      exact_mod_cast partDeg_add_partDeg G p v
    have h2 : (G.minDegree : ℝ) ≤ G.degree v := by exact_mod_cast G.minDegree_le_degree v
    have h3 : (3 : ℝ) * n ≤ 4 * G.minDegree := by simp only [hndef]; exact_mod_cast hδ
    linarith
  have hpdle : ∀ v i, (partDeg G p v i : ℝ) ≤ ((partClass p i).card : ℝ) := fun v i => by
    exact_mod_cast partDeg_le_card_partClass G p v i
  refine ⟨?_, hpart, fun v hv => ?_⟩
  · -- `|A| ≤ 2 s n`
    set A := univ.filter (fun v => (1 / 4 + 2 * s) * n ≤ (partDeg G p v (p v) : ℝ))
    set B := univ.filter (fun v => ¬ (G.degree v : ℝ) ≤ (3 / 4 + γ) * n)
    have hB : (B.card : ℝ) ≤ γ * n := by
      have h1 := hext.1
      have h2 := card_filter_add_card_filter_not (s := (univ : Finset V))
        (fun v => (G.degree v : ℝ) ≤ (3 / 4 + γ) * n)
      rw [card_univ] at h2
      have h2' : ((univ.filter (fun v => (G.degree v : ℝ) ≤ (3 / 4 + γ) * n)).card : ℝ) +
          B.card = n := by simp only [B, hndef]; exact_mod_cast h2
      linarith
    -- vertices of `A ∖ B` in each part miss at least `s n` vertices of the other part
    have hmiss : ∀ v ∈ A \ B, ∀ i, i ≠ p v →
        s * n ≤ ((partClass p i).card : ℝ) - partDeg G p v i := by
      intro v hv i hi
      simp only [A, B, mem_sdiff, mem_filter, mem_univ, true_and, not_not] at hv
      have h1 : (partDeg G p v 0 : ℝ) + partDeg G p v 1 = G.degree v := by
        exact_mod_cast partDeg_add_partDeg G p v
      have hcl := hpart i
      have hγs : γ ≤ s / 2 := by rw [← hss]; nlinarith
      rcases fin2_cases (p v) with h | h <;> rcases fin2_cases i with h' | h'
      · exact absurd (h'.trans h.symm) hi
      · rw [h] at hv; rw [h']; rw [h'] at hcl; nlinarith
      · rw [h] at hv; rw [h']; rw [h'] at hcl; nlinarith
      · exact absurd (h'.trans h.symm) hi
    set W0 := (A \ B).filter (fun v => p v = 0)
    set W1 := (A \ B).filter (fun v => p v = 1)
    have hW : (A \ B).card = W0.card + W1.card := by
      rw [← card_union_of_disjoint]
      · congr 1; ext v; simp only [W0, W1, mem_union, mem_filter]
        rcases fin2_cases (p v) with h | h <;> simp [h]
      · exact disjoint_filter.mpr fun v _ h1 h2 => by rw [h1] at h2; exact absurd h2 (by decide)
    have hW0 : (W0.card : ℝ) * (s * n) ≤ a * b - c := by
      have e1 : (W0.card : ℝ) * (s * n) ≤ ∑ v ∈ W0, (b - partDeg G p v 1) := by
        rw [← nsmul_eq_mul, ← sum_const]
        refine sum_le_sum fun v hv => ?_
        simp only [W0, mem_filter] at hv
        exact hmiss v hv.1 1 (by rw [hv.2]; decide)
      have e2 : ∑ v ∈ W0, (b - partDeg G p v 1) ≤ ∑ v ∈ partClass p 0, (b - partDeg G p v 1) := by
        refine sum_le_sum_of_subset_of_nonneg (fun v hv => ?_) fun v _ _ => ?_
        · simp only [W0, mem_filter] at hv
          simp [partClass, hv.2]
        · have := hpdle v 1; linarith
      have e3 : ∑ v ∈ partClass p 0, (b - partDeg G p v 1) = a * b - c := by
        rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
        simp only [c, hc0]; push_cast; ring
      linarith
    have hW1 : (W1.card : ℝ) * (s * n) ≤ a * b - c := by
      have e1 : (W1.card : ℝ) * (s * n) ≤ ∑ v ∈ W1, (a - partDeg G p v 0) := by
        rw [← nsmul_eq_mul, ← sum_const]
        refine sum_le_sum fun v hv => ?_
        simp only [W1, mem_filter] at hv
        exact hmiss v hv.1 0 (by rw [hv.2]; decide)
      have e2 : ∑ v ∈ W1, (a - partDeg G p v 0) ≤ ∑ v ∈ partClass p 1, (a - partDeg G p v 0) := by
        refine sum_le_sum_of_subset_of_nonneg (fun v hv => ?_) fun v _ _ => ?_
        · simp only [W1, mem_filter] at hv
          simp [partClass, hv.2]
        · have := hpdle v 0; linarith
      have e3 : ∑ v ∈ partClass p 1, (a - partDeg G p v 0) = b * a - c := by
        rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
        simp only [c, hc1]; push_cast; ring
      linarith
    have habc : a * b - c ≤ γ * n ^ 2 / 4 := by
      have : a * b ≤ n ^ 2 / 4 := by nlinarith [sq_nonneg (a - b)]
      linarith
    have hAB : (A.card : ℝ) ≤ (A \ B).card + B.card := by
      have := card_le_card_sdiff_add_card (s := A) (t := B)
      exact_mod_cast this
    have hW' : ((A \ B).card : ℝ) * (s * n) ≤ γ * n ^ 2 / 2 := by
      have : ((A \ B).card : ℝ) = W0.card + W1.card := by exact_mod_cast hW
      rw [this, add_mul]; linarith
    have hspos : 0 < s := Real.sqrt_pos.mpr hγ
    rcases eq_or_lt_of_le hn0 with hn | hn
    · have hA0 : (A.card : ℝ) ≤ n := by
        have := card_le_univ A
        simp only [hndef]; exact_mod_cast this
      rw [← hn] at hA0 ⊢; linarith
    · have hsnpos : 0 < s * n := mul_pos hspos hn
      have hAB' : ((A \ B).card : ℝ) ≤ s * n / 2 := by
        have h' : ((A \ B).card : ℝ) * (s * n) ≤ (s * n / 2) * (s * n) := by
          have : γ * n ^ 2 / 2 = (s * n / 2) * (s * n) := by rw [← hss]; ring
          linarith
        exact le_of_mul_le_mul_right h' hsnpos
      have hγs : γ * n ≤ s * n := by
        have : γ ≤ s := by rw [← hss]; nlinarith
        exact mul_le_mul_of_nonneg_right this hn0
      linarith
  · -- (b)
    have hd := hdeg v
    constructor
    · rcases fin2_cases (p v) with h | h <;> rw [h] at hv ⊢
      · have := hpdle v 1; linarith
      · have := hpdle v 0; linarith
    · intro i hi
      rcases fin2_cases (p v) with h | h <;> rcases fin2_cases i with h' | h'
      · exact absurd (h'.trans h.symm) hi
      · rw [h] at hv; rw [h']; linarith
      · rw [h] at hv; rw [h']; linarith
      · exact absurd (h'.trans h.symm) hi

end NashWilliams18
