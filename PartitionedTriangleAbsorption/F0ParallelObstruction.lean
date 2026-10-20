/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedLoadPreparation

/-! # A class-level obstruction to the balanced F0 boost

The graph is the complete four-partite graph with classes `0,1` in part `0` and
classes `2,3` in part `1`, of sizes `s 0, s 1, s 2, s 3`. Every triangle uses
three distinct classes, and all of them are F0-copies.

Besides the F0 type functional, the edge function `parZ` (`+1` on the edges
between classes `0,2` and `1,3`, `-1` between `0,3` and `1,2`, zero on internal
edges) vanishes on every triangle of this graph. Its total charge is
`2 (s 0 - s 1)(s 2 - s 3)`. This functional is not a function of the parts:
it is invisible to the global F0 balance and to the vertex-cone faces.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F0ParallelObstruction

open Finset TypedNibble TypedLoadNecessity TypedLoadFamilies TypedApplicationLinks
  TypedLoadCounterexample TypedLoadPreparation

section General

variable (s : Fin 4 → ℕ)

/-- Vertices: a class and an index inside it. -/
abbrev QV := Σ c : Fin 4, Fin (s c)

/-- The class of a vertex. -/
def qcls : QV s → Fin 4 := fun u => u.1

/-- The F0 part of a vertex: classes `0,1` in part `0`, classes `2,3` in part `1`. -/
def qpart : QV s → Fin 2 := fun u => cls u.1

/-- The complete four-partite graph on the classes. -/
def qgraph : SimpleGraph (QV s) where
  Adj u v := u.1 ≠ v.1
  symm := ⟨fun _ _ h => Ne.symm h⟩
  loopless := ⟨fun _ h => h rfl⟩

instance : DecidableRel (qgraph s).Adj :=
  fun u v => inferInstanceAs (Decidable (u.1 ≠ v.1))

variable {s}

theorem card_QV : Fintype.card (QV s) = ∑ c, s c := by
  simp [Fintype.card_sigma]

theorem sum_filter_qcls (P : Fin 4 → Prop) [DecidablePred P] (g : Fin 4 → ℝ) :
    ∑ z ∈ univ.filter (fun z : QV s => P z.1), g z.1 =
      ∑ c ∈ univ.filter P, (s c : ℝ) * g c := by
  have h : univ.filter (fun z : QV s => P z.1) = (univ.filter P).sigma (fun _ => univ) := by
    ext z
    simp
  rw [h, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp

theorem card_filter_qcls (P : Fin 4 → Prop) [DecidablePred P] :
    ((univ.filter (fun z : QV s => P z.1)).card : ℝ) = ∑ c ∈ univ.filter P, (s c : ℝ) := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  have := sum_filter_qcls (s := s) P (fun _ => 1)
  simp only [mul_one] at this
  simpa using this

/-- The four transversal class types. -/
def D4 : Finset (Multiset (Fin 4)) := {{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}}

theorem transversal_mem (a b c : Fin 4) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Multiset (Fin 4)) ∈ D4 := by
  revert a b c
  decide

/-- The parallel-minus-antiparallel functional on class pairs. -/
def parZ : Fin 4 → Fin 4 → ℤ :=
  ![![0, 0, 1, -1], ![0, 0, -1, 1], ![1, -1, 0, 0], ![-1, 1, 0, 0]]

/-- Its absolute value. -/
def parAbs : Fin 4 → Fin 4 → ℤ :=
  ![![0, 0, 1, 1], ![0, 0, 1, 1], ![1, 1, 0, 0], ![1, 1, 0, 0]]

theorem annihilates_D4 : Annihilates D4 parZ := by
  unfold Annihilates pairFun typeEdgeVec
  decide

theorem isCopy_qpart_iff (t : Finset (QV s)) :
    IsCopy (qpart s) F0 (qgraph s) t ↔ (qgraph s).IsNClique 3 t := by
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := SimpleGraph.is3Clique_iff.mp h
  rw [map_three _ ((qgraph s).ne_of_adj hab) ((qgraph s).ne_of_adj hac)
    ((qgraph s).ne_of_adj hbc)]
  exact cls_type_mem a.1 b.1 c.1 hab hac hbc

theorem isCopy_qcls_iff (t : Finset (QV s)) :
    IsCopy (qcls s) D4 (qgraph s) t ↔ (qgraph s).IsNClique 3 t := by
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := SimpleGraph.is3Clique_iff.mp h
  rw [map_three _ ((qgraph s).ne_of_adj hab) ((qgraph s).ne_of_adj hac)
    ((qgraph s).ne_of_adj hbc)]
  exact transversal_mem a.1 b.1 c.1 hab hac hbc

theorem copies_qpart_eq : copies (qpart s) F0 (qgraph s) = copies (qcls s) D4 (qgraph s) := by
  ext t
  rw [mem_copies_iff, mem_copies_iff, isCopy_qpart_iff, isCopy_qcls_iff]

theorem edgeLoad_qpart_eq (ψ : Finset (QV s) → ℝ) (e : Sym2 (QV s)) :
    edgeLoad (qpart s) F0 (qgraph s) ψ e = edgeLoad (qcls s) D4 (qgraph s) ψ e := by
  unfold edgeLoad
  rw [copies_qpart_eq]

theorem degVec_lift {t : ℕ} (f : Fin 4 → Fin t) (v : QV s) (j : Fin t) :
    (degVec (fun u : QV s => f u.1) (qgraph s).edgeFinset v j : ℝ) =
      ∑ c ∈ univ.filter (fun c => v.1 ≠ c ∧ f c = j), (s c : ℝ) := by
  rw [degVec_edgeFinset, Int.cast_natCast, ← card_filter_qcls (fun c => v.1 ≠ c ∧ f c = j)]
  rfl

theorem edgeVec_lift {t : ℕ} (f : Fin 4 → Fin t) (i j : Fin t) :
    (edgeVec (fun u : QV s => f u.1) (qgraph s).edgeFinset i j : ℝ) =
      ∑ a ∈ univ.filter (fun a => f a = i), (s a : ℝ) *
        ∑ c ∈ univ.filter (fun c => a ≠ c ∧ f c = j), (s c : ℝ) := by
  rw [edgeVec_eq_sum_degVec, Int.cast_sum]
  simp only [degVec_lift]
  exact sum_filter_qcls (fun a => f a = i)
    (fun a => ∑ c ∈ univ.filter (fun c => a ≠ c ∧ f c = j), (s c : ℝ))

theorem edgeVec_qcls (i j : Fin 4) :
    (edgeVec (qcls s) (qgraph s).edgeFinset i j : ℝ) =
      ∑ a ∈ univ.filter (fun a => a = i), (s a : ℝ) *
        ∑ c ∈ univ.filter (fun c => a ≠ c ∧ c = j), (s c : ℝ) :=
  edgeVec_lift id i j

theorem edgeVec_qpart (i j : Fin 2) :
    (edgeVec (qpart s) (qgraph s).edgeFinset i j : ℝ) =
      ∑ a ∈ univ.filter (fun a => cls a = i), (s a : ℝ) *
        ∑ c ∈ univ.filter (fun c => a ≠ c ∧ cls c = j), (s c : ℝ) :=
  edgeVec_lift cls i j

/-- The total parallel charge of the graph. -/
theorem parallel_charge :
    (pairFun parZ (edgeVec (qcls s) (qgraph s).edgeFinset) : ℝ) =
      2 * ((s 0 : ℝ) - s 1) * ((s 2 : ℝ) - s 3) := by
  rw [pairFun_cast]
  simp only [Fin.sum_univ_four, edgeVec_qcls]
  simp only [Finset.sum_filter, Fin.sum_univ_four]
  simp [parZ]
  ring

/-- The absolute mass of the parallel functional. -/
theorem parallel_mass :
    ∑ e ∈ (qgraph s).edgeFinset, |(pairFun parZ (pairVec (qcls s) e) : ℝ)| =
      2 * ((s 0 : ℝ) + s 1) * ((s 2 : ℝ) + s 3) := by
  have key : ∀ i j : Fin 4, |parZ i j + parZ j i| = parAbs i j + parAbs j i := by decide
  have hper : ∀ e : Sym2 (QV s), |(pairFun parZ (pairVec (qcls s) e) : ℝ)| =
      (pairFun parAbs (pairVec (qcls s) e) : ℝ) := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      rw [← Int.cast_abs, pairFun_pairVec_mk, pairFun_pairVec_mk, key]
  simp only [hper]
  rw [← Int.cast_sum, ← pairFun_edgeVec, pairFun_cast]
  simp only [Fin.sum_univ_four, edgeVec_qcls]
  simp only [Finset.sum_filter, Fin.sum_univ_four]
  simp [parAbs]
  ring

/-- **Exact obstruction.** Any real weights (no sign or cap condition) whose
F0 loads are all within `τ` of one force
`|(s 0 - s 1)(s 2 - s 3)| ≤ τ (s 0 + s 1)(s 2 + s 3)`. -/
theorem parallel_near_loads_force (ψ : Finset (QV s) → ℝ) {τ : ℝ}
    (hload : ∀ e ∈ (qgraph s).edgeFinset, |edgeLoad (qpart s) F0 (qgraph s) ψ e - 1| ≤ τ) :
    |((s 0 : ℝ) - s 1) * ((s 2 : ℝ) - s 3)| ≤ τ * (((s 0 : ℝ) + s 1) * ((s 2 : ℝ) + s 3)) := by
  have hload' : ∀ e ∈ (qgraph s).edgeFinset,
      |edgeLoad (qcls s) D4 (qgraph s) ψ e - 1| ≤ τ := by
    intro e he
    rw [← edgeLoad_qpart_eq]
    exact hload e he
  have h := annihilator_balance (qcls s) D4 (qgraph s) ψ annihilates_D4 hload'
  rw [parallel_charge, parallel_mass] at h
  have habs : |2 * ((s 0 : ℝ) - s 1) * ((s 2 : ℝ) - s 3)| =
      2 * |((s 0 : ℝ) - s 1) * ((s 2 : ℝ) - s 3)| := by
    rw [mul_assoc, abs_mul, abs_two]
  rw [habs] at h
  linarith

/-- **No F0-decomposition** when both class pairs are unbalanced: every
decomposition would give zero parallel charge. -/
theorem not_hasDecomp (h01 : s 0 ≠ s 1) (h23 : s 2 ≠ s 3) :
    ¬ HasDecomp (qpart s) F0 (qgraph s).edgeFinset := by
  rintro ⟨D, hD, hdisj, hU⟩
  have hzero : pairFun parZ (edgeVec (qcls s) (qgraph s).edgeFinset) = 0 := by
    rw [← hU, edgeVec, Finset.sum_biUnion hdisj, pairFun_sum]
    refine Finset.sum_eq_zero fun t ht => ?_
    have hcard : t.card = 3 := (hD t ht).1
    rw [← edgeVec, edgeVec_triEdges _ hcard]
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hcard
    have hsub : triEdges ({a, b, c} : Finset (QV s)) ⊆ (qgraph s).edgeFinset := by
      rw [← hU]
      exact Finset.subset_biUnion_of_mem triEdges ht
    have hadj : ∀ x y : QV s, x ∈ ({a, b, c} : Finset (QV s)) →
        y ∈ ({a, b, c} : Finset (QV s)) → x ≠ y → x.1 ≠ y.1 := by
      intro x y hx hy hxy
      exact SimpleGraph.mem_edgeFinset.mp (hsub (mem_triEdges_iff.mpr ⟨hx, hy, hxy⟩))
    have h1 := hadj a b (by simp) (by simp) hab
    have h2 := hadj a c (by simp) (by simp) hac
    have h3 := hadj b c (by simp) (by simp) hbc
    rw [triType, map_three _ hab hac hbc]
    exact annihilates_D4 _ (transversal_mem a.1 b.1 c.1 h1 h2 h3)
  have hR := parallel_charge (s := s)
  rw [hzero, Int.cast_zero] at hR
  have h01' : (s 0 : ℝ) - s 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h01)
  have h23' : (s 2 : ℝ) - s 3 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h23)
  have : 2 * ((s 0 : ℝ) - s 1) * ((s 2 : ℝ) - s 3) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero h01') h23'
  exact this hR.symm

/-- Number of third vertices for an edge between classes `a ≠ b`. -/
def thirdCount (s : Fin 4 → ℕ) (a b : Fin 4) : ℝ :=
  ∑ c ∈ univ.filter (fun c => a ≠ c ∧ b ≠ c), (s c : ℝ)

theorem load_const (w : ℝ) {u v : QV s} (huv : (qgraph s).Adj u v) :
    edgeLoad (qpart s) F0 (qgraph s) (fun _ => w) s(u, v) = w * thirdCount s u.1 v.1 := by
  unfold edgeLoad
  rw [Finset.sum_const, nsmul_eq_mul, card_edgeCopies _ _ _ huv, mul_comm]
  congr 1
  have hfil : univ.filter (fun z : QV s => (qgraph s).Adj u z ∧ (qgraph s).Adj v z ∧
      ({qpart s u, qpart s v, qpart s z} : Multiset (Fin 2)) ∈ F0) =
      univ.filter (fun z : QV s => u.1 ≠ z.1 ∧ v.1 ≠ z.1) := by
    ext z
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2, -⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2, cls_type_mem _ _ _ huv h1 h2⟩
  rw [hfil, card_filter_qcls (fun c => u.1 ≠ c ∧ v.1 ≠ c)]
  rfl

/-- Common neighbours of `u, v` in part `k`. -/
theorem common_card (u v : QV s) (k : Fin 2) :
    ((univ.filter (fun w => (qgraph s).Adj u w ∧ (qgraph s).Adj w v ∧ qpart s w = k)).card : ℝ) =
      ∑ c ∈ univ.filter (fun c => u.1 ≠ c ∧ c ≠ v.1 ∧ cls c = k), (s c : ℝ) := by
  rw [← card_filter_qcls (fun c => u.1 ≠ c ∧ c ≠ v.1 ∧ cls c = k)]
  rfl

/-- The F0 face (internal minus crossing degree) at a vertex. -/
theorem face_eq (v : QV s) :
    (degFun (groupFace g0 (qpart s v)) (degVec (qpart s) (qgraph s).edgeFinset v) : ℝ) =
      ∑ c ∈ univ.filter (fun c => v.1 ≠ c),
        (if cls c = cls v.1 then (1 : ℝ) else -1) * (s c : ℝ) := by
  simp only [degFun, Int.cast_sum, Int.cast_mul]
  simp only [Fin.sum_univ_two]
  have h0 := degVec_lift (s := s) cls v 0
  have h1 := degVec_lift (s := s) cls v 1
  change (degVec (qpart s) _ v 0 : ℝ) = _ at h0
  change (degVec (qpart s) _ v 1 : ℝ) = _ at h1
  rw [h0, h1]
  rcases v with ⟨a, i⟩
  fin_cases a <;> simp only [Finset.sum_filter, Fin.sum_univ_four] <;>
    simp [groupFace, g0, qpart, cls] <;> ring

end General

section Family

/-- Class sizes `2k(q+12), 2k(q+6), 2k(q+8), 2kq`. They satisfy
`(a+b)(c+d) = 2(ab+cd)` exactly (zero F0 charge) while `(a-b)(c-d) = 192k^2`. -/
def fam (k q : ℕ) : Fin 4 → ℕ :=
  ![2 * k * (q + 12), 2 * k * (q + 6), 2 * k * (q + 8), 2 * k * q]

variable {k q : ℕ}

theorem card_fam : (Fintype.card (QV (fam k q)) : ℝ) = 2 * k * (4 * q + 26) := by
  rw [card_QV]
  simp [fam, Fin.sum_univ_four]
  ring

theorem thirdCount_fam (a b : Fin 4) (hab : a ≠ b) :
    2 * (k : ℝ) * (2 * q + 6) ≤ thirdCount (fam k q) a b ∧
      thirdCount (fam k q) a b ≤ 2 * (k : ℝ) * (2 * q + 20) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  fin_cases a <;> fin_cases b <;>
    simp only [thirdCount, Finset.sum_filter, Fin.sum_univ_four] at hab ⊢ <;>
    simp [fam] at hab ⊢ <;> constructor <;> nlinarith [mul_nonneg hk hq]

/-- **The seed**: constant weight, `2`-regular and `14/(2q+20)`-almost. -/
theorem fam_seed (hk : 0 < k) :
    IsRegularAlmostPacking (qpart (fam k q)) F0 (qgraph (fam k q)) 2 (14 / (2 * (q : ℝ) + 20))
      (fun _ => 1 / (2 * (k : ℝ) * (2 * q + 20))) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hD : (0 : ℝ) < 2 * k * (2 * q + 20) := by positivity
  refine ⟨fun t _ => ?_, fun e he => ?_⟩
  · rw [card_fam]
    constructor
    · rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg hkR.le hq]
    · rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg hkR.le hq]
  · induction e using Sym2.ind with
    | _ u v =>
      have huv : (qgraph (fam k q)).Adj u v := SimpleGraph.mem_edgeFinset.mp he
      have hload := load_const (s := fam k q) (1 / (2 * (k : ℝ) * (2 * q + 20))) huv
      unfold edgeLoad at hload
      rw [hload, one_div_mul_eq_div]
      obtain ⟨hlo, hhi⟩ := thirdCount_fam (k := k) (q := q) u.1 v.1 huv
      constructor
      · have h1 : 1 - 14 / (2 * (q : ℝ) + 20) = 2 * k * (2 * q + 6) / (2 * k * (2 * q + 20)) := by
          field_simp
          ring
        rw [h1]
        exact div_le_div_of_nonneg_right hlo hD.le
      · exact (div_le_one hD).mpr hhi

theorem fam_common (a b : Fin 4) (j : Fin 2)
    (hF : ({cls a, cls b, j} : Multiset (Fin 2)) ∈ F0) :
    2 * (k : ℝ) * q ≤
      ∑ c ∈ univ.filter (fun c => a ≠ c ∧ c ≠ b ∧ cls c = j), (fam k q c : ℝ) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  fin_cases a <;> fin_cases b <;> fin_cases j <;> first
    | exact absurd hF (by decide)
    | (simp only [Finset.sum_filter, Fin.sum_univ_four]; simp [cls, fam] <;>
        nlinarith [mul_nonneg hk hq0])

/-- **Anti-edgefulness** with `α = 1/8` once `q ≥ 7`. -/
theorem fam_antiEdgeful (hq : 7 ≤ q) :
    AntiEdgeful (qpart (fam k q)) F0 (qgraph (fam k q)) (1 / 8) := by
  intro τ hτ i j l hijk u v _ hu hv
  rw [common_card]
  have hF : ({cls u.1, cls v.1, l} : Multiset (Fin 2)) ∈ F0 := by
    have h1 : cls u.1 = i := hu
    have h2 : cls v.1 = j := hv
    rw [h1, h2, ← hijk]
    exact hτ
  refine le_trans ?_ (fam_common u.1 v.1 l hF)
  rw [card_fam]
  have hq7 : (7 : ℝ) ≤ q := by exact_mod_cast hq
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith [mul_nonneg hk (sub_nonneg.mpr hq7)]

/-- **Exact global F0 balance.** -/
theorem fam_balance :
    pairFun (groupPair g0) (edgeVec (qpart (fam k q)) (qgraph (fam k q)).edgeFinset) = 0 := by
  have h : (pairFun (groupPair g0)
      (edgeVec (qpart (fam k q)) (qgraph (fam k q)).edgeFinset) : ℝ) = 0 := by
    rw [pairFun_cast]
    simp only [Fin.sum_univ_two, edgeVec_qpart]
    simp only [Finset.sum_filter, Fin.sum_univ_four]
    simp [cls, fam, groupPair, g0]
    ring
  exact_mod_cast h

/-- **Strict local margin at every vertex**: internal minus crossing degree is
at most `-(1/512) n`. -/
theorem fam_face (hq : 7 ≤ q) (v : QV (fam k q)) :
    (degFun (groupFace g0 (qpart (fam k q) v))
        (degVec (qpart (fam k q)) (qgraph (fam k q)).edgeFinset v) : ℝ) ≤
      -(1 / 512) * Fintype.card (QV (fam k q)) := by
  rw [face_eq, card_fam]
  have hq7 : (7 : ℝ) ≤ q := by exact_mod_cast hq
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rcases v with ⟨a, i⟩
  fin_cases a <;> simp only [Finset.sum_filter, Fin.sum_univ_four] <;> simp [cls, fam] <;>
    nlinarith [mul_nonneg hk (sub_nonneg.mpr hq7)]

theorem typeEdgeVec_001 : typeEdgeVec ({0, 0, 1} : Multiset (Fin 2)) = ![![2, 2], ![2, 0]] := by
  funext i j
  fin_cases i <;> fin_cases j <;> decide

theorem typeEdgeVec_011 : typeEdgeVec ({0, 1, 1} : Multiset (Fin 2)) = ![![0, 2], ![2, 2]] := by
  funext i j
  fin_cases i <;> fin_cases j <;> decide

theorem typeDegVec_001 (a : Fin 2) :
    typeDegVec ({0, 0, 1} : Multiset (Fin 2)) a = if a = 0 then ![1, 1] else ![2, 0] := by
  funext i
  fin_cases a <;> fin_cases i <;> decide

theorem typeDegVec_011 (a : Fin 2) :
    typeDegVec ({0, 1, 1} : Multiset (Fin 2)) a = if a = 0 then ![0, 2] else ![1, 1] := by
  funext i
  fin_cases a <;> fin_cases i <;> decide

theorem F0_sum {M : Type*} [AddCommMonoid M] (f : Multiset (Fin 2) → M) :
    ∑ τ ∈ F0, f τ = f {0, 0, 1} + f {0, 1, 1} :=
  Finset.sum_pair (by decide)

theorem F0_filter_mem (i : Fin 2) : F0.filter (fun τ => i ∈ τ) = F0 := by
  revert i
  decide

theorem ne_011_001 : ({0, 1, 1} : Multiset (Fin 2)) ≠ {0, 0, 1} := by decide

/-- **Exact integral F0-divisibility** of the example (all class sizes are even). -/
theorem fam_isIntDiv : IsIntDiv (qpart (fam k q)) F0 (qgraph (fam k q)).edgeFinset := by
  refine ⟨⟨fun τ => if τ = {0, 0, 1} then (2 * k * (q + 12) : ℤ) * (2 * k * (q + 6))
      else (2 * k * (q + 8) : ℤ) * (2 * k * q), ?_⟩, fun v => ?_⟩
  · rw [F0_sum]
    simp only [↓reduceIte, ne_011_001, typeEdgeVec_001, typeEdgeVec_011]
    funext i j
    apply Int.cast_injective (α := ℝ)
    rw [edgeVec_qpart]
    fin_cases i <;> fin_cases j <;> simp only [Finset.sum_filter, Fin.sum_univ_four] <;>
      simp [cls, fam] <;> ring
  · rcases v with ⟨a, i⟩
    have hdeg : ∀ j, (degVec (qpart (fam k q)) (qgraph (fam k q)).edgeFinset ⟨a, i⟩ j : ℝ) =
        ∑ c ∈ univ.filter (fun c => a ≠ c ∧ cls c = j), (fam k q c : ℝ) :=
      fun j => degVec_lift cls ⟨a, i⟩ j
    have hp : qpart (fam k q) ⟨a, i⟩ = cls a := rfl
    let c0 : ℤ := if cls a = 0 then
        (if a = 0 then 2 * k * (q + 6) else 2 * k * (q + 12))
      else (if a = 2 then k * (q + 18) else k * (q + 10))
    let c1 : ℤ := if cls a = 0 then
        (if a = 0 then k * (q + 2) else k * ((q : ℤ) - 4))
      else (if a = 2 then 2 * k * q else 2 * k * (q + 8))
    refine ⟨fun τ => if τ = {0, 0, 1} then c0 else c1, ?_⟩
    rw [hp, F0_filter_mem, F0_sum]
    simp only [↓reduceIte, ne_011_001, typeDegVec_001, typeDegVec_011]
    funext j
    apply Int.cast_injective (α := ℝ)
    rw [hdeg]
    fin_cases a <;> fin_cases j <;> simp only [Finset.sum_filter, Fin.sum_univ_four] <;>
      simp [c0, c1, cls, fam] <;> ring

end Family

section Refutation

variable {k q : ℕ}

/-- **The example has no F0-decomposition at all**, although it carries a
`2`-regular `14/(2q+20)`-almost seed, is `1/8`-anti-edgeful, is integrally
F0-divisible, has zero global F0 charge, and has internal minus crossing degree
at most `-(1/512) n` at every vertex. -/
theorem fam_hypotheses_without_decomposition (hk : 0 < k) (hq : 7 ≤ q) :
    IsRegularAlmostPacking (qpart (fam k q)) F0 (qgraph (fam k q)) 2 (14 / (2 * (q : ℝ) + 20))
        (fun _ => 1 / (2 * (k : ℝ) * (2 * q + 20))) ∧
      AntiEdgeful (qpart (fam k q)) F0 (qgraph (fam k q)) (1 / 8) ∧
      IsIntDiv (qpart (fam k q)) F0 (qgraph (fam k q)).edgeFinset ∧
      pairFun (groupPair g0) (edgeVec (qpart (fam k q)) (qgraph (fam k q)).edgeFinset) = 0 ∧
      (∀ v, (degFun (groupFace g0 (qpart (fam k q) v))
        (degVec (qpart (fam k q)) (qgraph (fam k q)).edgeFinset v) : ℝ) ≤
          -(1 / 512) * Fintype.card (QV (fam k q))) ∧
      ¬ HasDecomp (qpart (fam k q)) F0 (qgraph (fam k q)).edgeFinset := by
  refine ⟨fam_seed hk, fam_antiEdgeful hq, fam_isIntDiv, fam_balance, fam_face hq,
    not_hasDecomp ?_ ?_⟩
  · simp only [fam, Matrix.cons_val_zero, Matrix.cons_val_one]
    intro h
    have : 2 * k * (q + 12) = 2 * k * (q + 6) + 12 * k := by ring
    omega
  · simp only [fam]
    intro h
    have h' : 2 * k * (q + 8) = 2 * k * q := h
    have : 2 * k * (q + 8) = 2 * k * q + 16 * k := by ring
    omega

/-- **No near-unit loads on the example**, for arbitrary real weights (no sign
or cap condition), at precision `24 / ((2q+18)(2q+8))`. -/
theorem fam_no_near_loads (hk : 0 < k) (ψ : Finset (QV (fam k q)) → ℝ) :
    ¬ ∀ e ∈ (qgraph (fam k q)).edgeFinset,
      |edgeLoad (qpart (fam k q)) F0 (qgraph (fam k q)) ψ e - 1| ≤
        24 / ((2 * (q : ℝ) + 18) * (2 * q + 8)) := by
  intro hload
  have h := parallel_near_loads_force ψ hload
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have e1 : ((fam k q 0 : ℝ) - fam k q 1) * ((fam k q 2 : ℝ) - fam k q 3) = 192 * (k : ℝ) ^ 2 := by
    simp [fam]
    ring
  have e2 : ((fam k q 0 : ℝ) + fam k q 1) * ((fam k q 2 : ℝ) + fam k q 3) =
      4 * (k : ℝ) ^ 2 * ((2 * q + 18) * (2 * q + 8)) := by
    simp [fam]
    ring
  rw [e1, e2, abs_of_nonneg (by positivity)] at h
  have hP : (0 : ℝ) < (2 * q + 18) * (2 * q + 8) := by positivity
  have e3 : 24 / ((2 * (q : ℝ) + 18) * (2 * q + 8)) *
      (4 * (k : ℝ) ^ 2 * ((2 * q + 18) * (2 * q + 8))) = 96 * (k : ℝ) ^ 2 := by
    field_simp
    ring
  rw [e3] at h
  nlinarith

/-- **Strengthened variant of `F0BalancedBoostTarget`**, with every additional
input hypothesis that the Stage36/Stage37 route can supply: besides the
`κ`-balance and `κ`-faces, exact integral F0-divisibility and the strict local
margin `-(α²/(4C)) n` at every vertex. The conclusion only asks for real weights
(no sign or cap condition). It is refuted by `not_F0StrictDivSignedTarget`. -/
def F0StrictDivSignedTarget : Prop :=
  ∀ C α : ℝ, 1 ≤ C → 0 < α →
    ∃ ε : ℝ, 0 < ε ∧ ∀ τ : ℝ, 0 < τ → ∃ κ : ℝ, 0 < κ ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (p : V → Fin 2) (J : SimpleGraph V) [DecidableRel J.Adj] (φ : Finset V → ℝ),
        IsRegularAlmostPacking p F0 J C ε φ → AntiEdgeful p F0 J α →
        |(pairFun (groupPair g0) (edgeVec p J.edgeFinset) : ℝ)| ≤
          κ * (Fintype.card V : ℝ) ^ 2 →
        (∀ v, (degFun (groupFace g0 (p v)) (degVec p J.edgeFinset v) : ℝ) ≤
          κ * Fintype.card V) →
        (∀ v, (degFun (groupFace g0 (p v)) (degVec p J.edgeFinset v) : ℝ) ≤
          -(α ^ 2 / (4 * C)) * Fintype.card V) →
        IsIntDiv p F0 J.edgeFinset →
        ∃ ψ : Finset V → ℝ, ∀ e ∈ J.edgeFinset, |edgeLoad p F0 J ψ e - 1| ≤ τ

/-- The current target implies the strengthened signed variant (it has fewer
hypotheses and a stronger conclusion). -/
theorem strictDivSigned_of_balanced (h : F0BalancedBoostTarget) :
    F0StrictDivSignedTarget := by
  intro C α hC hα
  obtain ⟨b, ε, -, hε, H⟩ := h C α hC hα
  refine ⟨ε, hε, fun τ hτ => ?_⟩
  obtain ⟨κ, hκ, N, hN⟩ := H τ hτ
  refine ⟨κ, hκ, N, fun V _ _ hV p J _ φ hs ha hbal hface _ _ => ?_⟩
  obtain ⟨ψ, -, hψ⟩ := hN V hV p J φ hs ha hbal hface
  exact ⟨ψ, hψ⟩

/-- **The strengthened signed variant is false**, already for `C = 2`,
`α = 1/8`: for every input tolerance `ε > 0` there is a precision `τ > 0` such
that for every `κ > 0` and every `N` the complete four-partite graph with class
sizes `2k(q+12), 2k(q+6), 2k(q+8), 2kq` (`q = ⌈14/ε⌉ + 7`, `k = N + 1`) satisfies
all hypotheses (with zero global charge) but carries no real weights whose loads
are all within `τ` of one. -/
theorem not_F0StrictDivSignedTarget : ¬ F0StrictDivSignedTarget := by
  intro h
  obtain ⟨ε, hε, H⟩ := h 2 (1 / 8) (by norm_num) (by norm_num)
  set q : ℕ := ⌈14 / ε⌉₊ + 7 with hq
  have hq7 : 7 ≤ q := by omega
  have hqR : 14 / ε ≤ (q : ℝ) := by
    rw [hq]
    push_cast
    linarith [Nat.le_ceil (14 / ε)]
  have hqε : 14 / (2 * (q : ℝ) + 20) ≤ ε := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hε] at hqR
    nlinarith
  obtain ⟨κ, hκ, N, hN⟩ := H (24 / ((2 * (q : ℝ) + 18) * (2 * q + 8))) (by positivity)
  set k : ℕ := N + 1 with hk
  have hkpos : 0 < k := by omega
  have hcard : N ≤ Fintype.card (QV (fam k q)) := by
    have h1 : (N : ℝ) ≤ Fintype.card (QV (fam k q)) := by
      rw [card_fam, hk]
      push_cast
      nlinarith [(Nat.cast_nonneg q : (0 : ℝ) ≤ q), (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    exact_mod_cast h1
  have hseed := fam_seed (q := q) hkpos
  have hseed' : IsRegularAlmostPacking (qpart (fam k q)) F0 (qgraph (fam k q)) 2 ε
      (fun _ => 1 / (2 * (k : ℝ) * (2 * q + 20))) :=
    ⟨hseed.1, fun e he => ⟨by linarith [(hseed.2 e he).1], (hseed.2 e he).2⟩⟩
  have hn : (0 : ℝ) ≤ Fintype.card (QV (fam k q)) := Nat.cast_nonneg _
  obtain ⟨ψ, hψ⟩ := hN (QV (fam k q)) hcard (qpart _) (qgraph _) _ hseed'
    (fam_antiEdgeful hq7)
    (by rw [fam_balance, Int.cast_zero, abs_zero]; positivity)
    (fun v => (fam_face hq7 v).trans (by nlinarith [mul_nonneg hκ.le hn]))
    (fun v => (fam_face hq7 v).trans (le_of_eq (by norm_num)))
    fam_isIntDiv
  exact fam_no_near_loads hkpos ψ hψ

/-- **`F0BalancedBoostTarget` is false.** -/
theorem not_F0BalancedBoostTarget : ¬ F0BalancedBoostTarget :=
  fun h => not_F0StrictDivSignedTarget (strictDivSigned_of_balanced h)

end Refutation

end PartitionedTriangleAbsorption.F0ParallelObstruction
