/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SignedCertificate.Packing

/-! # The double hexagon: an actual signed-certificate input that defeats pairwise supply

Roots (`Fin 9`): `0 = x, 1 = y, 2 = z, 3 = a, 4 = b, 5 = c, 6 = a', 7 = b', 8 = c'`, with
parts `x,y,b,b' ∈ V₀` and `z,a,c,a',c' ∈ V₁`. The source is the union of two hexagons

  `P = (x a y b z c) ∪ (x a' y b' z c')`  (12 edges, every root of even degree).

The host on `Fin 9 ⊕ (Fin 4 × Fin m)` has root–root edges exactly `P ∪ {xy, yz, zx}`,
four bulk classes (two per part, complete multipartite between distinct classes) and all
root–bulk edges. It is F0-anti-edgeful with `α = 1/5` for `m ≥ 9`.

`P` has the actual signed physical certificate
`xay + ybz + zcx + xa'y + yb'z + zc'x - 2·xyz` of weight `8` (a negative coefficient is
essential). Every root has even degree, `|P| = 12`, `e₀₀ = e₁₁ = 2`, `e₀₁ = 8`.

`no_degenerate_twoMode`: no two-mode solution `(A, Q)` (with `A ⊆ E(G)`, `Q` outside the
roots) has `A ∪ P ∪ Q` 2-degenerate over the roots. Consequently the pairwise-supply version
of the Stage 49 candidate is false (`not_pairSupplyCandidate`). This is **not** a refutation
of the candidate itself: `DoubleHexagonAbsorber` exhibits a bounded absorber in the same
hosts.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SignedCertificate.DoubleHexagon

open Finset TypedApplicationLinks

/-! ### Abstract ear lemmas -/

section Ears

variable {V : Type*} [DecidableEq V]

/-- If the only `E`-neighbours of `a` are `x, y` and `ax ∈ E`, every decomposition of `E`
contains a triangle through `a, x, y`. -/
theorem ear_triangle {p : V → Fin 2} {E : Finset (Sym2 V)} {D : Finset (Finset V)}
    (hD : IsDecomp p F0 E D) {a x y : V} (hax : s(a, x) ∈ E)
    (hN : ∀ u, s(a, u) ∈ E → u = x ∨ u = y) : ∃ s ∈ D, a ∈ s ∧ x ∈ s ∧ y ∈ s := by
  rw [← hD.2.2, mem_biUnion] at hax
  obtain ⟨s, hs, hes⟩ := hax
  obtain ⟨has, hxs⟩ := mem_of_mk_mem_triEdges' hes
  have hne : a ≠ x := by
    simp only [triEdges, mem_filter, Sym2.mk_isDiag_iff] at hes; exact hes.2
  obtain ⟨c, hcs, hca, hcx⟩ : ∃ c ∈ s, c ≠ a ∧ c ≠ x := by
    by_contra h
    push Not at h
    have hsub : s ⊆ {a, x} := fun c hc => by
      by_cases hca : c = a
      · simp [hca]
      · simp [h c hc hca]
    have := card_le_card hsub
    rw [(hD.1 s hs).1] at this
    have := card_insert_le a ({x} : Finset V)
    simp at this
    omega
  have hac : s(a, c) ∈ E := by
    rw [← hD.2.2]
    exact mem_biUnion.mpr ⟨s, hs, mk_mem_triEdges_of_mem has hcs (Ne.symm hca)⟩
  rcases hN c hac with rfl | rfl
  · exact absurd rfl hcx
  · exact ⟨s, hs, has, hxs, hcs⟩

/-- **Double ear.** Two distinct vertices `a, a'` whose only `E`-neighbours are `x, y`
(with `ax, a'x ∈ E` and `a, a', x, y` distinct) make `E` non-decomposable. -/
theorem not_hasDecomp_double_ear {p : V → Fin 2} {E : Finset (Sym2 V)} {a a' x y : V}
    (hdist : ({a, a', x, y} : Finset V).card = 4)
    (hax : s(a, x) ∈ E) (ha'x : s(a', x) ∈ E)
    (hN : ∀ u, s(a, u) ∈ E → u = x ∨ u = y) (hN' : ∀ u, s(a', u) ∈ E → u = x ∨ u = y) :
    ¬ HasDecomp p F0 E := by
  rintro ⟨D, hD⟩
  obtain ⟨s, hs, has, hxs, hys⟩ := ear_triangle hD hax hN
  obtain ⟨s', hs', has', hxs', hys'⟩ := ear_triangle hD ha'x hN'
  have hxy : x ≠ y := by
    intro h; subst h
    have : ({a, a', x, x} : Finset V).card ≤ 3 := by
      simp only [insert_eq_of_mem (mem_singleton_self x)]
      exact (card_insert_le _ _).trans (by
        have := card_insert_le a' ({x} : Finset V)
        simp at this ⊢
        omega)
    omega
  by_cases hss : s = s'
  · subst hss
    have : ({a, a', x, y} : Finset V) ⊆ s := by
      intro v hv; simp only [mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> assumption
    have := card_le_card this
    rw [hdist, (hD.1 s hs).1] at this
    omega
  · have h1 := mk_mem_triEdges_of_mem hxs hys hxy
    have h2 := mk_mem_triEdges_of_mem hxs' hys' hxy
    exact disjoint_left.mp (hD.2.1 hs hs' hss) h1 h2

end Ears

/-! ### The roots -/

/-- The source on the roots: two hexagons through `x, y, z`. -/
def Pc : Finset (Sym2 (Fin 9)) :=
  {s(0, 3), s(3, 1), s(1, 4), s(4, 2), s(2, 5), s(5, 0),
    s(0, 6), s(6, 1), s(1, 7), s(7, 2), s(2, 8), s(8, 0)}

/-- The central triangle `xyz`. -/
def tc : Finset (Sym2 (Fin 9)) := {s(0, 1), s(1, 2), s(0, 2)}

/-- Root parts. -/
def rootPart : Fin 9 → Fin 2 := ![0, 0, 1, 1, 0, 1, 1, 0, 1]

/-- Parts of the four bulk classes. -/
def classPart : Fin 4 → Fin 2 := ![0, 0, 1, 1]

/-- The seven certificate triangles. -/
def triC : Fin 7 → Finset (Fin 9) :=
  ![{0, 3, 1}, {1, 4, 2}, {2, 5, 0}, {0, 6, 1}, {1, 7, 2}, {2, 8, 0}, {0, 1, 2}]

/-- Certificate coefficients: six ears `+1`, the central triangle `-2`. -/
def coef : Fin 7 → ℤ := ![1, 1, 1, 1, 1, 1, -2]

theorem root_irrefl : ∀ i : Fin 9, s(i, i) ∉ Pc ∪ tc := by decide

theorem root_cert : ∀ i j : Fin 9,
    ind Pc s(i, j) = ∑ k, coef k * ind (triEdges (triC k)) s(i, j) := by
  unfold ind Pc triC coef triEdges
  decide

theorem root_tri : ∀ k : Fin 7, (triC k).card = 3 ∧ (triC k).val.map rootPart ∈ F0 ∧
    ∀ a ∈ triC k, ∀ b ∈ triC k, a ≠ b → s(a, b) ∈ Pc ∪ tc := by
  unfold triC Pc tc rootPart F0
  decide

theorem certWeight_coef : certWeight coef = 8 := by
  unfold certWeight coef
  decide

/-- Neighbourhood facts used against 2-degenerate constructions. -/
theorem root_ear : ∀ u : Fin 9, (s(3, u) ∈ Pc → u = 0 ∨ u = 1) ∧ (s(6, u) ∈ Pc → u = 0 ∨ u = 1) ∧
    s(3, u) ∉ tc ∧ s(6, u) ∉ tc := by
  unfold Pc tc
  decide

/-! ### The host -/

/-- Host vertices: nine roots and four bulk classes of size `m`. -/
abbrev HV (m : ℕ) := Fin 9 ⊕ (Fin 4 × Fin m)

/-- Host parts. -/
def part (m : ℕ) : HV m → Fin 2
  | .inl i => rootPart i
  | .inr q => classPart q.1

/-- Host adjacency. -/
def hAdj (m : ℕ) : HV m → HV m → Prop
  | .inl i, .inl j => s(i, j) ∈ Pc ∪ tc
  | .inl _, .inr _ => True
  | .inr _, .inl _ => True
  | .inr q, .inr q' => q.1 ≠ q'.1

instance (m : ℕ) : DecidableRel (hAdj m) := fun u v => by
  cases u <;> cases v <;> unfold hAdj <;> infer_instance

/-- The scaled host graph. -/
def host (m : ℕ) : SimpleGraph (HV m) where
  Adj := hAdj m
  symm := ⟨by
    intro u v h
    cases u <;> cases v <;> simp only [hAdj] at h ⊢
    · rwa [Sym2.eq_swap]
    · exact Ne.symm h⟩
  loopless := ⟨fun u h => by
    cases u with
    | inl i => exact root_irrefl i h
    | inr q => exact h rfl⟩

instance (m : ℕ) : DecidableRel (host m).Adj := inferInstanceAs (DecidableRel (hAdj m))

theorem card_HV (m : ℕ) : Fintype.card (HV m) = 9 + 4 * m := by
  simp [Fintype.card_sum, Fintype.card_prod]

/-- Class-level witnesses for anti-edgefulness. -/
theorem class_witness : ∀ (ou ov : Option (Fin 4)) (pu pv k : Fin 2),
    (∀ c, ou = some c → classPart c = pu) → (∀ c, ov = some c → classPart c = pv) →
    ({pu, pv, k} : Multiset (Fin 2)) ∈ F0 →
    ∃ e : Fin 4, classPart e = k ∧ ou ≠ some e ∧ ov ≠ some e := by
  unfold classPart F0
  decide

/-- Bulk class of a host vertex. -/
def cls {m : ℕ} : HV m → Option (Fin 4)
  | .inl _ => none
  | .inr q => some q.1

theorem cls_part {m : ℕ} (u : HV m) : ∀ c, cls u = some c → classPart c = part m u := by
  intro c h
  cases u with
  | inl _ => simp [cls] at h
  | inr q => simp only [cls, Option.some.injEq] at h; subst h; rfl

theorem adj_of_cls {m : ℕ} (u : HV m) (e : Fin 4) (l : Fin m) (h : cls u ≠ some e) :
    (host m).Adj u (.inr (e, l)) := by
  cases u with
  | inl _ => trivial
  | inr q => exact fun hq => h (by simp [cls, hq])

/-- **The host is F0-anti-edgeful** for every `α ≤ 1/5` once `m ≥ 9`. -/
theorem antiEdgeful (m : ℕ) (hm : 9 ≤ m) (α : ℝ) (hα : α ≤ 1 / 5) :
    AntiEdgeful (part m) F0 (host m) α := by
  intro τ hτ i j k hτeq u v huv hu hv
  subst hτeq
  obtain ⟨e, hek, heu, hev⟩ := class_witness (cls u) (cls v) i j k
    (fun c h => (cls_part u c h).trans hu) (fun c h => (cls_part v c h).trans hv) hτ
  have hsub : (univ.image fun l : Fin m => (Sum.inr (e, l) : HV m)) ⊆
      univ.filter (fun w => (host m).Adj u w ∧ (host m).Adj w v ∧ part m w = k) := by
    intro w hw
    obtain ⟨l, -, rfl⟩ := mem_image.mp hw
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨adj_of_cls u e l heu, (adj_of_cls v e l hev).symm, hek⟩
  have hcard := card_le_card hsub
  rw [card_image_of_injective _ (fun a b h => by simpa using h), card_univ,
    Fintype.card_fin] at hcard
  rw [card_HV]
  have hmR : (9 : ℝ) ≤ m := by exact_mod_cast hm
  have hcardR := (Nat.cast_le (α := ℝ)).mpr hcard
  push_cast
  have hα' : α * (9 + 4 * (m : ℝ)) ≤ 1 / 5 * (9 + 4 * m) :=
    mul_le_mul_of_nonneg_right hα (by positivity)
  linarith

theorem parts_inhabited (m : ℕ) : ∀ j : Fin 2, ∃ v, part m v = j := by
  intro j
  fin_cases j
  · exact ⟨.inl 0, rfl⟩
  · exact ⟨.inl 2, rfl⟩

/-! ### The source, its certificate and the excluded set -/

/-- The embedding of the roots. -/
def rootEmb (m : ℕ) : Fin 9 ↪ HV m := ⟨Sum.inl, Sum.inl_injective⟩

/-- Edge embedding of the roots. -/
def rootEdgeEmb (m : ℕ) : Sym2 (Fin 9) ↪ Sym2 (HV m) :=
  ⟨Sym2.map Sum.inl, Sym2.map.injective Sum.inl_injective⟩

/-- The physical source `P`. -/
def src (m : ℕ) : Finset (Sym2 (HV m)) := Pc.map (rootEdgeEmb m)

/-- The physical certificate triangles. -/
def tri (m : ℕ) (k : Fin 7) : Finset (HV m) := (triC k).map (rootEmb m)

/-- The excluded set `Z`: the nine roots. -/
def roots (m : ℕ) : Finset (HV m) := univ.map (rootEmb m)

theorem roots_card (m : ℕ) : (roots m).card = 9 := by simp [roots]

theorem triEdges_map {W V : Type*} [DecidableEq W] [DecidableEq V] (f : W ↪ V) (s : Finset W) :
    triEdges (s.map f) = (triEdges s).map ⟨Sym2.map f, Sym2.map.injective f.injective⟩ := by
  simp only [map_eq_image, triEdges, sym2_image, filter_image, Sym2.isDiag_map f.injective]
  rfl

theorem ind_map_root (m : ℕ) (S : Finset (Sym2 (Fin 9))) (e : Sym2 (Fin 9)) :
    ind (S.map (rootEdgeEmb m)) (Sym2.map Sum.inl e) = ind S e := by
  unfold ind
  rw [show Sym2.map Sum.inl e = rootEdgeEmb m e from rfl]
  by_cases h : e ∈ S <;> simp [h]

theorem ind_map_root_out (m : ℕ) (S : Finset (Sym2 (Fin 9))) (e : Sym2 (HV m))
    (he : ∀ e' : Sym2 (Fin 9), Sym2.map Sum.inl e' ≠ e) : ind (S.map (rootEdgeEmb m)) e = 0 := by
  simp only [ind, ite_eq_right (show e ∉ S.map (rootEdgeEmb m) by
    intro h; obtain ⟨e', -, h'⟩ := mem_map.mp h; exact he e' h')]

theorem tri_isCopy (m : ℕ) (k : Fin 7) : IsCopy (part m) F0 (host m) (tri m k) := by
  obtain ⟨h3, hF, hadj⟩ := root_tri k
  refine ⟨⟨?_, by simpa [tri] using h3⟩, ?_⟩
  · intro u hu v hv huv
    simp only [tri, coe_map, Set.mem_image, mem_coe] at hu hv
    obtain ⟨a, ha, rfl⟩ := hu
    obtain ⟨b, hb, rfl⟩ := hv
    exact hadj a ha b hb (fun h => huv (by rw [h]))
  · simp only [tri, map_val, Multiset.map_map]
    exact hF

/-- **The actual signed physical certificate of weight 8.** -/
theorem src_cert (m : ℕ) : IsSignedCert (part m) (host m) (src m) (tri m) coef := by
  refine ⟨tri_isCopy m, ?_⟩
  intro e
  by_cases he : ∃ e' : Sym2 (Fin 9), Sym2.map Sum.inl e' = e
  · obtain ⟨e', rfl⟩ := he
    induction e' using Sym2.ind with
    | _ i j =>
      rw [src, ind_map_root, root_cert i j]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [tri, triEdges_map]
      exact congrArg _ (ind_map_root m _ _).symm
  · push Not at he
    rw [src, ind_map_root_out m _ e he]
    symm
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [tri, triEdges_map]
    rw [show (⟨Sym2.map (rootEmb m), Sym2.map.injective (rootEmb m).injective⟩ :
      Sym2 (Fin 9) ↪ Sym2 (HV m)) = rootEdgeEmb m from rfl, ind_map_root_out m _ e he, mul_zero]

theorem src_subset (m : ℕ) : src m ⊆ (host m).edgeFinset := by
  intro e he
  obtain ⟨e', he', rfl⟩ := mem_map.mp he
  induction e' using Sym2.ind with
  | _ i j =>
    rw [SimpleGraph.mem_edgeFinset]
    change s(Sum.inl i, Sum.inl j) ∈ (host m).edgeSet
    rw [SimpleGraph.mem_edgeSet]
    exact mem_union_left _ he'

theorem src_roots (m : ℕ) : ∀ e ∈ src m, ∀ v ∈ e, v ∈ roots m := by
  intro e he v hv
  obtain ⟨e', -, rfl⟩ := mem_map.mp he
  obtain ⟨w, -, rfl⟩ := Sym2.mem_map.mp hv
  exact mem_map_of_mem _ (mem_univ w)

/-! ### No 2-degenerate solution -/

/-- **No pairwise-supply solution.** There is no two-mode solution `(A, Q)` for the double
hexagon with `A ⊆ E(G)`, `Q` avoiding the roots and `A ∪ P ∪ Q` 2-degenerate over the
roots. -/
theorem no_degenerate_twoMode (m : ℕ) (A Q : Finset (Sym2 (HV m))) (r : HV m → ℕ)
    (hA : A ⊆ (host m).edgeFinset) (hQZ : ∀ e ∈ Q, ∀ v ∈ e, v ∉ roots m)
    (h : IsTwoMode (part m) (src m) A Q)
    (hdeg : IsDegenerateOver (A ∪ src m ∪ Q) (roots m) r) : False := by
  obtain ⟨A', hA'A, hA'Z, ⟨hdisj, -, hdec⟩, -⟩ :=
    rootAbsorber_of_degenerate (src_roots m) hQZ h hdeg
  -- neighbourhoods of `a = 3` and `a' = 6` in `A' ∪ P`
  have hN : ∀ i : Fin 9, i = 3 ∨ i = 6 → ∀ u, s(.inl i, u) ∈ A' ∪ src m →
      u = .inl 0 ∨ u = .inl 1 := by
    intro i hi u hu
    have huZ : u ∈ roots m := by
      rcases mem_union.mp hu with h1 | h1
      · exact hA'Z _ h1 u (Sym2.mem_mk_right _ _)
      · exact src_roots m _ h1 u (Sym2.mem_mk_right _ _)
    obtain ⟨u', -, rfl⟩ := mem_map.mp huZ
    simp only [rootEmb, Function.Embedding.coeFn_mk] at hu ⊢
    rcases mem_union.mp hu with h1 | h1
    · exfalso
      have hG := hA (hA'A h1)
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hG
      change s(i, u') ∈ Pc ∪ tc at hG
      have hnP : s(i, u') ∉ Pc := fun hP =>
        disjoint_left.mp hdisj h1 (mem_map_of_mem (rootEdgeEmb m) hP)
      have := root_ear u'
      rcases hi with rfl | rfl <;> rcases mem_union.mp hG with h2 | h2 <;> tauto
    · have hP : s(i, u') ∈ Pc := by
        rw [src] at h1
        rwa [show (s(Sum.inl i, Sum.inl u') : Sym2 (HV m)) = rootEdgeEmb m s(i, u') from rfl,
          mem_map'] at h1
      have := root_ear u'
      rcases hi with rfl | rfl
      · rcases this.1 hP with rfl | rfl <;> simp
      · rcases this.2.1 hP with rfl | rfl <;> simp
  have hax : ∀ i : Fin 9, i = 3 ∨ i = 6 → s(.inl i, .inl 0) ∈ A' ∪ src m := by
    intro i hi
    refine mem_union_right _ ?_
    rw [show (s(Sum.inl i, Sum.inl 0) : Sym2 (HV m)) = rootEdgeEmb m s(i, 0) from rfl, src,
      mem_map']
    rcases hi with rfl | rfl <;> decide
  refine not_hasDecomp_double_ear (a := .inl 3) (a' := .inl 6) (x := .inl 0) (y := .inl 1)
    ?_ (hax 3 (Or.inl rfl)) (hax 6 (Or.inr rfl)) (hN 3 (Or.inl rfl)) (hN 6 (Or.inr rfl)) hdec
  rw [card_insert_of_notMem (by simp), card_insert_of_notMem (by simp), card_pair (by simp)]

/-! ### The pairwise-supply candidate is false -/

/-- Auxiliary vertices of a solution: vertices of `A ∪ Q` outside `Z`. -/
def auxVerts {V : Type*} [Fintype V] [DecidableEq V] (A Q : Finset (Sym2 V)) (Z : Finset V) :
    Finset V :=
  vertSet (A ∪ Q) \ Z

/-- **The Stage 49 candidate** (stated, not proved): uniform `C, N` chosen before the host;
for every certified physical source a bounded two-mode solution exists. -/
def SignedAbsorptionCandidate (α : ℝ) (K : ℕ) : Prop :=
  ∃ C : ℝ, ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 2)
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset (Sym2 V)) (ι : Type) [Fintype ι]
    (t : ι → Finset V) (c : ι → ℤ) (Z : Finset V),
    N ≤ Fintype.card V → (∀ j : Fin 2, ∃ v, p v = j) → AntiEdgeful p F0 G α →
    P ⊆ G.edgeFinset → IsSignedCert p G P t c → certWeight c ≤ K →
    (∀ e ∈ P, ∀ v ∈ e, v ∈ Z) → Z.card ≤ 3 * K →
    ∃ A Q : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Q ⊆ G.edgeFinset ∧ IsTwoMode p P A Q ∧
      (∀ e ∈ Q, ∀ v ∈ e, v ∉ Z) ∧
      pairCount p Q 0 0 = pairCount p P 0 0 ∧ pairCount p Q 1 1 = pairCount p P 1 1 ∧
      pairCount p Q 0 1 = pairCount p P 0 1 ∧
      (A.card : ℝ) ≤ C * K ∧ (Q.card : ℝ) ≤ C * K ∧ ((auxVerts A Q Z).card : ℝ) ≤ C * K

/-- The candidate restricted to **pairwise-supply constructions**: the solution must in
addition be 2-degenerate over `Z`. The size bounds and the part-count conclusion are
dropped; this only weakens the statement, so its refutation is stronger. -/
def PairSupplyCandidate (α : ℝ) (K : ℕ) : Prop :=
  ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 2)
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset (Sym2 V)) (ι : Type) [Fintype ι]
    (t : ι → Finset V) (c : ι → ℤ) (Z : Finset V),
    N ≤ Fintype.card V → (∀ j : Fin 2, ∃ v, p v = j) → AntiEdgeful p F0 G α →
    P ⊆ G.edgeFinset → IsSignedCert p G P t c → certWeight c ≤ K →
    (∀ e ∈ P, ∀ v ∈ e, v ∈ Z) → Z.card ≤ 3 * K →
    ∃ A Q : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Q ⊆ G.edgeFinset ∧ IsTwoMode p P A Q ∧
      (∀ e ∈ Q, ∀ v ∈ e, v ∉ Z) ∧ (∃ r : V → ℕ, IsDegenerateOver (A ∪ P ∪ Q) Z r)

/-- **Localized obstruction.** For `0 < α ≤ 1/5` and `K ≥ 8`, no uniform constants make
pairwise-supply constructions work, already for the double hexagon. -/
theorem not_pairSupplyCandidate (α : ℝ) (hα : α ≤ 1 / 5) (K : ℕ) (hK : 8 ≤ K) :
    ¬ PairSupplyCandidate α K := by
  rintro ⟨N, hC⟩
  set m := max 9 N
  obtain ⟨A, Q, hA, -, h2, hQZ, r, hdeg⟩ := hC (HV m) (part m) (host m) (src m) (Fin 7) (tri m)
    coef (roots m) (by rw [card_HV]; omega) (parts_inhabited m)
    (antiEdgeful m (le_max_left _ _) α hα) (src_subset m) (src_cert m)
    (by rw [certWeight_coef]; exact_mod_cast hK) (src_roots m) (by rw [roots_card]; omega)
  exact no_degenerate_twoMode m A Q r hA hQZ h2 hdeg

end PartitionedTriangleAbsorption.SignedCertificate.DoubleHexagon
