/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.VertexTransportStage268

@[expose] public section

/-!
# Robust parity filling of physical quadrilaterals (Stage 256, formalized)

For a finite simple graph `G` on `n` vertices with `n ≤ deg v + (1/4 + ε) n` for every `v`
(i.e. `δ(G) ≥ (3/4 - ε) n`), `0 ≤ ε ≤ 1/20`, which is not `a`-extremal for some `a ≥ 8ε`
(raw Definition 12.2 formula, as in Stage 265), every physical closed walk `a b c d` of length
four is, modulo two, a sum of at most `28` actual triangles of `G`:
`[ab] + [bc] + [cd] + [da] = g + 2 h`, where `g` has a physical `PhysCostZ` certificate of cost
`≤ 28` and `h` is an integer edge function supported on `E(G)`.

The proof is the alternative of Stage 256: either `b, d` are joined by a path in the common link
`G[N(a) ∩ N(c)]`, or `a, c` by a path in `G[N(b) ∩ N(d)]`; if both fail, `G` is extremal.  Paths
have length `≤ 14` (closed neighbourhoods along a shortest path).  Note that the extremality
margin needed is only `8ε ≤ a` (the note uses `32ε`).
-/

namespace NashWilliams18.ParityFill

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.BlowupB
  PartitionedTriangleAbsorption.OnePart

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An integer edge function supported on the edges of `G`. -/
def GEdge (G : SimpleGraph V) (h : Sym2 V → ℤ) : Prop := ∀ e, h e ≠ 0 → e ∈ G.edgeSet

omit [Fintype V] [DecidableEq V] in
theorem GEdge.zero (G : SimpleGraph V) : GEdge G (0 : Sym2 V → ℤ) := fun _ h => (h rfl).elim

omit [Fintype V] [DecidableEq V] in
theorem GEdge.add {G : SimpleGraph V} {f g : Sym2 V → ℤ} (hf : GEdge G f) (hg : GEdge G g) :
    GEdge G (f + g) := by
  intro e he
  by_contra hn
  exact he (by simp [show f e = 0 by by_contra h; exact hn (hf e h),
    show g e = 0 by by_contra h; exact hn (hg e h)])

omit [Fintype V] [DecidableEq V] in
theorem GEdge.neg {G : SimpleGraph V} {f : Sym2 V → ℤ} (hf : GEdge G f) : GEdge G (-f) :=
  fun e he => hf e (by simpa using he)

omit [Fintype V] [DecidableEq V] in
theorem GEdge.sub {G : SimpleGraph V} {f g : Sym2 V → ℤ} (hf : GEdge G f) (hg : GEdge G g) :
    GEdge G (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

omit [Fintype V] [DecidableEq V] in
theorem GEdge.smul {G : SimpleGraph V} {f : Sym2 V → ℤ} (hf : GEdge G f) (c : ℤ) :
    GEdge G (c • f) := fun e he => hf e (by
  intro h0; apply he; simp [h0])

omit [Fintype V] [DecidableEq V] in
theorem GEdge.sum {G : SimpleGraph V} {ι : Type*} (s : Finset ι) (f : ι → Sym2 V → ℤ)
    (h : ∀ i ∈ s, GEdge G (f i)) : GEdge G (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GEdge.zero G
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

omit [Fintype V] in
theorem GEdge.ind1 {G : SimpleGraph V} {u v : V} (h : G.Adj u v) : GEdge G (ind1 s(u, v)) := by
  intro e he
  rw [ind1_apply] at he
  split_ifs at he with hh
  · subst hh; exact h
  · exact (he rfl).elim

open scoped Classical in
/-- The raw `a`-extremality formula of Definition 12.2 (verbatim as in Stage 265). -/
def ExtrF (G : SimpleGraph V) [DecidableRel G.Adj] (a : ℝ) : Prop :=
  (1 - a) * Fintype.card V ≤
      ((univ.filter (fun w => (G.degree w : ℝ) ≤ (3 / 4 + a) * Fintype.card V)).card : ℝ) ∧
    ∃ T : Finset V, (1 - a) * (Fintype.card V : ℝ) ^ 2 / 4 ≤
      ((G.edgeFinset.filter (fun edge => ∃ x y, edge = s(x, y) ∧ x ∈ T ∧ y ∉ T)).card : ℝ)

/-- The common link of `r, s`. -/
def link (G : SimpleGraph V) [DecidableRel G.Adj] (r s : V) : Finset V :=
  univ.filter (fun x => G.Adj r x ∧ G.Adj s x)

/-- The two spokes from `r, s` to `x`. -/
def spoke (r s x : V) : Sym2 V → ℤ := ind1 s(r, x) + ind1 s(s, x)

/-- The closed walk `a b c d` as an integer edge function. -/
def quad (a b c d : V) : Sym2 V → ℤ := ind1 s(a, b) + ind1 s(b, c) + ind1 s(c, d) + ind1 s(d, a)

omit [Fintype V] in
/-- A triangle has a physical certificate of cost `1`. -/
theorem tri_cost (G : SimpleGraph V) {u v w : V}
    (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w) :
    PhysCostZ part1 triFam G (ind1 s(u, v) + ind1 s(u, w) + ind1 s(v, w)) 1 := by
  have h := SignedTransportStage265.triangle_cost G huv huw hvw
  rwa [indZ_triEdges_three huv.ne huw.ne hvw.ne] at h

/-- **Filling along a link path.** A walk `x → y` in the common link of `r, s` gives
`spoke x + spoke y = g + 2h` with `g` of cost `≤ 2·length`. -/
theorem link_walk_fill (G : SimpleGraph V) [DecidableRel G.Adj] (r s : V) :
    ∀ {x y : (↑(link G r s) : Set V)} (p : (G.induce (↑(link G r s) : Set V)).Walk x y),
    ∃ g h : Sym2 V → ℤ, PhysCostZ part1 triFam G g (2 * (p.length : ℤ)) ∧ GEdge G h ∧
      spoke r s x.val + spoke r s y.val = g + (2 : ℤ) • h := by
  intro x y p
  induction p with
  | nil =>
    rename_i x
    have hx := (mem_filter.mp (show x.val ∈ link G r s from x.property)).2
    refine ⟨0, spoke r s x.val, by simpa using PhysCostZ.zero part1 triFam G,
      (GEdge.ind1 hx.1).add (GEdge.ind1 hx.2), ?_⟩
    funext e; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]; ring
  | @cons x z y hxz p ih =>
    obtain ⟨g, h, hg, hh, he⟩ := ih
    have hx := (mem_filter.mp (show x.val ∈ link G r s from x.property)).2
    have hz := (mem_filter.mp (show z.val ∈ link G r s from z.property)).2
    have hxz' : G.Adj x.val z.val := hxz
    have t1 := tri_cost G hx.1 hz.1 hxz'
    have t2 := tri_cost G hx.2 hz.2 hxz'
    refine ⟨_ + _ + g, h - ind1 s(x.val, z.val) - spoke r s z.val,
      ((t1.add t2).add hg).mono (by rw [SimpleGraph.Walk.length_cons]; push_cast; linarith), ?_, ?_⟩
    · exact (hh.sub (GEdge.ind1 hxz')).sub ((GEdge.ind1 hz.1).add (GEdge.ind1 hz.2))
    · have he' := congrFun he
      funext e
      have := he' e
      simp only [spoke, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at this ⊢
      linarith

/-! ### Splitting a link that does not connect two of its vertices -/

/-- If `x, y ∈ L` are not joined in `G[L]`, then (with `q`-bounded non-degrees) every `u ∈ L`
has degree `≤ n - |L| + q`, at most `q` neighbours in `L`, and is not adjacent to both `x, y`. -/
theorem link_split (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℝ)
    (hdeg : ∀ v, (Fintype.card V : ℝ) ≤ G.degree v + q) (L : Finset V)
    {x y : V} (hx : x ∈ L) (hy : y ∈ L)
    (hnr : ¬ (G.induce (↑L : Set V)).Reachable ⟨x, hx⟩ ⟨y, hy⟩) :
    ∀ u ∈ L, (G.degree u : ℝ) ≤ Fintype.card V - L.card + q ∧
      ((L.filter (G.Adj u)).card : ℝ) ≤ q ∧ ¬ (G.Adj x u ∧ G.Adj y u) := by
  classical
  let H := G.induce (↑L : Set V)
  let A := L.filter (fun z => ∃ hz : z ∈ L, H.Reachable ⟨x, hx⟩ ⟨z, hz⟩)
  let B := L \ A
  have hAL : A ⊆ L := filter_subset _ _
  have hxA : x ∈ A := mem_filter.mpr ⟨hx, hx, SimpleGraph.Reachable.refl _⟩
  have hyB : y ∈ B := by
    refine mem_sdiff.mpr ⟨hy, fun h => ?_⟩
    obtain ⟨_, hz, hr⟩ := mem_filter.mp h
    exact hnr hr
  -- no edges between `A` and `B`
  have hnoAB : ∀ u ∈ A, ∀ v ∈ B, ¬ G.Adj u v := by
    intro u hu v hv huv
    obtain ⟨huL, _, hr⟩ := mem_filter.mp hu
    obtain ⟨hvL, hvA⟩ := mem_sdiff.mp hv
    apply hvA
    refine mem_filter.mpr ⟨hvL, hvL, hr.trans ?_⟩
    exact (show H.Adj ⟨u, huL⟩ ⟨v, hvL⟩ from huv).reachable
  have hfA : ∀ u ∈ A, L.filter (G.Adj u) ⊆ A := by
    intro u hu v hv
    obtain ⟨hvL, huv⟩ := mem_filter.mp hv
    by_contra hvA
    exact hnoAB u hu v (mem_sdiff.mpr ⟨hvL, hvA⟩) huv
  have hfB : ∀ u ∈ B, L.filter (G.Adj u) ⊆ B := by
    intro u hu v hv
    obtain ⟨hvL, huv⟩ := mem_filter.mp hv
    refine mem_sdiff.mpr ⟨hvL, fun hvA => ?_⟩
    exact hnoAB v hvA u hu huv.symm
  have hrl := fun v => TriangleFreeCoreStage260.restricted_degree_lower G q hdeg L v
  have hAcard : (L.card : ℝ) - q ≤ A.card := by
    have := card_le_card (hfA x hxA)
    have h2 := hrl x
    have : ((L.filter (G.Adj x)).card : ℝ) ≤ A.card := by exact_mod_cast this
    linarith
  have hBcard : (L.card : ℝ) - q ≤ B.card := by
    have := card_le_card (hfB y hyB)
    have h2 := hrl y
    have : ((L.filter (G.Adj y)).card : ℝ) ≤ B.card := by exact_mod_cast this
    linarith
  have hABL : (A.card : ℝ) + B.card = L.card := by
    have h' : B.card + A.card = L.card := card_sdiff_add_card_eq_card hAL
    exact_mod_cast (by omega : A.card + B.card = L.card)
  have hdegle : ∀ u (C : Finset V), (∀ v ∈ C, ¬ G.Adj u v) →
      (G.degree u : ℝ) ≤ Fintype.card V - C.card := by
    intro u C hC
    have hsub : G.neighborFinset u ⊆ univ \ C := by
      intro v hv
      exact mem_sdiff.mpr ⟨mem_univ _, fun hvC => hC v hvC ((G.mem_neighborFinset u v).mp hv)⟩
    have := card_le_card hsub
    rw [card_sdiff_of_subset (subset_univ C), card_univ,
      SimpleGraph.card_neighborFinset_eq_degree] at this
    have hC := card_le_univ C
    have : (G.degree u : ℝ) ≤ ((Fintype.card V - C.card : ℕ) : ℝ) := by exact_mod_cast this
    rwa [Nat.cast_sub hC] at this
  intro u hu
  by_cases huA : u ∈ A
  · refine ⟨?_, ?_, ?_⟩
    · have := hdegle u B (fun v hv => hnoAB u huA v hv)
      linarith
    · have := card_le_card (hfA u huA)
      have : ((L.filter (G.Adj u)).card : ℝ) ≤ A.card := by exact_mod_cast this
      linarith
    · rintro ⟨_, hyu⟩
      exact hnoAB u huA y hyB hyu.symm
  · have huB : u ∈ B := mem_sdiff.mpr ⟨hu, huA⟩
    refine ⟨?_, ?_, ?_⟩
    · have := hdegle u A (fun v hv h => hnoAB v hv u huB h.symm)
      linarith
    · have := card_le_card (hfB u huB)
      have : ((L.filter (G.Adj u)).card : ℝ) ≤ B.card := by exact_mod_cast this
      linarith
    · rintro ⟨hxu, _⟩
      exact hnoAB x hxA u huB hxu

omit [DecidableEq V] in
/-- `u ∈ link G r s ↔ r ~ u ∧ s ~ u`. -/
theorem mem_link {G : SimpleGraph V} [DecidableRel G.Adj] {r s u : V} :
    u ∈ link G r s ↔ G.Adj r u ∧ G.Adj s u := by simp [link]

/-- **Both link paths fail ⇒ extremal** (Stage 256, §1–2).  If `b, d` are not joined in
`G[N(a) ∩ N(c)]` and `a, c` are not joined in `G[N(b) ∩ N(d)]`, then `G` is `a₀`-extremal
whenever `8ε ≤ a₀`. -/
theorem extremal_of_both_links_fail (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε a₀ : ℝ) (he : 0 ≤ ε) (he1 : ε ≤ 1 / 20) (ha : 8 * ε ≤ a₀)
    (hdeg : ∀ v, (Fintype.card V : ℝ) ≤ G.degree v + (1 / 4 + ε) * Fintype.card V)
    {a b c d : V} (hb : b ∈ link G a c) (hd : d ∈ link G a c)
    (ha' : a ∈ link G b d) (hc : c ∈ link G b d)
    (hS : ¬ (G.induce (↑(link G a c) : Set V)).Reachable ⟨b, hb⟩ ⟨d, hd⟩)
    (hT : ¬ (G.induce (↑(link G b d) : Set V)).Reachable ⟨a, ha'⟩ ⟨c, hc⟩) :
    ExtrF G a₀ := by
  classical
  set n : ℝ := ((Fintype.card V : ℕ) : ℝ) with hn
  set q : ℝ := (1 / 4 + ε) * n with hq
  have hn0 : 0 ≤ n := by positivity
  set S := link G a c
  set T := link G b d
  have hSq := link_split G q hdeg S hb hd hS
  have hTq := link_split G q hdeg T ha' hc hT
  have hSlo : n - 2 * q ≤ S.card := TriangleFreeCoreStage260.common_link_size_lower G q hdeg a c
  have hTlo : n - 2 * q ≤ T.card := TriangleFreeCoreStage260.common_link_size_lower G q hdeg b d
  have hdisj : Disjoint S T := by
    rw [disjoint_left]
    intro u huS huT
    exact (hSq u huS).2.2 (mem_link.mp huT)
  have hlowS : ∀ u ∈ S, (G.degree u : ℝ) ≤ (3 / 4 + a₀) * n := by
    intro u hu
    have := (hSq u hu).1
    nlinarith
  have hlowT : ∀ u ∈ T, (G.degree u : ℝ) ≤ (3 / 4 + a₀) * n := by
    intro u hu
    have := (hTq u hu).1
    nlinarith
  refine ⟨?_, S, ?_⟩
  · have hsub : S ∪ T ⊆ univ.filter (fun w => (G.degree w : ℝ) ≤ (3 / 4 + a₀) * n) := by
      intro u hu
      rcases mem_union.mp hu with hu | hu
      · exact mem_filter.mpr ⟨mem_univ _, hlowS u hu⟩
      · exact mem_filter.mpr ⟨mem_univ _, hlowT u hu⟩
    have h1 := card_le_card hsub
    rw [card_union_of_disjoint hdisj] at h1
    have h2 : (S.card : ℝ) + T.card ≤
        ((univ.filter (fun w => (G.degree w : ℝ) ≤ (3 / 4 + a₀) * n)).card : ℝ) := by
      exact_mod_cast h1
    have : (1 - a₀) * n ≤ (S.card : ℝ) + T.card := by nlinarith
    convert this.trans h2 using 3
  · have hcut := TriangleFreeCoreStage260.cross_degree_sum_le_cut G S
    have hrow : ∀ u ∈ S, n - 2 * q ≤
        ((univ.filter (fun y => G.Adj u y ∧ y ∉ S)).card : ℝ) := by
      intro u hu
      have hsplit : G.neighborFinset u ⊆
          S.filter (G.Adj u) ∪ univ.filter (fun y => G.Adj u y ∧ y ∉ S) := by
        intro y hy
        have hy' := (G.mem_neighborFinset u y).mp hy
        by_cases hyS : y ∈ S
        · exact mem_union_left _ (mem_filter.mpr ⟨hyS, hy'⟩)
        · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, hy', hyS⟩)
      have h1 := (card_le_card hsplit).trans (card_union_le _ _)
      rw [SimpleGraph.card_neighborFinset_eq_degree] at h1
      have h2 : (G.degree u : ℝ) ≤ (S.filter (G.Adj u)).card +
          (univ.filter (fun y => G.Adj u y ∧ y ∉ S)).card := by exact_mod_cast h1
      have := (hSq u hu).2.1
      have := hdeg u
      linarith
    have hsum : (S.card : ℝ) * (n - 2 * q) ≤
        ∑ x ∈ S, ((univ.filter (fun y => G.Adj x y ∧ y ∉ S)).card : ℝ) := by
      have := sum_le_sum hrow
      rw [sum_const, nsmul_eq_mul] at this
      exact this
    have hnq : 0 ≤ n - 2 * q := by nlinarith
    have hsq : (n - 2 * q) * (n - 2 * q) ≤ (S.card : ℝ) * (n - 2 * q) :=
      mul_le_mul_of_nonneg_right hSlo hnq
    have hfin : (1 - a₀) * n ^ 2 / 4 ≤ (n - 2 * q) * (n - 2 * q) := by
      rw [hq]; nlinarith [sq_nonneg n, sq_nonneg ε]
    have := hfin.trans (hsq.trans (hsum.trans hcut))
    convert this using 3

omit [DecidableEq V] in
/-- **Short link paths** (Stage 256, §3): inside a common link, reachable vertices are joined
by a walk of length `≤ 14`. -/
theorem link_short_walk (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (he1 : ε ≤ 1 / 20)
    (hdeg : ∀ v, (Fintype.card V : ℝ) ≤ G.degree v + (1 / 4 + ε) * Fintype.card V)
    (r s : V) {x y : (↑(link G r s) : Set V)}
    (hr : (G.induce (↑(link G r s) : Set V)).Reachable x y) :
    ∃ p : (G.induce (↑(link G r s) : Set V)).Walk x y, p.length ≤ 14 := by
  classical
  set n : ℝ := ((Fintype.card V : ℕ) : ℝ)
  set q : ℝ := (1 / 4 + ε) * n
  have hn0 : 0 ≤ n := by positivity
  have hlo : n - 2 * q ≤ (link G r s).card :=
    TriangleFreeCoreStage260.common_link_size_lower G q hdeg r s
  obtain ⟨p, _, hp⟩ := GoodRemaindersStage261.reachable_walk_le_fourteen _ (fun z => by
    rw [GoodRemaindersStage261.induced_degree_eq_filter G (link G r s) z]
    have h1 := TriangleFreeCoreStage260.restricted_degree_lower G q hdeg (link G r s) z.val
    have hc : Fintype.card (↑(link G r s) : Set V) = (link G r s).card := by simp
    rw [hc]
    have h13 : 13 * q ≤ 4 * n := by simp only [q]; nlinarith
    have : ((link G r s).card : ℝ) ≤ 5 * ((link G r s).filter (G.Adj z.val)).card := by
      linarith
    exact_mod_cast this) hr
  exact ⟨p, hp⟩

/-- **Robust parity filling of a physical quadrilateral** (Stage 256).  If `G` has
`δ ≥ (3/4 - ε) n` with `0 ≤ ε ≤ 1/20` and is not `a₀`-extremal with `8ε ≤ a₀`, then every closed
walk `a b c d` of `G` satisfies `[ab]+[bc]+[cd]+[da] = g + 2h` with `g` certified by at most `28`
actual triangles of `G` and `h` supported on `E(G)`. -/
theorem quad_fill (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε a₀ : ℝ) (he : 0 ≤ ε) (he1 : ε ≤ 1 / 20) (ha : 8 * ε ≤ a₀)
    (hdeg : ∀ v, (Fintype.card V : ℝ) ≤ G.degree v + (1 / 4 + ε) * Fintype.card V)
    (hnot : ¬ ExtrF G a₀)
    {a b c d : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a) :
    ∃ g h : Sym2 V → ℤ, PhysCostZ part1 triFam G g 28 ∧ GEdge G h ∧
      quad a b c d = g + (2 : ℤ) • h := by
  classical
  have h0 : PhysCostZ part1 triFam G (0 : Sym2 V → ℤ) 28 :=
    (PhysCostZ.zero part1 triFam G).mono (by norm_num)
  by_cases hac : a = c
  · subst hac
    refine ⟨0, ind1 s(a, b) + ind1 s(a, d), h0,
      (GEdge.ind1 hab).add (GEdge.ind1 hda.symm), ?_⟩
    funext e
    simp only [quad, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Sym2.eq_swap (a := b) (b := a), Sym2.eq_swap (a := d) (b := a)]
    ring
  by_cases hbd : b = d
  · subst hbd
    refine ⟨0, ind1 s(a, b) + ind1 s(b, c), h0,
      (GEdge.ind1 hab).add (GEdge.ind1 hbc), ?_⟩
    funext e
    simp only [quad, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Sym2.eq_swap (a := c) (b := b), Sym2.eq_swap (a := b) (b := a)]
    ring
  have hb : b ∈ link G a c := mem_link.mpr ⟨hab, hbc.symm⟩
  have hd : d ∈ link G a c := mem_link.mpr ⟨hda.symm, hcd⟩
  have ha' : a ∈ link G b d := mem_link.mpr ⟨hab.symm, hda⟩
  have hc : c ∈ link G b d := mem_link.mpr ⟨hbc, hcd.symm⟩
  by_cases hS : (G.induce (↑(link G a c) : Set V)).Reachable ⟨b, hb⟩ ⟨d, hd⟩
  · obtain ⟨p, hp⟩ := link_short_walk G ε he1 hdeg a c hS
    obtain ⟨g, h, hg, hh, heq⟩ := link_walk_fill G a c p
    refine ⟨g, h, hg.mono (by push_cast; linarith [(by exact_mod_cast hp : (p.length : ℤ) ≤ 14)]),
      hh, ?_⟩
    rw [← heq]
    funext e
    simp only [quad, spoke, Pi.add_apply, Sym2.eq_swap (a := c) (b := b),
      Sym2.eq_swap (a := a) (b := d)]
    ring
  by_cases hT : (G.induce (↑(link G b d) : Set V)).Reachable ⟨a, ha'⟩ ⟨c, hc⟩
  · obtain ⟨p, hp⟩ := link_short_walk G ε he1 hdeg b d hT
    obtain ⟨g, h, hg, hh, heq⟩ := link_walk_fill G b d p
    refine ⟨g, h, hg.mono (by push_cast; linarith [(by exact_mod_cast hp : (p.length : ℤ) ≤ 14)]),
      hh, ?_⟩
    rw [← heq]
    funext e
    simp only [quad, spoke, Pi.add_apply, Sym2.eq_swap (a := b) (b := a),
      Sym2.eq_swap (a := d) (b := c)]
    ring
  exact (hnot (extremal_of_both_links_fail G ε a₀ he he1 ha hdeg hb hd ha' hc hS hT)).elim

end NashWilliams18.ParityFill
