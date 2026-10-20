/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.MoveLedgerStage88

/-! # Selecting fresh physical catalyst triangles for a deployed configuration

For every active vertex `y` of a configuration `Y` whose degrees are all `0`
or `2`, an active incident edge `y w` of `Y` supplies an allowed type
`{p y, p w, k} ∈ F`. We select a fresh physical triangle
`(co y, cs y, ct y)` with `p (co y) = p y` and label multiset
`{p y, p (cs y), p (ct y)} ∈ F`, using only the compatible four-root supply
`CompatibleSupply p F G a` (queries with at most two roots), the forbidden
degree bound on `B`, and an explicit budget. All chosen triples are mutually
vertex-disjoint, avoid a forbidden vertex set `Z₀` (which the caller makes
contain every active vertex), and all their edges are real edges of `G`
outside `B ∪ L`. Their union `D` has an actual decomposition and `|D| ≤ 3|Y|`.
Nothing about the later insertion is assumed here.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CatalystSelectionStage89

open Finset AntiEdgeSelection TypedTransformer PairMoveSelectionStage85

variable {V : Type*} [DecidableEq V] {t : ℕ}

/-- The three edges of the catalyst triangle with centre `o`. -/
def catEdges (o s u : V) : Finset (Sym2 V) := {s(o, s), s(o, u), s(s, u)}

/-- The three vertices of a catalyst triangle. -/
def catVerts (o s u : V) : Finset V := {o, s, u}

theorem triEdges_eq_catEdges {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    triEdges ({x, y, z} : Finset V) = catEdges x y z := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
  simp only [triEdges, catEdges, mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff,
    mem_insert, mem_singleton, Sym2.eq_iff]
  constructor
  · rintro ⟨⟨ha, hb⟩, hab⟩
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> simp_all
  · rintro (h | h | h) <;> rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all [Ne.symm]

/-- One catalyst triangle with an allowed label multiset decomposes. -/
theorem catalyst_decomp {p : V → Fin t} {F : Finset (Multiset (Fin t))} {o s u : V}
    (h1 : o ≠ s) (h2 : o ≠ u) (h3 : s ≠ u) (hl : Link F (p o) (p s) (p u)) :
    HasDecomp p F (catEdges o s u) := by
  refine ⟨{{o, s, u}}, ?_, by simp, by simp [triEdges_eq_catEdges h1 h2 h3]⟩
  intro T hT
  rw [mem_singleton.mp hT]
  refine ⟨?_, ?_⟩
  · rw [card_insert_of_notMem (by simp [h1, h2]), card_pair h3]
  · rw [insert_val_of_notMem (by simp [h1, h2]), insert_val_of_notMem (by simp [h3])]
    simpa [Link] using hl

theorem mem_catVerts_of_mem {o s u v : V} {e : Sym2 V} (he : e ∈ catEdges o s u)
    (hv : v ∈ e) : v ∈ catVerts o s u := by
  simp only [catEdges, mem_insert, mem_singleton] at he
  simp only [catVerts, mem_insert, mem_singleton]
  rcases he with rfl | rfl | rfl <;> simp only [Sym2.mem_iff] at hv <;> tauto

theorem catEdges_card_le (o s u : V) : (catEdges o s u).card ≤ 3 := by
  unfold catEdges
  exact (card_insert_le _ _).trans (Nat.succ_le_succ ((card_insert_le _ _).trans (by simp)))

theorem catVerts_card_le (o s u : V) : (catVerts o s u).card ≤ 3 := by
  unfold catVerts
  exact (card_insert_le _ _).trans (Nat.succ_le_succ ((card_insert_le _ _).trans (by simp)))

/-- Vertex-disjoint catalyst triangles are edge-disjoint. -/
theorem catEdges_disjoint {o s u o' s' u' : V}
    (h : Disjoint (catVerts o s u) (catVerts o' s' u')) :
    Disjoint (catEdges o s u) (catEdges o' s' u') := by
  rw [disjoint_left]
  intro e he he'
  induction e using Sym2.ind with
  | _ a b =>
  exact disjoint_left.mp h (mem_catVerts_of_mem he (Sym2.mem_mk_left a b))
    (mem_catVerts_of_mem he' (Sym2.mem_mk_left a b))

variable [Fintype V]

/-- The properties of a selected catalyst family indexed by `A`. -/
structure Catalysts (p : V → Fin t) (F : Finset (Multiset (Fin t))) (G : SimpleGraph V)
    [DecidableRel G.Adj] (B L : Finset (Sym2 V)) (Z₀ A : Finset V) (co cs ct : V → V) :
    Prop where
  /-- The centre has the label of its active vertex. -/
  label : ∀ y ∈ A, p (co y) = p y
  /-- The label multiset `{p y, p (cs y), p (ct y)}` is an allowed type. -/
  link : ∀ y ∈ A, Link F (p y) (p (cs y)) (p (ct y))
  distinct : ∀ y ∈ A, co y ≠ cs y ∧ co y ≠ ct y ∧ cs y ≠ ct y
  real : ∀ y ∈ A, catEdges (co y) (cs y) (ct y) ⊆ G.edgeFinset
  /-- Every catalyst vertex avoids the forbidden vertex set. -/
  fresh : ∀ y ∈ A, Disjoint (catVerts (co y) (cs y) (ct y)) Z₀
  /-- Distinct active vertices get vertex-disjoint triangles. -/
  vdisj : ∀ y ∈ A, ∀ y' ∈ A, y ≠ y' →
    Disjoint (catVerts (co y) (cs y) (ct y)) (catVerts (co y') (cs y') (ct y'))
  /-- Every catalyst edge avoids `B` and the ledger `L`. -/
  avoid : ∀ y ∈ A, Disjoint (catEdges (co y) (cs y) (ct y)) (B ∪ L)

/-- The union of the selected catalyst triangles. -/
def catUnion (A : Finset V) (co cs ct : V → V) : Finset (Sym2 V) :=
  A.biUnion fun y => catEdges (co y) (cs y) (ct y)

/-- All catalyst vertices. -/
def catVertsAll (A : Finset V) (co cs ct : V → V) : Finset V :=
  A.biUnion fun y => catVerts (co y) (cs y) (ct y)

section

variable {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
  [DecidableRel G.Adj] {B L : Finset (Sym2 V)} {Z₀ A : Finset V} {co cs ct : V → V}

theorem Catalysts.mono {A' : Finset V} (h : Catalysts p F G B L Z₀ A co cs ct) (hA : A' ⊆ A) :
    Catalysts p F G B L Z₀ A' co cs ct :=
  ⟨fun y hy => h.label y (hA hy), fun y hy => h.link y (hA hy),
    fun y hy => h.distinct y (hA hy), fun y hy => h.real y (hA hy),
    fun y hy => h.fresh y (hA hy), fun y hy y' hy' => h.vdisj y (hA hy) y' (hA hy'),
    fun y hy => h.avoid y (hA hy)⟩

omit [Fintype V] in
theorem catUnion_card_le (A : Finset V) (co cs ct : V → V) :
    (catUnion A co cs ct).card ≤ 3 * A.card := by
  unfold catUnion
  refine card_biUnion_le.trans ?_
  calc _ ≤ ∑ _y ∈ A, 3 := sum_le_sum fun y _ => catEdges_card_le _ _ _
    _ = 3 * A.card := by rw [sum_const, smul_eq_mul, Nat.mul_comm]

omit [Fintype V] in
theorem catVertsAll_card_le (A : Finset V) (co cs ct : V → V) :
    (catVertsAll A co cs ct).card ≤ 3 * A.card := by
  unfold catVertsAll
  refine card_biUnion_le.trans ?_
  calc _ ≤ ∑ _y ∈ A, 3 := sum_le_sum fun y _ => catVerts_card_le _ _ _
    _ = 3 * A.card := by rw [sum_const, smul_eq_mul, Nat.mul_comm]

theorem Catalysts.real_union (h : Catalysts p F G B L Z₀ A co cs ct) :
    catUnion A co cs ct ⊆ G.edgeFinset := by
  intro e he
  obtain ⟨y, hy, he⟩ := mem_biUnion.mp he
  exact h.real y hy he

theorem Catalysts.avoid_union (h : Catalysts p F G B L Z₀ A co cs ct) :
    Disjoint (catUnion A co cs ct) (B ∪ L) := by
  rw [disjoint_left]
  intro e he
  obtain ⟨y, hy, he⟩ := mem_biUnion.mp he
  exact disjoint_left.mp (h.avoid y hy) he

theorem Catalysts.fresh_all (h : Catalysts p F G B L Z₀ A co cs ct) :
    Disjoint (catVertsAll A co cs ct) Z₀ := by
  rw [disjoint_left]
  intro v hv
  obtain ⟨y, hy, hv⟩ := mem_biUnion.mp hv
  exact disjoint_left.mp (h.fresh y hy) hv

/-- The union of the catalysts has an actual decomposition. -/
theorem Catalysts.decomp (h : Catalysts p F G B L Z₀ A co cs ct) :
    HasDecomp p F (catUnion A co cs ct) := by
  induction A using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp, by simp [catUnion]⟩
  | @insert y A hy ih =>
    have hA := h.mono (subset_insert y A)
    have hy' : y ∈ insert y A := mem_insert_self y A
    obtain ⟨d1, d2, d3⟩ := h.distinct y hy'
    have hl : Link F (p (co y)) (p (cs y)) (p (ct y)) := by
      rw [h.label y hy']
      exact h.link y hy'
    have hdec := catalyst_decomp d1 d2 d3 hl
    have hdis : Disjoint (catEdges (co y) (cs y) (ct y)) (catUnion A co cs ct) := by
      rw [disjoint_left]
      intro e he he'
      obtain ⟨y', hy'A, he'⟩ := mem_biUnion.mp he'
      have hne : y ≠ y' := fun hh => hy (hh ▸ hy'A)
      exact disjoint_left.mp (catEdges_disjoint
        (h.vdisj y hy' y' (mem_insert_of_mem hy'A) hne)) he he'
    have heq : catUnion (insert y A) co cs ct =
        catEdges (co y) (cs y) (ct y) ∪ catUnion A co cs ct := by
      simp [catUnion, biUnion_insert]
    rw [heq]
    exact hdec.union (ih hA) hdis

end

/-- The selection induction. Each new triangle is chosen by three compatible
queries with at most two roots, avoiding the forbidden vertices `Z₀`, all
previously chosen catalyst vertices, `B`, the ledger `L` and all earlier
catalyst edges. Per triangle the forbidden vertex set grows by three and the
avoided edge set by three; hence the coefficient `3 + 4 * 3 = 15`. -/
theorem select_aux (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (a d : ℝ)
    (hs : CompatibleSupply p F G a) (B L : Finset (Sym2 V)) (hB : DegBounded B d)
    (hd : 0 ≤ d) (Z₀ : Finset V) :
    ∀ A : Finset V, (∀ y ∈ A, ∃ j k, Link F (p y) j k) →
      (Z₀.card : ℝ) + 15 * A.card + 4 * (d + L.card) < a →
      ∃ co cs ct : V → V, Catalysts p F G B L Z₀ A co cs ct := by
  intro A
  induction A using Finset.induction_on with
  | empty =>
    intro _ _
    exact ⟨id, id, id, ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩⟩
  | @insert y A hy ih =>
    intro htype hb
    have hcardA : ((insert y A).card : ℝ) = A.card + 1 := by
      rw [card_insert_of_notMem hy]; push_cast; ring
    obtain ⟨co, cs, ct, hc⟩ := ih (fun y' hy' => htype y' (mem_insert_of_mem hy'))
      (by rw [hcardA] at hb; linarith)
    set W := catVertsAll A co cs ct with hW
    set U := L ∪ catUnion A co cs ct with hU
    set Z := Z₀ ∪ W with hZ
    have hWc : (W.card : ℝ) ≤ 3 * A.card := by exact_mod_cast catVertsAll_card_le A co cs ct
    have hDc : ((catUnion A co cs ct).card : ℝ) ≤ 3 * A.card := by
      exact_mod_cast catUnion_card_le A co cs ct
    have hZc : (Z.card : ℝ) ≤ Z₀.card + 3 * A.card := by
      have : Z.card ≤ Z₀.card + W.card := card_union_le _ _
      have : (Z.card : ℝ) ≤ Z₀.card + W.card := by exact_mod_cast this
      linarith
    have hUc : (U.card : ℝ) ≤ L.card + 3 * A.card := by
      have : U.card ≤ L.card + (catUnion A co cs ct).card := card_union_le _ _
      have : (U.card : ℝ) ≤ L.card + (catUnion A co cs ct).card := by exact_mod_cast this
      linarith
    obtain ⟨j, k, hjk⟩ := htype y (mem_insert_self y A)
    -- the centre
    obtain ⟨o, hpo, -, hoZ, -⟩ := exists_fresh_with_history p F G a d hs ∅ Z (p y)
      (by simp) (by simp [Compatible]) B U hB hd (by rw [hcardA] at hb; linarith)
    -- the second vertex
    have hc₂ : Compatible p F {o} j := by
      intro v hv
      rw [mem_singleton.mp hv, hpo]
      exact ⟨k, (link_root_swap F (p y) j k).mp hjk⟩
    obtain ⟨s, hps, hadj₂, hsZ, he₂⟩ := exists_fresh_with_history p F G a d hs {o}
      (insert o Z) j (by simp) hc₂ B U hB hd (by
        have : ((insert o Z).card : ℝ) ≤ Z.card + 1 := by exact_mod_cast card_insert_le o Z
        rw [hcardA] at hb; linarith)
    -- the third vertex
    have hc₃ : Compatible p F {o, s} k := by
      intro v hv
      simp only [mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl
      · rw [hpo]
        exact ⟨j, rotate_link hjk⟩
      · rw [hps]
        exact ⟨p y, (link_swap F k (p y) j).mp (rotate_link hjk)⟩
    obtain ⟨u, hpu, hadj₃, huZ, he₃⟩ := exists_fresh_with_history p F G a d hs {o, s}
      (insert s (insert o Z)) k (card_insert_le _ _ |>.trans (by simp)) hc₃ B U hB hd (by
        have h1 : ((insert s (insert o Z)).card : ℝ) ≤ (insert o Z).card + 1 := by
          exact_mod_cast card_insert_le _ _
        have h2 : ((insert o Z).card : ℝ) ≤ Z.card + 1 := by exact_mod_cast card_insert_le o Z
        rw [hcardA] at hb; linarith)
    have hso : s ≠ o := by rintro rfl; exact hsZ (mem_insert_self _ _)
    have hus : u ≠ s := by rintro rfl; exact huZ (mem_insert_self _ _)
    have huo : u ≠ o := by rintro rfl; exact huZ (mem_insert_of_mem (mem_insert_self _ _))
    have hsZ' : s ∉ Z := fun h => hsZ (mem_insert_of_mem h)
    have huZ' : u ∉ Z := fun h => huZ (mem_insert_of_mem (mem_insert_of_mem h))
    have hnotZ : ∀ v ∈ catVerts o s u, v ∉ Z := by
      intro v hv
      simp only [catVerts, mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl | rfl <;> assumption
    refine ⟨Function.update co y o, Function.update cs y s, Function.update ct y u, ?_⟩
    have hupd : ∀ y' ∈ A, Function.update co y o y' = co y' ∧
        Function.update cs y s y' = cs y' ∧ Function.update ct y u y' = ct y' := by
      intro y' hy'
      have hne : y' ≠ y := fun h => hy (h ▸ hy')
      simp [Function.update_of_ne hne]
    have hedges : catEdges o s u ⊆ G.edgeFinset ∧ Disjoint (catEdges o s u) (B ∪ L) := by
      have hmem : ∀ e ∈ catEdges o s u, e ∈ G.edgeFinset ∧ e ∉ B ∪ U := by
        intro e he
        simp only [catEdges, mem_insert, mem_singleton] at he
        rcases he with rfl | rfl | rfl
        · exact ⟨by simpa using hadj₂ o (mem_singleton_self o), he₂ o (mem_singleton_self o)⟩
        · exact ⟨by simpa using hadj₃ o (by simp), he₃ o (by simp)⟩
        · exact ⟨by simpa using hadj₃ s (by simp), he₃ s (by simp)⟩
      refine ⟨fun e he => (hmem e he).1, ?_⟩
      rw [disjoint_left]
      intro e he hbl
      apply (hmem e he).2
      simp only [mem_union] at hbl ⊢
      rcases hbl with hbl | hbl
      · exact Or.inl hbl
      · exact Or.inr (mem_union.mpr (Or.inl hbl))
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro y' hy'
      rcases mem_insert.mp hy' with rfl | hy'
      · simpa using hpo
      · rw [(hupd y' hy').1]; exact hc.label y' hy'
    · intro y' hy'
      rcases mem_insert.mp hy' with rfl | hy'
      · simpa [hps, hpu] using hjk
      · rw [(hupd y' hy').2.1, (hupd y' hy').2.2]; exact hc.link y' hy'
    · intro y' hy'
      rcases mem_insert.mp hy' with rfl | hy'
      · simpa using ⟨hso.symm, huo.symm, hus.symm⟩
      · rw [(hupd y' hy').1, (hupd y' hy').2.1, (hupd y' hy').2.2]; exact hc.distinct y' hy'
    · intro y' hy'
      rcases mem_insert.mp hy' with rfl | hy'
      · simpa using hedges.1
      · rw [(hupd y' hy').1, (hupd y' hy').2.1, (hupd y' hy').2.2]; exact hc.real y' hy'
    · intro y' hy'
      rcases mem_insert.mp hy' with rfl | hy'
      · simp only [Function.update_self]
        rw [disjoint_left]
        intro v hv hv0
        exact hnotZ v hv (mem_union.mpr (Or.inl hv0))
      · rw [(hupd y' hy').1, (hupd y' hy').2.1, (hupd y' hy').2.2]; exact hc.fresh y' hy'
    · have hfar : ∀ y' ∈ A, Disjoint (catVerts o s u) (catVerts (co y') (cs y') (ct y')) := by
        intro y' hy'
        rw [disjoint_left]
        intro v hv hv'
        exact hnotZ v hv (mem_union.mpr (Or.inr (mem_biUnion.mpr ⟨y', hy', hv'⟩)))
      intro y₁ hy₁ y₂ hy₂ hne
      by_cases h₁ : y₁ = y <;> by_cases h₂ : y₂ = y
      · exact absurd (h₁.trans h₂.symm) hne
      · subst h₁
        have hy₂ : y₂ ∈ A := (mem_insert.mp hy₂).resolve_left h₂
        rw [(hupd y₂ hy₂).1, (hupd y₂ hy₂).2.1, (hupd y₂ hy₂).2.2]
        simpa using hfar y₂ hy₂
      · subst h₂
        have hy₁ : y₁ ∈ A := (mem_insert.mp hy₁).resolve_left h₁
        rw [(hupd y₁ hy₁).1, (hupd y₁ hy₁).2.1, (hupd y₁ hy₁).2.2]
        simpa using (hfar y₁ hy₁).symm
      · have hy₁ : y₁ ∈ A := (mem_insert.mp hy₁).resolve_left h₁
        have hy₂ : y₂ ∈ A := (mem_insert.mp hy₂).resolve_left h₂
        rw [(hupd y₁ hy₁).1, (hupd y₁ hy₁).2.1, (hupd y₁ hy₁).2.2,
          (hupd y₂ hy₂).1, (hupd y₂ hy₂).2.1, (hupd y₂ hy₂).2.2]
        exact hc.vdisj y₁ hy₁ y₂ hy₂ hne
    · intro y' hy'
      rcases mem_insert.mp hy' with rfl | hy'
      · simpa using hedges.2
      · rw [(hupd y' hy').1, (hupd y' hy').2.1, (hupd y' hy').2.2]; exact hc.avoid y' hy'

/-- The active vertices of a configuration: those of degree two. -/
def active (Y : Finset (Sym2 V)) : Finset V := univ.filter fun v => incidentLoad Y v = 2

/-- In a loopless configuration with all degrees `0` or `2`, the number of
active vertices equals the number of edges (handshake). -/
theorem active_card {Y : Finset (Sym2 V)} (hloop : ∀ e ∈ Y, ¬ e.IsDiag)
    (hdeg : ∀ v, incidentLoad Y v = 0 ∨ incidentLoad Y v = 2) :
    (active Y).card = Y.card := by
  have hsum := PairSplitDeploymentStage87.sum_load hloop
  have hsplit : ∑ v, incidentLoad Y v = ∑ v ∈ active Y, 2 := by
    unfold active
    rw [sum_filter]
    apply sum_congr rfl
    intro v _
    rcases hdeg v with h | h <;> simp [h]
  rw [hsplit, sum_const, smul_eq_mul] at hsum
  omega

/-- Every endpoint of an edge of a `0`/`2`-configuration is active. -/
theorem mem_active_of_mem {Y : Finset (Sym2 V)}
    (hdeg : ∀ v, incidentLoad Y v = 0 ∨ incidentLoad Y v = 2) {e : Sym2 V} (he : e ∈ Y)
    {v : V} (hv : v ∈ e) : v ∈ active Y := by
  have hpos : 0 < incidentLoad Y v := card_pos.mpr ⟨e, mem_filter.mpr ⟨he, hv⟩⟩
  unfold active
  simp only [mem_filter, mem_univ, true_and]
  rcases hdeg v with h | h <;> omega

/-- An active vertex has an incident edge, hence an allowed type containing its label. -/
theorem active_type {F : Finset (Multiset (Fin t))} {p : V → Fin t} {Y : Finset (Sym2 V)}
    (hact : ∀ u v, s(u, v) ∈ Y → ∃ k, Link F (p u) (p v) k) :
    ∀ y ∈ active Y, ∃ j k, Link F (p y) j k := by
  intro y hy
  have h2 : incidentLoad Y y = 2 := (mem_filter.mp hy).2
  obtain ⟨e, he⟩ : (Y.filter fun e => y ∈ e).Nonempty := by
    rw [← card_pos]; unfold incidentLoad at h2; omega
  obtain ⟨he, hye⟩ := mem_filter.mp he
  induction e using Sym2.ind with
  | _ a b =>
  rcases Sym2.mem_iff.mp hye with rfl | rfl
  · obtain ⟨k, hk⟩ := hact _ _ he
    exact ⟨p b, k, hk⟩
  · rw [Sym2.eq_swap] at he
    obtain ⟨k, hk⟩ := hact _ _ he
    exact ⟨p a, k, hk⟩

/-- **Catalyst selection for a deployed configuration.** For a configuration
`Y` of real edges with every degree `0` or `2` and active edge types, select
for every active vertex `y` a fresh catalyst triangle `(co y, cs y, ct y)`
with `p (co y) = p y` and allowed label multiset `{p y, p (cs y), p (ct y)}`.
The triangles are mutually vertex-disjoint, avoid `Z₀` (which contains the
active support of `Y`), and have real edges outside `B ∪ L`. Their union `D`
decomposes, is real, avoids `B ∪ L`, and `|D| ≤ 3|Y|`; the number of active
vertices equals `|Y|`. Explicit budget: `|Z₀| + 15|Y| + 4(d + |L|) < a`. -/
theorem select_catalysts (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (a d : ℝ)
    (hs : CompatibleSupply p F G a) (B L Y : Finset (Sym2 V)) (Z₀ : Finset V)
    (hB : DegBounded B d) (hd : 0 ≤ d) (hYG : Y ⊆ G.edgeFinset)
    (hdeg : ∀ v, incidentLoad Y v = 0 ∨ incidentLoad Y v = 2)
    (hact : ∀ u v, s(u, v) ∈ Y → ∃ k, Link F (p u) (p v) k)
    (hZ : ∀ e ∈ Y, ∀ v ∈ e, v ∈ Z₀)
    (hb : (Z₀.card : ℝ) + 15 * Y.card + 4 * (d + L.card) < a) :
    ∃ co cs ct : V → V, Catalysts p F G B L Z₀ (active Y) co cs ct ∧
      (active Y).card = Y.card ∧ active Y ⊆ Z₀ ∧
      HasDecomp p F (catUnion (active Y) co cs ct) ∧
      catUnion (active Y) co cs ct ⊆ G.edgeFinset ∧
      Disjoint (catUnion (active Y) co cs ct) (B ∪ L) ∧
      (catUnion (active Y) co cs ct).card ≤ 3 * Y.card := by
  have hloop : ∀ e ∈ Y, ¬ e.IsDiag := fun e he =>
    G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (hYG he))
  have hcard := active_card hloop hdeg
  obtain ⟨co, cs, ct, hc⟩ := select_aux p F G a d hs B L hB hd Z₀ (active Y)
    (active_type hact) (by rw [hcard]; exact hb)
  have hAZ : active Y ⊆ Z₀ := by
    intro v hv
    have h2 : incidentLoad Y v = 2 := (mem_filter.mp hv).2
    obtain ⟨e, he⟩ : (Y.filter fun e => v ∈ e).Nonempty := by
      rw [← card_pos]; unfold incidentLoad at h2; omega
    exact hZ e (mem_filter.mp he).1 v (mem_filter.mp he).2
  refine ⟨co, cs, ct, hc, hcard, hAZ, hc.decomp, hc.real_union, hc.avoid_union, ?_⟩
  rw [← hcard]
  exact catUnion_card_le _ _ _ _

end PartitionedTriangleAbsorption.CatalystSelectionStage89
