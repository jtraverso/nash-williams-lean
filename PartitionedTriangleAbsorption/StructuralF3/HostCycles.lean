/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.StructuralF3.Characterization
public import PartitionedTriangleAbsorption.AntiEdgeFamily
public import PartitionedTriangleAbsorption.UniversalRefiner.Loads

/-! # Edge-disjoint typed rectangles in the complete four-class host

Host: `cls : V → Fin 4`, `G.Adj a b ↔ cls a ≠ cls b`, every class of size at least `γ n`.

A *rectangle of kind* `ρ ∈ {1, 2, 3}` is a four-cycle `a - x - b - y - a` with
`cls a = 0`, `cls b = ρ` and `{cls x, cls y}` the two remaining classes. Its edges use exactly
two of the three class matchings `{01,23}`, `{02,13}`, `{03,12}`, each twice, so its two F3
charges are fixed numbers depending only on `ρ` (`c4charge`):

| kind | classes | `chi3a` | `chi3b` |
|------|---------|---------|---------|
| 1    | 0-2-1-3 | `-4`    | `-4`    |
| 2    | 0-1-2-3 | `+4`    | `0`     |
| 3    | 0-1-3-2 | `0`     | `+4`    |

`exists_rectangles`: any finite list of rectangle kinds is realized by pairwise edge-disjoint
physical rectangles avoiding a given sparse edge set, with explicit vertex loads. The roots
`a, b` are spread over the classes by a fixed enumeration; the middles are chosen by the
accepted selection theorem `AntiEdgeSelection.exists_compatible_family`, whose two middle
requests per rectangle use different classes.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.StructuralF3

open Finset AntiEdgeSelection TypedApplicationLinks TypedRefinerCharge

/-- The two middle classes of a rectangle of kind `ρ`. -/
def mid (ρ : Fin 4) (b : Bool) : Fin 4 :=
  match ρ, b with
  | 1, false => 2
  | 1, true => 3
  | 2, false => 1
  | 2, true => 3
  | _, false => 1
  | _, true => 2

theorem mid_spec : ∀ ρ : Fin 4, ρ ≠ 0 → ∀ b : Bool,
    mid ρ b ≠ 0 ∧ mid ρ b ≠ ρ ∧ mid ρ false ≠ mid ρ true := by decide

/-- The charge of a rectangle of kind `ρ` for a weight matrix `χ`, read off from the classes. -/
def c4charge (χ : Fin 4 → Fin 4 → ℤ) (ρ : Fin 4) : ℤ :=
  (χ 0 (mid ρ false) + χ (mid ρ false) 0) + (χ (mid ρ false) ρ + χ ρ (mid ρ false)) +
    (χ 0 (mid ρ true) + χ (mid ρ true) 0) + (χ (mid ρ true) ρ + χ ρ (mid ρ true))

theorem c4charge_values :
    c4charge chi3a 1 = -4 ∧ c4charge chi3b 1 = -4 ∧
    c4charge chi3a 2 = 4 ∧ c4charge chi3b 2 = 0 ∧
    c4charge chi3a 3 = 0 ∧ c4charge chi3b 3 = 4 := by
  unfold c4charge chi3a chi3b mid
  decide

theorem F3_distinct : ∀ i j k : Fin 4, ({i, j, k} : Multiset (Fin 4)) ∈ F3 →
    i ≠ j ∧ i ≠ k ∧ j ≠ k := by
  unfold F3; decide

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- The complete four-class host is anti-edgeful for the structural family. -/
theorem antiEdgeful_host [Fintype V] (cls : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ a b, G.Adj a b ↔ cls a ≠ cls b) (γ : ℝ)
    (hcls : ∀ i, γ * Fintype.card V ≤ ((univ.filter fun v => cls v = i).card : ℝ)) :
    AntiEdgeful cls F3 G γ := by
  intro τ hτ i j k hijk u v _ hu hv
  subst hijk
  obtain ⟨-, hik, hjk⟩ := F3_distinct i j k hτ
  refine (hcls k).trans ?_
  exact_mod_cast card_le_card fun w hw => by
    have hwk := (mem_filter.mp hw).2
    refine mem_filter.mpr ⟨mem_univ _, (hG u w).mpr ?_, (hG w v).mpr ?_, hwk⟩
    · rw [hu, hwk]; exact hik
    · rw [hv, hwk]; exact Ne.symm hjk

/-! ### Spreading roots over a class -/

/-- The `k`-th vertex of `S`, cyclically (with a fallback for empty `S`). -/
noncomputable def cyc (S : Finset V) (v0 : V) (k : ℕ) : V :=
  if h : 0 < S.card then (S.equivFin.symm ⟨k % S.card, Nat.mod_lt _ h⟩ : V) else v0

omit [DecidableEq V] in
theorem cyc_mem {S : Finset V} (v0 : V) (h : 0 < S.card) (k : ℕ) : cyc S v0 k ∈ S := by
  unfold cyc; rw [dite_eq_left h]; exact (S.equivFin.symm _).2

theorem card_cyc_le {S : Finset V} (v0 : V) (h : 0 < S.card) (K : ℕ) (x : V) :
    ((range K).filter fun k => cyc S v0 k = x).card ≤ K / S.card + 1 := by
  by_cases hx : x ∈ S
  · set i := (S.equivFin ⟨x, hx⟩ : ℕ)
    refine (card_le_card ?_).trans (UniversalRefiner.card_filter_add_mod_le K 0 S.card i)
    intro k hk
    obtain ⟨hk, hkx⟩ := mem_filter.mp hk
    refine mem_filter.mpr ⟨hk, ?_⟩
    unfold cyc at hkx
    rw [dite_eq_left h] at hkx
    have : S.equivFin.symm ⟨k % S.card, Nat.mod_lt _ h⟩ = ⟨x, hx⟩ := Subtype.ext hkx
    have h2 := congrArg (fun y => (S.equivFin y : ℕ)) this
    simp only [Equiv.apply_symm_apply] at h2
    simpa [i] using h2
  · rw [card_eq_zero.mpr]
    · exact Nat.zero_le _
    · exact filter_eq_empty_iff.mpr fun k _ hk => hx (hk ▸ cyc_mem v0 h k)

/-! ### Rectangle requests -/

/-- Vertices of class `i`. -/
def classSet [Fintype V] (cls : V → Fin 4) (i : Fin 4) : Finset V := univ.filter fun v => cls v = i

/-- The edge set of the rectangle `a - x - b - y - a`. -/
def rect (a b x y : V) : Finset (Sym2 V) := pathEdges a b x ∪ pathEdges a b y

theorem incidentLoad_pathEdges {u v w : V} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (z : V) :
    incidentLoad (pathEdges u v w) z =
      (if u = z then 1 else 0) + (if v = z then 1 else 0) + 2 * (if w = z then 1 else 0) := by
  have hne : s(u, w) ≠ s(v, w) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact huv h1
    · exact huw h1
  have heq : pathEdges u v w = {s(u, w)} ∪ {s(v, w)} := by simp [pathEdges]
  unfold incidentLoad
  rw [heq, filter_union, card_union_of_disjoint (disjoint_filter_filter
    (disjoint_singleton.mpr hne))]
  rw [filter_singleton, filter_singleton]
  split_ifs <;> grind


theorem rootLoad_cyc_le [Fintype V] (cls : V → Fin 4) (v0 : V)
    (hpos : ∀ i, 0 < (classSet cls i).card) (K : ℕ) (ρ : ℕ → Fin 4)
    (r : ℕ) (hr : ∀ i, 4 * (K / (classSet cls i).card + 1) ≤ r) (z : V) :
    rootLoad ((range K) ×ˢ (univ : Finset Bool)) (fun i => cyc (classSet cls 0) v0 i.1)
      (fun i => cyc (classSet cls (ρ i.1)) v0 i.1) z ≤ r := by
  unfold rootLoad
  beta_reduce
  have h1 : (((range K) ×ˢ (univ : Finset Bool)).filter
      fun i => cyc (classSet cls 0) v0 i.1 = z).card ≤ 2 * (K / (classSet cls 0).card + 1) := by
    rw [filter_product_left (fun k => cyc (classSet cls 0) v0 k = z), card_product, card_univ,
      Fintype.card_bool, mul_comm]
    exact Nat.mul_le_mul_left 2 (card_cyc_le v0 (hpos 0) K z)
  have h2 : (((range K) ×ˢ (univ : Finset Bool)).filter
      fun i => cyc (classSet cls (ρ i.1)) v0 i.1 = z).card ≤
        2 * (K / (classSet cls (cls z)).card + 1) := by
    rw [filter_product_left (fun k => cyc (classSet cls (ρ k)) v0 k = z), card_product,
      card_univ, Fintype.card_bool, mul_comm]
    refine Nat.mul_le_mul_left 2 ((card_le_card fun k hk => ?_).trans
      (card_cyc_le v0 (hpos (cls z)) K z))
    obtain ⟨hk, hkz⟩ := mem_filter.mp hk
    refine mem_filter.mpr ⟨hk, ?_⟩
    have hmem := cyc_mem v0 (hpos (ρ k)) k
    rw [hkz] at hmem
    have hc : cls z = ρ k := (mem_filter.mp hmem).2
    rw [hc]; exact hkz
  have := hr 0
  have := hr (cls z)
  omega

/-- **Physical rectangles.** Every finite list of rectangle kinds is realized by pairwise
edge-disjoint rectangles of the host avoiding `B`, with total incidence at most `r + 2q` at
every vertex. -/
theorem exists_rectangles [Fintype V] (cls : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ a b, G.Adj a b ↔ cls a ≠ cls b) (γ : ℝ)
    (hcls : ∀ i, γ * Fintype.card V ≤ ((classSet cls i).card : ℝ))
    (hpos : ∀ i, 0 < (classSet cls i).card)
    (B : Finset (Sym2 V)) (d : ℝ) (hB : DegBounded B d) (K : ℕ) (ρ : ℕ → Fin 4)
    (hρ : ∀ k, ρ k ≠ 0) (q r : ℕ) (hq : 0 < q)
    (hr : ∀ i, 4 * (K / (classSet cls i).card + 1) ≤ r)
    (hbudget : (2 * K : ℝ) / q + 2 * (d + r + 2 * q) < γ * Fintype.card V) :
    ∃ a b x y : ℕ → V,
      (∀ k, cls (a k) = 0 ∧ cls (b k) = ρ k) ∧
      (∀ k < K, cls (x k) = mid (ρ k) false ∧ cls (y k) = mid (ρ k) true) ∧
      (∀ k < K, rect (a k) (b k) (x k) (y k) ⊆ G.edgeFinset) ∧
      (∀ k < K, Disjoint (rect (a k) (b k) (x k) (y k)) B) ∧
      ((range K : Set ℕ).PairwiseDisjoint fun k => rect (a k) (b k) (x k) (y k)) ∧
      (∀ v, incidentLoad ((range K).biUnion fun k => rect (a k) (b k) (x k) (y k)) v ≤
        r + 2 * q) := by
  obtain ⟨v0, hv0⟩ := card_pos.mp (hpos 0)
  set s : Finset (ℕ × Bool) := (range K) ×ˢ (univ : Finset Bool) with hs
  set uu : ℕ × Bool → V := fun i => cyc (classSet cls 0) v0 i.1 with huu
  set vv : ℕ × Bool → V := fun i => cyc (classSet cls (ρ i.1)) v0 i.1 with hvv
  have hcu : ∀ k, cls (cyc (classSet cls 0) v0 k) = 0 := fun k =>
    (mem_filter.mp (cyc_mem v0 (hpos 0) k)).2
  have hcv : ∀ k, cls (cyc (classSet cls (ρ k)) v0 k) = ρ k := fun k =>
    (mem_filter.mp (cyc_mem v0 (hpos (ρ k)) k)).2
  have hneq : ∀ i ∈ s, uu i ≠ vv i := by
    intro i _ h
    have := congrArg cls h
    simp only [huu, hvv, hcu, hcv] at this
    exact hρ i.1 this.symm
  have htype : ∀ i ∈ s, ({cls (uu i), cls (vv i), mid (ρ i.1) i.2} : Multiset (Fin 4)) ∈ F3 := by
    intro i _
    simp only [huu, hvv, hcu, hcv]
    obtain ⟨h1, h2, -⟩ := mid_spec (ρ i.1) (hρ i.1) i.2
    exact ClassCertificate.distinct_mem_F3 _ _ _ (Ne.symm (hρ i.1)) (Ne.symm h1) (Ne.symm h2)
  have hroot : ∀ z, rootLoad s uu vv z ≤ r := rootLoad_cyc_le cls v0 hpos K ρ r hr
  have hscard : (s.card : ℝ) = 2 * K := by
    rw [hs, card_product, card_range, card_univ, Fintype.card_bool]; push_cast; ring
  obtain ⟨f, hf, hdis, haux⟩ := exists_compatible_family cls F3 G γ d
    (antiEdgeful_host cls G hG γ hcls) B hB ∅ uu vv (fun i => mid (ρ i.1) i.2) s hneq htype
    r q hq hroot (by rw [card_empty, hscard]; push_cast; linarith)
  have hmemS : ∀ k < K, ∀ β : Bool, (k, β) ∈ s := fun k hk β =>
    mem_product.mpr ⟨mem_range.mpr hk, mem_univ _⟩
  have hrect : ∀ k, rect (uu (k, false)) (vv (k, false)) (f (k, false)) (f (k, true)) =
      pathEdges (uu (k, false)) (vv (k, false)) (f (k, false)) ∪
        pathEdges (uu (k, true)) (vv (k, true)) (f (k, true)) := fun k => rfl
  refine ⟨fun k => uu (k, false), fun k => vv (k, false), fun k => f (k, false),
    fun k => f (k, true), fun k => ⟨hcu k, hcv k⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    exact ⟨(hf _ (hmemS k hk false)).2.2.1, (hf _ (hmemS k hk true)).2.2.1⟩
  · intro k hk e he
    rw [hrect] at he
    rcases mem_union.mp he with he | he <;>
    · obtain ⟨h1, h2, -⟩ := hf _ (hmemS k hk _)
      simp only [pathEdges, mem_insert, mem_singleton] at he
      rcases he with rfl | rfl
      · exact SimpleGraph.mem_edgeFinset.mpr h1
      · exact SimpleGraph.mem_edgeFinset.mpr h2.symm
  · intro k hk
    rw [hrect, disjoint_union_left]
    constructor <;>
    · obtain ⟨-, -, -, -, h5, h6⟩ := hf _ (hmemS k hk _)
      rw [disjoint_left]
      intro e he heB
      simp only [pathEdges, mem_insert, mem_singleton] at he
      rcases he with rfl | rfl
      · exact h5 heB
      · exact h6 heB
  · intro k hk k' hk' hkk'
    change Disjoint (rect _ _ _ _) (rect _ _ _ _)
    rw [hrect, hrect, disjoint_union_left, disjoint_union_right, disjoint_union_right]
    have hk1 := mem_range.mp (mem_coe.mp hk)
    have hk2 := mem_range.mp (mem_coe.mp hk')
    have hne : ∀ β β' : Bool, (k, β) ≠ (k', β') := fun β β' h => hkk' (congrArg Prod.fst h)
    exact ⟨⟨hdis (hmemS k hk1 false) (hmemS k' hk2 false) (hne _ _),
      hdis (hmemS k hk1 false) (hmemS k' hk2 true) (hne _ _)⟩,
      hdis (hmemS k hk1 true) (hmemS k' hk2 false) (hne _ _),
      hdis (hmemS k hk1 true) (hmemS k' hk2 true) (hne _ _)⟩
  · intro v
    have hsub : ((range K).biUnion fun k =>
        rect (uu (k, false)) (vv (k, false)) (f (k, false)) (f (k, true))) ⊆
        familyEdges s uu vv f := by
      intro e he
      obtain ⟨k, hk, he⟩ := mem_biUnion.mp he
      rw [hrect] at he
      unfold familyEdges
      rcases mem_union.mp he with he | he
      · exact mem_biUnion.mpr ⟨_, hmemS k (mem_range.mp hk) false, he⟩
      · exact mem_biUnion.mpr ⟨_, hmemS k (mem_range.mp hk) true, he⟩
    exact (ModThreeLayer.incidentLoad_mono hsub v).trans
      ((family_incident_card_le s uu vv f v).trans
        (Nat.add_le_add (hroot v) (Nat.mul_le_mul_left 2 (haux v))))

end PartitionedTriangleAbsorption.StructuralF3
