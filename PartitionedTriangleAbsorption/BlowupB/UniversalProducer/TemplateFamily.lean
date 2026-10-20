/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.GuardedTemplates

/-!
# Sparse families of copies of templates on an arbitrary finite vertex type

This generalizes `StructuralF3General.GuardedTemplates` from six-position templates to
templates on an arbitrary finite type `U` (all positions are embedded injectively).  The
placement uses the actual guarded embedding theorem `guarded_exists_embedding` (guarded
common-neighbour supply of order `|U|`), avoids a prescribed sparse ledger `B`, keeps the
copies pairwise edge-disjoint and excludes saturated vertices, so the total incidence of the
family is at most `T + M` at every vertex (`M` bounds the template sizes).
-/

namespace PartitionedTriangleAbsorption.BlowupB.UniversalProducer

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.StructuralF3General

variable {V I U : Type*} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U] {t : ℕ}

/-- The image of a template edge set under a placement. -/
def mappedU (E : Finset (Sym2 U)) (f : U → V) : Finset (Sym2 V) :=
  E.image (Sym2.map f)

theorem guarded_template_copyU [Nonempty V]
    (p : V → Fin t) (G : SimpleGraph V) [DecidableRel G.Adj]
    (Allowed : Fin t → Fin t → Prop)
    (E : Finset (Sym2 U)) (label : U → Fin t)
    (hloop : ∀ e ∈ E, ¬ e.IsDiag)
    (hproper : ∀ i j, s(i, j) ∈ E → Allowed (label i) (label j))
    (a d : ℝ) (hs : GuardedSupply p G Allowed (Fintype.card U) a)
    (B : Finset (Sym2 V)) (Z : Finset V) (hB : DegBounded B d) (hd : 0 ≤ d)
    (hbudget : (Fintype.card U : ℝ) + Z.card + Fintype.card U * d < a) :
    ∃ f : U ↪ V, (∀ i, p (f i) = label i) ∧
      mappedU E f ⊆ G.edgeFinset ∧ Disjoint (mappedU E f) B ∧ ∀ i, f i ∉ Z := by
  classical
  let T : SimpleGraph U := SimpleGraph.fromEdgeSet E
  have hadj (i j : U) (hij : s(i, j) ∈ E) : T.Adj i j := by
    apply (SimpleGraph.fromEdgeSet_adj _).mpr
    refine ⟨hij, ?_⟩
    intro heq
    exact hloop _ hij (by simp [heq])
  have hT : ∀ i j, T.Adj i j → Allowed (label i) (label j) :=
    fun i j hij => hproper i j ((SimpleGraph.fromEdgeSet_adj _).mp hij).1
  let rootMap : U → V := fun _ => Classical.choice (inferInstance : Nonempty V)
  have hroot : PartialEmbedding T G B ∅ rootMap := by
    constructor <;> simp
  obtain ⟨f, hlabel, _, hedges, havoid⟩ := guarded_exists_embedding T G p label Allowed hT
    a d hs B Z hB hd hbudget ∅ rootMap hroot (by simp)
  refine ⟨f, hlabel, ?_, ?_, fun i => havoid i (by simp)⟩
  · intro e he
    obtain ⟨e', he', rfl⟩ := mem_image.mp he
    induction e' using Sym2.ind with
    | _ i j => exact SimpleGraph.mem_edgeFinset.mpr (hedges i j (hadj i j he')).1
  · rw [disjoint_left]
    intro e he hB'
    obtain ⟨e', he', rfl⟩ := mem_image.mp he
    induction e' using Sym2.ind with
    | _ i j => exact (hedges i j (hadj i j he')).2 hB'

/-- A sparse family of template copies. -/
structure CopiesU (p : V → Fin t) (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset (Sym2 V)) (E : I → Finset (Sym2 U))
    (label : I → U → Fin t) (T : ℝ) (M : ℕ) (s : Finset I) (f : I → U → V) : Prop where
  injective : ∀ i ∈ s, Function.Injective (f i)
  labels : ∀ i ∈ s, ∀ j, p (f i j) = label i j
  subgraph : ∀ i ∈ s, mappedU (E i) (f i) ⊆ G.edgeFinset
  avoid : ∀ i ∈ s, Disjoint (mappedU (E i) (f i)) B
  disjoint : (s : Set I).PairwiseDisjoint (fun i => mappedU (E i) (f i))
  degree : DegBounded (s.biUnion fun i => mappedU (E i) (f i)) (T + M)
  card : (s.biUnion fun i => mappedU (E i) (f i)).card ≤ s.card * M

theorem CopiesU.incidence {p : V → Fin t} {G : SimpleGraph V} [DecidableRel G.Adj]
    {B : Finset (Sym2 V)} {E : I → Finset (Sym2 U)}
    {label : I → U → Fin t} {T : ℝ} {M : ℕ} {s : Finset I} {f : I → U → V}
    (h : CopiesU p G B E label T M s f) (v : V) :
    ((∑ i ∈ s, incidentLoad (mappedU (E i) (f i)) v : ℕ) : ℝ) ≤ T + M := by
  have heq : ∑ i ∈ s, incidentLoad (mappedU (E i) (f i)) v =
      incidentLoad (s.biUnion fun i => mappedU (E i) (f i)) v := by
    unfold incidentLoad
    rw [filter_biUnion, card_biUnion]
    intro i hi j hj hij
    exact disjoint_filter_filter (h.disjoint hi hj hij)
  rw [heq]
  exact h.degree v

theorem guarded_template_familyU [Nonempty V]
    (p : V → Fin t) (G : SimpleGraph V) [DecidableRel G.Adj]
    (Allowed : Fin t → Fin t → Prop) (s : Finset I)
    (E : I → Finset (Sym2 U)) (label : I → U → Fin t) (M : ℕ)
    (hloop : ∀ i ∈ s, ∀ e ∈ E i, ¬ e.IsDiag)
    (hproper : ∀ i ∈ s, ∀ x y, s(x, y) ∈ E i → Allowed (label i x) (label i y))
    (hcard : ∀ i ∈ s, (E i).card ≤ M)
    (a d T : ℝ) (hs : GuardedSupply p G Allowed (Fintype.card U) a)
    (B : Finset (Sym2 V)) (hB : DegBounded B d) (hd : 0 ≤ d) (hT : 0 < T)
    (hbudget : (Fintype.card U : ℝ) + Fintype.card U * (d + T + M) < a / 2)
    (hcount : 4 * M * (s.card : ℝ) ≤ T * a) :
    ∃ f : I → U → V, CopiesU p G B E label T M s f := by
  classical
  have hcU : (0 : ℝ) ≤ Fintype.card U := Nat.cast_nonneg _
  have H : ∀ K : Finset I, K ⊆ s → ∃ f, CopiesU p G B E label T M K f := by
    intro K
    induction K using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨fun _ _ => Classical.choice (inferInstance : Nonempty V), ?_⟩
      constructor
      · simp
      · simp
      · simp
      · simp
      · simp
      · intro v
        simp only [biUnion_empty, filter_empty, card_empty, Nat.cast_zero]
        have : (0 : ℝ) ≤ M := Nat.cast_nonneg _
        linarith
      · simp
    | @insert j K hj ih =>
      intro hKs
      have hjS : j ∈ s := hKs (mem_insert_self _ _)
      have hK : K ⊆ s := fun i hi => hKs (mem_insert_of_mem hi)
      obtain ⟨f, hf⟩ := ih hK
      let Un := K.biUnion fun i => mappedU (E i) (f i)
      let High : Finset V := univ.filter fun v => T < (incidentLoad Un v : ℝ)
      have hcountU : 4 * (Un.card : ℝ) ≤ T * a := by
        have h1 : (Un.card : ℝ) ≤ K.card * M := by exact_mod_cast hf.card
        have h2 : (K.card : ℝ) ≤ s.card := by exact_mod_cast card_le_card hK
        have h3 : (K.card : ℝ) * M ≤ s.card * M :=
          mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _)
        linarith
      have hHigh : (High.card : ℝ) ≤ a / 2 := by
        have hc := PrivateFamily.card_highLoad_le Un T
        change (High.card : ℝ) * T ≤ 2 * Un.card at hc
        nlinarith
      have hBU : DegBounded (B ∪ Un) (d + T + M) := by
        convert GuardedTemplates.degree_union hB hf.degree using 1
        ring
      have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
      obtain ⟨g, hglabel, hgG, hgavoid, hgHigh⟩ := guarded_template_copyU p G Allowed (E j)
        (label j) (hloop j hjS) (hproper j hjS) a (d + T + M) hs (B ∪ Un) High hBU
        (by positivity) (by linarith)
      let f' : I → U → V := fun i => if i = j then g else f i
      have hfj : f' j = g := by simp [f']
      have hfi : ∀ i ∈ K, f' i = f i := fun i hi => by
        have hij : i ≠ j := by
          intro hij
          exact hj (hij ▸ hi)
        simp only [f', if_neg hij]
      let A := mappedU (E j) g
      have hAc : A.card ≤ M := card_image_le.trans (hcard j hjS)
      have hAB : Disjoint A B := hgavoid.mono_right subset_union_left
      have hAU : Disjoint A Un := hgavoid.mono_right subset_union_right
      have hAi : ∀ i ∈ K, Disjoint A (mappedU (E i) (f i)) := fun i hi =>
        hAU.mono_right (subset_biUnion_of_mem (fun i => mappedU (E i) (f i)) hi)
      have hbig : ((insert j K).biUnion fun i => mappedU (E i) (f' i)) = Un ∪ A := by
        rw [biUnion_insert, hfj, union_comm]
        congr 1
        exact biUnion_congr rfl fun i hi => by rw [hfi i hi]
      refine ⟨f', ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · intro i hi
        rcases mem_insert.mp hi with rfl | hi
        · rw [hfj]; exact g.injective
        · rw [hfi i hi]; exact hf.injective i hi
      · intro i hi k
        rcases mem_insert.mp hi with rfl | hi
        · rw [hfj]; exact hglabel k
        · rw [hfi i hi]; exact hf.labels i hi k
      · intro i hi
        rcases mem_insert.mp hi with rfl | hi
        · rw [hfj]; exact hgG
        · rw [hfi i hi]; exact hf.subgraph i hi
      · intro i hi
        rcases mem_insert.mp hi with rfl | hi
        · rw [hfj]; exact hAB
        · rw [hfi i hi]; exact hf.avoid i hi
      · intro i hi k hk hik
        change Disjoint (mappedU (E i) (f' i)) (mappedU (E k) (f' k))
        rcases mem_insert.mp hi with hij | hiK
        · subst i
          rcases mem_insert.mp hk with hkj | hkK
          · subst k; exact False.elim (hik rfl)
          · rw [hfj, hfi k hkK]; exact hAi k hkK
        · rcases mem_insert.mp hk with hkj | hkK
          · subst k; rw [hfi i hiK, hfj]; exact (hAi i hiK).symm
          · rw [hfi i hiK, hfi k hkK]; exact hf.disjoint hiK hkK hik
      · intro v
        change (incidentLoad ((insert j K).biUnion fun i => mappedU (E i) (f' i)) v : ℝ) ≤ T + M
        rw [hbig, PrivateFamily.incidentLoad_union hAU.symm]
        have hAv : (incidentLoad A v : ℝ) ≤ M := by
          exact_mod_cast (PrivateFamily.incidentLoad_le_card A v).trans hAc
        by_cases hv : v ∈ vertSet A
        · have hvHigh : v ∉ High := by
            obtain ⟨e, he, hve⟩ := SignedHinge.mem_vertSet.mp hv
            obtain ⟨e', he', rfl⟩ := mem_image.mp he
            obtain ⟨w, _, rfl⟩ := Sym2.mem_map.mp hve
            exact hgHigh w
          have hUv : (incidentLoad Un v : ℝ) ≤ T :=
            le_of_not_gt fun h => hvHigh (mem_filter.mpr ⟨mem_univ _, h⟩)
          push_cast
          linarith
        · rw [PrivateFamily.incidentLoad_eq_zero hv, add_zero]
          exact hf.degree v
      · rw [hbig, card_insert_of_notMem hj]
        have h1 := card_union_le Un A
        have h2 := hf.card
        change Un.card ≤ K.card * M at h2
        have : (K.card + 1) * M = K.card * M + M := by ring
        omega
  exact H s subset_rfl

end PartitionedTriangleAbsorption.BlowupB.UniversalProducer
