/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.GuardedLedger

/-! # Sparse families of prescribed six-position templates

An individual template may use only some of its six positions.  All six are
embedded injectively.  The finite family has pairwise disjoint physical edges,
avoids a prescribed ledger, and has bounded total incidence.  The placement
uses the actual guarded embedding theorem and excludes saturated vertices.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.StructuralF3General.GuardedTemplates

open Finset AntiEdgeSelection

variable {V I : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

def mapped (E : Finset (Sym2 (Fin 6))) (f : Fin 6 → V) : Finset (Sym2 V) :=
  E.image (Sym2.map f)

omit [Fintype V] in
theorem degree_union {E F : Finset (Sym2 V)} {d e : ℝ}
    (hE : DegBounded E d) (hF : DegBounded F e) : DegBounded (E ∪ F) (d + e) := by
  intro v
  have h : incidentLoad (E ∪ F) v ≤ incidentLoad E v + incidentLoad F v := by
    unfold incidentLoad
    rw [filter_union]
    exact card_union_le _ _
  have hR : (incidentLoad (E ∪ F) v : ℝ) ≤ incidentLoad E v + incidentLoad F v := by
    exact_mod_cast h
  change (incidentLoad (E ∪ F) v : ℝ) ≤ d + e
  exact hR.trans (add_le_add (hE v) (hF v))

theorem guarded_template_copy [Nonempty V]
    (p : V → Fin t) (G : SimpleGraph V) [DecidableRel G.Adj]
    (Allowed : Fin t → Fin t → Prop)
    (E : Finset (Sym2 (Fin 6))) (label : Fin 6 → Fin t)
    (hloop : ∀ e ∈ E, ¬ e.IsDiag)
    (hproper : ∀ i j, s(i, j) ∈ E → Allowed (label i) (label j))
    (a d : ℝ) (hs : GuardedSupply p G Allowed 6 a)
    (B : Finset (Sym2 V)) (Z : Finset V) (hB : DegBounded B d) (hd : 0 ≤ d)
    (hbudget : 6 + (Z.card : ℝ) + 6 * d < a) :
    ∃ f : Fin 6 ↪ V, (∀ i, p (f i) = label i) ∧
      mapped E f ⊆ G.edgeFinset ∧ Disjoint (mapped E f) B ∧ ∀ i, f i ∉ Z := by
  classical
  let T : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet E
  have hadj (i j : Fin 6) (hij : s(i, j) ∈ E) : T.Adj i j := by
    apply (SimpleGraph.fromEdgeSet_adj _).mpr
    refine ⟨hij, ?_⟩
    intro heq
    exact hloop _ hij (by simp [heq])
  have hT : ∀ i j, T.Adj i j → Allowed (label i) (label j) :=
    fun i j hij => hproper i j ((SimpleGraph.fromEdgeSet_adj _).mp hij).1
  let rootMap : Fin 6 → V := fun _ => Classical.choice (inferInstance : Nonempty V)
  have hroot : PartialEmbedding T G B ∅ rootMap := by
    constructor <;> simp
  obtain ⟨f, hlabel, _, hedges, havoid⟩ := guarded_exists_embedding T G p label Allowed hT
    a d (by simpa using hs) B Z hB hd (by simpa using hbudget) ∅ rootMap hroot (by simp)
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

structure Copies (p : V → Fin t) (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset (Sym2 V)) (E : I → Finset (Sym2 (Fin 6)))
    (label : I → Fin 6 → Fin t) (T : ℝ) (s : Finset I) (f : I → Fin 6 → V) : Prop where
  injective : ∀ i ∈ s, Function.Injective (f i)
  labels : ∀ i ∈ s, ∀ j, p (f i j) = label i j
  subgraph : ∀ i ∈ s, mapped (E i) (f i) ⊆ G.edgeFinset
  avoid : ∀ i ∈ s, Disjoint (mapped (E i) (f i)) B
  disjoint : (s : Set I).PairwiseDisjoint (fun i => mapped (E i) (f i))
  degree : DegBounded (s.biUnion fun i => mapped (E i) (f i)) (T + 6)
  card : (s.biUnion fun i => mapped (E i) (f i)).card ≤ s.card * 6

theorem Copies.incidence {p : V → Fin t} {G : SimpleGraph V} [DecidableRel G.Adj]
    {B : Finset (Sym2 V)} {E : I → Finset (Sym2 (Fin 6))}
    {label : I → Fin 6 → Fin t} {T : ℝ} {s : Finset I} {f : I → Fin 6 → V}
    (h : Copies p G B E label T s f) (v : V) :
    ((∑ i ∈ s, incidentLoad (mapped (E i) (f i)) v : ℕ) : ℝ) ≤ T + 6 := by
  have heq : ∑ i ∈ s, incidentLoad (mapped (E i) (f i)) v =
      incidentLoad (s.biUnion fun i => mapped (E i) (f i)) v := by
    unfold incidentLoad
    rw [filter_biUnion, card_biUnion]
    intro i hi j hj hij
    exact disjoint_filter_filter (h.disjoint hi hj hij)
  rw [heq]
  exact h.degree v

theorem guarded_template_family [Nonempty V]
    (p : V → Fin t) (G : SimpleGraph V) [DecidableRel G.Adj]
    (Allowed : Fin t → Fin t → Prop) (s : Finset I)
    (E : I → Finset (Sym2 (Fin 6))) (label : I → Fin 6 → Fin t)
    (hloop : ∀ i ∈ s, ∀ e ∈ E i, ¬ e.IsDiag)
    (hproper : ∀ i ∈ s, ∀ x y, s(x, y) ∈ E i → Allowed (label i x) (label i y))
    (hcard : ∀ i ∈ s, (E i).card ≤ 6)
    (a d T : ℝ) (hs : GuardedSupply p G Allowed 6 a)
    (B : Finset (Sym2 V)) (hB : DegBounded B d) (hd : 0 ≤ d) (hT : 0 < T)
    (hbudget : 6 + 6 * (d + T + 6) < a / 2)
    (hcount : 24 * (s.card : ℝ) ≤ T * a) :
    ∃ f : I → Fin 6 → V, Copies p G B E label T s f := by
  classical
  have H : ∀ K : Finset I, K ⊆ s → ∃ f, Copies p G B E label T K f := by
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
        linarith
      · simp
    | @insert j K hj ih =>
      intro hKs
      have hjS : j ∈ s := hKs (mem_insert_self _ _)
      have hK : K ⊆ s := fun i hi => hKs (mem_insert_of_mem hi)
      obtain ⟨f, hf⟩ := ih hK
      let U := K.biUnion fun i => mapped (E i) (f i)
      let High : Finset V := univ.filter fun v => T < (incidentLoad U v : ℝ)
      have hcountU : 4 * (U.card : ℝ) ≤ T * a := by
        have h1 : (U.card : ℝ) ≤ K.card * 6 := by exact_mod_cast hf.card
        have h2 : (K.card : ℝ) ≤ s.card := by exact_mod_cast card_le_card hK
        linarith
      have hHigh : (High.card : ℝ) ≤ a / 2 := by
        have hc := PrivateFamily.card_highLoad_le U T
        change (High.card : ℝ) * T ≤ 2 * U.card at hc
        nlinarith
      have hBU : DegBounded (B ∪ U) (d + T + 6) := by
        convert degree_union hB hf.degree using 1
        ring
      obtain ⟨g, hglabel, hgG, hgavoid, hgHigh⟩ := guarded_template_copy p G Allowed (E j)
        (label j) (hloop j hjS) (hproper j hjS) a (d + T + 6) hs (B ∪ U) High hBU
        (by positivity) (by linarith)
      let f' : I → Fin 6 → V := fun i => if i = j then g else f i
      have hfj : f' j = g := by simp [f']
      have hfi : ∀ i ∈ K, f' i = f i := fun i hi => by
        have hij : i ≠ j := by
          intro hij
          exact hj (hij ▸ hi)
        simp only [f', ite_eq_right hij]
      let A := mapped (E j) g
      have hAc : A.card ≤ 6 := card_image_le.trans (hcard j hjS)
      have hAB : Disjoint A B := hgavoid.mono_right subset_union_left
      have hAU : Disjoint A U := hgavoid.mono_right subset_union_right
      have hAi : ∀ i ∈ K, Disjoint A (mapped (E i) (f i)) := fun i hi =>
        hAU.mono_right (subset_biUnion_of_mem (fun i => mapped (E i) (f i)) hi)
      have hbig : ((insert j K).biUnion fun i => mapped (E i) (f' i)) = U ∪ A := by
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
        change Disjoint (mapped (E i) (f' i)) (mapped (E k) (f' k))
        rcases mem_insert.mp hi with hij | hiK
        · subst i
          rcases mem_insert.mp hk with hkj | hkK
          · subst k; exact False.elim (hik rfl)
          · rw [hfj, hfi k hkK]; exact hAi k hkK
        · rcases mem_insert.mp hk with hkj | hkK
          · subst k; rw [hfi i hiK, hfj]; exact (hAi i hiK).symm
          · rw [hfi i hiK, hfi k hkK]; exact hf.disjoint hiK hkK hik
      · intro v
        change (incidentLoad ((insert j K).biUnion fun i => mapped (E i) (f' i)) v : ℝ) ≤ T + 6
        rw [hbig, PrivateFamily.incidentLoad_union hAU.symm]
        have hAv : (incidentLoad A v : ℝ) ≤ 6 := by
          exact_mod_cast (PrivateFamily.incidentLoad_le_card A v).trans hAc
        by_cases hv : v ∈ vertSet A
        · have hvHigh : v ∉ High := by
            obtain ⟨e, he, hve⟩ := SignedHinge.mem_vertSet.mp hv
            obtain ⟨e', he', rfl⟩ := mem_image.mp he
            obtain ⟨w, _, rfl⟩ := Sym2.mem_map.mp hve
            exact hgHigh w
          have hUv : (incidentLoad U v : ℝ) ≤ T :=
            le_of_not_gt fun h => hvHigh (mem_filter.mpr ⟨mem_univ _, h⟩)
          push_cast
          linarith
        · rw [PrivateFamily.incidentLoad_eq_zero hv, add_zero]
          exact hf.degree v
      · rw [hbig, card_insert_of_notMem hj]
        have h1 := card_union_le U A
        have h2 := hf.card
        change U.card ≤ K.card * 6 at h2
        omega
  exact H s le_rfl

theorem template_scalar_budget (ω lam rho n k : ℝ)
    (hω : ω ≤ 1) (hlam : 0 < lam) (hlamω : 1024 * lam ≤ ω)
    (hrho : 0 < rho) (hscale : (2 ^ 32 : ℝ) * rho ≤ lam ^ 2)
    (hn0 : 0 ≤ n) (hn1 : 1 ≤ rho * n) (hk : k ≤ 2 ^ 22 * rho * n ^ 2) :
    0 < n ∧ 0 < lam * n / 2 ∧
      6 + 6 * (6 * lam * n + lam * n / 2 + 6) < ω * n / 2 ∧
      24 * k ≤ (lam * n / 2) * (ω * n) ∧ lam * n / 2 + 6 ≤ lam * n := by
  have hn : 0 < n := by nlinarith only [hn1, hrho.le, hn0]
  have hlam1 : lam ≤ 1 := by linarith only [hlamω, hω, hlam.le]
  have hlam2 : lam ^ 2 ≤ lam := by nlinarith only [hlam1, hlam.le]
  have hrholam : 12 * rho ≤ lam := by
    norm_num at hscale
    nlinarith only [hscale, hlam2, hrho.le]
  have hnlam : 12 ≤ lam * n := by
    have h1 := mul_le_mul_of_nonneg_left hn1 (show (0 : ℝ) ≤ 12 by norm_num)
    have h2 := mul_le_mul_of_nonneg_right hrholam hn0
    nlinarith only [h1, h2]
  have hlnωn := mul_le_mul_of_nonneg_right hlamω hn0
  have hbudget : 6 + 6 * (6 * lam * n + lam * n / 2 + 6) < ω * n / 2 := by
    nlinarith only [hnlam, hlnωn]
  have hcoef : 24 * (2 ^ 22 : ℝ) * rho ≤ lam * ω / 2 := by
    have hll := mul_le_mul_of_nonneg_left hlamω hlam.le
    norm_num at hscale ⊢
    nlinarith only [hscale, hll, sq_nonneg lam]
  have hcount : 24 * k ≤ (lam * n / 2) * (ω * n) := by
    calc
      _ ≤ 24 * (2 ^ 22 * rho * n ^ 2) := mul_le_mul_of_nonneg_left hk (by norm_num)
      _ = (24 * 2 ^ 22 * rho) * n ^ 2 := by ring
      _ ≤ (lam * ω / 2) * n ^ 2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg n)
      _ = _ := by ring
  exact ⟨hn, by positivity, hbudget, hcount, by linarith only [hnlam]⟩

/-- Both F1/F2 token demands fit these common numerical budgets. -/
theorem guarded_template_family_scaled
    (p : V → Fin t) (G : SimpleGraph V) [DecidableRel G.Adj]
    (Allowed : Fin t → Fin t → Prop) (s : Finset I)
    (E : I → Finset (Sym2 (Fin 6))) (label : I → Fin 6 → Fin t)
    (hloop : ∀ i ∈ s, ∀ e ∈ E i, ¬ e.IsDiag)
    (hproper : ∀ i ∈ s, ∀ x y, s(x, y) ∈ E i → Allowed (label i x) (label i y))
    (hcard : ∀ i ∈ s, (E i).card ≤ 6)
    (ω lam rho : ℝ) (hs : GuardedSupply p G Allowed 6 (ω * Fintype.card V))
    (B : Finset (Sym2 V)) (hB : DegBounded B (6 * lam * Fintype.card V))
    (hω : ω ≤ 1) (hlam : 0 < lam) (hlamω : 1024 * lam ≤ ω)
    (hrho : 0 < rho) (hscale : (2 ^ 32 : ℝ) * rho ≤ lam ^ 2)
    (hn1 : 1 ≤ rho * Fintype.card V)
    (hcount : (s.card : ℝ) ≤ 2 ^ 22 * rho * (Fintype.card V : ℝ) ^ 2) :
    ∃ f : I → Fin 6 → V,
      Copies p G B E label (lam * Fintype.card V / 2) s f ∧
      ∀ v, ((∑ i ∈ s, incidentLoad (mapped (E i) (f i)) v : ℕ) : ℝ) ≤
        lam * Fintype.card V := by
  obtain ⟨hn, hT, hbudget, htokens, hfinal⟩ := template_scalar_budget ω lam rho
    (Fintype.card V) s.card hω hlam hlamω hrho hscale (Nat.cast_nonneg _) hn1 hcount
  have hnNat : 0 < Fintype.card V := by exact_mod_cast hn
  let : Nonempty V := Fintype.card_pos_iff.mp hnNat
  obtain ⟨f, hf⟩ := guarded_template_family p G Allowed s E label hloop hproper hcard
    (ω * Fintype.card V) (6 * lam * Fintype.card V) (lam * Fintype.card V / 2) hs B hB
    (by positivity) hT hbudget htokens
  exact ⟨f, hf, fun v => (hf.incidence v).trans hfinal⟩

#print axioms guarded_template_copy
#print axioms guarded_template_family
#print axioms Copies.incidence
#print axioms template_scalar_budget
#print axioms guarded_template_family_scaled

end PartitionedTriangleAbsorption.StructuralF3General.GuardedTemplates
