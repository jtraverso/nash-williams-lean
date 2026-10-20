/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CatalystInsertionStage89

/-! # One insertion step changes exactly four token positions

Processing the active vertex `y ∉ P` with fresh carriers `z, z'` moves the
two original tokens at `y` from `y a₀`, `y b₀` to `z a₀`, `z' b₀`, and the two
catalytic tokens at `co y` from `co y – cs y`, `co y – ct y` to `z – cs y`,
`z' – ct y`. Here `a₀`, `b₀` are the CURRENT far endpoints of the tokens
`y – nm y`, `y – np y` (possibly carriers created earlier at `nm y`, `np y`).
All other tokens, including `cs y – ct y`, keep their positions.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CatalystInsertionStage89

open Finset AntiEdgeSelection TypedTransformer CatalystSelectionStage89

variable {V : Type*} [DecidableEq V] {t : ℕ}

namespace Data

variable (S : Data V) (cz cz' : V → V) (P : Finset V) (y : V)

/-- The current far endpoint of the token `y – nm y`. -/
def a₀ : V := S.rep cz cz' P (S.nm y) s(y, S.nm y)

/-- The current far endpoint of the token `y – np y`. -/
def b₀ : V := S.rep cz cz' P (S.np y) s(y, S.np y)

/-- The four source edges of the exchange at `y`. -/
def srcEdges : Finset (Sym2 V) :=
  {s(y, S.a₀ cz cz' P y), s(y, S.b₀ cz cz' P y), s(S.co y, S.cs y), s(S.co y, S.ct y)}

/-- The four destination edges of the exchange at `y`. -/
def newEdges (z z' : V) : Finset (Sym2 V) :=
  {s(z, S.a₀ cz cz' P y), s(z, S.cs y), s(z', S.b₀ cz cz' P y), s(z', S.ct y)}

/-- The token positions not affected by the exchange at `y`. -/
def rest : Finset (Sym2 V) :=
  (S.Y.filter fun e => y ∉ e).image (S.curY cz cz' P) ∪
    (S.A.erase y).biUnion (S.catCur cz cz' P) ∪ {s(S.cs y, S.ct y)}

end Data

variable [Fintype V]

section

variable {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
  [DecidableRel G.Adj] {B : Finset (Sym2 V)} {S : Data V} {Z₀ : Finset V}
  {cz cz' : V → V} {P : Finset V} {y : V}

theorem config_split (fr : Frame p F G B S Z₀) (hy : y ∈ S.A) (hyP : y ∉ P) :
    S.config cz cz' P = S.rest cz cz' P y ∪ S.srcEdges cz cz' P y := by
  have h1 : S.Y.image (S.curY cz cz' P) = (S.Y.filter fun e => y ∉ e).image (S.curY cz cz' P) ∪
      {s(y, S.a₀ cz cz' P y), s(y, S.b₀ cz cz' P y)} := by
    conv_lhs => rw [← filter_union_filter_not_eq (fun e => y ∈ e) S.Y]
    rw [fr.star y hy, image_union, union_comm]
    congr 1
    simp [Data.curY_mk, S.rep_of_not_mem cz cz' P hyP, Data.a₀, Data.b₀]
  have h2 : S.A.biUnion (S.catCur cz cz' P) =
      S.catCur cz cz' P y ∪ (S.A.erase y).biUnion (S.catCur cz cz' P) := by
    rw [← biUnion_insert, insert_erase hy]
  have h3 : S.catCur cz cz' P y = catEdges (S.co y) (S.cs y) (S.ct y) := by
    simp [Data.catCur, hyP]
  unfold Data.config Data.rest Data.srcEdges
  rw [h1, h2, h3]
  ext e
  simp only [catEdges, mem_union, mem_insert, mem_singleton]
  tauto

theorem config_split_next (fr : Frame p F G B S Z₀) (hy : y ∈ S.A) (z z' : V) :
    S.config (Function.update cz y z) (Function.update cz' y z') (insert y P) =
      S.rest cz cz' P y ∪ S.newEdges cz cz' P y z z' := by
  obtain ⟨hnm, hnp⟩ := fr.nm_ne hy
  have hrep : ∀ e : Sym2 V, ∀ u, u ≠ y →
      S.rep (Function.update cz y z) (Function.update cz' y z') (insert y P) u e =
        S.rep cz cz' P u e := by
    intro e u hu
    simp [Data.rep, mem_insert, hu]
  have hgh : s(y, S.np y) ≠ s(y, S.nm y) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨_, h⟩ | ⟨h, _⟩
    · exact fr.nm_ne_np y hy h.symm
    · exact hnm h.symm
  have h1 : S.Y.image (S.curY (Function.update cz y z) (Function.update cz' y z') (insert y P)) =
      (S.Y.filter fun e => y ∉ e).image (S.curY cz cz' P) ∪
        {s(z, S.a₀ cz cz' P y), s(z', S.b₀ cz cz' P y)} := by
    conv_lhs => rw [← filter_union_filter_not_eq (fun e => y ∈ e) S.Y]
    rw [fr.star y hy, image_union, union_comm]
    congr 1
    · apply image_congr
      intro e he
      have hye : y ∉ e := (mem_filter.mp he).2
      unfold Data.curY
      apply Sym2.map_congr
      intro u hu
      exact hrep e u (fun h => hye (h ▸ hu))
    · rw [image_insert, image_singleton, Data.curY_mk, Data.curY_mk, hrep _ _ hnm,
        hrep _ _ hnp]
      simp [Data.rep, hgh, Data.a₀, Data.b₀]
  have h2 : S.A.biUnion (S.catCur (Function.update cz y z) (Function.update cz' y z')
        (insert y P)) =
      {s(z, S.cs y), s(z', S.ct y), s(S.cs y, S.ct y)} ∪
        (S.A.erase y).biUnion (S.catCur cz cz' P) := by
    rw [← insert_erase hy, biUnion_insert, insert_erase hy]
    congr 1
    · simp [Data.catCur]
    · apply biUnion_congr rfl
      intro y' hy'
      have hne : y' ≠ y := (mem_erase.mp hy').1
      simp [Data.catCur, mem_insert, hne]
  unfold Data.config Data.rest Data.newEdges
  rw [h1, h2]
  ext e
  simp only [mem_union, mem_insert, mem_singleton]
  tauto

/-- No unaffected token position contains `y` or `co y`. -/
theorem rest_avoids (fr : Frame p F G B S Z₀) (hc : Carriers Z₀ cz cz' P)
    (hy : y ∈ S.A) (hyP : y ∉ P) :
    ∀ e ∈ S.rest cz cz' P y, y ∉ e ∧ S.co y ∉ e := by
  obtain ⟨hco, hcs, hct⟩ := fr.mem_cat hy
  obtain ⟨d1, d2, d3⟩ := fr.distinct y hy
  obtain ⟨n1, n2, n3⟩ := fr.cat_notA hy
  intro e he
  simp only [Data.rest, mem_union, mem_image, mem_filter, mem_biUnion, mem_erase,
    mem_singleton] at he
  rcases he with (⟨e₀, ⟨he₀, hye₀⟩, rfl⟩ | ⟨y', ⟨hne, hy'⟩, he⟩) | rfl
  · constructor
    · intro hmem
      obtain ⟨u, hu, hru⟩ := (S.mem_curY cz cz' P).mp hmem
      have huA := fr.supp e₀ he₀ u hu
      have hne : u ≠ y := fun h => hye₀ (h ▸ hu)
      apply rep_ne_of_ne fr hc huA hy hne e₀ e₀
      rw [hru, S.rep_of_not_mem cz cz' P hyP]
    · intro hmem
      obtain ⟨u, hu, hru⟩ := (S.mem_curY cz cz' P).mp hmem
      exact rep_not_cat fr hc (fr.supp e₀ he₀ u hu) e₀ hy (by simp [catVerts]) hru
  · have hvd := fr.vdisj y hy y' hy' (Ne.symm hne)
    have hnotA' := fr.cat_notA hy'
    have hco' : S.co y ∉ catVerts (S.co y') (S.cs y') (S.ct y') := fun h =>
      disjoint_left.mp hvd (by simp [catVerts]) h
    simp only [catVerts, mem_insert, mem_singleton, not_or] at hco'
    unfold Data.catCur at he
    split_ifs at he with hP
    · have hf := hc.fresh y' hP
      simp only [mem_insert, mem_singleton] at he
      constructor <;> rcases he with rfl | rfl | rfl <;> simp only [Sym2.mem_iff, not_or] <;>
        refine ⟨?_, ?_⟩ <;> intro h
      all_goals first
        | exact hf.1 (h ▸ fr.ZA hy) | exact hf.2 (h ▸ fr.ZA hy)
        | exact hf.1 (h ▸ hco) | exact hf.2 (h ▸ hco)
        | exact hnotA'.2.1 (h ▸ hy) | exact hnotA'.2.2 (h ▸ hy)
        | exact hco'.2.1 h | exact hco'.2.2 h
    · simp only [catEdges, mem_insert, mem_singleton] at he
      constructor <;> rcases he with rfl | rfl | rfl <;> simp only [Sym2.mem_iff, not_or] <;>
        refine ⟨?_, ?_⟩ <;> intro h
      all_goals first
        | exact hnotA'.1 (h ▸ hy) | exact hnotA'.2.1 (h ▸ hy) | exact hnotA'.2.2 (h ▸ hy)
        | exact hco'.1 h | exact hco'.2.1 h | exact hco'.2.2 h
  · simp only [Sym2.mem_iff, not_or]
    refine ⟨⟨fun h => n2 (h ▸ hy), fun h => n3 (h ▸ hy)⟩, d1, d2⟩

theorem rest_disjoint (fr : Frame p F G B S Z₀) (hc : Carriers Z₀ cz cz' P)
    (hy : y ∈ S.A) (hyP : y ∉ P) :
    Disjoint (S.rest cz cz' P y) (S.srcEdges cz cz' P y) := by
  rw [disjoint_left]
  intro e he hsrc
  obtain ⟨h1, h2⟩ := rest_avoids fr hc hy hyP e he
  simp only [Data.srcEdges, mem_insert, mem_singleton] at hsrc
  rcases hsrc with rfl | rfl | rfl | rfl
  · exact h1 (Sym2.mem_mk_left _ _)
  · exact h1 (Sym2.mem_mk_left _ _)
  · exact h2 (Sym2.mem_mk_left _ _)
  · exact h2 (Sym2.mem_mk_left _ _)

/-- **Exact token bookkeeping of one insertion step.** -/
theorem config_step (fr : Frame p F G B S Z₀) (hc : Carriers Z₀ cz cz' P)
    (hy : y ∈ S.A) (hyP : y ∉ P) (z z' : V) :
    S.config (Function.update cz y z) (Function.update cz' y z') (insert y P) =
      (S.config cz cz' P \ S.srcEdges cz cz' P y) ∪ S.newEdges cz cz' P y z z' := by
  rw [config_split_next fr hy, config_split fr hy hyP, union_sdiff_right,
    sdiff_eq_self_of_disjoint (rest_disjoint fr hc hy hyP)]

end

end PartitionedTriangleAbsorption.CatalystInsertionStage89
