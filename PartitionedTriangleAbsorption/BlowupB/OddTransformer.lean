/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.OddLinks

/-! # BlowupB.OddTransformer — the transformer with odd link walks of any length

Generalizes the eleven-edge transformer of `PrivateTemplate.Transformer` (walks of length `3`,
which forces `ThreeStepLinks`) to walks of any odd length `2m + 1`.

Positions `I` with a successor permutation `σ`; source trail edges `x i x (σ i)`, target trail
edges `y i y (σ i)`, the same classes at `x i` and `y i`. At each position a fresh path
`a i 0, …, a i (2m)`, closed by `a (σ i) 0`. The transformer `oddT` consists of all spokes from
`x i` and `y i` to the path and the path edges. Then

* `T ∪ Hx` decomposes into the triangles `x i x (σ i) a (σ i) 0` and the **fans**
  `y q(2j) q(2j+1)`, `x q(2j+1) q(2j+2)` over each path (`oddTransformer_source`);
* `T ∪ Hy` decomposes symmetrically (`oddTransformer_target`).

The type conditions (`OddTypes`) say that along each path the classes form a walk in the link
of the class of `x i`: an odd walk of length `2m + 1`, nothing more.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset

variable {W : Type*} [DecidableEq W] {t : ℕ}

/-! ### Generic decomposition lemmas -/

section Generic

variable {p : W → Fin t} {F : Finset (Multiset (Fin t))}

theorem hasDecomp_tri {s : Finset W} (hs : s.card = 3) (hF : s.val.map p ∈ F) :
    HasDecomp p F (triEdges s) :=
  ⟨{s}, fun x hx => by rw [mem_singleton] at hx; subst hx; exact ⟨hs, hF⟩,
    by simp [Set.PairwiseDisjoint, Set.Pairwise], by simp⟩

theorem hasDecomp_empty' : HasDecomp p F (∅ : Finset (Sym2 W)) :=
  ⟨∅, fun _ h => absurd h (notMem_empty _), by simp, by simp⟩

theorem hasDecomp_union {E₁ E₂ : Finset (Sym2 W)} (h₁ : HasDecomp p F E₁) (h₂ : HasDecomp p F E₂)
    (hd : Disjoint E₁ E₂) : HasDecomp p F (E₁ ∪ E₂) := by
  obtain ⟨D₁, hT₁, hP₁, hU₁⟩ := h₁
  obtain ⟨D₂, hT₂, hP₂, hU₂⟩ := h₂
  refine ⟨D₁ ∪ D₂, fun s hs => (mem_union.mp hs).elim (hT₁ s) (hT₂ s), ?_, ?_⟩
  · intro s hs s' hs' hne
    simp only [coe_union, Set.mem_union, mem_coe] at hs hs'
    have sub₁ : ∀ u ∈ D₁, triEdges u ⊆ E₁ := fun u hu => hU₁ ▸ subset_biUnion_of_mem _ hu
    have sub₂ : ∀ u ∈ D₂, triEdges u ⊆ E₂ := fun u hu => hU₂ ▸ subset_biUnion_of_mem _ hu
    rcases hs with hs | hs <;> rcases hs' with hs' | hs'
    · exact hP₁ hs hs' hne
    · exact disjoint_of_subset_left (sub₁ s hs) (disjoint_of_subset_right (sub₂ s' hs') hd)
    · exact disjoint_of_subset_left (sub₂ s hs)
        (disjoint_of_subset_right (sub₁ s' hs') hd.symm)
    · exact hP₂ hs hs' hne
  · rw [union_biUnion, hU₁, hU₂]

theorem hasDecomp_biUnion {ι : Type*} [DecidableEq ι] (s : Finset ι) (E : ι → Finset (Sym2 W))
    (h : ∀ i ∈ s, HasDecomp p F (E i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (E i) (E j)) : HasDecomp p F (s.biUnion E) := by
  induction s using Finset.induction_on with
  | empty => simpa using (hasDecomp_empty' (p := p) (F := F))
  | insert a s ha ih =>
    rw [biUnion_insert]
    refine hasDecomp_union (h a (mem_insert_self a s))
      (ih (fun i hi => h i (mem_insert_of_mem hi))
        (fun i hi j hj hij => hd i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hij)) ?_
    rw [disjoint_biUnion_right]
    intro j hj
    exact hd a (mem_insert_self a s) j (mem_insert_of_mem hj) (fun h' => ha (h' ▸ hj))

end Generic

/-! ### Fans -/

/-- The fan over the path `q 0, …, q (2m+1)` with apexes `y` (even steps) and `x` (odd steps). -/
def fanEdges (x y : W) : (ℕ → W) → ℕ → Finset (Sym2 W)
  | q, 0 => triEdges {y, q 0, q 1}
  | q, m + 1 => triEdges {y, q 0, q 1} ∪ triEdges {x, q 1, q 2} ∪
      fanEdges x y (fun k => q (k + 2)) m

/-- Distinctness hypotheses of a fan. -/
structure FanOK (x y : W) (q : ℕ → W) (m : ℕ) : Prop where
  inj : ∀ a b, a ≤ 2 * m + 1 → b ≤ 2 * m + 1 → q a = q b → a = b
  hx : ∀ k, k ≤ 2 * m + 1 → x ≠ q k
  hy : ∀ k, k ≤ 2 * m + 1 → y ≠ q k
  hxy : x ≠ y

theorem FanOK.shift {x y : W} {q : ℕ → W} {m : ℕ} (h : FanOK x y q (m + 1)) :
    FanOK x y (fun k => q (k + 2)) m :=
  ⟨fun a b ha hb hab => by
      have := h.inj (a + 2) (b + 2) (by omega) (by omega) hab; omega,
    fun k _ => h.hx (k + 2) (by omega), fun k _ => h.hy (k + 2) (by omega), h.hxy⟩

theorem mem_fanEdges {x y : W} {q : ℕ → W} {m : ℕ} (h : FanOK x y q m) {e : Sym2 W} :
    e ∈ fanEdges x y q m ↔
      (∃ k, 1 ≤ k ∧ k ≤ 2 * m ∧ e = s(x, q k)) ∨ (∃ k, k ≤ 2 * m + 1 ∧ e = s(y, q k)) ∨
      (∃ k, k ≤ 2 * m ∧ e = s(q k, q (k + 1))) := by
  induction m generalizing q with
  | zero =>
    have h01 : q 0 ≠ q 1 := fun hh => absurd (h.inj 0 1 (by omega) (by omega) hh) (by omega)
    rw [fanEdges, triEdges_three (h.hy 0 (by omega)) (h.hy 1 (by omega)) h01]
    simp only [mem_insert, mem_singleton]
    constructor
    · rintro (rfl | rfl | rfl)
      · exact Or.inr (Or.inl ⟨0, by omega, rfl⟩)
      · exact Or.inr (Or.inl ⟨1, by omega, rfl⟩)
      · exact Or.inr (Or.inr ⟨0, by omega, rfl⟩)
    · rintro (⟨k, hk1, hk2, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
      · omega
      · rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl <;> simp
      · obtain rfl : k = 0 := by omega
        simp
  | succ m ih =>
    have hs := h.shift
    have h01 : q 0 ≠ q 1 := fun hh => absurd (h.inj 0 1 (by omega) (by omega) hh) (by omega)
    have h12 : q 1 ≠ q 2 := fun hh => absurd (h.inj 1 2 (by omega) (by omega) hh) (by omega)
    rw [fanEdges, mem_union, mem_union, ih hs,
      triEdges_three (h.hy 0 (by omega)) (h.hy 1 (by omega)) h01,
      triEdges_three (h.hx 1 (by omega)) (h.hx 2 (by omega)) h12]
    simp only [mem_insert, mem_singleton]
    constructor
    · rintro (((rfl | rfl | rfl) | (rfl | rfl | rfl)) |
        (⟨k, hk1, hk2, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩))
      · exact Or.inr (Or.inl ⟨0, by omega, rfl⟩)
      · exact Or.inr (Or.inl ⟨1, by omega, rfl⟩)
      · exact Or.inr (Or.inr ⟨0, by omega, rfl⟩)
      · exact Or.inl ⟨1, by omega, by omega, rfl⟩
      · exact Or.inl ⟨2, by omega, by omega, rfl⟩
      · exact Or.inr (Or.inr ⟨1, by omega, rfl⟩)
      · exact Or.inl ⟨k + 2, by omega, by omega, rfl⟩
      · exact Or.inr (Or.inl ⟨k + 2, by omega, rfl⟩)
      · exact Or.inr (Or.inr ⟨k + 2, by omega, rfl⟩)
    · rintro (⟨k, hk1, hk2, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
      · rcases (show k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with rfl | rfl | hk3
        · exact Or.inl (Or.inr (Or.inl rfl))
        · exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
        · refine Or.inr (Or.inl ⟨k - 2, by omega, by omega, ?_⟩)
          rw [show k - 2 + 2 = k by omega]
      · rcases (show k = 0 ∨ k = 1 ∨ 2 ≤ k by omega) with rfl | rfl | hk2
        · exact Or.inl (Or.inl (Or.inl rfl))
        · exact Or.inl (Or.inl (Or.inr (Or.inl rfl)))
        · refine Or.inr (Or.inr (Or.inl ⟨k - 2, by omega, ?_⟩))
          rw [show k - 2 + 2 = k by omega]
      · rcases (show k = 0 ∨ k = 1 ∨ 2 ≤ k by omega) with rfl | rfl | hk2
        · exact Or.inl (Or.inl (Or.inr (Or.inr rfl)))
        · exact Or.inl (Or.inr (Or.inr (Or.inr rfl)))
        · refine Or.inr (Or.inr (Or.inr ⟨k - 2, by omega, ?_⟩))
          rw [show k - 2 + 2 = k by omega, show k - 2 + 1 + 2 = k + 1 by omega]

set_option hygiene false in
/-- Closing tactic for vertex coincidences in a fan. -/
local macro "fanclose" : tactic => `(tactic| first
  | exact absurd h1 h.hxy | exact absurd h1.symm h.hxy
  | exact absurd h1 (h.hx _ (by omega)) | exact absurd h1.symm (h.hx _ (by omega))
  | exact absurd h1 (h.hy _ (by omega)) | exact absurd h1.symm (h.hy _ (by omega))
  | (have := h.inj _ _ (by omega) (by omega) h1; omega)
  | exact absurd h2 h.hxy | exact absurd h2.symm h.hxy
  | exact absurd h2 (h.hx _ (by omega)) | exact absurd h2.symm (h.hx _ (by omega))
  | exact absurd h2 (h.hy _ (by omega)) | exact absurd h2.symm (h.hy _ (by omega))
  | (have := h.inj _ _ (by omega) (by omega) h2; omega))

/-- The fan decomposes into its triangles. -/
theorem fan_hasDecomp {p : W → Fin t} {F : Finset (Multiset (Fin t))} {x y : W} {q : ℕ → W}
    {m : ℕ} (h : FanOK x y q m) (hpy : p y = p x)
    (hτ : ∀ k, k ≤ 2 * m → ({p x, p (q k), p (q (k + 1))} : Multiset (Fin t)) ∈ F) :
    HasDecomp p F (fanEdges x y q m) := by
  induction m generalizing q with
  | zero =>
    have h01 : q 0 ≠ q 1 := fun hh => absurd (h.inj 0 1 (by omega) (by omega) hh) (by omega)
    refine hasDecomp_tri (Finset.card_eq_three.mpr ⟨y, q 0, q 1, h.hy 0 (by omega),
      h.hy 1 (by omega), h01, rfl⟩) ?_
    rw [map_three p (h.hy 0 (by omega)) (h.hy 1 (by omega)) h01, hpy]
    exact hτ 0 (by omega)
  | succ m ih =>
    have hs := h.shift
    have h01 : q 0 ≠ q 1 := fun hh => absurd (h.inj 0 1 (by omega) (by omega) hh) (by omega)
    have h12 : q 1 ≠ q 2 := fun hh => absurd (h.inj 1 2 (by omega) (by omega) hh) (by omega)
    have hA : HasDecomp p F (triEdges {y, q 0, q 1}) := by
      refine hasDecomp_tri (Finset.card_eq_three.mpr ⟨y, q 0, q 1, h.hy 0 (by omega),
        h.hy 1 (by omega), h01, rfl⟩) ?_
      rw [map_three p (h.hy 0 (by omega)) (h.hy 1 (by omega)) h01, hpy]
      exact hτ 0 (by omega)
    have hB : HasDecomp p F (triEdges {x, q 1, q 2}) := by
      refine hasDecomp_tri (Finset.card_eq_three.mpr ⟨x, q 1, q 2, h.hx 1 (by omega),
        h.hx 2 (by omega), h12, rfl⟩) ?_
      rw [map_three p (h.hx 1 (by omega)) (h.hx 2 (by omega)) h12]
      exact hτ 1 (by omega)
    have hC := ih hs (fun k hk => hτ (k + 2) (by omega))
    have hAB : Disjoint (triEdges {y, q 0, q 1}) (triEdges {x, q 1, q 2}) := by
      rw [triEdges_three (h.hy 0 (by omega)) (h.hy 1 (by omega)) h01,
        triEdges_three (h.hx 1 (by omega)) (h.hx 2 (by omega)) h12, disjoint_left]
      intro e he he'
      simp only [mem_insert, mem_singleton] at he he'
      rcases he with rfl | rfl | rfl <;> rcases he' with h0 | h0 | h0 <;>
        rcases Sym2.eq_iff.mp h0 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> fanclose
    have hABC : Disjoint (triEdges {y, q 0, q 1} ∪ triEdges {x, q 1, q 2})
        (fanEdges x y (fun k => q (k + 2)) m) := by
      rw [triEdges_three (h.hy 0 (by omega)) (h.hy 1 (by omega)) h01,
        triEdges_three (h.hx 1 (by omega)) (h.hx 2 (by omega)) h12, disjoint_left]
      intro e he he'
      rw [mem_fanEdges hs] at he'
      simp only [mem_union, mem_insert, mem_singleton] at he
      rcases he' with ⟨k, hk1, hk2, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ <;>
        rcases he with (h0 | h0 | h0) | (h0 | h0 | h0) <;>
        rcases Sym2.eq_iff.mp h0 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> fanclose
    rw [fanEdges]
    exact hasDecomp_union (hasDecomp_union hA hB hAB) hC hABC

/-! ### The odd transformer -/

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The path at position `i`: `a i 0, …, a i (2m)`, then `a (σ i) 0`. -/
def oddPath (σ : Equiv.Perm I) (m : ℕ) (a : I → ℕ → W) (i : I) (k : ℕ) : W :=
  if k ≤ 2 * m then a i k else a (σ i) 0

/-- Distinctness data of an odd transformer. -/
structure OddTransformerData (σ : Equiv.Perm I) (x y : I → W) (m : ℕ) (a : I → ℕ → W) :
    Prop where
  hx : ∀ i, x i ≠ x (σ i)
  hy : ∀ i, y i ≠ y (σ i)
  hxinj : Function.Injective fun i => s(x i, x (σ i))
  hyinj : Function.Injective fun i => s(y i, y (σ i))
  ha : ∀ i j k l, k ≤ 2 * m → l ≤ 2 * m → a i k = a j l → i = j ∧ k = l
  hax : ∀ i k j, k ≤ 2 * m → a i k ≠ x j
  hay : ∀ i k j, k ≤ 2 * m → a i k ≠ y j
  hxy : ∀ i j, x i ≠ y j

/-- Type data of an odd transformer: along each path the classes walk in the link of the
class of `x i`, and the closing triangles have allowed types. -/
structure OddTypes (p : W → Fin t) (F : Finset (Multiset (Fin t))) (σ : Equiv.Perm I)
    (x y : I → W) (m : ℕ) (a : I → ℕ → W) : Prop where
  hpy : ∀ i, p (y i) = p (x i)
  hA : ∀ i, ({p (x i), p (x (σ i)), p (a (σ i) 0)} : Multiset (Fin t)) ∈ F
  hW : ∀ i k, k ≤ 2 * m →
    ({p (x i), p (oddPath σ m a i k), p (oddPath σ m a i (k + 1))} : Multiset (Fin t)) ∈ F

variable {σ : Equiv.Perm I} {x y : I → W} {m : ℕ} {a : I → ℕ → W}

theorem OddTransformerData.swap (h : OddTransformerData σ x y m a) :
    OddTransformerData σ y x m a :=
  ⟨h.hy, h.hx, h.hyinj, h.hxinj, h.ha, h.hay, h.hax, fun i j e => h.hxy j i e.symm⟩

theorem OddTypes.swap {p : W → Fin t} {F : Finset (Multiset (Fin t))}
    (h : OddTypes p F σ x y m a) : OddTypes p F σ y x m a := by
  refine ⟨fun i => (h.hpy i).symm, fun i => ?_, fun i k hk => ?_⟩
  · rw [h.hpy, h.hpy]; exact h.hA i
  · rw [h.hpy]; exact h.hW i k hk

/-- The source trail edges. -/
def srcE (σ : Equiv.Perm I) (x : I → W) : Finset (Sym2 W) := univ.image fun i => s(x i, x (σ i))

/-- The closing triangles of the source. -/
def coreE (σ : Equiv.Perm I) (x : I → W) (a : I → ℕ → W) : Finset (Sym2 W) :=
  univ.biUnion fun i => triEdges {x i, x (σ i), a (σ i) 0}

/-- Spokes from `z i` to the path at `i`. -/
def spokesE (σ : Equiv.Perm I) (m : ℕ) (a : I → ℕ → W) (z : I → W) : Finset (Sym2 W) :=
  univ.biUnion fun i => (range (2 * m + 2)).image fun k => s(z i, oddPath σ m a i k)

/-- Path edges. -/
def pathE (σ : Equiv.Perm I) (m : ℕ) (a : I → ℕ → W) : Finset (Sym2 W) :=
  univ.biUnion fun i =>
    (range (2 * m + 1)).image fun k => s(oddPath σ m a i k, oddPath σ m a i (k + 1))

/-- **The odd transformer.** -/
def oddT (σ : Equiv.Perm I) (x y : I → W) (m : ℕ) (a : I → ℕ → W) : Finset (Sym2 W) :=
  spokesE σ m a x ∪ spokesE σ m a y ∪ pathE σ m a

theorem oddT_comm : oddT σ x y m a = oddT σ y x m a := by
  unfold oddT; rw [union_comm (spokesE σ m a x)]

theorem oddPath_le {i : I} {k : ℕ} (hk : k ≤ 2 * m) : oddPath σ m a i k = a i k := by
  simp [oddPath, hk]

theorem oddPath_top (i : I) : oddPath σ m a i (2 * m + 1) = a (σ i) 0 := by
  simp [oddPath]

theorem OddTransformerData.fanOK (h : OddTransformerData σ x y m a) (i : I) :
    FanOK (x i) (y i) (oddPath σ m a i) m := by
  refine ⟨fun u v hu hv huv => ?_, fun k hk => ?_, fun k hk => ?_, h.hxy i i⟩
  · unfold oddPath at huv
    split_ifs at huv with h1 h2 h2
    · exact (h.ha _ _ _ _ h1 h2 huv).2
    · obtain ⟨e1, _⟩ := h.ha _ _ _ _ h1 (by omega) huv
      exact absurd (congrArg x e1) (h.hx i)
    · obtain ⟨e1, _⟩ := h.ha _ _ _ _ (by omega) h2 huv
      exact absurd (congrArg x e1).symm (h.hx i)
    · omega
  · unfold oddPath; split_ifs with h1
    · exact fun e => h.hax i k i h1 e.symm
    · exact fun e => h.hax (σ i) 0 i (by omega) e.symm
  · unfold oddPath; split_ifs with h1
    · exact fun e => h.hay i k i h1 e.symm
    · exact fun e => h.hay (σ i) 0 i (by omega) e.symm

theorem OddTransformerData.qx (h : OddTransformerData σ x y m a) (i : I) (k : ℕ) (j : I) :
    oddPath σ m a i k ≠ x j := by
  unfold oddPath; split_ifs with hk
  · exact h.hax i k j hk
  · exact h.hax (σ i) 0 j (by omega)

theorem OddTransformerData.qy (h : OddTransformerData σ x y m a) (i : I) (k : ℕ) (j : I) :
    oddPath σ m a i k ≠ y j := by
  unfold oddPath; split_ifs with hk
  · exact h.hay i k j hk
  · exact h.hay (σ i) 0 j (by omega)

theorem OddTransformerData.qeq (h : OddTransformerData σ x y m a) {i j : I} {k l : ℕ}
    (hk : k ≤ 2 * m + 1) (hl : l ≤ 2 * m + 1) (he : oddPath σ m a i k = oddPath σ m a j l) :
    (i = j ∧ k = l) ∨ (k = 0 ∧ l = 2 * m + 1 ∧ i = σ j) ∨
      (k = 2 * m + 1 ∧ l = 0 ∧ j = σ i) := by
  unfold oddPath at he
  split_ifs at he with h1 h2 h2
  · exact Or.inl (h.ha _ _ _ _ h1 h2 he)
  · obtain ⟨e1, e2⟩ := h.ha _ _ _ _ h1 (by omega) he
    exact Or.inr (Or.inl ⟨e2, by omega, e1⟩)
  · obtain ⟨e1, e2⟩ := h.ha _ _ _ _ (by omega) h2 he
    exact Or.inr (Or.inr ⟨by omega, e2.symm, e1.symm⟩)
  · obtain ⟨e1, _⟩ := h.ha _ _ _ _ (by omega) (by omega) he
    exact Or.inl ⟨σ.injective e1, by omega⟩

/-- Fans at different positions are edge-disjoint. -/
theorem OddTransformerData.fans_disjoint (h : OddTransformerData σ x y m a) {i j : I}
    (hij : i ≠ j) : Disjoint (fanEdges (x i) (y i) (oddPath σ m a i) m)
      (fanEdges (x j) (y j) (oddPath σ m a j) m) := by
  rw [disjoint_left]
  intro e he he'
  rw [mem_fanEdges (h.fanOK i)] at he
  rw [mem_fanEdges (h.fanOK j)] at he'
  rcases he with ⟨k, hk1, hk2, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ <;>
    rcases he' with ⟨l, hl1, hl2, h0⟩ | ⟨l, hl, h0⟩ | ⟨l, hl, h0⟩ <;>
    rcases Sym2.eq_iff.mp h0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  -- X / X
  · rcases h.qeq (by omega) (by omega) h2 with ⟨e1, _⟩ | ⟨e1, _, _⟩ | ⟨e1, _, _⟩
    · exact hij e1
    · omega
    · omega
  · exact h.qx _ _ _ h1.symm
  -- X / Y
  · exact h.hxy _ _ h1
  · exact h.qx _ _ _ h1.symm
  -- X / P
  · exact h.qx _ _ _ h1.symm
  · exact h.qx _ _ _ h1.symm
  -- Y / X
  · exact h.hxy _ _ h1.symm
  · exact h.qy _ _ _ h1.symm
  -- Y / Y
  · rcases h.qeq (by omega) (by omega) h2 with ⟨e1, _⟩ | ⟨_, _, e3⟩ | ⟨_, _, e3⟩
    · exact hij e1
    · rw [e3] at h1; exact h.hy j h1.symm
    · rw [e3] at h1; exact h.hy i h1
  · exact h.qy _ _ _ h1.symm
  -- Y / P
  · exact h.qy _ _ _ h1.symm
  · exact h.qy _ _ _ h1.symm
  -- P / X
  · exact h.qx _ _ _ h1
  · exact h.qx _ _ _ h2
  -- P / Y
  · exact h.qy _ _ _ h1
  · exact h.qy _ _ _ h2
  -- P / P
  · rcases h.qeq (by omega) (by omega) h1 with ⟨e1, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩
    · exact hij e1
    · omega
    · omega
  · rcases h.qeq (by omega) (by omega) h1 with ⟨e1, _⟩ | ⟨ek, _, e3⟩ | ⟨_, _, _⟩
    · exact hij e1
    · rcases h.qeq (by omega) (by omega) h2 with ⟨e1', _⟩ | ⟨_, _, _⟩ | ⟨_, _, e3'⟩
      · exact hij e1'
      · omega
      · apply hij
        apply h.hxinj
        show s(x i, x (σ i)) = s(x j, x (σ j))
        rw [← e3', ← e3]
        exact Sym2.eq_swap
    · omega

/-- `T ∪ Hx` is the union of the closing triangles and the fans. -/
theorem oddT_union_src (h : OddTransformerData σ x y m a) :
    oddT σ x y m a ∪ srcE σ x =
      coreE σ x a ∪ univ.biUnion fun i => fanEdges (x i) (y i) (oddPath σ m a i) m := by
  have tri : ∀ i, triEdges {x i, x (σ i), a (σ i) 0} =
      {s(x i, x (σ i)), s(x i, a (σ i) 0), s(x (σ i), a (σ i) 0)} := fun i =>
    triEdges_three (h.hx i) (fun e => h.hax (σ i) 0 i (by omega) e.symm)
      (fun e => h.hax (σ i) 0 (σ i) (by omega) e.symm)
  ext e
  simp only [oddT, srcE, coreE, spokesE, pathE, mem_union, mem_biUnion, mem_univ, true_and,
    mem_image, mem_range, tri, mem_insert, mem_singleton, mem_fanEdges (h.fanOK _)]
  constructor
  · rintro (((⟨i, k, hk, rfl⟩ | ⟨i, k, hk, rfl⟩) | ⟨i, k, hk, rfl⟩) | ⟨i, rfl⟩)
    · rcases (show k = 0 ∨ (1 ≤ k ∧ k ≤ 2 * m) ∨ k = 2 * m + 1 by omega) with rfl | hk' | rfl
      · refine Or.inl ⟨σ.symm i, Or.inr (Or.inr ?_)⟩
        rw [Equiv.apply_symm_apply, oddPath_le (by omega)]
      · exact Or.inr ⟨i, Or.inl ⟨k, hk'.1, hk'.2, rfl⟩⟩
      · exact Or.inl ⟨i, Or.inr (Or.inl (by rw [oddPath_top]))⟩
    · exact Or.inr ⟨i, Or.inr (Or.inl ⟨k, by omega, rfl⟩)⟩
    · exact Or.inr ⟨i, Or.inr (Or.inr ⟨k, by omega, rfl⟩)⟩
    · exact Or.inl ⟨i, Or.inl rfl⟩
  · rintro (⟨i, rfl | rfl | rfl⟩ | ⟨i, ⟨k, hk1, hk2, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩⟩)
    · exact Or.inr ⟨i, rfl⟩
    · exact Or.inl (Or.inl (Or.inl ⟨i, 2 * m + 1, by omega, by rw [oddPath_top]⟩))
    · exact Or.inl (Or.inl (Or.inl ⟨σ i, 0, by omega, by rw [oddPath_le (by omega)]⟩))
    · exact Or.inl (Or.inl (Or.inl ⟨i, k, by omega, rfl⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨i, k, by omega, rfl⟩))
    · exact Or.inl (Or.inr ⟨i, k, by omega, rfl⟩)

set_option hygiene false in
/-- Closing tactic for vertex coincidences in the transformer. -/
local macro "tclose" : tactic => `(tactic| first
  | exact absurd h1 (h.hax _ _ _ (by omega)) | exact absurd h1.symm (h.hax _ _ _ (by omega))
  | exact absurd h2 (h.hax _ _ _ (by omega)) | exact absurd h2.symm (h.hax _ _ _ (by omega))
  | exact absurd h1 (h.hay _ _ _ (by omega)) | exact absurd h1.symm (h.hay _ _ _ (by omega))
  | exact absurd h2 (h.hay _ _ _ (by omega)) | exact absurd h2.symm (h.hay _ _ _ (by omega))
  | exact absurd h1 (h.hxy _ _) | exact absurd h1.symm (h.hxy _ _)
  | exact absurd h2 (h.hxy _ _) | exact absurd h2.symm (h.hxy _ _))

/-- **Odd transformer, source mode.** -/
theorem oddTransformer_source {p : W → Fin t} {F : Finset (Multiset (Fin t))}
    (h : OddTransformerData σ x y m a) (hT : OddTypes p F σ x y m a) :
    HasDecomp p F (oddT σ x y m a ∪ srcE σ x) := by
  rw [oddT_union_src h]
  have tri : ∀ i, triEdges {x i, x (σ i), a (σ i) 0} =
      {s(x i, x (σ i)), s(x i, a (σ i) 0), s(x (σ i), a (σ i) 0)} := fun i =>
    triEdges_three (h.hx i) (fun e => h.hax (σ i) 0 i (by omega) e.symm)
      (fun e => h.hax (σ i) 0 (σ i) (by omega) e.symm)
  -- closing triangles
  have hcore : HasDecomp p F (coreE σ x a) := by
    refine hasDecomp_biUnion univ _ (fun i _ => hasDecomp_tri ?_ ?_) ?_
    · exact Finset.card_eq_three.mpr ⟨_, _, _, h.hx i,
        (fun e => h.hax (σ i) 0 i (by omega) e.symm),
        (fun e => h.hax (σ i) 0 (σ i) (by omega) e.symm), rfl⟩
    · rw [map_three p (h.hx i) (fun e => h.hax (σ i) 0 i (by omega) e.symm)
        (fun e => h.hax (σ i) 0 (σ i) (by omega) e.symm)]
      exact hT.hA i
    · intro i _ j _ hij
      rw [tri, tri, disjoint_left]
      intro e he he'
      simp only [mem_insert, mem_singleton] at he he'
      rcases he with rfl | rfl | rfl <;> rcases he' with h0 | h0 | h0
      · exact hij (h.hxinj h0)
      all_goals
        rcases Sym2.eq_iff.mp h0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        all_goals first
          | tclose
          | (obtain ⟨e1, _⟩ := h.ha _ _ _ _ (by omega) (by omega) h2
             exact hij (σ.injective e1))
          | (obtain ⟨e1, _⟩ := h.ha _ _ _ _ (by omega) (by omega) h1
             exact hij (σ.injective e1))
  -- fans
  have hfans : HasDecomp p F (univ.biUnion fun i => fanEdges (x i) (y i) (oddPath σ m a i) m) := by
    exact hasDecomp_biUnion univ _ (fun i _ => fan_hasDecomp (h.fanOK i) (hT.hpy i)
      (fun k hk => hT.hW i k hk)) (fun i _ j _ hij => h.fans_disjoint hij)
  -- closing triangles versus fans
  have hcf : Disjoint (coreE σ x a)
      (univ.biUnion fun i => fanEdges (x i) (y i) (oddPath σ m a i) m) := by
    rw [disjoint_left]
    intro e he he'
    simp only [coreE, mem_biUnion, mem_univ, true_and, tri, mem_insert, mem_singleton] at he
    simp only [mem_biUnion, mem_univ, true_and] at he'
    obtain ⟨i, he⟩ := he
    obtain ⟨j, he'⟩ := he'
    rw [mem_fanEdges (h.fanOK j)] at he'
    rcases he with rfl | rfl | rfl <;>
      rcases he' with ⟨l, hl1, hl2, h0⟩ | ⟨l, hl, h0⟩ | ⟨l, hl, h0⟩ <;>
      rcases Sym2.eq_iff.mp h0 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      first
      | exact h.hxy _ _ h1
      | exact h.qx _ _ _ h1.symm
      | exact h.qx _ _ _ h2.symm
      | (rw [oddPath_le (by omega)] at h2
         obtain ⟨_, e2⟩ := h.ha _ _ _ _ (by omega) (by omega) h2
         omega)
  exact hasDecomp_union hcore hfans hcf

/-- **Odd transformer, target mode.** -/
theorem oddTransformer_target {p : W → Fin t} {F : Finset (Multiset (Fin t))}
    (h : OddTransformerData σ x y m a) (hT : OddTypes p F σ x y m a) :
    HasDecomp p F (oddT σ x y m a ∪ srcE σ y) := by
  rw [oddT_comm]
  exact oddTransformer_source h.swap hT.swap

end PartitionedTriangleAbsorption.BlowupB
