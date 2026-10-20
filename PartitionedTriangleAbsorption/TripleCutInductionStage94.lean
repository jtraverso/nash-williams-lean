/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TripleCutStepStage94

/-! # Cutting all triples of a given disjoint family

A `TargetTriple` is combinatorial data only: three original tokens together
with corner labels `i, j, k` such that the tokens have endpoint-label types
`(i,j)`, `(j,k)`, `(k,i)` and `{i,j,k} ∈ F`. It is not a physical
decomposition of anything. Given a list of valid target triples whose token
sets are pairwise disjoint and contained in the remaining tokens, `cut_all`
cuts them one after another with `cut_triple`.

Budget: `|Z| + 4 (d + |U|) + 330 r < a` for `r` triples. Each cut adds at
most `6` active vertices and `81` ledger edges, and needs
`234 + |Z| + 4 (d + |U|) < a`; `330 = 6 + 4 · 81`. The result is a trace of
exactly `9 r` moves with ledger growth at most `81 r`, every triple an
isolated allowed triangle in the final configuration, the boundary invariant
for the rest, and a continuation from the final ledger.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TripleCutStage94

open Finset AntiEdgeSelection TypedTransformer CatalystInsertionStage89 PhysicalMovesStage86

variable {V : Type*} [DecidableEq V] {t : ℕ}

/-- A prescribed target triple: three original tokens and their corner labels. -/
structure TargetTriple (V : Type*) (t : ℕ) where
  e₁ : Sym2 V
  e₂ : Sym2 V
  e₃ : Sym2 V
  i : Fin t
  j : Fin t
  k : Fin t

/-- The three tokens of a target triple. -/
def TargetTriple.toks (T : TargetTriple V t) : Finset (Sym2 V) := {T.e₁, T.e₂, T.e₃}

/-- Label validity of a target triple (purely combinatorial). -/
structure TargetTriple.Valid (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (T : TargetTriple V t) : Prop where
  ne₁₂ : T.e₁ ≠ T.e₂
  ne₁₃ : T.e₁ ≠ T.e₃
  ne₂₃ : T.e₂ ≠ T.e₃
  ty₁ : Sym2.map p T.e₁ = s(T.i, T.j)
  ty₂ : Sym2.map p T.e₂ = s(T.j, T.k)
  ty₃ : Sym2.map p T.e₃ = s(T.k, T.i)
  link : Link F T.i T.j T.k

/-- All tokens of a list of target triples. -/
def allToks : List (TargetTriple V t) → Finset (Sym2 V)
  | [] => ∅
  | T :: Ts => T.toks ∪ allToks Ts

@[simp] theorem allToks_nil : allToks ([] : List (TargetTriple V t)) = ∅ := rfl

@[simp] theorem allToks_cons (T : TargetTriple V t) (Ts : List (TargetTriple V t)) :
    allToks (T :: Ts) = T.toks ∪ allToks Ts := rfl

theorem allToks_subset {Ts : List (TargetTriple V t)} {X : Finset (Sym2 V)}
    (h : ∀ T ∈ Ts, T.toks ⊆ X) : allToks Ts ⊆ X := by
  induction Ts with
  | nil => simp
  | cons T Ts ih =>
    rw [allToks_cons]
    exact union_subset (h T (List.mem_cons_self ..))
      (ih fun T' hT' => h T' (List.mem_cons_of_mem _ hT'))

theorem disjoint_allToks {Ts : List (TargetTriple V t)} {X : Finset (Sym2 V)}
    (h : ∀ T ∈ Ts, Disjoint X T.toks) : Disjoint X (allToks Ts) := by
  induction Ts with
  | nil => simp
  | cons T Ts ih =>
    rw [allToks_cons, disjoint_union_right]
    exact ⟨h T (List.mem_cons_self ..), ih fun T' hT' => h T' (List.mem_cons_of_mem _ hT')⟩

/-- A finished triangle survives a later cut of a disjoint triple. -/
theorem TriangleCut.persist {p : V → Fin t} {F : Finset (Multiset (Fin t))} {S : Data V}
    {pos pos' : Tok V → Sym2 V} {e₁ e₂ e₃ : Sym2 V} {i j k : Fin t} {zA zB zC : V}
    (h : TriangleCut p F S pos e₁ e₂ e₃ i j k zA zB zC)
    (hpos : ∀ e ∈ ({e₁, e₂, e₃} : Finset (Sym2 V)), pos' (.inl e) = pos (.inl e))
    (hat : ∀ v ∈ ({zA, zB, zC} : Finset V), tokAtP S pos' v = tokAtP S pos v) :
    TriangleCut p F S pos' e₁ e₂ e₃ i j k zA zB zC := by
  refine ⟨h.ne, h.label, ?_, ?_, ?_, h.decomp, ?_, ?_, ?_⟩
  · rw [hpos e₁ (by simp)]; exact h.pos₁
  · rw [hpos e₂ (by simp)]; exact h.pos₂
  · rw [hpos e₃ (by simp)]; exact h.pos₃
  · rw [hat zA (by simp)]; exact h.atA
  · rw [hat zB (by simp)]; exact h.atB
  · rw [hat zC (by simp)]; exact h.atC

/-- A vertex of a finished triangle carries no token outside the triple. -/
theorem TriangleCut.not_mem {p : V → Fin t} {F : Finset (Multiset (Fin t))} {S : Data V}
    {pos : Tok V → Sym2 V} {e₁ e₂ e₃ : Sym2 V} {i j k : Fin t} {zA zB zC : V}
    (h : TriangleCut p F S pos e₁ e₂ e₃ i j k zA zB zC) {v : V}
    (hv : v ∈ ({zA, zB, zC} : Finset V)) {e : Sym2 V} (he : e ∈ S.Y)
    (hne : e ∉ ({e₁, e₂, e₃} : Finset (Sym2 V))) : v ∉ pos (.inl e) := by
  intro hm
  have hq : (.inl e : Tok V) ∈ tokAtP S pos v := mem_tokAtP.mpr ⟨(mem_tokens_inl e).mpr he, hm⟩
  simp only [mem_insert, mem_singleton] at hv hne
  rcases hv with rfl | rfl | rfl
  · rw [h.atA] at hq; simp only [mem_insert, mem_singleton, Sum.inl.injEq] at hq; tauto
  · rw [h.atB] at hq; simp only [mem_insert, mem_singleton, Sum.inl.injEq] at hq; tauto
  · rw [h.atC] at hq; simp only [mem_insert, mem_singleton, Sum.inl.injEq] at hq; tauto

variable [Fintype V]

/-- **Cutting every triple of a given disjoint family.** -/
theorem cut_all {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G : SimpleGraph V} [DecidableRel G.Adj] {B : Finset (Sym2 V)} (a d : ℝ)
    (hF : ThreeStepLinks F) (hs : PairMoveSelectionStage85.CompatibleSupply p F G a)
    (hB : DegBounded B d) (hd : 0 ≤ d) {S : Data V} :
    ∀ (Ts : List (TargetTriple V t)) (pos : Tok V → Sym2 V) (R U : Finset (Sym2 V))
      (Z : Finset V),
      Phys p F G B S.tokens pos U Z → Bdry p F S pos R →
      (∀ T ∈ Ts, T.Valid p F ∧ T.toks ⊆ R) →
      Ts.Pairwise (fun T T' => Disjoint T.toks T'.toks) →
      (Z.card : ℝ) + 4 * (d + U.card) + 330 * Ts.length < a →
      ∃ (pos' : Tok V → Sym2 V) (U' : Finset (Sym2 V)) (Z' : Finset V),
        Phys p F G B S.tokens pos' U' Z' ∧ Bdry p F S pos' (R \ allToks Ts) ∧
        (∀ T ∈ Ts, ∃ zA zB zC : V, TriangleCut p F S pos' T.e₁ T.e₂ T.e₃ T.i T.j T.k zA zB zC) ∧
        (∀ e, e ∉ allToks Ts → pos' (.inl e) = pos (.inl e)) ∧
        (∀ y, pos' (.inr (y, 2)) = pos (.inr (y, 2))) ∧
        (∀ v ∈ Z, (∀ e ∈ allToks Ts, v ∉ pos (.inl e)) → tokAtP S pos' v = tokAtP S pos v) ∧
        Z ⊆ Z' ∧ Z'.card ≤ Z.card + 6 * Ts.length ∧
        U ⊆ U' ∧ U'.card ≤ U.card + 81 * Ts.length ∧
        PhysicalMoves p F G.edgeFinset B U (S.tokens.image pos) (S.tokens.image pos')
          (9 * Ts.length) ∧
        ∀ W m, PhysicalMoves p F G.edgeFinset B U' (S.tokens.image pos') W m →
          PhysicalMoves p F G.edgeFinset B U (S.tokens.image pos) W (9 * Ts.length + m) := by
  intro Ts
  induction Ts with
  | nil =>
    intro pos R U Z ph bd _ _ _
    refine ⟨pos, U, Z, ph, by simpa using bd, by simp, fun _ _ => rfl, fun _ => rfl,
      fun _ _ _ => rfl, Subset.refl _, by simp, Subset.refl _, by simp, .stop _ _, ?_⟩
    intro W m h
    simpa using h
  | cons T Ts ih =>
    intro pos R U Z ph bd hval hpw hb
    obtain ⟨⟨n12, n13, n23, ty₁, ty₂, ty₃, hl⟩, hTR⟩ := hval T (List.mem_cons_self ..)
    have hm : ∀ e ∈ T.toks, e ∈ R := fun e he => hTR he
    have h₁ : T.e₁ ∈ R := hm _ (by simp [TargetTriple.toks])
    have h₂ : T.e₂ ∈ R := hm _ (by simp [TargetTriple.toks])
    have h₃ : T.e₃ ∈ R := hm _ (by simp [TargetTriple.toks])
    have hlen : ((T :: Ts).length : ℝ) = Ts.length + 1 := by simp
    have hL0 : (0 : ℝ) ≤ Ts.length := Nat.cast_nonneg _
    obtain ⟨pos₁, U₁, Z₁, zA, zB, zC, ph₁, bd₁, tri, hzA, hzB, hzC, unO₁, un2₁, loc₁, hZZ₁,
        hZ₁, hUU₁, hU₁, htr₁, hcont₁⟩ :=
      cut_triple a d hF hs hB hd ph bd h₁ h₂ h₃ n12 n13 n23 ty₁ ty₂ ty₃ hl
        (by rw [hlen] at hb; linarith)
    rw [List.pairwise_cons] at hpw
    have hdisj : ∀ T' ∈ Ts, Disjoint T.toks T'.toks := hpw.1
    have hdisjAll : Disjoint T.toks (allToks Ts) := disjoint_allToks hdisj
    have hval' : ∀ T' ∈ Ts, T'.Valid p F ∧ T'.toks ⊆ R \ T.toks := by
      intro T' hT'
      obtain ⟨hv, hsub⟩ := hval T' (List.mem_cons_of_mem _ hT')
      refine ⟨hv, fun e he => mem_sdiff.mpr ⟨hsub he, fun h => ?_⟩⟩
      exact disjoint_left.mp (hdisj T' hT') h he
    have hZ₁r : (Z₁.card : ℝ) ≤ Z.card + 6 := by exact_mod_cast hZ₁
    have hU₁r : (U₁.card : ℝ) ≤ U.card + 81 := by exact_mod_cast hU₁
    have hRT : R \ {T.e₁, T.e₂, T.e₃} = R \ T.toks := rfl
    rw [hRT] at bd₁
    obtain ⟨pos₂, U₂, Z₂, ph₂, bd₂, tris, unO₂, un2₂, loc₂, hZZ₂, hZ₂, hUU₂, hU₂, htr₂, hcont₂⟩ :=
      ih pos₁ (R \ T.toks) U₁ Z₁ ph₁ bd₁ hval' hpw.2 (by rw [hlen] at hb; linarith)
    have hRR : (R \ T.toks) \ allToks Ts = R \ allToks (T :: Ts) := by
      rw [allToks_cons, sdiff_sdiff_left]; rfl
    rw [hRR] at bd₂
    -- the first triangle survives the later cuts
    have hYT : ∀ e ∈ T.toks, e ∈ S.Y := fun e he => bd.rem (hm e he)
    have tri' : TriangleCut p F S pos₂ T.e₁ T.e₂ T.e₃ T.i T.j T.k zA zB zC := by
      refine tri.persist (fun e he => unO₂ e (fun h => disjoint_left.mp hdisjAll he h)) ?_
      intro v hv
      have hvZ : v ∈ Z₁ := by
        have hq : (.inl T.e₁ : Tok V) ∈ S.tokens :=
          (mem_tokens_inl _).mpr (hYT _ (by simp [TargetTriple.toks]))
        simp only [mem_insert, mem_singleton] at hv
        rcases hv with rfl | rfl | rfl
        · exact ph₁.supp _ hq _ (by rw [tri.pos₁]; exact Sym2.mem_mk_left _ _)
        · exact ph₁.supp _ hq _ (by rw [tri.pos₁]; exact Sym2.mem_mk_right _ _)
        · have hq₂ : (.inl T.e₂ : Tok V) ∈ S.tokens :=
            (mem_tokens_inl _).mpr (hYT _ (by simp [TargetTriple.toks]))
          exact ph₁.supp _ hq₂ _ (by rw [tri.pos₂]; exact Sym2.mem_mk_right _ _)
      refine loc₂ v hvZ fun e he => ?_
      have heY : e ∈ S.Y :=
        bd.rem (allToks_subset (fun T' hT' => (hval T' (List.mem_cons_of_mem _ hT')).2) he)
      exact tri.not_mem hv heY (fun h => disjoint_left.mp hdisjAll h he)
    have notT : ∀ {e}, e ∉ T.toks → e ≠ T.e₁ ∧ e ≠ T.e₂ ∧ e ≠ T.e₃ := by
      intro e he
      simp only [TargetTriple.toks, mem_insert, mem_singleton, not_or] at he
      exact he
    have hlen' : (T :: Ts).length = Ts.length + 1 := List.length_cons
    refine ⟨pos₂, U₂, Z₂, ph₂, bd₂, ?_, ?_, ?_, ?_, hZZ₁.trans hZZ₂, ?_, hUU₁.trans hUU₂, ?_, ?_,
      ?_⟩
    · intro T' hT'
      rcases List.mem_cons.mp hT' with rfl | hT'
      · exact ⟨zA, zB, zC, tri'⟩
      · exact tris T' hT'
    · intro e he
      simp only [allToks_cons, mem_union, not_or] at he
      obtain ⟨c1, c2, c3⟩ := notT he.1
      rw [unO₂ e he.2, unO₁ e c1 c2 c3]
    · intro y
      rw [un2₂, un2₁]
    · intro v hv hnot
      have h1 : tokAtP S pos₁ v = tokAtP S pos v :=
        loc₁ v hv (hnot _ (by simp [TargetTriple.toks])) (hnot _ (by simp [TargetTriple.toks]))
          (hnot _ (by simp [TargetTriple.toks]))
      rw [← h1]
      refine loc₂ v (hZZ₁ hv) fun e he => ?_
      have heT : e ∉ T.toks := fun h => disjoint_left.mp hdisjAll h he
      obtain ⟨c1, c2, c3⟩ := notT heT
      rw [unO₁ e c1 c2 c3]
      exact hnot e (by simp [he])
    · rw [hlen']; omega
    · rw [hlen']; omega
    · have h := hcont₁ _ _ htr₂
      rwa [show 9 + 9 * Ts.length = 9 * (T :: Ts).length by rw [hlen']; ring] at h
    · intro W m h
      have h' := hcont₁ _ _ (hcont₂ W m h)
      rwa [show 9 + (9 * Ts.length + m) = 9 * (T :: Ts).length + m by rw [hlen']; ring] at h'

end PartitionedTriangleAbsorption.TripleCutStage94
