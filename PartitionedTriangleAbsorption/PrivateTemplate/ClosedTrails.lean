/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PrivateTemplate.TriangleBlocks

/-!
# Closed-trail systems of even graphs

A *closed-trail system* of a loopless edge set `P` is a finite set of positions with a
successor permutation `σ` and a vertex `X i` at each position such that
`i ↦ X i X (σ i)` is a bijection onto `P` and `X i ≠ X (σ i)`.  Every orbit of `σ` is a
closed trail; the system is the same thing as a decomposition of `P` into closed trails
together with an orientation of each.

We prove that every loopless edge set with all degrees even has such a system, indexed by
`Fin P.card`.  The proof is a direct induction (splitting off a pair of edges `va, vb` at a
vertex `v`), with no appeal to an external Euler/Veblen theorem.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PrivateTemplate

open Finset OnePart AntiEdgeSelection

variable {V : Type*} [DecidableEq V]

/-- A closed-trail system of `P`. -/
structure IsTrailSystem {I : Type*} (P : Finset (Sym2 V)) (σ : Equiv.Perm I) (X : I → V) :
    Prop where
  ne : ∀ i, X i ≠ X (σ i)
  inj : Function.Injective fun i => s(X i, X (σ i))
  mem : ∀ e, e ∈ P ↔ ∃ i, e = s(X i, X (σ i))

/-- Inserting a vertex `v` into the trail edge at position `j0`. -/
theorem IsTrailSystem.insert_step {I : Type*} [Finite I]
    {P' : Finset (Sym2 V)} {σ : Equiv.Perm I} {X : I → V} (h : IsTrailSystem P' σ X)
    (j0 : I) (v : V) (hv1 : v ≠ X j0) (hv2 : v ≠ X (σ j0))
    (hn1 : s(X j0, v) ∉ P') (hn2 : s(v, X (σ j0)) ∉ P') :
    ∃ (σ' : Equiv.Perm (Option I)) (X' : Option I → V),
      IsTrailSystem (insert s(X j0, v) (insert s(v, X (σ j0)) (P'.erase s(X j0, X (σ j0)))))
        σ' X' := by
  classical
  let f : Option I → Option I := fun p =>
    match p with
    | none => some (σ j0)
    | some i => if i = j0 then none else some (σ i)
  have hf : Function.Injective f := by
    intro p q hpq
    rcases p with _ | i <;> rcases q with _ | j
    · rfl
    · simp only [f] at hpq
      split_ifs at hpq with hj
      exact absurd (σ.injective (Option.some.inj hpq)).symm hj
    · simp only [f] at hpq
      split_ifs at hpq with hi
      exact absurd (σ.injective (Option.some.inj hpq)) hi
    · simp only [f] at hpq
      split_ifs at hpq with hi hj hj
      · rw [hi, hj]
      · exact congrArg some (σ.injective (Option.some.inj hpq))
  let σ' : Equiv.Perm (Option I) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
  let X' : Option I → V := fun p => match p with
    | none => v
    | some i => X i
  have hσn : σ' none = some (σ j0) := rfl
  have hσj : σ' (some j0) = none := by simp [σ', f]
  have hσi : ∀ i, i ≠ j0 → σ' (some i) = some (σ i) := by
    intro i hi; simp [σ', f, hi]
  have hE : ∀ p, s(X' p, X' (σ' p)) =
      match p with
      | none => s(v, X (σ j0))
      | some i => if i = j0 then s(X j0, v) else s(X i, X (σ i)) := by
    rintro (_ | i)
    · rw [hσn]
    · by_cases hi : i = j0
      · subst hi; rw [hσj]; simp [X']
      · rw [hσi i hi]; simp [X', hi]
  have hmemP : ∀ i, s(X i, X (σ i)) ∈ P' := fun i => (h.mem _).mpr ⟨i, rfl⟩
  refine ⟨σ', X', ⟨?_, ?_, ?_⟩⟩
  · rintro (_ | i)
    · rw [hσn]; exact hv2
    · by_cases hi : i = j0
      · subst hi; rw [hσj]; exact fun e => hv1 e.symm
      · rw [hσi i hi]; exact h.ne i
  · intro p q hpq
    simp only [hE] at hpq
    rcases p with _ | i <;> rcases q with _ | j
    · rfl
    · simp only at hpq
      split_ifs at hpq with hj
      · rcases Sym2.eq_iff.mp hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact absurd h1 hv1
        · exact absurd h2.symm (h.ne j0)
      · exact absurd (hpq ▸ hmemP j) hn2
    · simp only at hpq
      split_ifs at hpq with hi
      · rcases Sym2.eq_iff.mp hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact absurd h1.symm hv1
        · exact absurd h1 (h.ne j0)
      · exact absurd (hpq ▸ hmemP i) hn2
    · simp only at hpq
      split_ifs at hpq with hi hj hj
      · rw [hi, hj]
      · exact absurd (hpq ▸ hmemP j) hn1
      · exact absurd (hpq.symm ▸ hmemP i) hn1
      · exact congrArg some (h.inj hpq)
  · intro e
    simp only [hE, mem_insert, mem_erase]
    constructor
    · rintro (rfl | rfl | ⟨hne, he⟩)
      · exact ⟨some j0, by simp⟩
      · exact ⟨none, rfl⟩
      · obtain ⟨i, rfl⟩ := (h.mem e).mp he
        refine ⟨some i, ?_⟩
        have hi : i ≠ j0 := by rintro rfl; exact hne rfl
        simp [hi]
    · rintro ⟨_ | i, rfl⟩
      · exact Or.inr (Or.inl rfl)
      · by_cases hi : i = j0
        · subst hi; simp
        · simp only [hi, ite_false]
          refine Or.inr (Or.inr ⟨fun he => hi (h.inj he), hmemP i⟩)

/-- Appending a disjoint triangle `v a b` as a new closed trail. -/
theorem IsTrailSystem.triangle_step {I : Type*} {P'' : Finset (Sym2 V)}
    {σ : Equiv.Perm I} {X : I → V} (h : IsTrailSystem P'' σ X) (v a b : V)
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (h1 : s(v, a) ∉ P'') (h2 : s(a, b) ∉ P'') (h3 : s(b, v) ∉ P'') :
    ∃ (σ' : Equiv.Perm (I ⊕ Fin 3)) (X' : I ⊕ Fin 3 → V),
      IsTrailSystem (P'' ∪ {s(v, a), s(a, b), s(b, v)}) σ' X' := by
  let σ' : Equiv.Perm (I ⊕ Fin 3) := Equiv.sumCongr σ (finRotate 3)
  let X' : I ⊕ Fin 3 → V := Sum.elim X ![v, a, b]
  have hr0 : finRotate 3 0 = 1 := rfl
  have hr1 : finRotate 3 1 = 2 := rfl
  have hr2 : finRotate 3 2 = 0 := rfl
  have hE : ∀ k : Fin 3, s(X' (Sum.inr k), X' (σ' (Sum.inr k))) =
      ![s(v, a), s(a, b), s(b, v)] k := by
    intro k; fin_cases k <;> simp [X', σ', hr0, hr1, hr2]
  have hEl : ∀ i, s(X' (Sum.inl i), X' (σ' (Sum.inl i))) = s(X i, X (σ i)) := fun i => rfl
  have hmemP : ∀ i, s(X i, X (σ i)) ∈ P'' := fun i => (h.mem _).mpr ⟨i, rfl⟩
  have hnot : ∀ k : Fin 3, ![s(v, a), s(a, b), s(b, v)] k ∉ P'' := by
    intro k; fin_cases k <;> simpa
  refine ⟨σ', X', ⟨?_, ?_, ?_⟩⟩
  · rintro (i | k)
    · exact h.ne i
    · fin_cases k <;> simp [X', σ', hr0, hr1, hr2, hva, hab, hvb.symm]
  · rintro (i | k) (j | l) hpq
    · exact congrArg Sum.inl (h.inj hpq)
    · have := hpq
      simp only [hEl, hE] at this
      exact absurd (this ▸ hmemP i) (hnot l)
    · have := hpq
      simp only [hEl, hE] at this
      exact absurd (this.symm ▸ hmemP j) (hnot k)
    · have := hpq
      simp only [hE] at this
      fin_cases k <;> fin_cases l <;>
        simp [hva, hvb, hab, hva.symm, hvb.symm, hab.symm] at this ⊢
  · intro e
    simp only [mem_union, mem_insert, mem_singleton]
    constructor
    · rintro (he | rfl | rfl | rfl)
      · obtain ⟨i, rfl⟩ := (h.mem e).mp he
        exact ⟨Sum.inl i, rfl⟩
      · exact ⟨Sum.inr 0, (hE 0).symm⟩
      · exact ⟨Sum.inr 1, (hE 1).symm⟩
      · exact ⟨Sum.inr 2, (hE 2).symm⟩
    · rintro ⟨i | k, rfl⟩
      · exact Or.inl (hmemP i)
      · rw [hE k]; fin_cases k <;> simp


/-! ### Degree bookkeeping for the splitting step -/

theorem even_incidentLoad_tri {v a b : V} (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b) (w : V) :
    Even (incidentLoad ({s(v, a), s(a, b), s(b, v)} : Finset (Sym2 V)) w) := by
  have hav := hva.symm
  have hbv := hvb.symm
  have hba := hab.symm
  unfold incidentLoad
  rw [filter_insert, filter_insert, filter_singleton]
  by_cases h1 : w = v
  · subst h1; simp [*]
  by_cases h2 : w = a
  · subst h2; simp [*]
  by_cases h3 : w = b
  · subst h3; simp [*]
  simp [*]

theorem even_incidentLoad_pair_add {v a b : V} (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (w : V) :
    Even (incidentLoad ({s(v, a), s(v, b)} : Finset (Sym2 V)) w +
      incidentLoad ({s(a, b)} : Finset (Sym2 V)) w) := by
  have hav := hva.symm
  have hbv := hvb.symm
  have hba := hab.symm
  unfold incidentLoad
  rw [filter_insert, filter_singleton, filter_singleton]
  by_cases h1 : w = v
  · subst h1; simp [*]
  by_cases h2 : w = a
  · subst h2; simp [*]
  by_cases h3 : w = b
  · subst h3; simp [*]
  simp [*]

/-! ### Existence -/

theorem exists_trailSystem_aux (n : ℕ) : ∀ P : Finset (Sym2 V), P.card = n →
    (∀ e ∈ P, ¬ e.IsDiag) → (∀ w, Even (incidentLoad P w)) →
    ∃ (I : Type) (_ : Fintype I) (σ : Equiv.Perm I) (X : I → V), IsTrailSystem P σ X := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hcard hloop heven
  rcases P.eq_empty_or_nonempty with rfl | ⟨e, he⟩
  · exact ⟨Empty, inferInstance, Equiv.refl _, Empty.elim,
      ⟨fun i => i.elim, fun i => i.elim, fun e => by simp⟩⟩
  induction e using Sym2.ind with
  | _ v a =>
  have hva : v ≠ a := fun h => hloop _ he (by simp [h])
  -- a second edge at `v`
  have hload : 2 ≤ incidentLoad P v := by
    have h1 : 1 ≤ incidentLoad P v :=
      card_pos.mpr ⟨s(v, a), mem_filter.mpr ⟨he, Sym2.mem_mk_left v a⟩⟩
    obtain ⟨k, hk⟩ := heven v
    omega
  obtain ⟨e', he', hne'⟩ : ∃ e' ∈ P.filter (fun e => v ∈ e), e' ≠ s(v, a) := by
    by_contra hcon
    push Not at hcon
    have : P.filter (fun e => v ∈ e) ⊆ {s(v, a)} := fun e he => mem_singleton.mpr (hcon e he)
    have := card_le_card this
    simp only [card_singleton] at this
    unfold incidentLoad at hload
    omega
  obtain ⟨he'P, hve'⟩ := mem_filter.mp he'
  obtain ⟨b, rfl⟩ := Sym2.mem_iff_exists.mp hve'
  have hvb : v ≠ b := fun h => hloop _ he'P (by simp [h])
  have hab : a ≠ b := by rintro rfl; exact hne' rfl
  have hav := hva.symm
  have hbv := hvb.symm
  have hba := hab.symm
  by_cases habP : s(a, b) ∈ P
  · -- remove the triangle `v a b`
    set T3 : Finset (Sym2 V) := {s(v, a), s(a, b), s(b, v)} with hT3
    have hT3P : T3 ⊆ P := by
      intro e he
      simp only [hT3, mem_insert, mem_singleton] at he
      rcases he with rfl | rfl | rfl
      · exact he
      · exact habP
      · rw [Sym2.eq_swap]; exact he'P
    set P'' := P \ T3
    have hcardT3 : T3.card = 3 := by
      rw [hT3, card_insert_of_notMem, card_insert_of_notMem, card_singleton]
      · simp [*]
      · simp [*]
    have hPeq : P = P'' ∪ T3 := (sdiff_union_of_subset hT3P).symm
    have hdisj : Disjoint P'' T3 := sdiff_disjoint
    have hcard'' : P''.card = n - 3 := by
      rw [card_sdiff_of_subset hT3P, hcardT3, hcard]
    have hn : 3 ≤ n := hcard ▸ hcardT3 ▸ card_le_card hT3P
    have heven'' : ∀ w, Even (incidentLoad P'' w) := by
      intro w
      have h := heven w
      rw [hPeq, incidentLoad_union hdisj] at h
      exact (Nat.even_add.mp h).mpr (even_incidentLoad_tri hva hvb hab w)
    obtain ⟨I, _, σ, X, hX⟩ := ih (n - 3) (by omega) P'' hcard''
      (fun e he => hloop e (sdiff_subset he)) heven''
    have hn1 : s(v, a) ∉ P'' := fun h => (mem_sdiff.mp h).2 (by simp [hT3])
    have hn2 : s(a, b) ∉ P'' := fun h => (mem_sdiff.mp h).2 (by simp [hT3])
    have hn3 : s(b, v) ∉ P'' := fun h => (mem_sdiff.mp h).2 (by simp [hT3])
    obtain ⟨σ', X', hX'⟩ := hX.triangle_step v a b hva hvb hab hn1 hn2 hn3
    exact ⟨I ⊕ Fin 3, inferInstance, σ', X', hPeq ▸ hX'⟩
  · -- replace the path `a v b` by the edge `a b`
    set Q := P \ {s(v, a), s(v, b)} with hQ
    have hpairP : ({s(v, a), s(v, b)} : Finset (Sym2 V)) ⊆ P := by
      intro e he
      simp only [mem_insert, mem_singleton] at he
      rcases he with rfl | rfl
      exacts [he, he'P]
    have hcard2 : ({s(v, a), s(v, b)} : Finset (Sym2 V)).card = 2 := by
      rw [card_insert_of_notMem, card_singleton]
      simp [*]
    have habQ : s(a, b) ∉ Q := fun h => habP (sdiff_subset h)
    set P' := insert s(a, b) Q with hP'
    have hcardQ : Q.card = n - 2 := by
      rw [hQ, card_sdiff_of_subset hpairP, hcard2, hcard]
    have hn : 2 ≤ n := hcard ▸ hcard2 ▸ card_le_card hpairP
    have hcard' : P'.card = n - 1 := by
      rw [hP', card_insert_of_notMem habQ, hcardQ]; omega
    have hPeq : P = Q ∪ {s(v, a), s(v, b)} := (sdiff_union_of_subset hpairP).symm
    have hP'eq : P' = Q ∪ {s(a, b)} := by
      rw [hP', union_comm]; rfl
    have heven' : ∀ w, Even (incidentLoad P' w) := by
      intro w
      have h := heven w
      rw [hPeq, incidentLoad_union sdiff_disjoint] at h
      rw [hP'eq, incidentLoad_union (disjoint_singleton_right.mpr habQ)]
      have h2 := even_incidentLoad_pair_add hva hvb hab w
      rw [Nat.even_add] at h h2 ⊢
      tauto
    have hloop' : ∀ e ∈ P', ¬ e.IsDiag := by
      intro e he
      rcases mem_insert.mp he with rfl | he
      · simpa using hab
      · exact hloop e (sdiff_subset he)
    obtain ⟨I, _, σ, X, hX⟩ := ih (n - 1) (by omega) P' hcard' hloop' heven'
    classical
    obtain ⟨j0, hj0⟩ := (hX.mem (s(a, b))).mp (mem_insert_self _ _)
    -- orient so that the trail edge at `j0` is `a → b`
    have key : ∀ a' b' : V, s(a', b') = s(a, b) → X j0 = a' → X (σ j0) = b' →
        ∃ (I' : Type) (_ : Fintype I') (σ' : Equiv.Perm I') (X' : I' → V),
          IsTrailSystem P σ' X' := by
      intro a' b' hab' ha' hb'
      have hva' : v ≠ X j0 := by
        rw [ha']; rcases Sym2.eq_iff.mp hab' with ⟨rfl, -⟩ | ⟨rfl, -⟩
        exacts [hva, hvb]
      have hvb' : v ≠ X (σ j0) := by
        rw [hb']; rcases Sym2.eq_iff.mp hab' with ⟨-, rfl⟩ | ⟨-, rfl⟩
        exacts [hvb, hva]
      have hpair : ({s(X j0, v), s(v, X (σ j0))} : Finset (Sym2 V)) =
          {s(v, a), s(v, b)} := by
        rw [ha', hb']
        rcases Sym2.eq_iff.mp hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [Sym2.eq_swap]
        · rw [Sym2.eq_swap, pair_comm]
      have hnot : ∀ e ∈ ({s(X j0, v), s(v, X (σ j0))} : Finset (Sym2 V)), e ∉ P' := by
        rw [hpair]
        intro e he heP'
        rcases mem_insert.mp heP' with rfl | heQ
        · simp only [mem_insert, mem_singleton] at he
          rcases he with h | h <;> rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
            first
            | exact hva h1.symm | exact hvb h1.symm | exact hva h2.symm | exact hvb h2.symm
        · exact (mem_sdiff.mp heQ).2 he
      obtain ⟨σ', X', hX'⟩ := hX.insert_step j0 v hva' hvb'
        (hnot _ (by simp)) (hnot _ (by simp))
      refine ⟨Option I, inferInstance, σ', X', ?_⟩
      have hset : insert s(X j0, v) (insert s(v, X (σ j0)) (P'.erase s(X j0, X (σ j0)))) =
          P := by
        ext e
        have hp := congrArg (e ∈ ·) hpair
        simp only [mem_insert, mem_singleton, eq_iff_iff] at hp
        rw [← hj0, hP', erase_insert habQ, hPeq]
        simp only [mem_insert, mem_union, mem_singleton]
        tauto
      rw [← hset]; exact hX'
    rcases Sym2.eq_iff.mp hj0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact key a b rfl h1.symm h2.symm
    · exact key b a Sym2.eq_swap h2.symm h1.symm


omit [DecidableEq V] in
theorem IsTrailSystem.card_eq {I : Type*} [Fintype I] {P : Finset (Sym2 V)}
    {σ : Equiv.Perm I} {X : I → V} (h : IsTrailSystem P σ X) : Fintype.card I = P.card := by
  classical
  have hP : P = univ.image fun i => s(X i, X (σ i)) := by
    ext e; rw [h.mem e]; simp [eq_comm]
  rw [hP, card_image_of_injective _ h.inj, card_univ]

/-- **Closed-trail systems exist.** Every loopless edge set with all degrees even has a
closed-trail system indexed by `Fin P.card`. -/
theorem exists_trailSystem (P : Finset (Sym2 V)) (hloop : ∀ e ∈ P, ¬ e.IsDiag)
    (heven : ∀ w, Even (incidentLoad P w)) :
    ∃ (σ : Equiv.Perm (Fin P.card)) (X : Fin P.card → V), IsTrailSystem P σ X := by
  obtain ⟨I, _, σ, X, hX⟩ := exists_trailSystem_aux P.card P rfl hloop heven
  let e : I ≃ Fin P.card := Fintype.equivFinOfCardEq hX.card_eq
  refine ⟨e.symm.trans (σ.trans e), X ∘ e.symm, ⟨?_, ?_, ?_⟩⟩
  · intro j
    simpa using hX.ne (e.symm j)
  · intro j k hjk
    have := hX.inj (a₁ := e.symm j) (a₂ := e.symm k) (by simpa using hjk)
    simpa using this
  · intro f
    rw [hX.mem f]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨e i, by simp⟩
    · rintro ⟨j, rfl⟩; exact ⟨e.symm j, by simp⟩

/-- In a closed-trail system every vertex is the tail of exactly half of its edges. -/
theorem IsTrailSystem.two_mul_card_tail {I : Type*} [Fintype I]
    {P : Finset (Sym2 V)} {σ : Equiv.Perm I} {X : I → V} (h : IsTrailSystem P σ X) (w : V) :
    2 * (univ.filter fun i => X i = w).card = incidentLoad P w := by
  classical
  have hP : P = univ.image fun i => s(X i, X (σ i)) := by
    ext e; rw [h.mem e]; simp [eq_comm]
  have hfil : P.filter (fun e => w ∈ e) =
      ((univ.filter fun i => X i = w) ∪ (univ.filter fun i => X (σ i) = w)).image
        fun i => s(X i, X (σ i)) := by
    rw [hP, filter_image]
    congr 1
    ext i
    simp [eq_comm]
  have hdisj : Disjoint (univ.filter fun i => X i = w) (univ.filter fun i => X (σ i) = w) := by
    rw [disjoint_filter]
    intro i _ h1 h2
    exact h.ne i (h1.trans h2.symm)
  have hσ : (univ.filter fun i => X (σ i) = w).card = (univ.filter fun i => X i = w).card := by
    apply card_bij (fun i _ => σ i)
    · intro i hi; simpa using hi
    · intro i _ j _ hij; exact σ.injective hij
    · intro j hj
      exact ⟨σ.symm j, by simpa using hj, by simp⟩
  unfold incidentLoad
  rw [hfil, card_image_of_injOn (h.inj.injOn), card_union_of_disjoint hdisj, hσ]
  ring

end PartitionedTriangleAbsorption.PrivateTemplate
