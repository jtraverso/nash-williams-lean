/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.CloseExtremal
public import RequestProject.NW18.Stab4

@[expose] public section

/-!
# Certificates of closeness to the extremal graphs

A map `f : V → Fin 4` together with a symmetric pattern `P` on the four classes describes a
graph on `V`.  If `G` differs from it in few adjacencies (counted vertex by vertex) and the four
classes have about `n/4` vertices each, then `G` is close (in the sense of `IsClose`) to the
pattern graph on `Fin n` with the standard four-class layout.
-/

namespace NashWilliams18

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The neighbourhood of `x` prescribed by the pattern `P` and the class map `f`. -/
def patNb (P : Fin 4 → Fin 4 → Bool) (f : V → Fin 4) (x : V) : Finset V :=
  univ.filter (fun y => y ≠ x ∧ P (f x) (f y) = true)

/-- The number of adjacencies (counted from both ends) in which `G` differs from the pattern. -/
def patCost (G : SimpleGraph V) [DecidableRel G.Adj] (P : Fin 4 → Fin 4 → Bool) (f : V → Fin 4) :
    ℕ :=
  ∑ x, (symmDiff (univ.filter (G.Adj x)) (patNb P f x)).card

/-- The size of the class `i`. -/
def fib (f : V → Fin 4) (i : Fin 4) : ℕ := (univ.filter (fun x => f x = i)).card

/-- Total imbalance with respect to the standard layout. -/
def imbal (f : V → Fin 4) : ℕ :=
  ∑ i, Int.natAbs ((fib f i : ℤ) - (classOf (Fintype.card V) i).card)

omit [DecidableEq V] in
lemma sum_fib (f : V → Fin 4) : ∑ i, fib f i = Fintype.card V := by
  unfold fib
  rw [← card_univ, card_eq_sum_card_fiberwise (f := f) (t := univ) (fun x _ => by simp)]

lemma sum_classOf (n : ℕ) : ∑ i, (classOf n i).card = n := by
  have := sum_fib (quarter n)
  simpa [fib, classOf] using this

/-- Moving a single vertex changes the cost by at most `2n`. -/
lemma patCost_update_le (G : SimpleGraph V) [DecidableRel G.Adj] (P : Fin 4 → Fin 4 → Bool)
    (f : V → Fin 4) (v : V) (j : Fin 4) :
    patCost G P (Function.update f v j) ≤ patCost G P f + 2 * Fintype.card V := by
  unfold patCost
  rw [← sum_erase_add _ _ (mem_univ v), ← sum_erase_add _ _ (mem_univ v)]
  have h1 : ∀ x ∈ univ.erase v,
      (symmDiff (univ.filter (G.Adj x)) (patNb P (Function.update f v j) x)).card ≤
        (symmDiff (univ.filter (G.Adj x)) (patNb P f x)).card + 1 := by
    intro x hx
    have hxv : x ≠ v := ne_of_mem_erase hx
    have hsub : symmDiff (patNb P f x) (patNb P (Function.update f v j) x) ⊆ {v} := by
      intro y hy
      rw [mem_singleton]
      by_contra hyv
      rw [mem_symmDiff] at hy
      simp only [patNb, mem_filter, mem_univ, true_and, Function.update_of_ne hxv,
        Function.update_of_ne hyv] at hy
      tauto
    have := card_symmDiff_triangle (univ.filter (G.Adj x)) (patNb P f x)
      (patNb P (Function.update f v j) x)
    have := (card_le_card hsub).trans (card_singleton v).le
    omega
  have h2 := sum_le_sum h1
  rw [sum_add_distrib, sum_const, card_erase_of_mem (mem_univ v), card_univ] at h2
  have h3 : (symmDiff (univ.filter (G.Adj v)) (patNb P (Function.update f v j) v)).card ≤
      Fintype.card V := card_le_univ _
  simp only [smul_eq_mul, mul_one] at h2
  omega

lemma fib_update_of_ne (f : V → Fin 4) (v : V) (j k : Fin 4) (hk1 : k ≠ f v) (hk2 : k ≠ j) :
    fib (Function.update f v j) k = fib f k := by
  unfold fib; congr 1; ext x
  simp only [mem_filter, mem_univ, true_and]
  by_cases hx : x = v
  · subst hx; simp [Function.update_self]; exact ⟨fun h => absurd h.symm hk2,
      fun h => absurd h.symm hk1⟩
  · rw [Function.update_of_ne hx]

lemma fib_update_old (f : V → Fin 4) (v : V) (j : Fin 4) (hj : j ≠ f v) :
    fib (Function.update f v j) (f v) + 1 = fib f (f v) := by
  unfold fib
  have : univ.filter (fun x => f x = f v) =
      insert v (univ.filter (fun x => Function.update f v j x = f v)) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    by_cases hx : x = v
    · subst hx; simp
    · rw [Function.update_of_ne hx]; simp [hx]
  rw [this, card_insert_of_notMem (by simp [Function.update_self, hj])]

lemma fib_update_new (f : V → Fin 4) (v : V) (j : Fin 4) (hj : j ≠ f v) :
    fib (Function.update f v j) j = fib f j + 1 := by
  unfold fib
  have : univ.filter (fun x => Function.update f v j x = j) =
      insert v (univ.filter (fun x => f x = j)) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    by_cases hx : x = v
    · subst hx; simp
    · rw [Function.update_of_ne hx]; simp [hx]
  rw [this, card_insert_of_notMem (by simp [Ne.symm hj])]

/-- **Rebalancing.**  One can reach the exact class sizes of the standard layout at a cost of
at most `n` per unit of imbalance. -/
lemma rebalance (G : SimpleGraph V) [DecidableRel G.Adj] (P : Fin 4 → Fin 4 → Bool) :
    ∀ k : ℕ, ∀ f : V → Fin 4, imbal f = k →
      ∃ g : V → Fin 4, (∀ i, fib g i = (classOf (Fintype.card V) i).card) ∧
        patCost G P g ≤ patCost G P f + Fintype.card V * k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro f hf
    set q : Fin 4 → ℕ := fun i => (classOf (Fintype.card V) i).card with hq
    by_cases hall : ∀ i, fib f i = q i
    · exact ⟨f, hall, by omega⟩
    push_neg at hall
    have hsum : ∑ i, fib f i = ∑ i, q i := by rw [sum_fib, hq, sum_classOf]
    -- an overfull class and an underfull class
    have hover : ∃ i, q i < fib f i := by
      by_contra h
      push_neg at h
      obtain ⟨i0, hi0⟩ := hall
      have hlt : fib f i0 < q i0 := lt_of_le_of_ne (h i0) hi0
      have := sum_lt_sum (fun i _ => h i) ⟨i0, mem_univ _, hlt⟩
      omega
    have hunder : ∃ j, fib f j < q j := by
      by_contra h
      push_neg at h
      obtain ⟨i0, hi0⟩ := hall
      have hlt : q i0 < fib f i0 := lt_of_le_of_ne (h i0) (Ne.symm hi0)
      have := sum_lt_sum (fun i _ => h i) ⟨i0, mem_univ _, hlt⟩
      omega
    obtain ⟨i, hi⟩ := hover
    obtain ⟨j, hj⟩ := hunder
    have hij : j ≠ i := by rintro rfl; omega
    have hne : (univ.filter (fun x => f x = i)).Nonempty := by
      rw [← card_pos]; unfold fib at hi; omega
    obtain ⟨v, hv⟩ := hne
    have hfv : f v = i := (mem_filter.mp hv).2
    have hjv : j ≠ f v := hfv ▸ hij
    have hold := fib_update_old f v j hjv
    have hnew := fib_update_new f v j hjv
    rw [hfv] at hold
    set f' := Function.update f v j with hf'
    have hother : ∀ k, k ≠ i → k ≠ j → fib f' k = fib f k := fun k hk1 hk2 =>
      fib_update_of_ne f v j k (hfv ▸ hk1) hk2
    -- the imbalance drops by two
    have himb : imbal f' + 2 = imbal f := by
      unfold imbal
      rw [← sum_erase_add _ _ (mem_univ i), ← sum_erase_add _ _ (mem_univ i),
        ← sum_erase_add _ _ (mem_erase.mpr ⟨hij, mem_univ j⟩),
        ← sum_erase_add _ _ (mem_erase.mpr ⟨hij, mem_univ j⟩)]
      have hrest : ∑ x ∈ (univ.erase i).erase j,
          Int.natAbs ((fib f' x : ℤ) - (classOf (Fintype.card V) x).card) =
          ∑ x ∈ (univ.erase i).erase j,
          Int.natAbs ((fib f x : ℤ) - (classOf (Fintype.card V) x).card) := by
        refine sum_congr rfl fun x hx => ?_
        rw [hother x (ne_of_mem_erase (mem_of_mem_erase hx)) (ne_of_mem_erase hx)]
      rw [hrest]
      have h1 : Int.natAbs ((fib f' i : ℤ) - (classOf (Fintype.card V) i).card) + 1 =
          Int.natAbs ((fib f i : ℤ) - (classOf (Fintype.card V) i).card) := by
        have : q i < fib f i := hi
        simp only [hq] at this
        omega
      have h2 : Int.natAbs ((fib f' j : ℤ) - (classOf (Fintype.card V) j).card) + 1 =
          Int.natAbs ((fib f j : ℤ) - (classOf (Fintype.card V) j).card) := by
        have : fib f j < q j := hj
        simp only [hq] at this
        omega
      omega
    obtain ⟨g, hg, hcost⟩ := ih (imbal f') (by omega) f' rfl
    refine ⟨g, hg, ?_⟩
    have := patCost_update_le G P f v j
    rw [← hf'] at this
    have hk : k = imbal f' + 2 := by omega
    rw [hk, Nat.mul_add]
    omega

/-- With exact class sizes, the edit distance to the pattern graph is at most the cost. -/
lemma isClose_of_exact (G : SimpleGraph V) [DecidableRel G.Adj] (P : Fin 4 → Fin 4 → Bool)
    (hP : ∀ a b, P a b = P b a) (g : V → Fin 4)
    (hg : ∀ i, fib g i = (classOf (Fintype.card V) i).card) :
    ∃ e : V ≃ Fin (Fintype.card V), (symmDiff G.edgeFinset
      (SimpleGraph.comap (⇑e) (patternGraph (Fintype.card V) P hP)).edgeFinset).card ≤
        patCost G P g := by
  set n := Fintype.card V
  have hcard : ∀ i, Fintype.card {x // g x = i} = Fintype.card {j : Fin n // quarter n j = i} := by
    intro i
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact hg i
  let ei : ∀ i, {x // g x = i} ≃ {j : Fin n // quarter n j = i} :=
    fun i => Fintype.equivOfCardEq (hcard i)
  let e : V ≃ Fin n := (Equiv.sigmaFiberEquiv g).symm.trans
    ((Equiv.sigmaCongrRight ei).trans (Equiv.sigmaFiberEquiv (quarter n)))
  have he : ∀ x, quarter n (e x) = g x := fun x => (ei (g x) ⟨x, rfl⟩).2
  refine ⟨e, ?_⟩
  -- the symmetric difference is covered by the image of the disagreeing ordered pairs
  have hsub : symmDiff G.edgeFinset
      (SimpleGraph.comap (⇑e) (patternGraph n P hP)).edgeFinset ⊆
      (univ.sigma (fun x => symmDiff (univ.filter (G.Adj x)) (patNb P g x))).image
        (fun p => s(p.1, p.2)) := by
    intro z hz
    induction z using Sym2.ind with
    | _ x y =>
      rw [mem_image]
      refine ⟨⟨x, y⟩, ?_, rfl⟩
      rw [mem_sigma]
      refine ⟨mem_univ _, ?_⟩
      rw [mem_symmDiff] at hz ⊢
      have hpat : s(x, y) ∈
          (SimpleGraph.comap (⇑e) (patternGraph n P hP)).edgeFinset ↔
          x ≠ y ∧ P (g x) (g y) = true := by
        rw [SimpleGraph.mem_edgeFinset]
        change (e x ≠ e y ∧ P (quarter n (e x)) (quarter n (e y)) = true) ↔ _
        rw [he x, he y, e.injective.ne_iff]
      rw [SimpleGraph.mem_edgeFinset, hpat] at hz
      simp only [patNb, mem_filter, mem_univ, true_and]
      rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; exact ⟨h1, fun h => h2 ⟨fun hxy => h.1 hxy.symm, h.2⟩⟩
      · right
        refine ⟨⟨fun hxy => h1.1 hxy.symm, h1.2⟩, h2⟩
  refine (card_le_card hsub).trans (card_image_le.trans ?_)
  rw [card_sigma]
  rfl

/-- **Certificate of closeness.** -/
theorem isClose_of_cert (G : SimpleGraph V) [DecidableRel G.Adj] (P : Fin 4 → Fin 4 → Bool)
    (hP : ∀ a b, P a b = P b a) (f : V → Fin 4) {θ : ℝ}
    (hcost : (patCost G P f : ℝ) ≤ θ * (Fintype.card V : ℝ) ^ 2)
    (hfib : ∀ i, |(fib f i : ℝ) - Fintype.card V / 4| ≤ θ * Fintype.card V)
    (hn : 9 ≤ θ * Fintype.card V) :
    IsClose (6 * θ) G (patternGraph (Fintype.card V) P hP) := by
  set n := Fintype.card V
  obtain ⟨g, hg, hgc⟩ := rebalance G P (imbal f) f rfl
  obtain ⟨e, he⟩ := isClose_of_exact G P hP g hg
  refine ⟨e, ?_⟩
  -- bound on the imbalance
  have hq : ∀ i, |((classOf n i).card : ℝ) - n / 4| ≤ 9 / 4 := by
    intro i
    have hlow : ∀ k, (n : ℝ) ≤ 4 * (classOf n k).card + 3 := fun k => by
      exact_mod_cast card_classOf n k
    have hs : ∑ k, ((classOf n k).card : ℝ) = n := by exact_mod_cast sum_classOf n
    rw [Fin.sum_univ_four] at hs
    rw [abs_le]
    fin_cases i <;> simp <;> constructor <;>
      linarith [hlow 0, hlow 1, hlow 2, hlow 3]
  have himb : (imbal f : ℝ) ≤ 4 * θ * n + 9 := by
    unfold imbal
    push_cast
    have : ∀ i, (((fib f i : ℤ) - (classOf n i).card).natAbs : ℝ) ≤ θ * n + 9 / 4 := by
      intro i
      have h1 : (((fib f i : ℤ) - (classOf n i).card).natAbs : ℝ) =
          |(fib f i : ℝ) - (classOf n i).card| := by
        rw [Nat.cast_natAbs]; push_cast; rfl
      rw [h1]
      have := hfib i
      have := hq i
      calc |(fib f i : ℝ) - (classOf n i).card|
          ≤ |(fib f i : ℝ) - n / 4| + |((classOf n i).card : ℝ) - n / 4| := by
            rw [abs_sub_comm ((classOf n i).card : ℝ)]
            exact abs_sub_le _ _ _
        _ ≤ _ := by linarith
    calc ∑ i, (((fib f i : ℤ) - (classOf n i).card).natAbs : ℝ)
        ≤ ∑ _i : Fin 4, (θ * n + 9 / 4) := sum_le_sum fun i _ => this i
      _ = 4 * θ * n + 9 := by simp; ring
  have h1 : ((symmDiff G.edgeFinset (SimpleGraph.comap (⇑e)
      (patternGraph n P hP)).edgeFinset).card : ℝ) ≤ patCost G P g := by exact_mod_cast he
  have h2 : (patCost G P g : ℝ) ≤ patCost G P f + n * imbal f := by exact_mod_cast hgc
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have h3 : (n : ℝ) * imbal f ≤ n * (4 * θ * n + 9) := mul_le_mul_of_nonneg_left himb hn0
  have h4 : (n : ℝ) * 9 ≤ n * (θ * n) := mul_le_mul_of_nonneg_left hn hn0
  nlinarith

end NashWilliams18
