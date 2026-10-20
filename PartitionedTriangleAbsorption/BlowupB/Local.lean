/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Cost

/-! # BlowupB.Local — deletions: the reduction under a local hypothesis, with costs

`LocalHyp p F G R W` replaces "complete blowup":
* every edge of `G` is an allowed pair (`G` is contained in the complete blowup);
* every representative is adjacent in `G` to every *good* vertex (a vertex of `W`, or a
  representative) with which it forms an allowed pair.

Edges of `G` between two non-representatives may be missing arbitrarily: this covers every
graph obtained from a complete blowup by deleting edges that avoid the representatives (relative
to `W`). All gadgets of `ZeroDeg`/`Uniform` only use edges at representatives or edges of the
support, so the reduction goes through, now with explicit costs:

* `physCostZ_c4_local` (cost `4`), `physCostZ_piece_local` (cost `8`);
* `physCostZ_of_zeroDeg_local`: a balanced residual `u` costs at most `8 · l1 u`;
* `exists_deg_gadget_local` (cost `2`), `exists_copy_of_type_local`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

/-- **Local blowup hypothesis** (deletions away from the representatives). -/
structure LocalHyp (p : V → Fin t) (F : Finset (Multiset (Fin t))) (G : SimpleGraph V) {q : ℕ}
    (R : Reps p q) (W : V → Prop) : Prop where
  allowed : ∀ u v, G.Adj u v → AllowedPair F (p u) (p v)
  univ : ∀ v r, (W v ∨ v ∈ R.set) → r ∈ R.set → v ≠ r → AllowedPair F (p v) (p r) → G.Adj v r

/-- Good vertices: those of `W` and the representatives. -/
def Good {p : V → Fin t} {q : ℕ} (R : Reps p q) (W : V → Prop) (v : V) : Prop := W v ∨ v ∈ R.set

/-- Every edge in the support of `w` has good endpoints. -/
def OnGood {p : V → Fin t} {q : ℕ} (R : Reps p q) (W : V → Prop) (w : Sym2 V → ℤ) : Prop :=
  ∀ e, w e ≠ 0 → ∀ x ∈ e, Good R W x

section Basic

variable {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V} {W : V → Prop}

omit [Fintype V] in
theorem LocalHyp.of_complete (hG : IsCompleteBlowup p F G) {q : ℕ} (R : Reps p q)
    (W : V → Prop) : LocalHyp p F G R W :=
  ⟨fun _ _ h => allowedPair_of_adj hG h, fun v r _ _ hne hA => (hG v r).mpr ⟨hne, hA⟩⟩

omit [Fintype V] in
theorem good_rep {q : ℕ} (R : Reps p q) (i : Fin t) (a : Fin q) : Good R W (R.rep i a) :=
  Or.inr (R.rep_mem i a)

omit [Fintype V] in
theorem LocalHyp.adj {q : ℕ} {R : Reps p q} (hL : LocalHyp p F G R W) {v r : V}
    (hv : Good R W v) (hr : r ∈ R.set) (hne : v ≠ r) (hA : AllowedPair F (p v) (p r)) :
    G.Adj v r :=
  hL.univ v r hv hr hne hA

omit [Fintype V] in
theorem isCopy_of_adj {a b c : V} (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c)
    (hτ : ({p a, p b, p c} : Multiset (Fin t)) ∈ F) : IsCopy p F G {a, b, c} := by
  have h1 := G.ne_of_adj hab
  have h2 := G.ne_of_adj hac
  have h3 := G.ne_of_adj hbc
  refine ⟨?_, by rw [map_three p h1 h2 h3]; exact hτ⟩
  rw [SimpleGraph.isNClique_iff]
  refine ⟨?_, Finset.card_eq_three.mpr ⟨a, b, c, h1, h2, h3, rfl⟩⟩
  intro x hx y hy hxy
  simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  · exact absurd rfl hxy
  · exact hab
  · exact hac
  · exact hab.symm
  · exact absurd rfl hxy
  · exact hbc
  · exact hac.symm
  · exact hbc.symm
  · exact absurd rfl hxy

variable {q : ℕ} {R : Reps p q}

omit [Fintype V] in
theorem OnGood.zero : OnGood R W (0 : Sym2 V → ℤ) := fun _ h => absurd rfl h

omit [Fintype V] in
theorem OnGood.add {w₁ w₂ : Sym2 V → ℤ} (h₁ : OnGood R W w₁) (h₂ : OnGood R W w₂) :
    OnGood R W (w₁ + w₂) := by
  intro e he
  by_cases h : w₁ e = 0
  · exact h₂ e (by simpa [h] using he)
  · exact h₁ e h

omit [Fintype V] in
theorem OnGood.neg {w : Sym2 V → ℤ} (h : OnGood R W w) : OnGood R W (-w) :=
  fun e he => h e (by simpa using he)

omit [Fintype V] in
theorem OnGood.sub {w₁ w₂ : Sym2 V → ℤ} (h₁ : OnGood R W w₁) (h₂ : OnGood R W w₂) :
    OnGood R W (w₁ - w₂) := by
  rw [sub_eq_add_neg]; exact h₁.add h₂.neg

omit [Fintype V] in
theorem OnGood.smul {w : Sym2 V → ℤ} (h : OnGood R W w) (a : ℤ) : OnGood R W (a • w) :=
  fun e he => h e (by intro h0; apply he; simp [h0])

omit [Fintype V] in
theorem OnGood.sum {ι : Type*} (s : Finset ι) (f : ι → Sym2 V → ℤ)
    (h : ∀ i ∈ s, OnGood R W (f i)) : OnGood R W (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty]; exact OnGood.zero
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

omit [Fintype V] in
theorem onGood_triEdges {s : Finset V} (hs : ∀ x ∈ s, Good R W x) :
    OnGood R W (indZ (triEdges s)) := by
  intro e he x hx
  have hmem : e ∈ triEdges s := by
    by_contra h; exact he (indZ_not_mem h)
  exact hs x ((Finset.mem_sym2_iff.mp (mem_filter.mp hmem).1) x hx)

omit [Fintype V] in
theorem onGood_indZ {E : Finset (Sym2 V)} (hW : ∀ e ∈ E, ∀ x ∈ e, W x) :
    OnGood R W (indZ E) := by
  intro e he x hx
  have hmem : e ∈ E := by
    by_contra h; exact he (indZ_not_mem h)
  exact Or.inl (hW e hmem x hx)

theorem good_of_degVecZ_ne_zero {u : Sym2 V → ℤ} (hu : OnGood R W u) {v : V}
    (h : degVecZ p u v ≠ 0) : Good R W v := by
  obtain ⟨e, he, hve⟩ := exists_of_degVecZ_ne_zero h
  exact hu e he v hve

end Basic

/-! ### Alternating 4-cycles, locally, with cost -/

section Pieces

variable {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V} {W : V → Prop}

omit [Fintype V] in
theorem physCostZ_c4_local {q : ℕ} {R : Reps p q} (hL : LocalHyp p F G R W) (hq : 5 ≤ q)
    {a b c d : V} (hga : Good R W a) (hgb : Good R W b) (hgc : Good R W c) (hgd : Good R W d)
    (hac : p a = p c) (hbd : p b = p d)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a) :
    PhysCostZ p F G (c4 a b c d) 4 := by
  have hA := hL.allowed a b hab
  have hτ := third_spec F (p a) (p b) hA
  set k := third F (p a) (p b) hA with hk
  obtain ⟨_, hAak, hAbk⟩ := allowedPair_of_three hτ
  obtain ⟨m, hm⟩ := R.exists_avoid k {a, b, c, d} (lt_of_le_of_lt card_le_four (by omega))
  simp only [mem_insert, mem_singleton, not_or] at hm
  set s := R.rep k m with hs
  have hps : p s = k := R.cls _ _
  have hsR : s ∈ R.set := R.rep_mem _ _
  have has : a ≠ s := fun h => hm.1 h.symm
  have hbs : b ≠ s := fun h => hm.2.1 h.symm
  have hcs : c ≠ s := fun h => hm.2.2.1 h.symm
  have hds : d ≠ s := fun h => hm.2.2.2 h.symm
  have hAs : G.Adj a s := hL.adj hga hsR has (by rw [hps]; exact hAak)
  have hBs : G.Adj b s := hL.adj hgb hsR hbs (by rw [hps]; exact hAbk)
  have hCs : G.Adj c s := hL.adj hgc hsR hcs (by rw [hps, ← hac]; exact hAak)
  have hDs : G.Adj d s := hL.adj hgd hsR hds (by rw [hps, ← hbd]; exact hAbk)
  have h1 := isCopy_of_adj (p := p) (F := F) hab hAs hBs (by rw [hps]; exact hτ)
  have h2 := isCopy_of_adj (p := p) (F := F) hbc hBs hCs (by rw [hps, ← hac, three_swap12]; exact hτ)
  have h3 := isCopy_of_adj (p := p) (F := F) hcd hCs hDs (by rw [hps, ← hac, ← hbd]; exact hτ)
  have h4 := isCopy_of_adj (p := p) (F := F) hda hDs hAs (by rw [hps, ← hbd, three_swap12]; exact hτ)
  rw [c4_identity (G.ne_of_adj hab) (G.ne_of_adj hbc) (G.ne_of_adj hcd) (G.ne_of_adj hda)
    has hbs hcs hds]
  exact ((((physCostZ_of_isCopy h1).sub (physCostZ_of_isCopy h2)).add
    (physCostZ_of_isCopy h3)).sub (physCostZ_of_isCopy h4)).mono (by norm_num)

theorem physCostZ_mono_free_local {q : ℕ} {R : Reps p q} (hL : LocalHyp p F G R W)
    (hq : 5 ≤ q) (o : Fin t → V) {i : Fin t} {x y O1 O2 : V} (hpx : p x = i) (hpy : p y = i)
    (hpO : p (o i) = i) (hp1 : p O1 = i) (hp2 : p O2 = i) (hgx : Good R W x)
    (hgy : Good R W y) (hoR : o i ∈ R.set) (h1R : O1 ∈ R.set) (h2R : O2 ∈ R.set)
    (hadj : G.Adj x y) (hxO : x ≠ o i) (hyO : y ≠ o i) (h1O : O1 ≠ o i) (h2O : O2 ≠ o i)
    (h12 : O1 ≠ O2) :
    PhysCostZ p F G (qg p o s(x, y) - qg p o s(O1, O2)) 8 := by
  have hxy : x ≠ y := G.ne_of_adj hadj
  have hAi : AllowedPair F i i := by
    have := hL.allowed x y hadj; rwa [hpx, hpy] at this
  have adjR : ∀ {v r : V}, Good R W v → r ∈ R.set → p v = i → p r = i → v ≠ r → G.Adj v r :=
    fun hv hr hpv hpr hne => hL.adj hv hr hne (by rw [hpv, hpr]; exact hAi)
  have gO : Good R W (o i) := Or.inr hoR
  have g1 : Good R W O1 := Or.inr h1R
  have g2 : Good R W O2 := Or.inr h2R
  have C : ∀ {a b c d : V}, p a = i → p c = i → p b = i → p d = i → Good R W a → Good R W b →
      Good R W c → Good R W d → G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      PhysCostZ p F G (c4 a b c d) 4 :=
    fun ha hc hb hd ga gb gc gd hab hbc hcd hda =>
      physCostZ_c4_local hL hq ga gb gc gd (ha.trans hc.symm) (hb.trans hd.symm) hab hbc hcd hda
  have hexp : qg p o s(x, y) - qg p o s(O1, O2) =
      ind1 s(x, y) - (ind1 s(x, o i) + ind1 s(y, o i)) + ind1 s(o i, o i) -
        (ind1 s(O1, O2) - (ind1 s(O1, o i) + ind1 s(O2, o i)) + ind1 s(o i, o i)) := by
    rw [qg_mk, qg_mk, hpx, hpy, hp1, hp2]
  rw [hexp]
  by_cases hx1 : x = O1
  · rw [hx1]
    have hy1 : y ≠ O1 := fun h => hxy (hx1.trans h.symm)
    by_cases hy2 : y = O2
    · rw [hy2, sub_self]; exact (PhysCostZ.zero p F G).mono (by norm_num)
    · have key : ind1 s(O1, y) - (ind1 s(O1, o i) + ind1 s(y, o i)) + ind1 s(o i, o i) -
          (ind1 s(O1, O2) - (ind1 s(O1, o i) + ind1 s(O2, o i)) + ind1 s(o i, o i)) =
          c4 O1 y (o i) O2 := by
        unfold c4; rw [ind1_swap (o i) O2, ind1_swap O2 O1]; abel
      rw [key]
      exact (C hp1 hpO hpy hp2 g1 hgy gO g2 (adjR hgy h1R hpy hp1 hy1).symm
        (adjR hgy hoR hpy hpO hyO) (adjR g2 hoR hp2 hpO h2O).symm
        (adjR g2 h1R hp2 hp1 (Ne.symm h12))).mono (by norm_num)
  · by_cases hx2 : x = O2
    · rw [hx2]
      have hy2 : y ≠ O2 := fun h => hxy (hx2.trans h.symm)
      by_cases hy1 : y = O1
      · rw [hy1]
        have key : ind1 s(O2, O1) - (ind1 s(O2, o i) + ind1 s(O1, o i)) + ind1 s(o i, o i) -
            (ind1 s(O1, O2) - (ind1 s(O1, o i) + ind1 s(O2, o i)) + ind1 s(o i, o i)) = 0 := by
          rw [ind1_swap O2 O1]; abel
        rw [key]; exact (PhysCostZ.zero p F G).mono (by norm_num)
      · have key : ind1 s(O2, y) - (ind1 s(O2, o i) + ind1 s(y, o i)) + ind1 s(o i, o i) -
            (ind1 s(O1, O2) - (ind1 s(O1, o i) + ind1 s(O2, o i)) + ind1 s(o i, o i)) =
            c4 O2 y (o i) O1 := by
          unfold c4; rw [ind1_swap (o i) O1]; abel
        rw [key]
        exact (C hp2 hpO hpy hp1 g2 hgy gO g1 (adjR hgy h2R hpy hp2 hy2).symm
          (adjR hgy hoR hpy hpO hyO) (adjR g1 hoR hp1 hpO h1O).symm
          (adjR g1 h2R hp1 hp2 h12)).mono (by norm_num)
    · by_cases hy1 : y = O1
      · rw [hy1]
        have key : ind1 s(x, O1) - (ind1 s(x, o i) + ind1 s(O1, o i)) + ind1 s(o i, o i) -
            (ind1 s(O1, O2) - (ind1 s(O1, o i) + ind1 s(O2, o i)) + ind1 s(o i, o i)) =
            c4 O1 x (o i) O2 := by
          unfold c4; rw [ind1_swap O1 x, ind1_swap (o i) O2, ind1_swap O2 O1]; abel
        rw [key]
        exact (C hp1 hpO hpx hp2 g1 hgx gO g2 (adjR hgx h1R hpx hp1 hx1).symm
          (adjR hgx hoR hpx hpO hxO) (adjR g2 hoR hp2 hpO h2O).symm
          (adjR g2 h1R hp2 hp1 (Ne.symm h12))).mono (by norm_num)
      · by_cases hy2 : y = O2
        · rw [hy2]
          have key : ind1 s(x, O2) - (ind1 s(x, o i) + ind1 s(O2, o i)) + ind1 s(o i, o i) -
              (ind1 s(O1, O2) - (ind1 s(O1, o i) + ind1 s(O2, o i)) + ind1 s(o i, o i)) =
              c4 O2 x (o i) O1 := by
            unfold c4; rw [ind1_swap O2 x, ind1_swap (o i) O1]; abel
          rw [key]
          exact (C hp2 hpO hpx hp1 g2 hgx gO g1 (adjR hgx h2R hpx hp2 hx2).symm
            (adjR hgx hoR hpx hpO hxO) (adjR g1 hoR hp1 hpO h1O).symm
            (adjR g1 h2R hp1 hp2 h12)).mono (by norm_num)
        · have key : ind1 s(x, y) - (ind1 s(x, o i) + ind1 s(y, o i)) + ind1 s(o i, o i) -
              (ind1 s(O1, O2) - (ind1 s(O1, o i) + ind1 s(O2, o i)) + ind1 s(o i, o i)) =
              c4 x y (o i) O1 + c4 x O1 O2 (o i) := by
            unfold c4; rw [ind1_swap (o i) O1, ind1_swap O1 x, ind1_swap (o i) x]; abel
          rw [key]
          exact ((C hpx hpO hpy hp1 hgx hgy gO g1 hadj (adjR hgy hoR hpy hpO hyO)
            (adjR g1 hoR hp1 hpO h1O).symm (adjR hgx h1R hpx hp1 hx1).symm).add
            (C hpx hp2 hp1 hpO hgx g1 g2 gO (adjR hgx h1R hpx hp1 hx1)
              (adjR g1 h2R hp1 hp2 h12) (adjR g2 hoR hp2 hpO h2O)
              (adjR hgx hoR hpx hpO hxO).symm)).mono (by norm_num)

/-- The piece of an edge of the support, locally, at cost `8`. -/
theorem physCostZ_piece_local {R : Reps p 5} (hL : LocalHyp p F G R W) {x y : V}
    (hadj : G.Adj x y) (hgx : Good R W x) (hgy : Good R W y) :
    PhysCostZ p F G (qg p (fun i => R.rep i 0) s(x, y) -
      ∑ i, lam p (fun i => R.rep i 0) i s(x, y) •
        qg p (fun i => R.rep i 0) s(R.rep i 1, R.rep i 2)) 8 := by
  set o : Fin t → V := fun i => R.rep i 0 with ho
  have hpo : ∀ i, p (o i) = i := fun i => R.cls i 0
  have hoR : ∀ i, o i ∈ R.set := fun i => R.rep_mem i 0
  have hoinj : ∀ i j, o i = o j → i = j := fun i j h => (R.inj i 0 j 0 h).1
  have hxy : x ≠ y := G.ne_of_adj hadj
  have hA : AllowedPair F (p x) (p y) := hL.allowed x y hadj
  have hlam_other : ∀ i, i ≠ p x → lam p o i s(x, y) = 0 := by
    intro i hi
    have h1 : ¬ p x = i := fun h => hi h.symm
    have h2 : x ≠ o i := fun h => h1 (by rw [h, hpo])
    simp [lam, mcls, degContrib, h1, h2]
  rw [Finset.sum_eq_single (p x) (fun i _ hi => by rw [hlam_other i hi, zero_smul])
    (fun h => absurd (mem_univ _) h)]
  by_cases hc : p x = p y
  · obtain ⟨i, hpx⟩ : ∃ i, p x = i := ⟨_, rfl⟩
    have hpy : p y = i := hc.symm.trans hpx
    rw [hpx]
    by_cases hxo : x = o i
    · have hyo : y ≠ o i := fun h => hxy (hxo.trans h.symm)
      have hl : lam p o i s(x, y) = 0 := by
        simp [lam, mcls, degContrib, hpy, hxo, hpo, hyo]
      rw [qg_eq_zero_left o (by rw [hpx]; exact hxo.symm), hl, zero_smul, sub_zero]
      exact (PhysCostZ.zero p F G).mono (by norm_num)
    · by_cases hyo : y = o i
      · have hl : lam p o i s(x, y) = 0 := by
          simp [lam, mcls, degContrib, hpx, hyo, hpo, hxo]
        rw [qg_eq_zero_right o (by rw [hpy]; exact hyo.symm), hl, zero_smul, sub_zero]
        exact (PhysCostZ.zero p F G).mono (by norm_num)
      · have hl : lam p o i s(x, y) = 1 := by
          simp [lam, mcls, degContrib, hpx, hpy, hxo, hyo]
        rw [hl, one_smul]
        have h1O : R.rep i 1 ≠ o i := fun h => absurd (R.inj _ _ _ _ h).2 (by decide)
        have h2O : R.rep i 2 ≠ o i := fun h => absurd (R.inj _ _ _ _ h).2 (by decide)
        have h12 : R.rep i 1 ≠ R.rep i 2 := fun h => absurd (R.inj _ _ _ _ h).2 (by decide)
        exact physCostZ_mono_free_local hL le_rfl o hpx hpy (hpo i) (R.cls i 1) (R.cls i 2)
          hgx hgy (hoR i) (R.rep_mem _ _) (R.rep_mem _ _) hadj hxo hyo h1O h2O h12
  · have hy' : y ≠ o (p x) := fun h => hc (by rw [h, hpo])
    have hx' : x ≠ o (p y) := fun h => hc (by rw [h, hpo])
    have hl : lam p o (p x) s(x, y) = 0 := by
      simp [lam, mcls, degContrib, Ne.symm hc, hy']
    rw [hl, zero_smul, sub_zero]
    by_cases hxo : o (p x) = x
    · rw [qg_eq_zero_left o hxo]; exact (PhysCostZ.zero p F G).mono (by norm_num)
    · by_cases hyo : o (p y) = y
      · rw [qg_eq_zero_right o hyo]; exact (PhysCostZ.zero p F G).mono (by norm_num)
      · rw [qg_cross]
        have hgo : ∀ i, Good R W (o i) := fun i => Or.inr (hoR i)
        have a2 : G.Adj y (o (p x)) :=
          hL.adj hgy (hoR _) hy' (by rw [hpo]; exact hA.symm)
        have a3 : G.Adj (o (p x)) (o (p y)) :=
          hL.adj (hgo _) (hoR _) (fun h => hc (hoinj _ _ h)) (by rw [hpo, hpo]; exact hA)
        have a4 : G.Adj (o (p y)) x :=
          (hL.adj hgx (hoR _) hx' (by rw [hpo]; exact hA)).symm
        exact (physCostZ_c4_local hL le_rfl hgx hgy (hgo _) (hgo _) (hpo _).symm (hpo _).symm
          hadj a2 a3 a4).mono (by norm_num)

/-- **Balanced residuals, locally, with cost.** -/
theorem physCostZ_of_zeroDeg_local {R : Reps p 5} (hL : LocalHyp p F G R W)
    {u : Sym2 V → ℤ} (hsupp : OnG G u) (hgood : OnGood R W u) (hE : edgeVecZ p u = 0)
    (hD : ∀ v, degVecZ p u v = 0) : PhysCostZ p F G u (8 * l1 u) := by
  set o : Fin t → V := fun i => R.rep i 0 with ho
  have hdecomp : u = ∑ e, u e •
      (qg p o e - ∑ i, lam p o i e • qg p o s(R.rep i 1, R.rep i 2)) := by
    have h1 : ∑ e, u e • ∑ i, lam p o i e • qg p o s(R.rep i 1, R.rep i 2) = 0 := by
      simp_rw [smul_sum, smul_smul]
      rw [sum_comm]
      refine sum_eq_zero fun i _ => ?_
      rw [← sum_smul, sum_mul_lam_eq_zero o hE hD i, zero_smul]
    simp only [smul_sub, sum_sub_distrib]
    rw [h1, sub_zero, sum_smul_qg o hE hD]
  have key : PhysCostZ p F G (∑ e, u e •
      (qg p o e - ∑ i, lam p o i e • qg p o s(R.rep i 1, R.rep i 2))) (8 * l1 u) := by
    refine (PhysCostZ.sum univ _ (fun e => |u e| * 8) fun e _ => ?_).mono
      (le_of_eq (by rw [l1, mul_sum]; exact sum_congr rfl fun e _ => mul_comm _ _))
    by_cases hue : u e = 0
    · rw [hue, zero_smul]; exact (PhysCostZ.zero p F G).mono (by simp)
    · refine PhysCostZ.smul ?_ _
      have he := hsupp e hue
      have hg := hgood e hue
      induction e using Sym2.ind with
      | _ x y =>
        exact physCostZ_piece_local hL ((G.mem_edgeSet).mp he) (hg x (Sym2.mem_mk_left x y))
          (hg y (Sym2.mem_mk_right x y))
  exact key.congr hdecomp.symm

/-! ### Copies of the types and difference gadgets, locally -/

omit [Fintype V] in
theorem exists_copy_of_type_local {R : Reps p 5} (hL : LocalHyp p F G R W)
    {τ : Multiset (Fin t)} (hτ : τ ∈ F) (hc : Multiset.card τ = 3) :
    ∃ T : Finset V, IsCopy p F G T ∧ triType p T = τ ∧ ∀ x ∈ T, Good R W x := by
  obtain ⟨a, b, c, rfl⟩ := Multiset.card_eq_three.mp hc
  have h01 : R.rep a 0 ≠ R.rep b 1 := fun h => absurd (R.inj _ _ _ _ h).2 (by decide)
  have h02 : R.rep a 0 ≠ R.rep c 2 := fun h => absurd (R.inj _ _ _ _ h).2 (by decide)
  have h12 : R.rep b 1 ≠ R.rep c 2 := fun h => absurd (R.inj _ _ _ _ h).2 (by decide)
  obtain ⟨Aab, Aac, Abc⟩ := allowedPair_of_three hτ
  have e1 : G.Adj (R.rep a 0) (R.rep b 1) :=
    hL.adj (good_rep R a 0) (R.rep_mem _ _) h01 (by rw [R.cls, R.cls]; exact Aab)
  have e2 : G.Adj (R.rep a 0) (R.rep c 2) :=
    hL.adj (good_rep R a 0) (R.rep_mem _ _) h02 (by rw [R.cls, R.cls]; exact Aac)
  have e3 : G.Adj (R.rep b 1) (R.rep c 2) :=
    hL.adj (good_rep R b 1) (R.rep_mem _ _) h12 (by rw [R.cls, R.cls]; exact Abc)
  refine ⟨{R.rep a 0, R.rep b 1, R.rep c 2}, isCopy_of_adj (p := p) (F := F) e1 e2 e3 ?_, ?_, ?_⟩
  · rw [R.cls, R.cls, R.cls]; exact hτ
  · rw [triType, map_three p h01 h02 h12, R.cls, R.cls, R.cls]
  · intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> exact good_rep R _ _

theorem exists_deg_gadget_local {R : Reps p 5} (hL : LocalHyp p F G R W)
    (hF3 : ∀ τ ∈ F, Multiset.card τ = 3) {v : V} (hv : v ≠ R.rep (p v) 0) (hgv : Good R W v)
    {τ : Multiset (Fin t)} (hτ : τ ∈ F) (hi : p v ∈ τ) :
    ∃ g : Sym2 V → ℤ, PhysCostZ p F G g 2 ∧ OnGood R W g ∧ edgeVecZ p g = 0 ∧ ∀ w,
      degVecZ p g w = (if w = v then typeDegVec τ (p v) else 0) -
        (if w = R.rep (p v) 0 then typeDegVec τ (p v) else 0) := by
  obtain ⟨τ', hτ'⟩ := Multiset.exists_cons_of_mem hi
  have hc' : Multiset.card τ' = 2 := by
    have := hF3 τ hτ
    rw [hτ', Multiset.card_cons] at this
    omega
  obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp hc'
  subst hτ'
  set v0 := R.rep (p v) 0 with hv0
  obtain ⟨ma, hma⟩ := R.exists_avoid a {v, v0} (lt_of_le_of_lt card_le_two (by norm_num))
  obtain ⟨mb, hmb⟩ := R.exists_avoid b {v, v0, R.rep a ma}
    (lt_of_le_of_lt card_le_three (by norm_num))
  simp only [mem_insert, mem_singleton, not_or] at hma hmb
  set x := R.rep a ma with hx
  set y := R.rep b mb with hy
  have hpx : p x = a := R.cls _ _
  have hpy : p y = b := R.cls _ _
  have hpv0 : p v0 = p v := R.cls _ _
  have hvx : v ≠ x := fun h => hma.1 h.symm
  have hvy : v ≠ y := fun h => hmb.1 h.symm
  have hxy : x ≠ y := fun h => hmb.2.2 h.symm
  have h0x : v0 ≠ x := fun h => hma.2 h.symm
  have h0y : v0 ≠ y := fun h => hmb.2.1 h.symm
  have hτ3 : ({p v, p x, p y} : Multiset (Fin t)) ∈ F := by rw [hpx, hpy]; exact hτ
  obtain ⟨Avx, Avy, Axy⟩ := allowedPair_of_three hτ3
  have gx : Good R W x := good_rep R _ _
  have gy : Good R W y := good_rep R _ _
  have g0 : Good R W v0 := good_rep R _ _
  have evx : G.Adj v x := hL.adj hgv (R.rep_mem _ _) hvx Avx
  have evy : G.Adj v y := hL.adj hgv (R.rep_mem _ _) hvy Avy
  have exy : G.Adj x y := hL.adj gx (R.rep_mem _ _) hxy Axy
  have e0x : G.Adj v0 x := hL.adj g0 (R.rep_mem _ _) h0x (by rw [hpv0]; exact Avx)
  have e0y : G.Adj v0 y := hL.adj g0 (R.rep_mem _ _) h0y (by rw [hpv0]; exact Avy)
  have hT1 := isCopy_of_adj (p := p) (F := F) evx evy exy hτ3
  have hT2 := isCopy_of_adj (p := p) (F := F) e0x e0y exy (by rw [hpv0]; exact hτ3)
  have htt1 : triType p {v, x, y} = p v ::ₘ {a, b} := by
    rw [triType, map_three p hvx hvy hxy, hpx, hpy]; rfl
  have htt2 : triType p {v0, x, y} = p v ::ₘ {a, b} := by
    rw [triType, map_three p h0x h0y hxy, hpv0, hpx, hpy]; rfl
  have hgood3 : ∀ {z₁ z₂ z₃ : V}, Good R W z₁ → Good R W z₂ → Good R W z₃ →
      ∀ z ∈ ({z₁, z₂, z₃} : Finset V), Good R W z := by
    intro z₁ z₂ z₃ h₁ h₂ h₃ z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact h₁
    · exact h₂
    · exact h₃
  refine ⟨indZ (triEdges {v, x, y}) - indZ (triEdges {v0, x, y}),
    ((physCostZ_of_isCopy hT1).sub (physCostZ_of_isCopy hT2)).mono (by norm_num),
    (onGood_triEdges (hgood3 hgv gx gy)).sub (onGood_triEdges (hgood3 g0 gx gy)), ?_,
    fun w => ?_⟩
  · rw [edgeVecZ_sub, edgeVecZ_indZ, edgeVecZ_indZ, edgeVec_triEdges p hT1.1.card_eq,
      edgeVec_triEdges p hT2.1.card_eq, htt1, htt2, sub_self]
  · rw [degVecZ_sub, degVecZ_indZ, degVecZ_indZ, degVec_triEdges p hT1.1.card_eq,
      degVec_triEdges p hT2.1.card_eq, htt1, htt2]
    by_cases hwv : w = v
    · rw [hwv]
      simp [hvx, hvy, hv]
    · by_cases hw0 : w = v0
      · rw [hw0]
        have h0v : v0 ≠ v := fun h => hv h.symm
        simp [h0x, h0y, h0v, hpv0]
      · by_cases hwx : w = x
        · rw [hwx]
          simp [Ne.symm hvx, Ne.symm h0x]
        · by_cases hwy : w = y
          · rw [hwy]
            simp [Ne.symm hvy, Ne.symm h0y]
          · simp [hwv, hw0, hwx, hwy]

end Pieces

end PartitionedTriangleAbsorption.BlowupB
