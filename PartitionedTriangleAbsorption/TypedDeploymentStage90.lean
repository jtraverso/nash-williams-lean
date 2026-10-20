/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.MoveLedgerStage88
public import PartitionedTriangleAbsorption.PhysicalPaddingStage89

/-! # Type-preserving physical deployment

The existing splitting producer forgets the selected carrier label. This
strengthening retains the edge-vector invariant in the actual producer and
its induction. Accepted Stage87 sources are not modified. No claim is made
about arbitrary PhysicalMoves, which need not preserve their type vectors.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedDeploymentStage90

open Finset AntiEdgeSelection TypedTransformer PairMoveSelectionStage85
  PhysicalHingeSupply PhysicalMovesStage86 PairSplitDeploymentStage87

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

omit [Fintype V] in
/-- Replacing a carrier by one of the same label preserves the pair vector. -/
theorem pair_edgeVec (p : V → Fin t) {x z a b : V} (hab : a ≠ b)
    (hpz : p z = p x) :
    edgeVec p ({s(z,a),s(z,b)} : Finset (Sym2 V)) =
      edgeVec p ({s(x,a),s(x,b)} : Finset (Sym2 V)) := by
  have hne (u : V) : s(u,a) ≠ s(u,b) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨_, h⟩ | ⟨h₁, h₂⟩
    · exact hab h
    · exact hab (h₂.trans h₁)
  rw [edgeVec, edgeVec, sum_pair (hne z), sum_pair (hne x)]
  funext i j
  simp [pairVec, hpz]

omit [Fintype V] in
/-- Additivity connects local pair preservation to the complete configuration. -/
theorem edgeVec_replace (p : V → Fin t) {X Q R : Finset (Sym2 V)}
    (hQ : Q ⊆ X) (hXR : Disjoint X R) (hvec : edgeVec p R = edgeVec p Q) :
    edgeVec p ((X \ Q) ∪ R) = edgeVec p X := by
  rw [edgeVec_union p (hXR.mono_left sdiff_subset), hvec]
  exact sum_sdiff hQ

theorem exists_split_move (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (hF : ThreeStepLinks F) (G : SimpleGraph V) [DecidableRel G.Adj] (a d : ℝ)
    (hs : CompatibleSupply p F G a) (B U X : Finset (Sym2 V)) (Z : Finset V)
    (hB : DegBounded B d) (hd : 0 ≤ d)
    (hXU : X ⊆ U) (hXG : X ⊆ G.edgeFinset)
    (hZ : ∀ e ∈ X, ∀ v ∈ e, v ∈ Z)
    (hact : ∀ u v, s(u, v) ∈ X → ∃ k, Link F (p u) (p v) k)
    (hbudget : (Z.card : ℝ) + 1 + 4 * d + 4 * U.card < a)
    (x : V) (hx : 4 ≤ incidentLoad X x) :
    ∃ z : V, ∃ Q R H : Finset (Sym2 V),
      z ∉ Z ∧ x ≠ z ∧ Q ⊆ X ∧ Disjoint (H ∪ R) (B ∪ U) ∧ H ∪ R ⊆ G.edgeFinset ∧
      IsTransformer (p := p) (F := F) H Q R ∧ H.card ≤ 7 ∧ R.card ≤ 2 ∧
      (∀ v, v ≠ x → v ≠ z → incidentLoad ((X \ Q) ∪ R) v = incidentLoad X v) ∧
      incidentLoad ((X \ Q) ∪ R) x + 2 = incidentLoad X x ∧
      incidentLoad ((X \ Q) ∪ R) z = 2 ∧ incidentLoad X z = 0 ∧
      ((X \ Q) ∪ R).card = X.card ∧
      (∀ e ∈ (X \ Q) ∪ R, ∀ v ∈ e, v ∈ insert z Z) ∧
      (∀ u v, s(u, v) ∈ (X \ Q) ∪ R → ∃ k, Link F (p u) (p v) k) ∧
      edgeVec p ((X \ Q) ∪ R) = edgeVec p X := by
  -- two distinct edges of `X` at `x`
  obtain ⟨e₁, he₁, e₂, he₂, hne⟩ := one_lt_card.mp (show 1 < incidentLoad X x by omega)
  obtain ⟨he₁X, hx₁⟩ := mem_filter.mp he₁
  obtain ⟨he₂X, hx₂⟩ := mem_filter.mp he₂
  obtain ⟨a', rfl⟩ := (Sym2.mem_iff_exists.mp hx₁).imp fun _ h => h
  obtain ⟨b', rfl⟩ := (Sym2.mem_iff_exists.mp hx₂).imp fun _ h => h
  have hxa : x ≠ a' := (SimpleGraph.mem_edgeFinset.mp (hXG he₁X)).ne
  have hxb : x ≠ b' := (SimpleGraph.mem_edgeFinset.mp (hXG he₂X)).ne
  have hab : a' ≠ b' := by rintro rfl; exact hne rfl
  have hxZ : x ∈ Z := hZ _ he₁X x (Sym2.mem_mk_left _ _)
  have haZ : a' ∈ Z := hZ _ he₁X a' (Sym2.mem_mk_right _ _)
  have hbZ : b' ∈ Z := hZ _ he₂X b' (Sym2.mem_mk_right _ _)
  obtain ⟨ka, hka⟩ := hact _ _ he₁X
  obtain ⟨kb, hkb⟩ := hact _ _ he₂X
  -- the new carrier `z`
  have hS : ({a', b'} : Finset V).card ≤ 4 := (card_le_two).trans (by norm_num)
  have hcS : Compatible p F {a', b'} (p x) := by
    intro v hv
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact ⟨ka, hka⟩
    · exact ⟨kb, hkb⟩
  obtain ⟨z, hpz, hzadj, hzZ, hzfresh⟩ :=
    exists_fresh_with_history p F G a d hs {a', b'} Z (p x) hS hcS B U hB hd (by linarith)
  have hxz : x ≠ z := fun h => hzZ (h ▸ hxZ)
  have haz : a' ≠ z := fun h => hzZ (h ▸ haZ)
  have hbz : b' ≠ z := fun h => hzZ (h ▸ hbZ)
  -- the gadget on the roots `x, z, a, b`
  let r4 : Fin 4 ↪ V := ⟨![x, z, a', b'], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩
  have hr4 : ∀ i, r4 i = ![x, z, a', b'] i := fun _ => rfl
  have hZ' : ∀ i, r4 i ∈ insert z Z := by
    intro i
    fin_cases i <;> simp [hr4, hxZ, haZ, hbZ]
  have hcard' : ((insert z Z).card : ℝ) ≤ Z.card + 1 := by
    exact_mod_cast card_insert_le z Z
  obtain ⟨f, hfix, -, -, htrans, hcard7, hHG, hHfresh⟩ :=
    exists_physical_gadget p F hF G a d hs r4 (insert z Z) hZ'
      (show p z = p x from hpz) ⟨ka, show Link F (p x) (p a') ka from hka⟩
      ⟨kb, show Link F (p x) (p b') kb from hkb⟩
      B U hB hd (by linarith)
  have f0 : f 0 = x := hfix 0
  have f1 : f 1 = z := hfix 1
  have f2 : f 2 = a' := hfix 2
  have f3 : f 3 = b' := hfix 3
  have hsrc : PairMoveStage85.source.map (edgeEmb f) = {s(x, a'), s(x, b')} := by
    simp [PairMoveStage85.source, edgeEmb, f0, f2, f3]
  have htgt : PairMoveStage85.target.map (edgeEmb f) = {s(z, a'), s(z, b')} := by
    simp [PairMoveStage85.target, edgeEmb, f1, f2, f3]
  rw [hsrc, htgt] at htrans
  set H := PairMoveStage85.gadget.map (edgeEmb f)
  set Q : Finset (Sym2 V) := {s(x, a'), s(x, b')}
  set R : Finset (Sym2 V) := {s(z, a'), s(z, b')}
  have hQX : Q ⊆ X := by
    intro e he
    simp only [Q, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl
    · exact he₁X
    · exact he₂X
  have hRfresh : Disjoint R (B ∪ U) := by
    rw [disjoint_left]
    intro e he hbu
    simp only [R, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl
    · exact hzfresh a' (by simp) (by rw [Sym2.eq_swap]; exact hbu)
    · exact hzfresh b' (by simp) (by rw [Sym2.eq_swap]; exact hbu)
  have hRG : R ⊆ G.edgeFinset := by
    intro e he
    simp only [R, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl
    · exact SimpleGraph.mem_edgeFinset.mpr (hzadj a' (by simp)).symm
    · exact SimpleGraph.mem_edgeFinset.mpr (hzadj b' (by simp)).symm
  have hXR : Disjoint X R := by
    rw [disjoint_left]
    intro e heX heR
    exact disjoint_left.mp hRfresh heR (mem_union.mpr (Or.inr (hXU heX)))
  have hzX : incidentLoad X z = 0 := by
    unfold incidentLoad
    rw [card_eq_zero, filter_eq_empty_iff]
    intro e he hz
    exact hzZ (hZ e he z hz)
  have hload := load_replace hQX hXR
  have hQload := pair_load hxa hxb hab
  have hRload := pair_load (Ne.symm haz) (Ne.symm hbz) hab
  have hQcard : Q.card = 2 := by
    have := hQload x
    simpa [incidentLoad, Q, filter_true_of_mem, Sym2.mem_iff] using this
  have hRcard : R.card = 2 := by
    have := hRload z
    simpa [incidentLoad, R, filter_true_of_mem, Sym2.mem_iff] using this
  refine ⟨z, Q, R, H, hzZ, hxz, hQX, disjoint_union_left.mpr ⟨hHfresh, hRfresh⟩,
    union_subset hHG hRG, htrans, hcard7.le, hRcard.le, ?_, ?_, ?_, hzX, ?_, ?_, ?_, ?_⟩
  · intro v hvx hvz
    have h1 := hload v
    rw [hQload v, hRload v] at h1
    simp only [hvx, hvz, ite_false] at h1
    omega
  · have h1 := hload x
    rw [hQload x, hRload x] at h1
    simp only [hxz, hxa, hxb, ite_true, ite_false] at h1
    omega
  · have h1 := hload z
    rw [hQload z, hRload z, hzX] at h1
    simp only [Ne.symm hxz, Ne.symm haz, Ne.symm hbz, ite_true, ite_false] at h1
    omega
  · rw [card_union_of_disjoint (hXR.mono_left sdiff_subset), card_sdiff_of_subset hQX,
      hQcard, hRcard]
    have : 2 ≤ X.card := by
      have := card_le_card hQX
      omega
    omega
  · intro e he v hv
    rcases mem_union.mp he with he | he
    · exact mem_insert_of_mem (hZ e (mem_sdiff.mp he).1 v hv)
    · simp only [R, mem_insert, mem_singleton] at he
      rcases he with rfl | rfl <;> rcases Sym2.mem_iff.mp hv with rfl | rfl <;>
        simp [haZ, hbZ]
  · intro u v he
    rcases mem_union.mp he with he | he
    · exact hact u v (mem_sdiff.mp he).1
    · simp only [R, mem_insert, mem_singleton] at he
      rcases he with he | he <;> rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨ka, by rw [hpz]; exact hka⟩
      · exact ⟨ka, by rw [hpz]; exact (link_root_swap F _ _ _).mp hka⟩
      · exact ⟨kb, by rw [hpz]; exact hkb⟩
      · exact ⟨kb, by rw [hpz]; exact (link_root_swap F _ _ _).mp hkb⟩
  · exact edgeVec_replace p hQX hXR (by
      dsimp [Q, R]
      exact pair_edgeVec p hab hpz)

theorem deploy_aux (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (hF : ThreeStepLinks F) (G : SimpleGraph V) [DecidableRel G.Adj] (a d : ℝ)
    (hs : CompatibleSupply p F G a) (B : Finset (Sym2 V))
    (hB : DegBounded B d) (hd : 0 ≤ d) :
    ∀ n : ℕ, ∀ (U X : Finset (Sym2 V)) (Z : Finset V), excess X = n →
      X ⊆ U → X ⊆ G.edgeFinset → Disjoint X B →
      (∀ e ∈ X, ∀ v ∈ e, v ∈ Z) →
      (∀ u v, s(u, v) ∈ X → ∃ k, Link F (p u) (p v) k) →
      (∀ v, Even (incidentLoad X v)) →
      (Z.card : ℝ) + 37 * n + 4 * (d + U.card) < a →
      ∃ Y, PhysicalMoves p F G.edgeFinset B U X Y n ∧
        (∀ v, incidentLoad Y v = 0 ∨ incidentLoad Y v = 2) ∧
        Y ⊆ G.edgeFinset ∧ Disjoint Y B ∧ Y.card = X.card ∧ edgeVec p Y = edgeVec p X := by
  intro n
  induction n with
  | zero =>
    intro U X Z hn _ hXG hXB _ _ heven _
    exact ⟨X, .stop U X, degrees_of_excess_zero hn heven, hXG, hXB, rfl, rfl⟩
  | succ n ih =>
    intro U X Z hn hXU hXG hXB hZ hact heven hb
    obtain ⟨x, hx⟩ := exists_high_of_excess (X := X) (by omega)
    obtain ⟨z, Q, R, H, hzZ, hxz, hQX, hfresh, hphys, hmove, hH, hR, hother, hx', hz',
        hz, hcard, hZ', hact', hvecStep⟩ :=
      exists_split_move p F hF G a d hs B U X Z hB hd hXU hXG hZ hact
        (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; push_cast at hb; linarith) x hx
    have hex : excess ((X \ Q) ∪ R) = n := by
      have := excess_step hxz hother hx' hx hz' hz
      omega
    have hRB : Disjoint R B := (hfresh.mono_left subset_union_right).mono_right
      subset_union_left
    have hRU : R ⊆ U ∪ H ∪ R := subset_union_right
    have hZc : ((insert z Z).card : ℝ) ≤ Z.card + 1 := by exact_mod_cast card_insert_le z Z
    have hUc : ((U ∪ H ∪ R).card : ℝ) ≤ U.card + 9 := by
      have h1 := card_union_le (U ∪ H) R
      have h2 := card_union_le U H
      exact_mod_cast (show (U ∪ H ∪ R).card ≤ U.card + 9 by omega)
    obtain ⟨Y, htail, hYdeg, hYG, hYB, hYc, hYvec⟩ := ih (U ∪ H ∪ R) ((X \ Q) ∪ R) (insert z Z) hex
      (union_subset (sdiff_subset.trans (hXU.trans (subset_union_left.trans
        subset_union_left))) hRU)
      (union_subset (sdiff_subset.trans hXG) (subset_union_right.trans hphys))
      (disjoint_union_left.mpr ⟨hXB.mono_left sdiff_subset, hRB⟩) hZ' hact'
      (by
        intro v
        by_cases hvx : v = x
        · subst hvx
          obtain ⟨k, hk⟩ := heven v
          exact ⟨k - 1, by omega⟩
        · by_cases hvz : v = z
          · subst hvz
            rw [hz']
            exact ⟨1, rfl⟩
          · rw [hother v hvx hvz]
            exact heven v)
      (by push_cast at hb; linarith)
    exact ⟨Y, .step hXU hQX hfresh hphys hmove hH hR htail, hYdeg, hYG, hYB,
      hYc.trans hcard, hYvec.trans hvecStep⟩

theorem deploy (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (hF : ThreeStepLinks F) (G : SimpleGraph V) [DecidableRel G.Adj] (a d : ℝ)
    (hs : CompatibleSupply p F G a) (B U X : Finset (Sym2 V)) (Z : Finset V)
    (hB : DegBounded B d) (hd : 0 ≤ d)
    (hXU : X ⊆ U) (hXG : X ⊆ G.edgeFinset) (hXB : Disjoint X B)
    (hZ : ∀ e ∈ X, ∀ v ∈ e, v ∈ Z)
    (hact : ∀ u v, s(u, v) ∈ X → ∃ k, Link F (p u) (p v) k)
    (heven : ∀ v, Even (incidentLoad X v))
    (hbudget : (Z.card : ℝ) + 37 * X.card + 4 * (d + U.card) < a) :
    ∃ Y m, m ≤ X.card ∧ PhysicalMoves p F G.edgeFinset B U X Y m ∧
      (∀ v, incidentLoad Y v = 0 ∨ incidentLoad Y v = 2) ∧
      Y ⊆ G.edgeFinset ∧ Disjoint Y B ∧ Y.card = X.card ∧ edgeVec p Y = edgeVec p X := by
  have hloop : ∀ e ∈ X, ¬ e.IsDiag := fun e he =>
    G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (hXG he))
  have hle := excess_le_card hloop
  obtain ⟨Y, ht, h1, h2, h3, h4, hvec⟩ := deploy_aux p F hF G a d hs B hB hd (excess X) U X Z rfl
    hXU hXG hXB hZ hact heven (by
      have : ((excess X : ℕ) : ℝ) ≤ X.card := by exact_mod_cast hle
      linarith)
  exact ⟨Y, excess X, hle, ht, h1, h2, h3, h4, hvec⟩



/-- The strengthened producer also returns the ledger needed for catalysts.
The edge-vector equality belongs to this actual producer, not to every trace. -/
theorem deploy_for_catalysts {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a d : ℝ) (hF : ThreeStepLinks F) (hs : CompatibleSupply p F G a)
    (B U X : Finset (Sym2 V)) (Z : Finset V)
    (hB : DegBounded B d) (hd : 0 ≤ d)
    (hXU : X ⊆ U) (hXG : X ⊆ G.edgeFinset) (hXB : Disjoint X B)
    (hZ : ∀ e ∈ X, ∀ v ∈ e, v ∈ Z)
    (hact : ∀ u v, s(u, v) ∈ X → ∃ k, Link F (p u) (p v) k)
    (heven : ∀ v, Even (incidentLoad X v))
    (hb : (Z.card : ℝ) + 37 * X.card + 4 * (d + U.card) < a) :
    ∃ Y L m, m ≤ X.card ∧ PhysicalMoves p F G.edgeFinset B U X Y m ∧
      (∀ v, incidentLoad Y v = 0 ∨ incidentLoad Y v = 2) ∧
      Y ⊆ G.edgeFinset ∧ Disjoint Y B ∧ Y.card = X.card ∧ edgeVec p Y = edgeVec p X ∧
      U ⊆ L ∧ Y ⊆ L ∧ L.card ≤ U.card + 9 * X.card ∧
      (∀ D : Finset (Sym2 V), Disjoint D L →
        PhysicalMoves p F G.edgeFinset B (U ∪ D) (X ∪ D) (Y ∪ D) m) := by
  obtain ⟨Y,m,hm,ht,hdeg,hYG,hYB,hYcard,hYvec⟩ :=
    deploy p F hF G a d hs B U X Z hB hd hXU hXG hXB hZ hact heven hb
  obtain ⟨L,hUL,hYL,hc,hpad⟩ := MoveLedgerStage88.trace_with_final_ledger ht hXU hm
  exact ⟨Y,L,m,hm,ht,hdeg,hYG,hYB,hYcard,hYvec,hUL,hYL,hc,hpad⟩

end PartitionedTriangleAbsorption.TypedDeploymentStage90

