/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case126.SpreadPairingF1
import RequestProject.NW18.Case126.ApexSpreadF1

/-!
# Theorem 14.7 for `F₁`, vortex route: one cover-down level in the VORTEX regime (produced)

`F1_spread_level_cover_down` is the `F₁` analogue of the F0 project's `spread_level_cover_down`
(`L3_F0_reference/L3F0/SpreadLevel.lean`; architecture adapted, `F₁` content new):

* the outer leftover `Hout = {x_i y_i}` (both ends outside the child set `U`) is covered by apex
  triangles `x_i y_i z_i`, `z_i ∈ U`, with apex edges taken from the cross graph `Q`
  (`ApexF1.F1_apex_cover_spread`, apex load cap `β`);
* the remaining cross edges at every root `r j ∉ U` are closed by `F₁` link matchings in the
  internal reserve `R ⊆ E(U)` chosen SPREAD (`SpreadF1.F1_spread_root_cover_down`).

The parity of the remaining cross degree at each root is DERIVED (apex triangles remove an even
number of edges at every vertex, `even_deg_of_hasDecomp`), from the parity of the degree of the
root in `Hout ∪ Q`; this is exactly the `F₁` rooted parity `|T_c| + |T_{d₁}| + |T_{d₂}|` even.
The margins are stated on the cross neighbourhoods BEFORE the apex step, with slack `γ`.

**Output.**  `M ⊆ R` with `Δ(M) ≤ L` and an actual `F₁`-decomposition of `Hout ∪ Q ∪ M`.  So after
this step every remaining edge of the level lies inside `U`, and the damage inside `U` is `M`.
If `R` contains no edge inside the next set `U'`, neither does `M`.

**No regime restriction.**  The number of roots `kr` and of leftover edges `k` are only charged
through `k / β < s` and the second-order budget `(e-1) ω L / K + log ∑ |T0 j| ≤ B`; nothing compares
`kr` with `|U|` (contrast with `CrossingCover.crossing_cover_regime`).
-/

namespace NashWilliams18.SpreadF1

open Finset PartitionedTriangleAbsorption LinkPairing CrossingCover SpreadGen ApexF1
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)

variable {V : Type} [DecidableEq V]

/-- A decomposable edge set has even degree at every vertex. -/
theorem even_deg_of_hasDecomp {t : ℕ} {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {E : Finset (Sym2 V)} (h : HasDecomp p F E) (v : V) : Even (deg E v) := by
  classical
  obtain ⟨D, hty, hdisj, rfl⟩ := h
  have hsum : deg (D.biUnion triEdges) v = ∑ s ∈ D, deg (triEdges s) v := by
    unfold deg
    rw [Finset.filter_biUnion, Finset.card_biUnion]
    intro s hs s' hs' hne
    exact Finset.disjoint_filter_filter (hdisj hs hs' hne)
  rw [hsum]
  apply Finset.even_sum
  intro s hs
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp (hty s hs).1
  rw [PartitionedTriangleAbsorption.triEdges_three hab hac hbc]
  unfold deg
  by_cases ha : v = a
  · subst ha
    have : ({s(v, b), s(v, c), s(b, c)} : Finset (Sym2 V)).filter (fun e => v ∈ e) =
        {s(v, b), s(v, c)} := by
      ext e; simp only [mem_filter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨h | h | h, hv⟩
        · exact Or.inl h
        · exact Or.inr h
        · subst h; rcases Sym2.mem_iff.mp hv with h | h
          · exact absurd h hab
          · exact absurd h hac
      · rintro (h | h) <;> subst h <;> simp
    rw [this, card_pair (by simp [hbc, Ne.symm hab])]; exact even_two
  by_cases hb : v = b
  · subst hb
    have : ({s(a, v), s(a, c), s(v, c)} : Finset (Sym2 V)).filter (fun e => v ∈ e) =
        {s(a, v), s(v, c)} := by
      ext e; simp only [mem_filter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨h | h | h, hv⟩
        · exact Or.inl h
        · subst h; rcases Sym2.mem_iff.mp hv with h | h
          · exact absurd h.symm hab
          · exact absurd h hbc
        · exact Or.inr h
      · rintro (h | h) <;> subst h <;> simp
    rw [this, card_pair (by simp [hac, hab])]; exact even_two
  by_cases hc : v = c
  · subst hc
    have : ({s(a, b), s(a, v), s(b, v)} : Finset (Sym2 V)).filter (fun e => v ∈ e) =
        {s(a, v), s(b, v)} := by
      ext e; simp only [mem_filter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨h | h | h, hv⟩
        · subst h; rcases Sym2.mem_iff.mp hv with h | h
          · exact absurd h.symm hac
          · exact absurd h.symm hbc
        · exact Or.inl h
        · exact Or.inr h
      · rintro (h | h) <;> subst h <;> simp
    rw [this, card_pair (by simp [hab, hac])]; exact even_two
  · have : ({s(a, b), s(a, c), s(b, c)} : Finset (Sym2 V)).filter (fun e => v ∈ e) = ∅ := by
      rw [filter_eq_empty_iff]
      intro e he hv
      simp only [mem_insert, mem_singleton] at he
      rcases he with rfl | rfl | rfl <;> rcases Sym2.mem_iff.mp hv with h | h <;> tauto
    rw [this]; exact ⟨0, rfl⟩

/-- The cross neighbourhood of `a` in `U` along the cross graph `Q`. -/
def tgt (U : Finset V) (Q : Finset (Sym2 V)) (a : V) : Finset V := U.filter (fun u => s(a, u) ∈ Q)

/-- `F₁` link margins of a cross neighbourhood with defect `Γ` and slack `γ` for the edges that
the apex step may remove (no parity: the parity is derived). -/
def MarginsSlack (p : V → Fin 4) (c : Fin 4) (T : Finset V) (Γ γ : ℕ) : Prop :=
  4 * Γ + 1 + γ ≤ (T.filter fun y => p y = c).card ∧
  6 * Γ + 1 + γ ≤ (T.filter fun y => p y = partner1 c).card ∧
  6 * Γ + 1 + γ ≤ (T.filter fun y => p y = partner2 c).card ∧
  (T.filter fun y => p y = c).card + 8 * Γ + 1 + 2 * γ ≤
    (T.filter fun y => p y = partner1 c).card + (T.filter fun y => p y = partner2 c).card

/-- A set all of whose vertices have class `c` or a partner class is the disjoint union of its
three class parts. -/
theorem card_three_classes (p : V → Fin 4) (c : Fin 4) (T : Finset V)
    (hT : ∀ y ∈ T, p y = c ∨ p y = partner1 c ∨ p y = partner2 c) :
    (T.filter fun y => p y = c).card + (T.filter fun y => p y = partner1 c).card +
      (T.filter fun y => p y = partner2 c).card = T.card := by
  obtain ⟨h1, h2, h12⟩ := partner_ne c
  have hdis : ∀ a b : Fin 4, a ≠ b →
      Disjoint (T.filter fun y => p y = a) (T.filter fun y => p y = b) := by
    intro a b hab
    rw [disjoint_left]
    intro y hy hy'
    exact hab ((mem_filter.mp hy).2.symm.trans (mem_filter.mp hy').2)
  have hU : (T.filter fun y => p y = c) ∪ (T.filter fun y => p y = partner1 c) ∪
      (T.filter fun y => p y = partner2 c) = T := by
    ext y
    simp only [mem_union, mem_filter]
    constructor
    · rintro ((h | h) | h) <;> exact h.1
    · intro hy
      rcases hT y hy with h | h | h
      · exact Or.inl (Or.inl ⟨hy, h⟩)
      · exact Or.inl (Or.inr ⟨hy, h⟩)
      · exact Or.inr ⟨hy, h⟩
  conv_rhs => rw [← hU]
  rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨hdis _ _ h2, hdis _ _ h12⟩),
    card_union_of_disjoint (hdis _ _ h1)]

theorem deg_union_of_disjoint {A B : Finset (Sym2 V)} (h : Disjoint A B) (v : V) :
    deg (A ∪ B) v = deg A v + deg B v := by
  unfold deg
  rw [filter_union, card_union_of_disjoint (disjoint_filter_filter h)]

/-- **One `F₁` cover-down level in the vortex regime** (produced). -/
theorem F1_spread_level_cover_down (p : V → Fin 4) (U : Finset V) (Q R : Finset (Sym2 V))
    (k : ℕ) (x y : ℕ → V) (kr : ℕ) (r : ℕ → V) (s γ β γ₀ K B ω L : ℕ)
    -- the outer leftover
    (hxy : ∀ i < k, x i ≠ y i)
    (hinj : ∀ i < k, ∀ j < k, s(x i, y i) = s(x j, y j) → i = j)
    (hxU : ∀ i < k, x i ∉ U) (hyU : ∀ i < k, y i ∉ U)
    (hdegH : ∀ v, ((range k).filter (fun i => v = x i ∨ v = y i)).card ≤ γ)
    (hsup : ∀ i < k, s ≤ (U.filter (fun z => s(x i, z) ∈ Q ∧ s(y i, z) ∈ Q ∧
      ({p (x i), p (y i), p z} : Multiset (Fin 4)) ∈ F1)).card)
    (hβ : 0 < β) (hs : 2 * γ + k / β < s)
    -- the cross graph and its roots
    (hQ : ∀ e ∈ Q, ∃ j < kr, ∃ u ∈ U, e = s(r j, u))
    (hr : ∀ i < kr, ∀ j < kr, r i = r j → i = j)
    (hrU : ∀ j < kr, r j ∉ U)
    (hpar : ∀ j < kr, Even (deg ((range k).image (fun i => s(x i, y i)) ∪ Q) (r j)))
    -- the internal reserve and the spread supply (on the pre-apex cross neighbourhoods)
    (hRU : ∀ e ∈ R, ∀ v ∈ e, v ∈ U)
    (hK : 0 < K)
    (hcls : ∀ j < kr, ∀ u ∈ tgt U Q (r j),
      p u = p (r j) ∨ p u = partner1 (p (r j)) ∨ p u = partner2 (p (r j)))
    (hdense : ∀ j < kr, ∀ v ∈ tgt U Q (r j), ∀ c : Fin 4, LinkPair (p (r j)) (p v) c →
      ((tgt U Q (r j)).filter fun z => p z = c ∧ ¬ (z ≠ v ∧ s(v, z) ∈ R)).card ≤ γ₀)
    (hmarg : ∀ j < kr, MarginsSlack p (p (r j)) (tgt U Q (r j)) (γ₀ + (B + K)) γ)
    (hover : ∀ i < kr, ∀ j < kr, i ≠ j → ((tgt U Q (r i)) ∩ (tgt U Q (r j))).card ≤ ω)
    (hload : ∀ v, visits (fun j => tgt U Q (r j)) kr v ≤ L)
    (hB : (Real.exp 1 - 1) * ω * L / K +
      Real.log (∑ j ∈ range kr, ((tgt U Q (r j)).card : ℝ)) ≤ B) :
    ∃ M : Finset (Sym2 V), M ⊆ R ∧ (∀ v, deg M v ≤ L) ∧
      HasDecomp p F1 ((range k).image (fun i => s(x i, y i)) ∪ Q ∪ M) := by
  classical
  set Hout := (range k).image (fun i => s(x i, y i)) with hHout
  obtain ⟨z, hzU, hCQ, hdisHC, -, hdegC, hdecHC⟩ := F1_apex_cover_spread p Q U k x y s γ β hxy
    hinj hxU hyU (fun i _ => hdegH (x i)) (fun i _ => hdegH (y i)) hsup hβ hs
  set C := apexEdges k x y z with hC
  set T0 : ℕ → Finset V := fun j => tgt U Q (r j) with hT0
  set T : ℕ → Finset V := fun j => U.filter (fun u => s(r j, u) ∈ Q \ C) with hT
  have hHnoU : ∀ e ∈ Hout, ∀ v ∈ e, v ∉ U := by
    intro e he v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    exacts [hxU i (Finset.mem_range.mp hi), hyU i (Finset.mem_range.mp hi)]
  have hHQ : Disjoint Hout Q := by
    rw [Finset.disjoint_left]
    intro e he heQ
    obtain ⟨j, -, u, hu, rfl⟩ := hQ e heQ
    exact hHnoU _ he u (Sym2.mem_mk_right _ _) hu
  have hQout : ∀ e ∈ Q, ∃ v ∈ e, v ∉ U := by
    intro e he
    obtain ⟨j, hj, u, -, rfl⟩ := hQ e he
    exact ⟨r j, Sym2.mem_mk_left _ _, hrU j hj⟩
  have hTdeg : ∀ j < kr, (T j).card = deg (Q \ C) (r j) := by
    intro j hj
    unfold deg
    apply Finset.card_nbij (fun u => s(r j, u))
    · intro u hu
      simp only [hT, Finset.coe_filter, Set.mem_setOf_eq] at hu
      simp only [Finset.coe_filter, Set.mem_setOf_eq]
      exact ⟨hu.2, Sym2.mem_mk_left _ _⟩
    · intro a _ b _ hab
      exact Sym2.congr_right.mp hab
    · intro e he
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at he
      obtain ⟨j', hj', u, hu, rfl⟩ := hQ e (Finset.mem_sdiff.mp he.1).1
      rcases Sym2.mem_iff.mp he.2 with h | h
      · have := hr j hj j' hj' h
        subst this
        refine ⟨u, ?_, rfl⟩
        simp only [hT, Finset.coe_filter, Set.mem_setOf_eq]
        exact ⟨hu, he.1⟩
      · exact absurd (h ▸ hu) (hrU j hj)
  have hloss : ∀ j < kr, (T0 j \ T j).card ≤ γ := by
    intro j hj
    have h1 : (T0 j \ T j).card ≤ deg C (r j) := by
      unfold deg
      apply Finset.card_le_card_of_injOn (fun u => s(r j, u))
      · intro u hu
        have hu' := Finset.mem_sdiff.mp (Finset.mem_coe.mp hu)
        simp only [hT0, hT, tgt, Finset.mem_filter, Finset.mem_sdiff] at hu'
        simp only [Finset.coe_filter, Set.mem_setOf_eq]
        refine ⟨?_, Sym2.mem_mk_left _ _⟩
        by_contra hc
        exact hu'.2 ⟨hu'.1.1, hu'.1.2, hc⟩
      · intro a _ b _ hab
        exact Sym2.congr_right.mp hab
    have h2 := hdegC (r j)
    have h3 : ((range k).filter (fun i => z i = r j)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i hi h
      exact hrU j hj (h ▸ hzU i (Finset.mem_range.mp hi))
    have := hdegH (r j)
    omega
  have hTsub : ∀ j, T j ⊆ T0 j := by
    intro j u hu
    simp only [hT, hT0, tgt, Finset.mem_filter, Finset.mem_sdiff] at hu ⊢
    exact ⟨hu.1, hu.2.1⟩
  have hsplitE : Hout ∪ Q = (Hout ∪ C) ∪ (Q \ C) := by
    ext e; simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (h | h)
      · exact Or.inl (Or.inl h)
      · by_cases hc : e ∈ C
        · exact Or.inl (Or.inr hc)
        · exact Or.inr ⟨h, hc⟩
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (hCQ h)
      · exact Or.inr h.1
  have hdisj1 : Disjoint (Hout ∪ C) (Q \ C) := by
    rw [Finset.disjoint_left]
    intro e he he'
    rcases Finset.mem_union.mp he with h | h
    · exact Finset.disjoint_left.mp hHQ h (Finset.mem_sdiff.mp he').1
    · exact (Finset.mem_sdiff.mp he').2 h
  have hev : ∀ j < kr, Even (T j).card := by
    intro j hj
    rw [hTdeg j hj]
    have h1 := hpar j hj
    rw [hsplitE, deg_union_of_disjoint hdisj1] at h1
    have h2 := even_deg_of_hasDecomp hdecHC (r j)
    exact (Nat.even_add.mp h1).mp h2
  have hcov : ∀ j < kr, ∀ (P : V → Prop) [DecidablePred P],
      ((T0 j).filter P).card ≤ ((T j).filter P).card + γ := by
    intro j hj P _
    refine (Finset.card_le_card ?_).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left (hloss j hj) _))
    intro w hw
    simp only [Finset.mem_filter] at hw
    by_cases hwT : w ∈ T j
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hwT, hw.2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hw.1, hwT⟩)
  have hsumT : Real.log (∑ j ∈ range kr, ((T j).card : ℝ)) ≤
      Real.log (∑ j ∈ range kr, ((T0 j).card : ℝ)) := by
    have hle : (∑ j ∈ range kr, ((T j).card : ℝ)) ≤ ∑ j ∈ range kr, ((T0 j).card : ℝ) :=
      Finset.sum_le_sum (fun j _ => by exact_mod_cast Finset.card_le_card (hTsub j))
    rcases (Finset.sum_nonneg (fun j _ => Nat.cast_nonneg (T j).card) :
        (0 : ℝ) ≤ ∑ j ∈ range kr, ((T j).card : ℝ)).eq_or_lt with h0 | hpos
    · rw [← h0, Real.log_zero]
      have hnat : (∑ j ∈ range kr, ((T0 j).card : ℝ)) =
          ((∑ j ∈ range kr, (T0 j).card : ℕ) : ℝ) := by
        push_cast; rfl
      rw [hnat]
      exact Real.log_natCast_nonneg _
    · exact Real.log_le_log hpos hle
  have hclsT : ∀ j < kr, ∀ u ∈ T j,
      p u = p (r j) ∨ p u = partner1 (p (r j)) ∨ p u = partner2 (p (r j)) :=
    fun j hj u hu => hcls j hj u (hTsub j hu)
  obtain ⟨M, hMR, hdegM, -, hdecM⟩ := F1_spread_root_cover_down p R kr r T γ₀ K B ω L hK hr
    (fun i hi j _ hxT => hrU i hi (Finset.mem_filter.mp hxT).1) hclsT
    (fun j hj v hv c hc => (Finset.card_le_card (Finset.filter_subset_filter _ (hTsub j))).trans
      (hdense j hj v (hTsub j hv) c hc))
    (fun j hj => by
      obtain ⟨m1, m2, m3, m4⟩ := hmarg j hj
      have c1 := hcov j hj (fun w => p w = p (r j))
      have c2 := hcov j hj (fun w => p w = partner1 (p (r j)))
      have c3 := hcov j hj (fun w => p w = partner2 (p (r j)))
      have d1 : ((T j).filter fun w => p w = p (r j)).card ≤
          ((T0 j).filter fun w => p w = p (r j)).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ (hTsub j))
      have hpar' := card_three_classes p (p (r j)) (T j) (hclsT j hj)
      have hevj := hev j hj
      simp only [hT0] at c1 c2 c3 d1
      refine ⟨by omega, by omega, by omega, by omega, ?_⟩
      rw [hpar']
      exact Nat.even_iff.mp hevj)
    (fun i hi j hj hij =>
      (Finset.card_le_card (Finset.inter_subset_inter (hTsub i) (hTsub j))).trans
      (hover i hi j hj hij))
    (fun v => le_trans (Finset.card_le_card (fun j hj => by
        have hj' := Finset.mem_filter.mp hj
        exact Finset.mem_filter.mpr ⟨hj'.1, hTsub j hj'.2⟩)) (hload v))
    (by linarith)
  have hstar : rootStar kr r T = Q \ C := by
    ext e
    simp only [rootStar, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨j, -, u, hu, rfl⟩
      exact (Finset.mem_filter.mp hu).2
    · intro he
      obtain ⟨j, hj, u, hu, rfl⟩ := hQ e (Finset.mem_sdiff.mp he).1
      exact ⟨j, hj, u, Finset.mem_filter.mpr ⟨hu, he⟩, rfl⟩
  rw [hstar] at hdecM
  have hMin : ∀ e ∈ M, ∀ v ∈ e, v ∈ U := fun e he => hRU e (hMR he)
  have hdisj2 : Disjoint (Hout ∪ C) ((Q \ C) ∪ M) := by
    rw [Finset.disjoint_union_right]
    refine ⟨hdisj1, ?_⟩
    rw [Finset.disjoint_left]
    intro e he heM
    rcases Finset.mem_union.mp he with h | h
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
      exact hxU i (Finset.mem_range.mp hi) (hMin _ heM _ (Sym2.mem_mk_left _ _))
    · obtain ⟨v, hv, hvU⟩ := hQout e (hCQ h)
      exact hvU (hMin _ heM v hv)
  have hall := hdecHC.union hdecM hdisj2
  have heq : (Hout ∪ C) ∪ ((Q \ C) ∪ M) = Hout ∪ Q ∪ M := by
    rw [← Finset.union_assoc, ← hsplitE]
  exact ⟨M, hMR, hdegM, heq ▸ hall⟩

end NashWilliams18.SpreadF1
