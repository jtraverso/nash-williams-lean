/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case124.BoundedCore.SingleAbsorber
import RequestProject.NW18.HingeCount
import RequestProject.NW18.CloseExtremal
import RequestProject.NW18.Case124.SignedCertificateHosts

/-!
# The finite-core absorber of the bounded-core route (`CoreAbsorberSpec124`, proved)

* `hingeSupply_of_host`: on a 12.4 host (`δ(G) ≥ 3n/4`, not `β`-extremal, `n` large) the
  root-clean eight-vertex `K₃`-hinges of Lemma 14.4 give the explicit hinge supply
  `HingeSupply onePart K3fam G c 8` (with `i = 8`, `c n⁴` hinges for every two triangles
  sharing exactly one edge).  This is the proved `lemma_14_4_configs`, converted from
  non-closeness by `extremal_of_isCloseToExtremal`.
* `codegree_half`: every two vertices have `≥ n/2` common neighbours.
* `library_absorber`: one absorber per divisible `L ⊆ E(G[U])`, built successively, each new
  one avoiding the vertices of the previous ones and the small set `U₁`; their union absorbs
  every such `L`.  Multiplicities of the signed certificates are kept (`absorber_onePart`).
* `coreAbsorberSpec124 : CoreAbsorberSpec124`.  The size of `A` is a constant depending only on
  the core bound `m` (chosen before the host), so `A` has maximum degree `≤ ρ n` for large `n`.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.SignedHinge
  PartitionedTriangleAbsorption.SignedCertificate

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Hinge supply on the 12.4 hosts -/

/-- **Explicit hinge supply on the 12.4 hosts** (from Lemma 14.4's configuration count). -/
theorem hingeSupply_of_host (β : ℝ) (hβ : 0 < β) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], n₀ ≤ Fintype.card V → 3 * Fintype.card V ≤ 4 * G.minDegree →
      ¬ IsExtremal β G → HingeSupply onePart K3fam G c 8 := by
  obtain ⟨α₀, hα₀, hcfg⟩ := lemma_14_4_configs
  set α : ℝ := min α₀ (min (β ^ 2 / 8) (β / 8)) with hα
  have hαpos : 0 < α := lt_min hα₀ (lt_min (by positivity) (by positivity))
  obtain ⟨c, hc, n₁, hn₁⟩ := hcfg α hαpos (min_le_left _ _)
  obtain ⟨n₂, hn₂⟩ := extremal_of_isCloseToExtremal hβ
  refine ⟨c, hc, max n₁ n₂, fun V _ _ G _ hn hδ hnx => ?_⟩
  have hnc : ¬ IsCloseToExtremal α G := fun hcl =>
    hnx (hn₂ V G (le_trans (le_max_right _ _) hn) α
      ((min_le_right _ _).trans (min_le_left _ _)) ((min_le_right _ _).trans (min_le_right _ _))
      hcl)
  intro S S' hS hS' h1
  obtain ⟨u₁, u₂, v₁, v₂, h12, h13, h14, h23, h24, h34, rfl, rfl⟩ :=
    two_triangles_sharing_edge hS.1.2 hS'.1.2 h1
  have adj : ∀ {T : Finset V} {x y : V}, IsCopy onePart K3fam G T → x ∈ T → y ∈ T → x ≠ y →
      G.Adj x y := fun hT hx hy hxy => hT.1.1 (mem_coe.mpr hx) (mem_coe.mpr hy) hxy
  have inj : Function.Injective ![u₁, u₂, v₁, v₂] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | (simp at hij; first | exact absurd hij ‹_› | exact absurd hij.symm ‹_›)
  refine ⟨8, by simp, ?_⟩
  show c * (Fintype.card V : ℝ) ^ 4 ≤ _
  rcases hn₁ V G (le_trans (le_max_left _ _) hn) hδ hnc u₁ u₂ v₁ v₂ inj
      (adj hS (by simp) (by simp) h12)
      (adj hS (by simp) (by simp) h13) (adj hS (by simp) (by simp) h23)
      (adj hS' (by simp) (by simp) h14) (adj hS' (by simp) (by simp) h24) with h | h | h
  · exact h.trans (cfgCount_le_hingeCount model_hinge1 vertSet_mH1 G u₁ u₂ v₁ v₂
      (fun x y hx hy hxy => image_mH1_injective hx hy hxy))
  · exact h.trans (cfgCount_le_hingeCount model_hinge2 vertSet_mH2 G u₁ u₂ v₁ v₂
      (fun x y hx hy hxy => image_mH2_injective hx hy hxy))
  · have := h.trans (cfgCount_le_hingeCount model_hinge2 vertSet_mH2 G u₂ u₁ v₁ v₂
      (fun x y hx hy hxy => image_mH2_injective hx hy hxy))
    rwa [insert_comm u₂ u₁, insert_comm u₂ u₁] at this

/-! ### Codegrees -/

/-- Any two vertices of a graph with `δ(G) ≥ 3n/4` have `≥ n/2` common neighbours. -/
theorem codegree_half (G : SimpleGraph V) [DecidableRel G.Adj]
    (hδ : 3 * Fintype.card V ≤ 4 * G.minDegree) (u v w0 : V) :
    (1 / 2 : ℝ) * Fintype.card V ≤
      (univ.filter fun w => G.Adj u w ∧ G.Adj w v ∧ onePart w = onePart w0).card := by
  classical
  have h1 : (univ.filter fun w => G.Adj u w ∧ G.Adj w v ∧ onePart w = onePart w0) =
      (univ.filter (G.Adj u)) ∩ (univ.filter (G.Adj v)) := by
    ext w; simp [onePart, G.adj_comm v w]
  rw [h1]
  have hu : G.degree u = (univ.filter (G.Adj u)).card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  have hv : G.degree v = (univ.filter (G.Adj v)).card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  have hcu := card_union_add_card_inter (univ.filter (G.Adj u)) (univ.filter (G.Adj v))
  have hle := card_le_univ ((univ.filter (G.Adj u)) ∪ (univ.filter (G.Adj v)))
  have hdu := G.minDegree_le_degree u
  have hdv := G.minDegree_le_degree v
  have key : Fintype.card V ≤ 2 * ((univ.filter (G.Adj u)) ∩ (univ.filter (G.Adj v))).card := by
    omega
  have : (Fintype.card V : ℝ) ≤ 2 * (((univ.filter (G.Adj u)) ∩
      (univ.filter (G.Adj v))).card : ℝ) := by exact_mod_cast key
  linarith

/-! ### The library over all divisible residues of a bounded core -/

/-- **The finite library.**  For a fixed host with codegrees `≥ n/2` and the hinge supply,
a set `U ⊆ U₁` whose divisible residues have certificates of weight `≤ Kc`, and the two budget
conditions: for every family `S` of at most `s` divisible `L ⊆ E(G[U])` there is one
`A ⊆ E(G)`, decomposable, with every edge having an endpoint outside `U₁`, `|A| ≤ |S| a₀`,
and `A ∪ L` decomposable for every `L ∈ S`. -/
theorem library_absorber (c' : ℝ) (Kc a0 s u1 : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcand : ∀ u v w0 : V, u ≠ v → (1 / 2 : ℝ) * Fintype.card V ≤
      (univ.filter fun w => G.Adj u w ∧ G.Adj w v ∧ onePart w = onePart w0).card)
    (hsup : HingeSupply onePart K3fam G c' 8) (U U₁ : Finset V) (hUU : U ⊆ U₁)
    (hU1 : U₁.card ≤ u1)
    (hcert : ∀ L ⊆ insideEdges G U, IsIntDiv onePart K3fam L →
      ∃ (ι : Type) (_ : Fintype ι) (t : ι → Finset V) (c : ι → ℤ),
        (∀ j, IsCopy onePart K3fam G (t j)) ∧
        (∀ e, ind L e = ∑ j, c j * ind (triEdges (t j)) e) ∧ certWeight c ≤ Kc)
    (ha0 : 4 * Kc * (Nat.choose (8 + 1) 2 + 2) ≤ a0)
    (hαM : ((u1 + 2 * (s * a0) + 3 * Kc + 4 * Kc * 8 + 1 : ℕ) : ℝ) <
      1 / 2 * Fintype.card V)
    (hβM : (2 ^ Nat.choose (8 + 1) 2 : ℝ) *
      ((u1 + 2 * (s * a0) + 3 * Kc + 4 * Kc * 8 + 1 : ℕ) : ℝ) < c' * Fintype.card V) :
    ∀ S : Finset (Finset (Sym2 V)), S.card ≤ s →
      (∀ L ∈ S, L ⊆ insideEdges G U ∧ IsIntDiv onePart K3fam L) →
      ∃ A ⊆ G.edgeFinset, HasDecomp onePart K3fam A ∧ (∀ e ∈ A, ∃ v ∈ e, v ∉ U₁) ∧
        A.card ≤ S.card * a0 ∧ ∀ L ∈ S, HasDecomp onePart K3fam (A ∪ L) := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _ _
    exact ⟨∅, empty_subset _, empty_hasDecomp, by simp, by simp, by simp⟩
  | insert L S hLS ih =>
    intro hcard hS
    rw [card_insert_of_notMem hLS] at hcard
    obtain ⟨A, hAG, hAdec, hAout, hAcard, hAS⟩ :=
      ih (by omega) (fun L' hL' => hS L' (mem_insert_of_mem hL'))
    obtain ⟨hLU, hLdiv⟩ := hS L (mem_insert_self L S)
    obtain ⟨ι, _, t, c, hcopy, hid, hK⟩ := hcert L hLU hLdiv
    set Z : Finset V := U₁ ∪ vertSet A with hZ
    have hZcard : Z.card ≤ u1 + 2 * (s * a0) := by
      refine (card_union_le _ _).trans ?_
      have h1 := card_vertSet_le A
      have h2 : S.card * a0 ≤ s * a0 := Nat.mul_le_mul_right _ (by omega)
      omega
    have hPZ : ∀ e ∈ L, ∀ v ∈ e, v ∈ Z := fun e he v hv =>
      mem_union_left _ (hUU (mem_of_mem_insideEdges (hLU he) hv))
    obtain ⟨AL, hALG, hALdis, hALdec, hALLdec, hALout, hALcard⟩ :=
      absorber_onePart (1 / 2) c' 8 Kc (u1 + 2 * (s * a0)) G hcand hsup L t c hcopy hid hK Z
        hPZ hZcard hαM hβM
    -- disjointness facts
    have hdisA : Disjoint A AL := by
      rw [disjoint_left]
      intro e heA heAL
      obtain ⟨v, hv, hvZ⟩ := hALout e heAL
      exact hvZ (mem_union_right _ (mem_vertSet_of_mem heA hv))
    have hinsideU₁ : ∀ {L' : Finset (Sym2 V)}, L' ⊆ insideEdges G U → ∀ e ∈ L', ∀ v ∈ e,
        v ∈ U₁ := fun hL' e he v hv => hUU (mem_of_mem_insideEdges (hL' he) hv)
    have hdisAL' : ∀ {L' : Finset (Sym2 V)}, L' ⊆ insideEdges G U → Disjoint A L' := by
      intro L' hL'
      rw [disjoint_left]
      intro e heA heL
      obtain ⟨v, hv, hvU⟩ := hAout e heA
      exact hvU (hinsideU₁ hL' e heL v hv)
    have hdisALL' : ∀ {L' : Finset (Sym2 V)}, L' ⊆ insideEdges G U → Disjoint AL L' := by
      intro L' hL'
      rw [disjoint_left]
      intro e heA heL
      obtain ⟨v, hv, hvZ⟩ := hALout e heA
      exact hvZ (mem_union_left _ (hinsideU₁ hL' e heL v hv))
    refine ⟨A ∪ AL, union_subset hAG hALG, HasDecomp.union hAdec hALdec hdisA, ?_, ?_, ?_⟩
    · intro e he
      rcases mem_union.mp he with he | he
      · exact hAout e he
      · obtain ⟨v, hv, hvZ⟩ := hALout e he
        exact ⟨v, hv, fun h => hvZ (mem_union_left _ h)⟩
    · rw [card_insert_of_notMem hLS]
      refine (card_union_le _ _).trans ?_
      have : AL.card ≤ a0 := hALcard.trans ha0
      nlinarith
    · intro L' hL'
      rcases mem_insert.mp hL' with rfl | hL'S
      · have hdis2 : Disjoint A (AL ∪ L') := disjoint_union_right.mpr ⟨hdisA, hdisAL' hLU⟩
        have := HasDecomp.union hAdec hALLdec hdis2
        rwa [← union_assoc] at this
      · have hL'U := (hS L' (mem_insert_of_mem hL'S)).1
        have hdis2 : Disjoint (A ∪ L') AL :=
          disjoint_union_left.mpr ⟨hdisA, (hdisALL' hL'U).symm⟩
        have := HasDecomp.union (hAS L' hL'S) hALdec hdis2
        rwa [union_right_comm] at this

/-! ### The finite-core absorber -/

/-- **`CoreAbsorberSpec124` holds.** -/
theorem coreAbsorberSpec124 : CoreAbsorberSpec124 := by
  intro β hβ hβ1
  obtain ⟨c', hc', nh, hsupply⟩ := hingeSupply_of_host β hβ
  set ζ : ℝ := min (1 / 8) (c' / 2 ^ (Nat.choose (8 + 1) 2 + 1)) with hζ
  have hζpos : 0 < ζ := lt_min (by norm_num) (by positivity)
  refine ⟨ζ, hζpos, fun m ρ hρ => ?_⟩
  set q : ℕ := Nat.choose (m + 1) 2 with hq
  set Kc : ℕ := 16741 * q with hKc
  set a0 : ℕ := 4 * Kc * (Nat.choose (8 + 1) 2 + 2) with ha0
  set s : ℕ := 2 ^ q with hs
  set D : ℕ := 2 * (s * a0) + 3 * Kc + 4 * Kc * 8 + 1 with hD
  set P2 : ℝ := (2 : ℝ) ^ Nat.choose (8 + 1) 2 with hP2
  have hP2pos : 0 < P2 := by positivity
  refine ⟨nh + 8 * D + 1 + ⌈4 * P2 * D / c'⌉₊ + ⌈((s * a0 : ℕ) : ℝ) / ρ⌉₊,
    fun V _ _ G _ hn hδ hnx U U₁ hUU₁ hU₁ hUm => ?_⟩
  classical
  set n := Fintype.card V with hn_def
  have hnh : nh ≤ n := by omega
  have hnD : 8 * D + 1 ≤ n := by omega
  have hnR : (n : ℝ) ≥ ⌈4 * P2 * D / c'⌉₊ := by exact_mod_cast (by omega : _ ≤ n)
  have hnρ : (n : ℝ) ≥ ⌈((s * a0 : ℕ) : ℝ) / ρ⌉₊ := by exact_mod_cast (by omega : _ ≤ n)
  have hnpos : 0 < n := by omega
  have hsup := hsupply V G hnh hδ hnx
  have hcand := fun u v w0 (_ : u ≠ v) => codegree_half G hδ u v w0
  -- certificates for every divisible residue of the core
  have hinside_card : ∀ L ⊆ insideEdges G U, L.card ≤ q := by
    intro L hL
    refine (card_le_card (hL.trans inter_subset_right)).trans ?_
    refine (card_le_card (filter_subset _ _)).trans ?_
    rw [Finset.card_sym2]
    exact Nat.choose_le_choose 2 (by omega)
  have hcert : ∀ L ⊆ insideEdges G U, IsIntDiv onePart K3fam L →
      ∃ (ι : Type) (_ : Fintype ι) (t : ι → Finset V) (c : ι → ℤ),
        (∀ j, IsCopy onePart K3fam G (t j)) ∧
        (∀ e, ind L e = ∑ j, c j * ind (triEdges (t j)) e) ∧ certWeight c ≤ Kc := by
    intro L hL hdiv
    have hLG : ∀ f ∈ L, f ∈ G.edgeSet := fun f hf =>
      SimpleGraph.mem_edgeFinset.mp (insideEdges_subset G U (hL hf))
    have hev : OnePart.Even3 L :=
      (OnePart.isIntDiv_part1_iff L fun f hf => G.not_isDiag_of_mem_edgeSet (hLG f hf)).mp hdiv
    obtain ⟨ι, hι, T, c, ⟨hT, hTid⟩, hw⟩ := ParityFill.signed_certificate_edgeSet
      (ParityFill.nonextHyp_of_host G hβ hβ1 hnpos hδ hnx) L hLG hev
    refine ⟨ι, hι, T, c, hT, hTid, ?_⟩
    have hLq := hinside_card L hL
    unfold certWeight
    have : (16741 * (L.card : ℤ)) ≤ Kc := by rw [hKc]; push_cast; omega
    exact hw.trans this
  -- the budgets
  have hU1n : (U₁.card : ℝ) ≤ ζ * n := hU₁
  set u1 : ℕ := U₁.card with hu1
  have hbig : ((u1 + 2 * (s * a0) + 3 * Kc + 4 * Kc * 8 + 1 : ℕ) : ℝ) = u1 + D := by
    rw [hD]; push_cast; ring
  have hDn : (8 * D + 1 : ℝ) ≤ n := by exact_mod_cast hnD
  have hζ8 : ζ ≤ 1 / 8 := min_le_left _ _
  have hζc : ζ ≤ c' / (2 * P2) := by
    rw [hζ, hP2, pow_succ]; exact (min_le_right _ _).trans (le_of_eq (by ring))
  have hαM : ((u1 + 2 * (s * a0) + 3 * Kc + 4 * Kc * 8 + 1 : ℕ) : ℝ) < 1 / 2 * n := by
    rw [hbig]
    have : (u1 : ℝ) ≤ n / 8 := hU1n.trans (by nlinarith)
    linarith
  have hβM : P2 * ((u1 + 2 * (s * a0) + 3 * Kc + 4 * Kc * 8 + 1 : ℕ) : ℝ) < c' * n := by
    rw [hbig]
    have h1 : P2 * (u1 : ℝ) ≤ c' / 2 * n := by
      have := mul_le_mul_of_nonneg_left (hU1n.trans (mul_le_mul_of_nonneg_right hζc
        (Nat.cast_nonneg n))) hP2pos.le
      calc P2 * (u1 : ℝ) ≤ P2 * (c' / (2 * P2) * n) := this
        _ = c' / 2 * n := by field_simp
    have h2 : 4 * P2 * D / c' ≤ n := (Nat.le_ceil _).trans hnR
    rw [div_le_iff₀ hc'] at h2
    nlinarith
  -- the library over all divisible residues
  set S : Finset (Finset (Sym2 V)) :=
    (insideEdges G U).powerset.filter (fun L => IsIntDiv onePart K3fam L) with hSdef
  have hScard : S.card ≤ s := by
    refine (card_filter_le _ _).trans ?_
    rw [card_powerset]
    exact Nat.pow_le_pow_right (by norm_num) (hinside_card _ subset_rfl)
  obtain ⟨A, hAG, -, hAout, hAcard, hAS⟩ := library_absorber c' Kc a0 s u1 G hcand hsup U U₁
    hUU₁ le_rfl hcert le_rfl hαM hβM S hScard (fun L hL => by
      rw [hSdef, mem_filter, mem_powerset] at hL
      exact hL)
  refine ⟨A, hAG, ?_, ?_, fun L hL hdiv => hAS L ?_⟩
  · rw [disjoint_left]
    intro e heA heI
    obtain ⟨v, hv, hvU⟩ := hAout e heA
    exact hvU (mem_of_mem_insideEdges heI hv)
  · intro v
    have h1 : ((A.filter fun e => v ∈ e).card : ℝ) ≤ A.card := by
      exact_mod_cast card_filter_le _ _
    have h2 : (A.card : ℝ) ≤ ((s * a0 : ℕ) : ℝ) := by
      exact_mod_cast hAcard.trans (Nat.mul_le_mul_right _ hScard)
    have h3 : ((s * a0 : ℕ) : ℝ) / ρ ≤ n := (Nat.le_ceil _).trans hnρ
    rw [div_le_iff₀ hρ] at h3
    linarith
  · rw [hSdef, mem_filter, mem_powerset]
    exact ⟨hL, hdiv⟩

end NashWilliams18
