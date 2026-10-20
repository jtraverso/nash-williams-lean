/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.RealInverse.Stages

/-! # The general real inverse producer

For every finite family `F` of three-element multisets on `Fin 4` there is a
constant `C(F) > 0`, chosen before the host, with
`PaddedGeneral.CompleteInverseCertLocalBound F C(F)`.

The chain is the sum of three actual chains on permitted copies:

1. global type columns (`classTotal_globalMode`), removing all class totals;
2. balanced vertex-profile columns (`vertex_stage`, `vertexFactor_prop`),
   removing every local profile; the coefficients are the bounded linear
   section of `exists_uniform_profile_coefficients`, which sum to zero in
   each class;
3. zero-profile edge corrections (`edge_stage`).

With `K₁, K₂` the section constants of the global and local profile matrices,
`C(F) = 64 K₁ + 24 K₂ (1 + 64 K₁) + 6 (1 + 24 K₂)(1 + 64 K₁)`. -/

noncomputable section

namespace PaddedGeneral.RealInverse

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedNibble

/-- The final inverse constant in terms of the two section constants. -/
def realInverseConstant (K₁ K₂ : ℝ) : ℝ :=
  64 * K₁ + 24 * K₂ * (1 + 64 * K₁) + 6 * (1 + 24 * K₂) * (1 + 64 * K₁)

theorem final_budget (K₁ K₂ ε γ n : ℝ) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hε : 0 ≤ ε)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hn : 0 < n) :
    64 * K₁ * ε / (γ ^ 3 * n) + 3 * (8 * K₂ * ((1 + 64 * K₁) * ε / γ ^ 3) / (γ ^ 2 * n)) +
        6 * ((1 + 24 * K₂) * (1 + 64 * K₁) * ε / γ ^ 5) / (γ * n) ≤
      realInverseConstant K₁ K₂ * ε / (γ ^ 6 * n) := by
  have heq : 64 * K₁ * ε / (γ ^ 3 * n) +
        3 * (8 * K₂ * ((1 + 64 * K₁) * ε / γ ^ 3) / (γ ^ 2 * n)) +
        6 * ((1 + 24 * K₂) * (1 + 64 * K₁) * ε / γ ^ 5) / (γ * n) =
      (64 * K₁ * γ ^ 3 + 24 * K₂ * (1 + 64 * K₁) * γ +
        6 * (1 + 24 * K₂) * (1 + 64 * K₁)) * ε / (γ ^ 6 * n) := by
    field_simp
    ring
  rw [heq]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ hε
  unfold realInverseConstant
  have h3 : γ ^ 3 ≤ 1 := pow_le_one₀ hγ.le hγ1
  have ha : 64 * K₁ * γ ^ 3 ≤ 64 * K₁ := by nlinarith
  have hb : 24 * K₂ * (1 + 64 * K₁) * γ ≤ 24 * K₂ * (1 + 64 * K₁) := by
    have : 0 ≤ 24 * K₂ * (1 + 64 * K₁) := by positivity
    nlinarith
  linarith

/-- **The general real inverse producer.** -/
theorem exists_completeInverseCertLocalBound (F : Finset (Multiset (Fin 4)))
    (hF : ∀ τ ∈ F, Multiset.card τ = 3) :
    ∃ C : ℝ, 0 < C ∧ CompleteInverseCertLocalBound F C := by
  classical
  obtain ⟨K₁, hK₁, hglob⟩ := exists_bounded_global_coefficients F
  obtain ⟨K₂, hK₂, hprof⟩ := exists_uniform_profile_coefficients F
  refine ⟨realInverseConstant K₁ K₂, by unfold realInverseConstant; positivity, ?_⟩
  intro V _ _ p r ε γ hε hγ hγ1 hlarge hmin hs hr hfull
  obtain ⟨hspan, hloc⟩ := hfull
  set n : ℝ := (Fintype.card V : ℝ) with hn_def
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hn : 0 < n := by
    by_contra h
    have : n = 0 := le_antisymm (not_lt.mp h) hn0
    rw [this, mul_zero] at hlarge
    norm_num at hlarge
  set m : ℝ := γ * n with hm_def
  have hm : 8 ≤ m := hlarge
  have hmin' : ∀ k, m ≤ classSize p k := hmin
  have hm0 : 0 < m := by linarith
  /- Stage 1: global type columns. -/
  obtain ⟨c, hc, hcb⟩ := hglob V p r ε hε hr hspan
  set c' : Multiset (Fin 4) → ℝ := fun τ => if h : τ ∈ F then c ⟨τ, h⟩ else 0 with hc'
  have hNlow : ∀ τ ∈ F, m ^ 3 / 64 ≤ (typeCount p F τ : ℝ) :=
    fun τ hτ => typeCount_lower p F hτ (hF τ hτ) hm hmin'
  have hN : ∀ τ ∈ F, typeCount p F τ ≠ 0 := by
    intro τ hτ h0
    have h1 := hNlow τ hτ
    rw [h0, Nat.cast_zero] at h1
    have : 0 < m ^ 3 / 64 := by positivity
    linarith
  set X₁ : Multiset (Fin 4) → V → V → V → ℝ :=
    fun τ _ _ _ => c' τ / typeCount p F τ with hX₁
  set w₁ := typedWeight p F X₁ with hw₁
  have hw₁s : TernarySymmetric w₁ :=
    typedWeight_symmetric p F X₁ (fun τ => ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩)
  have hw₁p : TernarySupported p F w₁ := typedWeight_supported p F X₁
  set M₁ : ℝ := 64 * K₁ * ε / (γ ^ 3 * n) with hM₁_def
  have hM₁ : 0 ≤ M₁ := by positivity
  have hw₁b : ∀ a b d, |w₁ a b d| ≤ M₁ := by
    intro a b d
    apply typedWeight_bound p F X₁ M₁ hM₁
    intro a b d _ _ _ hτ
    have hcτ : |c' {p a, p b, p d}| ≤ K₁ * ε * n ^ 2 := by
      simp only [hc', dif_pos hτ]
      exact hcb ⟨_, hτ⟩
    have hNτ := hNlow _ hτ
    have hNpos : 0 < (typeCount p F {p a, p b, p d} : ℝ) :=
      lt_of_lt_of_le (by positivity) hNτ
    show |c' {p a, p b, p d} / typeCount p F {p a, p b, p d}| ≤ M₁
    rw [abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos]
    calc
      _ ≤ K₁ * ε * n ^ 2 := hcτ
      _ = M₁ * (m ^ 3 / 64) := by
        rw [hM₁_def, hm_def]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hNτ hM₁
  have hw₁tot : classTotal p (fun a b => boundary (chainOf p F w₁) s(a, b)) =
      classTotal p (fun a b => r s(a, b)) := by
    rw [hw₁, hX₁, classTotal_globalMode p F c' hN, ← hc]
    show _ = ∑ τ : F, c τ • (fun i j => (typeEdgeVec τ.val i j : ℝ))
    rw [← Finset.sum_coe_sort F]
    apply sum_congr rfl
    intro τ _
    simp only [hc', dif_pos τ.2]
  set r₁ : Sym2 V → ℝ := fun e => r e - boundary (chainOf p F w₁) e with hr₁
  set E₁ : ℝ := (1 + 64 * K₁) * ε / γ ^ 3 with hE₁_def
  have hE₁ : 0 ≤ E₁ := by positivity
  have hεγ3 : ε ≤ ε / γ ^ 3 := le_div_self hε (by positivity) (pow_le_one₀ hγ.le hγ1)
  have hr₁b : ∀ e, |r₁ e| ≤ E₁ := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      have h1 := hr s(a, b)
      have h2 : |boundary (chainOf p F w₁) s(a, b)| ≤ n * M₁ := by
        rw [chainOf_boundary p F hw₁s hw₁p]
        exact abs_ternaryLoad_le w₁ M₁ hw₁b a b
      have h3 : n * M₁ = 64 * K₁ * ε / γ ^ 3 := by
        rw [hM₁_def]
        field_simp
      have h4 : E₁ = ε / γ ^ 3 + 64 * K₁ * ε / γ ^ 3 := by rw [hE₁_def]; ring
      calc
        |r₁ s(a, b)| ≤ |r s(a, b)| + |boundary (chainOf p F w₁) s(a, b)| := abs_sub _ _
        _ ≤ E₁ := by linarith
  have hloc₁ : LocalSpanCompat p F r₁ :=
    hloc.sub (localSpan_boundary p F _ _ (chainOf_supported p F w₁))
  have htot₁ : ∀ i j, classTotal p (fun a b => r₁ s(a, b)) i j = 0 := by
    intro i j
    have h := congrFun (congrFun hw₁tot i) j
    rw [hr₁, classTotal_sub, h, sub_self]
  /- Stage 2: balanced vertex-profile columns. -/
  have hcoef := fun i => hprof V p r₁ E₁ hE₁ hr₁b hloc₁ i (htot₁ i)
  choose cc hcc₁ hcc₂ hcc₃ using hcoef
  have hκex : ∀ (τ : Multiset (Fin 4)) (i : Fin 4), ∃ κ : ℝ, τ ∈ F → i ∈ τ →
      m ^ 2 / 8 ≤ κ ∧
        ∀ l, vertexFactor (classSize p) τ i l = κ * ((typeDegVec τ i l : ℤ) : ℝ) := by
    intro τ i
    by_cases h : τ ∈ F ∧ i ∈ τ
    · obtain ⟨κ, h1, h2⟩ := vertexFactor_prop (classSize p) hm hmin' (hF τ h.1) h.2
      exact ⟨κ, fun _ _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose κ hκ using hκex
  set φ : Multiset (Fin 4) → V → ℝ := fun τ v =>
    if h : τ ∈ F ∧ p v ∈ τ then
      cc (p v) ⟨v, (mem_classVertices p (p v) v).mpr rfl⟩ ⟨τ, mem_filter.mpr h⟩ / κ τ (p v)
    else 0 with hφ_def
  have hφeval : ∀ τ l v (hv : v ∈ classVertices p l) (h : τ ∈ F ∧ l ∈ τ),
      φ τ v = cc l ⟨v, hv⟩ ⟨τ, mem_filter.mpr h⟩ / κ τ l := by
    intro τ l v hv h
    have hl : p v = l := (mem_classVertices p l v).mp hv
    subst hl
    simp only [hφ_def, dif_pos h]
  have hφzero : ∀ τ v, ¬ (τ ∈ F ∧ p v ∈ τ) → φ τ v = 0 := by
    intro τ v h
    simp only [hφ_def, dif_neg h]
  have hφsum : ∀ τ l, ∑ v ∈ classVertices p l, φ τ v = 0 := by
    intro τ l
    by_cases h : τ ∈ F ∧ l ∈ τ
    · rw [← Finset.sum_coe_sort (classVertices p l)]
      rw [sum_congr rfl (fun v _ => hφeval τ l v.val v.2 h), ← sum_div]
      have h0 := congrFun (hcc₂ l) ⟨τ, mem_filter.mpr h⟩
      simp only [Finset.sum_apply, Pi.zero_apply] at h0
      simp only [Subtype.coe_eta, h0, zero_div]
    · apply sum_eq_zero
      intro v hv
      have hl := (mem_classVertices p l v).mp hv
      exact hφzero τ v (fun h' => h ⟨h'.1, hl ▸ h'.2⟩)
  set B₂ : ℝ := 8 * K₂ * E₁ / (γ ^ 2 * n) with hB₂_def
  have hB₂ : 0 ≤ B₂ := by positivity
  have hφb : ∀ τ v, |φ τ v| ≤ B₂ := by
    intro τ v
    by_cases h : τ ∈ F ∧ p v ∈ τ
    · rw [hφeval τ (p v) v ((mem_classVertices p (p v) v).mpr rfl) h]
      obtain ⟨hκ1, _⟩ := hκ τ (p v) h.1 h.2
      have hκpos : 0 < κ τ (p v) := lt_of_lt_of_le (by positivity) hκ1
      rw [abs_div, abs_of_pos hκpos, div_le_iff₀ hκpos]
      calc
        _ ≤ K₂ * n * E₁ := hcc₃ _ _ _
        _ = B₂ * (m ^ 2 / 8) := by
          rw [hB₂_def, hm_def]
          field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hκ1 hB₂
    · rw [hφzero τ v h, abs_zero]
      exact hB₂
  obtain ⟨hw₂s, hw₂p, hw₂b, hw₂row⟩ := vertex_stage p F φ hφsum hB₂ hφb
  set w₂ := typedWeight p F (fun τ a b c => φ τ a + φ τ b + φ τ c) with hw₂
  have hrow : ∀ u l, classRow p (fun a b => ternaryLoad w₂ a b) u l =
      classRow p (fun a b => r₁ s(a, b)) u l := by
    intro u l
    have hv : u ∈ classVertices p (p u) := (mem_classVertices p (p u) u).mpr rfl
    rw [hw₂row u l, ← hcc₁ (p u) ⟨u, hv⟩]
    rw [← sum_filter_of_ne (p := fun τ => p u ∈ τ)]
    · rw [← Finset.sum_coe_sort]
      show _ = (∑ τ : (F.filter fun τ => p u ∈ τ),
        cc (p u) ⟨u, hv⟩ τ • fun j => (typeDegVec τ.val (p u) j : ℝ)) l
      rw [Finset.sum_apply]
      apply sum_congr rfl
      intro τ _
      have hτ := mem_filter.mp τ.2
      obtain ⟨hκ1, hκ2⟩ := hκ τ.val (p u) hτ.1 hτ.2
      have hκpos : κ τ.val (p u) ≠ 0 := (lt_of_lt_of_le (by positivity) hκ1).ne'
      rw [hφeval τ.val (p u) u hv hτ, hκ2 l]
      simp only [Pi.smul_apply, smul_eq_mul, Subtype.coe_eta]
      field_simp
    · intro τ _ hne
      by_contra hτ
      exact hne (by rw [vertexFactor_eq_zero hτ, mul_zero])
  /- Stage 3: zero-profile edge corrections. -/
  set g₂ : V → V → ℝ := fun a b => r₁ s(a, b) - boundary (chainOf p F w₂) s(a, b) with hg₂
  have hg₂s : ∀ a b, g₂ a b = g₂ b a := by
    intro a b
    simp only [hg₂]
    rw [Sym2.eq_swap]
  have hg₂d : ∀ a, g₂ a a = 0 := by
    intro a
    simp only [hg₂, hr₁]
    rw [hs.diag a, chainOf_boundary p F hw₁s hw₁p, chainOf_boundary p F hw₂s hw₂p,
      hw₁p.load_diag, hw₂p.load_diag]
    ring
  have hg₂r : ∀ a l, ∑ c ∈ classVertices p l, g₂ a c = 0 := by
    intro a l
    change classRow p g₂ a l = 0
    rw [hg₂, classRow_sub]
    simp only [chainOf_boundary p F hw₂s hw₂p]
    rw [hrow a l, sub_self]
  have hg₂a : ∀ x y, x ≠ y → (¬ ∃ k, Link F (p x) (p y) k) → g₂ x y = 0 := by
    intro x y hxy hnot
    have hload : ∀ w : V → V → V → ℝ, TernarySupported p F w → ternaryLoad w x y = 0 :=
      fun w hw => sum_eq_zero fun d _ => hw x y d (fun h => hnot ⟨p d, h.2.2.2⟩)
    have hrxy : r s(x, y) = 0 := by
      apply hs
      intro h
      exact hnot ((SimpleGraph.mem_edgeSet _).mp (SimpleGraph.mem_edgeFinset.mp h)).2
    simp only [hg₂, hr₁]
    rw [chainOf_boundary p F hw₁s hw₁p, chainOf_boundary p F hw₂s hw₂p,
      hload w₁ hw₁p, hload w₂ hw₂p, hrxy]
    ring
  set E₂ : ℝ := (1 + 24 * K₂) * (1 + 64 * K₁) * ε / γ ^ 5 with hE₂_def
  have hE₂ : 0 ≤ E₂ := by positivity
  have hg₂b : ∀ a b, |g₂ a b| ≤ E₂ := by
    intro a b
    have h1 := hr₁b s(a, b)
    have h2 : |boundary (chainOf p F w₂) s(a, b)| ≤ n * (3 * B₂) := by
      rw [chainOf_boundary p F hw₂s hw₂p]
      exact abs_ternaryLoad_le w₂ (3 * B₂) hw₂b a b
    have h3 : n * (3 * B₂) = 24 * K₂ * E₁ / γ ^ 2 := by
      rw [hB₂_def]
      field_simp
      ring
    have h4 : E₁ ≤ E₁ / γ ^ 2 := le_div_self hE₁ (by positivity) (pow_le_one₀ hγ.le hγ1)
    have h5 : E₂ = E₁ / γ ^ 2 + 24 * K₂ * E₁ / γ ^ 2 := by
      rw [hE₂_def, hE₁_def]
      field_simp
    calc
      |g₂ a b| ≤ |r₁ s(a, b)| + |boundary (chainOf p F w₂) s(a, b)| := abs_sub _ _
      _ ≤ E₂ := by linarith
  obtain ⟨w₃, hw₃s, hw₃p, hw₃b, hw₃l⟩ :=
    edge_stage p F g₂ hg₂s hg₂d hg₂r hg₂a hm hmin' hE₂ hg₂b
  /- Assembly. -/
  refine ⟨fun T => chainOf p F w₁ T + chainOf p F w₂ T + chainOf p F w₃ T, ?_, ?_, ?_⟩
  · exact ((chainOf_supported p F w₁).add (chainOf_supported p F w₂)).add
      (chainOf_supported p F w₃)
  · funext e
    rw [boundary_add, boundary_add]
    induction e using Sym2.ind with
    | _ a b =>
      rw [chainOf_boundary p F hw₃s hw₃p, hw₃l a b]
      simp only [hg₂, hr₁]
      ring
  · intro T
    have h1 := chainOf_bound p F hw₁s hw₁p M₁ hM₁ hw₁b T
    have h2 := chainOf_bound p F hw₂s hw₂p (3 * B₂) (by positivity) hw₂b T
    have h3 := chainOf_bound p F hw₃s hw₃p (6 * E₂ / m) (by positivity) hw₃b T
    have hfin := final_budget K₁ K₂ ε γ n hK₁.le hK₂.le hε hγ hγ1 hn
    calc
      |chainOf p F w₁ T + chainOf p F w₂ T + chainOf p F w₃ T| ≤
          |chainOf p F w₁ T| + |chainOf p F w₂ T| + |chainOf p F w₃ T| := abs_add_three _ _ _
      _ ≤ M₁ + 3 * B₂ + 6 * E₂ / m := by linarith
      _ ≤ realInverseConstant K₁ K₂ * ε / (γ ^ 6 * n) := by
        rw [hM₁_def, hB₂_def, hE₂_def, hm_def, hE₁_def]
        convert hfin using 2

end PaddedGeneral.RealInverse
