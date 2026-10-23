import DeJongAlterations.StableModificationBridge.NilradicalSectionLifting

/-! Actual reduced good sections INTERNALLY give actual original good sections after native nilradical lifting. -/

noncomputable section

namespace DeJongAlterations.StableModificationBridge.NilradicalGoodSection

open CategoryTheory AlgebraicGeometry TopologicalSpace
open StableModification StableModification.Projectivity StableModification.CurvesField
open Projectivity.LineBundleData

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

/-- The SAME actual reduction and native nonvanishing opens transfer both original good-section conditions. -/
theorem good_conditions_of_reduction {X : Scheme.{u}} {L : LineBundleData X} {n m : ℤ}
    (s : L.Sections n ⊤) (sr : (L.pullback X.nilradical.subschemeι).Sections m ⊤)
    (hpre : X.nilradical.subschemeι ⁻¹ᵁ s.nonvanishingLocus = sr.nonvanishingLocus)
    (hgen : ∀ x : X.nilradical.subscheme, ¬ IsClosed ({x} : Set X.nilradical.subscheme) →
      x ∈ sr.nonvanishingLocus)
    (hzero : ∀ x : X.nilradical.subscheme, ¬ IsClosed ({x} : Set X.nilradical.subscheme) →
      ∃ z, x ⤳ z ∧ z ∉ sr.nonvanishingLocus) :
    (∀ x : X, ¬ IsClosed ({x} : Set X) → x ∈ s.nonvanishingLocus) ∧
      (∀ x : X, ¬ IsClosed ({x} : Set X) → ∃ z, x ⤳ z ∧ z ∉ s.nonvanishingLocus) := by
  have hclosed (x : X.nilradical.subscheme) (hx : IsClosed ({x} : Set X.nilradical.subscheme)) :
      IsClosed ({X.nilradical.subschemeι x} : Set X) := by
    simpa only [Set.image_singleton] using X.nilradical.subschemeι.isClosedEmbedding.isClosedMap _ hx
  constructor
  · intro x hx
    obtain ⟨y, rfl⟩ := NilradicalCoverEngine.reduction_surjective X x
    have hy : ¬ IsClosed ({y} : Set X.nilradical.subscheme) := fun h => hx (hclosed y h)
    have hmem := hgen y hy
    rw [← hpre] at hmem
    exact hmem
  · intro x hx
    obtain ⟨y, rfl⟩ := NilradicalCoverEngine.reduction_surjective X x
    have hy : ¬ IsClosed ({y} : Set X.nilradical.subscheme) := fun h => hx (hclosed y h)
    obtain ⟨z, hyz, hz⟩ := hzero y hy
    refine ⟨X.nilradical.subschemeι z, hyz.map X.nilradical.subschemeι.continuous, ?_⟩
    rw [← hpre] at hz
    exact hz

/-- An actual positive original good section is produced from the SAME actual reduced affine cover. -/
theorem exists_good_section_of_affine_cover
    {X : Scheme.{u}} [IsLocallyNoetherian X] {L : LineBundleData X} {N : ℕ}
    (hN : 0 < N) {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : IsAffineOpen (U ⊓ V))
    (s₀ s₁ : (L.pullback X.nilradical.subschemeι).Sections N ⊤)
    (h₀ : s₀.nonvanishingLocus = X.nilradical.subschemeι ⁻¹ᵁ U)
    (h₁ : s₁.nonvanishingLocus = X.nilradical.subschemeι ⁻¹ᵁ V)
    {K : Type u} [Field K] (p : X.nilradical.subscheme ⟶ Spec (.of K)) (hp : IsProjectiveOver p)
    (hcov : s₀.nonvanishingLocus ⊔ s₁.nonvanishingLocus = ⊤)
    (haff₀ : IsAffineOpen s₀.nonvanishingLocus) (haff₁ : IsAffineOpen s₁.nonvanishingLocus)
    (hgen : ∀ x : X.nilradical.subscheme, ¬ IsClosed ({x} : Set X.nilradical.subscheme) →
      x ∈ s₀.nonvanishingLocus)
    (hzero : ∀ x : X.nilradical.subscheme, ¬ IsClosed ({x} : Set X.nilradical.subscheme) →
      ∃ z, x ⤳ z ∧ z ∉ s₀.nonvanishingLocus) :
    ∃ (n : ℕ) (s : L.Sections n ⊤), 0 < n ∧
      X.nilradical.subschemeι ⁻¹ᵁ s.nonvanishingLocus = s₀.nonvanishingLocus ∧
      (∀ x : X, ¬ IsClosed ({x} : Set X) → x ∈ s.nonvanishingLocus) ∧
      (∀ x : X, ¬ IsClosed ({x} : Set X) → ∃ z, x ⤳ z ∧ z ∉ s.nonvanishingLocus) := by
  let : IsProper p := hp.isProper
  let : CompactSpace X.nilradical.subscheme := Ample.compactSpace_of_quasiCompact p
  let : IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X.nilradical.subscheme)) :=
    Ample.isAffineHom_diagonal_of_isSeparated p
  obtain ⟨k₀, hk₀⟩ := NilradicalSectionLifting.exists_eventual_surjective_pullback
    hU hV hUV s₀ s₁ h₀ h₁ p hp hcov haff₀ haff₁
  let k := max k₀ 1
  have hk : 0 < k := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  obtain ⟨T, hT⟩ := hk₀ k (le_max_left _ _) (s₀.npow k)
  change T.pullback X.nilradical.subschemeι = s₀.npow k at hT
  have hcast : (N : ℤ) * k = ((N * k : ℕ) : ℤ) := (Nat.cast_mul N k).symm
  let s := T.cast hcast
  have hpre : X.nilradical.subschemeι ⁻¹ᵁ s.nonvanishingLocus = s₀.nonvanishingLocus := by
    rw [Sections.nonvanishingLocus_cast, ← Sections.nonvanishingLocus_pullback, hT,
      Sections.nonvanishingLocus_npow s₀ hk]
  obtain ⟨hgen', hzero'⟩ := good_conditions_of_reduction s s₀ hpre hgen hzero
  exact ⟨N * k, s, Nat.mul_pos hN hk, hpre, hgen', hzero'⟩

end DeJongAlterations.StableModificationBridge.NilradicalGoodSection
