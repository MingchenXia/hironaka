import DeJongAlterations.StableModificationBridge.AffineClosedSectionLifting
import DeJongAlterations.StableModification.CurvesField.AmplePositiveNormalization

/-! Actual reduced two-section geometry internally lifts every sufficiently high whole global section. -/

noncomputable section

namespace DeJongAlterations.StableModificationBridge.NilradicalSectionLifting

open CategoryTheory Opposite AlgebraicGeometry
open StableModification StableModification.Projectivity StableModification.Cohomology
open StableModification.CurvesField StableModification.CurvesField.Positive
open StableModification.CurvesField.Ample StableModification.CurvesField.Ample.LineBundleData
open Projectivity.LineBundleData TwoSectionScalarVanishing SubschemeScalarVanishing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

/-- Powers of the SAME actual section commute with its WHOLE original pullback. -/
theorem pullback_npow {X Y : Scheme.{u}} (f : Y ⟶ X) {L : LineBundleData X}
    {m : ℤ} {U : X.Opens} (s : L.Sections m U) (k : ℕ) :
    (s.npow k).pullback f = (s.pullback f).npow k := by
  ext j
  simp only [Sections.coeff_pullback, Sections.coeff_npow, map_pow]

/-- The WHOLE native unit transition is preserved by the SAME actual pullback. -/
theorem transUnit_pullback {X Y : Scheme.{u}} (f : Y ⟶ X) {L : LineBundleData X}
    {m : ℤ} {U V : X.Opens} {τ : L.Sections m U} {σ : L.Sections m V}
    (hτ : τ.nonvanishingLocus = U) (hσ : σ.nonvanishingLocus = V) :
    f.app (U ⊓ V) (transUnit hσ hτ : Γ(X, U ⊓ V)) =
      (transUnit (τ := τ.pullback f) (σ := σ.pullback f)
        (by rw [Sections.nonvanishingLocus_pullback, hσ])
        (by rw [Sections.nonvanishingLocus_pullback, hτ]) :
        Γ(Y, f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V)) := by
  rw [coe_transUnit, coe_transUnit]
  symm
  apply transFun_eq_of_eq_smul
  have h := congrArg (Sections.pullback f) (restrict_eq_transFun_smul τ hσ)
  rw [Sections.pullback_smul', Sections.pullback_restrict', Sections.pullback_restrict'] at h
  exact h

/-- Section transport uses only equality of the SAME native opens. -/
def sectionOn {Y : Scheme.{u}} {M : LineBundleData Y} {m : ℤ} {W Z : Y.Opens}
    (h : W = Z) (s : M.Sections m Z) : M.Sections m W := by
  subst W
  exact s

private theorem sectionOn_global {Y : Scheme.{u}} {M : LineBundleData Y} {m : ℤ}
    {W Z : Y.Opens} (h : W = Z) (s : M.Sections m ⊤) :
    sectionOn h (s.restrict (le_top : Z ≤ ⊤)) = s.restrict (le_top : W ≤ ⊤) := by
  subst W
  rfl

private theorem sectionOn_nonvanishing {Y : Scheme.{u}} {M : LineBundleData Y} {m : ℤ}
    {W Z : Y.Opens} (h : W = Z) (s : M.Sections m Z) :
    (sectionOn h s).nonvanishingLocus = s.nonvanishingLocus := by
  subst W
  rfl

private theorem sectionOn_roundtrip {Y : Scheme.{u}} {M : LineBundleData Y} {m : ℤ}
    {W Z : Y.Opens} (h : W = Z) (s : M.Sections m W) :
    sectionOn h (sectionOn h.symm s) = s := by
  subst W
  rfl

private theorem overlap_eq {X : Scheme.{u}} (I : X.IdealSheafData) {U V : X.Opens}
    {W Z : I.subscheme.Opens} (hW : W = I.subschemeι ⁻¹ᵁ U)
    (hZ : Z = I.subschemeι ⁻¹ᵁ V) : W ⊓ Z = I.subschemeι ⁻¹ᵁ (U ⊓ V) := by
  rw [hW, hZ]
  rfl

/-- Actual whole-frame pullback INTERNALLY gives the SAME quotient transition identity. -/
theorem coverMap_transUnit {X : Scheme.{u}} (I : X.IdealSheafData) {L : LineBundleData X}
    {m : ℤ} {U V : X.Opens} {τ : L.Sections m U} {σ : L.Sections m V}
    (hτ : τ.nonvanishingLocus = U) (hσ : σ.nonvanishingLocus = V)
    {W Z : I.subscheme.Opens} (hW : W = I.subschemeι ⁻¹ᵁ U)
    (hZ : Z = I.subschemeι ⁻¹ᵁ V)
    {τr : (L.pullback I.subschemeι).Sections m W}
    {σr : (L.pullback I.subschemeι).Sections m Z}
    (hτr : τr.nonvanishingLocus = W) (hσr : σr.nonvanishingLocus = Z)
    (heτ : sectionOn hW (τ.pullback I.subschemeι) = τr)
    (heσ : sectionOn hZ (σ.pullback I.subschemeι) = σr) :
    coverMap I (U ⊓ V) (W ⊓ Z) (overlap_eq I hW hZ)
        (transUnit hσ hτ : Γ(X, U ⊓ V)) =
      (transUnit hσr hτr : Γ(I.subscheme, W ⊓ Z)) := by
  subst W
  subst Z
  change τ.pullback I.subschemeι = τr at heτ
  change σ.pullback I.subschemeι = σr at heσ
  subst τr
  subst σr
  exact transUnit_pullback I.subschemeι hτ hσ

private theorem sectionOn_pullback_restrict {X : Scheme.{u}} (I : X.IdealSheafData)
    {L : LineBundleData X} {m : ℤ} {U : X.Opens} {W : I.subscheme.Opens}
    (hW : W = I.subschemeι ⁻¹ᵁ U) (s : L.Sections m ⊤) :
    sectionOn hW ((s.restrict (le_top : U ≤ ⊤)).pullback I.subschemeι) =
      (s.pullback I.subschemeι).restrict (le_top : W ≤ ⊤) := by
  subst W
  exact Sections.pullback_restrict L m I.subschemeι le_top s

private theorem sectionOn_pullback_smul_npow {X : Scheme.{u}} (I : X.IdealSheafData)
    {L : LineBundleData X} {m : ℤ} {U : X.Opens} {W : I.subscheme.Opens}
    (hW : W = I.subschemeι ⁻¹ᵁ U) (a : Γ(X, U)) (τ : L.Sections m U) (k : ℕ) :
    sectionOn hW ((a • τ.npow k).pullback I.subschemeι) =
      coverMap I U W hW a • (sectionOn hW (τ.pullback I.subschemeι)).npow k := by
  subst W
  change (a • τ.npow k).pullback I.subschemeι =
    I.subschemeι.app U a • (τ.pullback I.subschemeι).npow k
  rw [Sections.pullback_smul, pullback_npow]

private theorem exists_reduced_global_frame {X : Scheme.{u}} {L : LineBundleData X}
    {N : ℤ} {U : X.Opens} (hU : IsAffineOpen U)
    (s : (L.pullback X.nilradical.subschemeι).Sections N ⊤)
    (h : s.nonvanishingLocus = X.nilradical.subschemeι ⁻¹ᵁ U) :
    ∃ τ : L.Sections N U, τ.nonvanishingLocus = U ∧
      sectionOn h (τ.pullback X.nilradical.subschemeι) = leftFrame s := by
  let sr := sectionOn h.symm (leftFrame s)
  have hsr : sr.nonvanishingLocus = X.nilradical.subschemeι ⁻¹ᵁ U := by
    rw [sectionOn_nonvanishing, leftFrame_nonvanishing, h]
  obtain ⟨τ, hτ, hτnv⟩ :=
    AffineClosedSectionLifting.exists_nilradical_frame L N hU sr hsr
  refine ⟨τ, hτnv, ?_⟩
  rw [hτ]
  exact sectionOn_roundtrip h _

variable {X : Scheme.{u}} {L : LineBundleData X} {N : ℤ} {U V : X.Opens}
  [IsLocallyNoetherian X] [CompactSpace X.nilradical.subscheme]
  [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X.nilradical.subscheme))]
  (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : IsAffineOpen (U ⊓ V))
  (s₀ s₁ : (L.pullback X.nilradical.subschemeι).Sections N ⊤)
  (h₀ : s₀.nonvanishingLocus = X.nilradical.subschemeι ⁻¹ᵁ U)
  (h₁ : s₁.nonvanishingLocus = X.nilradical.subschemeι ⁻¹ᵁ V)
  {K : Type u} [Field K] (p : X.nilradical.subscheme ⟶ Spec (.of K)) (hp : IsProjectiveOver p)

include hp hU hV hUV h₀ h₁ in
/-- Every sufficiently high WHOLE reduced global section lifts INTERNALLY on the SAME original scheme. -/
theorem exists_eventual_surjective_pullback
    (hcov : s₀.nonvanishingLocus ⊔ s₁.nonvanishingLocus = ⊤)
    (haff₀ : IsAffineOpen s₀.nonvanishingLocus) (haff₁ : IsAffineOpen s₁.nonvanishingLocus) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      Function.Surjective (fun t : L.Sections (N * k) ⊤ => t.pullback X.nilradical.subschemeι) := by
  obtain ⟨τ, hτ, heτ⟩ := exists_reduced_global_frame hU s₀ h₀
  obtain ⟨σ, hσ, heσ⟩ := exists_reduced_global_frame hV s₁ h₁
  let g := transUnit hσ hτ
  have hg : coverMap X.nilradical (U ⊓ V) _ (overlap_eq X.nilradical h₀ h₁) g =
      (transition s₀ s₁ : Γ(X.nilradical.subscheme, s₀.nonvanishingLocus ⊓ s₁.nonvanishingLocus)) :=
    coverMap_transUnit X.nilradical hτ hσ h₀ h₁
      (leftFrame_nonvanishing s₀) (rightFrame_nonvanishing s₁) heτ heσ
  obtain ⟨k₀, hk₀⟩ := NilradicalCoverEngine.exists_pair_lifts hU hV hUV s₀ s₁ h₀ h₁
    g hg p hp hcov haff₀ haff₁
  have hcover : U ⊔ V = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨z, rfl⟩ := NilradicalCoverEngine.reduction_surjective X x
    have hz : z ∈ s₀.nonvanishingLocus ⊔ s₁.nonvanishingLocus := by
      rw [hcov]
      trivial
    rw [h₀, h₁] at hz
    exact hz
  refine ⟨k₀, fun k hk t => ?_⟩
  let αr := coefU (leftFrame_nonvanishing s₀) k t
  let βr := coefU (rightFrame_nonvanishing s₁) k t
  obtain ⟨α, hα⟩ := coverMap_surjective X.nilradical U hU _ h₀ αr
  obtain ⟨β, hβ⟩ := coverMap_surjective X.nilradical V hV _ h₁ βr
  have hcompat : resR U V β - (g : Γ(X, U ⊓ V)) ^ k * resL U V α ∈
      X.nilradical.ideal ⟨_, hUV⟩ := by
    rw [← coverMap_kernel X.nilradical (U ⊓ V) hUV _ (overlap_eq X.nilradical h₀ h₁)]
    change coverMap X.nilradical (U ⊓ V) _ (overlap_eq X.nilradical h₀ h₁)
      (resR U V β - (g : Γ(X, U ⊓ V)) ^ k * resL U V α) = 0
    rw [map_sub, map_mul, map_pow, hg,
      coverMap_restrict X.nilradical inf_le_right h₁ (overlap_eq X.nilradical h₀ h₁),
      coverMap_restrict X.nilradical inf_le_left h₀ (overlap_eq X.nilradical h₀ h₁), hα, hβ]
    apply sub_eq_zero.mpr
    exact resR_coefU_coefU (leftFrame_nonvanishing s₀) (rightFrame_nonvanishing s₁) k t
  obtain ⟨a, b, hab, ha, hb⟩ := hk₀ k hk α β hcompat
  have hqa : coverMap X.nilradical U _ h₀ a = αr := by
    rw [← coverMap_kernel X.nilradical U hU _ h₀] at ha
    change coverMap X.nilradical U _ h₀ (a - α) = 0 at ha
    rw [map_sub] at ha
    exact (sub_eq_zero.mp ha).trans hα
  have hqb : coverMap X.nilradical V _ h₁ b = βr := by
    rw [← coverMap_kernel X.nilradical V hV _ h₁] at hb
    change coverMap X.nilradical V _ h₁ (b - β) = 0 at hb
    rw [map_sub] at hb
    exact (sub_eq_zero.mp hb).trans hβ
  obtain ⟨T, hT₀, hT₁⟩ := exists_section_of_pair hσ hcover k a b
    (by simpa only [g, coe_transUnit] using hab)
  refine ⟨T, ?_⟩
  have he₀ : (T.pullback X.nilradical.subschemeι).restrict
      (le_top : s₀.nonvanishingLocus ≤ ⊤) = t.restrict le_top := by
    rw [← sectionOn_pullback_restrict X.nilradical h₀ T, hT₀,
      sectionOn_pullback_smul_npow, heτ, hqa]
    exact (restrict_eq_coefU_smul (leftFrame_nonvanishing s₀) k t).symm
  have he₁ : (T.pullback X.nilradical.subschemeι).restrict
      (le_top : s₁.nonvanishingLocus ≤ ⊤) = t.restrict le_top := by
    rw [← sectionOn_pullback_restrict X.nilradical h₁ T, hT₁,
      sectionOn_pullback_smul_npow, heσ, hqb]
    exact (restrict_eq_coefU_smul (rightFrame_nonvanishing s₁) k t).symm
  exact (twistSheafAb ((L.pullback X.nilradical.subschemeι).twist
    (unitModule X.nilradical.subscheme) (N * k))).eq_of_locally_eq₂
      (homOfLE (le_top : s₀.nonvanishingLocus ≤ ⊤))
      (homOfLE (le_top : s₁.nonvanishingLocus ≤ ⊤)) (by rw [hcov]) _ _ he₀ he₁

end DeJongAlterations.StableModificationBridge.NilradicalSectionLifting
