import DeJongAlterations.StableModification.CurvesField.AmplePositiveTwoSection
import DeJongAlterations.StableModification.CurvesField.AmpleSerre

/-! Actual projectivity and two actual global sections internally supply the scalar Serre engine input. -/

noncomputable section

namespace DeJongAlterations.StableModificationBridge.TwoSectionScalarVanishing

open CategoryTheory AlgebraicGeometry
open StableModification StableModification.Cohomology StableModification.Projectivity
open StableModification.CurvesField StableModification.CurvesField.Ample
open StableModification.CurvesField.Positive Projectivity.LineBundleData

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {Y : Scheme.{u}} {L : LineBundleData Y} {N : ℤ}
  (s₀ s₁ : L.Sections N ⊤)

/-- The left frame is the restriction of the SAME actual original global section. -/
def leftFrame : L.Sections N s₀.nonvanishingLocus := s₀.restrict le_top

/-- The actual left frame generates on the SAME original nonvanishing locus. -/
theorem leftFrame_nonvanishing : (leftFrame s₀).nonvanishingLocus = s₀.nonvanishingLocus := by
  rw [leftFrame, Sections.nonvanishingLocus_restrict, inf_idem]

/-- The right frame is the restriction of the SAME actual original global section. -/
def rightFrame : L.Sections N s₁.nonvanishingLocus := s₁.restrict le_top

/-- The actual right frame generates on the SAME original nonvanishing locus. -/
theorem rightFrame_nonvanishing : (rightFrame s₁).nonvanishingLocus = s₁.nonvanishingLocus := by
  rw [rightFrame, Sections.nonvanishingLocus_restrict, inf_idem]

/-- The actual unit transition between the SAME original two section frames. -/
def transition : Γ(Y, s₀.nonvanishingLocus ⊓ s₁.nonvanishingLocus)ˣ :=
  transUnit (rightFrame_nonvanishing s₁) (leftFrame_nonvanishing s₀)

variable [CompactSpace Y] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from Y))]
  {K : Type u} [Field K] (p : Y ⟶ Spec (.of K)) (hp : IsProjectiveOver p)

include p hp

/-- Every actual overlap coefficient is eventually an actual coboundary, INTERNALLY from projectivity. -/
theorem exists_scalar_coboundaries
    (hcov : s₀.nonvanishingLocus ⊔ s₁.nonvanishingLocus = ⊤)
    (h₀ : IsAffineOpen s₀.nonvanishingLocus) (h₁ : IsAffineOpen s₁.nonvanishingLocus) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∀ w : Γ(Y, s₀.nonvanishingLocus ⊓ s₁.nonvanishingLocus),
      ∃ a : Γ(Y, s₀.nonvanishingLocus), ∃ b : Γ(Y, s₁.nonvanishingLocus),
        w = resR s₀.nonvanishingLocus s₁.nonvanishingLocus b +
          (transition s₀ s₁ : Γ(Y, s₀.nonvanishingLocus ⊓ s₁.nonvanishingLocus)) ^ k *
            resL s₀.nonvanishingLocus s₁.nonvanishingLocus a := by
  let c := structureCoeff p
  let : Module.Finite K (cohomology (unitModule Y) c 1) :=
    finite_cohomology_of_isProjectiveOver hp (unitModule Y)
      (fun W _ => Module.Finite.self Γ(Y, W)) 1
  obtain ⟨k₀, hk₀⟩ := exists_twist_vanishing_generated s₀ s₁ hcov h₀ h₁ c
    (unitModule Y) (fun W _ => Module.Finite.self Γ(Y, W))
  refine ⟨k₀, fun k hk w => ?_⟩
  let e := twoTrivIso (rightFrame_nonvanishing s₁) (leftFrame_nonvanishing s₀)
    (unitModule Y) k hcov
  let E := (cohomologyIsoOfIso e c 1).toLinearEquiv.trans
    (cohomologyTwistOneEquiv (unitModule Y) s₀.nonvanishingLocus s₁.nonvanishingLocus
      (transition s₀ s₁ ^ (k : ℤ)) c hcov h₀ h₁ (h₀.inf h₁))
  have hzero := (hk₀ k hk).1
  have hsource : Subsingleton (cohomology (L.twist (unitModule Y) (N * k)) c 1) :=
    ModuleCat.isZero_iff_subsingleton.mp hzero
  let : Subsingleton (H1 (resUV (unitModule Y) s₀.nonvanishingLocus s₁.nonvanishingLocus c)
      (resVU (unitModule Y) s₀.nonvanishingLocus s₁.nonvanishingLocus c)
      (smulLin (unitModule Y) c
        ((transition s₀ s₁ ^ (k : ℤ) : Γ(Y, s₀.nonvanishingLocus ⊓ s₁.nonvanishingLocus)ˣ) :
          Γ(Y, s₀.nonvanishingLocus ⊓ s₁.nonvanishingLocus)))) := E.symm.injective.subsingleton
  have hw : (w : sectionsModuleCat (unitModule Y) c
      (s₀.nonvanishingLocus ⊓ s₁.nonvanishingLocus) le_top) ∈ LinearMap.range
      (twistDiff (resUV (unitModule Y) s₀.nonvanishingLocus s₁.nonvanishingLocus c)
        (resVU (unitModule Y) s₀.nonvanishingLocus s₁.nonvanishingLocus c)
        (smulLin (unitModule Y) c
          ((transition s₀ s₁ ^ (k : ℤ) : Γ(Y, s₀.nonvanishingLocus ⊓ s₁.nonvanishingLocus)ˣ) :
            Γ(Y, s₀.nonvanishingLocus ⊓ s₁.nonvanishingLocus)))) :=
    (Submodule.Quotient.mk_eq_zero (R := K)
      (M := sectionsModuleCat (unitModule Y) c
        (s₀.nonvanishingLocus ⊓ s₁.nonvanishingLocus) le_top) _).mp (Subsingleton.elim _ _)
  obtain ⟨⟨a, b⟩, hab⟩ := hw
  refine ⟨-a, b, ?_⟩
  change resR s₀.nonvanishingLocus s₁.nonvanishingLocus b -
    ((transition s₀ s₁ ^ (k : ℤ) : Γ(Y, s₀.nonvanishingLocus ⊓ s₁.nonvanishingLocus)ˣ) :
      Γ(Y, s₀.nonvanishingLocus ⊓ s₁.nonvanishingLocus)) *
        resL s₀.nonvanishingLocus s₁.nonvanishingLocus a = w at hab
  simpa only [zpow_natCast, Units.val_pow_eq_pow_val, map_neg, mul_neg, sub_eq_add_neg] using hab.symm

end DeJongAlterations.StableModificationBridge.TwoSectionScalarVanishing
