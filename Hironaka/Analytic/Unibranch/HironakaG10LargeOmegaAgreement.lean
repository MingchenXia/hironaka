import Hironaka.Analytic.Unibranch.HironakaG10SchemeBoundaryThickening
import Hironaka.Analytic.Unibranch.HironakaG10UniformRadicalPower

/-! # A large power preserves the actual scheme boundary near a compact set -/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG10LargeOmegaAgreement

open Hironaka HironakaG10HirIdealGerms
  HironakaG10FiniteIdealFamilyArithmetic HironakaSingularModuleSheafStalk
  HironakaIntrinsicReducedCentreOpenPullback
open Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10LocallyAnalyticTrace
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
  Hironaka.Analytic.Unibranch.HironakaG10AnalyticStratumBoundary
  Hironaka.Analytic.Unibranch.HironakaG10LocalIntrinsicIdeal
  Hironaka.Analytic.Unibranch.HironakaG10SchemeBoundaryThickening
  Hironaka.Analytic.Unibranch.HironakaG10UniformRadicalPower
  Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus

noncomputable section

/-- Once the actual local radical containment has been established on a
  compact set, one large power makes the global thickening agree with the
  original scheme-theoretic boundary on an entire neighborhood. -/
theorem exists_large_omega_agreement {X Y : SourceReducedComplexSpace}
    [CompactSpace X.obj.left] (f : Y ⟶ X) (B C : Set X.obj.left)
    (Z : LocalFlattener f) (i : ℕ)
    (hS : IsLocallyAnalyticOn X Z.V (strata f B (i + 1)))
    (hC : IsLocallyAnalyticOn X Z.V C) (hCclosed : IsClosed C) (hCV : C ⊆ Z.V)
    (K : Set X.obj.left) (hK : IsCompact K) (hKV : K ⊆ Z.V)
    (hrad : ∀ x ∈ K, intrinsicCentreStalkRange X.obj.left C x ≤
      (intrinsicCentreStalkRange X.obj.left
        (closure ((strata f B (i + 1) ∩ Z.V) \ Z.support)) x ⊔ Z.H x).radical) :
    ∃ (W : Set X.obj.left) (N : ℕ), IsOpen W ∧ K ⊆ W ∧ W ⊆ Z.V ∧
      ∀ ω ≥ N, ∃ (D : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
        (d : D ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf)),
        D.IsFiniteType ∧ nonunitLocus D d = C ∩ stratumBoundary f B Z.V Z.support i ∧
        ∀ x ∈ W, LinearMap.range
          (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf D d x) =
            intrinsicCentreStalkRange X.obj.left
              (closure ((strata f B (i + 1) ∩ Z.V) \ Z.support)) x ⊔ Z.H x := by
  let G := closure ((strata f B (i + 1) ∩ Z.V) \ Z.support)
  let IC := intrinsicCentreStalkRange X.obj.left C
  let IG := intrinsicCentreStalkRange X.obj.left G
  let IE := fun x => IG x ⊔ Z.H x
  have hG : IsLocallyAnalyticOn X Z.V G := closure_locallyAnalytic f B Z i hS
  have hIC : IsLocallyFinitelyGeneratedOn X.obj.left Z.V IC :=
    local_intrinsicCentreStalkRange_finitelyGenerated X Z.V C hC
  have hIG : IsLocallyFinitelyGeneratedOn X.obj.left Z.V IG :=
    local_intrinsicCentreStalkRange_finitelyGenerated X Z.V G hG
  have hIE : IsLocallyFinitelyGeneratedOn X.obj.left Z.V IE :=
    isLocallyFinitelyGeneratedOn_sup Z.V IG Z.H hIG Z.fg
  obtain ⟨W,N,hW,hKW,hWV,hpower⟩ :=
    exists_uniform_power_on_compact Z.V K Z.isOpen hK hKV IC IE hIC hIE hrad
  refine ⟨W,max N 1,hW,hKW,hWV,fun ω hω => ?_⟩
  have hωN : N ≤ ω := (le_max_left N 1).trans hω
  have hω0 : ω ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one ((le_max_right N 1).trans hω))
  obtain ⟨D,d,hfinite,hQ,hstalk,_⟩ := exists_scheme_boundary_thickening f B C Z i ω hω0 hS hC hCclosed hCV
  refine ⟨D,d,hfinite,hQ,fun x hx => ?_⟩
  rw [hstalk x (hWV hx)]
  exact sup_eq_right.mpr (hpower x hx ω hωN)

end
end Hironaka.Analytic.Unibranch.HironakaG10LargeOmegaAgreement
