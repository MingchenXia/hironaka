import Hironaka.Analytic.Unibranch.HironakaG10LocalIntrinsicIdeal
import Hironaka.Analytic.Unibranch.HironakaG10LocalStratumClosure
import Hironaka.Resolution.HironakaG10FiniteIdealFamilyArithmetic
import Hironaka.Resolution.HironakaG10GlobalSumIdealModule

/-! # Global extension of a powered reduced boundary-support ideal -/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG10SchemeBoundaryThickening

open Hironaka HironakaG10HirIdealGerms
  HironakaG10GlobalSumIdealModule HironakaG10FiniteIdealFamilyArithmetic HironakaSingularModuleSheafStalk
  HironakaIntrinsicReducedCentreOpenPullback
open Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10LocallyAnalyticTrace
  Hironaka.Analytic.Unibranch.HironakaG10LocallyAnalyticBoundary
  Hironaka.Analytic.Unibranch.HironakaG10LocalStratumClosure
  Hironaka.Analytic.Unibranch.HironakaG10LocalBoundaryGlobalCut
  Hironaka.Analytic.Unibranch.HironakaG10LocalIntrinsicIdeal
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
  Hironaka.Analytic.Unibranch.HironakaG10AnalyticStratumBoundary
  Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus

noncomputable section

/-- The source closure preceding the scheme-theoretic intersection is
  locally analytic on the flattener domain. -/
theorem closure_locallyAnalytic {X Y : SourceReducedComplexSpace}
    (f : Y ⟶ X) (B : Set X.obj.left) (Z : LocalFlattener f) (i : ℕ)
    (hS : IsLocallyAnalyticOn X Z.V (strata f B (i + 1))) :
    IsLocallyAnalyticOn X Z.V (closure ((strata f B (i + 1) ∩ Z.V) \ Z.support)) := by
  intro x hx
  obtain ⟨e,he,_,A,hA,htrace⟩ := locallyAnalytic_stratumClosure f B Z i hS x hx
  exact ⟨e,he,A,hA,htrace⟩

/-- Hironaka's scheme-theoretic ideal `I_G + I_Z + I_C^ω` glues to an actual
  global finite-type ideal with nonunit locus the exact compact boundary cut. -/
theorem exists_scheme_boundary_thickening {X Y : SourceReducedComplexSpace}
    [CompactSpace X.obj.left] (f : Y ⟶ X) (B C : Set X.obj.left)
    (Z : LocalFlattener f) (i ω : ℕ) (hω : ω ≠ 0)
    (hS : IsLocallyAnalyticOn X Z.V (strata f B (i + 1)))
    (hC : IsLocallyAnalyticOn X Z.V C) (hCclosed : IsClosed C) (hCV : C ⊆ Z.V) :
    let G := closure ((strata f B (i + 1) ∩ Z.V) \ Z.support)
    let E := stratumBoundary f B Z.V Z.support i
    let Q := C ∩ E
    ∃ (D : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
      (d : D ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf)),
      D.IsFiniteType ∧ nonunitLocus D d = Q ∧
      (∀ x ∈ Z.V, LinearMap.range
        (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf D d x) =
          (intrinsicCentreStalkRange X.obj.left C x) ^ ω ⊔
            (intrinsicCentreStalkRange X.obj.left G x ⊔ Z.H x)) ∧
      (∀ x ∉ Q, LinearMap.range
        (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf D d x) = ⊤) := by
  let G := closure ((strata f B (i + 1) ∩ Z.V) \ Z.support)
  let E := stratumBoundary f B Z.V Z.support i
  let Q := C ∩ E
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
  have hQ : X.IsAnalyticSubset Q := analytic_global_cut_of_local_data f B C Z i hS hC hCclosed hCV
  have hQV : Q ⊆ Z.V := fun _ hx => hCV hx.1
  have htop : ∀ x ∈ Z.V, x ∉ Q → IC x ^ ω ⊔ IE x = ⊤ := by
    intro x hxV hxQ
    change (intrinsicCentreStalkRange X.obj.left C x) ^ ω ⊔
      (intrinsicCentreStalkRange X.obj.left G x ⊔ Z.H x) = ⊤
    by_cases hxC : x ∈ C
    · by_cases hxG : x ∈ G
      · have hxH : Z.H x = ⊤ := by
          by_contra hH
          exact hxQ ⟨hxC,hxG,⟨hxV,hH⟩⟩
        rw [hxH, sup_top_eq, sup_top_eq]
      · rw [intrinsicCentreStalkRange_eq_top_of_not_mem X Z.V G Z.isOpen hG x hxV hxG,
          top_sup_eq, sup_top_eq]
    · rw [intrinsicCentreStalkRange_eq_top_of_not_mem X Z.V C Z.isOpen hC x hxV hxC,
        Ideal.top_pow, top_sup_eq]
  obtain ⟨D,d,hfinite,hstalk,houtside⟩ := exists_global_sum_ideal_module
    X.obj.left Z.V Q Z.isOpen hQ.isClosed hQV IC IE hIC hIE ω htop
  have hDQ : nonunitLocus D d ⊆ Q := by
    intro x hx
    by_contra hxQ
    exact hx (houtside x hxQ)
  have hQD : Q ⊆ nonunitLocus D d := by
    intro x hxQ hunit
    have hle : IC x ^ ω ⊔ IE x ≤ IsLocalRing.maximalIdeal (X.obj.left.presheaf.stalk x) :=
      sup_le ((Ideal.pow_le_self hω).trans (intrinsicCentreStalkRange_le_maximalIdeal _ _ _ hxQ.1))
        (sup_le (intrinsicCentreStalkRange_le_maximalIdeal _ _ _ hxQ.2.1)
          (IsLocalRing.le_maximalIdeal hxQ.2.2.2))
    rw [← hstalk x (hQV hxQ), hunit] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal (X.obj.left.presheaf.stalk x)).ne_top
      (top_le_iff.mp hle)
  exact ⟨D,d,hfinite,Set.Subset.antisymm hDQ hQD,hstalk,houtside⟩

end
end Hironaka.Analytic.Unibranch.HironakaG10SchemeBoundaryThickening
