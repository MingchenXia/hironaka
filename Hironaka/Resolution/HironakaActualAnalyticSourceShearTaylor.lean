import Hironaka.Resolution.HironakaActualAnalyticDirectionRemovalQuotient
import Hironaka.Resolution.HironakaActualFormalBlowupAllDirections

/-! The actual analytic source shear realizes the SAME complete formal source
shear. This whole-series/whole-ideal dictionary is obtained from the two real
blowup squares and zero-chart injectivity; no analytic realization certificate
is supplied. It is a source-coordinate producer for arbitrary-direction
analytic adaptation, not a whole historical HS-presentation theorem. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualAnalyticSourceShearTaylor
noncomputable section
open HolGerm HironakaActualAnalyticBlowupTaylor
 HironakaActualCoefficientPresentationCentrePower HironakaActualFormalCoordinatePowerDivision
 HironakaActualFormalBlowupMemberGeneration HironakaActualFormalBlowupAllDirections
 HironakaActualFormalMonomialBlowupReflection HironakaActualAnalyticDirectionRemovalQuotient
variable {n : ℕ}

theorem actualTaylor_analytic_source_shear
    (A : Set (Fin n)) (e : Fin n) (he : e∈A) (b : Fin n → ℂ)
    (g : HolGerm (ComplexModel n)) :
    actualUnshiftedTaylorAlgHom n (actualAnalyticDirectionShearGermEquiv A e b g)=
      actualFormalCenterShear A e b (actualUnshiftedTaylorAlgHom n g) := by
  apply actualFormalBlowup_zero_injective A e
  calc
    actualFormalBlowup A e (fun _=>0)
        (actualUnshiftedTaylorAlgHom n (actualAnalyticDirectionShearGermEquiv A e b g))=
        actualUnshiftedTaylorAlgHom n (actualAnalyticBlowupPullback A e (fun _=>0)
          (actualAnalyticDirectionShearGermEquiv A e b g)) :=
      (DFunLike.congr_fun (actualTaylor_analyticBlowupPullback A e (fun _=>0))
        (actualAnalyticDirectionShearGermEquiv A e b g)).symm
    _=actualUnshiftedTaylorAlgHom n (actualAnalyticBlowupPullback A e b g) :=
      congrArg (actualUnshiftedTaylorAlgHom n)
        (actualAnalyticBlowupPullback_direction_shear A e b g).symm
    _=actualFormalBlowup A e b (actualUnshiftedTaylorAlgHom n g) :=
      DFunLike.congr_fun (actualTaylor_analyticBlowupPullback A e b) g
    _=actualFormalBlowup A e (fun _=>0)
        (actualFormalCenterShear A e b (actualUnshiftedTaylorAlgHom n g)) :=
      actualFormalBlowup_eq_zero_comp_centerShear A e he b _

/-- The ENTIRE actual analytic source ideal realizes the independently named
formal shear of the ENTIRE original Taylor ideal. -/
theorem map_actualTaylor_analytic_source_shear
    (A : Set (Fin n)) (e : Fin n) (he : e∈A) (b : Fin n → ℂ)
    (I : Ideal (HolGerm (ComplexModel n))) :
    Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom
      (Ideal.map (actualAnalyticDirectionShearGermEquiv A e b).toRingEquiv.toRingHom I)=
    Ideal.map (actualFormalCenterShear A e b).toRingHom
      (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) := by
  rw [Ideal.map_map,Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro g
  exact actualTaylor_analytic_source_shear A e he b g

end
end Hironaka.HironakaActualAnalyticSourceShearTaylor
