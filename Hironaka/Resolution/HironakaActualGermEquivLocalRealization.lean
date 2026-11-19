import Hironaka.Resolution.HironakaActualTaylorCoordinateNaturality
import Hironaka.Resolution.HironakaActualNormalZeroAnalyticSaturation

/-! A whole analytic germ algebra equivalence is realized on a genuine common
local holomorphic chart. Its coordinate representatives and inverse are
constructed internally; no analytic map or inverse realization is assumed. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualGermEquivLocalRealization
noncomputable section
open HolGerm HironakaHolomorphicJetMonomialSpan
 HironakaHolomorphicJetChartInvariance HironakaActualTaylorCoordinateNaturality
 HironakaActualCoefficientPresentationCentrePower HironakaActualFormalCoordinatePowerDivision
 HironakaActualNormalZeroAnalyticSaturation HironakaActualOriginalFormalHSTransfer
 HironakaActualAnalyticFormalNormalPowers
variable {n : ℕ}

private theorem exists_coordinate_map (c : Fin n → HolGerm (ComplexModel n))
    (hc : ∀i,HolGerm.eval (c i)=0) :
    ∃η : ComplexModel n → ComplexModel n,
    ∃hη : ∀ᶠ z in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ η z,
    ∃hη0 : η 0=0,∀i,compAlgHom η hη hη0 (coordinateGerm i)=c i := by
  choose H hH hG using fun i=>HolGerm.exists_eq_mk (c i)
  let η : ComplexModel n → ComplexModel n:=
    fun z=>(EuclideanSpace.equiv (𝕜:=ℂ) (ι:=Fin n)).symm (fun i=>H i z)
  have hη : ∀ᶠ z in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ η z := by
    filter_upwards [eventually_all.mpr hH] with z hz
    exact (EuclideanSpace.equiv (𝕜:=ℂ) (ι:=Fin n)).symm.differentiableAt.comp z
      (differentiableAt_pi.mpr hz)
  have hη0 : η 0=0 := by
    ext i
    change H i 0=0
    have h:=congrArg HolGerm.eval (hG i)
    simpa only [HolGerm.eval_mk,hc i] using h.symm
  refine ⟨η,hη,hη0,?_⟩
  intro i
  have heq : compAlgHom η hη hη0 (coordinateGerm i)=HolGerm.mk (H i) (hH i) := by
    unfold coordinateGerm
    rw [compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z=>rfl
  exact heq.trans (hG i).symm

private theorem equiv_coordinate_mem_maximal
    (E : HolGerm (ComplexModel n)≃ₐ[ℂ]HolGerm (ComplexModel n)) (i : Fin n) :
    E (coordinateGerm i)∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) := by
  have hi : coordinateGerm i∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) :=
    (HolGerm.mem_maximalIdeal_iff _).mpr rfl
  have h:=Ideal.mem_map_of_mem E.toRingEquiv.toRingHom hi
  have hMap : Ideal.map E.toRingEquiv.toRingHom (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)))=
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) := IsLocalRing.map_ringEquiv_maximalIdeal E.toRingEquiv
  rw [hMap] at h
  exact h

/-- The ENTIRE abstract analytic germ equivalence is an actual holomorphic
pullback fixing zero, constructed from finite genuine coordinate germs. -/
theorem exists_actual_holomorphic_pullback_of_germ_equiv
    (E : HolGerm (ComplexModel n)≃ₐ[ℂ]HolGerm (ComplexModel n)) :
    ∃η : ComplexModel n → ComplexModel n,
    ∃hη : ∀ᶠ z in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ η z,
    ∃hη0 : η 0=0,compAlgHom η hη hη0=E.toAlgHom := by
  have heval (i : Fin n) : HolGerm.eval (E (coordinateGerm i))=0 :=
    (HolGerm.mem_maximalIdeal_iff _).mp (equiv_coordinate_mem_maximal E i)
  obtain ⟨η,hη,hη0,hCoord⟩:=exists_coordinate_map (fun i=>E (coordinateGerm i)) heval
  have hT : (actualUnshiftedTaylorAlgHom n).comp (compAlgHom η hη hη0)=
      (actualUnshiftedTaylorAlgHom n).comp E.toAlgHom := by
    apply actualGermAlgHom_eq_of_coordinate_images
    · intro i
      change actualUnshiftedTaylorAlgHom n (compAlgHom η hη hη0 (coordinateGerm i))=
        actualUnshiftedTaylorAlgHom n (E (coordinateGerm i))
      rw [hCoord]
    · intro i
      change actualUnshiftedTaylorAlgHom n (compAlgHom η hη hη0 (coordinateGerm i))∈_
      rw [hCoord]
      have h:=Ideal.mem_map_of_mem (actualUnshiftedTaylorAlgHom n).toRingHom
        (equiv_coordinate_mem_maximal E i)
      have hMax : Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom
          (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)))=actualFormalCoordinateIdeal n univ := by
        simpa only [pow_one,actualFormalCoordinateIdeal,Set.image_univ,genuineFormalVariables] using
          map_actualUnshifted_maximal_pow n 1
      rwa [hMax] at h
  refine ⟨η,hη,hη0,?_⟩
  apply AlgHom.ext
  intro g
  apply actualUnshiftedTaylorAlgHom_injective n
  exact DFunLike.congr_fun hT g

private theorem eventual_inverse_of_pullbacks
    (η ξ : ComplexModel n → ComplexModel n)
    (hη : ∀ᶠ z in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ η z) (hη0 : η 0=0)
    (hξ : ∀ᶠ z in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ ξ z) (hξ0 : ξ 0=0)
    (hInv : ∀g,compAlgHom η hη hη0 (compAlgHom ξ hξ hξ0 g)=g) :
    ∀ᶠz in 𝓝 (0 : ComplexModel n),ξ (η z)=z := by
  have hCoord (i : Fin n) : ∀ᶠz in 𝓝 (0 : ComplexModel n),(ξ (η z)) i=z i := by
    have h:=hInv (coordinateGerm i)
    unfold coordinateGerm at h
    rw [compAlgHom_mk,compAlgHom_mk] at h
    exact HolGerm.mk_eq_mk_iff.mp h
  filter_upwards [eventually_all.mpr hCoord] with z hz
  ext i
  exact hz i

private theorem injective_derivative_of_eventual_inverse
    (η ξ : ComplexModel n → ComplexModel n)
    (hη : ∀ᶠ z in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ η z) (hη0 : η 0=0)
    (hξ : ∀ᶠ z in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ ξ z)
    (hInv : ∀ᶠz in 𝓝 (0 : ComplexModel n),ξ (η z)=z) :
    Function.Injective (fderiv ℂ η 0) := by
  have hηd : DifferentiableAt ℂ η 0:=hη.self_of_nhds
  have hξd : DifferentiableAt ℂ ξ (η 0):=by simpa only [hη0] using hξ.self_of_nhds
  have hcomp : (fderiv ℂ ξ 0).comp (fderiv ℂ η 0)=ContinuousLinearMap.id ℂ (ComplexModel n) := by
    have hEq : (ξ ∘ η)=ᶠ[𝓝 (0 : ComplexModel n)] id:=hInv
    have h:=Filter.EventuallyEq.fderiv_eq (𝕜:=ℂ) hEq
    rw [fderiv_comp 0 hξd hηd,fderiv_id] at h
    simpa only [hη0] using h
  have hLeft : Function.LeftInverse (fderiv ℂ ξ 0) (fderiv ℂ η 0) := by
    intro z
    exact congrArg (fun L=>L z) hcomp
  exact hLeft.injective

/-- A genuine common local holomorphic coordinate equivalence realizes the
ENTIRE supplied analytic germ algebra equivalence. Its actual local inverse
is internally constructed; no holomorphic inverse or domain certificate is
an input. -/
theorem exists_localHolomorphicEquivAt_of_germ_equiv
    (E : HolGerm (ComplexModel n)≃ₐ[ℂ]HolGerm (ComplexModel n)) :
    ∃Φ : LocalHolomorphicEquivAt (n:=n) (0 : ComplexModel n),
    ∃hΦ0 : Φ.toFun 0=0,localGermAlgEquiv Φ hΦ0=E := by
  obtain ⟨η,hη,hη0,hE⟩:=exists_actual_holomorphic_pullback_of_germ_equiv E
  obtain ⟨ξ,hξ,hξ0,hInvE⟩:=exists_actual_holomorphic_pullback_of_germ_equiv E.symm
  have hInv : ∀g,compAlgHom η hη hη0 (compAlgHom ξ hξ hξ0 g)=g := by
    intro g
    rw [hE,hInvE]
    exact E.apply_symm_apply g
  have hNear:=eventual_inverse_of_pullbacks η ξ hη hη0 hξ hξ0 hInv
  have hinj:=injective_derivative_of_eventual_inverse η ξ hη hη0 hξ hNear
  obtain ⟨U,hU,hUo,h0U⟩:=mem_nhds_iff.mp hη
  have hηU : DifferentiableOn ℂ η U:=fun z hz=>(hU hz).differentiableWithinAt
  obtain ⟨Φ,_hΦsrc,hΦFun,_hΦinj⟩:=exists_localHolomorphicEquivAt hUo h0U hηU hinj
  have hΦ0 : Φ.toFun 0=0:=by rw [hΦFun,hη0]
  refine ⟨Φ,hΦ0,?_⟩
  apply AlgEquiv.ext
  intro g
  obtain ⟨F,hF,rfl⟩:=HolGerm.exists_eq_mk g
  have hcomp : compAlgHom η hη hη0 (HolGerm.mk F hF)=E (HolGerm.mk F hF) :=
    DFunLike.congr_fun hE _
  rw [compAlgHom_mk] at hcomp
  rw [localGermAlgEquiv_mk]
  apply Eq.trans ?_ hcomp
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z=>congrArg F (congrFun hΦFun z)

end
end Hironaka.HironakaActualGermEquivLocalRealization
