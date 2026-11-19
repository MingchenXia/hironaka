import Hironaka.Resolution.HironakaG10ArtinianParameterPullback
set_option autoImplicit false
namespace Hironaka.HironakaG10ArtinianNormalIdeal
open HolGerm HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetChartInvariance
  HironakaRelativeNormalIdeal HironakaActualCentreJointJets HironakaActualJointBaseFibre
  HironakaG10ArtinianParameterPullback
noncomputable section

/-- Every normal coordinate is the actual pullback of its corresponding
parameter coordinate. -/
theorem jointNormalPullback_coordinate' (t d : ℕ) (i : Fin d) :
    jointNormalPullback t d (coordinateGerm i) = normalCoordinate t d i := by
  unfold jointNormalPullback coordinateGerm normalCoordinate
  rw [compAlgHom_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Filter.Eventually.of_forall fun _ => rfl

/-- The normal ideal is contained in the extended parameter maximal ideal. -/
theorem normalIdeal_le_parameter_maximal (t d : ℕ) :
    normalIdeal t d ≤ Ideal.map (jointNormalPullback t d).toRingHom
      (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d))) := by
  unfold normalIdeal
  apply Ideal.span_le.mpr
  rintro _ ⟨i,rfl⟩
  rw [← jointNormalPullback_coordinate']
  exact Ideal.mem_map_of_mem _ ((HolGerm.mem_maximalIdeal_iff _).mpr rfl)

/-- A nilpotent parameter kernel contains the full normal-power remainder
in swapped joint coordinates. -/
theorem normalPower_le_swapped_parameter_kernel {Q : Type} [CommRing Q] [Algebra ℂ Q]
    (d t q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom) :
    normalIdeal t d ^ (q+1) ≤
      Ideal.map (swapParameterFibre d t).toRingHom
        (Ideal.map (tangentPullback d t).toRingHom (RingHom.ker φ.toRingHom)) := by
  have hmaps : (jointNormalPullback t d).toRingHom =
      (swapParameterFibre d t).toRingHom.comp (tangentPullback d t).toRingHom := by
    apply RingHom.ext
    intro a
    exact (swapParameterFibre_base d t a).symm
  calc
    normalIdeal t d ^ (q+1) ≤
        (Ideal.map (jointNormalPullback t d).toRingHom
          (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)))) ^ (q+1) :=
      pow_le_pow_left' (normalIdeal_le_parameter_maximal t d) _
    _ = Ideal.map (jointNormalPullback t d).toRingHom
        (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1)) := by
      rw [Ideal.map_pow]
    _ ≤ Ideal.map (jointNormalPullback t d).toRingHom (RingHom.ker φ.toRingHom) :=
      Ideal.map_mono hφ
    _ = _ := by rw [hmaps, Ideal.map_map]
end
end Hironaka.HironakaG10ArtinianNormalIdeal
