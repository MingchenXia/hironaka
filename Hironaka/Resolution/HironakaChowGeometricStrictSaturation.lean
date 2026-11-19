import Hironaka.Resolution.HironakaActualStrictPullbackSaturation
import Hironaka.Blowup.BlowupStrictSubmanifold

/-!
# Whole saturation for the actual centre-relative geometric strict transform

The literal inverse image of the coordinate-plane centre is the pivot zero
hyperplane in every positive normal dimension. The centre-relative geometric
closure therefore has its entire original ideal equal to the exceptional
saturation of the entire original pullback ideal, including normal dimension
one and deletion of centre-supported components. The differential exceptional
locus, regularity of the raw pullback quotient, and a supplied saturation
identity play no role. The existing inverse-chart and coherent-power engines
are reused without additional mathematical credit.

Blueprint: `hironaka-g10-geometric-strict-saturation.tex`.
-/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaChowGeometricStrictSaturation
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
  BlowupStrictSubmanifold HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetChartInvariance
  HironakaRelativeNormalDeformationInitialRelations HironakaActualPointGeometricBennett
  HironakaActualPointExceptionalVanishing HironakaActualAnalyticBlowupTaylor
  HironakaActualCoefficientPresentationCentrePower HironakaActualStrictExceptionalRegularity
  HironakaActualStrictPullbackSaturation

/-- The actual coordinate-plane centre pulls back to the pivot hyperplane, including normal dimension one. -/
theorem preimage_tangent_centre_eq_pivot_zero (d t : ℕ) (j : Fin t)
    (b : Fin (d+t) → ℂ) :
    (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) ⁻¹'
      complexCoordinatePlane (d+t) d = {z : ComplexModel (d+t) | z (j.natAdd d)=0} := by
  have he : j.natAdd d∈actualTangentCentreVariables d t := ⟨j,rfl⟩
  ext z
  change (∀ i : Fin (d+t), d ≤ i.val →
    actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b z i=0) ↔ z (j.natAdd d)=0
  constructor
  · intro hz
    have hp := hz (j.natAdd d) (by simp)
    simpa only [actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate,if_pos he,ite_true] using hp
  · intro hz i hi
    have hiA : i∈actualTangentCentreVariables d t := by
      refine ⟨⟨i.val-d,by omega⟩,?_⟩
      apply Fin.ext
      simp only [Fin.val_natAdd]
      omega
    rw [actualAnalyticBlowupMap_apply]
    unfold actualAnalyticBlowupCoordinate
    simp only [if_pos hiA]
    split_ifs
    · exact hz
    · rw [hz,zero_mul]

/-- The actual geometric strict transform uses the centre complement in every normal dimension. -/
theorem geoStrictTransform_eq_closure_off_pivot (d t : ℕ) (j : Fin t)
    (b : Fin (d+t) → ℂ) (W : Set (ComplexModel (d+t))) :
    geoStrictTransform (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b)
      (complexCoordinatePlane (d+t) d) W =
    closure ((actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) ⁻¹' W \
      {z : ComplexModel (d+t) | z (j.natAdd d)=0}) := by
  unfold geoStrictTransform
  rw [preimage_sdiff,preimage_tangent_centre_eq_pivot_zero]

/-- Every pivot power cancels in the entire actual geometric-closure vanishing ideal. -/
theorem coordinate_pow_mul_mem_geoStrict_ideal_iff (d t : ℕ) (j : Fin t)
    (b : Fin (d+t) → ℂ) (W : Set (ComplexModel (d+t)))
    (q : ℕ) (g : HolGerm (ComplexModel (d+t))) :
    (coordinateGerm (j.natAdd d))^q*g∈originalCoherentOriginIdeal (vanishingIdeal (n := d+t)
      (geoStrictTransform (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b)
        (complexCoordinatePlane (d+t) d) W)) ↔
    g∈originalCoherentOriginIdeal (vanishingIdeal (n := d+t)
      (geoStrictTransform (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b)
        (complexCoordinatePlane (d+t) d) W)) := by
  rw [geoStrictTransform_eq_closure_off_pivot]
  exact coordinate_pow_mul_mem_closure_ideal_iff _ _ (fun _ hz => hz.2) q g

private theorem contMDiff_blowup {n : ℕ} (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (actualAnalyticBlowupMap A e b) := by
  have hp (i : Fin n) : ContDiff ℂ ∞ (fun z : ComplexModel n => z i) :=
    (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).contDiff
  have hc (i : Fin n) : ContDiff ℂ ∞ (actualAnalyticBlowupCoordinate A e b i) := by
    unfold actualAnalyticBlowupCoordinate
    split_ifs
    · exact hp e
    · exact (hp e).mul ((contDiff_const (c := b i)).add (hp i))
    · exact hp i
  exact ((EuclideanSpace.equiv (Fin n) ℂ).symm.contDiff.comp (contDiff_pi.mpr hc)).contMDiff

/-- Original analytic geometry derives the ENTIRE centre-relative geometric strict ideal as saturation of the WHOLE pullback. -/
theorem mem_geoStrict_ideal_iff_exists_coordinate_power
    (d t : ℕ) (j : Fin t) (b : Fin (d+t) → ℂ)
    (W : Set (ComplexModel (d+t))) (hW : IsComplexAnalyticSubset (n := d+t) W)
    (g : HolGerm (ComplexModel (d+t))) :
    g∈originalCoherentOriginIdeal (vanishingIdeal (n := d+t)
      (geoStrictTransform (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b)
        (complexCoordinatePlane (d+t) d) W)) ↔
      ∃ N : ℕ,(coordinateGerm (j.natAdd d))^N*g∈
        Ideal.map (actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b).toRingHom
          (originalCoherentOriginIdeal (vanishingIdeal (n := d+t) W)) := by
  let A := actualTangentCentreVariables d t
  let e := j.natAdd d
  let π := actualAnalyticBlowupMap A e b
  let C := complexCoordinatePlane (d+t) d
  let I := vanishingIdeal (n := d+t) W
  let J := GermIdeal.pullback (m := d+t) π I
  have hI : I.IsCoherent := CartanIrreducible.cartanCoherence W hW
  have hπ := contMDiff_blowup A e b
  have hπ0 : π 0=0 := actualAnalyticBlowupMap_zero A e b
  have hJ : J.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback hπ hI
  have hmap : originalCoherentOriginIdeal J=
      Ideal.map (actualAnalyticBlowupPullback A e b).toRingHom (originalCoherentOriginIdeal I) := by
    exact originalOriginIdeal_holomorphic_pullback_eq π hπ hπ0 I hI
  have hπnear : ∀ᶠ z in 𝓝 (0 : ComplexModel (d+t)),DifferentiableAt ℂ π z :=
    Eventually.of_forall fun _ => (differentiable_actualAnalyticBlowupMap A e b).differentiableAt
  have htπ : Tendsto π (𝓝 (0 : ComplexModel (d+t))) (𝓝 (0 : ComplexModel (d+t))) := by
    have h : Tendsto π (𝓝 (0 : ComplexModel (d+t))) (𝓝 (π 0)) := hπ.continuous.tendsto 0
    rwa [hπ0] at h
  constructor
  · intro hg
    obtain ⟨G,hG,rfl⟩ := HolGerm.exists_eq_mk g
    have hzero := (mk_mem_original_vanishing_origin_ideal_iff _ G hG).mp hg
    obtain ⟨U,hUprop,hU,h0U⟩ := eventually_nhds_iff.mp (hG.and hzero)
    have hOff : ∀ᶠ y in 𝓝 (0 : ComplexModel (d+t)),y e≠0→J.mem y G := by
      filter_upwards [hU.mem_nhds h0U] with y hy hye
      apply (pullback_vanishingIdeal_mem_iff_off_coordinate A e b W y hye G).mpr
      have hGU : DifferentiableOn ℂ G U := fun z hz => (hUprop z hz).1.differentiableWithinAt
      refine ⟨(holAt_of_differentiableOn hU hGU hy).mono (fun _ h => h.mdifferentiableAt),?_⟩
      filter_upwards [hU.mem_nhds hy,
        (EuclideanSpace.proj e : ComplexModel (d+t) →L[ℂ] ℂ).continuous.continuousAt.eventually_ne hye]
        with z hz hze hzW
      apply (hUprop z hz).2
      rw [geoStrictTransform_eq_closure_off_pivot]
      exact subset_closure ⟨hzW,hze⟩
    obtain ⟨N,hN⟩ := exists_coordinate_power_mul_mem_of_off_divisor_membership J hJ G hG e hOff
    exact ⟨N,by rwa [hmap] at hN⟩
  · rintro ⟨N,hN⟩
    apply (coordinate_pow_mul_mem_geoStrict_ideal_iff d t j b W N g).mp
    have hle : Ideal.map (actualAnalyticBlowupPullback A e b).toRingHom (originalCoherentOriginIdeal I)≤
        originalCoherentOriginIdeal (vanishingIdeal (n := d+t) (geoStrictTransform π C W)) := by
      apply Ideal.map_le_iff_le_comap.mpr
      apply Ideal.span_le.mpr
      rintro _ ⟨F,hF,hFW,rfl⟩
      change actualAnalyticBlowupPullback A e b (HolGerm.mk F hF)∈
        originalCoherentOriginIdeal (vanishingIdeal (n := d+t) (geoStrictTransform π C W))
      rw [actualAnalyticBlowupPullback,compAlgHom_mk]
      apply (mk_mem_original_vanishing_origin_ideal_iff _ (F∘π) _).mpr
      apply eventually_zero_on_closure_of_eventually_continuous (F∘π)
        (π ⁻¹' (W\C))
        ((holomorphic_comp π hπnear hπ0 hF).mono fun _ h => h.continuousAt)
      filter_upwards [htπ.eventually hFW.2] with z hz hzS
      exact hz hzS.1
    exact hle hN

end
end Hironaka.HironakaChowGeometricStrictSaturation
