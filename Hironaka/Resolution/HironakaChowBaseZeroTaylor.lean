import Hironaka.Resolution.HironakaActualFormalNormalSeries
import Hironaka.Resolution.HironakaActualJointBaseFibre

/-! The literal ORIGINAL base-zero analytic trace retains EVERY same normal
Taylor coefficient. Direct next consumer: actual fibre complement in I
has zero trace, hence lies in actual base-maximal-ideal times N. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology
namespace Hironaka.HironakaChowBaseZeroTaylor
noncomputable section
open HolGerm HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetChartInvariance
  HironakaActualJointBaseFibre HironakaActualCentreJointJets
  HironakaActualFormalNormalSeries HironakaActualCoefficientPresentationCentrePower
  HironakaActualRelativeTaylorCoefficients HironakaActualRelativeCoefficientGerms
  HironakaActualTaylorCoordinateNaturality HironakaActualFormalCoordinatePowerDivision

private def baseConstantCoeff (d : ℕ) : MvPowerSeries (Fin d) ℂ →ₐ[ℂ] ℂ where
  toRingHom := MvPowerSeries.constantCoeff
  commutes' a := by
    change MvPowerSeries.constantCoeff (MvPowerSeries.C a) = a
    exact MvPowerSeries.constantCoeff_C a

private def formalBaseZeroTrace (d t : ℕ) :
    MvPowerSeries (Fin (d+t)) ℂ →ₐ[ℂ] MvPowerSeries (Fin t) ℂ :=
  (MvPowerSeries.mapAlgHom (σ := Fin t) (baseConstantCoeff d)).comp
    (formalNormalSeriesEquiv d t).toAlgHom

private theorem formalBaseZeroTrace_coeff (d t : ℕ)
    (F : MvPowerSeries (Fin (d+t)) ℂ) (γ : Fin t →₀ ℕ) :
    MvPowerSeries.coeff γ (formalBaseZeroTrace d t F) =
      MvPowerSeries.coeff (actualJoinedExponent (0 : Fin d →₀ ℕ) γ) F := rfl

private theorem formalBaseZeroTrace_X_base (d t : ℕ) (i : Fin d) :
    formalBaseZeroTrace d t (MvPowerSeries.X (i.castAdd t)) = 0 := by
  ext γ
  rw [formalBaseZeroTrace_coeff,MvPowerSeries.coeff_X,map_zero]
  have hn : actualJoinedExponent (0 : Fin d →₀ ℕ) γ ≠ Finsupp.single (i.castAdd t) 1 := by
    intro he
    have hv := congrArg (fun α : Fin (d+t) →₀ ℕ => α (i.castAdd t)) he
    simp [actualJoinedExponent] at hv
  exact if_neg hn

private theorem formalBaseZeroTrace_X_normal (d t : ℕ) (i : Fin t) :
    formalBaseZeroTrace d t (MvPowerSeries.X (i.natAdd d)) = MvPowerSeries.X i := by
  ext γ
  rw [formalBaseZeroTrace_coeff,MvPowerSeries.coeff_X,MvPowerSeries.coeff_X,
    actualJoinedExponent_normal_embedding]
  change (if Finsupp.embDomain (actualNormalFormalEmbedding d t) γ =
    Finsupp.single ((actualNormalFormalEmbedding d t) i) 1 then (1 : ℂ) else 0) = _
  rw [← Finsupp.embDomain_single]
  simp only [(Finsupp.embDomain_injective (actualNormalFormalEmbedding d t)).eq_iff]

private theorem trace_coordinate_base (d t : ℕ) (i : Fin d) :
    jointBaseZeroTrace d t (coordinateGerm (i.castAdd t)) = 0 := by
  unfold jointBaseZeroTrace coordinateGerm
  rw [compAlgHom_mk]
  change HolGerm.mk _ _ = HolGerm.mk (fun _ : ComplexModel t => (0 : ℂ))
    (eventually_differentiableAt_const 0)
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z => actualJointNormalInclusion_tangent d t z i

private theorem trace_coordinate_normal (d t : ℕ) (i : Fin t) :
    jointBaseZeroTrace d t (coordinateGerm (i.natAdd d)) = coordinateGerm i := by
  unfold jointBaseZeroTrace coordinateGerm
  rw [compAlgHom_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z => actualJointNormalInclusion_normal d t z i

/-- WHOLE literal Taylor identity for the actual ORIGINAL analytic trace. -/
theorem taylor_jointBaseZeroTrace (d t : ℕ) (f : HolGerm (ComplexModel (d+t))) :
    actualUnshiftedTaylorAlgHom t (jointBaseZeroTrace d t f) =
      formalBaseZeroTrace d t (actualUnshiftedTaylorAlgHom (d+t) f) := by
  have he : (actualUnshiftedTaylorAlgHom t).comp (jointBaseZeroTrace d t) =
      (formalBaseZeroTrace d t).comp (actualUnshiftedTaylorAlgHom (d+t)) := by
    apply actualGermAlgHom_eq_of_coordinate_images
    · intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · change actualUnshiftedTaylorAlgHom t (jointBaseZeroTrace d t (coordinateGerm (j.castAdd t))) =
          formalBaseZeroTrace d t (actualUnshiftedTaylorAlgHom (d+t) (coordinateGerm (j.castAdd t)))
        rw [trace_coordinate_base,map_zero,actualUnshiftedTaylor_coordinate,formalBaseZeroTrace_X_base]
      · change actualUnshiftedTaylorAlgHom t (jointBaseZeroTrace d t (coordinateGerm (j.natAdd d))) =
          formalBaseZeroTrace d t (actualUnshiftedTaylorAlgHom (d+t) (coordinateGerm (j.natAdd d)))
        rw [trace_coordinate_normal,actualUnshiftedTaylor_coordinate,actualUnshiftedTaylor_coordinate,
          formalBaseZeroTrace_X_normal]
    · intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · change actualUnshiftedTaylorAlgHom t (jointBaseZeroTrace d t (coordinateGerm (j.castAdd t))) ∈ _
        rw [trace_coordinate_base,map_zero]
        exact Ideal.zero_mem _
      · change actualUnshiftedTaylorAlgHom t (jointBaseZeroTrace d t (coordinateGerm (j.natAdd d))) ∈ _
        rw [trace_coordinate_normal,actualUnshiftedTaylor_coordinate]
        exact Ideal.subset_span ⟨j,mem_univ _,rfl⟩
  exact congrArg (fun h : HolGerm (ComplexModel (d+t)) →ₐ[ℂ] MvPowerSeries (Fin t) ℂ => h f) he

/-- EVERY actual normal coefficient is the SAME original joined zero-base coefficient. -/
theorem coeff_taylor_jointBaseZeroTrace (d t : ℕ) (f : HolGerm (ComplexModel (d+t)))
    (γ : Fin t →₀ ℕ) :
    MvPowerSeries.coeff γ (actualUnshiftedTaylorAlgHom t (jointBaseZeroTrace d t f)) =
      MvPowerSeries.coeff (actualJoinedExponent (0 : Fin d →₀ ℕ) γ)
        (actualUnshiftedTaylorAlgHom (d+t) f) := by
  rw [taylor_jointBaseZeroTrace,formalBaseZeroTrace_coeff]

end
end Hironaka.HironakaChowBaseZeroTaylor
