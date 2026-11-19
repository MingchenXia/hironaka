import Hironaka.Resolution.HironakaActualWeightedVertexSmallTails
import Hironaka.Resolution.HironakaActualJointBaseFibre

/-! SAME original fibre generators lift to the ORIGINAL ideal and retain their
genuine normal weights. A larger internally chosen base weight gives actual
analytic tail factors, with no division by the scaling parameter. BP first. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology

namespace Hironaka.HironakaChowFibreLiftWeightedFactors
noncomputable section
open HolGerm HironakaActualJointBaseFibre HironakaActualCentreJointJets
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetMonomialSpan
  HironakaRelativeNormalFibreHilbertSamuel HironakaRelativeNormalIdeal
  HironakaActualWeightedScaling HironakaActualWeightedVertexSmallTails
  HironakaActualFiniteDegLexWeights HironakaActualCoefficientPresentationCentrePower

def extendedWeight (d t L : ℕ) (w : Fin t → ℕ) : Fin (d+t) → ℕ :=
  Fin.addCases (fun _ => L) w

@[simp] theorem extendedWeight_base (d t L : ℕ) (w : Fin t → ℕ) (i : Fin d) :
    extendedWeight d t L w (i.castAdd t) = L := by simp [extendedWeight]

@[simp] theorem extendedWeight_normal (d t L : ℕ) (w : Fin t → ℕ) (i : Fin t) :
    extendedWeight d t L w (i.natAdd d) = w i := by simp [extendedWeight]

private def normalParameterIndex (d t : ℕ) : Fin (t+1) → Fin ((d+t)+1) :=
  Fin.addCases (fun i : Fin t => (i.natAdd d).castAdd 1) (fun _ => parameterIndex (d+t))

private def normalParameterProjection (d t : ℕ) :
    ComplexModel ((d+t)+1) →L[ℂ] ComplexModel (t+1) :=
  (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin (t+1))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => EuclideanSpace.proj (normalParameterIndex d t i))

private theorem normalParameterProjection_base (d t : ℕ)
    (z : ComplexModel ((d+t)+1)) (i : Fin t) :
    normalParameterProjection d t z (i.castAdd 1) = z ((i.natAdd d).castAdd 1) := by
  change z (normalParameterIndex d t (i.castAdd 1)) = _
  simp [normalParameterIndex]

private theorem normalParameterProjection_parameter (d t : ℕ)
    (z : ComplexModel ((d+t)+1)) :
    normalParameterProjection d t z (parameterIndex t) = z (parameterIndex (d+t)) := by
  change z (normalParameterIndex d t (parameterIndex t)) = _
  simp [normalParameterIndex, parameterIndex]

private def normalParameterPullback (d t : ℕ) :
    HolGerm (ComplexModel (t+1)) →ₐ[ℂ] HolGerm (ComplexModel ((d+t)+1)) :=
  compAlgHom (normalParameterProjection d t)
    (Eventually.of_forall fun _ => (normalParameterProjection d t).differentiableAt) (map_zero _)

private theorem normalParameterPullback_coordinate (d t : ℕ) (i : Fin (t+1)) :
    normalParameterPullback d t (coordinateGerm i) = coordinateGerm (normalParameterIndex d t i) := by
  unfold normalParameterPullback coordinateGerm
  rw [compAlgHom_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun _ => rfl

private theorem scaling_normal_comm (d t L : ℕ) (w : Fin t → ℕ)
    (g : HolGerm (ComplexModel t)) :
    actualWeightedScalingPullback (extendedWeight d t L w) (jointNormalPullback d t g) =
      normalParameterPullback d t (actualWeightedScalingPullback w g) := by
  induction g using HolGerm.induction_on with
  | h f hf =>
    unfold actualWeightedScalingPullback jointNormalPullback normalParameterPullback
    rw [compAlgHom_mk, compAlgHom_mk, compAlgHom_mk, compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    apply Eventually.of_forall
    intro z
    apply congrArg f
    ext i
    change z (parameterIndex (d+t)) ^ extendedWeight d t L w (i.natAdd d) *
      z ((i.natAdd d).castAdd 1) =
      normalParameterProjection d t z (parameterIndex t) ^ w i *
        normalParameterProjection d t z (i.castAdd 1)
    rw [extendedWeight_normal, normalParameterProjection_parameter, normalParameterProjection_base]

private theorem pullback_scaled_monomial (d t L : ℕ) (w : Fin t → ℕ)
    (a : Fin t →₀ ℕ) :
    normalParameterPullback d t (actualScaledMonomialGerm w a) =
      actualScaledMonomialGerm (extendedWeight d t L w) (actualJoinedExponent (0 : Fin d →₀ ℕ) a) := by
  rw [actualScaledMonomialGerm, map_prod, actualScaledMonomialGerm, Fin.prod_univ_add]
  simp only [map_pow, map_mul, normalParameterPullback_coordinate]
  simp [normalParameterIndex, parameterIndex, actualJoinedExponent, extendedWeight]

private theorem scaled_lift_difference (d t L : ℕ) (w : Fin t → ℕ)
    (F : HolGerm (ComplexModel (d+t))) (g : HolGerm (ComplexModel t))
    (hTrace : jointBaseZeroTrace d t F = g) :
    ∃ B : HolGerm (ComplexModel ((d+t)+1)),
      actualWeightedScalingPullback (extendedWeight d t L w) F -
        actualWeightedScalingPullback (extendedWeight d t L w) (jointNormalPullback d t g) =
      coordinateGerm (parameterIndex (d+t)) ^ L * B := by
  have hZero : jointBaseZeroTrace d t (F - jointNormalPullback d t g) = 0 := by
    rw [map_sub, hTrace, jointBaseZeroTrace_normalPullback, sub_self]
  have hBase : F - jointNormalPullback d t g ∈ originalBaseMaximalIdeal d t := by
    rw [baseMaximalIdeal_eq_ker_jointBaseZeroTrace]
    exact hZero
  rw [baseMaximalIdeal_eq_tangent_span] at hBase
  obtain ⟨H, hH⟩ := Ideal.mem_span_range_iff_exists_fun.mp hBase
  let σ := actualWeightedScalingPullback (extendedWeight d t L w)
  refine ⟨∑ i : Fin d, σ (H i) * coordinateGerm ((i.castAdd t).castAdd 1), ?_⟩
  change σ F - σ (jointNormalPullback d t g) = _
  dsimp only [σ]
  rw [← map_sub, ← hH, map_sum]
  simp only [map_mul, actualWeightedScalingPullback_coordinate, extendedWeight_base]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem lifted_factor (d t L : ℕ) (w : Fin t → ℕ)
    (a : Fin t →₀ ℕ) (g : HolGerm (ComplexModel t))
    (A : HolGerm (ComplexModel (t+1)))
    (hA : actualWeightedScalingPullback w g - actualScaledMonomialGerm w a =
      coordinateGerm (parameterIndex t) ^ (weightedDegree w a + 1) * A)
    (F : HolGerm (ComplexModel (d+t))) (hF : jointBaseZeroTrace d t F = g)
    (hL : weightedDegree w a < L) :
    ∃ B : HolGerm (ComplexModel ((d+t)+1)),
      actualWeightedScalingPullback (extendedWeight d t L w) F -
        actualScaledMonomialGerm (extendedWeight d t L w) (actualJoinedExponent (0 : Fin d →₀ ℕ) a) =
      coordinateGerm (parameterIndex (d+t)) ^ (weightedDegree w a + 1) * B := by
  obtain ⟨B, hB⟩ := scaled_lift_difference d t L w F g hF
  have hNormal := congrArg (normalParameterPullback d t) hA
  rw [map_sub, ← scaling_normal_comm d t L w, pullback_scaled_monomial d t L w,
    map_mul, map_pow, normalParameterPullback_coordinate] at hNormal
  have hIndex : normalParameterIndex d t (parameterIndex t) = parameterIndex (d+t) := by
    simp [normalParameterIndex, parameterIndex]
  rw [hIndex] at hNormal
  let s : HolGerm (ComplexModel ((d+t)+1)) := coordinateGerm (parameterIndex (d+t))
  have hPow : s ^ L = s ^ (weightedDegree w a + 1) * s ^ (L - (weightedDegree w a + 1)) := by
    rw [← pow_add, Nat.add_sub_of_le (Nat.succ_le_of_lt hL)]
  refine ⟨normalParameterPullback d t A + s ^ (L - (weightedDegree w a + 1)) * B, ?_⟩
  calc
    _ = (actualWeightedScalingPullback (extendedWeight d t L w) F -
          actualWeightedScalingPullback (extendedWeight d t L w) (jointNormalPullback d t g)) +
        (actualWeightedScalingPullback (extendedWeight d t L w) (jointNormalPullback d t g) -
          actualScaledMonomialGerm (extendedWeight d t L w) (actualJoinedExponent (0 : Fin d →₀ ℕ) a)) := by ring
    _ = s ^ L * B + s ^ (weightedDegree w a + 1) * normalParameterPullback d t A := by
      rw [hB, hNormal]
    _ = _ := by rw [hPow]; ring

/-- ORIGINAL ideal alone supplies SAME genuine fibre-weighted basis lifts and actual analytic tail factors. -/
theorem exists_original_fibre_lift_weighted_factors (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    let J := Ideal.map (jointBaseZeroTrace d t).toRingHom I
    ∃ P : ActualWeightedVertexGermData t J,
      ∃ F : ActualVertexIndex t J → HolGerm (ComplexModel (d+t)),
      (∀ a, F a ∈ I ∧ jointBaseZeroTrace d t (F a) = P.generator a) ∧
      ∃ L : ℕ, 0 < L ∧
        (∀ a : ActualVertexIndex t J, weightedDegree (degLexWeight t P.degreeBound) a.val < L) ∧
        ∀ a : ActualVertexIndex t J, ∃ B : HolGerm (ComplexModel ((d+t)+1)),
          actualWeightedScalingPullback (extendedWeight d t L (degLexWeight t P.degreeBound)) (F a) -
            actualScaledMonomialGerm (extendedWeight d t L (degLexWeight t P.degreeBound))
              (actualJoinedExponent (0 : Fin d →₀ ℕ) a.val) =
          coordinateGerm (parameterIndex (d+t)) ^
            (weightedDegree (degLexWeight t P.degreeBound) a.val + 1) * B := by
  dsimp only
  let J := Ideal.map (jointBaseZeroTrace d t).toRingHom I
  obtain ⟨P⟩ := nonempty_actualWeightedVertexGermData t J
  have hLift (a : ActualVertexIndex t J) :
      ∃ F ∈ I, jointBaseZeroTrace d t F = P.generator a :=
    (Ideal.mem_map_iff_of_surjective (jointBaseZeroTrace d t).toRingHom
      (jointBaseZeroTrace_surjective d t)).mp (P.member a)
  choose F hFI hF using hLift
  let w := degLexWeight t P.degreeBound
  let L := 1 + ∑ a : ActualVertexIndex t J, weightedDegree w a.val
  have hL (a : ActualVertexIndex t J) : weightedDegree w a.val < L := by
    have h := Finset.single_le_sum (f := fun b : ActualVertexIndex t J => weightedDegree w b.val)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
    dsimp only [L]
    omega
  refine ⟨P, F, fun a => ⟨hFI a, hF a⟩, L, by dsimp [L]; omega, hL, ?_⟩
  intro a
  exact lifted_factor d t L w a.val (P.generator a) (P.factor a) (P.factor_spec a)
    (F a) (hF a) (hL a)

end
end Hironaka.HironakaChowFibreLiftWeightedFactors
