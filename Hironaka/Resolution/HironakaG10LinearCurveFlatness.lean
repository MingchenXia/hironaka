import Hironaka.Resolution.HironakaG10HirChartFlattener
import Hironaka.Resolution.HironakaG10LinearGermDetection

/-!
# Actual chart flatness detected on linear curves in a smooth base

For any ideal in the actual holomorphic germ ring, the associated structure
homomorphism is flat if and only if every linear-curve base change is flat.
This uses the canonical flattener's analytic universal property and detection
of nonzero holomorphic germs by linear curves. Both dimensions may be zero;
the ideal is arbitrary, with no reducedness assumption on the total space.
-/

set_option autoImplicit false

open Filter

namespace Hironaka.HironakaG10LinearCurveFlatness

noncomputable section

open HolGerm HironakaActualAnalyticBaseChangeCoefficients
  HironakaChowPresentationIndependentFlattener HironakaHolomorphicJetChartInvariance
  HironakaG10HirFlatQuotient
  HironakaG10HirChartFlattener HironakaG10LinearGermDetection

/-- Actual flatness over a smooth analytic germ is detected by all linear-curve
base changes, for the whole original ideal, in every base dimension. -/
theorem chartMap_flat_iff_forall_linear_curve (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d + t)))) :
    (chartMap d t I).Flat ↔
      ∀ L : ComplexModel 1 →L[ℂ] ComplexModel d,
        (chartMap 1 t
          (Ideal.map (jointBasePullback d 1 t L
            (Eventually.of_forall fun _ => L.differentiableAt) L.map_zero).toRingHom I)).Flat := by
  have original : (chartMap d t I).Flat ↔ canonicalFlattenerIdeal d t I = ⊥ := by
    rw [← flat_quotMap_bot_iff, isFlattenerIdeal_chartMap d t I, le_bot_iff]
  have curve (L : ComplexModel 1 →L[ℂ] ComplexModel d) :
      (chartMap 1 t
        (Ideal.map (jointBasePullback d 1 t L
          (Eventually.of_forall fun _ => L.differentiableAt) L.map_zero).toRingHom I)).Flat ↔
      Ideal.map (compAlgHom L
        (Eventually.of_forall fun _ => L.differentiableAt) L.map_zero).toRingHom
        (canonicalFlattenerIdeal d t I) = ⊥ := by
    rw [← flat_quotMap_bot_iff,
      isFlattenerIdeal_chartMap_baseChange d t I 1 L
        (Eventually.of_forall fun _ => L.differentiableAt) L.map_zero,
      le_bot_iff]
  constructor
  · intro h L
    apply (curve L).mpr
    rw [original.mp h, Ideal.map_bot]
  · intro h
    apply original.mpr
    exact ideal_eq_bot_of_forall_linear_map_eq_bot _ fun L => (curve L).mp (h L)

end

end Hironaka.HironakaG10LinearCurveFlatness
