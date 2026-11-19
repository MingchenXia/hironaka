import Hironaka.Analytic.Unibranch.HironakaG10ReassociatedSquareZeroIdeal
import Hironaka.Resolution.HironakaG10LinearCurveFlatness

/-! Actual tangent actions and quotient flatness across model reassociation. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology
open Hironaka Hironaka
  HolGerm HironakaRelativeNormalIdeal HironakaHolomorphicJetChartInvariance
  HironakaG10HirChartFlattener
  Hironaka.Analytic.Unibranch.HironakaG10ModelAssociativity
  Hironaka.Analytic.Unibranch.HironakaG10ModelAssociativityGerm
  Hironaka.Analytic.Unibranch.HironakaG10ActualSquareZeroMatrixEquiv
  Hironaka.Analytic.Unibranch.HironakaG10ReassociatedSquareZeroIdeal
namespace Hironaka.Analytic.Unibranch.HironakaG10ReassociatedSquareZeroFlat
noncomputable section

/-- The inverse reassociation is the literal inverse finite-index cast. -/
theorem assocModel_symm_apply (d t a : ℕ) (w : ComplexModel (d+(t+a))) (i : Fin ((d+t)+a)) :
    (assocModel d t a).symm w i = w (Fin.cast (Nat.add_assoc d t a) i) := by rfl

/-- Reassociation preserves the full original parameter projection. -/
theorem assocModel_tangentProjection (d t a : ℕ) (w : ComplexModel (d+(t+a))) :
    tangentProjection d t (tangentProjection (d+t) a ((assocModel d t a).symm w)) =
      tangentProjection d (t+a) w := by
  ext i
  simp only [tangentProjection_apply,assocModel_symm_apply]
  have hi : Fin.cast (Nat.add_assoc d t a) ((i.castAdd t).castAdd a) = i.castAdd (t+a) := by
    apply Fin.ext
    simp
  rw [hi]

/-- The whole original parameter-germ pullback is unchanged by reassociation. -/
theorem assocGermEquiv_tangentPullback (d t a : ℕ) (r : HolGerm (ComplexModel d)) :
    assocGermEquiv d t a (tangentPullback (d+t) a (tangentPullback d t r)) =
      tangentPullback d (t+a) r := by
  induction r using HolGerm.induction_on with
  | h f hf =>
    unfold assocGermEquiv tangentPullback
    rw [compAlgHom_mk,compAlgHom_mk,HolGerm.comapEquiv_mk,compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun w => congrArg f (assocModel_tangentProjection d t a w)

/-- The actual quotient equivalence respects the original parameter action. -/
theorem chartMap_reassociated_flat_iff_nested (d t a : ℕ) {b : ℕ}
    (F : Matrix (Fin a) (Fin b) (HolGerm (ComplexModel (d+t)))) :
    letI := tangentAlgebra d t
    let B := HolGerm (ComplexModel (d+t))
    let R := HolGerm (ComplexModel d)
    let Q := HolGerm (ComplexModel ((d+t)+a)) ⧸ actualSquareZeroMatrixIdeal (d+t) a F
    letI : Algebra B (HolGerm (ComplexModel ((d+t)+a))) := tangentAlgebra (d+t) a
    letI : Module R Q := Module.compHom Q (tangentPullback d t).toRingHom
    (chartMap d (t+a) (reassociatedSquareZeroIdeal d t a F)).Flat ↔ Module.Flat R Q := by
  let _ := tangentAlgebra d t
  let B := HolGerm (ComplexModel (d+t))
  let R := HolGerm (ComplexModel d)
  let J := actualSquareZeroMatrixIdeal (d+t) a F
  let Q := HolGerm (ComplexModel ((d+t)+a)) ⧸ J
  let _ : Algebra B (HolGerm (ComplexModel ((d+t)+a))) := tangentAlgebra (d+t) a
  let _ : Module R Q := Module.compHom Q (tangentPullback d t).toRingHom
  change (chartMap d (t+a) (reassociatedSquareZeroIdeal d t a F)).Flat ↔ Module.Flat R Q
  let e := Ideal.quotientEquiv J (reassociatedSquareZeroIdeal d t a F) (assocGermEquiv d t a) rfl
  let η : R →+* Q := (Ideal.Quotient.mk J).comp
    ((tangentPullback (d+t) a).toRingHom.comp (tangentPullback d t).toRingHom)
  have he : e.toRingHom.comp η = chartMap d (t+a) (reassociatedSquareZeroIdeal d t a F) := by
    apply RingHom.ext
    intro r
    change Ideal.Quotient.mk (reassociatedSquareZeroIdeal d t a F)
      (assocGermEquiv d t a (tangentPullback (d+t) a (tangentPullback d t r))) = _
    rw [assocGermEquiv_tangentPullback]
    rfl
  have hflat : (chartMap d (t+a) (reassociatedSquareZeroIdeal d t a F)).Flat ↔ η.Flat := by
    rw [← he]
    exact RingHom.Flat.comp_iff_of_bijective_left (f := η) (g := e.toRingHom) e.bijective
  rw [hflat]
  rfl
end
end Hironaka.Analytic.Unibranch.HironakaG10ReassociatedSquareZeroFlat
