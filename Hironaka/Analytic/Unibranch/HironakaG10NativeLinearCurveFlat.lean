import Hironaka.Analytic.Unibranch.HironakaG10OneParameterMatrixChart
import Mathlib.RingTheory.Flat.Stability

/-! Actual centered native matrix-cokernel flatness along all linear base curves. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology
open Hironaka Hironaka
  HolGerm OkaRelationSheaf HironakaRelativeNormalIdeal HironakaActualCentreJointJets
  HironakaG10FlatGermChain HironakaG10FlatResolutionStart HironakaG10SmoothBaseFibreExactness
  HironakaG10OneParameterCokernelFlatness HironakaG10CurveChartQuotient
  HironakaG10LinearCurveMatrixPullback
  Hironaka.Analytic.Unibranch.HironakaG10HigherRankCurveFlat
  Hironaka.Analytic.Unibranch.HironakaG10OneParameterMatrixChart
namespace Hironaka.Analytic.Unibranch.HironakaG10NativeLinearCurveFlat
noncomputable section
local instance (t : ℕ) : Algebra (HolGerm (ComplexModel 1)) (HolGerm (ComplexModel (1+t))) :=
  tangentAlgebra 1 t

/-- Restricting a flat module through a ring equivalence preserves flatness. -/
theorem flat_restrict_of_ringEquiv {R S M : Type} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M] (e : R ≃+* S) (h : Module.Flat S M) :
    letI : Module R M := Module.compHom M e.toRingHom
    Module.Flat R M := by
  let _ : Algebra R S := e.toRingHom.toAlgebra
  let _ : Module R M := Module.compHom M e.toRingHom
  let _ : IsScalarTower R S M := IsScalarTower.of_compHom R S M
  let _ : Module.Flat R S := RingHom.Flat.of_bijective e.bijective
  let _ : Module.Flat S M := h
  exact Module.Flat.trans R S M

/-- An exact original normal fibre gives actual centered matrix-cokernel
flatness over the actual one-dimensional model-germ ring along every line. -/
theorem native_curve_cokernel_flat_of_exact_normal_fibre {a b c : ℕ} (d t : ℕ)
    (F : Fin a → Fin b → ComplexModel (d+t) → ℂ)
    (G : Fin b → Fin c → ComplexModel (d+t) → ℂ)
    (hF : ∀ i j, HolAt (F i j) 0)
    (hG : ∀ j k, HolAt (G j k) 0)
    (hcomp : ∀ i k, ∀ᶠ x in 𝓝 (0 : ComplexModel (d+t)), ∑ j, F i j x * G j k x = 0)
    (hfib : ∀ v : Fin b → ComplexModel t → ℂ,
      IsRelationAt (fun i j z => F i j (actualJointNormalInclusion d t z)) 0 v →
      IsCombinationAt (columns (fun j k z => G j k (actualJointNormalInclusion d t z))) 0 v)
    (L : ComplexModel 1 →L[ℂ] ComplexModel d) :
    Module.Flat (HolGerm (ComplexModel 1))
      (nativeCokernel 1 t (germMat 0 (curveFamily d t L F))) := by
  let FM := curveFamily d t L F
  let M := germCokernel (productFamily t FM) 0
  let _ : Module (HolGerm ℂ) M := parameterModule (productFamily t FM) 0
  have hflat : Module.Flat (HolGerm ℂ) M :=
    curve_cokernel_flat_of_exact_normal_fibre d t F G hF hG hcomp hfib L
  let _ : Module (HolGerm (ComplexModel 1)) M := Module.compHom M baseGermEquiv.toRingHom
  let _ : Module.Flat (HolGerm (ComplexModel 1)) M := flat_restrict_of_ringEquiv baseGermEquiv hflat
  exact Module.Flat.of_linearEquiv (curveChartMatrixCokernelEquiv t FM (holAt_curveFamily d t L F hF))
end
end Hironaka.Analytic.Unibranch.HironakaG10NativeLinearCurveFlat
