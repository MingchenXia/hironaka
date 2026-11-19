import Hironaka.Analytic.Unibranch.HironakaG10HigherRankArtinianBaseChange
import Hironaka.Analytic.Unibranch.HironakaG10HigherRankCurveFlat
import Hironaka.Resolution.HironakaG10CurveChartQuotient
import Hironaka.Resolution.HironakaG10SmoothBaseFibreExactness

/-! Transport arbitrary-rank one-parameter matrix cokernels through the actual curve chart. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology
open Hironaka Hironaka
  HolGerm OkaGermBridge OkaRelationSheaf HironakaRelativeNormalIdeal
  HironakaG10FlatGermChain HironakaG10SmoothBaseFibreExactness
  HironakaG10OneParameterCokernelFlatness HironakaG10CurveChartQuotient
  Hironaka.Analytic.Unibranch.HironakaG10HigherRankArtinianBaseChange
namespace Hironaka.Analytic.Unibranch.HironakaG10OneParameterMatrixChart
noncomputable section
local instance (t : ℕ) : Algebra (HolGerm (ComplexModel 1)) (HolGerm (ComplexModel (1+t))) :=
  tangentAlgebra 1 t

/-- The arbitrary-rank actual matrix cokernel is carried through the curve
chart with the literal base-germ equivalence and first-projection action. -/
def curveChartMatrixCokernelEquiv (t : ℕ) {a b : ℕ}
    (F : Fin a → Fin b → ComplexModel (1+t) → ℂ)
    (hF : ∀ i j, HolAt (F i j) 0) :
    letI : Module (HolGerm ℂ) (germCokernel (productFamily t F) 0) := parameterModule (productFamily t F) 0
    letI : Module (HolGerm (ComplexModel 1)) (germCokernel (productFamily t F) 0) :=
      Module.compHom _ baseGermEquiv.toRingHom
    nativeCokernel 1 t (germMat 0 F) ≃ₗ[HolGerm (ComplexModel 1)]
      germCokernel (productFamily t F) 0 := by
  let R := HolGerm (ComplexModel 1)
  let A := HolGerm (ComplexModel (1+t))
  let C := HolGerm (ℂ × ComplexModel t)
  letI : Algebra R C := ((basePullback (ComplexModel t)).comp baseGermEquiv.toRingHom).toAlgebra
  let e : A ≃ₐ[R] C := {
    toRingEquiv := ambientGermEquiv t
    commutes' := ambientGermEquiv_tangentPullback t
  }
  let M := germMat 0 F
  let N := germMat 0 (productFamily t F)
  have hentries : (fun i j => e (M i j)) = N := by
    funext i j
    exact ambientGermEquiv_germAt t (F i j) (hF i j)
  let E := matrixCokernelEquiv (S := R) e M
  rw [hentries] at E
  letI : Module (HolGerm ℂ) (germCokernel (productFamily t F) 0) := parameterModule (productFamily t F) 0
  letI : Module R (germCokernel (productFamily t F) 0) := Module.compHom _ baseGermEquiv.toRingHom
  exact (Submodule.Quotient.restrictScalarsEquiv R (LinearMap.range M.mulVecLin)).trans E
end
end Hironaka.Analytic.Unibranch.HironakaG10OneParameterMatrixChart
