import Hironaka.Algebra.NodeFittingSmooth
import Hironaka.Algebra.NodeFittingOmegaFinite
import Mathlib.RingTheory.Kaehler.TensorProduct

/-! # Full intrinsic ORIGINAL relative differential Fitting ideals on actual scalar extensions -/

noncomputable section

open scoped TensorProduct

namespace Hironaka.Algebra.NodeFittingOmegaScalarExtension

open NodeFittingModule

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Pushout

variable (A R K T : Type*) [CommRing A] [CommRing R] [CommRing K] [CommRing T]
  [Algebra A R] [Algebra A K] [Algebra A T] [Algebra R T] [Algebra K T]
  [IsScalarTower A R T] [IsScalarTower A K T] [Algebra.IsPushout A K R T]
  [Module.FinitePresentation R (KaehlerDifferential A R)]

include A R in
/-- Native actual differential pushout internally transfers native finite presentation. -/
theorem finitePresentation_pushout : Module.FinitePresentation T (KaehlerDifferential K T) :=
  (KaehlerDifferential.tensorKaehlerEquiv A K R T).finitePresentation_iff.mp inferInstance

/-- The ENTIRE original relative Fitting ideal follows the actual ORIGINAL pushout coefficient map. -/
theorem fittingIdeal_pushout (i : ℕ) :
    letI := finitePresentation_pushout A R K T
    (fittingIdeal (R := R) (M := KaehlerDifferential A R) i).map (algebraMap R T) =
      fittingIdeal (R := T) (M := KaehlerDifferential K T) i := by
  let := finitePresentation_pushout A R K T
  exact (fittingIdeal_baseChange (R := R) (M := KaehlerDifferential A R) T i).trans
    (fittingIdeal_equiv (KaehlerDifferential.tensorKaehlerEquiv A K R T) i)

end Pushout

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (A R K : Type*) [CommRing A] [CommRing R] [Field K] [PerfectField K]
  [Algebra A R] [Algebra A K] [Algebra.FinitePresentation A R]

/-- At EVERY actual smooth geometric affine prime, the image of the full ORIGINAL family ideal is excluded. -/
theorem original_fitting_not_le_of_scalarExtension_smoothAt
    (p : Ideal (K ⊗[A] R)) [p.IsPrime] [Algebra.IsSmoothAt K p]
    (hdim : ringKrullDim (K ⊗[A] R) ≤ 1) :
    letI := NodeFittingOmega.finitePresentation A R
    ¬ (fittingIdeal (R := R) (M := KaehlerDifferential A R) 1).map
      (algebraMap R (K ⊗[A] R)) ≤ p := by
  let := NodeFittingOmega.finitePresentation A R
  let : Algebra.FiniteType K (K ⊗[A] R) := inferInstance
  let := NodeFittingClosedRegular.affineOmega_finitePresentation K (K ⊗[A] R)
  rw [fittingIdeal_pushout A R K (K ⊗[A] R) 1]
  exact NodeFittingSmooth.fitting_not_le_of_isSmoothAt K (K ⊗[A] R) p hdim

end Hironaka.Algebra.NodeFittingOmegaScalarExtension
