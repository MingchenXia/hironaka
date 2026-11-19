import Hironaka.Analytic.Unibranch.HironakaG10ArtinianHolomorphicMatrix

/-! # Translation of actual whole tensor germs -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace Hironaka.Analytic.Unibranch.HironakaG10TensorGermTranslate
open Hironaka OkaRelationSheaf OkaGermBridge
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianHolomorphicMatrix

local instance {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] : Algebra ℂ (HolGerm X) :=
  (HolGerm.constHom : ℂ →+* HolGerm X).toAlgebra

/-- Recentering the actual holomorphic function at a fibre point gives the
same whole tensor germ as taking its germ at that original point. -/
theorem tensorGermAt_translate
    {Q X ι : Type*} [NormedCommRing Q] [NormedAlgebra ℂ Q] [FiniteDimensional ℂ Q]
    [NormedAddCommGroup X] [NormedSpace ℂ X] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ Q) (z : X) (f : X → Q)
    (hf : ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ f x) :
    tensorGermAt b z f = tensorGermAt b 0 (fun x => f (z+x)) := by
  apply (parameterTensorEquiv b).injective
  apply funext
  intro i
  rw [tensorGermAt_coordinate, tensorGermAt_coordinate]
  have hc := holomorphic_coordinate b i hf
  rw [germAt_of_holAt hc, germAt_of_holAt hc.translate]
  congr 1
  funext x
  simp

end Hironaka.Analytic.Unibranch.HironakaG10TensorGermTranslate
