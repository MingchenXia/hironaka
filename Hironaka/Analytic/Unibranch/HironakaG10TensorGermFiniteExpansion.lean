import Hironaka.Analytic.Unibranch.HironakaG10ArtinianHolomorphicMatrix

/-! # Whole finite-parameter fibre germs from actual local expansions -/
set_option autoImplicit false
open Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10TensorGermFiniteExpansion
open Hironaka OkaRelationSheaf OkaGermBridge
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianHolomorphicMatrix

local instance {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] : Algebra ℂ (HolGerm X) :=
  (HolGerm.constHom : ℂ →+* HolGerm X).toAlgebra

/-- Whole tensor germs agree if the actual parameter-valued holomorphic
functions agree on a neighborhood of the original fibre point. -/
theorem tensorGermAt_congr_eventually
    {Q X ι : Type*} [NormedCommRing Q] [NormedAlgebra ℂ Q] [FiniteDimensional ℂ Q]
    [NormedAddCommGroup X] [NormedSpace ℂ X] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ Q) {z : X} {f g : X → Q}
    (hf : ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ f x)
    (hg : ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ g x) (h : f =ᶠ[𝓝 z] g) :
    tensorGermAt b z f = tensorGermAt b z g := by
  apply (parameterTensorEquiv b).injective
  apply funext
  intro i
  rw [tensorGermAt_coordinate, tensorGermAt_coordinate]
  apply (germAt_eq_germAt_iff (holomorphic_coordinate b i hf) (holomorphic_coordinate b i hg)).mpr
  exact h.mono fun _ hx => congrArg (b.coord i) hx

/-- If an actual holomorphic parameter-valued family locally equals a finite
sum of scalar holomorphic functions times fixed parameter elements, its
whole tensor germ is exactly the corresponding sum of original scalar germs. -/
theorem tensorGermAt_eq_finite_expansion
    {Q X ι κ : Type*} [NormedCommRing Q] [NormedAlgebra ℂ Q] [FiniteDimensional ℂ Q]
    [NormedAddCommGroup X] [NormedSpace ℂ X] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ Q) {z : X} (s : Finset κ)
    (f : X → Q) (hf : ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ f x)
    (c : κ → X → ℂ) (hc : ∀ i ∈ s, HolAt (c i) z) (a : κ → Q)
    (h : f =ᶠ[𝓝 z] fun x => ∑ i ∈ s, c i x • a i) :
    tensorGermAt b z f = ∑ i ∈ s, a i ⊗ₜ[ℂ] germAt z (c i) := by
  have hterm : ∀ i ∈ s, ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ (fun x => c i x • a i) x :=
    fun i hi => (hc i hi).mono fun _ hx => hx.smul_const (a i)
  have hsum : ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ (fun x => ∑ i ∈ s, c i x • a i) x := by
    filter_upwards [(eventually_all_finset s).mpr hterm] with x hx
    exact DifferentiableAt.fun_sum fun i hi => hx i hi
  rw [tensorGermAt_congr_eventually b hf hsum h, tensorGermAt_finset_sum b s hterm]
  apply Finset.sum_congr rfl
  intro i hi
  exact tensorGermAt_smul_const b (hc i hi) (a i)

end Hironaka.Analytic.Unibranch.HironakaG10TensorGermFiniteExpansion
