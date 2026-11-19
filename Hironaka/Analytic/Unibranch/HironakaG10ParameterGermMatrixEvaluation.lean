import Hironaka.Analytic.Unibranch.HironakaG10BanachJetScalarization

/-! # Actual scalar parameter-germ evaluation of finite matrix rows -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace Hironaka.Analytic.Unibranch.HironakaG10ParameterGermMatrixEvaluation
open Hironaka Hironaka

/-- A quotient map evaluates the actual finite scalar matrix row against a
fixed complex vector by the corresponding parameter-algebra matrix row. -/
theorem parameter_germ_sum_mul_constants
    {Q ι : Type*} [CommRing Q] [Algebra ℂ Q] [Fintype ι]
    (d : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q)
    (f : ι → ComplexModel d → ℂ) (c : ι → ℂ)
    (hf : ∀ j, ∀ᶠ s in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ (f j) s) :
    ∃ hs : ∀ᶠ s in 𝓝 (0 : ComplexModel d),
      DifferentiableAt ℂ (fun s => ∑ j, f j s * c j) s,
      φ (HolGerm.mk (fun s => ∑ j, f j s * c j) hs) =
        ∑ j, φ (HolGerm.mk (f j) (hf j)) * algebraMap ℂ Q (c j) := by
  have hp : ∀ j, ∀ᶠ s in 𝓝 (0 : ComplexModel d),
      DifferentiableAt ℂ (fun s => f j s * c j) s :=
    fun j => (hf j).mono fun _ h => h.mul_const (c j)
  have hs : ∀ᶠ s in 𝓝 (0 : ComplexModel d),
      DifferentiableAt ℂ (fun s => ∑ j, f j s * c j) s := by
    filter_upwards [eventually_all.mpr hp] with s hs
    exact DifferentiableAt.fun_sum fun j _ => hs j
  refine ⟨hs,?_⟩
  rw [HolGerm.mk_sum Finset.univ (fun j s => f j s * c j) hp, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [HolGerm.mk_mul (f j) (fun _ => c j) (hf j)
    (Eventually.of_forall fun _ => differentiableAt_const (c j)), map_mul]
  congr 1
  change φ ((algebraMap ℂ (HolGerm (ComplexModel d))) (c j)) = _
  exact φ.commutes (c j)

end Hironaka.Analytic.Unibranch.HironakaG10ParameterGermMatrixEvaluation
