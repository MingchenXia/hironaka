import Hironaka.Analytic.Unibranch.HironakaG10AllBanachJetsSeparate
import Hironaka.Analytic.Unibranch.HironakaG10CoefficientOperatorFaithful
import Hironaka.Analytic.Unibranch.HironakaG10OperatorJetNaturality

/-! All finite-coefficient actions detect the actual operator germ. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Filter Set
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10AllCoefficientOperatorsSeparate
open Hironaka Hironaka
  HolGerm HironakaRelativeNormalIdeal HironakaG10ArtinianBaseChange
  HironakaG10ArtinianFlatQuotient HironakaHolomorphicPointJets
  Hironaka.Analytic.Unibranch.HironakaG10AllBanachJetsSeparate
  Hironaka.Analytic.Unibranch.HironakaG10CoefficientOperatorFaithful
  Hironaka.Analytic.Unibranch.HironakaG10CoefficientTensorOperator
  Hironaka.Analytic.Unibranch.HironakaG10BanachParameterJet
  Hironaka.Analytic.Unibranch.HironakaG10OperatorJetNaturality
noncomputable section
local instance (n : ℕ) : Algebra ℂ (HolGerm (ComplexModel n)) :=
  (HolGerm.constHom : ℂ →+* HolGerm (ComplexModel n)).toAlgebra

/-- If every actual finite-coefficient action of the operator family vanishes,
the original holomorphic operator family itself vanishes near the origin. -/
theorem eventually_zero_of_all_coefficient_actions_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (d : ℕ) (T : ComplexModel d → (E →L[ℂ] F))
    (hT : ∀ᶠ x in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ T x)
    (hcoeff : ∀ q : ℕ,
      let Q := HolGerm (ComplexModel d) ⧸ truncatedParameterIdeal d q ⊥
      letI : FiniteDimensional ℂ Q := finiteDimensional_quotient_sup_maximalIdeal_pow d (q+1) ⊥
      let basis := Module.finBasis ℂ Q
      coefficientTensorOperator (E := E) (F := F) basis
        (banachJet d q (parameterQuotientMap d q ⊥) T) = 0) :
    T =ᶠ[𝓝 (0 : ComplexModel d)] fun _ => 0 := by
  apply eventually_zero_of_all_banachJets_zero d T hT
  intro q
  let Q := HolGerm (ComplexModel d) ⧸ truncatedParameterIdeal d q ⊥
  let : FiniteDimensional ℂ Q := finiteDimensional_quotient_sup_maximalIdeal_pow d (q+1) ⊥
  let basis := Module.finBasis ℂ Q
  apply (coefficientTensorOperator_injective (E := E) (F := F) basis)
  have h0 : coefficientTensorOperator (E := E) (F := F) basis (0 : Q ⊗[ℂ] (E →L[ℂ] F)) = 0 := by
    ext v i
    simp [coefficientTensorOperator]
  exact (hcoeff q).trans h0.symm
end
end Hironaka.Analytic.Unibranch.HironakaG10AllCoefficientOperatorsSeparate
