import Hironaka.Analytic.Unibranch.HironakaG10ScalarIdealJet
import Hironaka.Analytic.Unibranch.HironakaG10BanachJetCoordinates
import Mathlib.Analysis.LocallyConvex.SeparatingDual

set_option autoImplicit false
set_option maxHeartbeats 1500000
open Filter Set
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10ScalarIdealJetConverse
open Hironaka Hironaka
  HolGerm OkaGermBridge HironakaRelativeNormalIdeal HironakaHolomorphicPointJets
  HironakaG10ArtinianBaseChange HironakaG10ArtinianFlatQuotient
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients
  Hironaka.Analytic.Unibranch.HironakaG10BanachParameterJet
  Hironaka.Analytic.Unibranch.HironakaG10BanachJetCoordinates
  Hironaka.Analytic.Unibranch.HironakaG10CoefficientTensorOperator
noncomputable section
local instance (n : ℕ) : Algebra ℂ (HolGerm (ComplexModel n)) :=
  (HolGerm.constHom : ℂ →+* HolGerm (ComplexModel n)).toAlgebra

/-- Containment of every actual scalar operator germ in the whole ideal forces
all actual operator tensor jets over its maximal-ideal thickenings to vanish. -/
theorem banachJet_zero_of_scalar_operator_ideal_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (d : ℕ) (I : Ideal (HolGerm (ComplexModel d)))
    (T : ComplexModel d → (E →L[ℂ] F))
    (hT : ∀ᶠ x in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ T x)
    (hI : Ideal.span (Set.range fun p : E × (F →L[ℂ] ℂ) =>
      let L := p.2.comp (ContinuousLinearMap.apply ℂ F p.1)
      HolGerm.mk (L ∘ T) (hT.mono fun _ h => L.differentiableAt.comp _ h)) ≤ I)
    (q : ℕ) : banachJet d q (parameterQuotientMap d q I) T = 0 := by
  classical
  let Q := HolGerm (ComplexModel d) ⧸ truncatedParameterIdeal d q I
  let : FiniteDimensional ℂ Q := finiteDimensional_quotient_sup_maximalIdeal_pow d (q+1) I
  let basis := Module.finBasis ℂ Q
  let φ := parameterQuotientMap d q I
  apply (parameterTensorEquiv basis).injective
  ext i v
  apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ)
  intro ell
  let L := ell.comp (ContinuousLinearMap.apply ℂ F v)
  have hmem : HolGerm.mk (L ∘ T) (hT.mono fun _ h => L.differentiableAt.comp _ h) ∈ I :=
    hI (Ideal.subset_span ⟨(v,ell), rfl⟩)
  have hzero : φ (HolGerm.mk (L ∘ T) (hT.mono fun _ h => L.differentiableAt.comp _ h)) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact (show I ≤ truncatedParameterIdeal d q I from le_sup_left) hmem
  have hsum : (∑ j, (L (parameterTensorEquiv basis (banachJet d q φ T) j)) • basis j) = 0 := by
    rw [← scalar_germ_eq_coefficient_jet basis d q φ (parameterQuotientMap_kills d q I) T hT L]
    exact hzero
  have hz := (linearIndependent_iff'.mp basis.linearIndependent) Finset.univ
    (fun j => L (parameterTensorEquiv basis (banachJet d q φ T) j)) hsum i (Finset.mem_univ i)
  simpa [L] using hz
end
end Hironaka.Analytic.Unibranch.HironakaG10ScalarIdealJetConverse
