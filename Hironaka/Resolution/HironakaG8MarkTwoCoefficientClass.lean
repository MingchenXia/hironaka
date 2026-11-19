import Hironaka.Resolution.HironakaG8MarkTwoFullCoefficient
import Hironaka.Resolution.HironakaG8LocalCoeff
import Hironaka.Resolution.HironakaG1OriginalInvariantClassFunctorial
import Hironaka.Resolution.HironakaG8CuspDerivativeTrace

/-! The full mark-two double coefficient operation has the original
canonical value of its raw same-mark class. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8MarkTwoCoefficientClass
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec CanonicalCentres
  HomogenizedIdealAlong HomogenizedIdeal HomogenizedGlueing
  DerivativeIdeal DerivativeIdealAlong IdealWeightPowers CoefficientIdeal
  RestrictedIdealExtension GermIdealPullbackCalculus RelativePrincipalizationSpan InvertibleIdealQuotient
  BlowupDerivativeIdeal DivisorExponentAlong FactorizationFromResolution RestrictLeCalculus
  HironakaG8MarkTwoFullCoefficient HironakaG8LocalCoeff HironakaG11InvBMClass
  HironakaG1OriginalInvariantClassFunctorial HironakaG8CuspDerivativeTrace

variable {n : ℕ} {X : CMfd.{0} n}

/-- The first coefficient operation already reaches the complete double
coefficient ideal at mark two and on the full carrier. -/
theorem mark_two_coefficient_ideal (M : MarkedIdeal n X) (hM : M.ideal.IsCoherent)
    (hN : M.N = univ) (hMark : M.d = 2) :
    (coeffMarkedAlong M).ideal = sumIdeal M.ideal (idealPow (derivIdeal M.ideal) 2) := by
  change finSumIdeal (fun i => idealPow (iterDerivIdealAlong M.N M.ideal i)
    (sumExp (fun j => M.d - j) M.d i)) M.d = _
  rw [hN,hMark]
  have ihol := fun x g hg => GermIdeal.IsCoherent.holomorphicAt_mem hM (x := x) (g := g) hg
  simp only [iterDerivIdealAlong_univ ihol]
  let J := fun i => idealPow (iterDerivIdeal M.ideal i) (sumExp (fun j => 2 - j) 2 i)
  have hJ (i : ℕ) := isCoherent_idealPow (isCoherent_iterDerivIdeal hM i)
    (sumExp (fun j => 2 - j) 2 i)
  change finSumIdeal J 2 = _
  rw [finSumIdeal_succ (μ := 1) (fun i _ => hJ i), finSumIdeal_one (hJ 0)]
  have h0 : sumExp (fun j => 2 - j) 2 0 = 1 := by decide
  have h1 : sumExp (fun j => 2 - j) 2 1 = 2 := by decide
  rw [h0,h1]
  change sumIdeal (idealPow M.ideal 1) (idealPow (derivIdeal M.ideal) 2) = _
  rw [idealPow_one_of_isCoherent hM]

/-- Literal equality includes the original mark and whole ordered boundary. -/
theorem mark_two_double_coefficient_record_eq (M : MarkedIdeal n X)
    (hM : M.ideal.IsCoherent) (hN : M.N = univ) (hMark : M.d = 2) :
    coeffMarkedAlong (coeffMarkedAlong (homMarkedAlong M)) = coeffMarkedAlong M := by
  have hd : (coeffMarkedAlong M).d = 2 := by
    rw [coeffMarkedAlong_d (by rw [hMark]; decide),hMark]
    decide
  have hd' : (coeffMarkedAlong (homMarkedAlong M)).d = 2 := hd
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of (𝔪 := coeffMarkedAlong (coeffMarkedAlong (homMarkedAlong M))) (𝔫 := coeffMarkedAlong M) rfl rfl ?_ ?_
  · rw [mark_two_double_coefficient_ideal M hM hN hMark, mark_two_coefficient_ideal M hM hN hMark]
  · rw [coeffMarkedAlong_d (by rw [hd']; decide),hd',hd]
    decide

/-- Domain of the exact coefficient recoding at the same mark. Ideal
inclusion preserves the actual nonzero condition on the entire carrier. -/
theorem mark_two_coefficient_domain (M : MarkedIdeal n X)
    (hM : IsInvDomain n M) (hN : M.N = univ) (hMark : M.d = 2) :
    IsInvDomain n (coeffMarkedAlong M) := by
  have hC := isCoherent_coeffMarkedAlong hM.isWellFormed.isCoherent
    hM.isWellFormed.isClosedSubmanifold_N
  refine ⟨⟨hM.isWellFormed.isClosedSubmanifold_N,hC,hM.isWellFormed.isSNCDivisor,
    hM.isWellFormed.isTransverse⟩,hM.dimLE,?_,?_⟩
  · rw [coeffMarkedAlong_d hM.one_le_d,hMark]
    decide
  · intro x hx
    obtain ⟨g,hg,hNonzero⟩ := hM.isNonzeroAlongAt x hx
    refine ⟨g,?_,hNonzero⟩
    rw [mark_two_coefficient_ideal M hM.isWellFormed.isCoherent hN hMark]
    exact le_sumIdeal_left hM.isWellFormed.isCoherent x g hg

/-- The literal mark-two double coefficient recoding retains the genuine
original canonical initial value on the common cosupport. -/
theorem mark_two_double_coefficient_original_initial_value (M : MarkedIdeal n X)
    (hM : IsInvDomain n M) (hN : M.N = univ) (hE : M.E = []) (hMark : M.d = 2)
    (x : X) (hx : x ∈ M.cosupp) :
    (canonicalInvariant n).inv (coeffMarkedAlong (coeffMarkedAlong (homMarkedAlong M))) .refl x =
      (canonicalInvariant n).inv M .refl x := by
  rw [mark_two_double_coefficient_record_eq M hM.isWellFormed.isCoherent hN hMark]
  have hd : M.d = (coeffMarkedAlong M).d := by
    rw [coeffMarkedAlong_d hM.one_le_d,hMark]
    decide
  exact ((classFunctorialFor_canonicalInvariant n).inv_eq M (coeffMarkedAlong M) hM
    (mark_two_coefficient_domain M hM hN hMark) (locWPEquiv_coeffMarkedAlong_of_nil M hM hE)
    hd rfl (SameCarrierDim.of_N_eq rfl) (expAgree_of_nil hE) .refl trivial x hx).symm

end
end Hironaka.HironakaG8MarkTwoCoefficientClass
