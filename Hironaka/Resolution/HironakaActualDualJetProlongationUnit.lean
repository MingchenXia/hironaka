/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualDualJetProlongation
import Hironaka.Resolution.HironakaRelativeNormalTaylorCoefficients

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualDualJetProlongationUnit
noncomputable section
open HolGerm HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan
  HironakaHolomorphicJetRankLoci HironakaRelativeNormalIdeal HironakaActualTangentJetConnection
  HironakaActualDualJetProlongation HironakaActualMacaulayAnnihilatorConnection
  HironakaActualHSZeroCentreVanishing HironakaRelativeNormalTaylorCoefficients

/-- The EXISTING canonical derivative of the SAME original germ has exactly the genuine successor scalar-jet coordinates. -/
theorem actual_directional_derivative_germ_scalar_jet {n : ℕ} (q : ℕ)
    (g : HolGerm (ComplexModel n)) (w : ComplexModel n) (row : monomialIndex n q) :
    finiteCoordinateArray q (finiteJet q (iteratedDerivativeGerm [w] g)) row =
      finiteJet (q+1) g ⟨row.1.val+1, Nat.succ_lt_succ row.1.isLt⟩
        (Fin.cons w (fun k => EuclideanSpace.basisFun (Fin n) ℂ (row.2 k))) := by
  induction g using HolGerm.induction_on with
  | h f hf =>
    rw [iteratedDerivativeGerm_mk]
    change iteratedFDeriv ℂ row.1.val (fun z => fderiv ℂ f z w) 0
      (fun k => EuclideanSpace.basisFun (Fin n) ℂ (row.2 k)) = _
    obtain ⟨U, hUf, hU, h0⟩ := eventually_nhds_iff.mp hf
    have hAn : AnalyticAt ℂ f 0 := HolomorphicAnalytic.analyticAt_of_differentiableOn hU
      (fun z hz => (hUf z hz).differentiableWithinAt) h0
    exact actual_analytic_directional_jet hAn row.1.val
      (fun k => EuclideanSpace.basisFun (Fin n) ℂ (row.2 k)) w

/-- Zero on ALL old TRUE jets on an actual open forces the genuine prolongation zero on ALL next TRUE jets. -/
theorem actualDualJetProlongation_zero_of_old_true_jet_zero (d t q : ℕ)
    (η : monomialIndex (d+t) q → ComplexModel d → ℂ)
    {V : Set (ComplexModel d)} (hV : IsOpen V)
    (hη : ∀ row, DifferentiableOn ℂ (η row) V)
    (hzero : ∀ c ∈ V, ∀ g : HolGerm (ComplexModel (d+t)),
      ∑ row, η row c * finiteCoordinateArray q (finiteJet q g) row = 0)
    (c a : ComplexModel d) (hc : c ∈ V)
    (v : LinearMap.range (finiteJet (n := d+t) (q+1))) :
    actualDualJetProlongation d t q η c a v.val = 0 := by
  rcases v with ⟨v, g, rfl⟩
  obtain ⟨f, hf, rfl⟩ := HolGerm.exists_eq_mk g
  have hDzero : ∑ row : monomialIndex (d+t) q, fderiv ℂ (η row) c a *
      finiteCoordinateArray q (finiteJet q (HolGerm.mk f hf)) row = 0 := by
    have hs := HasFDerivAt.fun_sum (u := (Finset.univ : Finset (monomialIndex (d+t) q)))
      (fun row _ => ((hη row).differentiableAt (hV.mem_nhds hc)).hasFDerivAt.mul_const
        (finiteCoordinateArray q (finiteJet q (HolGerm.mk f hf)) row))
    have hz : (fun b => ∑ row, η row b * finiteCoordinateArray q (finiteJet q (HolGerm.mk f hf)) row)
        =ᶠ[𝓝 c] (fun _ => (0 : ℂ)) := by
      filter_upwards [hV.mem_nhds hc] with b hb
      exact hzero b hb (HolGerm.mk f hf)
    have he := congrArg (fun L : ComplexModel d →L[ℂ] ℂ => L a) hs.fderiv
    change fderiv ℂ (fun b => ∑ row, η row b * finiteCoordinateArray q (finiteJet q (HolGerm.mk f hf)) row) c a = _ at he
    rw [hz.fderiv_eq, fderiv_const_apply] at he
    simpa [smul_eq_mul, mul_comm] using he.symm
  have hdir := hzero c hc (iteratedDerivativeGerm [tangentInclusion d t a] (HolGerm.mk f hf))
  have he (row : monomialIndex (d+t) q) :=
    actual_directional_derivative_germ_scalar_jet q (HolGerm.mk f hf) (tangentInclusion d t a) row
  simp only [he] at hdir
  change (∑ row : monomialIndex (d+t) q,
    (fderiv ℂ (η row) c a * finiteCoordinateArray q (finiteJet q (HolGerm.mk f hf)) row +
      η row c * finiteJet (q+1) (HolGerm.mk f hf) ⟨row.1.val+1, Nat.succ_lt_succ row.1.isLt⟩
        (Fin.cons (tangentInclusion d t a)
          (fun k => EuclideanSpace.basisFun (Fin (d+t)) ℂ (row.2 k))))) = 0
  rw [Finset.sum_add_distrib, hDzero, hdir, add_zero]

/-- The original unit-ideal complement kills EVERY next true jet without any generator-vanishing premise. -/
theorem actualDualJetProlongation_zero_of_translatedIdeal_eq_top (d t q : ℕ) {ι : Type*} [Fintype ι]
    {U : Set (ComplexModel (d+t))} (hU : IsOpen U)
    (G : ι → ComplexModel (d+t) → ℂ) (hG : ∀ i, DifferentiableOn ℂ (G i) U)
    {V : Set (ComplexModel d)} (hV : IsOpen V)
    (hVU : ∀ c ∈ V, tangentInclusion d t c ∈ U)
    (η : monomialIndex (d+t) q → ComplexModel d → ℂ)
    (hη : ∀ row, DifferentiableOn ℂ (η row) V)
    (hker : ∀ c ∈ V, ∀ col, ∑ row, η row c *
      originalMacaulayMatrix q G (tangentInclusion d t c) row col = 0)
    (htop : ∀ c (hc : c ∈ V), translatedIdeal G (tangentInclusion d t c)
      (actual_family_holomorphicAt hU G hG _ (hVU c hc)) = ⊤)
    (c a : ComplexModel d) (hc : c ∈ V)
    (v : LinearMap.range (finiteJet (n := d+t) (q+1))) :
    actualDualJetProlongation d t q η c a v.val = 0 := by
  apply actualDualJetProlongation_zero_of_old_true_jet_zero d t q η hV hη _ c a hc v
  intro b hb g
  exact actual_macaulay_annihilator_whole_ideal (d+t) q G (tangentInclusion d t b)
    (actual_family_holomorphicAt hU G hG _ (hVU b hb)) (fun row => η row b) (hker b hb) g
    (by rw [htop b hb]; trivial)

end
end Hironaka.HironakaActualDualJetProlongationUnit
