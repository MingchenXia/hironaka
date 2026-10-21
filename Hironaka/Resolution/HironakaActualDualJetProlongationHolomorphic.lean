/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualDualJetProlongation

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualDualJetProlongationHolomorphic
noncomputable section
open HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan
  HironakaRelativeNormalIdeal HironakaActualDualJetProlongation

/-- EVERY fixed TRUE original next jet has genuine holomorphic prolongation evaluation on the SAME coefficient domain. -/
theorem actualDualJetProlongation_holomorphic_fixed_jet (d t q : ℕ)
    (η : monomialIndex (d+t) q → ComplexModel d → ℂ) (a : ComplexModel d)
    {V : Set (ComplexModel d)}
    (hη : ∀ row, DifferentiableOn ℂ (η row) V)
    (hDη : ∀ row, DifferentiableOn ℂ (fun c => fderiv ℂ (η row) c a) V)
    (v : LinearMap.range (finiteJet (n := d+t) (q+1))) :
    DifferentiableOn ℂ (fun c => actualDualJetProlongation d t q η c a v.val) V := by
  have hs : DifferentiableOn ℂ (∑ row : monomialIndex (d+t) q, fun c =>
      fderiv ℂ (η row) c a *
        v.val ⟨row.1.val, Nat.lt_succ_of_lt row.1.isLt⟩
          (fun k => EuclideanSpace.basisFun (Fin (d+t)) ℂ (row.2 k)) +
      η row c * v.val ⟨row.1.val+1, Nat.succ_lt_succ row.1.isLt⟩
        (Fin.cons (tangentInclusion d t a)
          (fun k => EuclideanSpace.basisFun (Fin (d+t)) ℂ (row.2 k)))) V := by
    apply DifferentiableOn.sum
    intro row _
    exact ((hDη row).mul_const _).add ((hη row).mul_const _)
  exact hs.congr fun c _ => by
    simp only [actualDualJetProlongation, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply]

end
end Hironaka.HironakaActualDualJetProlongationHolomorphic
