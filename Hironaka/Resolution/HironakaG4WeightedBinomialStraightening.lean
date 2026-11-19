import Hironaka.Resolution.HironakaG8CaseTCoordinateReplacement
import Hironaka.Resolution.HironakaG34CoordinateScaling
import Hironaka.Analytic.CoordinatePlaneDivision

/-! Straighten a weighted binomial without losing the carrier plane. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaG4WeightedBinomialStraightening
noncomputable section
open Hironaka.BlowupSequences NormalCrossings HironakaG34CoordinateScaling
  HironakaG8CaseTCoordinateReplacement CoordinatePlaneDivision

variable {n : ℕ}

/-- A holomorphic normal coordinate vanishing on a carrier plane can replace
its specified normal coordinate while preserving the plane and all other
coordinates. -/
theorem exists_carrier_preserving_replacement {g : ComplexModel n → ℂ}
    {U : Set (ComplexModel n)} (hU : IsOpen U) (h0U : (0 : ComplexModel n) ∈ U)
    (hg : DifferentiableOn ℂ g U) (hg0 : g 0 = 0) (S : Finset (Fin n)) (s : Fin n)
    (hs : s ∈ S) (hvan : ∀ z ∈ U, z ∈ coordSubspace S → g z = 0)
    (hsderiv : fderiv ℂ g 0 (EuclideanSpace.single s 1) ≠ 0) :
    ∃ Ψ : LocalHolomorphicEquivAt (n := n) 0,
      Ψ.source ⊆ U ∧ Ψ.toFun 0 = 0 ∧
      (∀ z, Ψ.toFun z s = g z) ∧
      (∀ z j, j ≠ s → Ψ.toFun z j = z j) ∧
      ∀ z ∈ Ψ.source, (z ∈ coordSubspace S ↔ Ψ.toFun z ∈ coordSubspace S) := by
  classical
  obtain ⟨Φ, hΦU, hΦ0, hΦs, hΦother⟩ :=
    exists_coordinate_replacement_at hU h0U hg hg0 s hsderiv
  let p : ComplexModel n → ComplexModel n := fun z => setCoord z s 0
  have hp : Continuous p := by
    change Continuous (fun z : ComplexModel n => setCoord z s 0)
    simpa only [Function.comp_def, id_eq] using
      ((differentiable_setCoord s).continuous.comp
        (continuous_id.prodMk (continuous_const : Continuous (fun _ : ComplexModel n => (0 : ℂ)))))
  let V : Set (ComplexModel n) := p ⁻¹' Φ.source
  have hV : IsOpen V := Φ.isOpen_source.preimage hp
  have h0V : (0 : ComplexModel n) ∈ V := by
    change setCoord 0 s 0 ∈ Φ.source
    simpa [setCoord] using Φ.center_mem_source
  let Ψ := Φ.restrict V hV 0 ⟨Φ.center_mem_source, h0V⟩
  refine ⟨Ψ, fun z hz => hΦU hz.1, hΦ0, hΦs, hΦother, ?_⟩
  intro z hz
  change z ∈ coordSubspace S ↔ Φ.toFun z ∈ coordSubspace S
  constructor
  · intro hzS i hi
    by_cases his : i = s
    · subst i
      rw [hΦs, hvan z (hΦU hz.1) hzS]
    · rw [hΦother z i his]
      exact hzS i hi
  · intro hzS
    have hpΦ : p z ∈ Φ.source := hz.2
    have hpS : p z ∈ coordSubspace S := by
      intro i hi
      by_cases his : i = s
      · subst i; simp [p]
      · have hh := hzS i hi
        rw [hΦother z i his] at hh
        simpa [p, his] using hh
    have hgp : g (p z) = 0 := hvan (p z) (hΦU hpΦ) hpS
    have heq : Φ.toFun z = Φ.toFun (p z) := by
      ext i
      by_cases his : i = s
      · subst i
        rw [hΦs, hΦs, hgp]
        simpa [hΦs] using hzS s hs
      · rw [hΦother z i his, hΦother (p z) i his]
        simp [p, his]
    have hzEq : z = p z := by
      calc z = Φ.invFun (Φ.toFun z) := (Φ.left_inv z hz.1).symm
           _ = Φ.invFun (Φ.toFun (p z)) := congrArg Φ.invFun heq
           _ = p z := Φ.left_inv (p z) hpΦ
    rwa [hzEq]

/-- The replacement converts a scalar normal correction plus a weighted
monomial into the prescribed binomial, retaining all transverse coordinates. -/
theorem binomial_after_replacement (Ψ : LocalHolomorphicEquivAt (n := n) 0)
    (g : ComplexModel n → ℂ) (s t : Fin n) (c : Fin n → ℕ)
    (hst : t ≠ s) (hcs : c s = 0)
    (hs : ∀ z, Ψ.toFun z s = g z)
    (hother : ∀ z j, j ≠ s → Ψ.toFun z j = z j) (z : ComplexModel n) :
    binomial s t c (Ψ.toFun z) = g z + z t * ∏ b, z b ^ c b := by
  rw [binomial, hs, hother z t hst]
  congr 2
  apply Finset.prod_congr rfl
  intro b hb
  by_cases hbs : b = s
  · subst b
    simp [hcs]
  · rw [hother z b hbs]

end
end Hironaka.HironakaG4WeightedBinomialStraightening
