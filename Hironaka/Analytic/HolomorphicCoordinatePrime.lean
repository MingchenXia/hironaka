/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.ActualHolomorphicGermFactoriality
import Hironaka.Analytic.HolomorphicGermReducednessBridge

set_option autoImplicit false

/-! # Actual coordinate irreducibility and primeness from the germ derivative -/

open Set Filter
open scoped Topology

namespace Hironaka.HolomorphicCoordinatePrime

open HolomorphicGermReducednessBridge

noncomputable section

/-- The genuine coordinate derivative rules out a factorization into two nonunits. -/
theorem irreducible_coordinate_germ {n : ℕ} (j : Fin n) :
    Irreducible (HolGerm.mk (fun z : ComplexModel n => z j)
      (eventually_differentiableAt_coordinate j)) := by
  constructor
  · intro hu
    have hval := (HolGerm.isUnit_iff_eval_ne_zero _).mp hu
    simp only [HolGerm.eval_mk, PiLp.zero_apply] at hval
    exact hval rfl
  · intro a b hab
    by_contra hunit
    push Not at hunit
    obtain ⟨f, hf, rfl⟩ := HolGerm.exists_eq_mk a
    obtain ⟨g, hg, rfl⟩ := HolGerm.exists_eq_mk b
    have hf0 : f 0 = 0 := by
      by_contra hne
      apply hunit.1
      exact (HolGerm.isUnit_iff_eval_ne_zero _).mpr
        (by simpa only [HolGerm.eval_mk] using hne)
    have hg0 : g 0 = 0 := by
      by_contra hne
      apply hunit.2
      exact (HolGerm.isUnit_iff_eval_ne_zero _).mpr
        (by simpa only [HolGerm.eval_mk] using hne)
    have heq : (fun z : ComplexModel n => z j) =ᶠ[𝓝 0] fun z => f z * g z := by
      apply HolGerm.mk_eq_mk_iff.mp
      exact hab.trans (HolGerm.mk_mul f g hf hg).symm
    have hderiv : fderiv ℂ (fun z : ComplexModel n => z j) 0
        (AnalyticJacobianSingularCore.coordinateDirection j) ≠ 0 := by
      apply fderiv_apply_coordinateDirection_ne_zero_of_eventuallyEq_unit_mul_coordinate
        (f := fun z : ComplexModel n => z j) (u := fun _ : ComplexModel n => (1 : ℂ))
      · exact differentiableAt_const _
      · norm_num
      · filter_upwards with z
        simp
    apply hderiv
    rw [heq.fderiv_eq]
    change fderiv ℂ (f * g) 0 (AnalyticJacobianSingularCore.coordinateDirection j) = 0
    rw [(hf.self_of_nhds.hasFDerivAt.mul hg.self_of_nhds.hasFDerivAt).fderiv]
    simp [hf0, hg0]

/-- Proved actual germ factoriality converts the genuine coordinate irreducibility to prime. -/
theorem prime_coordinate_germ {n : ℕ} (j : Fin n) :
    Prime (HolGerm.mk (fun z : ComplexModel n => z j)
      (eventually_differentiableAt_coordinate j)) := by
  let : UniqueFactorizationMonoid (HolGerm (ComplexModel n)) :=
    ActualHolomorphicGermFactoriality.uniqueFactorizationMonoid_holGerm_euclidean n
  exact UniqueFactorizationMonoid.irreducible_iff_prime.mp (irreducible_coordinate_germ j)

end
end Hironaka.HolomorphicCoordinatePrime
