/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualNormalBlowupExceptionalLocus
import Mathlib.RingTheory.Regular.IsSMulRegular
/-!
# The actual exceptional parameter is regular on the whole geometric strict quotient

Actual local vanishing and continuity prove that the whole original vanishing
ideal of any closure defined off a coordinate hyperplane is saturated under
all coordinate powers. The genuine differential exceptional locus of a normal
blowup chart internally supplies this off-hyperplane condition, so the actual
exceptional coordinate acts injectively on the ENTIRE geometric strict germ
quotient. No normalized-ideal equality or Hilbert--Samuel persistence is assumed.

Blueprint: `hironaka-actual-strict-exceptional-regularity-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualStrictExceptionalRegularity
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm OkaRelationSheaf
  HironakaHolomorphicJetMonomialSpan HironakaRelativeNormalDeformationInitialRelations
  HironakaActualPointGeometricBennett HironakaActualPointExceptionalVanishing
  HironakaActualNormalBlowupExceptionalLocus HironakaActualAnalyticBlowupTaylor
  HironakaActualCoefficientPresentationCentrePower
variable {n : ℕ}

/-- Actual whole vanishing ideals of closures off a coordinate hyperplane are saturated at every power. -/
theorem coordinate_pow_mul_mem_closure_ideal_iff (S : Set (ComplexModel n))
    (e : Fin n) (hS : ∀ z∈S,z e≠0) (q : ℕ) (g : HolGerm (ComplexModel n)) :
    (coordinateGerm e)^q*g∈originalCoherentOriginIdeal (vanishingIdeal (n := n) (closure S)) ↔
      g∈originalCoherentOriginIdeal (vanishingIdeal (n := n) (closure S)) := by
  constructor
  · intro hg
    obtain ⟨G,hG,rfl⟩ := HolGerm.exists_eq_mk g
    have he : HolAt (fun z : ComplexModel n => z e) 0 :=
      Eventually.of_forall fun _ => (EuclideanSpace.proj e : ComplexModel n →L[ℂ] ℂ).differentiableAt
    have hp := eventually_differentiableAt_mul (eventually_differentiableAt_pow he q) hG
    have hmk : HolGerm.mk (fun z : ComplexModel n => z e^q*G z) hp=
        (coordinateGerm e)^q*HolGerm.mk G hG := by
      rw [HolGerm.mk_mul _ _ (eventually_differentiableAt_pow he q) hG,HolGerm.mk_pow _ he q]
      rfl
    rw [← hmk] at hg
    have hz := (mk_mem_original_vanishing_origin_ideal_iff (closure S) _ hp).mp hg
    have hzero : ∀ᶠ z in 𝓝 (0 : ComplexModel n),z∈S→G z=0 := by
      filter_upwards [hz] with z hz hzS
      exact (mul_eq_zero.mp (hz (subset_closure hzS))).resolve_left (pow_ne_zero q (hS z hzS))
    exact (mk_mem_original_vanishing_origin_ideal_iff (closure S) G hG).mpr
      (eventually_zero_on_closure_of_eventually_continuous G S (hG.mono fun _ h => h.continuousAt) hzero)
  · exact fun hg => Ideal.mul_mem_left _ _ hg

/-- The equality concerns the whole original ideal quotient, including the power-zero case. -/
theorem closure_ideal_colon_coordinate_pow (S : Set (ComplexModel n))
    (e : Fin n) (hS : ∀ z∈S,z e≠0) (q : ℕ) :
    (originalCoherentOriginIdeal (vanishingIdeal (n := n) (closure S))).colon {(coordinateGerm e)^q}=
      originalCoherentOriginIdeal (vanishingIdeal (n := n) (closure S)) := by
  ext g
  rw [Submodule.mem_colon_singleton,smul_eq_mul,mul_comm]
  exact coordinate_pow_mul_mem_closure_ideal_iff S e hS q g

/-- The genuine geometric strict transform internally supplies the off-hyperplane dense defining subset. -/
theorem coordinate_pow_mul_mem_geometric_strict_ideal_iff (d t : ℕ) (ht : 2≤t)
    (j : Fin t) (b : Fin (d+t) → ℂ) (W : Set (ComplexModel (d+t)))
    (q : ℕ) (g : HolGerm (ComplexModel (d+t))) :
    (coordinateGerm (j.natAdd d))^q*g∈originalCoherentOriginIdeal (vanishingIdeal (n := d+t)
      (strictTransform (d+t) (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) W)) ↔
    g∈originalCoherentOriginIdeal (vanishingIdeal (n := d+t)
      (strictTransform (d+t) (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) W)) := by
  apply coordinate_pow_mul_mem_closure_ideal_iff
  intro z hz hze
  exact hz.2 (mem_exceptionalLocus_actual_normal_blowup_of_coordinate_eq_zero d t ht j b z hze)

/-- Every actual exceptional-power colon of the whole geometric strict ideal is the same ideal. -/
theorem geometric_strict_ideal_colon_coordinate_pow (d t : ℕ) (ht : 2≤t)
    (j : Fin t) (b : Fin (d+t) → ℂ) (W : Set (ComplexModel (d+t))) (q : ℕ) :
    (originalCoherentOriginIdeal (vanishingIdeal (n := d+t)
      (strictTransform (d+t) (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) W))).colon
        {(coordinateGerm (j.natAdd d))^q}=
    originalCoherentOriginIdeal (vanishingIdeal (n := d+t)
      (strictTransform (d+t) (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) W)) := by
  ext g
  rw [Submodule.mem_colon_singleton,smul_eq_mul,mul_comm]
  exact coordinate_pow_mul_mem_geometric_strict_ideal_iff d t ht j b W q g

/-- Multiplication by the actual exceptional parameter is injective on the entire geometric strict quotient. -/
theorem exceptional_isSMulRegular_geometric_strict_quotient (d t : ℕ) (ht : 2≤t)
    (j : Fin t) (b : Fin (d+t) → ℂ) (W : Set (ComplexModel (d+t))) :
    IsSMulRegular (HolGerm (ComplexModel (d+t)) ⧸ originalCoherentOriginIdeal (vanishingIdeal (n := d+t)
      (strictTransform (d+t) (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) W)))
      (coordinateGerm (j.natAdd d)) := by
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mpr
  intro g hg
  exact (coordinate_pow_mul_mem_geometric_strict_ideal_iff d t ht j b W 1 g).mp
    (by simpa only [pow_one,smul_eq_mul] using hg)

end
end Hironaka.HironakaActualStrictExceptionalRegularity
