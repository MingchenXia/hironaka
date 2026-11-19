import Hironaka.Resolution.HironakaActualFixedInheritedSelectorPermutation
import Hironaka.Resolution.HironakaActualAnalyticBlowupTaylor

/-! The existing genuine real source AND target coordinate permutation
commutes with actual polynomial blowup maps and whole analytic germ pullback.
Only the original actual centre power is supplied; an actual normalized
quotient and its SAME permuted quotient are internally produced, with both
true Taylor dictionaries. No desired target compatibility is a premise.

An arbitrary permutation is not asserted to preserve a current monic family.
The existing specific stable-insertion source-family theorem remains the
separate consumer for historical labels/selectors/prefix/contact data. -/

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaActualAnalyticOwnerPermutationQuotient

noncomputable section

open HolGerm HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicJetMonomialSpan HironakaActualCoefficientPresentationCentrePower
  HironakaActualFormalBlowupMemberGeneration HironakaActualAnalyticBlowupTaylor
  HironakaActualAnalyticBlockGraphTranslation HironakaActualFixedInheritedSelectorPermutation

variable {n : ℕ}

private theorem actual_permutation_mem_image_iff
    (p : Fin n ≃ Fin n) (A : Set (Fin n)) (i : Fin n) : p i ∈ p '' A ↔ i ∈ A := by
  constructor
  · rintro ⟨j, hj, he⟩
    exact (p.injective he) ▸ hj
  · intro hi
    exact ⟨i, hi, rfl⟩

/-- This is an ACTUAL global polynomial square. The real permutation satisfies
R_p(z)_i=z_(p i), so physical source and target coordinates use R_p inverse. -/
theorem actualAnalyticBlowupMap_permutation_square
    (p : Fin n ≃ Fin n) (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (z : ComplexModel n) :
    actualPermutationLinearEquiv p
        (actualAnalyticBlowupMap (p '' A) (p e) (fun i => b (p.symm i)) z) =
      actualAnalyticBlowupMap A e b (actualPermutationLinearEquiv p z) := by
  ext i
  by_cases hi : i ∈ A
  · have hip : p i ∈ p '' A := (actual_permutation_mem_image_iff p A i).mpr hi
    by_cases hie : i = e
    · subst i
      simp [actualPermutationLinearEquiv_apply, actualAnalyticBlowupMap_apply,
        actualAnalyticBlowupCoordinate, hi]
    · have hpie : p i ≠ p e := fun h => hie (p.injective h)
      simp [actualPermutationLinearEquiv_apply, actualAnalyticBlowupMap_apply,
        actualAnalyticBlowupCoordinate, hi, hie, hpie]
  · have hip : p i ∉ p '' A := fun h => hi ((actual_permutation_mem_image_iff p A i).mp h)
    simp [actualPermutationLinearEquiv_apply, actualAnalyticBlowupMap_apply,
      actualAnalyticBlowupCoordinate, hi]

/-- Existing whole coordinate-ideal transport applies to the literal analytic
centre ideal; no new source permutation or inverse is invented. -/
theorem map_actualAnalyticCoordinateIdeal_permutation
    (p : Fin n ≃ Fin n) (A : Set (Fin n)) :
    Ideal.map (actualPermutationGermEquiv p).toRingEquiv.toRingHom
        (actualAnalyticCoordinateIdeal A) = actualAnalyticCoordinateIdeal (p '' A) := by
  simpa only [actualAnalyticCoordinateIdeal, actualAnalyticCoordinateBlockIdeal] using
    map_coordinateIdeal_actualPermutation p A

theorem map_actualAnalyticCoordinateIdeal_pow_permutation
    (p : Fin n ≃ Fin n) (A : Set (Fin n)) (μ : ℕ) :
    Ideal.map (actualPermutationGermEquiv p).toRingEquiv.toRingHom
        (actualAnalyticCoordinateIdeal A ^ μ) = actualAnalyticCoordinateIdeal (p '' A) ^ μ := by
  rw [Ideal.map_pow, map_actualAnalyticCoordinateIdeal_permutation]

/-- The genuine entire original analytic germ maps have the same two-sided
polynomial square, on EVERY germ rather than a finite Taylor approximation. -/
theorem actualAnalyticBlowupPullback_permutation
    (p : Fin n ≃ Fin n) (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (g : HolGerm (ComplexModel n)) :
    actualPermutationGermEquiv p (actualAnalyticBlowupPullback A e b g) =
      actualAnalyticBlowupPullback (p '' A) (p e) (fun i => b (p.symm i))
        (actualPermutationGermEquiv p g) := by
  obtain ⟨H, hH, rfl⟩ := HolGerm.exists_eq_mk g
  have h0 : (actualPermutationLocalEquiv p).toFun 0 = 0 :=
    map_zero (actualPermutationLinearEquiv p)
  change localGermAlgEquiv (actualPermutationLocalEquiv p) h0
      (actualAnalyticBlowupPullback A e b (HolGerm.mk H hH)) =
    actualAnalyticBlowupPullback (p '' A) (p e) (fun i => b (p.symm i))
      (localGermAlgEquiv (actualPermutationLocalEquiv p) h0 (HolGerm.mk H hH))
  unfold actualAnalyticBlowupPullback
  rw [compAlgHom_mk, localGermAlgEquiv_mk, localGermAlgEquiv_mk, compAlgHom_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z => by
    change H (actualAnalyticBlowupMap A e b (actualPermutationLinearEquiv p z)) =
      H (actualPermutationLinearEquiv p
        (actualAnalyticBlowupMap (p '' A) (p e) (fun i => b (p.symm i)) z))
    exact congrArg H (actualAnalyticBlowupMap_permutation_square p A e b z).symm

/-- ONLY the original genuine source centre power internally produces both
actual quotient products with SAME mark, numerator and analytic quotient,
and their whole Taylor dictionaries. No target orders or desired square,
current diagram, supplied quotient or new selector is an input. -/
theorem exists_actual_same_analytic_quotient_after_owner_permutation
    (p : Fin n ≃ Fin n) (A : Set (Fin n)) (e : Fin n) (he : e ∈ A)
    (b : Fin n → ℂ) (μ : ℕ) (g : HolGerm (ComplexModel n))
    (hg : g ∈ actualAnalyticCoordinateIdeal A ^ μ) :
    ∃ he' : p e ∈ p '' A,
      ∃ hp : actualPermutationGermEquiv p g ∈ actualAnalyticCoordinateIdeal (p '' A) ^ μ,
      ∃ N : HolGerm (ComplexModel n),
        (coordinateGerm e) ^ μ * N = actualAnalyticBlowupPullback A e b g ∧
        (coordinateGerm (p e)) ^ μ * actualPermutationGermEquiv p N =
          actualAnalyticBlowupPullback (p '' A) (p e) (fun i => b (p.symm i))
            (actualPermutationGermEquiv p g) ∧
        actualUnshiftedTaylorAlgHom n N = actualNormalizedFormalMember A e he b μ
          (actualUnshiftedTaylorAlgHom n g) (actualTaylor_mem_coordinateCentre_pow A μ g hg) ∧
        actualUnshiftedTaylorAlgHom n (actualPermutationGermEquiv p N) =
          actualNormalizedFormalMember (p '' A) (p e) he' (fun i => b (p.symm i)) μ
            (actualUnshiftedTaylorAlgHom n (actualPermutationGermEquiv p g))
            (actualTaylor_mem_coordinateCentre_pow (p '' A) μ (actualPermutationGermEquiv p g) hp) := by
  have he' : p e ∈ p '' A := ⟨e, he, rfl⟩
  have hp : actualPermutationGermEquiv p g ∈ actualAnalyticCoordinateIdeal (p '' A) ^ μ := by
    have h := Ideal.mem_map_of_mem (actualPermutationGermEquiv p).toRingEquiv.toRingHom hg
    rwa [map_actualAnalyticCoordinateIdeal_pow_permutation p A μ] at h
  obtain ⟨N, hN, hTaylor⟩ := exists_actualAnalyticBlowup_quotient A e he b μ g hg
  have hN' : (coordinateGerm (p e)) ^ μ * actualPermutationGermEquiv p N =
      actualAnalyticBlowupPullback (p '' A) (p e) (fun i => b (p.symm i))
        (actualPermutationGermEquiv p g) := by
    have h := congrArg (actualPermutationGermEquiv p) hN
    rw [map_mul, map_pow, actualPermutationGermEquiv_coordinate,
      actualAnalyticBlowupPullback_permutation] at h
    exact h
  refine ⟨he', hp, N, hN, hN', hTaylor, ?_⟩
  apply actualNormalizedFormalMember_unique
  have ht := congrArg (actualUnshiftedTaylorAlgHom n) hN'
  rw [map_mul, map_pow, actualUnshiftedTaylor_coordinate] at ht
  exact ht.trans (DFunLike.congr_fun
    (actualTaylor_analyticBlowupPullback (p '' A) (p e) (fun i => b (p.symm i)))
    (actualPermutationGermEquiv p g))

end

end Hironaka.HironakaActualAnalyticOwnerPermutationQuotient
