import DeJongAlterations.Algebra.CompletionRegularityCotangent
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-! Independence of the original specified equations is preserved and reflected by actual completion. -/

noncomputable section

open IsLocalRing

namespace DeJongAlterations.Algebra.CompletionIntersectionRegularityCotangent

open CompletionRegularityBasics CompletionRegularityCotangent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- The actual coefficient images of the original maximal-ideal elements. -/
def completedFamily {ι : Type v} (t : ι → maximalIdeal R) : ι → maximalIdeal (Completion R) :=
  fun i ↦ ⟨algebraMap R (Completion R) (t i), by
    change (t i : R) ∈ (maximalIdeal (Completion R)).comap (algebraMap R (Completion R))
    rw [IsLocalRing.maximalIdeal_comap]
    exact (t i).property⟩

/-- The actual original cotangent classes are independent whenever their actual coefficient images are. -/
theorem independent_of_completed {ι : Type v} (t : ι → maximalIdeal R)
    (hli : LinearIndependent (ResidueField (Completion R))
      (fun i ↦ (maximalIdeal (Completion R)).toCotangent (completedFamily R t i))) :
    LinearIndependent (ResidueField R) (fun i ↦ (maximalIdeal R).toCotangent (t i)) := by
  classical
  rw [linearIndependent_iff'] at hli ⊢
  intro s a hsum i hi
  have h := congrArg (cotangentMap R) hsum
  simp only [map_sum, cotangentMap_residue_smul, cotangentMap_toCotangent, map_zero] at h
  have ha := hli s (fun j ↦ ResidueField.map (algebraMap R (Completion R)) (a j)) h i hi
  apply (RingHom.injective (ResidueField.map (algebraMap R (Completion R))))
  simpa only [map_zero] using ha

/-- Native cotangent bijectivity and the actual residue isomorphism preserve original independence in completion. -/
theorem independent_completed_of_original {ι : Type v} (t : ι → maximalIdeal R)
    (hli : LinearIndependent (ResidueField R) (fun i ↦ (maximalIdeal R).toCotangent (t i))) :
    LinearIndependent (ResidueField (Completion R))
      (fun i ↦ (maximalIdeal (Completion R)).toCotangent (completedFamily R t i)) := by
  have h := hli.map_of_surjective_injectiveₛ
    (R' := ResidueField (Completion R)) (M' := CotangentSpace (Completion R))
    (ResidueField.map (algebraMap R (Completion R))) (cotangentMap R).toAddHom
    (residueField_map_bijective R).surjective (cotangentMap_injective R)
    (cotangentMap_residue_smul R)
  change LinearIndependent (ResidueField (Completion R))
    (fun i ↦ cotangentMap R ((maximalIdeal R).toCotangent (t i))) at h
  simpa only [cotangentMap_toCotangent, completedFamily] using h

/-- Independence refers to the same original equations and exactly the native original/completed residue fields. -/
theorem independent_iff_completed {ι : Type v} (t : ι → maximalIdeal R) :
    LinearIndependent (ResidueField R) (fun i ↦ (maximalIdeal R).toCotangent (t i)) ↔
      LinearIndependent (ResidueField (Completion R))
        (fun i ↦ (maximalIdeal (Completion R)).toCotangent (completedFamily R t i)) :=
  ⟨independent_completed_of_original R t, independent_of_completed R t⟩

end DeJongAlterations.Algebra.CompletionIntersectionRegularityCotangent
