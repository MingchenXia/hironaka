import DeJongAlterations.Algebra.CompletionFlatMapComparison
import DeJongAlterations.Algebra.NoetherianCompletion
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.RingHom.Flat

/-! Flatness of the actual induced completion map of an essentially finite type local algebra. -/

noncomputable section

open IsLocalRing
open scoped TensorProduct

namespace DeJongAlterations.Algebra.CompletionFlatMap

open CompletionRegularityBasics CompletionLocalMap

universe u
variable (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)]

/-- The literal algebra structure of the actual induced completed coefficient map. -/
@[instance_reducible]
def completedAlgebra : Algebra (Completion A) (Completion B) :=
  (completionMap (algebraMap A B)).toAlgebra

/-- The original and completed coefficient maps form the actual scalar tower. -/
theorem completedAlgebra_isScalarTower :
    letI := completedAlgebra A B
    IsScalarTower A (Completion A) (Completion B) := by
  let := completedAlgebra A B
  exact IsScalarTower.of_algebraMap_eq fun a ↦
    (completionMap_algebraMap (algebraMap A B) a).symm

variable [IsNoetherianRing A] [Algebra.EssFiniteType A B]

omit [IsLocalRing B] [IsLocalHom (algebraMap A B)] in
/-- The actual completed-base tensor ring is Noetherian, derived from original essential finite type. -/
theorem tensorRing_isNoetherianRing : IsNoetherianRing (TensorRing A B) :=
  Algebra.EssFiniteType.isNoetherianRing (Completion A) (TensorRing A B)

variable [Module.Flat A B]

/-- The actual map on literal maximal-adic completions is flat. The finite-level tensor
comparison is constructed internally and the original map is the only flatness hypothesis. -/
theorem flat_completionMap : (completionMap (algebraMap A B)).Flat := by
  let : IsNoetherianRing (TensorRing A B) := tensorRing_isNoetherianRing A B
  have hflat : (algebraMap (Completion A)
      (AdicCompletion (tensorIdeal A B) (TensorRing A B))).Flat := by
    rw [RingHom.flat_algebraMap_iff]
    exact Module.Flat.trans (Completion A) (TensorRing A B) _
  rw [← tensorCompletionEquiv_comp_algebraMap A B]
  exact hflat.comp (RingHom.Flat.of_bijective (tensorCompletionEquiv A B).bijective)

/-- Native module flatness for exactly the actual induced completed algebra. -/
theorem flat_completedAlgebra :
    letI := completedAlgebra A B
    Module.Flat (Completion A) (Completion B) :=
  flat_completionMap A B

/-- The actual induced completed local algebra is faithfully flat, with target
Noetherianity derived internally from original essential finite type. -/
theorem faithfullyFlat_completedAlgebra :
    letI := completedAlgebra A B
    Module.FaithfullyFlat (Completion A) (Completion B) := by
  let := completedAlgebra A B
  let : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing A B
  let : Module.Flat (Completion A) (Completion B) := flat_completedAlgebra A B
  let : IsLocalHom (algebraMap (Completion A) (Completion B)) := by
    change IsLocalHom (completionMap (algebraMap A B))
    infer_instance
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

end DeJongAlterations.Algebra.CompletionFlatMap
