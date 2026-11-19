import Hironaka.Algebra.CompletionLocalMap
import Mathlib.RingTheory.AdicCompletion.Functoriality

/-! The SAME native completion map preserves an actual whole original local surjection. -/

noncomputable section

namespace Hironaka.Algebra.CompletionSurjectiveLocalMap

open IsLocalRing CompletionRegularityBasics CompletionLocalMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
  [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
  (φ : A →+* B) [IsLocalHom φ] (hφ : Function.Surjective φ)

include hφ

/-- The WHOLE completed maximal ideal has its exact native image under the SAME actual map. -/
theorem maximalIdeal_map :
    (maximalIdeal (Completion A)).map (completionMap φ) = maximalIdeal (Completion B) := by
  have hcomp : (completionMap φ).comp (algebraMap A (Completion A)) =
      (algebraMap B (Completion B)).comp φ :=
    RingHom.ext (completionMap_algebraMap φ)
  rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map, hcomp, ← Ideal.map_map,
    map_maximalIdeal_of_surjective φ hφ, AdicCompletion.maximalIdeal_eq_map]

/-- Native maximal-adic completion preserves the WHOLE actual original surjection. -/
theorem surjective : Function.Surjective (completionMap φ) := by
  have hmax := maximalIdeal_map φ hφ
  let : IsHausdorff ((maximalIdeal (Completion A)).map (completionMap φ)) (Completion B) := by
    rw [hmax]
    infer_instance
  apply surjective_of_mk_map_comp_surjective
    (I := maximalIdeal (Completion A)) (completionMap φ)
  rw [hmax]
  intro c
  obtain ⟨r, rfl⟩ := (AdicCompletion.residueField_map_bijective B).2 c
  obtain ⟨b, rfl⟩ := residue_surjective r
  obtain ⟨a, rfl⟩ := hφ b
  refine ⟨algebraMap A (Completion A) a, ?_⟩
  change residue (Completion B) (completionMap φ (algebraMap A (Completion A) a)) = _
  rw [completionMap_algebraMap, ResidueField.map_residue]

end Hironaka.Algebra.CompletionSurjectiveLocalMap
