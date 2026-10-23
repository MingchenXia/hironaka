import DeJongAlterations.Algebra.CompletionRegularityBasics
import DeJongAlterations.Algebra.NodeFlatPresentationEvaluation
import Mathlib.RingTheory.AdicCompletion.Functoriality

/-! Actual complete evaluation at internally chosen original maximal-ideal generators. -/

noncomputable section

open IsLocalRing MvPowerSeries

namespace DeJongAlterations.Algebra.NoetherianCompletionEvaluation

open CompletionRegularityBasics

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- Actual original finite maximal-ideal generators, chosen internally from Noetherianity. -/
def generatorSet : Finset R := (maximalIdeal R).fg_of_isNoetherianRing.choose

/-- These exact original elements generate the full original maximal ideal. -/
theorem generatorSet_span : Ideal.span (generatorSet R : Set R) = maximalIdeal R :=
  (maximalIdeal R).fg_of_isNoetherianRing.choose_spec

/-- Every actual chosen generator belongs to the original maximal ideal. -/
theorem generator_mem (i : generatorSet R) : i.val ∈ maximalIdeal R := by
  rw [← generatorSet_span R]
  exact Ideal.subset_span i.property

/-- The literal completed coefficient images of the actual chosen original generators. -/
def completedGenerators : generatorSet R → Completion R :=
  fun i ↦ algebraMap R (Completion R) i.val

/-- These exact actual coefficient images lie in the actual completed maximal ideal. -/
theorem completedGenerators_mem (i : generatorSet R) : completedGenerators R i ∈ maximalIdeal (Completion R) := by
  change i.val ∈ (maximalIdeal (Completion R)).comap (algebraMap R (Completion R))
  rw [IsLocalRing.maximalIdeal_comap]
  exact generator_mem R i

/-- Actual coefficient-preserving formal evaluation, without any target Noetherianity premise. -/
def completionEvaluation : MvPowerSeries (generatorSet R) R →ₐ[R] Completion R :=
  NodeFlatPresentation.evaluation (maximalIdeal (Completion R)) (completedGenerators R) (completedGenerators_mem R)

/-- The actual original coefficient map is retained literally. -/
theorem completionEvaluation_C (a : R) : completionEvaluation R (C a) = algebraMap R (Completion R) a :=
  NodeFlatPresentation.evaluation_C _ _ _ _

/-- Each original formal variable maps to its specified original generator's actual completion image. -/
theorem completionEvaluation_X (i : generatorSet R) : completionEvaluation R (X i) = completedGenerators R i :=
  NodeFlatPresentation.evaluation_X _ _ _ _

/-- The full original variable ideal maps exactly to the actual completed maximal ideal. -/
theorem variableIdeal_image :
    (Ideal.span (Set.range (fun i : generatorSet R ↦ (X i : MvPowerSeries (generatorSet R) R)))).map
      (completionEvaluation R).toRingHom = maximalIdeal (Completion R) := by
  have hrange : Set.range (fun i : generatorSet R ↦ i.val) = (generatorSet R : Set R) := by ext x; simp
  calc
    (Ideal.span (Set.range (fun i : generatorSet R ↦ (X i : MvPowerSeries (generatorSet R) R)))).map
        (completionEvaluation R).toRingHom = Ideal.span (Set.range (completedGenerators R)) := by
      rw [Ideal.map_span, ← Set.range_comp]
      have hf : (completionEvaluation R).toRingHom ∘
          (fun i : generatorSet R ↦ (X i : MvPowerSeries (generatorSet R) R)) =
          completedGenerators R := by
        funext i
        exact completionEvaluation_X R i
      rw [hf]
    _ = (Ideal.span (Set.range (fun i : generatorSet R ↦ i.val))).map (algebraMap R (Completion R)) := by
      rw [Ideal.map_span, ← Set.range_comp]
      rfl
    _ = (maximalIdeal R).map (algebraMap R (Completion R)) := by rw [hrange, generatorSet_span]
    _ = maximalIdeal (Completion R) := AdicCompletion.maximalIdeal_eq_map.symm

/-- Native complete-source surjectivity gives an actual surjection onto the literal completion. -/
theorem completionEvaluation_surjective : Function.Surjective (completionEvaluation R) := by
  let V : Ideal (MvPowerSeries (generatorSet R) R) := Ideal.span (Set.range X)
  let : IsPrecomplete V (MvPowerSeries (generatorSet R) R) := inferInstance
  have hv : V.map (completionEvaluation R).toRingHom = maximalIdeal (Completion R) := variableIdeal_image R
  let : IsHausdorff (V.map (completionEvaluation R).toRingHom) (Completion R) := by
    rw [hv]
    infer_instance
  apply surjective_of_mk_map_comp_surjective (I := V) (completionEvaluation R).toRingHom
  rw [hv]
  intro y
  obtain ⟨z, hz⟩ := (residueField_map_bijective R).surjective y
  obtain ⟨r, hr⟩ := residue_surjective z
  use C r
  change residue (Completion R) (completionEvaluation R (C r)) = y
  rw [completionEvaluation_C, ← ResidueField.map_residue, hr, hz]

end DeJongAlterations.Algebra.NoetherianCompletionEvaluation
