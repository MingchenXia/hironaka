import Hironaka.Geometry.ProjectiveCurveFibration
import Hironaka.Geometry.FiberDimensionGenericGlobal
import Hironaka.Geometry.FiberDimensionCurveComponents

/-!
# A constructed dense open of actual pure curve fibres

The open and every actual fibre component dimension are internally derived.
This is an additional part of the projective curve-fibration preparation;
geometric connectedness, smoothness, markings and Bertini remain separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.ProjectiveCurveFibrationOpen

open FiberDimension FiberDimensionCurveComponents

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X S : Scheme.{u}}

/-- Positive generic curve dimension constructs an actual dense open of nonempty pure curve fibres. -/
theorem exists_nonempty_dense_pure_curve_fibers
    [IsIntegral X] [IsIntegral S] (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsDominant f]
    (hgen : fiberDimension f (genericPoint S) = 1) :
    ∃ V : S.Opens, Nonempty V ∧ Dense (V : Set S) ∧
      ∀ s : V, Nonempty (f.fiber s.val) ∧ topologicalKrullDim (f.fiber s.val) = 1 ∧
        ∀ C : Set (f.fiber s.val), C ∈ irreducibleComponents (f.fiber s.val) →
          topologicalKrullDim C = 1 := by
  obtain ⟨V, hV, hVdense, hdim⟩ :=
    FiberDimensionGenericGlobal.exists_nonempty_dense_fiberDimension_eq_generic f
  refine ⟨V, hV, hVdense, ?_⟩
  intro s
  have hs : topologicalKrullDim (f.fiber s.val) = 1 := (hdim s).trans hgen
  refine ⟨(topologicalKrullDim_nonneg_iff _).mp (hs.symm ▸ zero_le_one), hs, ?_⟩
  intro C hC
  apply le_antisymm
  · exact (topologicalKrullDim_subspace_le _ C).trans hs.le
  · exact one_le_fiberComponentDimension_of_one_le_genericFiberDimension f hgen.ge s.val C hC

variable {k : Type u} [Field k]

/-- The actual internally constructed projective graph model has pure curve fibres on a constructed dense open. -/
theorem exists_projective_model_pure_curve_fibers_over_dense_open
    (p : X ⟶ Spec (.of k)) [IsVariety p] (hp : IsProjectiveOver p)
    (h : SeparableGenericSmoothness.FunctionFieldSeparablyGenerated p)
    (htr : letI := SeparableGenericSmoothness.functionFieldAlgebra p
      Algebra.Transcendental k X.functionField) :
    ∃ (n : ℕ) (Y : Scheme.{u}) (π : Y ⟶ X) (F : Y ⟶ projectiveSpace k n),
      IsModification π ∧ IsVariety (π ≫ p) ∧ IsProjectiveOver (π ≫ p) ∧
      IsProper F ∧ IsDominant F ∧ F ≫ projectiveSpaceStructure k n = π ≫ p ∧
      ∃ V : (projectiveSpace k n).Opens, Nonempty V ∧
        Dense (V : Set (projectiveSpace k n)) ∧
        ∀ s : V, Nonempty (F.fiber s.val) ∧ topologicalKrullDim (F.fiber s.val) = 1 ∧
          ∀ C : Set (F.fiber s.val), C ∈ irreducibleComponents (F.fiber s.val) →
            topologicalKrullDim C = 1 := by
  obtain ⟨n, Y, π, F, hπ, hY, hprojective, hproper, hdominant, htriangle, hgeneric, -, -⟩ :=
    ProjectiveCurveFibration.exists_projective_curve_fibration_model p hp h htr
  let : IsVariety (π ≫ p) := hY
  let : IsIntegral (projectiveSpace k n) := ProjectiveCurveFibration.projectiveSpace_isIntegral k n
  let : IsProper F := hproper
  let : IsDominant F := hdominant
  exact ⟨n, Y, π, F, hπ, hY, hprojective, hproper, hdominant, htriangle,
    exists_nonempty_dense_pure_curve_fibers F hgeneric⟩

end Hironaka.Geometry.ProjectiveCurveFibrationOpen
