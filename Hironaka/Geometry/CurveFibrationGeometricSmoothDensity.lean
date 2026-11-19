import Hironaka.Geometry.CurveFibrationSmoothDensity
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Density of the original smooth locus after every residue-field extension

The same internally constructed dense base open works for every actual field
extension of every residue fibre. Native universal openness retains the actual
projections and the original relative smooth locus.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.CurveFibrationGeometricSmoothDensity

universe u

/-- Actual field scalar change pulls back every original dense subset densely. -/
theorem dense_fieldBaseChange_preimage
    {K : Type u} [Field K] {T : Scheme.{u}}
    (p : T ⟶ Spec (.of K)) (B : Set T) (hB : Dense B)
    (L : Type u) [Field L] (φ : K →+* L) :
    Dense ((pullback.fst p (Spec.map (CommRingCat.ofHom φ))) ⁻¹' B) :=
  hB.preimage (pullback.fst p (Spec.map (CommRingCat.ofHom φ))).isOpenMap

/-- The ORIGINAL smooth locus is dense on every actual field extension of every
residue fibre over the SAME internally constructed nonempty dense base open. -/
theorem exists_nonempty_dense_original_smoothLocus_geometricFiberwise_dense
    {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
    (f : X ⟶ S) [IsDominant f] [IsProper f] [LocallyOfFinitePresentation f]
    (hgen : FiberDimension.fiberDimension f (genericPoint S) = 1)
    (hsep : RelativeGenericSmoothness.FunctionFieldSeparablyGenerated f) :
    ∃ V : S.Opens, Nonempty V ∧ Dense (V : Set S) ∧
      ∀ s : V, ∀ (L : Type u) [Field L] (φ : S.residueField s.val →+* L),
        Dense (((pullback.fst (f.fiberToSpecResidueField s.val)
          (Spec.map (CommRingCat.ofHom φ))) ≫ f.fiberι s.val) ⁻¹' (f.smoothLocus : Set X)) := by
  obtain ⟨V, hV, hVdense, hdense⟩ :=
    CurveFibrationSmoothDensity.exists_nonempty_dense_original_smoothLocus_fiberwise_dense
      f hgen hsep
  refine ⟨V, hV, hVdense, ?_⟩
  intro s L inst φ
  exact dense_fieldBaseChange_preimage (f.fiberToSpecResidueField s.val)
    ((f.fiberι s.val) ⁻¹' (f.smoothLocus : Set X)) (hdense s) L φ

end Hironaka.Geometry.CurveFibrationGeometricSmoothDensity
