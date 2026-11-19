import Hironaka.Geometry.ProjectiveSecantGeometricDenseSmooth
import Hironaka.Geometry.ProjectiveSecantSmoothRationalPoint

/-!
# The original dense geometric open internally supplies actual rational smooth points on every original component
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.ProjectiveSecant

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual original geometric hypotheses internally supply a rational smooth scheme point in each actual original component and original geometric open; no point or separability certificate is assumed. -/
theorem exists_original_rational_smooth_component_point
    (k : Type u) [Field k] [IsSepClosed k] (m : ℕ) {X : Scheme.{u}}
    (i : X ⟶ projectiveSpace k m) [IsClosedImmersion i]
    (U : X.Opens) (hU : Dense (U : Set X))
    [GeometricallyReduced (U.ι ≫ (i ≫ projectiveSpaceStructure k m))]
    (C : Set X) (hC : C ∈ irreducibleComponents X) :
    ∃ s : Spec (CommRingCat.of k) ⟶ X,
      s (⊥ : PrimeSpectrum k) ∈ C ∧ s (⊥ : PrimeSpectrum k) ∈ U ∧
      (s ≫ i) ≫ projectiveSpaceStructure k m = 𝟙 _ ∧
      s (⊥ : PrimeSpectrum k) ∈ (i ≫ projectiveSpaceStructure k m).smoothLocus := by
  let W := originalComponentGeometricOpen k m i C hC U
  let : IsIntegral W := originalComponentGeometricOpen_isIntegral k m i C hC U hU
  let : GeometricallyReduced (W.ι ≫ (i ≫ projectiveSpaceStructure k m)) :=
    originalComponentGeometricOpen_geometricallyReduced k m i C hC U
  let f := W.ι ≫ (i ≫ projectiveSpaceStructure k m)
  have hne : (f.smoothLocus : Set W).Nonempty :=
    ⟨genericPoint W, genericPoint_mem_smoothLocus_of_geometricallyReduced f⟩
  let : Smooth (f.smoothLocus.ι ≫ f) := GenericSmoothness.smooth_smoothLocus f
  obtain ⟨t, ht, hts⟩ := exists_rational_point_in_smooth_open_of_isSepClosed k f f.smoothLocus hne
  have hts' : W.ι (t (⊥ : PrimeSpectrum k)) ∈ (i ≫ projectiveSpaceStructure k m).smoothLocus := by
    change t (⊥ : PrimeSpectrum k) ∈ (W.ι ≫ (i ≫ projectiveSpaceStructure k m)).smoothLocus at hts
    rwa [← Scheme.Hom.preimage_smoothLocus_eq, Scheme.Hom.mem_preimage] at hts
  refine ⟨t ≫ W.ι,
    originalComponentGeometricOpen_subset_component k m i C hC U (t (⊥ : PrimeSpectrum k)).2,
    originalComponentGeometricOpen_le_original k m i C hC U (t (⊥ : PrimeSpectrum k)).2, ?_, hts'⟩
  simpa only [Category.assoc] using ht

end Hironaka.Geometry.ProjectiveSecant
