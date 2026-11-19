import Hironaka.Geometry.ProjectiveSecantSmoothPointAlgebra
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Actual finite separable scheme points of the same original nonempty smooth source open
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.ProjectiveSecant

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original nonempty smooth scheme internally produces an actual finite separable scheme point retaining its literal original field triangle. -/
theorem exists_finite_separable_smooth_scheme_point
    (k : Type u) [Field k] {X : Scheme.{u}} [Nonempty X]
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] :
    ∃ L : IntermediateField k (SeparableClosure k), FiniteDimensional k L ∧ Algebra.IsSeparable k L ∧
      ∃ q : Spec (CommRingCat.of L) ⟶ X,
        q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
  let x : X := Classical.choice inferInstance
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, _⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ (⊤ : X.Opens) from trivial) (⊤ : X.Opens).isOpen
  have hr : x ∈ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    exact hxV
  obtain ⟨Q, _⟩ := hr
  let : Nontrivial Γ(X, V) := PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨Q⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hV.fromSpec ≫ f)
  algebraize [φ.hom]
  have hg : Smooth (Spec.map φ) := hφ.symm ▸ inferInstance
  let : Algebra.Smooth k Γ(X, V) := RingHom.smooth_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp hg)
  obtain ⟨L, hfin, hsep, ⟨χ⟩⟩ := exists_finite_separable_smooth_algebra_point k Γ(X, V)
  refine ⟨L, hfin, hsep, Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ hV.fromSpec, ?_⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext fun c => χ.commutes c)

/-- From an actual nonempty original smooth open, internally choose a finite separable original field and an actual scheme point in that SAME original open, with its literal original coefficient triangle. -/
theorem exists_finite_separable_point_in_smooth_open
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) (hU : (U : Set X).Nonempty)
    [Smooth (U.ι ≫ f)] :
    ∃ L : IntermediateField k (SeparableClosure k), FiniteDimensional k L ∧ Algebra.IsSeparable k L ∧
      ∃ q : Spec (CommRingCat.of L) ⟶ X,
        q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k L)) ∧
        q (⊥ : PrimeSpectrum L) ∈ U := by
  let : Nonempty U := hU.to_subtype
  obtain ⟨L, hfin, hsep, q, hq⟩ := exists_finite_separable_smooth_scheme_point k (U.ι ≫ f)
  exact ⟨L, hfin, hsep, q ≫ U.ι, by simpa only [Category.assoc] using hq,
    (q (⊥ : PrimeSpectrum L)).property⟩

end Hironaka.Geometry.ProjectiveSecant
