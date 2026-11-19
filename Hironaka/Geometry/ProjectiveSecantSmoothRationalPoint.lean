import Hironaka.Geometry.ProjectiveSecantSmoothPoint
import Mathlib.FieldTheory.IsSepClosed

/-!
# Actual rational points of the original smooth source over a separably closed field
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.ProjectiveSecant

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An actual nonempty original smooth scheme over a separably closed original field internally supplies a genuine rational point, without any perfectness or residue-field certificate. -/
theorem exists_rational_smooth_scheme_point_of_isSepClosed
    (k : Type u) [Field k] [IsSepClosed k] {X : Scheme.{u}} [Nonempty X]
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] :
    ∃ s : Spec (CommRingCat.of k) ⟶ X, s ≫ f = 𝟙 _ := by
  obtain ⟨L, _, hsep, q, hq⟩ := exists_finite_separable_smooth_scheme_point k f
  let : Algebra.IsSeparable k L := hsep
  let e : k ≃ₐ[k] L := AlgEquiv.ofBijective (Algebra.ofId k L) (IsSepClosed.algebraMap_bijective k L)
  refine ⟨Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ q, ?_⟩
  rw [Category.assoc, hq, ← Spec.map_comp]
  have he : CommRingCat.ofHom (algebraMap k L) ≫ CommRingCat.ofHom e.symm.toRingHom = 𝟙 _ := by
    apply CommRingCat.hom_ext
    ext a
    exact e.symm.commutes a
  rw [he, Spec.map_id]

/-- Every actual nonempty specified original smooth open has an internally produced actual original rational scheme point in that same open, preserving the entire coefficient triangle. -/
theorem exists_rational_point_in_smooth_open_of_isSepClosed
    (k : Type u) [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) (hU : (U : Set X).Nonempty)
    [Smooth (U.ι ≫ f)] :
    ∃ s : Spec (CommRingCat.of k) ⟶ X, s ≫ f = 𝟙 _ ∧ s (⊥ : PrimeSpectrum k) ∈ U := by
  let : Nonempty U := hU.to_subtype
  obtain ⟨s, hs⟩ := exists_rational_smooth_scheme_point_of_isSepClosed k (U.ι ≫ f)
  exact ⟨s ≫ U.ι, by simpa only [Category.assoc] using hs, (s (⊥ : PrimeSpectrum k)).2⟩

end Hironaka.Geometry.ProjectiveSecant
