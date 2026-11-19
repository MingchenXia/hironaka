import Hironaka.Geometry.RelativeNoetherNormalization
import Hironaka.Geometry.FiberDimensionGenericRestriction

/-!
# Constant actual fiber dimension on a dense open of an affine integral base

Actual relative Noether normalization produces the finite projection and
computes the fibers of the original principal-open restriction. Native
restriction-fiber isomorphisms and the actual affine spectrum arrow then
give dimensions of the original full fibers over a nonempty dense open.
No finite projection or fiber dimension is supplied by the caller.
This is not general upper semicontinuity or the componentwise lower bound.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.FiberDimensionGenericAffine

open FiberDimensionGenericFinite FiberDimensionGenericRestriction

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Internally computed dimensions of the original full affine fibers on a nonzero principal base open. -/
theorem exists_nonzero_constant_fiberDimension_spec
    (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
    [Algebra R A] [Algebra.FiniteType R A] (hinj : Function.Injective (algebraMap R A)) :
    ∃ b : R, b ≠ 0 ∧ ∃ n : ℕ, Nonempty (PrimeSpectrum.basicOpen b) ∧
      Dense (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum R)) ∧
      ∀ s : PrimeSpectrum.basicOpen b,
        FiberDimension.fiberDimension (AffineGenericFlatness.affineStructure R A) s.val = n := by
  obtain ⟨b, hb, n, hne, hdense, hdim⟩ :=
    RelativeNoetherNormalization.exists_nonzero_constant_fiberDimension_morphismRestrict R A hinj
  refine ⟨b, hb, n, hne, hdense, fun s => ?_⟩
  exact (fiberDimension_morphismRestrict
    (AffineGenericFlatness.affineStructure R A) (PrimeSpectrum.basicOpen b) s).symm.trans (hdim s)

/-- A dominant locally finite-type morphism of affine integral schemes internally constructs
a nonempty dense open where both the original and the restricted actual fibers have constant dimension. -/
theorem exists_nonempty_dense_constant_fiberDimension {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsDominant f] :
    ∃ U : Y.Opens, Nonempty U ∧ Dense (U : Set Y) ∧ ∃ n : ℕ,
      (∀ s : U, FiberDimension.fiberDimension f s.val = n) ∧
      ∀ s : U, FiberDimension.fiberDimension (f ∣_ U) s = n := by
  let R : Type u := Γ(Y, ⊤)
  let A : Type u := Γ(X, ⊤)
  let : Algebra R A := f.appTop.hom.toAlgebra
  have : IsDomain R := inferInstance
  have : IsDomain A := inferInstance
  have : IsAffineHom f := isAffineHom_of_isAffine f
  have : IsSchemeTheoreticallyDominant f := IsSchemeTheoreticallyDominant.of_isDominant f
  have hinj : Function.Injective (algebraMap R A) := by
    change Function.Injective f.appTop.hom
    simpa [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] using f.app_injective ⊤
  have : Algebra.FiniteType R A := RingHom.finiteType_algebraMap.mp
    (HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f inferInstance)
  obtain ⟨b, hb, n, hne, hdense, hdim⟩ := exists_nonzero_constant_fiberDimension_spec R A hinj
  let U : Y.Opens := Y.isoSpec.hom ⁻¹ᵁ PrimeSpectrum.basicOpen b
  have hU : Nonempty U := by
    obtain ⟨s⟩ := hne
    refine ⟨⟨Y.isoSpec.inv s.val, ?_⟩⟩
    change Y.isoSpec.hom (Y.isoSpec.inv s.val) ∈ PrimeSpectrum.basicOpen b
    simp [← Scheme.Hom.comp_apply]
  have hUdense : Dense (U : Set Y) := by
    apply U.isOpen.dense
    obtain ⟨s⟩ := hU
    exact ⟨s.val, s.property⟩
  have horig (s : U) : FiberDimension.fiberDimension f s.val = n := by
    have hcomp := fiberDimension_eq_of_arrowIso (arrowIsoSpecΓOfIsAffine f) s.val
    change FiberDimension.fiberDimension f s.val =
      FiberDimension.fiberDimension (AffineGenericFlatness.affineStructure R A)
        (Y.isoSpec.hom s.val) at hcomp
    exact hcomp.trans (hdim ⟨Y.isoSpec.hom s.val, s.property⟩)
  exact ⟨U, hU, hUdense, n, horig,
    fun s => (fiberDimension_morphismRestrict f U s).trans (horig s)⟩

end Hironaka.Geometry.FiberDimensionGenericAffine
