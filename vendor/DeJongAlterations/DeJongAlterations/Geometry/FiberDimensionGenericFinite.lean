import DeJongAlterations.Algebra.FunctionFieldDimension
import DeJongAlterations.Geometry.FiberDimension
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Actual finite fiber projections and relative affine-space dimensions

Finite surjective maps to reduced affine schemes preserve actual dimension.
Their native iterated-pullback fiber projections remain finite and surjective.
The literal fibers of relative affine space are compared with polynomial
spectra over the actual residue fields, giving their precise dimension.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

namespace DeJongAlterations.Geometry.FiberDimensionGenericFinite

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An actual isomorphism of scheme arrows identifies their actual fiber topologies. -/
def fiberHomeoOfArrowIso {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk g) (s : Y) :
    f.fiber s ≃ₜ g.fiber ((Arrow.rightFunc.mapIso e).hom s) := by
  let iX : X ≅ X' := Arrow.leftFunc.mapIso e
  let iY : Y ≅ Y' := Arrow.rightFunc.mapIso e
  refine (f.fiberHomeo s).trans ((iX.hom.homeomorph.subtype ?_).trans
    (g.fiberHomeo (iY.hom s)).symm)
  intro x
  change f x = s ↔ g (iX.hom x) = iY.hom s
  have hw : g (iX.hom x) = iY.hom (f x) := by
    have H : iX.hom ≫ g = f ≫ iY.hom := e.hom.w
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
    exact congrArg (fun h : X ⟶ Y' => h x) H
  rw [hw]
  exact iY.hom.injective.eq_iff.symm

/-- Native fiber dimension is invariant under an actual isomorphism of scheme arrows. -/
theorem fiberDimension_eq_of_arrowIso {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk g) (s : Y) :
    FiberDimension.fiberDimension f s =
      FiberDimension.fiberDimension g ((Arrow.rightFunc.mapIso e).hom s) :=
  IsHomeomorph.topologicalKrullDim_eq _ (fiberHomeoOfArrowIso e s).isHomeomorph

/-- Native affine scheme dimension equals its actual global coordinate-ring dimension. -/
theorem topologicalKrullDim_eq_ringKrullDim_of_isAffine (X : Scheme.{u}) [IsAffine X] :
    topologicalKrullDim X = ringKrullDim Γ(X, ⊤) := by
  rw [IsHomeomorph.topologicalKrullDim_eq _ X.isoSpec.hom.homeomorph.isHomeomorph]
  exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _

/-- Actual finite surjective maps to reduced affine schemes preserve dimension. -/
theorem topologicalKrullDim_eq_of_finite_surjective {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsAffine Y] [IsReduced Y] [IsFinite f] [Surjective f] :
    topologicalKrullDim X = topologicalKrullDim Y := by
  have : IsAffine X := isAffine_of_isAffineHom f
  have : IsSchemeTheoreticallyDominant f := IsSchemeTheoreticallyDominant.of_isDominant f
  have hf : f.appTop.hom.IsIntegral := f.finite_appTop.to_isIntegral
  have hi : Function.Injective f.appTop.hom := by
    simpa [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] using f.app_injective ⊤
  rw [topologicalKrullDim_eq_ringKrullDim_of_isAffine,
    topologicalKrullDim_eq_ringKrullDim_of_isAffine]
  exact le_antisymm
    (Algebra.FunctionFieldDimension.ringKrullDim_le_of_isIntegral f.appTop.hom hf)
    (Algebra.FunctionFieldDimension.ringKrullDim_le_of_isIntegral_of_injective f.appTop.hom hf hi)

/-- The actual fiber comparison is the base-change projection through the native pasted pullback. -/
def fiberProjection {X Y S : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S) (s : S) :
    (f ≫ q).fiber s ⟶ q.fiber s :=
  (pullbackRightPullbackFstIso q (S.fromSpecResidueField s) f).inv ≫
    pullback.snd f (q.fiberι s)

/-- The literal fiber inclusion square commutes. -/
@[reassoc (attr := simp)]
theorem fiberProjection_fiberι {X Y S : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S) (s : S) :
    fiberProjection f q s ≫ q.fiberι s = (f ≫ q).fiberι s ≫ f :=
  pullbackRightPullbackFstIso_inv_snd_fst q (S.fromSpecResidueField s) f

/-- The actual fiber projection square is Cartesian, not a supplied fiber certificate. -/
theorem fiberProjection_isPullback {X Y S : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S) (s : S) :
    IsPullback (fiberProjection f q s) ((f ≫ q).fiberι s) (q.fiberι s) f := by
  let e := pullbackRightPullbackFstIso q (S.fromSpecResidueField s) f
  refine (IsPullback.of_hasPullback f (q.fiberι s)).flip.of_iso e
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [e, fiberProjection]
  · simpa only [e, Scheme.Hom.fiberι, Iso.refl_hom, Category.comp_id] using
      (pullbackRightPullbackFstIso_hom_fst q (S.fromSpecResidueField s) f).symm
  · simp
  · simp

instance fiberProjection_isFinite {X Y S : Scheme.{u}} (f : X ⟶ Y)
    (q : Y ⟶ S) [IsFinite f] (s : S) : IsFinite (fiberProjection f q s) := by
  unfold fiberProjection
  infer_instance

instance fiberProjection_surjective {X Y S : Scheme.{u}} (f : X ⟶ Y)
    (q : Y ⟶ S) [Surjective f] (s : S) : Surjective (fiberProjection f q s) := by
  unfold fiberProjection
  infer_instance

/-- Finite surjective projection to an affine reduced actual fiber preserves its dimension. -/
theorem fiberDimension_comp_eq {X Y S : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S)
    [IsFinite f] [Surjective f] (s : S) [IsAffine (q.fiber s)] [IsReduced (q.fiber s)] :
    FiberDimension.fiberDimension (f ≫ q) s = FiberDimension.fiberDimension q s :=
  topologicalKrullDim_eq_of_finite_surjective (fiberProjection f q s)

/-- The actual relative affine-space structure map is the spectrum of the original constants. -/
def affineSpaceStructure (R : Type u) [CommRing R] (n : ℕ) :
    Spec (.of (MvPolynomial (Fin n) R)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R)))

/-- The literal scheme-theoretic affine-space fiber is the polynomial spectrum over its residue field. -/
def affineSpaceFiberIso (R : Type u) [CommRing R] (n : ℕ) (s : PrimeSpectrum R) :
    (affineSpaceStructure R n).fiber s ≅ Spec (.of (MvPolynomial (Fin n) s.asIdeal.ResidueField)) :=
  (Arrow.leftFunc.mapIso (Spec.fiberToSpecResidueFieldIso R (MvPolynomial (Fin n) R) s)) ≪≫
    Scheme.Spec.mapIso (MvPolynomial.algebraTensorAlgEquiv (σ := Fin n)
      R s.asIdeal.ResidueField).toRingEquiv.toCommRingCatIso.symm.op

instance affineSpace_fiber_isAffine (R : Type u) [CommRing R] (n : ℕ) (s : PrimeSpectrum R) :
    IsAffine ((affineSpaceStructure R n).fiber s) :=
  IsAffine.of_isIso (affineSpaceFiberIso R n s).hom

instance affineSpace_fiber_isReduced (R : Type u) [CommRing R] (n : ℕ) (s : PrimeSpectrum R) :
    IsReduced ((affineSpaceStructure R n).fiber s) :=
  isReduced_of_isOpenImmersion (affineSpaceFiberIso R n s).hom

/-- Every actual fiber of relative affine n-space has dimension n. -/
theorem affineSpace_fiber_dimension (R : Type u) [CommRing R] (n : ℕ) (s : PrimeSpectrum R) :
    FiberDimension.fiberDimension (affineSpaceStructure R n) s = n := by
  unfold FiberDimension.fiberDimension
  rw [IsHomeomorph.topologicalKrullDim_eq _ (affineSpaceFiberIso R n s).hom.homeomorph.isHomeomorph]
  change topologicalKrullDim (PrimeSpectrum (MvPolynomial (Fin n) s.asIdeal.ResidueField)) = n
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  simp

/-- The actual fibers of a finite surjective projection to relative affine space have its dimension. -/
theorem finiteProjection_fiber_dimension {R : Type u} [CommRing R] {n : ℕ}
    {X : Scheme.{u}} (f : X ⟶ Spec (.of (MvPolynomial (Fin n) R)))
    [IsFinite f] [Surjective f] (s : PrimeSpectrum R) :
    FiberDimension.fiberDimension (f ≫ affineSpaceStructure R n) s = n :=
  (fiberDimension_comp_eq f (affineSpaceStructure R n) s).trans (affineSpace_fiber_dimension R n s)

end DeJongAlterations.Geometry.FiberDimensionGenericFinite
