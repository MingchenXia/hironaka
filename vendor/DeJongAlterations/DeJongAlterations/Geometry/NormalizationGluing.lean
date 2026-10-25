/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.Algebra.IntegralClosureLocalization
import DeJongAlterations.Geometry.RegularCurve
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski

/-!
# Normalization in the canonical function field

The actual integral closures of nonempty affine coordinate rings in the canonical
function field form a native relative gluing datum. No field compatibility or
scheme gluing certificate is supplied as an input.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

set_option autoImplicit false

namespace DeJongAlterations.Geometry.NormalizationGluing

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The native affine Zariski site restricted to its nonempty affine opens. -/
def NonemptyAffineOpen (X : Scheme.{u}) := {U : X.AffineZariskiSite // Nonempty U.1}

instance nonempty_nonemptyAffineOpen {X : Scheme.{u}} (U : NonemptyAffineOpen X) :
    Nonempty U.1.1 := U.2

instance nonemptyAffineOpenPartialOrder {X : Scheme.{u}} : PartialOrder (NonemptyAffineOpen X) :=
  inferInstanceAs (PartialOrder {U : X.AffineZariskiSite // Nonempty U.1})

/-- The actual inclusion of the nonempty affine site into the full affine site. -/
def siteFunctor (X : Scheme.{u}) : NonemptyAffineOpen X ⥤ X.AffineZariskiSite :=
  (show Monotone (Subtype.val : NonemptyAffineOpen X → X.AffineZariskiSite) from
    fun _ _ h ↦ h).functor

variable {X : Scheme.{u}} [IsIntegral X]

private def fullCoefficientMap {U V : X.AffineZariskiSite} (h : U ⟶ V) :
    Γ(X, V.1) →+* Γ(X, U.1) :=
  (X.presheaf.map ((Scheme.AffineZariskiSite.toOpensFunctor X).map h).op).hom

omit [IsIntegral X] in
private theorem fullCoefficientMap_isLocalization {U V : X.AffineZariskiSite} (h : U ⟶ V) :
    ∃ s : Γ(X, V.1), letI := (fullCoefficientMap h).toAlgebra
      IsLocalization.Away s Γ(X, U.1) := by
  obtain ⟨s, hs⟩ := h.le
  refine ⟨s, ?_⟩
  have hU : U = V.basicOpen s := Subtype.ext hs.symm
  subst U
  have hh : h = homOfLE (V.basicOpen_le s) := Subsingleton.elim _ _
  subst h
  exact V.2.isLocalization_basicOpen s

/-- Actual restriction on the coordinate rings of nonempty affine opens. -/
def coefficientMap {U V : NonemptyAffineOpen X} (h : U ⟶ V) :
    Γ(X, V.1.1) →+* Γ(X, U.1.1) :=
  fullCoefficientMap ((siteFunctor X).map h)

/-- The canonical function-field maps commute with actual affine restriction. -/
theorem coefficientMap_functionField {U V : NonemptyAffineOpen X} (h : U ⟶ V) :
    (algebraMap Γ(X, U.1.1) X.functionField).comp (coefficientMap h) =
      algebraMap Γ(X, V.1.1) X.functionField := by
  change (X.presheaf.map _ ≫ X.germToFunctionField U.1.1).hom =
    (X.germToFunctionField V.1.1).hom
  exact congrArg CommRingCat.Hom.hom (X.presheaf.germ_res
    ((Scheme.AffineZariskiSite.toOpensFunctor X).map ((siteFunctor X).map h))
    (genericPoint X) _)

/-- The coefficient scalar tower is induced by the actual restriction and canonical germs. -/
theorem coefficientScalarTower {U V : NonemptyAffineOpen X} (h : U ⟶ V) :
    letI := (coefficientMap h).toAlgebra
    IsScalarTower Γ(X, V.1.1) Γ(X, U.1.1) X.functionField := by
  let := (coefficientMap h).toAlgebra
  exact IsScalarTower.of_algebraMap_eq' (coefficientMap_functionField h).symm

omit [IsIntegral X] in
/-- Every arrow of the nonempty affine site is actual principal coefficient localization. -/
theorem coefficientMap_isLocalization {U V : NonemptyAffineOpen X} (h : U ⟶ V) :
    ∃ s : Γ(X, V.1.1), letI := (coefficientMap h).toAlgebra
      IsLocalization.Away s Γ(X, U.1.1) := by
  exact fullCoefficientMap_isLocalization ((siteFunctor X).map h)

/-- The actual integral closure of an affine coordinate ring in the common function field. -/
abbrev closureRing (U : NonemptyAffineOpen X) := integralClosure Γ(X, U.1.1) X.functionField

/-- The identity on the common field induces the actual integral-closure transition map. -/
def closureMap {U V : NonemptyAffineOpen X} (h : U ⟶ V) :
    closureRing V →+* closureRing U := by
  letI := (coefficientMap h).toAlgebra
  letI := coefficientScalarTower h
  exact Algebra.IntegralClosureLocalization.closureMap

@[simp]
theorem closureMap_coe {U V : NonemptyAffineOpen X} (h : U ⟶ V) (x : closureRing V) :
    (closureMap h x : X.functionField) = (x : X.functionField) := rfl

@[simp]
theorem closureMap_id (U : NonemptyAffineOpen X) : closureMap (𝟙 U) = RingHom.id _ := by
  ext x
  rfl

@[simp]
theorem closureMap_comp {U V W : NonemptyAffineOpen X} (h : U ⟶ V) (k : V ⟶ W) :
    closureMap (h ≫ k) = (closureMap h).comp (closureMap k) := by
  ext x
  rfl

/-- The integral-closure transition preserves the actual coordinate-ring coefficients. -/
theorem closureMap_algebraMap {U V : NonemptyAffineOpen X} (h : U ⟶ V) :
    (closureMap h).comp (algebraMap Γ(X, V.1.1) (closureRing V)) =
      (algebraMap Γ(X, U.1.1) (closureRing U)).comp (coefficientMap h) := by
  ext r
  exact congrArg (fun f : Γ(X, V.1.1) →+* X.functionField ↦ f r)
    (coefficientMap_functionField h).symm

/-- Each actual integral-closure transition is localization at an actual coefficient. -/
theorem closureMap_isLocalization {U V : NonemptyAffineOpen X} (h : U ⟶ V) :
    ∃ s : Γ(X, V.1.1), letI := (closureMap h).toAlgebra
      IsLocalization.Away (algebraMap Γ(X, V.1.1) (closureRing V) s) (closureRing U) := by
  obtain ⟨s, hs⟩ := coefficientMap_isLocalization h
  let := (coefficientMap h).toAlgebra
  let := coefficientScalarTower h
  have : IsLocalization.Away s Γ(X, U.1.1) := hs
  have hunit : IsUnit (algebraMap Γ(X, V.1.1) X.functionField s) := by
    rw [IsScalarTower.algebraMap_apply Γ(X, V.1.1) Γ(X, U.1.1) X.functionField s]
    exact (IsLocalization.Away.algebraMap_isUnit (S := Γ(X, U.1.1)) s).map _
  refine ⟨s, ?_⟩
  exact Algebra.IntegralClosureLocalization.closure_isLocalization s hunit

/-- The genuine affine normalization diagram in the common canonical function field. -/
def affineDiagram (X : Scheme.{u}) [IsIntegral X] : NonemptyAffineOpen X ⥤ Scheme.{u} where
  obj U := Spec (CommRingCat.of (closureRing U))
  map h := Spec.map (CommRingCat.ofHom (closureMap h))
  map_id U := by simp only [closureMap_id, CommRingCat.ofHom_id, Spec.map_id]
  map_comp h k := by
    rw [closureMap_comp, CommRingCat.ofHom_comp, Spec.map_comp]

/-- The actual affine normalization structure map, induced by its coefficient inclusion. -/
def affineStructure (U : NonemptyAffineOpen X) :
    Spec (CommRingCat.of (closureRing U)) ⟶ Spec Γ(X, U.1.1) :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1.1) (closureRing U)))

/-- The actual structure maps form a natural transformation over the spectrum diagram. -/
def structureNatTrans (X : Scheme.{u}) [IsIntegral X] : affineDiagram X ⟶
    siteFunctor X ⋙ Scheme.AffineZariskiSite.toOpensFunctor X ⋙
      X.presheaf.rightOp ⋙ Scheme.Spec where
  app U := affineStructure U
  naturality {U V} h := by
    change Spec.map (CommRingCat.ofHom (closureMap h)) ≫ affineStructure V =
      affineStructure U ≫ Spec.map (CommRingCat.ofHom (coefficientMap h))
    unfold affineStructure
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) (closureMap_algebraMap h)

/-- Every actual affine normalization square is Cartesian, by coefficient localization. -/
theorem structureNatTrans_equifibered (X : Scheme.{u}) [IsIntegral X] :
    (structureNatTrans X).Equifibered := by
  intro U V h
  obtain ⟨s, hs⟩ := coefficientMap_isLocalization h
  let := (coefficientMap h).toAlgebra
  let := coefficientScalarTower h
  have : IsLocalization.Away s Γ(X, U.1.1) := hs
  have hunit : IsUnit (algebraMap Γ(X, V.1.1) X.functionField s) := by
    rw [IsScalarTower.algebraMap_apply Γ(X, V.1.1) Γ(X, U.1.1) X.functionField s]
    exact (IsLocalization.Away.algebraMap_isUnit (S := Γ(X, U.1.1)) s).map _
  let := (closureMap h).toAlgebra
  have : IsLocalization.Away (algebraMap Γ(X, V.1.1) (closureRing V) s) (closureRing U) :=
    Algebra.IntegralClosureLocalization.closure_isLocalization s hunit
  let q := Spec.map (CommRingCat.ofHom (coefficientMap h))
  let p := Spec.map (CommRingCat.ofHom (closureMap h))
  let : IsOpenImmersion q := IsOpenImmersion.of_isLocalization s
  let : IsOpenImmersion p := IsOpenImmersion.of_isLocalization
    (algebraMap Γ(X, V.1.1) (closureRing V) s)
  have hq : q.opensRange = PrimeSpectrum.basicOpen s := by
    apply SetLike.coe_injective
    exact PrimeSpectrum.localization_away_comap_range Γ(X, U.1.1) s
  have hp : p.opensRange =
      PrimeSpectrum.basicOpen (algebraMap Γ(X, V.1.1) (closureRing V) s) := by
    apply SetLike.coe_injective
    exact PrimeSpectrum.localization_away_comap_range (closureRing U) _
  change IsPullback p (affineStructure U) (affineStructure V) q
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback
  · exact (structureNatTrans X).naturality h
  · rw [hq, hp]
    rfl

/-- The native cover of X by its nonempty affine opens. -/
abbrev nonemptyAffineCover (X : Scheme.{u}) : X.OpenCover where
  I₀ := NonemptyAffineOpen X
  X U := U.1.1.toScheme
  f U := U.1.1.ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    obtain ⟨U, hxU⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_affineOpens_eq_top X).ge (Set.mem_univ x))
    exact ⟨⟨⟨U.1, U.2⟩, ⟨⟨x, hxU⟩⟩⟩, ⟨x, hxU⟩, rfl⟩

/-- The nonempty affine site retains the native locally directed intersections. -/
instance nonemptyAffineCover_locallyDirected (X : Scheme.{u}) :
    (nonemptyAffineCover X).LocallyDirected where
  trans h := X.homOfLE (Scheme.AffineZariskiSite.toOpens_mono h.le)
  directed {U V} x := by
    obtain ⟨W, hWU, hWV, y, hy⟩ :=
      (Scheme.AffineZariskiSite.directedCover X).exists_lift_trans_eq
        (i := U.1) (j := V.1) x
    exact ⟨⟨W, ⟨y⟩⟩, homOfLE hWU.le, homOfLE hWV.le, y, hy⟩

/-- The actual common-function-field integral closures produce native relative gluing data. -/
def relativeGluingData (X : Scheme.{u}) [IsIntegral X] :
    (nonemptyAffineCover X).RelativeGluingData where
  functor := affineDiagram X
  natTrans := structureNatTrans X ≫
    Functor.whiskerLeft (siteFunctor X) (Scheme.AffineZariskiSite.restrictIsoSpec X).inv
  equifibered := (structureNatTrans_equifibered X).comp (.of_isIso _)

/-- The global normalization constructed by gluing actual integral closures in K(X). -/
def normalization (X : Scheme.{u}) [IsIntegral X] : Scheme.{u} :=
  (relativeGluingData X).glued

/-- The genuine global normalization structure map to the original scheme. -/
def normalizationStructure (X : Scheme.{u}) [IsIntegral X] : normalization X ⟶ X :=
  (relativeGluingData X).toBase

/-- The canonical open cover by the actual spectra of integral closures. -/
abbrev normalizationCover (X : Scheme.{u}) [IsIntegral X] : (normalization X).OpenCover :=
  (relativeGluingData X).cover

/-- The native inclusion of an actual affine normalization into the global normalization. -/
def chartInclusion (X : Scheme.{u}) [IsIntegral X] (U : NonemptyAffineOpen X) :
    Spec (CommRingCat.of (closureRing U)) ⟶ normalization X := (normalizationCover X).f U

@[simp]
theorem normalizationCover_X (U : NonemptyAffineOpen X) :
    (normalizationCover X).X U = Spec (CommRingCat.of (closureRing U)) := rfl

@[simp]
theorem normalizationCover_f (U : NonemptyAffineOpen X) :
    (normalizationCover X).f U = chartInclusion X U := rfl

instance chartInclusion_isOpenImmersion (U : NonemptyAffineOpen X) :
    IsOpenImmersion (chartInclusion X U) :=
  inferInstanceAs (IsOpenImmersion ((normalizationCover X).f U))

/-- The actual affine normalizations have the prescribed global structure triangles. -/
@[reassoc]
theorem chartInclusion_structure (U : NonemptyAffineOpen X) :
    chartInclusion X U ≫ normalizationStructure X = affineStructure U ≫ U.1.2.fromSpec := by
  have h := (relativeGluingData X).ι_toBase U
  change chartInclusion X U ≫ normalizationStructure X =
    (affineStructure U ≫ U.1.2.isoSpec.inv) ≫ U.1.1.ι at h
  exact h.trans (by rw [Category.assoc, IsAffineOpen.isoSpec_inv_ι])

/-- The actual affine chart is the genuine pullback over its original base open subscheme. -/
theorem isPullback_chartOpen (U : NonemptyAffineOpen X) :
    IsPullback (affineStructure U ≫ U.1.2.isoSpec.inv)
      (chartInclusion X U) U.1.1.ι (normalizationStructure X) :=
  (relativeGluingData X).isPullback_natTrans_ι_toBase U

/-- The actual common-field affine normalization is the pullback over Spec Γ(U). -/
theorem isPullback_chart (U : NonemptyAffineOpen X) :
    IsPullback (affineStructure U) (chartInclusion X U)
      U.1.2.fromSpec (normalizationStructure X) := by
  refine (isPullback_chartOpen U).of_iso (Iso.refl _) U.1.2.isoSpec
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simpa only [Iso.refl_hom, Category.comp_id] using U.1.2.isoSpec_hom_fromSpec.symm
  · simp

/-- The affine normalization chart image is precisely the inverse image of the original open. -/
theorem chartInclusion_opensRange (U : NonemptyAffineOpen X) :
    (chartInclusion X U).opensRange = normalizationStructure X ⁻¹ᵁ U.1.1 := by
  have h := (relativeGluingData X).toBase_preimage_eq_opensRange_ι U
  change normalizationStructure X ⁻¹ᵁ U.1.1.ι.opensRange = (chartInclusion X U).opensRange at h
  rw [Scheme.Opens.opensRange_ι] at h
  exact h.symm

/-- Every actual affine normalization ring is integrally closed in its fraction field. -/
theorem closureRing_isIntegrallyClosed (U : NonemptyAffineOpen X) :
    IsIntegrallyClosed (closureRing U) := by
  let : IsFractionRing Γ(X, U.1.1) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U.1.1 U.1.2
  exact integralClosure.isIntegrallyClosedOfFiniteExtension X.functionField

/-- The actual global normalization is normal on its genuine local rings. -/
theorem normalization_isNormalScheme (X : Scheme.{u}) [IsIntegral X] :
    IsNormalScheme (normalization X) := by
  intro x
  let C := normalizationCover X
  obtain ⟨y, hy⟩ := C.covers x
  let U : NonemptyAffineOpen X := C.idx x
  let := closureRing_isIntegrallyClosed U
  have hnormal := isNormalScheme_spec (closureRing U) y
  let : IsDomain ((C.X U).presheaf.stalk y) := hnormal.1
  let : IsIntegrallyClosed ((C.X U).presheaf.stalk y) := hnormal.2
  let e := (asIso ((C.f U).stalkMap y)).commRingCatIsoToRingEquiv
  have h : IsDomain ((normalization X).presheaf.stalk (C.f U y)) ∧
      IsIntegrallyClosed ((normalization X).presheaf.stalk (C.f U y)) :=
    ⟨MulEquiv.isDomain _ e.toMulEquiv, IsIntegrallyClosed.of_equiv e.symm⟩
  rw [hy] at h
  exact h

end

end DeJongAlterations.Geometry.NormalizationGluing
