import DeJongAlterations.Geometry.NormalizationGluing
import DeJongAlterations.Algebra.IntegralClosureFiniteType

/-!
# Native normalization in a specified function-field extension

The ambient field and its actual canonical function-field algebra are inputs.
All affine coefficient embeddings, restrictions and Cartesian gluing squares
are constructed from the original scheme's actual germs.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

set_option autoImplicit false

namespace DeJongAlterations.Geometry.NormalizationInExtension

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev NonemptyAffineOpen := NormalizationGluing.NonemptyAffineOpen
abbrev siteFunctor := NormalizationGluing.siteFunctor
abbrev nonemptyAffineCover := NormalizationGluing.nonemptyAffineCover
abbrev coefficientMap := @NormalizationGluing.coefficientMap

variable {X : Scheme.{u}} [IsIntegral X] (L : Type u) [Field L] [Algebra X.functionField L]

/-- Canonical coefficients in the specified field, through the actual generic germ. -/
abbrev sectionsAlgebra (U : X.Opens) [Nonempty U] : Algebra Γ(X, U) L :=
  ((algebraMap X.functionField L).comp (algebraMap Γ(X, U) X.functionField)).toAlgebra

attribute [local instance] sectionsAlgebra

/-- The actual section embeddings and specified field extension form their canonical tower. -/
instance sectionsScalarTower (U : X.Opens) [Nonempty U] :
    IsScalarTower Γ(X, U) X.functionField L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Actual affine restrictions preserve the specified ambient coefficient embedding. -/
theorem coefficientMap_extension {U V : NonemptyAffineOpen X} (h : U ⟶ V) :
    (algebraMap Γ(X, U.1.1) L).comp (coefficientMap h) = algebraMap Γ(X, V.1.1) L := by
  change (algebraMap X.functionField L).comp
      ((algebraMap Γ(X, U.1.1) X.functionField).comp (coefficientMap h)) = _
  rw [NormalizationGluing.coefficientMap_functionField h]
  rfl

/-- The actual restriction supplies the compatible ambient scalar tower. -/
theorem coefficientScalarTower {U V : NonemptyAffineOpen X} (h : U ⟶ V) :
    letI := (coefficientMap h).toAlgebra
    IsScalarTower Γ(X, V.1.1) Γ(X, U.1.1) L := by
  let := (coefficientMap h).toAlgebra
  exact IsScalarTower.of_algebraMap_eq' (coefficientMap_extension L h).symm

abbrev coefficientMap_isLocalization := @NormalizationGluing.coefficientMap_isLocalization

/-- The actual integral closure of an affine coordinate ring in the specified common field. -/
abbrev closureRing (U : NonemptyAffineOpen X) := integralClosure Γ(X, U.1.1) L

/-- The identity on the common field induces the actual integral-closure transition map. -/
def closureMap {U V : NonemptyAffineOpen X} (h : U ⟶ V) :
    closureRing L V →+* closureRing L U := by
  letI := (coefficientMap h).toAlgebra
  letI := coefficientScalarTower L h
  exact Algebra.IntegralClosureLocalization.closureMap

@[simp]
theorem closureMap_coe {U V : NonemptyAffineOpen X} (h : U ⟶ V) (x : closureRing L V) :
    (closureMap L h x : L) = (x : L) := rfl

@[simp]
theorem closureMap_id (U : NonemptyAffineOpen X) : closureMap L (𝟙 U) = RingHom.id _ := by
  ext x
  rfl

@[simp]
theorem closureMap_comp {U V W : NonemptyAffineOpen X} (h : U ⟶ V) (k : V ⟶ W) :
    closureMap L (h ≫ k) = (closureMap L h).comp (closureMap L k) := by
  ext x
  rfl

/-- The integral-closure transition preserves the actual coordinate-ring coefficients. -/
theorem closureMap_algebraMap {U V : NonemptyAffineOpen X} (h : U ⟶ V) :
    (closureMap L h).comp (algebraMap Γ(X, V.1.1) (closureRing L V)) =
      (algebraMap Γ(X, U.1.1) (closureRing L U)).comp (coefficientMap h) := by
  ext r
  exact congrArg (fun f : Γ(X, V.1.1) →+* L ↦ f r)
    (coefficientMap_extension L h).symm

/-- Each actual integral-closure transition is localization at an actual coefficient. -/
theorem closureMap_isLocalization {U V : NonemptyAffineOpen X} (h : U ⟶ V) :
    ∃ s : Γ(X, V.1.1), letI := (closureMap L h).toAlgebra
      IsLocalization.Away (algebraMap Γ(X, V.1.1) (closureRing L V) s) (closureRing L U) := by
  obtain ⟨s, hs⟩ := coefficientMap_isLocalization h
  let := (coefficientMap h).toAlgebra
  let := coefficientScalarTower L h
  have : IsLocalization.Away s Γ(X, U.1.1) := hs
  have hunit : IsUnit (algebraMap Γ(X, V.1.1) L s) := by
    rw [IsScalarTower.algebraMap_apply Γ(X, V.1.1) Γ(X, U.1.1) L s]
    exact (IsLocalization.Away.algebraMap_isUnit (S := Γ(X, U.1.1)) s).map _
  refine ⟨s, ?_⟩
  exact Algebra.IntegralClosureLocalization.closure_isLocalization s hunit

/-- The genuine affine normalization diagram in the specified ambient extension. -/
def affineDiagram : NonemptyAffineOpen X ⥤ Scheme.{u} where
  obj U := Spec (CommRingCat.of (closureRing L U))
  map h := Spec.map (CommRingCat.ofHom (closureMap L h))
  map_id U := by simp only [closureMap_id, CommRingCat.ofHom_id, Spec.map_id]
  map_comp h k := by
    rw [closureMap_comp, CommRingCat.ofHom_comp, Spec.map_comp]

/-- The actual affine normalization structure map, induced by its coefficient inclusion. -/
def affineStructure (U : NonemptyAffineOpen X) :
    Spec (CommRingCat.of (closureRing L U)) ⟶ Spec Γ(X, U.1.1) :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1.1) (closureRing L U)))

/-- The actual structure maps form a natural transformation over the spectrum diagram. -/
def structureNatTrans : affineDiagram L ⟶
    siteFunctor X ⋙ Scheme.AffineZariskiSite.toOpensFunctor X ⋙
      X.presheaf.rightOp ⋙ Scheme.Spec where
  app U := affineStructure L U
  naturality {U V} h := by
    change Spec.map (CommRingCat.ofHom (closureMap L h)) ≫ affineStructure L V =
      affineStructure L U ≫ Spec.map (CommRingCat.ofHom (coefficientMap h))
    unfold affineStructure
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) (closureMap_algebraMap L h)

/-- Every actual affine normalization square is Cartesian, by coefficient localization. -/
theorem structureNatTrans_equifibered :
    (structureNatTrans (X := X) L).Equifibered := by
  intro U V h
  obtain ⟨s, hs⟩ := coefficientMap_isLocalization h
  let := (coefficientMap h).toAlgebra
  let := coefficientScalarTower L h
  have : IsLocalization.Away s Γ(X, U.1.1) := hs
  have hunit : IsUnit (algebraMap Γ(X, V.1.1) L s) := by
    rw [IsScalarTower.algebraMap_apply Γ(X, V.1.1) Γ(X, U.1.1) L s]
    exact (IsLocalization.Away.algebraMap_isUnit (S := Γ(X, U.1.1)) s).map _
  let := (closureMap L h).toAlgebra
  have : IsLocalization.Away (algebraMap Γ(X, V.1.1) (closureRing L V) s) (closureRing L U) :=
    Algebra.IntegralClosureLocalization.closure_isLocalization s hunit
  let q := Spec.map (CommRingCat.ofHom (coefficientMap h))
  let p := Spec.map (CommRingCat.ofHom (closureMap L h))
  let : IsOpenImmersion q := IsOpenImmersion.of_isLocalization s
  let : IsOpenImmersion p := IsOpenImmersion.of_isLocalization
    (algebraMap Γ(X, V.1.1) (closureRing L V) s)
  have hq : q.opensRange = PrimeSpectrum.basicOpen s := by
    apply SetLike.coe_injective
    exact PrimeSpectrum.localization_away_comap_range Γ(X, U.1.1) s
  have hp : p.opensRange =
      PrimeSpectrum.basicOpen (algebraMap Γ(X, V.1.1) (closureRing L V) s) := by
    apply SetLike.coe_injective
    exact PrimeSpectrum.localization_away_comap_range (closureRing L U) _
  change IsPullback p (affineStructure L U) (affineStructure L V) q
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback
  · exact (structureNatTrans (X := X) L).naturality h
  · rw [hq, hp]
    rfl

/-- The actual common-function-field integral closures produce native relative gluing data. -/
def relativeGluingData (X : Scheme.{u}) [IsIntegral X] (L : Type u) [Field L] [Algebra X.functionField L] :
    (nonemptyAffineCover X).RelativeGluingData where
  functor := affineDiagram L
  natTrans := structureNatTrans (X := X) L ≫
    Functor.whiskerLeft (siteFunctor X) (Scheme.AffineZariskiSite.restrictIsoSpec X).inv
  equifibered := (structureNatTrans_equifibered (X := X) L).comp (.of_isIso _)

/-- The global normalization constructed by gluing actual integral closures in L. -/
def normalization (X : Scheme.{u}) [IsIntegral X] (L : Type u) [Field L] [Algebra X.functionField L] : Scheme.{u} :=
  (relativeGluingData X L).glued

/-- The genuine global normalization structure map to the original scheme. -/
def normalizationStructure (X : Scheme.{u}) [IsIntegral X] (L : Type u) [Field L] [Algebra X.functionField L] : normalization X L ⟶ X :=
  (relativeGluingData X L).toBase

/-- The canonical open cover by the actual spectra of integral closures. -/
abbrev normalizationCover (X : Scheme.{u}) [IsIntegral X] (L : Type u) [Field L] [Algebra X.functionField L] : (normalization X L).OpenCover :=
  (relativeGluingData X L).cover

/-- The native inclusion of an actual affine normalization into the global normalization. -/
def chartInclusion (X : Scheme.{u}) [IsIntegral X] (L : Type u) [Field L] [Algebra X.functionField L] (U : NonemptyAffineOpen X) :
    Spec (CommRingCat.of (closureRing L U)) ⟶ normalization X L := (normalizationCover X L).f U

@[simp]
theorem normalizationCover_X (U : NonemptyAffineOpen X) :
    (normalizationCover X L).X U = Spec (CommRingCat.of (closureRing L U)) := rfl

@[simp]
theorem normalizationCover_f (U : NonemptyAffineOpen X) :
    (normalizationCover X L).f U = chartInclusion X L U := rfl

instance chartInclusion_isOpenImmersion (U : NonemptyAffineOpen X) :
    IsOpenImmersion (chartInclusion X L U) :=
  inferInstanceAs (IsOpenImmersion ((normalizationCover X L).f U))

/-- The actual affine normalizations have the prescribed global structure triangles. -/
@[reassoc]
theorem chartInclusion_structure (U : NonemptyAffineOpen X) :
    chartInclusion X L U ≫ normalizationStructure X L = affineStructure L U ≫ U.1.2.fromSpec := by
  have h := (relativeGluingData X L).ι_toBase U
  change chartInclusion X L U ≫ normalizationStructure X L =
    (affineStructure L U ≫ U.1.2.isoSpec.inv) ≫ U.1.1.ι at h
  exact h.trans (by rw [Category.assoc, IsAffineOpen.isoSpec_inv_ι])

/-- The actual affine chart is the genuine pullback over its original base open subscheme. -/
theorem isPullback_chartOpen (U : NonemptyAffineOpen X) :
    IsPullback (affineStructure L U ≫ U.1.2.isoSpec.inv)
      (chartInclusion X L U) U.1.1.ι (normalizationStructure X L) :=
  (relativeGluingData X L).isPullback_natTrans_ι_toBase U

/-- The actual common-field affine normalization is the pullback over Spec Γ(U). -/
theorem isPullback_chart (U : NonemptyAffineOpen X) :
    IsPullback (affineStructure L U) (chartInclusion X L U)
      U.1.2.fromSpec (normalizationStructure X L) := by
  refine (isPullback_chartOpen L U).of_iso (Iso.refl _) U.1.2.isoSpec
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simpa only [Iso.refl_hom, Category.comp_id] using U.1.2.isoSpec_hom_fromSpec.symm
  · simp

/-- The affine normalization chart image is precisely the inverse image of the original open. -/
theorem chartInclusion_opensRange (U : NonemptyAffineOpen X) :
    (chartInclusion X L U).opensRange = normalizationStructure X L ⁻¹ᵁ U.1.1 := by
  have h := (relativeGluingData X L).toBase_preimage_eq_opensRange_ι U
  change normalizationStructure X L ⁻¹ᵁ U.1.1.ι.opensRange = (chartInclusion X L U).opensRange at h
  rw [Scheme.Opens.opensRange_ι] at h
  exact h.symm

end

end DeJongAlterations.Geometry.NormalizationInExtension
