import DeJongAlterations.Geometry.NormalizationInExtensionFinite
import DeJongAlterations.Composition

/-!
# The actual function field of normalization in a specified extension

The field comparison uses the actual generic stalk map of a genuine chart
open immersion and the unique isomorphism of the two actual fraction fields
of its integral-closure ring.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped nonZeroDivisors

namespace DeJongAlterations.Geometry.NormalizationInExtension

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section DominantMaps

variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (f : X ⟶ Y) [IsDominant f]

/-- The actual function-field homomorphism induced by the actual dominant morphism. -/
def functionFieldMap : Y.functionField ⟶ X.functionField :=
  (Y.presheaf.stalkCongr (.of_eq (genericPoint_map_of_isDominant f).symm)).hom ≫
    f.stalkMap (genericPoint X)

/-- The actual induced function-field homomorphism is an isomorphism. -/
theorem functionFieldMap_isIso [IsOpenImmersion f] : IsIso (functionFieldMap f) := by
  let : IsIso (f.stalkMap (genericPoint X)) := inferInstance
  dsimp only [functionFieldMap]
  infer_instance

/-- Naturality of the actual function-field map with respect to every local ring. -/
theorem functionFieldMap_stalk (x : X) :
    CommRingCat.ofHom (algebraMap (Y.presheaf.stalk (f x)) Y.functionField) ≫
      functionFieldMap f =
    f.stalkMap x ≫ CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) := by
  change Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes (Set.mem_univ (f x))) ≫
      ((Y.presheaf.stalkCongr (.of_eq (genericPoint_map_of_isDominant f).symm)).hom ≫
        f.stalkMap (genericPoint X)) =
    f.stalkMap x ≫ X.presheaf.stalkSpecializes
      ((genericPoint_spec X).specializes (Set.mem_univ x))
  simpa only [← Category.assoc, TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.stalkSpecializes_comp] using
    f.stalkSpecializes_stalkMap (genericPoint X) x
      ((genericPoint_spec X).specializes (Set.mem_univ x))

/-- The same actual function-field map commutes with affine section maps. -/
theorem functionFieldMap_sections (U : Y.Opens) [Nonempty U]
    [hpre : Nonempty (f ⁻¹ᵁ U)] :
    Y.germToFunctionField U ≫ functionFieldMap f =
      f.app U ≫ X.germToFunctionField (f ⁻¹ᵁ U) := by
  let x : f ⁻¹ᵁ U := Classical.choice hpre
  have hY : Y.presheaf.germ U (f x) x.2 ≫
      CommRingCat.ofHom (algebraMap (Y.presheaf.stalk (f x)) Y.functionField) =
      Y.germToFunctionField U := by
    apply CommRingCat.hom_ext
    exact RingHom.ext fun a => Y.algebraMap_germ_eq_germToFunctionField x.2 a
  have hX : X.presheaf.germ (f ⁻¹ᵁ U) x x.2 ≫
      CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) =
      X.germToFunctionField (f ⁻¹ᵁ U) := by
    apply CommRingCat.hom_ext
    exact RingHom.ext fun a => X.algebraMap_germ_eq_germToFunctionField x.2 a
  rw [← hY, Category.assoc, functionFieldMap_stalk,
    ← Category.assoc, f.germ_stalkMap, Category.assoc, hX]

/-- Actual generic-stalk maps compose with the native scheme morphisms. -/
theorem functionFieldMap_comp [IsIntegral Z] (g : Y ⟶ Z) [IsDominant g] :
    functionFieldMap (f ≫ g) = functionFieldMap g ≫ functionFieldMap f := by
  have h := g.stalkMap_congr_point (genericPoint Y) (f (genericPoint X))
    (genericPoint_map_of_isDominant f).symm
  simp only [functionFieldMap, Scheme.Hom.stalkMap_comp, Category.assoc]
  rw [← Category.assoc (g.stalkMap (genericPoint Y)), h]
  simp only [← Category.assoc, TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.stalkSpecializes_comp]

/-- Native affine-open generic maps preserve the actual original section coefficients. -/
theorem functionFieldMap_fromSpec_coeff (U : Y.affineOpens) [Nonempty U.1] :
    letI := NormalizationFinite.affineCoordinate_isDominant U
    Y.germToFunctionField U.1 ≫ functionFieldMap U.2.fromSpec =
      CommRingCat.ofHom (algebraMap Γ(Y, U.1) (Spec Γ(Y, U.1)).functionField) := by
  let := NormalizationFinite.affineCoordinate_isDominant U
  let : IsDomain Γ(Y, U.1) := IsIntegral.component_integral U.1
  have : Nonempty (U.2.fromSpec ⁻¹ᵁ U.1) := by
    rw [U.2.fromSpec_preimage_self]
    exact ⟨⟨genericPoint (Spec Γ(Y, U.1)), trivial⟩⟩
  rw [functionFieldMap_sections, U.2.fromSpec_app_self, Category.assoc]
  change _ ≫ _ ≫ (Spec Γ(Y, U.1)).presheaf.germ _ _ _ = _
  rw [(Spec Γ(Y, U.1)).presheaf.germ_res]
  rfl

/-- Actual affine coefficients commute with specialization into the generic stalk. -/
theorem toStalk_functionField (R : CommRingCat.{u}) [IsDomain R] (x : Spec R) :
    StructureSheaf.toStalk R x ≫
      CommRingCat.ofHom (algebraMap ((Spec R).presheaf.stalk x) (Spec R).functionField) =
      CommRingCat.ofHom (algebraMap R (Spec R).functionField) := by
  let : Nonempty (⊤ : (Spec R).Opens) := ⟨⟨genericPoint (Spec R), trivial⟩⟩
  apply CommRingCat.hom_ext
  ext r
  change algebraMap ((Spec R).presheaf.stalk x) (Spec R).functionField
    ((Spec R).presheaf.germ ⊤ x trivial ((Scheme.ΓSpecIso R).inv r)) =
      (Spec R).germToFunctionField ⊤ ((Scheme.ΓSpecIso R).inv r)
  exact (Spec R).algebraMap_germ_eq_germToFunctionField (show x ∈ (⊤ : (Spec R).Opens) from trivial) _

/-- Native affine generic-stalk maps preserve the original ring homomorphism. -/
theorem functionFieldMap_spec_coeff {R S : CommRingCat.{u}} [IsDomain R] [IsDomain S]
    (φ : R ⟶ S) [IsDominant (Spec.map φ)] :
    CommRingCat.ofHom (algebraMap R (Spec R).functionField) ≫
      functionFieldMap (Spec.map φ) =
        φ ≫ CommRingCat.ofHom (algebraMap S (Spec S).functionField) := by
  let x := genericPoint (Spec S)
  rw [← toStalk_functionField R ((Spec.map φ) x), Category.assoc,
    functionFieldMap_stalk, ← Category.assoc]
  change (StructureSheaf.toStalk R (PrimeSpectrum.comap φ.hom x) ≫
    (Spec.sheafedSpaceMap φ).hom.stalkMap x) ≫ _ = _
  rw [stalkMap_toStalk, Category.assoc, toStalk_functionField]

end DominantMaps

variable {X : Scheme.{u}} [IsIntegral X] (L : Type u) [Field L] [Algebra X.functionField L]
  [FiniteDimensional X.functionField L]

attribute [local instance] sectionsAlgebra

instance normalization_integral : IsIntegral (normalization X L) := isIntegral_normalization L
instance normalization_dominant : IsDominant (normalizationStructure X L) :=
  normalizationStructure_isDominant L

/-- Actual nonempty normalization charts have dense images. -/
instance chartInclusion_dominant (U : NonemptyAffineOpen X) :
    IsDominant (chartInclusion X L U) := by
  constructor
  exact (chartInclusion X L U).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)

/-- The actual generic-stalk chart map is invertible. -/
def chartFunctionFieldIso (U : NonemptyAffineOpen X) :
    (normalization X L).functionField ≅ (Spec (.of (closureRing L U))).functionField := by
  let := functionFieldMap_isIso (chartInclusion X L U)
  exact asIso (functionFieldMap (chartInclusion X L U))

/-- The native affine source uses its actual coefficient-to-generic-stalk algebra. -/
instance nativeChartFunctionFieldAlgebra (U : NonemptyAffineOpen X) :
    Algebra (closureRing L U) (Spec (.of (closureRing L U))).functionField :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of (closureRing L U))

instance nativeChartFunctionField_isFractionRing (U : NonemptyAffineOpen X) :
    IsFractionRing (closureRing L U) (Spec (.of (closureRing L U))).functionField :=
  functionField_isFractionRing_of_affine (.of (closureRing L U))

/-- The actual generic field of the normalization is the prescribed ambient extension. -/
def functionFieldEquiv (U : NonemptyAffineOpen X) :
    (normalization X L).functionField ≃+* L := by
  let := closureRing_isFractionRing L U
  exact (chartFunctionFieldIso L U).commRingCatIsoToRingEquiv.trans
    (IsLocalization.algEquiv (closureRing L U)⁰
      (Spec (.of (closureRing L U))).functionField L).toRingEquiv

/-- The comparison fixes the actual coefficient fractions from the chosen chart. -/
theorem functionFieldEquiv_chart (U : NonemptyAffineOpen X)
    (x : (Spec (.of (closureRing L U))).functionField) :
    functionFieldEquiv L U ((chartFunctionFieldIso L U).inv x) =
      (letI := closureRing_isFractionRing L U
       IsLocalization.algEquiv (closureRing L U)⁰
         (Spec (.of (closureRing L U))).functionField L) x := by
  change (letI := closureRing_isFractionRing L U
    IsLocalization.algEquiv (closureRing L U)⁰
      (Spec (.of (closureRing L U))).functionField L)
    ((chartFunctionFieldIso L U).hom ((chartFunctionFieldIso L U).inv x)) = _
  simp

/-- The actual chart-stalk comparison preserves the specified canonical field embedding. -/
theorem functionFieldEquiv_comp (U : NonemptyAffineOpen X) :
    (functionFieldEquiv L U).toRingHom.comp
      (functionFieldMap (normalizationStructure X L)).hom = algebraMap X.functionField L := by
  let A := Γ(X, U.1.1)
  let C := closureRing L U
  let : IsDomain A := IsIntegral.component_integral U.1.1
  let : IsFractionRing A X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U.1.1 U.1.2
  let : IsFractionRing C L := closureRing_isFractionRing L U
  let : IsDominant (affineStructure L U) := ⟨(affineStructure_surjective L U).denseRange⟩
  let := NormalizationFinite.affineCoordinate_isDominant ⟨U.1.1, U.1.2⟩
  let : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap A C))) := by
    change IsDominant (affineStructure L U)
    infer_instance
  have h : X.germToFunctionField U.1.1 ≫ functionFieldMap (normalizationStructure X L) ≫
      (chartFunctionFieldIso L U).hom =
      CommRingCat.ofHom (algebraMap A C) ≫
        CommRingCat.ofHom (algebraMap C (Spec (.of C)).functionField) := by
    change X.germToFunctionField U.1.1 ≫ functionFieldMap (normalizationStructure X L) ≫
      functionFieldMap (chartInclusion X L U) = _
    have hm : functionFieldMap (normalizationStructure X L) ≫
        functionFieldMap (chartInclusion X L U) =
        functionFieldMap (affineStructure L U ≫ U.1.2.fromSpec) := by
      simpa only [chartInclusion_structure] using
        (functionFieldMap_comp (chartInclusion X L U) (normalizationStructure X L)).symm
    rw [hm, functionFieldMap_comp, ← Category.assoc,
      functionFieldMap_fromSpec_coeff ⟨U.1.1, U.1.2⟩]
    exact functionFieldMap_spec_coeff (CommRingCat.ofHom (algebraMap A C))
  apply IsLocalization.ringHom_ext A⁰
  ext a
  have ha := ConcreteCategory.congr_hom h a
  change (IsLocalization.algEquiv C⁰ (Spec (.of C)).functionField L)
    ((chartFunctionFieldIso L U).hom
      (functionFieldMap (normalizationStructure X L) (algebraMap A X.functionField a))) = _
  change (chartFunctionFieldIso L U).hom
    (functionFieldMap (normalizationStructure X L) (algebraMap A X.functionField a)) =
    algebraMap C (Spec (.of C)).functionField (algebraMap A C a) at ha
  rw [ha]
  exact (IsLocalization.algEquiv C⁰ (Spec (.of C)).functionField L).commutes
    (algebraMap A C a)

/-- The function-field algebra is the actual generic-point stalk map of the structure morphism. -/
abbrev normalizationFunctionFieldAlgebra : Algebra X.functionField (normalization X L).functionField :=
  (functionFieldMap (normalizationStructure X L)).hom.toAlgebra

/-- The actual function-field comparison is an algebra isomorphism for the specified embedding. -/
def functionFieldAlgEquiv (U : NonemptyAffineOpen X) :
    letI := normalizationFunctionFieldAlgebra (X := X) L
    (normalization X L).functionField ≃ₐ[X.functionField] L := by
  let := normalizationFunctionFieldAlgebra (X := X) L
  exact { functionFieldEquiv L U with
    commutes' := fun a => congrArg (fun f : X.functionField →+* L => f a)
      (functionFieldEquiv_comp L U) }

end DeJongAlterations.Geometry.NormalizationInExtension
