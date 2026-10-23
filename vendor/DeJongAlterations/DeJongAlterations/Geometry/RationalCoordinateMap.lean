import DeJongAlterations.Geometry.SeparableGenericSmoothness
import Mathlib.RingTheory.AlgebraicIndependent.Defs

/-!
# Rational coordinates realized on a common affine open

The common domain and all its sections are constructed from representatives
in the actual generic-point stalk. No caller supplies a regular representative,
an open domain, or a morphism realizing the coordinates.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace DeJongAlterations.Geometry.RationalCoordinateMap

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{u}} [IsIntegral X] {n : ℕ}

/-- Finitely many actual rational functions have a common nonempty affine domain. -/
theorem exists_affine_sections (r : Fin n → X.functionField) :
    ∃ U : X.affineOpens, ∃ _ : Nonempty U.1,
      ∃ s : Fin n → Γ(X, U.1), ∀ i, X.germToFunctionField U.1 (s i) = r i := by
  choose V hV s hs using fun i ↦ X.presheaf.exists_germ_eq (r i)
  let W : X.Opens := ⨅ i, V i
  have hW : genericPoint X ∈ W := by
    change genericPoint X ∈ (W : Set X)
    rw [show (W : Set X) = ⋂ i, (V i : Set X) by exact Opens.coe_iInf _]
    exact Set.mem_iInter.mpr hV
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hW W.isOpen
  have hUV (i : Fin n) : U ≤ V i := fun x hx ↦ (iInf_le V i) (hUW hx)
  let : Nonempty U := ⟨⟨genericPoint X, hxU⟩⟩
  refine ⟨⟨U, hU⟩, inferInstance, fun i ↦ X.presheaf.map (homOfLE (hUV i)).op (s i), ?_⟩
  intro i
  exact (X.presheaf.germ_res_apply (homOfLE (hUV i)) (genericPoint X) hxU (s i)).trans
    (hs i)

/-- The common affine domain chosen from actual generic-point representatives. -/
def coordinateOpen (r : Fin n → X.functionField) : X.affineOpens :=
  (exists_affine_sections r).choose

instance coordinateOpen_nonempty (r : Fin n → X.functionField) : Nonempty (coordinateOpen r).1 :=
  (exists_affine_sections r).choose_spec.choose

/-- The actual regular representative of each rational coordinate on the common domain. -/
def coordinateSection (r : Fin n → X.functionField) : Fin n → Γ(X, (coordinateOpen r).1) :=
  (exists_affine_sections r).choose_spec.choose_spec.choose

@[simp]
theorem coordinateSection_germ (r : Fin n → X.functionField) (i : Fin n) :
    X.germToFunctionField (coordinateOpen r).1 (coordinateSection r i) = r i :=
  (exists_affine_sections r).choose_spec.choose_spec.choose_spec i

theorem coordinateOpen_dense (r : Fin n → X.functionField) :
    Dense ((coordinateOpen r).1 : Set X) :=
  (coordinateOpen r).1.isOpen.dense (by simpa using (coordinateOpen_nonempty r))

variable {k : Type u} [Field k]

/-- The actual ground-field map obtained from the structure morphism on this open. -/
def coefficientMap (p : X ⟶ Spec (.of k)) (U : X.affineOpens) : k →+* Γ(X, U.1) :=
  (p.appLE ⊤ U.1 (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom

/-- The canonical coefficient scalar structure on an actual affine coordinate ring. -/
abbrev sectionAlgebra (p : X ⟶ Spec (.of k)) (U : X.affineOpens) : Algebra k Γ(X, U.1) :=
  (coefficientMap p U).toAlgebra

/-- The two actual structure maps agree on the common generic stalk. -/
theorem functionFieldScalarTower (p : X ⟶ Spec (.of k)) (U : X.affineOpens) [Nonempty U.1] :
    letI := SeparableGenericSmoothness.functionFieldAlgebra p
    letI := sectionAlgebra p U
    IsScalarTower k Γ(X, U.1) X.functionField := by
  let := SeparableGenericSmoothness.functionFieldAlgebra p
  let := sectionAlgebra p U
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change p.stalkMap (genericPoint X) (StructureSheaf.toStalk k (p (genericPoint X)) a) =
    X.germToFunctionField U.1 ((coefficientMap p U) a)
  change p.stalkMap (genericPoint X)
      ((Spec (.of k)).presheaf.germ ⊤ (p (genericPoint X)) trivial
        ((Scheme.ΓSpecIso (.of k)).inv a)) = _
  rw [p.germ_stalkMap_apply]
  simp only [coefficientMap, RingHom.comp_apply, Scheme.Hom.appLE,
    CommRingCat.hom_comp,
    Scheme.germToFunctionField, X.presheaf.germ_res_apply]

/-- Evaluation at the constructed regular representatives, over the actual field map. -/
def coordinateRingMap (p : X ⟶ Spec (.of k)) (r : Fin n → X.functionField) :
    MvPolynomial (Fin n) k →+* Γ(X, (coordinateOpen r).1) := by
  let := sectionAlgebra p (coordinateOpen r)
  exact (MvPolynomial.aeval (coordinateSection r)).toRingHom

/-- The actual coordinate morphism on the constructed dense affine domain. -/
def coordinateMap (p : X ⟶ Spec (.of k)) (r : Fin n → X.functionField) :
    (coordinateOpen r).1.toScheme ⟶ Spec (.of (MvPolynomial (Fin n) k)) :=
  (coordinateOpen r).2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (coordinateRingMap p r))

@[simp]
theorem coordinateRingMap_X (p : X ⟶ Spec (.of k)) (r : Fin n → X.functionField) (i : Fin n) :
    coordinateRingMap p r (MvPolynomial.X i) = coordinateSection r i := by
  let := sectionAlgebra p (coordinateOpen r)
  exact MvPolynomial.aeval_X _ _

/-- The evaluation map preserves the actual ground-field coefficients. -/
theorem coordinateRingMap_comp_algebraMap (p : X ⟶ Spec (.of k))
    (r : Fin n → X.functionField) :
    (coordinateRingMap p r).comp (algebraMap k (MvPolynomial (Fin n) k)) =
      coefficientMap p (coordinateOpen r) := by
  let := sectionAlgebra p (coordinateOpen r)
  ext a
  exact (MvPolynomial.aeval (R := k) (coordinateSection r)).commutes a

/-- Evaluating and then taking the canonical germ is exactly evaluation at the given functions. -/
theorem coordinateRingMap_germ (p : X ⟶ Spec (.of k)) (r : Fin n → X.functionField) :
    letI := SeparableGenericSmoothness.functionFieldAlgebra p
    (X.germToFunctionField (coordinateOpen r).1).hom.comp (coordinateRingMap p r) =
      (MvPolynomial.aeval r).toRingHom := by
  let := SeparableGenericSmoothness.functionFieldAlgebra p
  let := sectionAlgebra p (coordinateOpen r)
  let := functionFieldScalarTower p (coordinateOpen r)
  let g : Γ(X, (coordinateOpen r).1) →ₐ[k] X.functionField :=
    IsScalarTower.toAlgHom k Γ(X, (coordinateOpen r).1) X.functionField
  change (g.comp (MvPolynomial.aeval (coordinateSection r))).toRingHom = _
  rw [MvPolynomial.comp_aeval]
  congr 2
  funext i
  exact coordinateSection_germ r i

/-- The actual spectrum structure map of affine n-space over k. -/
def affineSpaceStructure (n : ℕ) : Spec (.of (MvPolynomial (Fin n) k)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin n) k)))

/-- The actual coordinate morphism commutes with the given structure morphism. -/
theorem coordinateMap_structure (p : X ⟶ Spec (.of k)) (r : Fin n → X.functionField) :
    coordinateMap p r ≫ affineSpaceStructure n = (coordinateOpen r).1.ι ≫ p := by
  rw [coordinateMap, affineSpaceStructure, Category.assoc, ← Spec.map_comp]
  have h := coordinateRingMap_comp_algebraMap p r
  change (coordinateOpen r).1.toSpecΓ ≫
    Spec.map (CommRingCat.ofHom ((coordinateRingMap p r).comp (algebraMap k _))) = _
  rw [h]
  change (coordinateOpen r).1.toSpecΓ ≫
    Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appLE ⊤ (coordinateOpen r).1 (by simp)) = _
  rw [Spec.map_comp, ← Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_appLE,
    Scheme.Opens.toSpecΓ_top]
  simp only [Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id,
    Scheme.Hom.resLE_comp_ι]

/-- Algebraic independence forces injectivity of the actual coordinate-ring map. -/
theorem coordinateRingMap_injective (p : X ⟶ Spec (.of k)) (r : Fin n → X.functionField)
    (hr : letI := SeparableGenericSmoothness.functionFieldAlgebra p; AlgebraicIndependent k r) :
    Function.Injective (coordinateRingMap p r) := by
  let := SeparableGenericSmoothness.functionFieldAlgebra p
  have hg := coordinateRingMap_germ p r
  intro a b hab
  apply hr
  change (MvPolynomial.aeval r).toRingHom a = (MvPolynomial.aeval r).toRingHom b
  rw [← RingHom.congr_fun hg a, ← RingHom.congr_fun hg b]
  exact congrArg (X.germToFunctionField (coordinateOpen r).1) hab

/-- The genuine coordinate morphism is dominant when the given functions are independent. -/
theorem coordinateMap_isDominant (p : X ⟶ Spec (.of k)) (r : Fin n → X.functionField)
    (hr : letI := SeparableGenericSmoothness.functionFieldAlgebra p; AlgebraicIndependent k r) :
    IsDominant (coordinateMap p r) := by
  have : IsDominant (Spec.map (CommRingCat.ofHom (coordinateRingMap p r))) := by
    constructor
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
    intro a ha
    have ha0 : a = 0 := (coordinateRingMap_injective p r hr)
      (by simpa using ha)
    simp [ha0]
  dsimp only [coordinateMap]
  infer_instance

end DeJongAlterations.Geometry.RationalCoordinateMap
