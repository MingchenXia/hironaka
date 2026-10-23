/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane PL-GLOBAL)
-/
import DeJongAlterations.StableModification.DeJong.FibrationGeneric
import DeJongAlterations.Geometry.SteinGeometricIntegrality

/-!
# The generic fibre of a morphism, read off the local rings of the source

Blueprint chapter `sm-dj-perfection-global`, nodes `lem:sm-dj-perfection-global-generic-fibre`
and `lem:sm-dj-perfection-global-function-field` (new route, not in de Jong 1996).

Let `f : X ⟶ Y` be a morphism with `Y` integral, with generic point `η`, and let
`X_η = f.fiber η` be the generic fibre, over the residue field `κ(η)`. The inclusion
`X_η ⟶ X` is a flat preimmersion, so it induces isomorphisms on all local rings and residue
fields; and `Spec κ(η) ⟶ Y` induces isomorphisms on the local rings, which are all fields. Hence:

* `smooth_genericFiber_of_formallySmooth`: `X_η` is smooth over `κ(η)` as soon as it is locally
  of finite presentation and the local ring maps `O_{Y,η} ⟶ O_{X,x}` are formally smooth at
  all points `x` of `X` over `η`;
* `separableResidueFieldsAlong_of_isSeparable`: the residue fields of the points of `X_η` over
  `W ⊆ X` are separable over `κ(η)` as soon as the residue field extensions `κ(η) ⊆ κ(x)` are
  separable at all points `x ∈ W` over `η`.

Geometric integrality of the generic fibre is a property of the function field:

* `isDomain_functionField_tensorProduct`: if `T` is integral and geometrically integral over a
  field `K`, then `K(T) ⊗_K F` is a domain for every field extension `F / K`. Proof: the base
  change `Spec (K(T) ⊗_K F) ⟶ T_F` of the generic point `Spec K(T) ⟶ T` is a flat preimmersion
  into the integral scheme `T_F`, hence has reduced source; its image is the fibre of `T_F ⟶ T`
  over the generic point, which contains the generic point of `T_F`, hence is irreducible.
* `isDomain_functionField_tensorProduct_of_genericFiber`: for a dominant `f : X ⟶ Y` of integral
  schemes with geometrically integral generic fibre, `K(X) ⊗_{K(Y)} F` is a domain for every
  field extension `F / K(Y)`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

namespace DeJongAlterations.StableModification.Perfection

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open DeJong Geometry

section Stalks

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral Y]

/-- The point `Spec κ(η) ⟶ Y` of the generic point of an integral scheme induces isomorphisms
on local rings. -/
theorem isIso_stalkMap_fromSpecResidueField (z : Spec (Y.residueField (genericPoint Y))) :
    IsIso ((Y.fromSpecResidueField (genericPoint Y)).stalkMap z) := by
  set j := Y.fromSpecResidueField (genericPoint Y)
  have hfield : IsField (Y.presheaf.stalk (j z)) := by
    rw [Scheme.fromSpecResidueField_apply]
    exact Field.toIsField Y.functionField
  have h1 : IsIso (Y.residue (j z)) := isIso_residue_of_isField Y (j z) hfield
  have h2 : IsIso ((Spec (Y.residueField (genericPoint Y))).residue z) :=
    isIso_residue_of_isField _ z (RegularSmoothConverse.specFieldStalk_isField z)
  have h3 : IsIso (j.residueFieldMap z) := isIso_residueFieldMap_of_isPreimmersion j z
  have h : j.stalkMap z = Y.residue (j z) ≫ j.residueFieldMap z ≫
      inv ((Spec (Y.residueField (genericPoint Y))).residue z) := by
    rw [← Category.assoc, Scheme.residue_residueFieldMap, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  rw [h]
  infer_instance

/-- Points of the generic fibre lie over the generic point. -/
theorem fiberι_apply_genericPoint (z : f.fiber (genericPoint Y)) :
    f (f.fiberι (genericPoint Y) z) = genericPoint Y := by
  have : f.fiberι (genericPoint Y) z ∈ Set.range (f.fiberι (genericPoint Y)) := ⟨z, rfl⟩
  rw [Scheme.Hom.range_fiberι] at this
  exact this

/-- **Smoothness of the generic fibre from the local rings.** If the generic fibre of `f` is
locally of finite presentation over `κ(η)` and the local ring maps of `f` are formally smooth at
all points over the generic point `η`, then the generic fibre is smooth over `κ(η)`. -/
theorem smooth_genericFiber_of_formallySmooth
    [LocallyOfFinitePresentation (f.fiberToSpecResidueField (genericPoint Y))]
    (h : ∀ x : X, f x = genericPoint Y → (f.stalkMap x).hom.FormallySmooth) :
    Smooth (f.fiberToSpecResidueField (genericPoint Y)) := by
  set g := f.fiberToSpecResidueField (genericPoint Y)
  set ι := f.fiberι (genericPoint Y)
  set j := Y.fromSpecResidueField (genericPoint Y)
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, eq_top_iff]
  intro z _
  rw [Scheme.Hom.mem_smoothLocus]
  have := flat_fiberι_genericPoint f
  have hι : IsIso (ι.stalkMap z) := GenericFiberIntegral.stalkMap_isIso_of_flat_preimmersion ι z
  have hj : IsIso (j.stalkMap (g z)) := isIso_stalkMap_fromSpecResidueField (g z)
  have h1 := h (ι z) (fiberι_apply_genericPoint f z)
  have h2 : ((ι ≫ f).stalkMap z).hom.FormallySmooth := by
    rw [Scheme.Hom.stalkMap_comp]
    exact (RingHom.FormallySmooth.respectsIso.cancel_right_isIso _ _).mpr h1
  rw [Scheme.Hom.stalkMap_congr_hom _ (g ≫ j) (Scheme.Hom.fiber_fac f _) z,
    Scheme.Hom.stalkMap_comp, ← Category.assoc] at h2
  exact (RingHom.FormallySmooth.respectsIso.cancel_left_isIso _ _).mp h2

/-- **Separable residue fields of the generic fibre from those of the source.** If the residue
field extensions `κ(η) ⊆ κ(x)` are separable at all points `x ∈ W` over the generic point, then
the points of the generic fibre lying on `W` have separable residue fields over `κ(η)`. -/
theorem separableResidueFieldsAlong_of_isSeparable (W : Set X)
    (h : ∀ x : X, f x = genericPoint Y → x ∈ W →
      letI := (f.residueFieldMap x).hom.toAlgebra
      Algebra.IsSeparable (Y.residueField (f x)) (X.residueField x)) :
    SeparableResidueFieldsAlong f (genericPoint Y) W := by
  intro z hz
  set g := f.fiberToSpecResidueField (genericPoint Y)
  set ι := f.fiberι (genericPoint Y)
  set j := Y.fromSpecResidueField (genericPoint Y)
  let := (g.residueFieldMap z).hom.toAlgebra
  let := (f.residueFieldMap (ι z)).hom.toAlgebra
  have hsep := h (ι z) (fiberι_apply_genericPoint f z) hz
  have hι : IsIso (ι.residueFieldMap z) := isIso_residueFieldMap_of_isPreimmersion ι z
  have hj : IsIso (j.residueFieldMap (g z)) := isIso_residueFieldMap_of_isPreimmersion j (g z)
  have hcomp := Scheme.Hom.residueFieldMap_congr (Scheme.Hom.fiber_fac f (genericPoint Y)) z
  rw [Scheme.residueFieldMap_comp, Scheme.residueFieldMap_comp] at hcomp
  have hpt : f (ι z) = j (g z) := by
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.fiber_fac, Scheme.Hom.comp_apply]
  let e₁ : Y.residueField (f (ι z)) ≃+* (Spec (Y.residueField (genericPoint Y))).residueField
      (g z) :=
    (asIso ((Scheme.residueFieldCongr hpt).hom ≫
      j.residueFieldMap (g z))).commRingCatIsoToRingEquiv
  let e₂ : X.residueField (ι z) ≃+* (f.fiber (genericPoint Y)).residueField z :=
    (asIso (ι.residueFieldMap z)).commRingCatIsoToRingEquiv
  refine Algebra.IsSeparable.of_equiv_equiv e₁ e₂ ?_
  have := congrArg CommRingCat.Hom.hom hcomp
  simp only [CommRingCat.hom_comp] at this
  ext a
  change (g.residueFieldMap z) (j.residueFieldMap (g z) ((Scheme.residueFieldCongr hpt).hom a)) =
    ι.residueFieldMap z (f.residueFieldMap (ι z) a)
  have h' := congrArg (fun φ => φ a) this
  simpa using h'.symm

end Stalks

section TensorDomain

/-- The generic point of an integral scheme is a flat morphism `Spec K(T) ⟶ T`. -/
theorem fromSpecStalk_genericPoint_flat (T : Scheme.{u}) [IsIntegral T] :
    Flat (T.fromSpecStalk (genericPoint T)) := by
  apply (Flat.iff_flat_stalkMap _).mpr
  intro x
  have hx : T.fromSpecStalk (genericPoint T) x = genericPoint T := by
    have hmem : T.fromSpecStalk (genericPoint T) x ∈
        Set.range (T.fromSpecStalk (genericPoint T)) := ⟨x, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hmem
    have hgen : IsGenericPoint (T.fromSpecStalk (genericPoint T) x) (Set.univ : Set T) := by
      rw [IsGenericPoint, Set.eq_univ_iff_forall]
      intro y
      exact specializes_iff_mem_closure.mp
        (((genericPoint_spec T).specializes (Set.mem_univ y)).trans' hmem)
    exact hgen.eq (genericPoint_spec T)
  have hfield : IsField (T.presheaf.stalk (T.fromSpecStalk (genericPoint T) x)) := by
    rw [hx]
    exact Field.toIsField T.functionField
  let : Field (T.presheaf.stalk (T.fromSpecStalk (genericPoint T) x)) := hfield.toField
  algebraize [((T.fromSpecStalk (genericPoint T)).stalkMap x).hom]
  change Module.Flat _ _
  infer_instance

/-- A ring whose spectrum is integral is a domain. -/
theorem isDomain_of_isIntegral_spec (R : CommRingCat.{u}) [IsIntegral (Spec R)] : IsDomain R := by
  have : Nonempty (⊤ : (Spec R).Opens) := ⟨⟨genericPoint (Spec R), trivial⟩⟩
  have := IsIntegral.component_integral (X := Spec R) ⊤
  exact (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm.toMulEquiv.isDomain

/-- **The function field of a geometrically integral scheme is geometrically integral.** If `T`
is integral and geometrically integral over a field `K`, then `K(T) ⊗_K F` is a domain for every
field extension `F / K`. -/
theorem isDomain_functionField_tensorProduct {K : Type u} [Field K] {T : Scheme.{u}}
    [IsIntegral T] (g : T ⟶ Spec (.of K)) [GeometricallyIntegral g] (F : Type u) [Field F]
    [Algebra K F] :
    letI := SeparableGenericSmoothness.functionFieldAlgebra g
    IsDomain (T.functionField ⊗[K] F) := by
  let := SeparableGenericSmoothness.functionFieldAlgebra g
  set jη := T.fromSpecStalk (genericPoint T)
  set e : Spec (.of F) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K F))
  have hstr : Spec.map (CommRingCat.ofHom (algebraMap K T.functionField)) = jη ≫ g :=
    SteinGenericFiber.structureFieldMap_generic g
  have : IsIntegral (pullback g e) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback _ _)
  let b := pullback.map (jη ≫ g) e g e jη (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hb : IsPullback (pullback.fst (jη ≫ g) e) b jη (pullback.fst g e) := by
    apply IsPullback.of_bot (v₂₁ := pullback.snd g e) (v₂₂ := g)
    · simpa [b] using (IsPullback.of_hasPullback (jη ≫ g) e)
    · simp [b]
    · exact IsPullback.of_hasPullback g e
  have := fromSpecStalk_genericPoint_flat T
  have : Flat b := by rw [← hb.isoPullback_hom_snd]; infer_instance
  have : IsPreimmersion b := by rw [← hb.isoPullback_hom_snd]; infer_instance
  have : IsReduced (pullback (jη ≫ g) e) :=
    GenericFiberIntegral.isReduced_of_flat_preimmersion b
  -- the image of `b` is the fibre over the generic point of `T`
  have hr : Set.range b = (pullback.fst g e) ⁻¹' {genericPoint T} := by
    have := Scheme.Pullback.range_map (jη ≫ g) e g e jη (𝟙 _) (𝟙 _) (by simp) (by simp)
    have hid : Set.range (𝟙 (Spec (.of F)) : Spec (.of F) ⟶ _) = Set.univ :=
      Set.range_eq_univ.mpr fun y => ⟨y, rfl⟩
    rw [this, hid, Set.preimage_univ, Set.inter_univ, Scheme.range_fromSpecStalk]
    ext y
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hy
      have hgen : IsGenericPoint (pullback.fst g e y) (Set.univ : Set T) := by
        rw [IsGenericPoint, Set.eq_univ_iff_forall]
        intro y'
        exact specializes_iff_mem_closure.mp
          (Specializes.trans hy ((genericPoint_spec T).specializes (Set.mem_univ y')))
      exact hgen.eq (genericPoint_spec T)
    · intro hy
      rw [hy]
  have hsurj : Surjective e := ⟨fun x => ⟨IsLocalRing.closedPoint F, Subsingleton.elim _ _⟩⟩
  have : IsDominant (pullback.fst g e) := inferInstance
  have hξ : genericPoint (pullback g e : Scheme.{u}) ∈ Set.range b := by
    rw [hr]
    exact genericPoint_map_of_isDominant (pullback.fst g e)
  have hirr : IsIrreducible (Set.range b) := by
    rw [← isIrreducible_iff_closure]
    have : closure (Set.range b) = Set.univ := by
      refine Set.eq_univ_of_univ_subset ?_
      rw [← (genericPoint_spec (pullback g e : Scheme.{u})).def]
      exact closure_mono (Set.singleton_subset_iff.mpr hξ)
    rw [this]
    exact IrreducibleSpace.isIrreducible_univ _
  have : IrreducibleSpace (Set.range b) := isIrreducible_iff_irreducibleSpace.mp hirr
  have : IrreducibleSpace (pullback (jη ≫ g) e : Scheme.{u}) :=
    (b.isEmbedding.toHomeomorph.irreducibleSpace_iff).mpr inferInstance
  have : IsIntegral (pullback (jη ≫ g) e) := isIntegral_of_irreducibleSpace_of_isReduced _
  let i : Spec (.of (T.functionField ⊗[K] F)) ⟶ pullback (jη ≫ g) e :=
    (pullbackSpecIso K T.functionField F).inv ≫ (pullback.congrHom hstr rfl).hom
  have : IsIntegral (Spec (.of (T.functionField ⊗[K] F))) := isIntegral_of_isOpenImmersion i
  exact isDomain_of_isIntegral_spec (.of (T.functionField ⊗[K] F))

/-- **Geometric integrality of the function field extension.** For a dominant morphism of
integral schemes whose generic fibre is geometrically integral, `K(X) ⊗_{K(Y)} F` is a domain
for every field extension `F / K(Y)`. -/
theorem isDomain_functionField_tensorProduct_of_genericFiber {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) [IsDominant f]
    (h : GeometricallyIntegral (f.fiberToSpecResidueField (genericPoint Y))) (F : Type u)
    [Field F] [Algebra Y.functionField F] :
    letI := FiniteBirationalNormal.functionFieldAlgebra f
    IsDomain (X.functionField ⊗[Y.functionField] F) := by
  let := FiniteBirationalNormal.functionFieldAlgebra f
  have : IsIntegral (f.fiber (genericPoint Y)) := GenericFiberIntegral.genericFiber_isIntegral f
  have := GenericFiberFunctionField.genericFiberι_isDominant f
  set T := f.fiber (genericPoint Y)
  set g := f.fiberToSpecResidueField (genericPoint Y)
  let r := Y.residue (genericPoint Y)
  have : IsIso r := (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨r.hom.injective, IsLocalRing.residue_surjective⟩
  let g' : T ⟶ Spec (.of Y.functionField) := g ≫ Spec.map r
  have : GeometricallyIntegral g' :=
    (MorphismProperty.cancel_right_of_respectsIso @GeometricallyIntegral g (Spec.map r)).mpr h
  let := SeparableGenericSmoothness.functionFieldAlgebra g'
  have hdom := isDomain_functionField_tensorProduct g' F
  -- the two `K(Y)`-structures on `K(T)` agree
  have halg : algebraMap Y.functionField T.functionField =
      (NormalizationInExtension.functionFieldMap (f.fiberι (genericPoint Y))).hom.comp
        (NormalizationInExtension.functionFieldMap f).hom := by
    let : Algebra (Y.residueField (genericPoint Y)) T.functionField :=
      SeparableGenericSmoothness.functionFieldAlgebra g
    have h1 : Spec.map (CommRingCat.ofHom (algebraMap Y.functionField T.functionField)) =
        Spec.map (r ≫ CommRingCat.ofHom
          (algebraMap (Y.residueField (genericPoint Y)) T.functionField)) := by
      rw [SteinGenericFiber.structureFieldMap_generic g', Spec.map_comp,
        ← Category.assoc, ← SteinGenericFiber.structureFieldMap_generic g]
      rfl
    have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    rw [CommRingCat.hom_ofHom] at h2
    rw [h2]
    exact SteinGenericFiber.coefficient_triangle f
  let e : X.functionField ≃ₐ[Y.functionField] T.functionField :=
    { (GenericFiberFunctionField.functionFieldIso f).commRingCatIsoToRingEquiv with
      commutes' := fun c => by
        change (NormalizationInExtension.functionFieldMap (f.fiberι (genericPoint Y))).hom
          ((NormalizationInExtension.functionFieldMap f).hom c) = _
        rw [halg]
        rfl }
  exact (Algebra.TensorProduct.congr e
    (AlgEquiv.refl : F ≃ₐ[Y.functionField] F)).toMulEquiv.isDomain

end TensorDomain

end DeJongAlterations.StableModification.Perfection

end
