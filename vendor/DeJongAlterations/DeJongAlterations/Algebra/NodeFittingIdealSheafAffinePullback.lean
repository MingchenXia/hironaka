/-
Adapted from Hironaka/Scheme/BlowUp/InverseImage.lean in
EnvelopeProperty/deps/hironaka-ep33, SHA256
4d7e0eb6480cec39995d3edad7fec14518894ecc101702d0298c50bbcc98bd87.
Copyright (c) 2026 Resolution; author Chris Elliott (Resolution).
Original Lean formalization by Claude Fable 5.1; Apache License 2.0.
Modified: retain only actual whole-ideal affine pullback, use Mathlib-only
imports and a disjoint namespace. The Apache License 2.0 is reproduced in
DeJongAlterations/Algebra/AdicCompletionTransport.lean.
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Actual affine-chart pullback of entire native ideal-sheaf ideals -/

noncomputable section

universe u

open CategoryTheory Limits TensorProduct

namespace DeJongAlterations.Algebra.NodeFittingIdealSheaf

open AlgebraicGeometry Scheme.IdealSheafData

variable {R S : CommRingCat.{u}}

theorem appTop_Spec_map (φ : R ⟶ S) :
    (Spec.map φ).appTop = (Scheme.ΓSpecIso R).hom ≫ φ ≫ (Scheme.ΓSpecIso S).inv := by
  rw [← Category.comp_id (Spec.map φ).appTop, ← (Scheme.ΓSpecIso S).hom_inv_id, ← Category.assoc,
    Scheme.ΓSpecIso_naturality, Category.assoc]

theorem injective_ΓSpecIso_inv : Function.Injective (Scheme.ΓSpecIso S).inv.hom :=
  (Scheme.ΓSpecIso S).symm.commRingCatIsoToRingEquiv.injective

/-- The kernel of the map on global sections induced by `φ : R → S` is `ker φ`, transported to
`Γ(Spec R, ⊤)`. -/
theorem ker_appTop_Spec_map (φ : R ⟶ S) :
    RingHom.ker (Spec.map φ).appTop.hom = (RingHom.ker φ.hom).map (Scheme.ΓSpecIso R).inv.hom := by
  rw [appTop_Spec_map, CommRingCat.hom_comp, CommRingCat.hom_comp, ← RingHom.comap_ker,
    RingHom.ker_comp_of_injective _ injective_ΓSpecIso_inv]
  ext x
  rw [Ideal.mem_comap, Ideal.mem_map_iff_of_surjective (Scheme.ΓSpecIso R).inv.hom
    (fun y => ⟨(Scheme.ΓSpecIso R).hom.hom y,
      (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm_apply_apply y⟩)]
  constructor
  · intro hx
    exact ⟨(Scheme.ΓSpecIso R).hom x, hx,
      (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm_apply_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    have h : (Scheme.ΓSpecIso R).hom.hom ((Scheme.ΓSpecIso R).inv.hom y) = y :=
      (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.apply_symm_apply y
    rw [h]
    exact hy

/-- The closed immersion `Spec (R/I) → Spec R` has kernel the ideal sheaf of `I`. -/
theorem ker_Spec_map_mk (I : Ideal R) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker =
      ofIdealTop (I.map (Scheme.ΓSpecIso R).inv.hom) := by
  rw [Scheme.ker_of_isAffine, ker_appTop_Spec_map, CommRingCat.hom_ofHom, Ideal.mk_ker]
  rfl

/-- The case `f = Spec.map φ`: the comap of the ideal sheaf of `I ⊆ R` along `Spec S → Spec R` is
the ideal sheaf of `IS`. -/
theorem comap_ofIdealTop_Spec_map (φ : R ⟶ S) (I : Ideal R) :
    (ofIdealTop (I.map (Scheme.ΓSpecIso R).inv.hom)).comap (Spec.map φ) =
      ofIdealTop ((I.map φ.hom).map (Scheme.ΓSpecIso S).inv.hom) := by
  let _ := φ.hom.toAlgebra
  have hfst : (pullbackSpecIso R S (R ⧸ I)).inv ≫
      Limits.pullback.fst (Spec.map φ) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        S →+* S ⊗[R] (R ⧸ I))) :=
    pullbackSpecIso_inv_fst R S (R ⧸ I)
  rw [← ker_Spec_map_mk, ← ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso (pullbackSpecIso R S (R ⧸ I)).inv, hfst,
    Scheme.ker_of_isAffine, ker_appTop_Spec_map, CommRingCat.hom_ofHom]
  have hincl : (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] (R ⧸ I)) =
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I :
        S ⧸ I.map (algebraMap R S) →ₐ[S] S ⊗[R] (R ⧸ I)) : _ →+* _).comp
        (Ideal.Quotient.mk (I.map (algebraMap R S))) :=
    RingHom.ext fun s => (Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk S I s).symm
  rw [hincl, RingHom.ker_comp_of_injective _
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).injective, Ideal.mk_ker]
  rfl


variable {X Y : Scheme.{u}}

/-- The closed subscheme of `J` over the affine open `U` is `Spec (Γ(X, U)/J(U))`: the square with
`hU.fromSpec` and `J.subschemeι` is a pullback. -/
theorem isPullback_fromSpec (J : X.IdealSheafData) (U : X.affineOpens) :
    IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.ideal U))))
      (J.subschemeCover.f U) U.2.fromSpec J.subschemeι := by
  have hU : IsAffineOpen U.1 := U.2
  have hopen : IsOpenImmersion (J.subschemeCover.f U) := J.subschemeCover.map_prop U
  change IsPullback _ _ hU.fromSpec _
  refine @IsOpenImmersion.isPullback _ _ _ _
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.ideal U))))
    (J.subschemeCover.f U) hU.fromSpec J.subschemeι hopen inferInstance ?_ ?_
  · exact (subschemeCover_map_subschemeι J U).trans (glueDataObjι_ι J U)
  · rw [IsAffineOpen.opensRange_fromSpec]
    exact (opensRange_subschemeCover_map J U).symm

/-- The comap of an ideal sheaf along `hU.fromSpec` is the ideal sheaf of `J(U)` on `Spec Γ(X, U)`
(the `ΓSpecIso` compatibility of `ofIdealTop`). -/
theorem comap_fromSpec (J : X.IdealSheafData) (U : X.affineOpens) :
    J.comap U.2.fromSpec = ofIdealTop ((J.ideal U).map (Scheme.ΓSpecIso Γ(X, U)).inv.hom) := by
  have hP := isPullback_fromSpec J U
  have hfst : Limits.pullback.fst U.2.fromSpec J.subschemeι =
      hP.isoPullback.inv ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.ideal U))) := by
    rw [Iso.eq_inv_comp, hP.isoPullback_hom_fst]
  rw [comap, hfst, Scheme.Hom.ker_comp_of_isIso, ker_Spec_map_mk]

/-- For affine opens `U ⊆ X`, `V ⊆ Y` with `f(V) ⊆ U`, the ideal of `I.comap f` on `V` is
`I(U)·Γ(Y, V)` (compare the proof of [Sta, Tag 0805]). -/
theorem ideal_comap_of_le (I : X.IdealSheafData) (f : Y ⟶ X) (U : X.affineOpens)
    (V : Y.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1) :
    (I.comap f).ideal V = (I.ideal U).map (f.appLE U.1 V.1 e).hom := by
  have h1 : (I.comap f).comap V.2.fromSpec =
      ofIdealTop (((I.comap f).ideal V).map (Scheme.ΓSpecIso Γ(Y, V)).inv.hom) :=
    comap_fromSpec _ V
  have h2 : (I.comap f).comap V.2.fromSpec =
      ofIdealTop (((I.ideal U).map (f.appLE U.1 V.1 e).hom).map
        (Scheme.ΓSpecIso Γ(Y, V)).inv.hom) := by
    rw [← comap_comp, ← IsAffineOpen.SpecMap_appLE_fromSpec f U.2 V.2 e, comap_comp,
      comap_fromSpec, comap_ofIdealTop_Spec_map]
  have h3 := h1.symm.trans h2
  have hinj : Function.Injective (ofIdealTop (X := Spec Γ(Y, V))) :=
    equivOfIsAffine.symm.injective
  have h4 := hinj h3
  -- cancel the isomorphism `ΓSpecIso`
  set e : Γ(Y, V) ≃+* Γ(Spec Γ(Y, V), ⊤) :=
    (Scheme.ΓSpecIso Γ(Y, V)).symm.commRingCatIsoToRingEquiv with he_def
  have he : (Scheme.ΓSpecIso Γ(Y, V)).inv.hom = (e : Γ(Y, V) →+* Γ(Spec Γ(Y, V), ⊤)) := rfl
  rw [he, Ideal.map_comap_of_equiv, Ideal.map_comap_of_equiv] at h4
  exact Ideal.comap_injective_of_surjective _ e.symm.surjective h4


end DeJongAlterations.Algebra.NodeFittingIdealSheaf
