/-
Copyright (c) 2026. All rights reserved.
-/
import Hironaka.Geometry.ProperSteinProjectiveCechFlatLocalFieldLift
import Hironaka.Geometry.ProperGeometricGlobalFunctionsBaseChange
import Hironaka.Geometry.ProperSteinGlobalIdempotentsThickening
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! # Literal original R/maximal closed fibres retain the whole prescribed-field fibre

Closed native pullback proofs adapted from
`EnvelopeProperty/EnvelopeProperty/Global/FibreCompletedLocal.lean`,
SHA256 0800cb7b8c96a097a786144ffbdee5ffb4df500a55e2c806381e17d4286c90b5.
The actual ORIGINAL quotient is R/maximal itself, preserving its presentation.
Both original source and prescribed-field structure maps are retained.
-/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.CompletedFieldFibre
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000

section Residue
variable {B K : Type u} [CommRing B] [IsLocalRing B] [Field K]
  (γ : B →+* K) (hγs : Function.Surjective γ)
  (hγk : RingHom.ker γ = IsLocalRing.maximalIdeal B)

/-- The literal ORIGINAL maximal-ideal quotient is the SAME original prescribed field. -/
def residueEquiv : B ⧸ IsLocalRing.maximalIdeal B ≃+* K :=
  (Ideal.quotEquivOfEq hγk.symm).trans (RingHom.quotientKerEquivOfSurjective hγs)

/-- EVERY original quotient coefficient retains its entire original field value. -/
theorem residueEquiv_mk (b : B) :
    residueEquiv γ hγs hγk (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B) b) = γ b := rfl

/-- The WHOLE inverse preserves exactly the literal ORIGINAL maximal-ideal quotient map. -/
theorem residueEquiv_symm_comp :
    (residueEquiv γ hγs hγk).symm.toRingHom.comp γ = Ideal.Quotient.mk (IsLocalRing.maximalIdeal B) := by
  ext b
  apply (residueEquiv γ hγs hγk).injective
  change residueEquiv γ hγs hγk ((residueEquiv γ hγs hγk).symm (γ b)) =
    residueEquiv γ hγs hγk (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B) b)
  rw [RingEquiv.apply_symm_apply, residueEquiv_mk]

/-- The genuine WHOLE original residue-scheme isomorphism uses the actual original coefficient quotient. -/
def residueSpecIso : Spec (.of (B ⧸ IsLocalRing.maximalIdeal B)) ≅ Spec (.of K) :=
  Scheme.Spec.mapIso (residueEquiv γ hγs hγk).symm.toCommRingCatIso.op

/-- The ENTIRE original residue-scheme coefficient triangle is retained. -/
theorem residueSpecIso_coefficient :
    (residueSpecIso γ hγs hγk).hom ≫ Spec.map (CommRingCat.ofHom γ) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B))) := by
  change Spec.map (CommRingCat.ofHom (residueEquiv γ hγs hγk).symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom γ) = _
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((residueEquiv γ hγs hγk).symm.toRingHom.comp γ)) = _
  rw [residueEquiv_symm_comp]

variable {Y : Scheme.{u}} (g : Y ⟶ Spec (.of B))

/-- Actual base change of the original residue equivalence identifies the WHOLE literal nonreduced fibres. -/
def residuePullbackIso :
    ProperSteinGlobalIdempotents.closedFiber g (IsLocalRing.maximalIdeal B) ≅
      pullback g (Spec.map (CommRingCat.ofHom γ)) := by
  let e := residueSpecIso γ hγs hγk
  let a := pullback.map g (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B))))
    g (Spec.map (CommRingCat.ofHom γ)) (𝟙 Y) e.hom (𝟙 _)
    (by simp) (by simpa only [Category.comp_id] using (residueSpecIso_coefficient γ hγs hγk).symm)
  exact asIso a

/-- The actual whole residue comparison retains the ORIGINAL total-scheme projection. -/
theorem residuePullbackIso_projection :
    (residuePullbackIso γ hγs hγk g).hom ≫ pullback.fst _ _ =
      pullback.fst g (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B)))) := by
  simp only [residuePullbackIso, asIso_hom, pullback.map, pullback.lift_fst, Category.comp_id]

/-- The SAME residue comparison retains the ENTIRE original prescribed-field structure. -/
theorem residuePullbackIso_structure :
    (residuePullbackIso γ hγs hγk g).hom ≫ pullback.snd _ _ =
      pullback.snd g (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B)))) ≫
        (residueSpecIso γ hγs hγk).hom := by
  simp only [residuePullbackIso, asIso_hom, pullback.map, pullback.lift_snd]
end Residue

section Tower
variable {A B K : Type u} [CommRing A] [CommRing B] [IsLocalRing B] [Field K]
  [Algebra A B] (w : A →+* K) (γ : B →+* K)
  (hγs : Function.Surjective γ) (hγk : RingHom.ker γ = IsLocalRing.maximalIdeal B)
  (hγw : γ.comp (algebraMap A B) = w)
  {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

omit [IsLocalRing B] in
include hγw in
/-- The WHOLE original coefficient identity gives the exact ORIGINAL spectrum triangle. -/
theorem coefficientSpec_comp :
    Spec.map (CommRingCat.ofHom γ) ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) =
      Spec.map (CommRingCat.ofHom w) := by
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (γ.comp (algebraMap A B))) = _
  rw [hγw]

/-- The SAME actual completed maximal-ideal closed fibre is the WHOLE original prescribed-field fibre. -/
def closedFibreIso :
    ProperSteinGlobalIdempotents.closedFiber
      (ProperGeometricGlobalFunctions.structureMap (S := B) f) (IsLocalRing.maximalIdeal B) ≅
      pullback f (Spec.map (CommRingCat.ofHom w)) :=
  residuePullbackIso γ hγs hγk (ProperGeometricGlobalFunctions.structureMap (S := B) f) ≪≫
    pullbackLeftPullbackSndIso f (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom γ)) ≪≫
        pullback.congrHom rfl (coefficientSpec_comp w γ hγw)

/-- The WHOLE original fibre comparison preserves the exact original map to X. -/
theorem closedFibreIso_projection :
    (closedFibreIso w γ hγs hγk hγw f).hom ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ ProperGeometricGlobalFunctions.firstProjection (S := B) f := by
  simp only [closedFibreIso, Iso.trans_hom, Category.assoc, pullback.congrHom_hom,
    pullback.map, pullback.lift_fst, Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]
  rw [← Category.assoc, residuePullbackIso_projection]

/-- The SAME whole comparison preserves the original prescribed-field structure map. -/
theorem closedFibreIso_structure :
    (closedFibreIso w γ hγs hγk hγw f).hom ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ (residueSpecIso γ hγs hγk).hom := by
  simp only [closedFibreIso, Iso.trans_hom, Category.assoc, pullback.congrHom_hom,
    pullback.map, pullback.lift_snd, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]
  exact residuePullbackIso_structure γ hγs hγk _
end Tower

section Presentation
variable {F A K : Type u} [Field F] [CommRing A] [Field K]
  [Algebra F A] [Algebra F K] [Algebra.FiniteType F A]
  (w : A →ₐ[F] K) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- Every ORIGINAL field point internally constructs the actual Noetherian complete flat coefficient model and the original whole-fibre projection comparison. -/
theorem exists_noetherian_completed_field_fibre_presentation :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (_ : IsNoetherianRing B)
      (_ : IsLocalRing B), Module.Flat A B ∧ IsAdicComplete (IsLocalRing.maximalIdeal B) B ∧
      ∃ γ : B →+* K, ∃ hγs : Function.Surjective γ, ∃ hγk : RingHom.ker γ = IsLocalRing.maximalIdeal B,
      ∃ hγw : γ.comp (algebraMap A B) = w.toRingHom,
      (closedFibreIso w.toRingHom γ hγs hγk hγw f).hom ≫ pullback.fst _ _ =
        pullback.fst _ _ ≫ ProperGeometricGlobalFunctions.firstProjection (S := B) f ∧
      (closedFibreIso w.toRingHom γ hγs hγk hγw f).hom ≫ pullback.snd _ _ =
        pullback.snd _ _ ≫ (residueSpecIso γ hγs hγk).hom := by
  obtain ⟨B, hRing, hAlg, hNoeth, hLocal, hFlat, hComplete, γ, hγs, hγk, hγw⟩ :=
    FlatLocalFieldLift.exists_noetherian_completed_flat_local_lift w
  exact ⟨B, hRing, hAlg, hNoeth, hLocal, hFlat, hComplete, γ, hγs, hγk, hγw,
    closedFibreIso_projection w.toRingHom γ hγs hγk hγw f,
    closedFibreIso_structure w.toRingHom γ hγs hγk hγw f⟩
end Presentation
end Hironaka.Geometry.ProperSteinProjectiveCech.CompletedFieldFibre
