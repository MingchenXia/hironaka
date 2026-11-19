import Mathlib.AlgebraicGeometry.ResidueField

/-! # Compatibility of native affine and ideal residue-field maps -/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.ResidueExtensionLift

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual affine residue-field comparison is natural for the actual spectrum map. -/
theorem spec_residueFieldIso_naturality {R S : CommRingCat.{u}} (φ : R ⟶ S) (q : Spec S) :
    (Scheme.Spec.residueFieldIso R (Spec.map φ q)).inv ≫
      (Spec.map φ).residueFieldMap q ≫ (Scheme.Spec.residueFieldIso S q).hom =
      CommRingCat.ofHom (Ideal.ResidueField.map (Spec.map φ q).asIdeal q.asIdeal φ.hom rfl) := by
  have hS : (Scheme.ΓSpecIso S).inv ≫ (Spec S).Γevaluation q ≫
      (Scheme.Spec.residueFieldIso S q).hom =
      CommRingCat.ofHom (algebraMap S q.asIdeal.ResidueField) := by
    have h := congrArg (fun m => m ≫ (Scheme.Spec.residueFieldIso S q).hom)
      (Scheme.Spec.algebraMap_residueFieldIso_inv S q)
    simpa only [Scheme.Γevaluation, Scheme.evaluation, Category.assoc,
      Iso.inv_hom_id, Category.comp_id] using h.symm
  have h : CommRingCat.ofHom (algebraMap R (Spec.map φ q).asIdeal.ResidueField) ≫
      (Scheme.Spec.residueFieldIso R (Spec.map φ q)).inv ≫
        (Spec.map φ).residueFieldMap q ≫ (Scheme.Spec.residueFieldIso S q).hom =
        φ ≫ CommRingCat.ofHom (algebraMap S q.asIdeal.ResidueField) := by
    rw [Scheme.Spec.algebraMap_residueFieldIso_inv_assoc]
    change (Scheme.ΓSpecIso R).inv ≫ (Spec R).Γevaluation (Spec.map φ q) ≫
      (Spec.map φ).residueFieldMap q ≫ (Scheme.Spec.residueFieldIso S q).hom = _
    rw [Scheme.Γevaluation_naturality_assoc, ← Scheme.ΓSpecIso_inv_naturality_assoc, hS]
  apply CommRingCat.hom_ext
  apply Ideal.ResidueField.ringHom_ext
  ext r
  change ((Scheme.Spec.residueFieldIso R (Spec.map φ q)).inv ≫
    (Spec.map φ).residueFieldMap q ≫ (Scheme.Spec.residueFieldIso S q).hom)
      (algebraMap R (Spec.map φ q).asIdeal.ResidueField r) =
    Ideal.ResidueField.map (Spec.map φ q).asIdeal q.asIdeal φ.hom rfl
      (algebraMap R (Spec.map φ q).asIdeal.ResidueField r)
  rw [Ideal.ResidueField.map_algebraMap]
  exact ConcreteCategory.congr_hom h r

/-- The same native comparison with an explicitly identified original base point. -/
theorem spec_residueFieldMap_congr {R S : CommRingCat.{u}} (φ : R ⟶ S) (q : Spec S)
    (p : Spec R) (h : Spec.map φ q = p) :
    (Scheme.Spec.residueFieldIso R p).inv ≫
      ((Spec R).residueFieldCongr h).inv ≫ (Spec.map φ).residueFieldMap q ≫
        (Scheme.Spec.residueFieldIso S q).hom =
      CommRingCat.ofHom (Ideal.ResidueField.map p.asIdeal q.asIdeal φ.hom
        (congrArg PrimeSpectrum.asIdeal h).symm) := by
  subst p
  simpa only [Scheme.residueFieldCongr_refl, Iso.refl_inv, Category.id_comp] using
    spec_residueFieldIso_naturality φ q

/-- Actual scheme residue maps transport along a target isomorphism and identified points. -/
theorem residueFieldMap_targetIso {X Y Z : Scheme.{u}} (e : Y ≅ Z)
    (f : X ⟶ Y) (g : X ⟶ Z) (h : f ≫ e.hom = g)
    (x : X) (y : Y) (hy : f x = y) (hz : g x = e.hom y) :
    e.hom.residueFieldMap y ≫ (Y.residueFieldCongr hy).inv ≫ f.residueFieldMap x =
      (Z.residueFieldCongr hz).inv ≫ g.residueFieldMap x := by
  subst g
  subst y
  simp only [Scheme.residueFieldCongr_refl, Iso.refl_inv, Category.id_comp,
    Scheme.residueFieldMap_comp]
  exact (Category.id_comp _).symm

end Hironaka.Geometry.ResidueExtensionLift
