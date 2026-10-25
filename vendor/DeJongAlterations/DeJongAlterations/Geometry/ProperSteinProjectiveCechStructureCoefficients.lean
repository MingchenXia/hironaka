/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import DeJongAlterations.Geometry.ProperSteinProjectiveCechGradedCoefficients

/-!
# Actual projective structure coefficients equal the original regular constants

Only the closed native structure-square helpers are adapted from
`EnvelopeProperty/deps/aintlib-ep33/ModularCurves/ForMathlib/ProjToSpecZero.lean`,
SHA256 ed171b450dbc598f89434b440b37301666011526ceaefe74317503946ee5c24d.
No other-project import is retained. The global coefficient identity is derived
from the actual positive homogeneous cover and original full-prime sections.
-/
universe u
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
namespace DeJongAlterations.Geometry.ProperSteinProjectiveCech
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {R A S : Type u} [CommRing R] [CommRing A] [Algebra R A] [CommRing S]
/-- For a positive-degree homogeneous element, the map on global sections induced by
`Proj.awayι` is restriction to the basic open followed by the inverse of the canonical
homogeneous-localization presentation. -/
theorem projectiveAwayPullbackSquare (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    {m : ℕ} (f : A) (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    (Proj.awayι 𝒜 f f_deg hm).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).hom =
    (Proj 𝒜).presheaf.map (homOfLE le_top).op ≫
      (Proj.basicOpenIsoAway 𝒜 f f_deg hm).inv := by
  rw [Iso.eq_comp_inv, Category.assoc]
  have hσ : (Proj.basicOpenIsoAway 𝒜 f f_deg hm).hom = Proj.awayToSection 𝒜 f := rfl
  rw [hσ]
  have hhomTop : (Proj.basicOpenToSpec 𝒜 f).appTop ≫
      (Proj.basicOpen 𝒜 f).topIso.hom =
      (Scheme.ΓSpecIso _).hom ≫ Proj.awayToSection 𝒜 f := by
    rw [show (Proj.basicOpenToSpec 𝒜 f).appTop =
      (Proj.basicOpenToSpec 𝒜 f).app ⊤ from rfl]
    rw [Proj.basicOpenToSpec_app_top, Category.assoc, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  rw [← hhomTop, ← Proj.basicOpenIsoSpec_inv_ι 𝒜 f f_deg hm,
    Scheme.Hom.comp_appTop, Category.assoc]
  rw [show Proj.basicOpenToSpec 𝒜 f =
    (Proj.basicOpenIsoSpec 𝒜 f f_deg hm).hom from rfl]
  rw [← Category.assoc ((Proj.basicOpenIsoSpec 𝒜 f f_deg hm).inv.appTop)]
  rw [show (Proj.basicOpenIsoSpec 𝒜 f f_deg hm).inv.appTop ≫
      (Proj.basicOpenIsoSpec 𝒜 f f_deg hm).hom.appTop = 𝟙 _ from by
    rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id]
    simp]
  rw [Category.id_comp, Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
  refine ((Proj 𝒜).presheaf.map_comp _ _).symm.trans
    (congrArg ((Proj 𝒜).presheaf.map) ?_)
  exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)

/-- The composite from a coefficient ring to sections on a positive projective basic open,
then to its degree-zero homogeneous localization, is the canonical degree-zero map. -/
theorem projectiveStructureSectionSquare (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (c : S →+* 𝒜 0) {m : ℕ} (f : A) (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫
      (Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom c)).appTop ≫
      (Proj 𝒜).presheaf.map (homOfLE le_top).op ≫
      (Proj.basicOpenIsoAway 𝒜 f f_deg hm).inv =
    CommRingCat.ofHom
      ((HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f)).comp c) := by
  have hbridge := projectiveAwayPullbackSquare 𝒜 f f_deg hm
  have hscheme :
      Proj.awayι 𝒜 f f_deg hm ≫
          (Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom c)) =
        Spec.map (CommRingCat.ofHom
          ((HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f)).comp c)) := by
    rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
  have hΓ := congrArg Scheme.Hom.appTop hscheme
  rw [Scheme.Hom.comp_appTop] at hΓ
  calc
    (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫
          (Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom c)).appTop ≫
          (Proj 𝒜).presheaf.map (homOfLE le_top).op ≫
          (Proj.basicOpenIsoAway 𝒜 f f_deg hm).inv =
        (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫
          ((Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom c)).appTop ≫
            (Proj.awayι 𝒜 f f_deg hm).appTop) ≫
          (Scheme.ΓSpecIso
            (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).hom := by
      rw [← hbridge]
      simp only [Category.assoc]
    _ = (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫
          (Spec.map (CommRingCat.ofHom
            ((HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f)).comp c))).appTop ≫
          (Scheme.ΓSpecIso
            (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).hom := by
      rw [hΓ]
    _ = _ := by
      rw [Scheme.ΓSpecIso_naturality, ← Category.assoc, Iso.inv_hom_id,
        Category.id_comp]


/-- Every original constant restricts to its literal original unit-denominator fraction. -/
theorem gradedProjectiveConstants_basicOpen (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : A) (r : R) :
    (Proj 𝒜).presheaf.map (homOfLE (show Proj.basicOpen 𝒜 f ≤ ⊤ from le_top)).op
      (gradedProjectiveConstants 𝒜 ⊤ r) =
    Proj.awayToSection 𝒜 f
      (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f) (gradedCoefficientZero 𝒜 r)) := by
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective
  rfl

/-- The SAME literal native structure morphism induces EXACTLY the original coefficient action. -/
theorem gradedProjectiveConstants_structure (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] :
    gradedProjectiveConstants 𝒜 ⊤ =
      ((Scheme.ΓSpecIso (.of R)).inv ≫
        (Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (gradedCoefficientZero 𝒜))).appTop).hom := by
  ext r
  apply TopCat.Presheaf.IsSheaf.section_ext (F := (Proj 𝒜).presheaf) (Proj 𝒜).sheaf.property
  intro x hx
  let C := Proj.affineOpenCover 𝒜
  let j := C.openCover.idx x
  have hx' : x ∈ Proj.basicOpen 𝒜 (j.2 : A) := by
    have h := C.openCover.covers x
    change x ∈ (Proj.awayι 𝒜 (j.2 : A) j.2.2 j.1.2).opensRange at h
    rwa [Proj.opensRange_awayι] at h
  refine ⟨Proj.basicOpen 𝒜 (j.2 : A), le_top, hx', ?_⟩
  apply (Proj.basicOpenIsoAway 𝒜 (j.2 : A) j.2.2 j.1.2).commRingCatIsoToRingEquiv.symm.injective
  have h := ConcreteCategory.congr_hom
    (projectiveStructureSectionSquare 𝒜 (gradedCoefficientZero 𝒜) (j.2 : A) j.2.2 j.1.2) r
  rw [gradedProjectiveConstants_basicOpen 𝒜 (j.2 : A)]
  exact (ConcreteCategory.congr_hom (Proj.basicOpenIsoAway 𝒜 (j.2 : A) j.2.2 j.1.2).hom_inv_id
    (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers (j.2 : A))
      (gradedCoefficientZero 𝒜 r))).trans h.symm

end
end DeJongAlterations.Geometry.ProperSteinProjectiveCech
