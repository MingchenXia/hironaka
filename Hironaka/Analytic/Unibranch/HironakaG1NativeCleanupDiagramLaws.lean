import Hironaka.Analytic.Unibranch.HironakaG1NativeCleanupDiagramComponents

/-! # Unique native cleanup diagram comparisons and exact functor laws

Constructed ACTUAL diagram comparisons reduce arbitrary candidate lifts
to endomorphisms of the SAME source cleanup. The HELD cleanupLift_eq
then gives full native uniqueness. Identity, composition/cocycle, inverse
and whole original ideal transport are derived, with no new geometric or
comparison-law certificate. Blueprint precedes source.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG1NativeCleanupDiagramLaws

open Hironaka HironakaNativePulledIdealSheaf
  HironakaIntrinsicComplexAnalyticRegularLocus SourceReducedComplexSpace
  HironakaG1NativeCleanupComponentModelIndependence

noncomputable section

private theorem inverseSquare {C : Type*} [Category C] {A B S T : C}
    (e : A ≅ B) (v : S ≅ T) (f : A ⟶ S) (g : B ⟶ T)
    (h : e.hom ≫ g = f ≫ v.hom) : e.inv ≫ f = g ≫ v.inv := by
  have H : e.inv ≫ (f ≫ v.hom) = g := by
    rw [← h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  calc
    e.inv ≫ f = (e.inv ≫ (f ≫ v.hom)) ≫ v.inv := by
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = g ≫ v.inv := by rw [H]

variable {X X' Y Y' : SourceReducedComplexSpace}

/-- ANY full native lifts over the actual diagram are equal, by reduction
to the HELD uniqueness of endomorphisms over the SAME original source. -/
theorem lift_eq
    (p' : Y' ⟶ X') (p : Y ⟶ X) (hp' : IsResolution p') (hp : IsResolution p)
    (u : X' ≅ X) (v : Y' ≅ Y) (hdiag : p' ≫ u.hom = v.hom ≫ p)
    (A' : ∀ c, ComponentModel hp'.1 c) (A : ∀ c, ComponentModel hp.1 c)
    (f g : cleanupSource p' hp' A' ⟶ cleanupSource p hp A)
    (hf : f ≫ cleanupProjection p hp A = cleanupProjection p' hp' A' ≫ v.hom)
    (hg : g ≫ cleanupProjection p hp A = cleanupProjection p' hp' A' ≫ v.hom) : f = g := by
  obtain ⟨E, hE, _, _⟩ := HironakaG1NativeCleanupDiagramComponents.exists_cleanup_diagram_iso
    p' p hp' hp u v hdiag A' A
  have hi := inverseSquare E v (cleanupProjection p' hp' A') (cleanupProjection p hp A) hE
  have hsf : (f ≫ E.inv) ≫ cleanupProjection p' hp' A' = cleanupProjection p' hp' A' := by
    rw [Category.assoc, hi, ← Category.assoc, hf, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hsg : (g ≫ E.inv) ≫ cleanupProjection p' hp' A' = cleanupProjection p' hp' A' := by
    rw [Category.assoc, hi, ← Category.assoc, hg, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have heq := HironakaG1NativeCleanupComparisonLaws.cleanupLift_eq p' hp' A' A'
    (f ≫ E.inv) (g ≫ E.inv) hsf hsg
  exact (cancel_mono E.inv).mp heq

/-- Actual original diagram squares compose internally. -/
theorem composite_diagram_square
    {X₀ X₁ X₂ Y₀ Y₁ Y₂ : SourceReducedComplexSpace}
    (p₀ : Y₀ ⟶ X₀) (p₁ : Y₁ ⟶ X₁) (p₂ : Y₂ ⟶ X₂)
    (u₀₁ : X₀ ≅ X₁) (v₀₁ : Y₀ ≅ Y₁) (u₁₂ : X₁ ≅ X₂) (v₁₂ : Y₁ ≅ Y₂)
    (h₀₁ : p₀ ≫ u₀₁.hom = v₀₁.hom ≫ p₁) (h₁₂ : p₁ ≫ u₁₂.hom = v₁₂.hom ≫ p₂) :
    p₀ ≫ (u₀₁.trans u₁₂).hom = (v₀₁.trans v₁₂).hom ≫ p₂ := by
  rw [Iso.trans_hom, Iso.trans_hom, ← Category.assoc, h₀₁, Category.assoc, h₁₂, ← Category.assoc]

/-- The inverse original diagram square follows from the true inverse equations. -/
theorem inverse_diagram_square
    (p' : Y' ⟶ X') (p : Y ⟶ X) (u : X' ≅ X) (v : Y' ≅ Y)
    (hdiag : p' ≫ u.hom = v.hom ≫ p) : p ≫ u.symm.hom = v.symm.hom ≫ p' :=
  (inverseSquare v u p' p hdiag.symm).symm

/-- Choose the already-constructed ACTUAL arbitrary-component native diagram iso. -/
def comparison
    (p' : Y' ⟶ X') (p : Y ⟶ X) (hp' : IsResolution p') (hp : IsResolution p)
    (u : X' ≅ X) (v : Y' ≅ Y) (hdiag : p' ≫ u.hom = v.hom ≫ p)
    (A' : ∀ c, ComponentModel hp'.1 c) (A : ∀ c, ComponentModel hp.1 c) :
    cleanupSource p' hp' A' ≅ cleanupSource p hp A :=
  Classical.choose (HironakaG1NativeCleanupDiagramComponents.exists_cleanup_diagram_iso
    p' p hp' hp u v hdiag A' A)

/-- The SAME full native square over the actual source isomorphism. -/
theorem comparison_overY
    (p' : Y' ⟶ X') (p : Y ⟶ X) (hp' : IsResolution p') (hp : IsResolution p)
    (u : X' ≅ X) (v : Y' ≅ Y) (hdiag : p' ≫ u.hom = v.hom ≫ p)
    (A' : ∀ c, ComponentModel hp'.1 c) (A : ∀ c, ComponentModel hp.1 c) :
    (comparison p' p hp' hp u v hdiag A' A).hom ≫ cleanupProjection p hp A =
      cleanupProjection p' hp' A' ≫ v.hom :=
  (Classical.choose_spec (HironakaG1NativeCleanupDiagramComponents.exists_cleanup_diagram_iso
    p' p hp' hp u v hdiag A' A)).1

/-- The SAME full native square over the actual original base isomorphism. -/
theorem comparison_overX
    (p' : Y' ⟶ X') (p : Y ⟶ X) (hp' : IsResolution p') (hp : IsResolution p)
    (u : X' ≅ X) (v : Y' ≅ Y) (hdiag : p' ≫ u.hom = v.hom ≫ p)
    (A' : ∀ c, ComponentModel hp'.1 c) (A : ∀ c, ComponentModel hp.1 c) :
    (comparison p' p hp' hp u v hdiag A' A).hom ≫ cleanupMorphism p hp A =
      cleanupMorphism p' hp' A' ≫ u.hom :=
  (Classical.choose_spec (HironakaG1NativeCleanupDiagramComponents.exists_cleanup_diagram_iso
    p' p hp' hp u v hdiag A' A)).2.1

/-- Exact inverse ORIGINAL regular loci for the SAME actual comparison. -/
theorem comparison_regularPreimage
    (p' : Y' ⟶ X') (p : Y ⟶ X) (hp' : IsResolution p') (hp : IsResolution p)
    (u : X' ≅ X) (v : Y' ≅ Y) (hdiag : p' ≫ u.hom = v.hom ≫ p)
    (A' : ∀ c, ComponentModel hp'.1 c) (A : ∀ c, ComponentModel hp.1 c) :
    (comparison p' p hp' hp u v hdiag A' A).hom.hom.left.base ⁻¹'
        ((cleanupMorphism p hp A).hom.left.base ⁻¹' intrinsicRegularLocus X.obj) =
      (cleanupMorphism p' hp' A').hom.left.base ⁻¹' intrinsicRegularLocus X'.obj :=
  (Classical.choose_spec (HironakaG1NativeCleanupDiagramComponents.exists_cleanup_diagram_iso
    p' p hp' hp u v hdiag A' A)).2.2

/-- Identity original diagrams recover the HELD comparisons of independent models. -/
theorem comparison_refl_models
    (p : Y ⟶ X) (hp : IsResolution p) (A B : ∀ c, ComponentModel hp.1 c) :
    comparison p p hp hp (Iso.refl X) (Iso.refl Y) (by simp) A B =
      HironakaG1NativeCleanupComparisonLaws.comparison p hp A B := by
  apply Iso.ext
  apply lift_eq p p hp hp (Iso.refl X) (Iso.refl Y) (by simp) A B
  · exact comparison_overY p p hp hp (Iso.refl X) (Iso.refl Y) (by simp) A B
  · simpa using HironakaG1NativeCleanupComparisonLaws.comparison_overY p hp A B

/-- The true identity law, reusing the HELD model-comparison identity. -/
theorem comparison_id (p : Y ⟶ X) (hp : IsResolution p) (A : ∀ c, ComponentModel hp.1 c) :
    comparison p p hp hp (Iso.refl X) (Iso.refl Y) (by simp) A A = Iso.refl (cleanupSource p hp A) := by
  rw [comparison_refl_models, HironakaG1NativeCleanupComparisonLaws.comparison_id]

/-- Composition/cocycle for THREE ordinary diagrams and independent actual models. -/
theorem comparison_trans
    {X₀ X₁ X₂ Y₀ Y₁ Y₂ : SourceReducedComplexSpace}
    (p₀ : Y₀ ⟶ X₀) (p₁ : Y₁ ⟶ X₁) (p₂ : Y₂ ⟶ X₂)
    (hp₀ : IsResolution p₀) (hp₁ : IsResolution p₁) (hp₂ : IsResolution p₂)
    (u₀₁ : X₀ ≅ X₁) (v₀₁ : Y₀ ≅ Y₁) (u₁₂ : X₁ ≅ X₂) (v₁₂ : Y₁ ≅ Y₂)
    (h₀₁ : p₀ ≫ u₀₁.hom = v₀₁.hom ≫ p₁) (h₁₂ : p₁ ≫ u₁₂.hom = v₁₂.hom ≫ p₂)
    (A₀ : ∀ c, ComponentModel hp₀.1 c) (A₁ : ∀ c, ComponentModel hp₁.1 c)
    (A₂ : ∀ c, ComponentModel hp₂.1 c) :
    (comparison p₀ p₁ hp₀ hp₁ u₀₁ v₀₁ h₀₁ A₀ A₁).trans
        (comparison p₁ p₂ hp₁ hp₂ u₁₂ v₁₂ h₁₂ A₁ A₂) =
      comparison p₀ p₂ hp₀ hp₂ (u₀₁.trans u₁₂) (v₀₁.trans v₁₂)
        (composite_diagram_square p₀ p₁ p₂ u₀₁ v₀₁ u₁₂ v₁₂ h₀₁ h₁₂) A₀ A₂ := by
  apply Iso.ext
  apply lift_eq p₀ p₂ hp₀ hp₂ (u₀₁.trans u₁₂) (v₀₁.trans v₁₂)
    (composite_diagram_square p₀ p₁ p₂ u₀₁ v₀₁ u₁₂ v₁₂ h₀₁ h₁₂) A₀ A₂
  · change ((comparison p₀ p₁ hp₀ hp₁ u₀₁ v₀₁ h₀₁ A₀ A₁).hom ≫
        (comparison p₁ p₂ hp₁ hp₂ u₁₂ v₁₂ h₁₂ A₁ A₂).hom) ≫ cleanupProjection p₂ hp₂ A₂ = _
    rw [Category.assoc, comparison_overY, ← Category.assoc, comparison_overY, Category.assoc,
      Iso.trans_hom]
  · exact comparison_overY _ _ _ _ _ _ _ _ _

/-- The genuine inverse is the chosen comparison of the actual inverse diagram. -/
theorem comparison_symm
    (p' : Y' ⟶ X') (p : Y ⟶ X) (hp' : IsResolution p') (hp : IsResolution p)
    (u : X' ≅ X) (v : Y' ≅ Y) (hdiag : p' ≫ u.hom = v.hom ≫ p)
    (A' : ∀ c, ComponentModel hp'.1 c) (A : ∀ c, ComponentModel hp.1 c) :
    (comparison p' p hp' hp u v hdiag A' A).symm =
      comparison p p' hp hp' u.symm v.symm (inverse_diagram_square p' p u v hdiag) A A' := by
  apply Iso.ext
  apply lift_eq p p' hp hp' u.symm v.symm (inverse_diagram_square p' p u v hdiag) A A'
  · exact inverseSquare (comparison p' p hp' hp u v hdiag A' A) v
      (cleanupProjection p' hp' A') (cleanupProjection p hp A)
      (comparison_overY p' p hp' hp u v hdiag A' A)
  · exact comparison_overY _ _ _ _ _ _ _ _ _

/-- SAME chosen diagram comparison, ENTIRE native totalideal and BOTH original inclusions. -/
theorem comparison_totalIdeal_transport
    (p' : Y' ⟶ X') (p : Y ⟶ X) (hp' : IsResolution p') (hp : IsResolution p)
    (u : X' ≅ X) (v : Y' ≅ Y) (hdiag : p' ≫ u.hom = v.hom ≫ p)
    (A' : ∀ c, ComponentModel hp'.1 c) (A : ∀ c, ComponentModel hp.1 c) :
    ∃ I : nativePulledIdealModule (comparison p' p hp' hp u v hdiag A' A).hom.hom.left
        (totalIdealModule p hp A) (totalIdealInclusion p hp A) ≅ totalIdealModule p' hp' A',
      I.hom ≫ totalIdealInclusion p' hp' A' =
        nativePulledIdealInclusion (comparison p' p hp' hp u v hdiag A' A).hom.hom.left
          (totalIdealModule p hp A) (totalIdealInclusion p hp A) ∧
      I.inv ≫ nativePulledIdealInclusion (comparison p' p hp' hp u v hdiag A' A).hom.hom.left
        (totalIdealModule p hp A) (totalIdealInclusion p hp A) = totalIdealInclusion p' hp' A' :=
  ⟨HironakaG1NativeCleanupDiagramComponents.totalIdealIso_of_diagram p' p hp' hp u A' A
      (comparison p' p hp' hp u v hdiag A' A) (comparison_overX p' p hp' hp u v hdiag A' A),
    HironakaG1NativeCleanupDiagramComponents.totalIdealIso_hom_comp_inclusion p' p hp' hp u A' A
      (comparison p' p hp' hp u v hdiag A' A) (comparison_overX p' p hp' hp u v hdiag A' A),
    HironakaG1NativeCleanupDiagramComponents.totalIdealIso_inv_comp_inclusion p' p hp' hp u A' A
      (comparison p' p hp' hp u v hdiag A' A) (comparison_overX p' p hp' hp u v hdiag A' A)⟩

end
end Hironaka.Analytic.Unibranch.HironakaG1NativeCleanupDiagramLaws
