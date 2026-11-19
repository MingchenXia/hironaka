import Hironaka.Analytic.Unibranch.HironakaG1NativeSmoothCleanup

/-! # Unique actual native smooth cleanup arrows and exact laws

Noninvertible diagrams use TRUE dense source good loci and smooth original
regular reflection, never inverse cancellation. HELD dense-lift uniqueness
and full native faithfulness derive all comparison/operator laws.
Blueprint precedes source; ordinary initial resolutions remain inputs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG1NativeSmoothCleanupLaws

open Hironaka HironakaIntrinsicComplexAnalyticRegularLocus
  HironakaNativePulledIdealSheaf SourceReducedComplexSpace OriginalNativeSmoothLocalProduct
  OriginalNativeSmoothComposition OriginalNativeSmoothSingularLocus
  HironakaG1NativeCleanupComponentModelIndependence HironakaG1NativeSmoothCleanup

noncomputable section

variable {X X' Y Y' : SourceReducedComplexSpace}

/-- ANY native lifts over a genuine smooth-base diagram coincide.  The source
arrow need not be invertible or smooth for this uniqueness theorem. -/
theorem lift_eq
    (p' : Y' ⟶ X') (p : Y ⟶ X) (hp' : IsResolution p') (hp : IsResolution p)
    (u : X' ⟶ X) (hu : IsSmoothMorphism u) (g : Y' ⟶ Y) (hdiag : p' ≫ u = g ≫ p)
    (A' : ∀ c, ComponentModel hp'.1 c) (A : ∀ c, ComponentModel hp.1 c)
    (f k : cleanupSource p' hp' A' ⟶ cleanupSource p hp A)
    (hf : f ≫ cleanupProjection p hp A = cleanupProjection p' hp' A' ≫ g)
    (hk : k ≫ cleanupProjection p hp A = cleanupProjection p' hp' A' ≫ g) : f = k := by
  have hbase : ∀ z, (cleanupProjection p hp A).hom.left.base (f.hom.left.base z) =
      (cleanupProjection p hp A).hom.left.base (k.hom.left.base z) := fun z =>
    congrArg (fun F : cleanupSource p' hp' A' ⟶ Y => F.hom.left.base z) (hf.trans hk.symm)
  have hDU (z : (cleanupSource p' hp' A').obj.left)
      (hz : z ∈ ((cleanupMorphism p' hp' A').hom.left.base ⁻¹' intrinsicSingularLocus X'.obj)ᶜ) :
      (cleanupProjection p hp A).hom.left.base (f.hom.left.base z) ∈
        p.hom.left.base ⁻¹' intrinsicRegularLocus X.obj := by
    have hpz := congrArg (fun F : cleanupSource p' hp' A' ⟶ Y => F.hom.left.base z) hf
    change (cleanupProjection p hp A).hom.left.base (f.hom.left.base z) =
      g.hom.left.base ((cleanupProjection p' hp' A').hom.left.base z) at hpz
    change p.hom.left.base ((cleanupProjection p hp A).hom.left.base (f.hom.left.base z)) ∈ intrinsicRegularLocus X.obj
    rw [hpz]
    have hc := congrArg (fun F : Y' ⟶ X => F.hom.left.base ((cleanupProjection p' hp' A').hom.left.base z)) hdiag
    change u.hom.left.base (p'.hom.left.base ((cleanupProjection p' hp' A').hom.left.base z)) =
      p.hom.left.base (g.hom.left.base ((cleanupProjection p' hp' A').hom.left.base z)) at hc
    rw [← hc]
    exact (smoothAt_regular_iff u _ (hu _)).mp (not_not.mp hz)
  have heq := HironakaG11LiftUniqueness.eq_of_comp_eq_of_dense
    (HironakaG1NativeCleanupComparisonLaws.cleanupProjection_isIsoOver p hp A)
    f.hom.left.base.hom.continuous k.hom.left.base.hom.continuous hbase
    (HironakaG1NativeCleanupComparisonLaws.cleanupGood_dense p' hp' A') hDU
  apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
  intro z
  exact congrFun heq z

/-- The ACTUAL operator supplies the unique full native lift, without a law packet. -/
theorem existsUnique_cleanupMap
    (p' : Y' ⟶ X') (p : Y ⟶ X) (hp' : IsResolution p') (hp : IsResolution p)
    (u : X' ⟶ X) (hu : IsSmoothMorphism u) (g : Y' ⟶ Y) (hg : IsSmoothMorphism g)
    (hdiag : p' ≫ u = g ≫ p) (A' : ∀ c, ComponentModel hp'.1 c) (A : ∀ c, ComponentModel hp.1 c) :
    ∃! F : cleanupSource p' hp' A' ⟶ cleanupSource p hp A,
      F ≫ cleanupProjection p hp A = cleanupProjection p' hp' A' ≫ g := by
  refine ⟨cleanupMap p' p hp' hp u hu g hg hdiag A' A, cleanupMap_overY _ _ _ _ _ _ _ _ _ _ _, ?_⟩
  intro F hF
  exact lift_eq p' p hp' hp u hu g hdiag A' A F _ hF (cleanupMap_overY _ _ _ _ _ _ _ _ _ _ _)

/-- Identity original diagrams recover the HELD actual independent-model arrows. -/
theorem cleanupMap_identity_models
    (p : Y ⟶ X) (hp : IsResolution p) (A B : ∀ c, ComponentModel hp.1 c) :
    cleanupMap p p hp hp (𝟙 X) (isSmoothMorphism_identity X) (𝟙 Y) (isSmoothMorphism_identity Y)
        (by simp) A B = (HironakaG1NativeCleanupComparisonLaws.comparison p hp A B).hom := by
  apply lift_eq p p hp hp (𝟙 X) (isSmoothMorphism_identity X) (𝟙 Y) (by simp) A B
  · exact cleanupMap_overY _ _ _ _ _ _ _ _ _ _ _
  · simpa using HironakaG1NativeCleanupComparisonLaws.comparison_overY p hp A B

/-- Genuine identity law, reusing the HELD independent-model comparison identity. -/
theorem cleanupMap_identity
    (p : Y ⟶ X) (hp : IsResolution p) (A : ∀ c, ComponentModel hp.1 c) :
    cleanupMap p p hp hp (𝟙 X) (isSmoothMorphism_identity X) (𝟙 Y) (isSmoothMorphism_identity Y)
        (by simp) A A = 𝟙 (cleanupSource p hp A) := by
  rw [cleanupMap_identity_models, HironakaG1NativeCleanupComparisonLaws.comparison_id]
  rfl

/-- On an ACTUAL isomorphism diagram this is the SAME full previously proved arrow. -/
theorem cleanupMap_of_iso
    (p' : Y' ⟶ X') (p : Y ⟶ X) (hp' : IsResolution p') (hp : IsResolution p)
    (u : X' ≅ X) (v : Y' ≅ Y) (hdiag : p' ≫ u.hom = v.hom ≫ p)
    (A' : ∀ c, ComponentModel hp'.1 c) (A : ∀ c, ComponentModel hp.1 c) :
    cleanupMap p' p hp' hp u.hom (HironakaG1NativeCleanupDiagramIso.nativeIso_smooth u)
        v.hom (HironakaG1NativeCleanupDiagramIso.nativeIso_smooth v) hdiag A' A =
      (HironakaG1NativeCleanupDiagramLaws.comparison p' p hp' hp u v hdiag A' A).hom := by
  apply lift_eq p' p hp' hp u.hom (HironakaG1NativeCleanupDiagramIso.nativeIso_smooth u) v.hom hdiag A' A
  · exact cleanupMap_overY _ _ _ _ _ _ _ _ _ _ _
  · exact HironakaG1NativeCleanupDiagramLaws.comparison_overY _ _ _ _ _ _ _ _ _

/-- The full intertwining square for ANY independent source/target model choices. -/
theorem cleanupMap_model_naturality
    (p' : Y' ⟶ X') (p : Y ⟶ X) (hp' : IsResolution p') (hp : IsResolution p)
    (u : X' ⟶ X) (hu : IsSmoothMorphism u) (g : Y' ⟶ Y) (hg : IsSmoothMorphism g)
    (hdiag : p' ≫ u = g ≫ p) (A'₀ A'₁ : ∀ c, ComponentModel hp'.1 c)
    (A₀ A₁ : ∀ c, ComponentModel hp.1 c) :
    (HironakaG1NativeCleanupComparisonLaws.comparison p' hp' A'₀ A'₁).hom ≫
        cleanupMap p' p hp' hp u hu g hg hdiag A'₁ A₁ =
      cleanupMap p' p hp' hp u hu g hg hdiag A'₀ A₀ ≫
        (HironakaG1NativeCleanupComparisonLaws.comparison p hp A₀ A₁).hom := by
  apply lift_eq p' p hp' hp u hu g hdiag A'₀ A₁
  · rw [Category.assoc, cleanupMap_overY, ← Category.assoc,
      HironakaG1NativeCleanupComparisonLaws.comparison_overY]
  · rw [Category.assoc, HironakaG1NativeCleanupComparisonLaws.comparison_overY, cleanupMap_overY]

/-- The ordinary composite original square is DERIVED from the two actual squares. -/
theorem composite_diagram_square
    {X₀ X₁ X₂ Y₀ Y₁ Y₂ : SourceReducedComplexSpace}
    (p₀ : Y₀ ⟶ X₀) (p₁ : Y₁ ⟶ X₁) (p₂ : Y₂ ⟶ X₂)
    (u₀₁ : X₀ ⟶ X₁) (g₀₁ : Y₀ ⟶ Y₁) (u₁₂ : X₁ ⟶ X₂) (g₁₂ : Y₁ ⟶ Y₂)
    (h₀₁ : p₀ ≫ u₀₁ = g₀₁ ≫ p₁) (h₁₂ : p₁ ≫ u₁₂ = g₁₂ ≫ p₂) :
    p₀ ≫ (u₀₁ ≫ u₁₂) = (g₀₁ ≫ g₁₂) ≫ p₂ := by
  rw [← Category.assoc, h₀₁, Category.assoc, h₁₂, ← Category.assoc]

/-- Actual composition/cocycle on THREE compatible native smooth diagrams/models. -/
theorem cleanupMap_composition
    {X₀ X₁ X₂ Y₀ Y₁ Y₂ : SourceReducedComplexSpace}
    (p₀ : Y₀ ⟶ X₀) (p₁ : Y₁ ⟶ X₁) (p₂ : Y₂ ⟶ X₂)
    (hp₀ : IsResolution p₀) (hp₁ : IsResolution p₁) (hp₂ : IsResolution p₂)
    (u₀₁ : X₀ ⟶ X₁) (hu₀₁ : IsSmoothMorphism u₀₁) (g₀₁ : Y₀ ⟶ Y₁) (hg₀₁ : IsSmoothMorphism g₀₁)
    (u₁₂ : X₁ ⟶ X₂) (hu₁₂ : IsSmoothMorphism u₁₂) (g₁₂ : Y₁ ⟶ Y₂) (hg₁₂ : IsSmoothMorphism g₁₂)
    (h₀₁ : p₀ ≫ u₀₁ = g₀₁ ≫ p₁) (h₁₂ : p₁ ≫ u₁₂ = g₁₂ ≫ p₂)
    (A₀ : ∀ c, ComponentModel hp₀.1 c) (A₁ : ∀ c, ComponentModel hp₁.1 c)
    (A₂ : ∀ c, ComponentModel hp₂.1 c) :
    cleanupMap p₀ p₁ hp₀ hp₁ u₀₁ hu₀₁ g₀₁ hg₀₁ h₀₁ A₀ A₁ ≫
        cleanupMap p₁ p₂ hp₁ hp₂ u₁₂ hu₁₂ g₁₂ hg₁₂ h₁₂ A₁ A₂ =
      cleanupMap p₀ p₂ hp₀ hp₂ (u₀₁ ≫ u₁₂) (isSmoothMorphism_comp _ _ hu₀₁ hu₁₂)
        (g₀₁ ≫ g₁₂) (isSmoothMorphism_comp _ _ hg₀₁ hg₁₂)
        (composite_diagram_square p₀ p₁ p₂ u₀₁ g₀₁ u₁₂ g₁₂ h₀₁ h₁₂) A₀ A₂ := by
  apply lift_eq p₀ p₂ hp₀ hp₂ (u₀₁ ≫ u₁₂) (isSmoothMorphism_comp _ _ hu₀₁ hu₁₂)
    (g₀₁ ≫ g₁₂) (composite_diagram_square p₀ p₁ p₂ u₀₁ g₀₁ u₁₂ g₁₂ h₀₁ h₁₂) A₀ A₂
  · rw [Category.assoc, cleanupMap_overY, ← Category.assoc, cleanupMap_overY, Category.assoc]
  · exact cleanupMap_overY _ _ _ _ _ _ _ _ _ _ _

/-- SAME actual arrow, ENTIRE totalideal module and BOTH literal original inclusions. -/
theorem cleanupMap_totalIdeal_transport
    (p' : Y' ⟶ X') (p : Y ⟶ X) (hp' : IsResolution p') (hp : IsResolution p)
    (u : X' ⟶ X) (hu : IsSmoothMorphism u) (g : Y' ⟶ Y) (hg : IsSmoothMorphism g)
    (hdiag : p' ≫ u = g ≫ p) (A' : ∀ c, ComponentModel hp'.1 c) (A : ∀ c, ComponentModel hp.1 c) :
    ∃ I : nativePulledIdealModule (cleanupMap p' p hp' hp u hu g hg hdiag A' A).hom.left
        (totalIdealModule p hp A) (totalIdealInclusion p hp A) ≅ totalIdealModule p' hp' A',
      I.hom ≫ totalIdealInclusion p' hp' A' =
        nativePulledIdealInclusion (cleanupMap p' p hp' hp u hu g hg hdiag A' A).hom.left
          (totalIdealModule p hp A) (totalIdealInclusion p hp A) ∧
      I.inv ≫ nativePulledIdealInclusion (cleanupMap p' p hp' hp u hu g hg hdiag A' A).hom.left
        (totalIdealModule p hp A) (totalIdealInclusion p hp A) = totalIdealInclusion p' hp' A' :=
  ⟨totalIdealIso p' p hp' hp u hu g hg hdiag A' A,
    totalIdealIso_hom_comp_inclusion p' p hp' hp u hu g hg hdiag A' A,
    totalIdealIso_inv_comp_inclusion p' p hp' hp u hu g hg hdiag A' A⟩

end
end Hironaka.Analytic.Unibranch.HironakaG1NativeSmoothCleanupLaws
