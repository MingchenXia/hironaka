import Hironaka.Analytic.Unibranch.EmbeddedBlowupUniversal
import Hironaka.Analytic.Unibranch.EmbeddedCentreIdealIso
import Hironaka.Resolution.HironakaSingularSubspaceBlowupCartierUniversalProjectionInvertible

/-!
# Canonical ORIGINAL comparison of the literal embedded blowup models

Original isomorphisms of explicitly contained pairs produce the SAME whole
centre ideal equality. Projection invertibility and the original no-global-SC
universal property then construct both full comparison maps and their inverse
identities. No comparison map or ideal certificate is an input. The original
ambient dimensions may differ. General resolution canonicity is not asserted.
Blueprint: `embedded-blowup-comparison.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.EmbeddedBlowupComparison

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaSingularSubspaceBlowupLift
  HironakaSingularSubspaceBlowupCartierUniversalProjectionInvertible
  SourceReducedComplexSpace EmbeddedBlowup EmbeddedBlowupUniversal EmbeddedCentreIdealIso

noncomputable section

private theorem ideal_map_stalk_comp {X Y Z : LocallyRingedSpace}
    (F : X ⟶ Y) (G : Y ⟶ Z) (x : X)
    (I : Ideal (Z.presheaf.stalk ((F ≫ G).base x)).carrier) :
    Ideal.map ((F ≫ G).stalkMap x).hom I =
      Ideal.map (F.stalkMap x).hom (Ideal.map (G.stalkMap (F.base x)).hom I) := by
  rw [Ideal.map_map, LocallyRingedSpace.stalkMap_comp]
  rfl

variable {n₀ n₁ : ℕ} {M₀ Y₀ M₁ Y₁ : Type}
  [TopologicalSpace M₀] [ChartedSpace (ComplexModel n₀) M₀] [IsComplexManifold n₀ M₀]
  [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n₀) Y₀] [IsComplexManifold n₀ Y₀]
  [TopologicalSpace M₁] [ChartedSpace (ComplexModel n₁) M₁] [IsComplexManifold n₁ M₁]
  [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n₁) Y₁] [IsComplexManifold n₁ Y₁]
  {C₀ W₀ : Set M₀} {C₁ W₁ : Set M₁} {π₀ : Y₀ → M₀} {π₁ : Y₁ → M₁}

/-- The SAME original composite projection has a standard invertible WHOLE
pulled ideal, derived from pair geometry without an ideal certificate. -/
theorem composite_projection_ideal_moduleInvertible
    (hπ₀ : IsBlowupAlong n₀ C₀ π₀)
    (hW₀ : IsComplexAnalyticSubset (n := n₀) W₀)
    (hW₁ : IsComplexAnalyticSubset (n := n₁) W₁)
    (e : ofClosedAnalytic W₀ hW₀ ≅ ofClosedAnalytic W₁ hW₁)
    (hC₀W₀ : C₀ ⊆ W₀) (hC₁W₁ : C₁ ⊆ W₁)
    (hdense₀ : W₀ ⊆ closure (W₀ \ C₀))
    (hcentres : ∀ x : W₀, x.val ∈ C₀ ↔ (e.hom.hom.left.base x).val ∈ C₁)
    (z : strictTransform n₀ π₀ W₀) :
    Module.Invertible
      ((actualSubspaceSheaf (n := n₀) (strictTransform n₀ π₀ W₀)).presheaf.stalk z).carrier
      (Ideal.map (((strictTransformMorphism hπ₀ hW₀) ≫ e.hom).hom.left.stalkMap z).hom
        (Ideal.map ((actualSubspaceInclusion (n := n₁) W₁).stalkMap
            (((strictTransformMorphism hπ₀ hW₀) ≫ e.hom).hom.left.base z)).hom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := n₁) C₁)
            (((strictTransformMorphism hπ₀ hW₀) ≫ e.hom).hom.left.base z).val))) := by
  let p₀ := strictTransformProjection hπ₀ hW₀.isClosed
  let f : actualSubspaceLocallyRingedSpace (n := n₀) W₀ ⟶
      actualSubspaceLocallyRingedSpace (n := n₁) W₁ := e.hom.hom.left
  have heq : Ideal.map ((p₀ ≫ f).stalkMap z).hom
        (Ideal.map ((actualSubspaceInclusion (n := n₁) W₁).stalkMap ((p₀ ≫ f).base z)).hom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := n₁) C₁) ((p₀ ≫ f).base z).val)) =
      Ideal.map (p₀.stalkMap z).hom
        (Ideal.map ((actualSubspaceInclusion (n := n₀) W₀).stalkMap (p₀.base z)).hom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := n₀) C₀) (p₀.base z).val)) := by
    rw [ideal_map_stalk_comp]
    exact congrArg (Ideal.map (p₀.stalkMap z).hom)
      (map_centreIdeal_eq_of_iso hW₀ hW₁ e hC₀W₀ hC₁W₁ hcentres (p₀.base z))
  exact (congrArg (fun I : Ideal
      ((actualSubspaceSheaf (n := n₀) (strictTransform n₀ π₀ W₀)).presheaf.stalk z).carrier =>
      Module.Invertible _ I) heq).mpr
    (projection_pulled_ideal_moduleInvertible hπ₀ hW₀.isClosed hdense₀ z)

/-- Two given embedded blowup models of original isomorphic CONTAINED pairs
have a UNIQUE full ORIGINAL comparison iso over the given original e. -/
theorem exists_unique_strictTransform_iso
    (hπ₀ : IsBlowupAlong n₀ C₀ π₀) (hπ₁ : IsBlowupAlong n₁ C₁ π₁)
    (hW₀ : IsComplexAnalyticSubset (n := n₀) W₀)
    (hW₁ : IsComplexAnalyticSubset (n := n₁) W₁)
    (e : ofClosedAnalytic W₀ hW₀ ≅ ofClosedAnalytic W₁ hW₁)
    (hC₀W₀ : C₀ ⊆ W₀) (hC₁W₁ : C₁ ⊆ W₁)
    (hdense₀ : W₀ ⊆ closure (W₀ \ C₀)) (hdense₁ : W₁ ⊆ closure (W₁ \ C₁))
    (hcentres : ∀ x : W₀, x.val ∈ C₀ ↔ (e.hom.hom.left.base x).val ∈ C₁) :
    ∃! E : ofClosedAnalytic (strictTransform n₀ π₀ W₀)
          (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
            hπ₀ hW₀) ≅
        ofClosedAnalytic (strictTransform n₁ π₁ W₁)
          (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
            hπ₁ hW₁),
      E.hom ≫ strictTransformMorphism hπ₁ hW₁ =
        strictTransformMorphism hπ₀ hW₀ ≫ e.hom := by
  let A₀ := ofClosedAnalytic (strictTransform n₀ π₀ W₀)
    (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong hπ₀ hW₀)
  let A₁ := ofClosedAnalytic (strictTransform n₁ π₁ W₁)
    (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong hπ₁ hW₁)
  let p₀ : A₀ ⟶ ofClosedAnalytic W₀ hW₀ := strictTransformMorphism hπ₀ hW₀
  let p₁ : A₁ ⟶ ofClosedAnalytic W₁ hW₁ := strictTransformMorphism hπ₁ hW₁
  have hcentresi : ∀ x : W₁, x.val ∈ C₁ ↔ (e.inv.hom.left.base x).val ∈ C₀ := by
    intro x
    have hp : e.hom.hom.left.base (e.inv.hom.left.base x) = x :=
      congrArg (fun H => H.base x) (SourceReducedComplexSpace.isoLeft e).inv_hom_id
    simpa only [hp] using (hcentres (e.inv.hom.left.base x)).symm
  obtain ⟨L, hL, hLu⟩ := exists_unique_source_factorization_of_module_invertible hπ₁ hW₁
    A₀ (p₀ ≫ e.hom)
      (composite_projection_ideal_moduleInvertible hπ₀ hW₀ hW₁ e hC₀W₀ hC₁W₁ hdense₀ hcentres)
  obtain ⟨R, hR, _⟩ := exists_unique_source_factorization_of_module_invertible hπ₀ hW₀
    A₁ (p₁ ≫ e.inv)
      (composite_projection_ideal_moduleInvertible hπ₁ hW₁ hW₀ e.symm hC₁W₁ hC₀W₀ hdense₁ hcentresi)
  obtain ⟨Q₀, _, hQ₀⟩ := exists_unique_source_factorization_of_module_invertible hπ₀ hW₀
    A₀ p₀ (projection_pulled_ideal_moduleInvertible hπ₀ hW₀.isClosed hdense₀)
  obtain ⟨Q₁, _, hQ₁⟩ := exists_unique_source_factorization_of_module_invertible hπ₁ hW₁
    A₁ p₁ (projection_pulled_ideal_moduleInvertible hπ₁ hW₁.isClosed hdense₁)
  have hLR : L ≫ R = 𝟙 A₀ := by
    apply (hQ₀ (L ≫ R) ?_).trans (hQ₀ (𝟙 A₀) (Category.id_comp p₀)).symm
    calc
      (L ≫ R) ≫ p₀ = L ≫ (R ≫ p₀) := Category.assoc _ _ _
      _ = L ≫ (p₁ ≫ e.inv) := congrArg (fun t => L ≫ t) hR
      _ = (L ≫ p₁) ≫ e.inv := (Category.assoc _ _ _).symm
      _ = (p₀ ≫ e.hom) ≫ e.inv := congrArg (fun t => t ≫ e.inv) hL
      _ = p₀ := by rw [Category.assoc, e.hom_inv_id, Category.comp_id]
  have hRL : R ≫ L = 𝟙 A₁ := by
    apply (hQ₁ (R ≫ L) ?_).trans (hQ₁ (𝟙 A₁) (Category.id_comp p₁)).symm
    calc
      (R ≫ L) ≫ p₁ = R ≫ (L ≫ p₁) := Category.assoc _ _ _
      _ = R ≫ (p₀ ≫ e.hom) := congrArg (fun t => R ≫ t) hL
      _ = (R ≫ p₀) ≫ e.hom := (Category.assoc _ _ _).symm
      _ = (p₁ ≫ e.inv) ≫ e.hom := congrArg (fun t => t ≫ e.hom) hR
      _ = p₁ := by rw [Category.assoc, e.inv_hom_id, Category.comp_id]
  let E : A₀ ≅ A₁ := ⟨L, R, hLR, hRL⟩
  refine ⟨E, hL, ?_⟩
  intro E' hE'
  apply Iso.ext
  exact hLu E'.hom hE'

end

end Hironaka.Analytic.Unibranch.EmbeddedBlowupComparison
