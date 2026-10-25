import DeJongAlterations.StableModificationBridge.StableOpenNormalizedSpecialCount
import DeJongAlterations.Geometry.CanonicalComponentGenusMinimal

/-! Exact original pole/mark support comparison and genuine native marked numerical positivity.
The finite sets enumerate intrinsic original loci; no cardinality or degree bound is supplied.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
noncomputable section
universe u

namespace DeJongAlterations.StableModificationBridge.StableOpenMarkedSupportCount

open StableModification
open CurvesField.Genus Omega.ComponentNormalization Omega.ComponentDegree Cohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original special locus on the SAME normalization is exactly its original pole-mark union. -/
theorem preimage_specialPoints_eq_union {X C S : Scheme.{u}}
    (β : X ⟶ C) (g : C ⟶ S) [DeJong.IsNodalCurve (β ≫ g)]
    (D' : X.IdealSheafData) {K : Type u} [Field K] [IsAlgClosed K]
    (a : Spec (.of K) ⟶ S)
    [IsAffineHom (pullback.diagonal (terminal.from (pullback (C := Scheme.{u}) (β ≫ g) a)))]
    (v : pullback (C := Scheme.{u}) (β ≫ g) a)
    (E M : Finset (componentNormalization (β ≫ g) a v))
    (hE : ∀ y, y ∈ E ↔ componentMap (β ≫ g) a v y ∉ (β ≫ g).smoothLocus)
    (hM : ∀ y, y ∈ M ↔ componentMap (β ≫ g) a v y ∈ (D'.support : Set X)) :
    normalizationPointsMap ({v} : Set (pullback (C := Scheme.{u}) (β ≫ g) a)) ⁻¹'
      Global.specialPoints β g D' a = (E : Set _) ∪ (M : Set _) := by
  ext y
  have hsm : componentMap (β ≫ g) a v y ∈ (β ≫ g).smoothLocus ↔
      normalizationPointsMap ({v} : Set (pullback (C := Scheme.{u}) (β ≫ g) a)) y ∈
        (pullback.snd (β ≫ g) a).smoothLocus := by
    rw [← Omega.preimage_smoothLocus_eq_of_isNodalCurve (β ≫ g) K a]
    rfl
  change (componentMap (β ≫ g) a v y ∈ (D'.support : Set X) ∨
      ¬ DeJong.IsSmoothAt (pullback.snd (β ≫ g) a)
        (normalizationPointsMap ({v} : Set (pullback (C := Scheme.{u}) (β ≫ g) a)) y)) ↔ y ∈ E ∨ y ∈ M
  rw [hE, hM, DeJong.isSmoothAt_iff_mem_smoothLocus, ← hsm]
  tauto

/-- Original numeric stability and corrected contraction internally give the actual genus-zero count. -/
theorem three_le_card_add_of_genus_zero {X C S : Scheme.{u}}
    (β : X ⟶ C) (g : C ⟶ S) [DeJong.IsNodalCurve (β ≫ g)] [IsProper (β ≫ g)]
    (D' : X.IdealSheafData) {K : Type u} [Field K] [IsAlgClosed K]
    (a : Spec (.of K) ⟶ S)
    [CompactSpace (pullback (C := Scheme.{u}) (β ≫ g) a)]
    [IsAffineHom (pullback.diagonal (terminal.from (pullback (C := Scheme.{u}) (β ≫ g) a)))]
    (hnum : Global.NumericallyStableFibre β g D' a) (hno : Global.NoContractedClopen β g a)
    (v : pullback (C := Scheme.{u}) (β ≫ g) a)
    (hv : v ∈ genericPoints (pullback (C := Scheme.{u}) (β ≫ g) a))
    (hcon : (Curves.pullbackCompMap β g a '' closure {v}).Subsingleton)
    (hg : componentGenus (structureCoeff (pullback.snd (β ≫ g) a)) v = 0)
    (E M : Finset (componentNormalization (β ≫ g) a v))
    (hE : ∀ y, y ∈ E ↔ componentMap (β ≫ g) a v y ∉ (β ≫ g).smoothLocus)
    (hM : ∀ y, y ∈ M ↔ componentMap (β ≫ g) a v y ∈ (D'.support : Set X)) :
    3 ≤ E.card + M.card := by
  classical
  have h3 := StableOpenNormalizedSpecialCount.three_le_encard_preimage_specialPoints
    β g D' a hnum hno v hv hcon hg
  rw [preimage_specialPoints_eq_union β g D' a v E M hE hM, ← Finset.coe_union,
    Set.encard_coe_eq_coe_finsetCard] at h3
  have h3' : 3 ≤ (E ∪ M).card := by exact_mod_cast h3
  exact h3'.trans (Finset.card_union_le E M)

/-- Actual projective nodal geometry makes the marked number positive; no positive degree or
marked bundle certificate is assumed, and both finite supports remain the original intrinsic ones. -/
theorem marked_component_number_pos {X C S : Scheme.{u}}
    (β : X ⟶ C) (g : C ⟶ S) [DeJong.IsNodalCurve (β ≫ g)] [IsProper (β ≫ g)]
    (D' : X.IdealSheafData) {K : Type u} [Field K] [IsAlgClosed K]
    (a : Spec (.of K) ⟶ S)
    [CompactSpace (pullback (C := Scheme.{u}) (β ≫ g) a)]
    [IsAffineHom (pullback.diagonal (terminal.from (pullback (C := Scheme.{u}) (β ≫ g) a)))]
    (hnum : Global.NumericallyStableFibre β g D' a) (hno : Global.NoContractedClopen β g a)
    (v : pullback (C := Scheme.{u}) (β ≫ g) a)
    (hv : v ∈ genericPoints (pullback (C := Scheme.{u}) (β ≫ g) a))
    (hcon : (Curves.pullbackCompMap β g a '' closure {v}).Subsingleton)
    (hN : IsProjectiveOver (componentStructure (β ≫ g) a v))
    (E M : Finset (componentNormalization (β ≫ g) a v))
    (hE : ∀ y, y ∈ E ↔ componentMap (β ≫ g) a v y ∉ (β ≫ g).smoothLocus)
    (hM : ∀ y, y ∈ M ↔ componentMap (β ≫ g) a v y ∈ (D'.support : Set X)) :
    0 < 2 * componentGenus (structureCoeff (pullback.snd (β ≫ g) a)) v - 2 + E.card + M.card := by
  have hg := Omega.ComponentDegreeMinimal.componentGenus_nonneg (β ≫ g) a hv hN
  by_cases hg0 : componentGenus (structureCoeff (pullback.snd (β ≫ g) a)) v = 0
  · have hc := three_le_card_add_of_genus_zero β g D' a hnum hno v hv hcon hg0 E M hE hM
    omega
  · obtain ⟨_, _, _, x, hx, hxns, _⟩ :=
      StableOpenSpecialBoundary.contracted_component_has_special_point β g D' a hno
        (closure {v}) hv hcon
    obtain ⟨y, hy⟩ : x ∈ Set.range (normalizationPointsMap
        ({v} : Set (pullback (C := Scheme.{u}) (β ≫ g) a))) := by
      rw [range_normalizationPointsMap]
      exact hx.1
    have hyE : y ∈ E := (hE y).mpr (by
      change pullback.fst (β ≫ g) a (normalizationPointsMap
        ({v} : Set (pullback (C := Scheme.{u}) (β ≫ g) a)) y) ∉ (β ≫ g).smoothLocus
      rw [hy]
      intro hs
      apply hxns
      rw [← Omega.preimage_smoothLocus_eq_of_isNodalCurve (β ≫ g) K a]
      exact hs)
    have hc : 0 < E.card := Finset.card_pos.mpr ⟨y, hyE⟩
    omega

end DeJongAlterations.StableModificationBridge.StableOpenMarkedSupportCount
