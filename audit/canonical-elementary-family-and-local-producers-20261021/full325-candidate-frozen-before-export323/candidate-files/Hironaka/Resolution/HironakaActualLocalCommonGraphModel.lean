/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualAnalyticSubspacePresentationIndependence
import Hironaka.Resolution.HironakaActualAnalyticSubspaceOpenRestriction
import Hironaka.Resolution.HironakaReducedComplexAnalyticSpaces
import Hironaka.Resolution.HironakaActualHolomorphicGraphIdeal

/-!
# A genuine common graph model from actual original local maps

The local representatives are holomorphic only on actual original opens,
and inverse identities are used only on original subsets. Wide graph models
and genuine containing-open quotient-model isomorphisms give a common model
without requiring reciprocal full-ambient mapping or a supplied LRS iso.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualLocalCommonGraphModel
noncomputable section
open Hironaka.HolomorphicIdealSheaves
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspacePresentationIndependence HironakaActualAnalyticSubspaceOpenRestriction
  HironakaReducedComplexAnalyticSpaces HironakaRelativeNormalIdeal HironakaActualCentreJointJets

/-- A genuine open containing ALL original subset points gives an actual whole quotient-model isomorphism. -/
def containingOpenSubspaceIso {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (C : Set M) (O : Opens M) (hC : C ⊆ O) :
    actualSubspaceLocallyRingedSpace (n := n) ((Subtype.val : O → M) ⁻¹' C) ≅
      actualSubspaceLocallyRingedSpace (n := n) C := by
  let j := actualOpenSubspaceMap (n := n) C O
  have hsurj : Function.Surjective j.base := fun c =>
    ⟨⟨⟨c.val,hC c.property⟩,c.property⟩,rfl⟩
  let : Epi j.base := by
    rw [TopCat.epi_iff_surjective]
    exact hsurj
  let : IsIso j := LocallyRingedSpace.IsOpenImmersion.to_iso j
  exact asIso j

private def openInside {n : ℕ} (A B : Opens (ComplexModel n)) : Opens A :=
  ⟨(Subtype.val : A → ComplexModel n) ⁻¹' B,B.isOpen.preimage continuous_subtype_val⟩

private def coordinateOpenDiffeomorph {n : ℕ} (A B : Opens (ComplexModel n)) (hBA : B ≤ A) :
    B ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openInside A B where
  toFun b := ⟨⟨b.val,hBA b.property⟩,b.property⟩
  invFun a := ⟨a.val.val,a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (openInside A B) _).mp
    apply (ContMDiff.subtypeVal_comp_iff A _).mp
    change ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (Subtype.val : B → ComplexModel n)
    exact contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff B _).mp
    change ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (fun a : openInside A B => a.val.val)
    exact contMDiff_subtype_val.comp contMDiff_subtype_val

/-- Genuine same-ambient coordinate-open comparison, with an actual subset-containment proof only. -/
def coordinateOpenSubspaceIso {n : ℕ} (A B : Opens (ComplexModel n)) (hBA : B ≤ A)
    (C : Set A) (hC : ∀ c ∈ C,c.val ∈ B) :
    actualSubspaceLocallyRingedSpace (n := n)
      ((fun b : B => (⟨b.val,hBA b.property⟩ : A)) ⁻¹' C) ≅
      actualSubspaceLocallyRingedSpace (n := n) C := by
  let e := coordinateOpenDiffeomorph A B hBA
  let D := (Subtype.val : openInside A B → A) ⁻¹' C
  let E := actualSubspaceBiholomorphicIso e
    ((fun b : B => (⟨b.val,hBA b.property⟩ : A)) ⁻¹' C) D (fun _ => Iff.rfl)
  exact E.trans (containingOpenSubspaceIso C (openInside A B) hC)

/-- The containing-open isomorphism retains the genuine complex structural map. -/
theorem containingOpenSubspaceIso_hom_point {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (C : Set M) (O : Opens M) (hC : C ⊆ O) :
    (containingOpenSubspaceIso C O hC).hom ≫ subspacePointMap (n := n) C =
      subspacePointMap (n := n) ((Subtype.val : O → M) ⁻¹' C) :=
  actualSubspaceMap_point contMDiff_subtype_val (fun _ hy => hy)

/-- Same-ambient coordinate-open comparison preserves the actual complex structure. -/
theorem coordinateOpenSubspaceIso_hom_point {n : ℕ} (A B : Opens (ComplexModel n)) (hBA : B ≤ A)
    (C : Set A) (hC : ∀ c ∈ C,c.val ∈ B) :
    (coordinateOpenSubspaceIso A B hBA C hC).hom ≫ subspacePointMap (n := n) C =
      subspacePointMap (n := n) ((fun b : B => (⟨b.val,hBA b.property⟩ : A)) ⁻¹' C) := by
  let e := coordinateOpenDiffeomorph A B hBA
  let D := (Subtype.val : openInside A B → A) ⁻¹' C
  change (actualSubspaceBiholomorphicIso e _ D (fun _ => Iff.rfl)).hom ≫
    (containingOpenSubspaceIso C (openInside A B) hC).hom ≫ subspacePointMap (n := n) C = _
  rw [containingOpenSubspaceIso_hom_point]
  exact actualSubspaceMap_point e.contMDiff (fun _ hy => hy)

private theorem iso_inv_point {X Y : LocallyRingedSpace} (e : X ≅ Y)
    (a : X ⟶ complexPoint) (b : Y ⟶ complexPoint) (h : e.hom ≫ b = a) : e.inv ≫ a = b := by
  rw [← h,← Category.assoc,e.inv_hom_id,Category.id_comp]

/-- A wide genuine coordinate open restricting only the first block. -/
def firstWideDomain {n m : ℕ} (U : Opens (ComplexModel n)) : Opens (ComplexModel (n+m)) :=
  ⟨(tangentProjection n m) ⁻¹' U,U.isOpen.preimage (tangentProjection n m).continuous⟩

/-- A wide genuine coordinate open restricting only the last block. -/
def secondWideDomain {n m : ℕ} (V : Opens (ComplexModel m)) : Opens (ComplexModel (n+m)) :=
  ⟨(actualJointNormalProjection n m) ⁻¹' V,V.isOpen.preimage (actualJointNormalProjection n m).continuous⟩

/-- The actual common original coordinate open. -/
def commonDomain {n m : ℕ} (U : Opens (ComplexModel n)) (V : Opens (ComplexModel m)) :
    Opens (ComplexModel (n+m)) := firstWideDomain U ⊓ secondWideDomain V

/-- The actual first graph subset, with no ideal or isomorphism certificate in its definition. -/
def firstGraphSubset {n m : ℕ} (U : Opens (ComplexModel n))
    (f : ComplexModel n → ComplexModel m) (W : Set (ComplexModel n)) : Set (firstWideDomain (m := m) U) :=
  {z | tangentProjection n m z.val ∈ W ∧ actualJointNormalProjection n m z.val = f (tangentProjection n m z.val)}

/-- The actual reverse graph subset in the SAME original block order. -/
def secondGraphSubset {n m : ℕ} (V : Opens (ComplexModel m))
    (g : ComplexModel m → ComplexModel n) (D : Set (ComplexModel m)) : Set (secondWideDomain (n := n) V) :=
  {z | actualJointNormalProjection n m z.val ∈ D ∧ tangentProjection n m z.val = g (actualJointNormalProjection n m z.val)}

private theorem block_decomposition {n m : ℕ} (z : ComplexModel (n+m)) :
    tangentInclusion n m (tangentProjection n m z) +
      actualJointNormalInclusion n m (actualJointNormalProjection n m z) = z := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

private def firstGraphSection {n m : ℕ} (U : Opens (ComplexModel n))
    (f : ComplexModel n → ComplexModel m) : U → firstWideDomain (m := m) U :=
  fun x => ⟨tangentInclusion n m x.val + actualJointNormalInclusion n m (f x.val),by
    change tangentProjection n m (tangentInclusion n m x.val + actualJointNormalInclusion n m (f x.val)) ∈ U
    simp [tangentProjection_tangentInclusion]⟩

private def firstGraphProjection {n m : ℕ} (U : Opens (ComplexModel n)) :
    firstWideDomain (m := m) U → U := fun z => ⟨tangentProjection n m z.val,z.property⟩

private def secondGraphSection {n m : ℕ} (V : Opens (ComplexModel m))
    (g : ComplexModel m → ComplexModel n) : V → secondWideDomain (n := n) V :=
  fun y => ⟨tangentInclusion n m (g y.val) + actualJointNormalInclusion n m y.val,by
    change actualJointNormalProjection n m (tangentInclusion n m (g y.val) + actualJointNormalInclusion n m y.val) ∈ V
    simp⟩

private def secondGraphProjection {n m : ℕ} (V : Opens (ComplexModel m)) :
    secondWideDomain (n := n) V → V := fun z => ⟨actualJointNormalProjection n m z.val,z.property⟩

private theorem local_vector_contMDiff {n m : ℕ} (U : Opens (ComplexModel n))
    (f : ComplexModel n → ComplexModel m) (hf : ContDiffOn ℂ ∞ f U) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ (fun x : U => f x.val) := by
  intro x
  exact contMDiffAt_subtype_iff.mpr ((hf.contDiffAt (U.isOpen.mem_nhds x.property)).contMDiffAt)

private theorem firstGraphSection_contMDiff {n m : ℕ} (U : Opens (ComplexModel n))
    (f : ComplexModel n → ComplexModel m) (hf : ContDiffOn ℂ ∞ f U) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (n+m)) ∞ (firstGraphSection U f) := by
  apply (ContMDiff.subtypeVal_comp_iff (firstWideDomain U) _).mp
  exact ((tangentInclusion n m).contMDiff.comp contMDiff_subtype_val).add
    ((actualJointNormalInclusion n m).contMDiff.comp (local_vector_contMDiff U f hf))

private theorem firstGraphProjection_contMDiff {n m : ℕ} (U : Opens (ComplexModel n)) :
    ContMDiff 𝓘(ℂ,ComplexModel (n+m)) 𝓘(ℂ,ComplexModel n) ∞ (firstGraphProjection (m := m) U) := by
  apply (ContMDiff.subtypeVal_comp_iff U _).mp
  exact (tangentProjection n m).contMDiff.comp contMDiff_subtype_val

private theorem secondGraphSection_contMDiff {n m : ℕ} (V : Opens (ComplexModel m))
    (g : ComplexModel m → ComplexModel n) (hg : ContDiffOn ℂ ∞ g V) :
    ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel (n+m)) ∞ (secondGraphSection V g) := by
  apply (ContMDiff.subtypeVal_comp_iff (secondWideDomain V) _).mp
  exact ((tangentInclusion n m).contMDiff.comp (local_vector_contMDiff V g hg)).add
    ((actualJointNormalInclusion n m).contMDiff.comp contMDiff_subtype_val)

private theorem secondGraphProjection_contMDiff {n m : ℕ} (V : Opens (ComplexModel m)) :
    ContMDiff 𝓘(ℂ,ComplexModel (n+m)) 𝓘(ℂ,ComplexModel m) ∞ (secondGraphProjection (n := n) V) := by
  apply (ContMDiff.subtypeVal_comp_iff V _).mp
  exact (actualJointNormalProjection n m).contMDiff.comp contMDiff_subtype_val

private theorem firstGraphSection_maps {n m : ℕ} (U : Opens (ComplexModel n))
    (f : ComplexModel n → ComplexModel m) (W : Set (ComplexModel n)) :
    ∀ x ∈ (Subtype.val : U → ComplexModel n) ⁻¹' W,firstGraphSection U f x ∈ firstGraphSubset U f W := by
  intro x hx
  constructor
  · simpa [firstGraphSection,tangentProjection_tangentInclusion] using hx
  · simp [firstGraphSection,tangentProjection_tangentInclusion]

private theorem secondGraphSection_maps {n m : ℕ} (V : Opens (ComplexModel m))
    (g : ComplexModel m → ComplexModel n) (D : Set (ComplexModel m)) :
    ∀ y ∈ (Subtype.val : V → ComplexModel m) ⁻¹' D,secondGraphSection V g y ∈ secondGraphSubset V g D := by
  intro y hy
  constructor
  · simpa [secondGraphSection] using hy
  · simp [secondGraphSection,tangentProjection_tangentInclusion]

/-- Actual original graph parametrization/projection, inverse ONLY on the original subsets, give a genuine wide-model iso. -/
def firstGraphModelIso {n m : ℕ} (U : Opens (ComplexModel n))
    (f : ComplexModel n → ComplexModel m) (hf : ContDiffOn ℂ ∞ f U) (W : Set (ComplexModel n)) :
    actualSubspaceLocallyRingedSpace (n := n) ((Subtype.val : U → ComplexModel n) ⁻¹' W) ≅
      actualSubspaceLocallyRingedSpace (n := n+m) (firstGraphSubset U f W) :=
  actualSubspaceMutualRestrictionIso (firstGraphSection_contMDiff U f hf) (firstGraphProjection_contMDiff U)
    (firstGraphSection_maps U f W) (fun _ hz => hz.1)
    (fun x _ => Subtype.ext (by simp [firstGraphSection,firstGraphProjection,tangentProjection_tangentInclusion]))
    (fun z hz => Subtype.ext (by
      change tangentInclusion n m (tangentProjection n m z.val) +
        actualJointNormalInclusion n m (f (tangentProjection n m z.val)) = z.val
      rw [← hz.2]
      exact block_decomposition z.val))

/-- Actual reverse graph and last projection, in the SAME original block order, give the genuine second model iso. -/
def secondGraphModelIso {n m : ℕ} (V : Opens (ComplexModel m))
    (g : ComplexModel m → ComplexModel n) (hg : ContDiffOn ℂ ∞ g V) (D : Set (ComplexModel m)) :
    actualSubspaceLocallyRingedSpace (n := m) ((Subtype.val : V → ComplexModel m) ⁻¹' D) ≅
      actualSubspaceLocallyRingedSpace (n := n+m) (secondGraphSubset V g D) :=
  actualSubspaceMutualRestrictionIso (secondGraphSection_contMDiff V g hg) (secondGraphProjection_contMDiff V)
    (secondGraphSection_maps V g D) (fun _ hz => hz.1)
    (fun y _ => Subtype.ext (by simp [secondGraphSection,secondGraphProjection]))
    (fun z hz => Subtype.ext (by
      change tangentInclusion n m (g (actualJointNormalProjection n m z.val)) +
        actualJointNormalInclusion n m (actualJointNormalProjection n m z.val) = z.val
      rw [← hz.2]
      exact block_decomposition z.val))

/-- The first genuine graph-model iso preserves the actual original complex structure. -/
theorem firstGraphModelIso_hom_point {n m : ℕ} (U : Opens (ComplexModel n))
    (f : ComplexModel n → ComplexModel m) (hf : ContDiffOn ℂ ∞ f U) (W : Set (ComplexModel n)) :
    (firstGraphModelIso U f hf W).hom ≫ subspacePointMap (n := n+m) (firstGraphSubset U f W) =
      subspacePointMap (n := n) ((Subtype.val : U → ComplexModel n) ⁻¹' W) :=
  actualSubspaceMap_point (firstGraphSection_contMDiff U f hf) (firstGraphSection_maps U f W)

/-- The second genuine graph-model iso preserves the SAME actual original complex structure. -/
theorem secondGraphModelIso_hom_point {n m : ℕ} (V : Opens (ComplexModel m))
    (g : ComplexModel m → ComplexModel n) (hg : ContDiffOn ℂ ∞ g V) (D : Set (ComplexModel m)) :
    (secondGraphModelIso V g hg D).hom ≫ subspacePointMap (n := n+m) (secondGraphSubset V g D) =
      subspacePointMap (n := m) ((Subtype.val : V → ComplexModel m) ⁻¹' D) :=
  actualSubspaceMap_point (secondGraphSection_contMDiff V g hg) (secondGraphSection_maps V g D)

private def subspaceSetEqIso {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {C D : Set M} (h : C = D) :
    actualSubspaceLocallyRingedSpace (n := n) C ≅ actualSubspaceLocallyRingedSpace (n := n) D :=
  eqToIso (congrArg (actualSubspaceLocallyRingedSpace (n := n)) h)

private theorem subspaceSetEqIso_point {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {C D : Set M} (h : C = D) :
    (subspaceSetEqIso h).hom ≫ subspacePointMap (n := n) D = subspacePointMap (n := n) C := by
  subst D
  exact Category.id_comp _

/-- The SAME actual common graph, in the SAME original block coordinates. -/
def commonGraphSubset {n m : ℕ} (U : Opens (ComplexModel n)) (V : Opens (ComplexModel m))
    (f : ComplexModel n → ComplexModel m) (W : Set (ComplexModel n)) : Set (commonDomain U V) :=
  {z | tangentProjection n m z.val ∈ W ∧ actualJointNormalProjection n m z.val = f (tangentProjection n m z.val)}

/-- Ordinary local holomorphic maps inverse ONLY on actual subsets internally produce genuine common whole graph model isos. -/
theorem actualCommonGraphModelIsos {n m : ℕ}
    (U : Opens (ComplexModel n)) (V : Opens (ComplexModel m))
    (W : Set (ComplexModel n)) (D : Set (ComplexModel m))
    (hW : W ⊆ U) (hD : D ⊆ V)
    (f : ComplexModel n → ComplexModel m) (g : ComplexModel m → ComplexModel n)
    (hf : ContDiffOn ℂ ∞ f U) (hg : ContDiffOn ℂ ∞ g V)
    (hFD : ∀ x ∈ W,f x ∈ D) (hGW : ∀ y ∈ D,g y ∈ W)
    (hgf : ∀ x ∈ W,g (f x) = x) (hfg : ∀ y ∈ D,f (g y) = y) :
    ∃ (eW : actualSubspaceLocallyRingedSpace (n := n) ((Subtype.val : U → ComplexModel n) ⁻¹' W) ≅
        actualSubspaceLocallyRingedSpace (n := n+m) (commonGraphSubset U V f W))
      (eD : actualSubspaceLocallyRingedSpace (n := m) ((Subtype.val : V → ComplexModel m) ⁻¹' D) ≅
        actualSubspaceLocallyRingedSpace (n := n+m) (commonGraphSubset U V f W)),
      eW.hom ≫ subspacePointMap (n := n+m) (commonGraphSubset U V f W) =
        subspacePointMap (n := n) ((Subtype.val : U → ComplexModel n) ⁻¹' W) ∧
      eD.hom ≫ subspacePointMap (n := n+m) (commonGraphSubset U V f W) =
        subspacePointMap (n := m) ((Subtype.val : V → ComplexModel m) ⁻¹' D) := by
  let P := commonDomain U V
  let A := firstWideDomain (m := m) U
  let B := secondWideDomain (n := n) V
  let C₁ := firstGraphSubset U f W
  let C₂ := secondGraphSubset V g D
  let H := commonGraphSubset U V f W
  have hC₁ : ∀ z ∈ C₁,z.val ∈ P := by
    intro z hz
    refine ⟨z.property,?_⟩
    change actualJointNormalProjection n m z.val ∈ V
    rw [hz.2]
    exact hD (hFD _ hz.1)
  have hC₂ : ∀ z ∈ C₂,z.val ∈ P := by
    intro z hz
    refine ⟨?_,z.property⟩
    change tangentProjection n m z.val ∈ U
    rw [hz.2]
    exact hW (hGW _ hz.1)
  let R₁ := coordinateOpenSubspaceIso A P inf_le_left C₁ hC₁
  let R₂ := coordinateOpenSubspaceIso B P inf_le_right C₂ hC₂
  let C₂' := (fun z : P => (⟨z.val,z.property.2⟩ : B)) ⁻¹' C₂
  have heq : C₂' = H := by
    ext z
    change (actualJointNormalProjection n m z.val ∈ D ∧
      tangentProjection n m z.val = g (actualJointNormalProjection n m z.val)) ↔
      tangentProjection n m z.val ∈ W ∧
        actualJointNormalProjection n m z.val = f (tangentProjection n m z.val)
    constructor
    · rintro ⟨hy,he⟩
      refine ⟨?_,?_⟩
      · rw [he]
        exact hGW _ hy
      · rw [he,hfg _ hy]
    · rintro ⟨hx,he⟩
      refine ⟨?_,?_⟩
      · rw [he]
        exact hFD _ hx
      · rw [he,hgf _ hx]
  let T := subspaceSetEqIso (n := n+m) heq.symm
  let R₂' := T.trans R₂
  have hR₁ : R₁.hom ≫ subspacePointMap (n := n+m) C₁ = subspacePointMap (n := n+m) H :=
    coordinateOpenSubspaceIso_hom_point A P inf_le_left C₁ hC₁
  have hR₂ : R₂.hom ≫ subspacePointMap (n := n+m) C₂ = subspacePointMap (n := n+m) C₂' :=
    coordinateOpenSubspaceIso_hom_point B P inf_le_right C₂ hC₂
  have hR₂' : R₂'.hom ≫ subspacePointMap (n := n+m) C₂ = subspacePointMap (n := n+m) H := by
    change (T.hom ≫ R₂.hom) ≫ subspacePointMap (n := n+m) C₂ = _
    rw [Category.assoc,hR₂]
    exact subspaceSetEqIso_point (n := n+m) heq.symm
  let E₁ := (firstGraphModelIso U f hf W).trans R₁.symm
  let E₂ := (secondGraphModelIso V g hg D).trans R₂'.symm
  refine ⟨E₁,E₂,?_,?_⟩
  · change ((firstGraphModelIso U f hf W).hom ≫ R₁.inv) ≫ subspacePointMap (n := n+m) H = _
    rw [Category.assoc,iso_inv_point R₁ _ _ hR₁]
    exact firstGraphModelIso_hom_point U f hf W
  · change ((secondGraphModelIso V g hg D).hom ≫ R₂'.inv) ≫ subspacePointMap (n := n+m) H = _
    rw [Category.assoc,iso_inv_point R₂' _ _ hR₂']
    exact secondGraphModelIso_hom_point V g hg D

/-- Genuine original analytic input internally yields an ACTUAL common analytic-category object, without a graph-atlas certificate. -/
theorem hasAnalyticCharts_commonGraphModel {n m : ℕ}
    (U : Opens (ComplexModel n)) (V : Opens (ComplexModel m))
    (W : Set (ComplexModel n)) (D : Set (ComplexModel m))
    (hW : W ⊆ U) (hD : D ⊆ V)
    (f : ComplexModel n → ComplexModel m) (g : ComplexModel m → ComplexModel n)
    (hf : ContDiffOn ℂ ∞ f U) (hg : ContDiffOn ℂ ∞ g V)
    (hFD : ∀ x ∈ W,f x ∈ D) (hGW : ∀ y ∈ D,g y ∈ W)
    (hgf : ∀ x ∈ W,g (f x) = x) (hfg : ∀ y ∈ D,f (g y) = y)
    (hWa : IsComplexAnalyticSubset (n := n) ((Subtype.val : U → ComplexModel n) ⁻¹' W)) :
    hasAnalyticCharts (modelOver (commonDomain U V) (commonGraphSubset U V f W)) := by
  obtain ⟨eW,_eD,hpoint,_⟩ := actualCommonGraphModelIsos U V W D hW hD f g hf hg hFD hGW hgf hfg
  refine ⟨?_,?_,?_⟩
  · change T2Space (commonGraphSubset U V f W)
    infer_instance
  · change SecondCountableTopology (commonGraphSubset U V f W)
    infer_instance
  intro x
  refine ⟨n,U,(Subtype.val : U → ComplexModel n) ⁻¹' W,hWa,eW.hom,inferInstance,hpoint,?_⟩
  refine ⟨eW.inv.base x,?_⟩
  have he := congrArg (fun a => a.base x) eW.inv_hom_id
  exact he

end
end Hironaka.HironakaActualLocalCommonGraphModel
