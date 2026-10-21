/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualIntrinsicIsoPairedWindows
import Hironaka.Resolution.HironakaActualAnalyticSubspaceLocalFunctions

/-!
# A specified intrinsic isomorphism has an entire common-graph comparison square

Literal original graph coordinates are retained by explicit common-model
isomorphisms. Whole quotient-model faithfulness upgrades the resulting
actual base equality to the entire locally ringed square for the GIVEN iso.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualIntrinsicIsoCommonGraphSquare
noncomputable section
open HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceLocalFunctions HironakaReducedComplexAnalyticSpaces
  HironakaActualLocalCommonGraphModel HironakaActualIntrinsicIsoPairedWindows
  HironakaRelativeNormalIdeal HironakaActualCentreJointJets

private theorem iso_inv_point {X Y : LocallyRingedSpace} (e : X ≅ Y)
    (a : X ⟶ complexPoint) (b : Y ⟶ complexPoint) (h : e.hom ≫ b = a) : e.inv ≫ a = b := by
  rw [← h,← Category.assoc,e.inv_hom_id,Category.id_comp]

private theorem coordinateOpenSubspaceIso_inv_value {n : ℕ}
    (A B : Opens (ComplexModel n)) (hBA : B ≤ A)
    (C : Set A) (hC : ∀ c ∈ C,c.val ∈ B) (x : C) :
    ((coordinateOpenSubspaceIso A B hBA C hC).inv.base x).val.val = x.val.val := by
  let e := coordinateOpenSubspaceIso A B hBA C hC
  have h := congrArg (fun a => (a.base x).val.val) e.inv_hom_id
  exact h

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

private theorem subspaceSetEqIso_inv_value {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {C D : Set M} (h : C = D) (x : D) :
    ((subspaceSetEqIso (n := n) h).inv.base x).val = x.val := by
  subst D
  rfl

/-- Explicit common-model isomorphisms retain literal graph tuples and the genuine complex structure. -/
theorem actualCommonGraphModelIsos_with_coordinates {n m : ℕ}
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
        subspacePointMap (n := m) ((Subtype.val : V → ComplexModel m) ⁻¹' D) ∧
      (∀ x, (eW.hom.base x).val.val = tangentInclusion n m x.val.val +
        actualJointNormalInclusion n m (f x.val.val)) ∧
      (∀ y, (eD.hom.base y).val.val = tangentInclusion n m (g y.val.val) +
        actualJointNormalInclusion n m y.val.val) := by
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
  refine ⟨E₁,E₂,?_,?_,?_,?_⟩
  · change ((firstGraphModelIso U f hf W).hom ≫ R₁.inv) ≫ subspacePointMap (n := n+m) H = _
    rw [Category.assoc,iso_inv_point R₁ _ _ hR₁]
    exact firstGraphModelIso_hom_point U f hf W
  · change ((secondGraphModelIso V g hg D).hom ≫ R₂'.inv) ≫ subspacePointMap (n := n+m) H = _
    rw [Category.assoc,iso_inv_point R₂' _ _ hR₂']
    exact secondGraphModelIso_hom_point V g hg D

  · intro x
    change (R₁.inv.base ((firstGraphModelIso U f hf W).hom.base x)).val.val = _
    exact coordinateOpenSubspaceIso_inv_value A P inf_le_left C₁ hC₁ _
  · intro y
    change (T.inv.base (R₂.inv.base ((secondGraphModelIso V g hg D).hom.base y))).val.val = _
    calc
      _ = (R₂.inv.base ((secondGraphModelIso V g hg D).hom.base y)).val.val :=
        congrArg Subtype.val (subspaceSetEqIso_inv_value (n := n+m) heq.symm _)
      _ = _ := coordinateOpenSubspaceIso_inv_value B P inf_le_right C₂ hC₂ _

/-- The actual original coordinate-window subset, retaining the literal original carrier. -/
def coordinateWindowSubset {n : ℕ} {U : Opens (ComplexModel n)}
    (C : Set U) (A : Opens (ComplexModel n)) : Set A :=
  (Subtype.val : A → ComplexModel n) ⁻¹' (coordinateCarrier C ∩ A)

private theorem coordinateWindow_maps {n : ℕ} {U : Opens (ComplexModel n)}
    (C : Set U) (A : Opens (ComplexModel n)) (hAU : A ≤ U) :
    ∀ x ∈ coordinateWindowSubset C A,(⟨x.val,hAU x.property⟩ : U) ∈ C := by
  rintro x ⟨⟨u,hu,he⟩,_⟩
  have hu' : u = (⟨x.val,hAU x.property⟩ : U) := Subtype.ext he
  exact hu' ▸ hu

/-- A genuine original coordinate-window inclusion is an actual whole quotient-model map. -/
def coordinateWindowInclusion {n : ℕ} {U : Opens (ComplexModel n)}
    (C : Set U) (A : Opens (ComplexModel n)) (hAU : A ≤ U) :
    actualSubspaceLocallyRingedSpace (n := n) (coordinateWindowSubset C A) ⟶
      actualSubspaceLocallyRingedSpace (n := n) C :=
  actualSubspaceMap (contMDiff_inclusion hAU) (coordinateWindow_maps C A hAU)

/-- The true window inclusion preserves the actual complex structural map. -/
theorem coordinateWindowInclusion_point {n : ℕ} {U : Opens (ComplexModel n)}
    (C : Set U) (A : Opens (ComplexModel n)) (hAU : A ≤ U) :
    coordinateWindowInclusion C A hAU ≫ subspacePointMap (n := n) C =
      subspacePointMap (n := n) (coordinateWindowSubset C A) :=
  actualSubspaceMap_point (contMDiff_inclusion hAU) (coordinateWindow_maps C A hAU)

/-- ANY specified intrinsic iso internally produces a WHOLE common-graph comparison square locally. -/
theorem exists_actual_intrinsic_iso_common_graph_square
    {n m : ℕ} {U : Opens (ComplexModel n)} {V : Opens (ComplexModel m)} {C : Set U} {D : Set V}
    (e : actualSubspaceLocallyRingedSpace (n := n) C ≅ actualSubspaceLocallyRingedSpace (n := m) D)
    (he : e.hom ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) C)
    (hC : IsComplexAnalyticSubset (n := n) C) (hD : IsComplexAnalyticSubset (n := m) D) (c : C) :
    ∃ (A : Opens (ComplexModel n)) (B : Opens (ComplexModel m))
      (F : ComplexModel n → ComplexModel m) (hAU : A ≤ U) (hBV : B ≤ V),
      c.val.val ∈ A ∧ (e.hom.base c).val.val ∈ B ∧
      let W := coordinateCarrier C ∩ (A : Set (ComplexModel n))
      ∃ (eW : actualSubspaceLocallyRingedSpace (n := n) (coordinateWindowSubset C A) ≅
          actualSubspaceLocallyRingedSpace (n := n+m) (commonGraphSubset A B F W))
        (eD : actualSubspaceLocallyRingedSpace (n := m) (coordinateWindowSubset D B) ≅
          actualSubspaceLocallyRingedSpace (n := n+m) (commonGraphSubset A B F W)),
        eW.hom ≫ subspacePointMap (n := n+m) (commonGraphSubset A B F W) =
          subspacePointMap (n := n) (coordinateWindowSubset C A) ∧
        eD.hom ≫ subspacePointMap (n := n+m) (commonGraphSubset A B F W) =
          subspacePointMap (n := m) (coordinateWindowSubset D B) ∧
        (eW.hom ≫ eD.inv) ≫ coordinateWindowInclusion D B hBV =
          coordinateWindowInclusion C A hAU ≫ e.hom ∧
        hasAnalyticCharts (modelOver (commonDomain A B) (commonGraphSubset A B F W)) := by
  obtain ⟨A,B,F,G,hAU,hBV,hcA,hdB,hF,hG,hWa,_hTa,hFD,hGW,hGF,hFG,hFval,_hGval⟩ :=
    exists_actual_intrinsic_iso_paired_windows e he hC hD c
  let W := coordinateCarrier C ∩ (A : Set (ComplexModel n))
  let T := coordinateCarrier D ∩ (B : Set (ComplexModel m))
  have hWA : W ⊆ A := inter_subset_right
  have hTB : T ⊆ B := inter_subset_right
  obtain ⟨eW,eD,hw,hd,hwcoords,hdcoords⟩ :=
    actualCommonGraphModelIsos_with_coordinates A B W T hWA hTB F G hF hG hFD hGW hGF hFG
  have ha := hasAnalyticCharts_commonGraphModel A B W T hWA hTB F G hF hG hFD hGW hGF hFG hWa
  refine ⟨A,B,F,hAU,hBV,hcA,hdB,eW,eD,hw,hd,?_,ha⟩
  apply actualSubspaceMap_eq_of_base_eq
  · rw [Category.assoc,coordinateWindowInclusion_point,Category.assoc]
    change eW.hom ≫ (eD.inv ≫ subspacePointMap (n := m)
      ((Subtype.val : B → ComplexModel m) ⁻¹' T)) = _
    exact (congrArg (fun a => eW.hom ≫ a) (iso_inv_point eD _ _ hd)).trans hw
  · rw [Category.assoc,he,coordinateWindowInclusion_point]
  · apply ConcreteCategory.hom_ext
    intro x
    let y := eD.inv.base (eW.hom.base x)
    have hinv := congrArg (fun a => (a.base (eW.hom.base x)).val.val) eD.inv_hom_id
    change (eD.hom.base y).val.val = (eW.hom.base x).val.val at hinv
    rw [hdcoords y,hwcoords x] at hinv
    have hy : y.val.val = F x.val.val := by
      have hn := congrArg (actualJointNormalProjection n m) hinv
      simpa using hn
    have hxF := hFval ((coordinateWindowInclusion C A hAU).base x) x.val.property
    apply Subtype.ext
    apply Subtype.ext
    change y.val.val = (e.hom.base ((coordinateWindowInclusion C A hAU).base x)).val.val
    exact hy.trans hxF

end
end Hironaka.HironakaActualIntrinsicIsoCommonGraphSquare
