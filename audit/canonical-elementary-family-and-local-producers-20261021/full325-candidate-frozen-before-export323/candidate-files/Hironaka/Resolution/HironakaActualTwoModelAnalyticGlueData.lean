/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualAnalyticSubspaceOpenRestriction
import Hironaka.Resolution.HironakaReducedComplexAnalyticSpaces
import Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing

/-!
# Native two-model gluing from original holomorphic overlap maps

Ordinary actual coordinate domains, closed analytic subsets, overlap opens and
holomorphic overlap maps carry no ringed-space transition data. Inverse laws
only on the actual subsets construct genuine quotient-model isomorphisms.
Actual open restriction then constructs native two-model gluing data, retaining
the original complex structural morphisms. Hausdorffness is not inferred.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualTwoModelAnalyticGlueData
noncomputable section
open Hironaka.HolomorphicIdealSheaves
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspacePresentationIndependence
  HironakaActualAnalyticSubspaceOpenRestriction HironakaReducedComplexAnalyticSpaces

/-- Ordinary original analytic overlap data; there are no structure-sheaf maps or isomorphism certificates. -/
structure ActualTwoModelHolomorphicOverlaps where
  dimension : Bool → ℕ
  domain : (i : Bool) → Opens (ComplexModel (dimension i))
  carrier : (i : Bool) → Set (domain i)
  analytic : ∀ i, IsComplexAnalyticSubset (n := dimension i) (carrier i)
  overlap : (i j : Bool) → Opens (domain i)
  transition : (i j : Bool) → overlap i j → overlap j i
  holomorphic : ∀ i j, ContMDiff 𝓘(ℂ,ComplexModel (dimension i))
    𝓘(ℂ,ComplexModel (dimension j)) ∞ (transition i j)
  mapsTo : ∀ i j, i≠j → ∀ x : overlap i j, x.val∈carrier i → (transition i j x).val∈carrier j
  inverse : ∀ i j, i≠j → ∀ x : overlap i j, x.val∈carrier i → transition j i (transition i j x)=x

variable (A : ActualTwoModelHolomorphicOverlaps)

/-- Each actual chart has its already constructed whole quotient sheaf. -/
abbrev actualChartModel (i : Bool) : LocallyRingedSpace :=
  actualSubspaceLocallyRingedSpace (n := A.dimension i) (A.carrier i)

/-- The literal original subset in its genuine overlap open. -/
abbrev actualOverlapCarrier (i j : Bool) : Set (A.overlap i j) :=
  (Subtype.val : A.overlap i j → A.domain i) ⁻¹' A.carrier i

/-- Each actual overlap is constructed from its original vanishing quotient, not a supplied sheaf. -/
abbrev actualOverlapModel (i j : Bool) : LocallyRingedSpace :=
  actualSubspaceLocallyRingedSpace (n := A.dimension i) (actualOverlapCarrier A i j)

/-- The SAME original open inclusion supplies the actual overlap-to-chart morphism. -/
abbrev actualOverlapInclusion (i j : Bool) : actualOverlapModel A i j ⟶ actualChartModel A i :=
  actualOpenSubspaceMap (n := A.dimension i) (A.carrier i) (A.overlap i j)

/-- Inverses only on the actual subsets internally construct whole quotient-model isomorphisms. -/
def actualOverlapIso (i j : Bool) (hij : i≠j) : actualOverlapModel A i j ≅ actualOverlapModel A j i :=
  actualSubspaceMutualRestrictionIso (A.holomorphic i j) (A.holomorphic j i)
    (A.mapsTo i j hij) (A.mapsTo j i hij.symm) (A.inverse i j hij) (A.inverse j i hij.symm)

private theorem no_three_distinct_bool (i j k : Bool) (hij : i≠j) (hik : i≠k) (hjk : j≠k) : False := by
  cases i <;> cases j <;> cases k <;> simp_all

/-- Genuine original two-model data internally give the native off-diagonal gluing datum. -/
def actualTwoModelOffDiagonalGlueData : CategoryTheory.GlueData' LocallyRingedSpace where
  J := Bool
  U := actualChartModel A
  V i j _ := actualOverlapModel A i j
  f i j _ := actualOverlapInclusion A i j
  t i j hij := (actualOverlapIso A i j hij).hom
  t' i j k hij hik hjk := (no_three_distinct_bool i j k hij hik hjk).elim
  t_fac i j k hij hik hjk := (no_three_distinct_bool i j k hij hik hjk).elim
  t_inv i j hij := (actualOverlapIso A i j hij).hom_inv_id
  cocycle i j k hij hik hjk := (no_three_distinct_bool i j k hij hik hjk).elim

/-- The actual constructed overlap maps give full native gluing data, with genuine open immersions. -/
def actualTwoModelGlueData : LocallyRingedSpace.GlueData where
  toGlueData := CategoryTheory.GlueData.ofGlueData' (actualTwoModelOffDiagonalGlueData A)
  f_open i j := by
    change LocallyRingedSpace.IsOpenImmersion ((actualTwoModelOffDiagonalGlueData A).f' i j)
    dsimp only [CategoryTheory.GlueData'.f']
    split_ifs with hij
    · infer_instance
    · have : LocallyRingedSpace.IsOpenImmersion ((actualTwoModelOffDiagonalGlueData A).f i j hij) := by
        change LocallyRingedSpace.IsOpenImmersion (actualOverlapInclusion A i j)
        infer_instance
      infer_instance

/-- The actual complex structural morphism of the unchanged original chart model. -/
abbrev actualChartPointMap (i : Bool) : actualChartModel A i ⟶ complexPoint :=
  subspacePointMap (n := A.dimension i) (A.carrier i)

/-- Actual original overlap inclusions retain the complex point without any scalar certificate. -/
theorem actualOverlapInclusion_point (i j : Bool) :
    actualOverlapInclusion A i j ≫ actualChartPointMap A i =
      subspacePointMap (n := A.dimension i) (actualOverlapCarrier A i j) :=
  actualSubspaceMap_point (f := (Subtype.val : A.overlap i j → A.domain i)) contMDiff_subtype_val
    (fun _ hx => hx)

/-- Actual original overlap transitions retain the SAME complex structural morphism. -/
theorem actualOverlapIso_point (i j : Bool) (hij : i≠j) :
    (actualOverlapIso A i j hij).hom ≫
        subspacePointMap (n := A.dimension j) (actualOverlapCarrier A j i) =
      subspacePointMap (n := A.dimension i) (actualOverlapCarrier A i j) :=
  actualSubspaceMap_point (A.holomorphic i j) (A.mapsTo i j hij)

/-- The internally constructed native gluing datum has genuine original complex-structural compatibility. -/
theorem actualTwoModelGlueData_point_compatible (i j : Bool) :
    (actualTwoModelGlueData A).f i j ≫ actualChartPointMap A i =
      (actualTwoModelGlueData A).t i j ≫ (actualTwoModelGlueData A).f j i ≫ actualChartPointMap A j := by
  cases i <;> cases j <;>
    simp [actualTwoModelGlueData,CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      actualTwoModelOffDiagonalGlueData,Category.assoc,actualOverlapInclusion_point,actualOverlapIso_point]

end
end Hironaka.HironakaActualTwoModelAnalyticGlueData
