/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualAnalyticSubspaceMaps
import Mathlib.Geometry.RingedSpace.OpenImmersion
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Actual reduced complex analytic spaces over the complex point

The native slice of locally ringed spaces retains complex structure. Its
Hausdorff second-countable objects with actual closed-analytic local models
form a full subcategory. Reduced stalks are derived from the genuine model
stalk isomorphisms; no resolution or terminal certificate is a field.
Blueprint: `hironaka-reduced-complex-analytic-spaces-extension.tex`.
-/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaReducedComplexAnalyticSpaces
noncomputable section
open Hironaka.HolomorphicIdealSheaves
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps

/-- The actual zero-dimensional complex manifold as a locally ringed point. -/
def complexPoint : LocallyRingedSpace :=
  ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel 0) (ComplexModel 0)

/-- The original constant holomorphic map retains the actual complex structure. -/
def ambientPointMap (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] :
    ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel n) M ⟶ complexPoint :=
  ChartedSpace.locallyRingedSpaceMap (fun _ : M => (0 : ComplexModel 0)) contMDiff_const

/-- The genuine quotient subspace's structural morphism. -/
def subspacePointMap {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] (C : Set M) :
    actualSubspaceLocallyRingedSpace (n := n) C ⟶ complexPoint :=
  actualSubspaceInclusion (n := n) C ≫ ambientPointMap n M

/-- Actual embedded models in original coordinate opens, as objects over the complex point. -/
def modelOver {n : ℕ} (U : Opens (ComplexModel n)) (C : Set U) : Over complexPoint :=
  Over.mk (subspacePointMap (n := n) C)

/-- The usual local analytic-model property, with genuine open immersions over the complex point. -/
def hasAnalyticCharts : ObjectProperty (Over complexPoint) := fun A =>
  T2Space A.left ∧ SecondCountableTopology A.left ∧
    ∀ x : A.left, ∃ (n : ℕ) (U : Opens (ComplexModel n)) (C : Set U),
      IsComplexAnalyticSubset (n := n) C ∧
      ∃ i : (modelOver U C).left ⟶ A.left,
        LocallyRingedSpace.IsOpenImmersion i ∧
        i ≫ A.hom=(modelOver U C).hom ∧ x ∈ range i.base

/-- Reduced complex analytic spaces form the native full subcategory of the complex slice. -/
abbrev ReducedComplexAnalyticSpace := hasAnalyticCharts.FullSubcategory

/-- Every actual closed analytic subset is internally an object of the analytic category. -/
theorem hasAnalyticCharts_model {n : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (hC : IsComplexAnalyticSubset (n := n) C) : hasAnalyticCharts (modelOver U C) := by
  refine ⟨?_,?_,?_⟩
  · change T2Space C
    infer_instance
  · change SecondCountableTopology C
    infer_instance
  intro x
  refine ⟨n,U,C,hC,𝟙 _,inferInstance,Category.id_comp _,?_⟩
  exact ⟨x,rfl⟩

/-- The original analytic model with its proved local-model property. -/
def embeddedModel {n : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (hC : IsComplexAnalyticSubset (n := n) C) : ReducedComplexAnalyticSpace :=
  ⟨modelOver U C,hasAnalyticCharts_model U C hC⟩

/-- Actual model stalk isomorphisms prove reducedness of every abstract analytic stalk. -/
theorem isReduced_stalk (A : ReducedComplexAnalyticSpace) (x : A.obj.left) :
    IsReduced (A.obj.left.presheaf.stalk x).carrier := by
  obtain ⟨n,U,C,_hC,i,hi,_hpoint,c,hcx⟩ := A.property.2.2 x
  subst x
  let : LocallyRingedSpace.IsOpenImmersion i := hi
  let e := (asIso (i.stalkMap c)).commRingCatIsoToRingEquiv
  let : IsReduced ((modelOver U C).left.presheaf.stalk c).carrier := by
    change IsReduced ((actualSubspaceSheaf (n := n) C).presheaf.stalk c).carrier
    exact actualSubspaceStalk_isReduced (n := n) C c
  refine ⟨?_⟩
  intro r hr
  apply e.injective
  exact (IsReduced.eq_zero (e r) (hr.map e.toRingHom)).trans (map_zero e).symm

section Maps
variable {n m : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]

/-- The actual holomorphic subspace map commutes with the original complex structural maps. -/
theorem actualSubspaceMap_point {f : M → N}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    {C : Set M} {D : Set N} (hCD : ∀ x ∈ C,f x ∈ D) :
    actualSubspaceMap hf hCD ≫ subspacePointMap (n := m) D=subspacePointMap (n := n) C := by
  have hc : ChartedSpace.locallyRingedSpaceMap f hf ≫ ambientPointMap m N=ambientPointMap n M := by
    exact (ChartedSpace.locallyRingedSpace_comp (IM := 𝓘(ℂ,ComplexModel n))
      (IN := 𝓘(ℂ,ComplexModel m)) (IP := 𝓘(ℂ,ComplexModel 0)) hf
      (show ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel 0) ∞
        (fun _ : N => (0 : ComplexModel 0)) from contMDiff_const)).symm
  unfold subspacePointMap
  rw [← Category.assoc,← actualSubspaceMap_inclusion,Category.assoc,hc]

end Maps

/-- Literal original holomorphic maps induce actual morphisms in the complex analytic category. -/
def embeddedModelMap {n m : ℕ} {U : Opens (ComplexModel n)} {V : Opens (ComplexModel m)}
    {C : Set U} {D : Set V} (hC : IsComplexAnalyticSubset (n := n) C)
    (hD : IsComplexAnalyticSubset (n := m) D) {f : U → V}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (hCD : ∀ x ∈ C,f x ∈ D) : embeddedModel U C hC ⟶ embeddedModel V D hD :=
  ObjectProperty.homMk (Over.homMk (actualSubspaceMap hf hCD) (actualSubspaceMap_point hf hCD))

/-- The actual analytic-category morphism retains original identity maps. -/
theorem embeddedModelMap_id {n : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (hC : IsComplexAnalyticSubset (n := n) C) :
    embeddedModelMap hC hC (f := id) contMDiff_id (fun _ hx => hx)=𝟙 (embeddedModel U C hC) := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact actualSubspaceMap_id (n := n) C

/-- Actual analytic-category morphisms preserve original holomorphic composition. -/
theorem embeddedModelMap_comp {n m p : ℕ}
    {U : Opens (ComplexModel n)} {V : Opens (ComplexModel m)} {W : Opens (ComplexModel p)}
    {C : Set U} {D : Set V} {E : Set W}
    (hC : IsComplexAnalyticSubset (n := n) C) (hD : IsComplexAnalyticSubset (n := m) D)
    (hE : IsComplexAnalyticSubset (n := p) E) {f : U → V} {g : V → W}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (hg : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel p) ∞ g)
    (hCD : ∀ x ∈ C,f x ∈ D) (hDE : ∀ y ∈ D,g y ∈ E) :
    embeddedModelMap hC hE (hg.comp hf) (fun x hx => hDE (f x) (hCD x hx))=
      embeddedModelMap hC hD hf hCD ≫ embeddedModelMap hD hE hg hDE := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact actualSubspaceMap_comp hf hg hCD hDE

end
end Hironaka.HironakaReducedComplexAnalyticSpaces
