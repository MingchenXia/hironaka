import Hironaka.Resolution.HironakaEmbeddedNativeMorphism
import Hironaka.Resolution.HironakaEmbeddedCommonResolution

/-!
# Original intrinsic restriction maps construct the native common resolution

The original restricted LRS maps, as actual open immersions with equal images,
construct their intrinsic isomorphism by the open-immersion universal property.
The native holomorphy theorem then derives the native transition and original
singleton fibres; neither is supplied. This consumes the geometric common-
model producer and retains the entire original structure-sheaf square.

Blueprint: `hironaka-embedded-native-morphism.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaEmbeddedNativeMorphism

noncomputable section

open Hironaka.BlowupSequences AnalyticModificationLocalDiscrepancy
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaReducedComplexAnalyticSpaces
  HironakaActualAnalyticSubspaceLocalFunctions

/-- Two actual open immersions with equal image have an internally constructed
intrinsic isomorphism over their original target. -/
def openImmersionIsoOfRangeEq {P Q R : LocallyRingedSpace}
    (f : P ⟶ R) (g : Q ⟶ R)
    [LocallyRingedSpace.IsOpenImmersion f] [LocallyRingedSpace.IsOpenImmersion g]
    (h : range f.base = range g.base) : P ≅ Q where
  hom := LocallyRingedSpace.IsOpenImmersion.lift g f h.subset
  inv := LocallyRingedSpace.IsOpenImmersion.lift f g h.symm.subset
  hom_inv_id := by
    apply (cancel_mono f).mp
    simp only [Category.assoc, LocallyRingedSpace.IsOpenImmersion.lift_fac,
      Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono g).mp
    simp only [Category.assoc, LocallyRingedSpace.IsOpenImmersion.lift_fac,
      Category.id_comp]

theorem openImmersionIsoOfRangeEq_hom_fac {P Q R : LocallyRingedSpace}
    (f : P ⟶ R) (g : Q ⟶ R)
    [LocallyRingedSpace.IsOpenImmersion f] [LocallyRingedSpace.IsOpenImmersion g]
    (h : range f.base = range g.base) :
    (openImmersionIsoOfRangeEq f g h).hom ≫ g = f :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac g f h.subset

/-- The literal original point map, named only to keep the restriction
formulas readable; it is not separately supplied. -/
def originalPointMap {m n : ℕ} {Y M : Type}
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    [TopologicalSpace M] [ChartedSpace (ComplexModel m) M] [IsComplexManifold m M]
    {D : Set M}
    (F : actualSubspaceLocallyRingedSpace (n := n) (univ : Set Y) ⟶
      actualSubspaceLocallyRingedSpace (n := m) D) : Y → M :=
  fun y => (F.base ⟨y, mem_univ y⟩).val

variable {m n : ℕ} {M Y₀ Y₁ : Type}
  [TopologicalSpace M] [ChartedSpace (ComplexModel m) M] [IsComplexManifold m M]
  [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n) Y₀] [IsComplexManifold n Y₀]
  [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁] [IsComplexManifold n Y₁]
  {D B : Set M}

/-- The original inverse-image good open, with holomorphy already derived
from the intrinsic map rather than supplied as a native certificate. -/
def originalGoodOpen {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    (F : actualSubspaceLocallyRingedSpace (n := n) (univ : Set Y) ⟶
      actualSubspaceLocallyRingedSpace (n := m) D)
    (hF : F ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) (univ : Set Y))
    (B : Set M) (hB : IsClosed B) : Opens Y :=
  HironakaEmbeddedCommon.goodOpen (originalPointMap F)
    (contMDiff_original_pointMap F hF) B hB

/-- Restriction of the original intrinsic morphism to its literal good open. -/
def restrictedOriginalMorphism {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    (F : actualSubspaceLocallyRingedSpace (n := n) (univ : Set Y) ⟶
      actualSubspaceLocallyRingedSpace (n := m) D)
    (hF : F ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) (univ : Set Y))
    (B : Set M) (hB : IsClosed B) :
    actualSubspaceLocallyRingedSpace (n := n)
      (univ : Set (originalGoodOpen F hF B hB)) ⟶
        actualSubspaceLocallyRingedSpace (n := m) D :=
  actualOpenSubspaceMap (n := n) (univ : Set Y) (originalGoodOpen F hF B hB) ≫ F

private theorem restrictedOriginalMorphism_point {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    (F : actualSubspaceLocallyRingedSpace (n := n) (univ : Set Y) ⟶
      actualSubspaceLocallyRingedSpace (n := m) D)
    (hF : F ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) (univ : Set Y))
    (B : Set M) (hB : IsClosed B) :
    restrictedOriginalMorphism F hF B hB ≫ subspacePointMap (n := m) D =
      subspacePointMap (n := n) (univ : Set (originalGoodOpen F hF B hB)) := by
  unfold restrictedOriginalMorphism
  rw [Category.assoc, hF]
  exact actualSubspaceMap_point contMDiff_subtype_val (fun _ _ => mem_univ _)

/-- The ORIGINAL open immersion restrictions construct a genuine native
transition, its commuting equation and singleton original fibres. -/
theorem exists_original_native_transition
    (F₀ : actualSubspaceLocallyRingedSpace (n := n) (univ : Set Y₀) ⟶
      actualSubspaceLocallyRingedSpace (n := m) D)
    (F₁ : actualSubspaceLocallyRingedSpace (n := n) (univ : Set Y₁) ⟶
      actualSubspaceLocallyRingedSpace (n := m) D)
    (hF₀ : F₀ ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) (univ : Set Y₀))
    (hF₁ : F₁ ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) (univ : Set Y₁))
    (hBc : IsClosed B)
    [hR₀ : LocallyRingedSpace.IsOpenImmersion (restrictedOriginalMorphism F₀ hF₀ B hBc)]
    [hR₁ : LocallyRingedSpace.IsOpenImmersion (restrictedOriginalMorphism F₁ hF₁ B hBc)]
    (hrange : range (restrictedOriginalMorphism F₁ hF₁ B hBc).base =
      range (restrictedOriginalMorphism F₀ hF₀ B hBc).base) :
    ∃ e : originalGoodOpen F₁ hF₁ B hBc ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      originalGoodOpen F₀ hF₀ B hBc,
      (∀ y, originalPointMap F₀ (e y).val = originalPointMap F₁ y.val) ∧
      InjOn (originalPointMap F₀) (originalPointMap F₀ ⁻¹' Bᶜ) := by
  let R₀ := restrictedOriginalMorphism F₀ hF₀ B hBc
  let R₁ := restrictedOriginalMorphism F₁ hF₁ B hBc
  let E := openImmersionIsoOfRangeEq R₁ R₀ hrange
  have hfac : E.hom ≫ R₀ = R₁ := openImmersionIsoOfRangeEq_hom_fac R₁ R₀ hrange
  have hEp : E.hom ≫ subspacePointMap (n := n)
      (univ : Set (originalGoodOpen F₀ hF₀ B hBc)) =
      subspacePointMap (n := n) (univ : Set (originalGoodOpen F₁ hF₁ B hBc)) := by
    rw [← restrictedOriginalMorphism_point F₀ hF₀ B hBc, ← Category.assoc, hfac]
    exact restrictedOriginalMorphism_point F₁ hF₁ B hBc
  let e := nativeDiffeomorph E hEp
  refine ⟨e, ?_, ?_⟩
  · intro y
    have h := congrArg (fun K => (K.base ⟨y, mem_univ y⟩).val) hfac
    exact h
  · intro y hy z hz heq
    let p : (univ : Set (originalGoodOpen F₀ hF₀ B hBc)) :=
      ⟨⟨y, hy⟩, mem_univ _⟩
    let q : (univ : Set (originalGoodOpen F₀ hF₀ B hBc)) :=
      ⟨⟨z, hz⟩, mem_univ _⟩
    have hR : R₀.base p = R₀.base q := Subtype.ext heq
    have hpq : p = q := hR₀.base_open.injective hR
    exact congrArg (fun w => w.val.val) hpq

/-- From ORIGINAL intrinsic restrictions, internally construct the common
native smooth model and retain the WHOLE original intrinsic sheaf square. -/
theorem exists_original_compact_smooth_common_model [CompactSpace Y₀]
    [CompactSpace Y₁] [ConnectedSpace Y₁]
    (F₀ : actualSubspaceLocallyRingedSpace (n := n) (univ : Set Y₀) ⟶
      actualSubspaceLocallyRingedSpace (n := m) D)
    (F₁ : actualSubspaceLocallyRingedSpace (n := n) (univ : Set Y₁) ⟶
      actualSubspaceLocallyRingedSpace (n := m) D)
    (hF₀ : F₀ ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) (univ : Set Y₀))
    (hF₁ : F₁ ≫ subspacePointMap (n := m) D = subspacePointMap (n := n) (univ : Set Y₁))
    (hBa : IsComplexAnalyticSubset (n := m) B)
    (hthin₀ : interior (originalPointMap F₀ ⁻¹' B) = ∅)
    (hthin₁ : interior (originalPointMap F₁ ⁻¹' B) = ∅)
    [hR₀ : LocallyRingedSpace.IsOpenImmersion
      (restrictedOriginalMorphism F₀ hF₀ B hBa.isClosed)]
    [hR₁ : LocallyRingedSpace.IsOpenImmersion
      (restrictedOriginalMorphism F₁ hF₁ B hBa.isClosed)]
    (hrange : range (restrictedOriginalMorphism F₁ hF₁ B hBa.isClosed).base =
      range (restrictedOriginalMorphism F₀ hF₀ B hBa.isClosed).base) :
    ∃ (Z : Type) (_ : TopologicalSpace Z) (_ : ChartedSpace (ComplexModel n) Z)
      (_ : IsComplexManifold n Z) (_ : ConnectedSpace Z) (_ : CompactSpace Z)
      (g₀ : Z → Y₀) (g₁ : Z → Y₁)
      (hg₀ : IsAnalyticModification (n := n) g₀)
      (hg₁ : IsAnalyticModification (n := n) g₁),
      originalPointMap F₀ ∘ g₀ = originalPointMap F₁ ∘ g₁ ∧
      actualSubspaceMap hg₀.1 (fun z (_ : z ∈ (univ : Set Z)) => mem_univ (g₀ z)) ≫ F₀ =
        actualSubspaceMap hg₁.1 (fun z (_ : z ∈ (univ : Set Z)) => mem_univ (g₁ z)) ≫ F₁ := by
  obtain ⟨e, he, hinj⟩ :=
    exists_original_native_transition F₀ F₁ hF₀ hF₁ hBa.isClosed hrange
  obtain ⟨Z, instTop, instChart, instMfd, instConn, instCompact, g₀, g₁, hg₀, hg₁, hbase⟩ :=
    HironakaEmbeddedCommon.exists_compact_smooth_common_model
      (contMDiff_original_pointMap F₀ hF₀) (contMDiff_original_pointMap F₁ hF₁)
      hBa hthin₀ hthin₁ e he hinj
  refine ⟨Z, instTop, instChart, instMfd, instConn, instCompact, g₀, g₁, hg₀, hg₁, hbase, ?_⟩
  have hp₀ : (actualSubspaceMap hg₀.1
      (fun z (_ : z ∈ (univ : Set Z)) => mem_univ (g₀ z)) ≫ F₀) ≫
      subspacePointMap (n := m) D = subspacePointMap (n := n) (univ : Set Z) := by
    rw [Category.assoc, hF₀]
    exact actualSubspaceMap_point hg₀.1 (fun _ _ => mem_univ _)
  have hp₁ : (actualSubspaceMap hg₁.1
      (fun z (_ : z ∈ (univ : Set Z)) => mem_univ (g₁ z)) ≫ F₁) ≫
      subspacePointMap (n := m) D = subspacePointMap (n := n) (univ : Set Z) := by
    rw [Category.assoc, hF₁]
    exact actualSubspaceMap_point hg₁.1 (fun _ _ => mem_univ _)
  apply actualSubspaceMap_eq_of_base_eq _ _ hp₀ hp₁
  ext z
  apply Subtype.ext
  exact congrFun hbase z.val

end

end Hironaka.HironakaEmbeddedNativeMorphism
