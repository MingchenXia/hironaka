import Hironaka.Analytic.Unibranch.SmoothCentreModification
import Hironaka.Blowup.BlowupTowers
import Hironaka.Resolution.HironakaAdmissibleCalculus

/-!
# The SAME original projection of an actual contained-centre blowup tower

Inputs are ONLY the existing native tower, original analytic W, and literal
per-prefix centre containment/density. Every intrinsic full original step is
DERIVED by the contained ambient constructor. The output is the actual native
composite's full reduced-subspace morphism, not a replacement projection.
Native strict-transform composition/carrier dictionaries get zero new credit.
Blueprint FIRST: `contained-centre-modification-sequence.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.ContainedCentreModificationSequence

open Hironaka Hironaka.BlowupSequences
  Hironaka BlowupTowers
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaReducedComplexAnalyticSpaces
  SourceReducedComplexSpace SmoothCentreModification EmbeddedBlowup

noncomputable section

variable {n : ℕ} {X Y : CMfd.{0} n}

/-- Literal ordinary geometry of EVERY centre of the SAME actual native tower. -/
def CentresContainedDense (W : Set X) : {Y : CMfd.{0} n} → BlowupTower X Y → Prop
  | _, .refl => True
  | _, .step T C _ _ =>
      CentresContainedDense W T ∧ C ⊆ strictTransform n T.proj W ∧
        strictTransform n T.proj W ⊆ closure (strictTransform n T.proj W \ C)

-- Technical dictionaries for SAME successive native strict transforms. No new geometry.
private def iteratedCarrier (W : Set X) : {Y : CMfd.{0} n} → BlowupTower X Y → Set Y
  | _, .refl => W
  | _, .step T _ π _ => strictTransform n π (iteratedCarrier W T)

private theorem iterated_analytic {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    {Y : CMfd.{0} n} (T : BlowupTower X Y) :
    IsComplexAnalyticSubset (n := n) (iteratedCarrier W T) := by
  induction T with
  | refl => exact hW
  | step T C π hπ ih =>
    exact HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong hπ ih

private theorem iterated_eq_native {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    {Y : CMfd.{0} n} (T : BlowupTower X Y) :
    iteratedCarrier W T = strictTransform n T.proj W := by
  induction T with
  | refl =>
    symm
    change strictTransform n (id : X → X) W = W
    rw [strictTransform, exceptionalLocus_id, sdiff_empty, preimage_id]
    exact hW.isClosed.closure_eq
  | step T C π hπ ih =>
    change strictTransform n π (iteratedCarrier W T) = strictTransform n (T.proj ∘ π) W
    rw [ih, StrictTransformComposition.strictTransform_comp T.contMDiff_proj hπ.contMDiff]

private theorem iterated_landing {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    {Y : CMfd.{0} n} (T : BlowupTower X Y) : iteratedCarrier W T ⊆ T.proj ⁻¹' W := by
  rw [iterated_eq_native hW T]
  exact HironakaAdmissibleCalculus.strictTransform_subset_preimage T.contMDiff_proj.continuous hW.isClosed

private def iteratedProjection {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    {Y : CMfd.{0} n} (T : BlowupTower X Y) :
    ofClosedAnalytic (iteratedCarrier W T) (iterated_analytic hW T) ⟶ ofClosedAnalytic W hW :=
  ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap T.contMDiff_proj (fun _ hy => iterated_landing hW T hy))
    (actualSubspaceMap_point T.contMDiff_proj (fun _ hy => iterated_landing hW T hy)))

private theorem iteratedProjection_refl {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) :
    iteratedProjection hW (.refl : BlowupTower X X) = 𝟙 (ofClosedAnalytic W hW) := by
  apply morphism_eq_of_pointwise_eq
  intro x
  rfl

private theorem iteratedProjection_step {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) {Y Z : CMfd.{0} n}
    (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π) :
    iteratedProjection hW (.step T C π hπ) =
      strictTransformMorphism hπ (iterated_analytic hW T) ≫ iteratedProjection hW T := by
  apply morphism_eq_of_pointwise_eq
  intro x
  apply Subtype.ext
  rfl

private theorem iterated_isModification {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) {Y : CMfd.{0} n}
    (T : BlowupTower X Y) (hT : CentresContainedDense W T) :
    IsModification (iteratedProjection hW T) := by
  induction T with
  | refl =>
    rw [iteratedProjection_refl]
    exact .id _
  | step T C π hπ ih =>
    obtain ⟨hT, hCW, hd⟩ := hT
    have hCW' : C ⊆ iteratedCarrier W T := by rwa [iterated_eq_native hW T]
    have hd' : iteratedCarrier W T ⊆ closure (iteratedCarrier W T \ C) := by
      rwa [iterated_eq_native hW T]
    rw [iteratedProjection_step]
    exact .cons _ _
      (strictTransformMorphism_isSmoothCentreStep hπ (iterated_analytic hW T) hπ.1 hCW' hd')
      (ih hT)

/-- The native final strict transform and unchanged FULL original composite projection. -/
def projectionMorphism {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    {Y : CMfd.{0} n} (T : BlowupTower X Y) :
    ofClosedAnalytic (strictTransform n T.proj W)
      (HironakaAdmissibleCalculus.isComplexAnalyticSubset_strictTransform T.isBlowupSequence hW) ⟶
      ofClosedAnalytic W hW :=
  ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap T.contMDiff_proj (fun _ hy =>
      HironakaAdmissibleCalculus.strictTransform_subset_preimage T.contMDiff_proj.continuous hW.isClosed hy))
    (actualSubspaceMap_point T.contMDiff_proj (fun _ hy =>
      HironakaAdmissibleCalculus.strictTransform_subset_preimage T.contMDiff_proj.continuous hW.isClosed hy)))

theorem projectionMorphism_point {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    {Y : CMfd.{0} n} (T : BlowupTower X Y) (y : strictTransform n T.proj W) :
    ((projectionMorphism hW T).hom.left.base y).val = T.proj y.val := rfl

/-- The full quotient-sheaf square is the SAME original ambient composite square. -/
theorem projectionMorphism_ambient {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    {Y : CMfd.{0} n} (T : BlowupTower X Y) :
    (projectionMorphism hW T).hom.left ≫ actualSubspaceInclusion (n := n) W =
      actualSubspaceInclusion (n := n) (strictTransform n T.proj W) ≫
        ChartedSpace.locallyRingedSpaceMap T.proj T.contMDiff_proj :=
  (actualSubspaceMap_inclusion T.contMDiff_proj (fun _ hy =>
    HironakaAdmissibleCalculus.strictTransform_subset_preimage T.contMDiff_proj.continuous hW.isClosed hy)).symm

private theorem object_eq {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {A B : Set M} (hA : IsComplexAnalyticSubset (n := n) A)
    (hB : IsComplexAnalyticSubset (n := n) B) (hAB : A = B) :
    ofClosedAnalytic A hA = ofClosedAnalytic B hB := by
  cases hAB
  rfl

private theorem object_eqToHom_base {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {A B : Set M} (hA : IsComplexAnalyticSubset (n := n) A)
    (hB : IsComplexAnalyticSubset (n := n) B) (hAB : A = B) (a : A) :
    ((eqToHom (object_eq hA hB hAB)).hom.left.base a).val = a.val := by
  cases hAB
  rfl

private theorem modification_precomp_eq {A B X : SourceReducedComplexSpace}
    (hAB : A = B) {p : B ⟶ X} (hp : IsModification p) :
    IsModification (eqToHom hAB ≫ p) := by
  cases hAB
  simpa only [eqToHom_refl, Category.id_comp] using hp

/-- ONLY literal per-prefix geometry derives a finite intrinsic modification
of the SAME native composite morphism, including its ENTIRE original sheaf map. -/
theorem projectionMorphism_isModification {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) {Y : CMfd.{0} n}
    (T : BlowupTower X Y) (hT : CentresContainedDense W T) :
    IsModification (projectionMorphism hW T) := by
  let hN := HironakaAdmissibleCalculus.isComplexAnalyticSubset_strictTransform T.isBlowupSequence hW
  let hI := iterated_analytic hW T
  have hsets : iteratedCarrier W T = strictTransform n T.proj W := iterated_eq_native hW T
  have hobj : ofClosedAnalytic (iteratedCarrier W T) hI =
      ofClosedAnalytic (strictTransform n T.proj W) hN := object_eq hI hN hsets
  have hm := modification_precomp_eq hobj.symm (iterated_isModification hW T hT)
  have hfull : eqToHom hobj.symm ≫ iteratedProjection hW T = projectionMorphism hW T := by
    apply morphism_eq_of_pointwise_eq
    intro y
    apply Subtype.ext
    change T.proj ((eqToHom hobj.symm).hom.left.base y).val = T.proj y.val
    exact congrArg T.proj (object_eqToHom_base hN hI hsets.symm y)
  rw [hfull] at hm
  exact hm

end
end Hironaka.Analytic.Unibranch.ContainedCentreModificationSequence
