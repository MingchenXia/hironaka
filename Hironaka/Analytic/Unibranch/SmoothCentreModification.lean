import Hironaka.Analytic.Unibranch.EmbeddedBlowupUniversalSheaf
import Hironaka.Analytic.Unibranch.OriginalClosedSubspaceFactorization
import Hironaka.Resolution.HironakaContainedCentrePulledIdeal
import Hironaka.Resolution.HironakaSingularSubspaceBlowupCartierUniversalProjectionLocallyFree

/-!
# Intrinsic smooth-centre blowups and finite original modifications

The core ideal-blowup predicate is own entire-ideal rank-one data plus its
full ORIGINAL-source universal property. Smooth-centre steps additionally
require an actual smooth closed-centre morphism and proper bimeromorphicity.
The contained ambient construction DERIVES these from ordinary containment,
smoothness and density. No ambient or resolution packet is in the definition.
Blueprint FIRST: `smooth-centre-modification.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.SmoothCentreModification

open Hironaka Hironaka.BlowupSequences
  Hironaka HironakaActualAnalyticSubspace
  HironakaSingularModuleSheafStalk HironakaIntrinsicReducedCentreIdealSheaf
  HironakaNativePulledIdealSheaf HironakaContainedCentrePulledIdeal
  HironakaSingularSubspaceBlowupCartierUniversalIdealSheaf
  HironakaSingularSubspaceBlowupCartierUniversalProjectionLocallyFree
  SourceReducedComplexSpace EmbeddedBlowup

noncomputable section

/-- Standard native singleton local-free generators on the ENTIRE actual module. -/
def HasRankOneData {X : LocallyRingedSpace.{0}}
    (B : SheafOfModules.{0} (forgetRing X.toSheafedSpace.sheaf)) : Prop :=
  ∃ q : B.LocalGeneratorsData.{0},
    q.IsLocallyFreeData ∧ ∀ i, Nonempty (Unique (q.generators i).I)

/-- General whole-ideal blowup: own Cartier data and the full original UP.
There is no density, proper-bimeromorphicity or component-retention condition. -/
def IsIdealBlowup {X Y : SourceReducedComplexSpace} (p : Y ⟶ X)
    (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
    (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf)) : Prop :=
  HasRankOneData (nativePulledIdealModule p.hom.left B b) ∧
    ∀ (A : SourceReducedComplexSpace) (F : A ⟶ X),
      HasRankOneData (nativePulledIdealModule F.hom.left B b) →
        ∃! L : A ⟶ Y, L ≫ p = F

/-- An actual original smooth closed-centre morphism and its admissible blowup.
All ideals and every full morphism live on the ORIGINAL objects. -/
def IsSmoothCentreBlowup {X Y S : SourceReducedComplexSpace}
    (p : Y ⟶ X) (i : S ⟶ X) : Prop :=
  S.IsSmooth ∧
  Topology.IsClosedEmbedding i.hom.left.base ∧
  (∀ s : S.obj.left, Function.Surjective (i.hom.left.stalkMap s)) ∧
  X.IsAnalyticSubset (range i.hom.left.base) ∧
  interior (range i.hom.left.base) = ∅ ∧
  IsIdealBlowup p
    (intrinsicReducedCentreIdealModule X.obj.left (range i.hom.left.base))
    (intrinsicReducedCentreIdealInclusion X.obj.left (range i.hom.left.base)) ∧
  IsProperBimeromorphic p

/-- A step retains its full original smooth closed-centre morphism. -/
def IsSmoothCentreStep {X Y : SourceReducedComplexSpace} (p : Y ⟶ X) : Prop :=
  ∃ (S : SourceReducedComplexSpace) (i : S ⟶ X), IsSmoothCentreBlowup p i

/-- The book's finite-composition construction on FULL ORIGINAL morphisms. -/
inductive IsModification : {X Y : SourceReducedComplexSpace} → (Y ⟶ X) → Prop
  | id (X : SourceReducedComplexSpace) : IsModification (𝟙 X)
  | cons {X Y Z : SourceReducedComplexSpace} (f : Z ⟶ Y) (g : Y ⟶ X)
      (hf : IsSmoothCentreStep f) (hg : IsModification g) : IsModification (f ≫ g)

theorem IsModification.of_step {X Y : SourceReducedComplexSpace} {p : Y ⟶ X}
    (hp : IsSmoothCentreStep p) : IsModification p := by
  simpa only [Category.comp_id] using IsModification.cons p (𝟙 X) hp (.id X)

theorem IsModification.comp {X Y Z : SourceReducedComplexSpace} {f : Z ⟶ Y} {g : Y ⟶ X}
    (hf : IsModification f) (hg : IsModification g) : IsModification (f ≫ g) := by
  revert X
  induction hf with
  | id => intro X g hg; simpa only [Category.id_comp] using hg
  | cons f g hf _ ih =>
    intro X h hh
    simpa only [Category.assoc] using IsModification.cons f (g ≫ h) hf (ih hh)

theorem IsModification.isProperMap {X Y : SourceReducedComplexSpace} {p : Y ⟶ X}
    (hp : IsModification p) : IsProperMap p.hom.left.base := by
  induction hp with
  | id => exact isProperMap_id
  | cons f g hf _ ih =>
    obtain ⟨S, i, _, _, _, _, _, _, hb⟩ := hf
    exact ih.comp hb.1

theorem IsModification.source_compact {X Y : SourceReducedComplexSpace}
    {p : Y ⟶ X} (hp : IsModification p) [CompactSpace X.obj.left] :
    CompactSpace Y.obj.left := by
  constructor
  simpa only [preimage_univ] using hp.isProperMap.isCompact_preimage
    (isCompact_univ : IsCompact (univ : Set X.obj.left))

section ContainedAmbient

variable {n : ℕ} {M Y : Type} [TopologicalSpace M] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {C W : Set M} {π : Y → M}

private theorem pulled_module_eq {T : LocallyRingedSpace.{0}}
    (F : T ⟶ actualSubspaceLocallyRingedSpace (n := n) W) (hCW : C ⊆ W) :
    nativePulledIdealModule F
      (intrinsicReducedCentreIdealModule (actualSubspaceLocallyRingedSpace (n := n) W)
        ((Subtype.val : W → M) ⁻¹' C))
      (intrinsicReducedCentreIdealInclusion (actualSubspaceLocallyRingedSpace (n := n) W)
        ((Subtype.val : W → M) ⁻¹' C)) =
      actualPulledCentreIdealModule (F ≫ actualSubspaceInclusion (n := n) W) C := by
  unfold nativePulledIdealModule actualPulledCentreIdealModule
  congr 1
  exact congrArg PresheafOfModules.Submodule.toPresheafOfModules
    (pulled_submodule_eq F hCW)

/-- Closed embedding of the SAME full original contained-centre morphism. -/
theorem contained_inclusion_isClosedEmbedding (hCa : IsComplexAnalyticSubset (n := n) C)
    (hWa : IsComplexAnalyticSubset (n := n) W) (hCW : C ⊆ W) :
    Topology.IsClosedEmbedding
      (OriginalClosedSubspaceFactorization.inclusion hCa hWa hCW).hom.left.base := by
  apply Topology.IsClosedEmbedding.of_comp Topology.IsEmbedding.subtypeVal
  exact hCa.isClosed.isClosedEmbedding_subtypeVal

/-- Surjectivity uses the SAME native closed-inclusion stalk maps and FULL square. -/
theorem contained_inclusion_stalk_surjective (hCa : IsComplexAnalyticSubset (n := n) C)
    (hWa : IsComplexAnalyticSubset (n := n) W) (hCW : C ⊆ W) (c : C) :
    Function.Surjective
      ((OriginalClosedSubspaceFactorization.inclusion hCa hWa hCW).hom.left.stalkMap c) := by
  let i : actualSubspaceLocallyRingedSpace (n := n) C ⟶
      actualSubspaceLocallyRingedSpace (n := n) W :=
    (OriginalClosedSubspaceFactorization.inclusion hCa hWa hCW).hom.left
  change Function.Surjective (i.stalkMap c)
  have hcomp : i ≫ actualSubspaceInclusion (n := n) W =
      actualSubspaceInclusion (n := n) C :=
    OriginalClosedSubspaceFactorization.inclusion_ambient hCa hWa hCW
  have hs : Function.Surjective ((i ≫ actualSubspaceInclusion (n := n) W).stalkMap c) := by
    rw [hcomp]
    exact actualSubspaceInclusionRingedHom_stalk_surjective (n := n) C c
  rw [LocallyRingedSpace.stalkMap_comp] at hs
  intro s
  obtain ⟨r, hr⟩ := hs s
  exact ⟨(actualSubspaceInclusion (n := n) W).stalkMap (i.base c) r, hr⟩

private theorem contained_inclusion_range (hCa : IsComplexAnalyticSubset (n := n) C)
    (hWa : IsComplexAnalyticSubset (n := n) W) (hCW : C ⊆ W) :
    range (OriginalClosedSubspaceFactorization.inclusion hCa hWa hCW).hom.left.base =
      (Subtype.val : W → M) ⁻¹' C := by
  ext w
  constructor
  · rintro ⟨c, rfl⟩
    exact c.property
  · intro hw
    exact ⟨⟨w.val, hw⟩, Subtype.ext rfl⟩

private theorem trace_interior_eq_empty (hdense : W ⊆ closure (W \ C)) :
    interior ((Subtype.val : W → M) ⁻¹' C) = ∅ := by
  rw [interior_eq_empty_iff_dense_compl, dense_iff_closure_eq, eq_univ_iff_forall]
  intro w
  rw [closure_subtype]
  have himage : (Subtype.val : W → M) '' (((Subtype.val : W → M) ⁻¹' C)ᶜ) = W \ C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
  change w.val ∈ closure ((Subtype.val : W → M) '' (((Subtype.val : W → M) ⁻¹' C)ᶜ))
  rw [himage]
  exact hdense w.property

/-- Own SAME intrinsic whole pulled ideal and full UP for EVERY original source. -/
theorem strictTransformMorphism_isIdealBlowup (hπ : IsBlowupAlong n C π)
    (hWa : IsComplexAnalyticSubset (n := n) W) (hCW : C ⊆ W)
    (hdense : W ⊆ closure (W \ C)) :
    IsIdealBlowup (strictTransformMorphism hπ hWa)
      (intrinsicReducedCentreIdealModule (ofClosedAnalytic W hWa).obj.left
        ((Subtype.val : W → M) ⁻¹' C))
      (intrinsicReducedCentreIdealInclusion (ofClosedAnalytic W hWa).obj.left
        ((Subtype.val : W → M) ⁻¹' C)) := by
  constructor
  · change HasRankOneData (nativePulledIdealModule
      (HironakaSingularSubspaceBlowupLift.strictTransformProjection hπ hWa.isClosed)
      (intrinsicReducedCentreIdealModule (actualSubspaceLocallyRingedSpace (n := n) W)
        ((Subtype.val : W → M) ⁻¹' C))
      (intrinsicReducedCentreIdealInclusion (actualSubspaceLocallyRingedSpace (n := n) W)
        ((Subtype.val : W → M) ⁻¹' C)))
    rw [pulled_module_eq _ hCW]
    exact projection_ideal_sheaf_exists_locallyFreeData hπ hWa.isClosed hdense
  · intro A F hF
    let G : A.obj.left ⟶ actualSubspaceLocallyRingedSpace (n := n) W := F.hom.left
    change HasRankOneData (nativePulledIdealModule G
      (intrinsicReducedCentreIdealModule (actualSubspaceLocallyRingedSpace (n := n) W)
        ((Subtype.val : W → M) ⁻¹' C))
      (intrinsicReducedCentreIdealInclusion (actualSubspaceLocallyRingedSpace (n := n) W)
        ((Subtype.val : W → M) ⁻¹' C))) at hF
    rw [pulled_module_eq _ hCW] at hF
    obtain ⟨q, hq, huniq⟩ := hF
    let qF : (actualPulledCentreIdealModule
      (F.hom.left ≫ actualSubspaceInclusion (n := n) W) C).LocalGeneratorsData.{0} := q
    let : qF.IsLocallyFreeData := hq
    let : ∀ i, Unique (qF.generators i).I := fun i => Classical.choice (huniq i)
    exact EmbeddedBlowupUniversalSheaf.exists_unique_source_factorization_of_locallyFreeData
      hπ hWa A F qF

/-- Actual containment, smoothness and density DERIVE the intrinsic admissible step. -/
theorem strictTransformMorphism_isSmoothCentreBlowup (hπ : IsBlowupAlong n C π)
    (hWa : IsComplexAnalyticSubset (n := n) W) (hC : IsClosedSubmanifold n C)
    (hCW : C ⊆ W) (hdense : W ⊆ closure (W \ C)) :
    IsSmoothCentreBlowup (strictTransformMorphism hπ hWa)
      (OriginalClosedSubspaceFactorization.inclusion
        (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hC) hWa hCW) := by
  let hCa := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hC
  have hrange := contained_inclusion_range hCa hWa hCW
  refine ⟨isSmooth_ofClosedAnalytic_of_isClosedSubmanifold hC,
    contained_inclusion_isClosedEmbedding hCa hWa hCW,
    contained_inclusion_stalk_surjective hCa hWa hCW, ?_, ?_, ?_,
    strictTransformMorphism_isProperBimeromorphic hπ hWa hCa hdense⟩
  · rw [hrange]
    exact isAnalyticSubset_preimage_val hWa hCa
  · rw [hrange]
    exact trace_interior_eq_empty hdense
  · rw [hrange]
    exact strictTransformMorphism_isIdealBlowup hπ hWa hCW hdense

theorem strictTransformMorphism_isSmoothCentreStep (hπ : IsBlowupAlong n C π)
    (hWa : IsComplexAnalyticSubset (n := n) W) (hC : IsClosedSubmanifold n C)
    (hCW : C ⊆ W) (hdense : W ⊆ closure (W \ C)) :
    IsSmoothCentreStep (strictTransformMorphism hπ hWa) :=
  ⟨_, _, strictTransformMorphism_isSmoothCentreBlowup hπ hWa hC hCW hdense⟩

end ContainedAmbient
end
end Hironaka.Analytic.Unibranch.SmoothCentreModification
