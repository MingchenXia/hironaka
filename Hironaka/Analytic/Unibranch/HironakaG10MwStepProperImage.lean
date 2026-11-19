import Hironaka.Analytic.Unibranch.HironakaG10MwStrataStep
import Hironaka.Analytic.Unibranch.OriginalAnalyticCover
import Hironaka.Analytic.Unibranch.EmbeddedCommonResolutionGeneralAnalyticSubsets
import Hironaka.Analytic.ProperMappingTheorem

/-!
# Proper images under one blow-up step (G10RD item L5.c.1; lane G10MW, run 0081)

**`stepProperImage s c : StepProperImage s c`**: the image of a native analytic subset under the blow-up
projection `σ = stepσ s c` of an admissible centre is analytic.

The source of `σ` is glued from the strict transforms `S i ⊆ Y i` of closed analytic carriers `W i ⊆ M i` under
manifold blow-ups `π i : Y i → M i`, with open charts `J i : W i ⟶ X` covering `X` and saturated local pieces
(`EmbeddedIdealBlowupObjectGluing.preimage_chart_range`).  Over `range (J i)` the image of `P` is
`J i (π i (P ∩ S i))`, and `π i (P ∩ S i)` is analytic in the manifold `M i` by Remmert's proper mapping theorem
(`ProperMappingTheorem.isComplexAnalyticSubset_image`, `π i` proper and holomorphic); the dictionary
`isAnalyticSubset_closedAnalytic_iff` translates between native analytic subsets of `ofClosedAnalytic` and
manifold analytic subsets, and `OriginalAnalyticCover.isAnalyticSubset_of_openImmersion_cover` glues.

* `isAnalyticSubset_image_projection` — the statement for the general glued blow-up
  `EmbeddedIdealBlowupOriginalObject.projectionMorphism`;
* **`stepProperImage`** — the specialisation to `stepσ s c`;
* `exists_isStratumComponent_of_next_proper`, `isStratumComponent_strictSet_proper` — L5 (c) for a proper family
  with `hPM` discharged (only `hDa`, the analyticity of the centre's nonunit locus, remains).

No named input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace Topology CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10MwStepProperImage

open Hironaka Hironaka.BlowupSequences
  Hironaka HironakaActualAnalyticSubspace
  HironakaReducedComplexAnalyticSpaces HironakaSingularSubspaceBlowupLift
  HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf AnalyticDimensionBasics
  SourceReducedComplexSpace EmbeddedBlowup

noncomputable section

section General

variable {X : SourceReducedComplexSpace} {ι : Type} {n : ι → ℕ}
  {M Y : ι → Type} [∀ i, TopologicalSpace (M i)] [∀ i, TopologicalSpace (Y i)]
  [∀ i, ChartedSpace (ComplexModel (n i)) (M i)] [∀ i, IsComplexManifold (n i) (M i)]
  [∀ i, ChartedSpace (ComplexModel (n i)) (Y i)] [∀ i, IsComplexManifold (n i) (Y i)]
  {C W : ∀ i, Set (M i)} {π : ∀ i, Y i → M i}
  (hW : ∀ i, IsComplexAnalyticSubset (n := n i) (W i))
  (hπ : ∀ i, IsBlowupAlong (n i) (C i) (π i))
  (J : ∀ i, ofClosedAnalytic (W i) (hW i) ⟶ X)
  [hJopen : ∀ i, LocallyRingedSpace.IsOpenImmersion (J i).hom.left]
  (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (hd : ∀ i, W i ⊆ closure (W i \ C i))
  (hJ : ∀ i (y : W i),
    Ideal.map ((actualSubspaceInclusion (n := n i) (W i)).stalkMap y).hom
      (HironakaSmoothCentreRealDomainActualSheafStalk.actualWholeSheafStalkIdeal
        (HolomorphicIdealSheaves.vanishingIdeal (n := n i) (C i)) y.val) =
          nativePulledIdealStalkIdeal (J i).hom.left B b y)
  (hcover : ∀ x : X.obj.left, ∃ (i : ι) (w : W i), (J i).hom.left.base w = x)

/-- **Remmert for the glued blow-up projection**: images of native analytic subsets are analytic. -/
theorem isAnalyticSubset_image_projection
    {P : Set (EmbeddedIdealBlowupOriginalObject.sourceObject hW hπ J B b hd hJ hcover).obj.left}
    (hP : (EmbeddedIdealBlowupOriginalObject.sourceObject hW hπ J B b hd hJ hcover).IsAnalyticSubset P) :
    X.IsAnalyticSubset
      ((EmbeddedIdealBlowupOriginalObject.projectionMorphism hW hπ J B b hd hJ hcover).hom.left.base ''
        P) := by
  refine OriginalAnalyticCover.isAnalyticSubset_of_openImmersion_cover J hJopen hcover _ ?_
  intro i
  refine (isAnalyticSubset_closedAnalytic_iff _).mpr ?_
  let L := EmbeddedIdealBlowupOriginalObject.localMorphism hW hπ J B b hd hJ hcover i
  let σ := EmbeddedIdealBlowupOriginalObject.projectionMorphism hW hπ J B b hd hJ hcover
  let q := (strictTransformMorphism (hπ i) (hW i)).hom.left.base
  have hsq : ∀ y, σ.hom.left.base (L.hom.left.base y) = (J i).hom.left.base (q y) := fun y =>
    congrArg (fun H => H.hom.left.base y)
      (EmbeddedIdealBlowupOriginalObject.localMorphism_projection hW hπ J B b hd hJ hcover i)
  have hsat : σ.hom.left.base ⁻¹' range (J i).hom.left.base ⊆ range L.hom.left.base :=
    (EmbeddedIdealBlowupObjectGluing.preimage_chart_range hW hπ J B b hd hJ i).subset
  have hPi : (EmbeddedIdealBlowupOverlap.localSpace hW hπ i).IsAnalyticSubset
      (L.hom.left.base ⁻¹' P) := hP.preimage L
  have hY : IsComplexAnalyticSubset (n := n i)
      (Subtype.val '' (L.hom.left.base ⁻¹' P) : Set (Y i)) :=
    isComplexAnalyticSubset_image_of_isAnalyticSubset_closedAnalytic hPi
  have hprop : ProperOn (π i) (Subtype.val '' (L.hom.left.base ⁻¹' P) : Set (Y i)) := fun K hK =>
    ((HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong (hπ i)).isCompact_preimage
      hK).inter_left hY.isClosed
  have himg := ProperMappingTheorem.isComplexAnalyticSubset_image (hπ i).contMDiff hY hprop
  convert himg using 1
  ext m
  constructor
  · rintro ⟨w, ⟨p, hpP, hpw⟩, rfl⟩
    obtain ⟨y, rfl⟩ := hsat ⟨w, hpw.symm⟩
    have hw : w = q y := (hJopen i).base_open.injective (hpw.symm.trans (hsq y))
    subst hw
    exact ⟨y.val, ⟨y, hpP, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hyP, rfl⟩, rfl⟩
    exact ⟨q y, ⟨L.hom.left.base y, hyP, hsq y⟩, rfl⟩

end General

/-! ### One admissible step -/

open Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine
  Hironaka.Analytic.Unibranch.HironakaG10ChowOneStepStrictTransform Hironaka.Analytic.Unibranch.HironakaG10RdPermRun
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata Hironaka.Analytic.Unibranch.HironakaG10SourceCSet
  Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus Hironaka.Analytic.Unibranch.HironakaG10MwStrataStep

/-- **L5.c.1: the blow-up projection of an admissible step maps analytic sets to analytic sets.** -/
theorem stepProperImage (s : Stage) (c : AdmissibleCentre s.f) : StepProperImage s c := by
  intro P hP
  let _ := c.finiteType
  change s.X.IsAnalyticSubset
    ((OriginalFiniteIdealBlowup.projectionMorphism c.B c.b c.dense).hom.left.base '' P)
  unfold OriginalFiniteIdealBlowup.projectionMorphism
  exact isAnalyticSubset_image_projection _ _ _ c.B c.b _ _ _ hP

variable (s : Stage) (c : AdmissibleCentre s.f)

/-- **L5 (c), forward**, for a proper family; only the analyticity of the centre remains as hypothesis. -/
theorem exists_isStratumComponent_of_next_proper (hf : IsProperMap s.f.hom.left.base)
    {B : Set s.X.obj.left} (hB : IsClosed B)
    (hDa : s.X.IsAnalyticSubset (nonunitLocus c.B c.b)) (j : ℕ)
    {C' : Set (nextWith s c).X.obj.left}
    (hC' : IsStratumComponent (nextWith s c).f (strictSet s c B) j C')
    (hCE : ¬ C' ⊆ σb s c ⁻¹' nonunitLocus c.B c.b) :
    ∃ C, IsStratumComponent s.f B j C ∧ ¬ C ⊆ nonunitLocus c.B c.b ∧ C' = strictSet s c C :=
  exists_isStratumComponent_of_next_of_proper s c hf hB hDa (stepProperImage s c) j hC' hCE

/-- **L5 (c), converse**, for a proper family; only the analyticity of the centre remains as hypothesis. -/
theorem isStratumComponent_strictSet_proper (hf : IsProperMap s.f.hom.left.base)
    {B : Set s.X.obj.left} (hB : IsClosed B)
    (hDa : s.X.IsAnalyticSubset (nonunitLocus c.B c.b)) (j : ℕ)
    {C : Set s.X.obj.left} (hC : IsStratumComponent s.f B j C)
    (hCD : ¬ C ⊆ nonunitLocus c.B c.b) :
    IsStratumComponent (nextWith s c).f (strictSet s c B) j (strictSet s c C) ∧
      ¬ strictSet s c C ⊆ σb s c ⁻¹' nonunitLocus c.B c.b :=
  isStratumComponent_strictSet_of_proper s c hf hB hDa (stepProperImage s c) j hC hCD

/-- The strict transform of an irreducible analytic set not inside the centre is irreducible. -/
theorem isIrreducible_strictSet' (hDa : s.X.IsAnalyticSubset (nonunitLocus c.B c.b))
    {C : Set s.X.obj.left} (hC : s.X.IsIrreducibleAnalyticSubset C)
    (hCD : ¬ C ⊆ nonunitLocus c.B c.b) :
    (nextWith s c).X.IsIrreducibleAnalyticSubset (strictSet s c C) :=
  isIrreducible_strictSet s c hDa (stepProperImage s c) hC hCD

end

end Hironaka.Analytic.Unibranch.HironakaG10MwStepProperImage
