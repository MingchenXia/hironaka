import Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupOriginalPivotObjects

/-! Actual strict restriction of the SAME allambient monomial map.
Complete approved blueprint FIRST. Ordinary643 ONCE,699 model helper SAME E.
Strict landing is DERIVED from actual canonical square/ranges. No raw-pair
source point, landing/comparison certificate, B or future C2 assumption.
Full ambient maps, genuine scalar laws and ENTIRE original stalk numerators.
C2/.7/Qsat/nonreduced raw-fibre remain separate. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialStrictRestriction
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka BlowupConstruction BlowupFlatCoordinates BlowupStrictSubmanifold
  HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaReducedComplexAnalyticSpaces
  HironakaSmoothCentreRealDomainActualSheafStalk
  SourceReducedComplexSpace EmbeddedGeometricBlowup OriginalFiniteIdealGraphChart
  CompatibleCanonicalIdealBlowupSquareCharts CompatibleCanonicalIdealBlowupNormalSections
  CompatibleCanonicalIdealBlowupExplicitProductCharts CompatibleCanonicalIdealBlowupMonomialLift
  CompatibleCanonicalIdealBlowupPivotOpenRanges CompatibleCanonicalIdealBlowupPivotOpenRestrictions
  CompatibleCanonicalIdealBlowupOriginalPivotObjects
open scoped ProductComplexManifold

theorem strict_chart_ambient_open_eq {n r : ℕ} {P : Type}
    [TopologicalSpace P] [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]
    (a : ProductNormalCharts n r P) (j : Fin r) :
    strictChartAmbientOpen a j = productChartOpen a j := by rfl

noncomputable section
section WholeNativeOutput
variable {n m : ℕ} {S T : Type} [TopologicalSpace S] [TopologicalSpace T]
  [ChartedSpace (ComplexModel n) S] [IsComplexManifold n S]
  [ChartedSpace (ComplexModel m) T] [IsComplexManifold m T]

/-- Nominal OUTPUT only: EXACT original EVERY-point/EVERY-ambient-numerator
whole quotient equation. The ordinary caller constructs it internally. -/
structure WholeNativeStalkLaws (f : S → T)
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (C : Set S) (D : Set T) (hCD : ∀ x ∈ C, f x ∈ D) : Prop where
  equation : ∀ (z : C)
    (r : actualComplexStructureStalk (n := m) (f z.val)),
    actualSubspaceStalkWholeEquiv (n := n) C z
      ((actualSubspaceMap hf hCD).stalkMap z
        ((actualSubspaceInclusion (n := m) D).stalkMap
          (actualSubspaceMapTop hf hCD z) r)) =
      Ideal.Quotient.mk (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) z.val)
        ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap z.val r)

private theorem constructedWholeNativeStalkLaws (f : S → T)
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (C : Set S) (D : Set T) (hCD : ∀ x ∈ C, f x ∈ D) :
    WholeNativeStalkLaws f hf C D hCD := by
  constructor
  intro z r
  exact actualSubspaceMap_stalk (n := n) (m := m) (M := S) (N := T)
    (f := f) (C := C) (D := D) hf hCD z r
end WholeNativeOutput

section SameCanonical
variable {X Y : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  [B.IsFiniteType] (F : X ⟶ Y) (x : X.obj.left)
  {y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left}
local instance : (nativePulledIdealModule F.hom.left B b).IsFiniteType :=
  HironakaNativePulledIdealFiniteType.nativePulledIdealModule_isFiniteType F.hom.left B b
variable (t : CanonicalTargetGraph B b y)
  (c : CanonicalCompatibleSourceGraph B b F x t)
  (g : CanonicalSquareGeometry B b F x t c)
  (d : CanonicalNormalSectionData B b F x t c g)
  (E : SameCanonicalExplicitProductModels B b F x t c g d)

abbrev targetStrictSet (j : Fin t.rank) : Set (productChartOpen E.target.charts j) :=
  strictChartCarrier E.target.charts (targetGraphSet B b t) j

abbrev sourceStrictSet (j : Fin t.rank) : Set (productChartOpen E.source.charts j) :=
  strictChartCarrier E.source.charts (sourceGraphSet B b F x t c) j

def targetChartAmbientInclusion (j : Fin t.rank) :
    actualSubspaceLocallyRingedSpace (n := t.embedding.dim+t.rank)
        (targetStrictSet B b F x t c g d E j) ⟶
      ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel (t.embedding.dim+t.rank))
        (productChartOpen E.target.charts j) :=
  actualSubspaceInclusion (n := t.embedding.dim+t.rank) (targetStrictSet B b F x t c g d E j)

def sourceChartAmbientInclusion (j : Fin t.rank) :
    actualSubspaceLocallyRingedSpace (n := c.embedding.dim+t.rank)
        (sourceStrictSet B b F x t c g d E j) ⟶
      ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel (c.embedding.dim+t.rank))
        (productChartOpen E.source.charts j) :=
  actualSubspaceInclusion (n := c.embedding.dim+t.rank) (sourceStrictSet B b F x t c g d E j)

abbrev monomialAmbientFunction (j : Fin t.rank) :=
  monomialLiftOnChart E.source.charts E.target.charts c.holomorphic
    (explicitAmbientLift B b F x t c g E.target E.source)
    E.square.holomorphic E.square.ambient_projection j

abbrev nativeMonomialAmbientMap (j : Fin t.rank) :=
  nativeMonomialLiftOnChart E.source.charts E.target.charts c.holomorphic
    (explicitAmbientLift B b F x t c g E.target E.source)
    E.square.holomorphic E.square.ambient_projection j

-- GENUINE new strict landing theorem; M has only held ALLambient laws.
-- No source point is selected from the raw pair. Every z is an existing
-- ambient chart point with the explicit actual strict-membership hypothesis.
theorem monomial_strict_landing
    (M : AllAmbientMonomialLiftData B b F x t c g d E) (j : Fin t.rank) :
    ∀ z ∈ sourceStrictSet B b F x t c g d E j,
      monomialAmbientFunction B b F x t c g d E j z ∈ targetStrictSet B b F x t c g d E j := by
  obtain ⟨P⟩ := pivot_open_ranges_of_models B b F x t c g d E
  intro z hz
  let zS : strictChartCarrier E.source.charts (sourceGraphSet B b F x t c) j := ⟨z,hz⟩
  let pS : (explicitSource B b F x t c).obj.left :=
    (strictChartInclusion E.source.charts (sourceGraphSet B b F x t c) j).base zS
  let KX := (sourceCanonicalMap B b F x t c g E.source).hom.left
  let KY := (targetCanonicalMap B b t E.target).hom.left
  let H := (explicitStrictMap B b F x t c g E.target E.source).hom.left
  let qX := KX.base pS
  have hqX : qX ∈ (sourcePivotOpen B b F x t c g d E j).1 := by
    rw [← P.chart_ranges.source_range j]
    exact ⟨zS,rfl⟩
  rw [P.source_preimage j] at hqX
  have hqY := hqX.2
  rw [← P.chart_ranges.target_range j] at hqY
  obtain ⟨w,hw⟩ := hqY
  let pY : (explicitTarget B b t).obj.left :=
    (strictChartInclusion E.target.charts (targetGraphSet B b t) j).base w
  have hcan :
      (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base qX =
        KY.base (H.base pS) :=
    congrArg (fun k => k.hom.left.base pS) E.square.canonical_square
  have hw' : KY.base pY =
      (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base qX := hw
  have hp : H.base pS = pY :=
    E.target_maps.open_immersion.base_open.injective (hcan.symm.trans hw'.symm)
  have hamb : (H.base pS).val =
      explicitAmbientLift B b F x t c g E.target E.source z.val :=
    congrArg (fun k => k.base pS) E.square.ambient_inclusion
  have hL : explicitAmbientLift B b F x t c g E.target E.source z.val = w.val.val := by
    rw [hp] at hamb
    exact hamb.symm
  have hchart : (monomialAmbientFunction B b F x t c g d E j z).val =
      explicitAmbientLift B b F x t c g E.target E.source z.val :=
    congrArg (fun k => k.base z) (M.inclusion_square j)
  have heq : monomialAmbientFunction B b F x t c g d E j z = w.val :=
    Subtype.ext (hchart.trans hL)
  exact heq.symm ▸ w.property

def actualMonomialStrictMap
    (M : AllAmbientMonomialLiftData B b F x t c g d E) (j : Fin t.rank) :
    actualSubspaceLocallyRingedSpace (n := c.embedding.dim+t.rank)
        (sourceStrictSet B b F x t c g d E j) ⟶
      actualSubspaceLocallyRingedSpace (n := t.embedding.dim+t.rank)
        (targetStrictSet B b F x t c g d E j) :=
  actualSubspaceMap (M.restricted_holomorphic j)
    (monomial_strict_landing B b F x t c g d E M j)

def actualOriginalMonomialStrictMap
    (M : AllAmbientMonomialLiftData B b F x t c g d E) (j : Fin t.rank) :
    sourceStrictOriginal B b F x t c g d E j ⟶ targetStrictOriginal B b F x t c g d E j :=
  ObjectProperty.homMk (Over.homMk
    (actualMonomialStrictMap B b F x t c g d E M j)
    (actualSubspaceMap_point (M.restricted_holomorphic j)
      (monomial_strict_landing B b F x t c g d E M j)))


-- Full actual factory square/scalars; no incoming landing certificate.
theorem monomial_strict_full_ambient
    (M : AllAmbientMonomialLiftData B b F x t c g d E) (j : Fin t.rank) :
    (actualOriginalMonomialStrictMap B b F x t c g d E M j).hom.left ≫
        targetChartAmbientInclusion B b F x t c g d E j =
      sourceChartAmbientInclusion B b F x t c g d E j ≫
        nativeMonomialAmbientMap B b F x t c g d E j := by
  exact (actualSubspaceMap_inclusion (M.restricted_holomorphic j)
    (monomial_strict_landing B b F x t c g d E M j)).symm

theorem monomial_strict_point
    (M : AllAmbientMonomialLiftData B b F x t c g d E) (j : Fin t.rank) :
    (actualOriginalMonomialStrictMap B b F x t c g d E M j).hom.left ≫
        (targetStrictOriginal B b F x t c g d E j).obj.hom =
      (sourceStrictOriginal B b F x t c g d E j).obj.hom := by
  exact actualSubspaceMap_point (M.restricted_holomorphic j)
    (monomial_strict_landing B b F x t c g d E M j)

theorem monomial_strict_ambient_point
    (M : AllAmbientMonomialLiftData B b F x t c g d E) (j : Fin t.rank) :
    nativeMonomialAmbientMap B b F x t c g d E j ≫
        ambientPointMap (t.embedding.dim+t.rank) (productChartOpen E.target.charts j) =
      ambientPointMap (c.embedding.dim+t.rank) (productChartOpen E.source.charts j) := by
  exact M.restricted_scalar j

theorem monomial_strict_whole_stalk_mk
    (M : AllAmbientMonomialLiftData B b F x t c g d E) (j : Fin t.rank) :
    WholeNativeStalkLaws
      (n := c.embedding.dim+t.rank) (m := t.embedding.dim+t.rank)
      (S := productChartOpen E.source.charts j) (T := productChartOpen E.target.charts j)
      (monomialAmbientFunction B b F x t c g d E j) (M.restricted_holomorphic j)
      (sourceStrictSet B b F x t c g d E j) (targetStrictSet B b F x t c g d E j)
      (monomial_strict_landing B b F x t c g d E M j) := by
  exact constructedWholeNativeStalkLaws
    (n := c.embedding.dim+t.rank) (m := t.embedding.dim+t.rank)
    (S := productChartOpen E.source.charts j) (T := productChartOpen E.target.charts j)
    (monomialAmbientFunction B b F x t c g d E j) (M.restricted_holomorphic j)
    (sourceStrictSet B b F x t c g d E j) (targetStrictSet B b F x t c g d E j)
    (monomial_strict_landing B b F x t c g d E M j)

-- A Prop of laws about the EXPLICIT ACTUAL original map factory, never a Prop
-- hiding Type data. The map factory itself has genuine original morphism type.
structure MonomialStrictRestrictionLaws
    (M : AllAmbientMonomialLiftData B b F x t c g d E) : Prop where
  landing : ∀ (j : Fin t.rank) (z : productChartOpen E.source.charts j),
    z ∈ sourceStrictSet B b F x t c g d E j →
      monomialAmbientFunction B b F x t c g d E j z ∈ targetStrictSet B b F x t c g d E j
  full_ambient : ∀ j : Fin t.rank,
    (actualOriginalMonomialStrictMap B b F x t c g d E M j).hom.left ≫
        targetChartAmbientInclusion B b F x t c g d E j =
      sourceChartAmbientInclusion B b F x t c g d E j ≫
        nativeMonomialAmbientMap B b F x t c g d E j
  genuine_scalar : ∀ j : Fin t.rank,
    (actualOriginalMonomialStrictMap B b F x t c g d E M j).hom.left ≫
        (targetStrictOriginal B b F x t c g d E j).obj.hom =
      (sourceStrictOriginal B b F x t c g d E j).obj.hom
  genuine_ambient_scalar : ∀ j : Fin t.rank,
    nativeMonomialAmbientMap B b F x t c g d E j ≫
        ambientPointMap (t.embedding.dim+t.rank) (productChartOpen E.target.charts j) =
      ambientPointMap (c.embedding.dim+t.rank) (productChartOpen E.source.charts j)
  whole_stalk_mk : ∀ j : Fin t.rank,
    WholeNativeStalkLaws
      (n := c.embedding.dim+t.rank) (m := t.embedding.dim+t.rank)
      (S := productChartOpen E.source.charts j) (T := productChartOpen E.target.charts j)
      (monomialAmbientFunction B b F x t c g d E j) (M.restricted_holomorphic j)
      (sourceStrictSet B b F x t c g d E j) (targetStrictSet B b F x t c g d E j)
      (monomial_strict_landing B b F x t c g d E M j)

theorem monomial_strict_restriction_of_models
    (M : AllAmbientMonomialLiftData B b F x t c g d E) :
    MonomialStrictRestrictionLaws B b F x t c g d E M := by
  exact {
    landing := monomial_strict_landing B b F x t c g d E M
    full_ambient := monomial_strict_full_ambient B b F x t c g d E M
    genuine_scalar := monomial_strict_point B b F x t c g d E M
    genuine_ambient_scalar := monomial_strict_ambient_point B b F x t c g d E M
    whole_stalk_mk := monomial_strict_whole_stalk_mk B b F x t c g d E M }
end SameCanonical

section OrdinaryCaller
variable {X Y : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  [B.IsFiniteType] (F : X ⟶ Y) (x : X.obj.left)
local instance : (nativePulledIdealModule F.hom.left B b).IsFiniteType :=
  HironakaNativePulledIdealFiniteType.nativePulledIdealModule_isFiniteType F.hom.left B b

theorem exists_same_canonical_monomial_strict_restriction
    (y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left)
    (hxy : F.hom.left.base x =
      (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base y) :
    ∃ (t : CanonicalTargetGraph B b y)
      (c : CanonicalCompatibleSourceGraph B b F x t)
      (g : CanonicalSquareGeometry B b F x t c)
      (d : CanonicalNormalSectionData B b F x t c g)
      (E : SameCanonicalExplicitProductModels B b F x t c g d)
      (M : AllAmbientMonomialLiftData B b F x t c g d E),
      MonomialStrictRestrictionLaws B b F x t c g d E M := by
  obtain ⟨t,c,g,d,E,⟨M⟩⟩ := exists_same_canonical_allambient_monomial_lift B b F x y hxy
  exact ⟨t,c,g,d,E,M,monomial_strict_restriction_of_models B b F x t c g d E M⟩
end OrdinaryCaller
end
end Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialStrictRestriction
