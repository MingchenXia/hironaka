import Hironaka.Resolution.HironakaG8CountableArrangementNoClock
import Hironaka.Resolution.HironakaG8SurfaceLimitEndpoint

/-! # An independent physical chronology for the countable arrangement -/
set_option autoImplicit false
open Set
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8ArrangementPhysicalChronology

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaEmbeddedAnalytic HironakaStageCenters HironakaLocallyFiniteResolutionSequence
  HironakaActualLocallyFiniteHistoryLimit HironakaActualLocallyFiniteLimitStrictTransforms
  HironakaActualLocallyFiniteHistoryOverlap ResolutionInvariantSeq
  HironakaG8CountablePlaneSheets HironakaG8CountablePlaneArrangement
  HironakaG8SurfaceLimitEndpoint NormalCrossings

attribute [local instance] limitChartedSpace
local instance (s : GrowingSeq sheetManifold) (hLF : LocallyFinite (centreImage s)) :
    IsComplexManifold 2 (actualHistoryGluedSpace s hLF) := limitSpace_isComplexManifold s hLF

local notation "A" => countablePlaneArrangement
private noncomputable abbrev original : MarkedIdeal 2 sheetManifold :=
  ⟨univ,[],vanishingIdeal (n := 2) A,1⟩

/-- The same analytic set admits its own physical singular-centred TEST
chronology, independently of the simultaneous ordering of the certified
Hilbert–Samuel charts. -/
theorem countableArrangement_finite_or_proper_limit :
    (∃ (Y : CMfd.{0} 2) (T : BlowupTower sheetManifold Y),
      StageCentres (fun P C => C ⊆ singularSet (n := 2) (strictTransform 2 P.proj A)) T ∧
      IsGeoTestTower original T ∧
      IsClosedSubmanifold 2 (strictTransform 2 T.proj A) ∧
      IsIsomorphismOver 2 T.proj (singularSet (n := 2) A)ᶜ) ∨
    ∃ (s : GrowingSeq sheetManifold) (hLF : LocallyFinite (centreImage s)),
      (∀ i, IsGeoTestTower original (s.stage i).2) ∧
      (∀ i, StageCentres
        (fun P C => C ⊆ singularSet (n := 2) (strictTransform 2 P.proj A)) (s.stage i).2) ∧
      IsClosedSubmanifold 2 (limitStrictTransform s hLF A) ∧
      limitStrictTransform s hLF A = strictTransform 2 (gluedProjection s hLF) A ∧
      IsProperMap (gluedProjection s hLF) ∧
      IsIsomorphismOver 2 (gluedProjection s hLF) (singularSet (n := 2) A)ᶜ ∧
      ContMDiff 𝓘(ℂ,ComplexModel 2) 𝓘(ℂ,ComplexModel 2) ∞ (gluedProjection s hLF) :=
  surface_singular_resolution_finite_or_proper_limit (X := sheetManifold)
    A isComplexAnalyticSubset_countablePlaneArrangement [] isSNCDivisor_nil

end Hironaka.HironakaG8ArrangementPhysicalChronology
