import Hironaka.Resolution.HironakaG4DiscreteSharpEndpoint
import Hironaka.Resolution.HironakaActualLocallyFiniteCarrierTransverse
import Hironaka.Resolution.HironakaActualLimitProtectedOpen

/-! Original carrier, boundary and projection readback on the actual limit. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4DiscreteLimitReadback
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings SimultaneousNormalCrossings
  IdealWeightPowers RestrictEmptyTower HironakaSharpActualFiniteChronologicalHistory HironakaSharpNormalCrossingsOpenLocus
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaG4CompactWholeMonomialMaskPhase HironakaG4SharpBadFootprint
  ResolutionInvariantSeq HironakaLocallyFiniteResolutionSequence
  HironakaActualLocallyFiniteHistoryOverlap HironakaActualLocallyFiniteHistoryLimit
  HironakaActualLocallyFiniteBoundary HironakaActualLocallyFiniteCarrierTransverse
  HironakaActualLocallyFiniteLimitStrictTransforms HironakaActualLimitProtectedOpen
attribute [local instance] limitChartedSpace
variable {n : ℕ} {X : CMfd.{u} n}

/-- Every actual centre image of a sharp sequence lies in the original bad locus. -/
theorem centreImage_subset_original_bad {W : Set X} {E : List (Set X)}
    (hW : IsClosed W) (hE : ∀ H ∈ E, IsClosed H)
    (s : GrowingSeq X) (hSharp : ∀ i, CurrentSharpCentres W E (s.stage i).2) :
    ∀ i, centreImage s i ⊆ originalSharpBadLocus (n := n) W E := by
  intro i x hx
  obtain ⟨z,hzC,rfl⟩ := hx
  obtain ⟨π,hπ,hStep⟩ := exists_step_map s i
  have h := hSharp (i+1)
  rw [hStep] at h
  obtain ⟨hFoot,_⟩ := currentSharpCentres_original_footprint hW hE (s.stage i).2 h.1
  exact hFoot (h.2 hzC)

/-- The actual locally finite limit has the original smooth carrier, the
whole labelled SNC boundary and a proper holomorphic projection that is an
isomorphism off the original bad locus. Pairwise NC at the limit is a
separate remaining readback. -/
theorem growing_limit_partial_geometry {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (hT : ∀ i, IsGeoTestTower (geometricTemplate W []) (s.stage i).2)
    (hFull : ∀ i, IsGeoTestTower (geometricTemplate (univ : Set X) E) (s.stage i).2)
    (hSharp : ∀ i, CurrentSharpCentres W E (s.stage i).2) :
    IsClosedSubmanifold n (limitStrictTransform s hLF W) ∧
      IsLocallyFiniteSNCDivisor n (limitBoundaryMember (geometricTemplate (univ : Set X) E) s hLF) ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (gluedProjection s hLF : limitManifold s hLF → X) ∧
      IsProperMap (gluedProjection s hLF : limitManifold s hLF → X) ∧
      IsIsomorphismOver n (gluedProjection s hLF : limitManifold s hLF → X)
        (originalSharpBadLocus (n := n) W E)ᶜ := by
  let M := geometricTemplate W []
  let P := geometricTemplate (univ : Set X) E
  have hM : M.IsWellFormed :=
    ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hP : P.IsWellFormed :=
    ⟨isClosedSubmanifold_univ,isCoherent_unitIdeal,hE,isTransverse_univ_of_isSNCDivisor hE⟩
  refine ⟨?_,isLocallyFiniteSNCDivisor_limitBoundaryMember P hP s hLF hFull,
    gluedProjection_contMDiff s hLF,gluedProjection_isProperMap s hLF,?_⟩
  · exact isClosedSubmanifold_limitCarrier M hM s hLF hT
  · exact gluedProjection_isIsomorphismOver_compl_of_centreImages_subset s hLF _
      (centreImage_subset_original_bad hW.1 hE.1 s hSharp)
end
end Hironaka.HironakaG4DiscreteLimitReadback
