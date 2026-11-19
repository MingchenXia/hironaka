import Hironaka.Resolution.HironakaG4WindowSharpSchedule

/-! Terminal and stable-window consequences for a compact-window sharp schedule. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4WindowSharpEndpoint
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower
  MemberInterTowerAlong MemberInterLocusAlong BlowupTowerIsomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings RestrictEmptyTower
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpNormalCrossingsOpenLocus
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaG4CompactWholeMonomialMaskPhase
  HironakaG4WindowServiceBlocks HironakaG4WindowSharpSchedule HironakaG4SharpCountStability
  HironakaG4SharpBadFootprint HironakaLocallyFiniteResolutionSequence ResolutionInvariantSeq
  HironakaG4RecordedTowerResidualCompatibility HironakaActualGeometricCleanupComposition
variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- Normal crossings over a base set persist through any subsequent sharp tail. -/
theorem good_persists_sharp {W : Set X} {E : List (Set X)}
    (hW : IsClosed W) (hE : ∀ H ∈ E, IsClosed H)
    (T : BlowupTower X Y) (S : BlowupTower Y Z) (hSharp : CurrentSharpCentres W E (T.append S))
    (L : Set X) (hGood : ∀ z ∈ strictAlong T W, T.proj z ∈ L →
      normalCrossingsAt (n := n) (strictAlong T W)
        (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E z) :
    ∀ z ∈ strictAlong (T.append S) W, (T.append S).proj z ∈ L →
      normalCrossingsAt (n := n) (strictAlong (T.append S) W)
        (geoTransformAlong (geometricTemplate (univ : Set X) E) (T.append S)).E z := by
  let N := strictAlong T W
  let F := (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E
  have hN : IsClosed N := isClosed_strictAlong T hW
  have hF : ∀ H ∈ F, IsClosed H :=
    HironakaPrincipalization.isClosed_of_mem_E_geoTransformAlong
      (geometricTemplate (univ : Set X) E) hE T
  have hSharpS := sharp_tail_of_append W E T S hSharp
  obtain ⟨hFoot,_⟩ := currentSharpCentres_original_footprint hN hF S hSharpS
  intro z hz hzL
  rw [strictAlong_append] at hz
  rw [strictAlong_append,geoTransformAlong_append,
    template_current (univ : Set X) E T,strict_univ T]
  rw [BlowupTower.proj_append] at hzL
  by_contra hnc
  obtain ⟨hzN,hbad⟩ := hFoot ⟨hz,hnc⟩
  exact hbad (hGood (S.proj z) hzN hzL)

section FullBoundary

variable {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
  (hLocal : ∀ x ∈ originalSharpBadLocus (n := n) W E, ∃ V : Opens X,
    x ∈ V ∧ IsCompact (originalSharpBadLocus (n := n) W E ∩ V))
  (K : CompactExhaustion X)

/-- If the selected finite blocks become stationary, their last actual tower
is a full sharp cleanup, with its proper projection and good-locus isomorphism. -/
theorem stationary_full_boundary_blocks_terminal (a : ℕ)
    (hstat : ∀ b, a ≤ b → fullBoundaryBlocks hW hE hLocal K b =
      fullBoundaryBlocks hW hE hLocal K a) :
    let T := (fullBoundaryBlocks hW hE hLocal K a).2
    let A := geoTransformAlong (geometricTemplate W []) T
    let F := (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E
    IsGeoTestTower (geometricTemplate W []) T ∧
    IsGeoTestTower (geometricTemplate (univ : Set X) E) T ∧
    CurrentSharpCentres W E T ∧ CentresOver (originalSharpBadLocus (n := n) W E) T ∧
    IsClosedSubmanifold n A.N ∧ IsSNCDivisor n F ∧ HasNormalCrossings n A.N F ∧
    IsProperMap T.proj ∧ IsIsomorphismOver n T.proj (originalSharpBadLocus (n := n) W E)ᶜ := by
  dsimp only
  let B := fullBoundaryBlocks hW hE hLocal K
  let T := (B a).2
  have hT : IsGeoTestTower (geometricTemplate W []) T := (fullBoundaryStates hW hE hLocal K a).test
  have hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T :=
    (fullBoundaryStates hW hE hLocal K a).full
  have hSharp : CurrentSharpCentres W E T := (fullBoundaryStates hW hE hLocal K a).sharp
  obtain ⟨_,hOver⟩ := currentSharpCentres_original_footprint hW.1 hE.1 T hSharp
  have hWTemplate : (geometricTemplate W []).IsWellFormed :=
    ⟨hW, IdealWeightPowers.isCoherent_unitIdeal, isSNCDivisor_nil,
      isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hETemplate : (geometricTemplate (univ : Set X) E).IsWellFormed :=
    ⟨isClosedSubmanifold_univ, IdealWeightPowers.isCoherent_unitIdeal, hE,
      SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  have hNsm :=
    (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hWTemplate T hT).isClosedSubmanifold_N
  have hSNC :=
    (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hETemplate T hFull).isSNCDivisor
  have hNC : HasNormalCrossings n (strictAlong T W)
      (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E := by
    intro z hz
    obtain ⟨j,hj⟩ := K.exists_mem (T.proj z)
    let b := max a (j+1)
    have hGood := (fullBoundaryStates hW hE hLocal K b).good j
      (lt_of_lt_of_le (Nat.lt_succ_self j) (le_max_right a (j+1)))
    change ∀ z ∈ strictAlong (B b).2 W, (B b).2.proj z ∈ K j →
      normalCrossingsAt (n := n) (strictAlong (B b).2 W)
        (geoTransformAlong (geometricTemplate (univ : Set X) E) (B b).2).E z at hGood
    have hstat' : B b = B a := hstat b (le_max_left a (j+1))
    rw [hstat'] at hGood
    exact hGood z hz hj
  refine ⟨hT,hFull,hSharp,hOver,hNsm,hSNC,?_,HironakaLocalPrincipalization.isProperMap_proj T,
    HironakaSharpOriginalDynamicGoodPrefixes.isIsomorphismOver_proj_of_centresOver _ T hOver⟩
  rw [N_geoTransformAlong]
  exact hNC
/-- The very same growing history is eventually normal crossings on an
open neighborhood of every compact base set. -/
theorem growing_full_boundary_eventually_nc_on_compacts (s : GrowingSeq X)
    (hBoundary : ∀ j, s.stage (fullBoundaryBlocks hW hE hLocal K j).2.length =
      fullBoundaryBlocks hW hE hLocal K j)
    (hSharp : ∀ i, CurrentSharpCentres W E (s.stage i).2) :
    ∀ L : Set X, IsCompact L → ∃ (U : Opens X) (N : ℕ), L ⊆ U ∧
      ∀ i, N ≤ i → ∀ z ∈ strictAlong (s.stage i).2 W, (s.stage i).2.proj z ∈ U →
        normalCrossingsAt (n := n) (strictAlong (s.stage i).2 W)
          (geoTransformAlong (geometricTemplate (univ : Set X) E) (s.stage i).2).E z := by
  intro L hL
  obtain ⟨a,ha⟩ := K.exists_superset_of_isCompact hL
  let j := a+1
  let N := (fullBoundaryBlocks hW hE hLocal K (j+1)).2.length
  let U : Opens X := ⟨interior (K j),isOpen_interior⟩
  have hLU : L ⊆ U := ha.trans (K.subset_interior_succ a)
  have hGoodN : ∀ z ∈ strictAlong (s.stage N).2 W, (s.stage N).2.proj z ∈ K j →
      normalCrossingsAt (n := n) (strictAlong (s.stage N).2 W)
        (geoTransformAlong (geometricTemplate (univ : Set X) E) (s.stage N).2).E z := by
    dsimp only [N]
    rw [hBoundary (j+1)]
    exact (fullBoundaryStates hW hE hLocal K (j+1)).good j (Nat.lt_succ_self j)
  refine ⟨U,N,hLU,?_⟩
  intro i hi
  obtain ⟨r,rfl⟩ : ∃ r, i = N+r := ⟨i-N,by omega⟩
  have hSharpAppend : CurrentSharpCentres W E ((s.stage N).2.append (tailTower s N r)) := by
    rw [append_tailTower]
    exact hSharp (N+r)
  have hGood := good_persists_sharp hW.1 hE.1 (s.stage N).2 (tailTower s N r)
    hSharpAppend (K j) hGoodN
  rw [append_tailTower] at hGood
  intro z hz hzU
  exact hGood z hz (interior_subset hzU)

include hW hE in
/-- Every finite stage has its actual centre footprint, proper projection,
and isomorphism over the original good locus. -/
theorem growing_stage_good_projection (s : GrowingSeq X)
    (hSharp : ∀ i, CurrentSharpCentres W E (s.stage i).2) :
    ∀ i, CentresOver (originalSharpBadLocus (n := n) W E) (s.stage i).2 ∧
      IsProperMap (s.stage i).2.proj ∧
      IsIsomorphismOver n (s.stage i).2.proj (originalSharpBadLocus (n := n) W E)ᶜ := by
  intro i
  obtain ⟨_,hOver⟩ := currentSharpCentres_original_footprint hW.1 hE.1 (s.stage i).2 (hSharp i)
  exact ⟨hOver,HironakaLocalPrincipalization.isProperMap_proj _,
    HironakaSharpOriginalDynamicGoodPrefixes.isIsomorphismOver_proj_of_centresOver _ _ hOver⟩


end FullBoundary

section Compatibility
variable (hn : 0 < n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
  (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
  (hLocal : ∀ x ∈ originalSharpBadLocus (n := n) W E, ∃ V : Opens X,
    x ∈ V ∧ IsCompact (originalSharpBadLocus (n := n) W E ∩ V))
  (K : CompactExhaustion X)

set_option linter.unusedVariables false in
theorem stationary_blocks_terminal (a : ℕ)
    (hstat : ∀ b, a ≤ b → blocks hn hW hE hdense hLocal K b =
      blocks hn hW hE hdense hLocal K a) :
    let T := (blocks hn hW hE hdense hLocal K a).2
    let A := geoTransformAlong (geometricTemplate W []) T
    let F := (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E
    IsGeoTestTower (geometricTemplate W []) T ∧
    IsGeoTestTower (geometricTemplate (univ : Set X) E) T ∧
    CurrentSharpCentres W E T ∧ CentresOver (originalSharpBadLocus (n := n) W E) T ∧
    IsClosedSubmanifold n A.N ∧ IsSNCDivisor n F ∧ HasNormalCrossings n A.N F ∧
    IsProperMap T.proj ∧ IsIsomorphismOver n T.proj (originalSharpBadLocus (n := n) W E)ᶜ :=
  stationary_full_boundary_blocks_terminal hW hE hLocal K a hstat

set_option linter.unusedVariables false in
theorem growing_eventually_nc_on_compacts (s : GrowingSeq X)
    (hBoundary : ∀ j, s.stage (blocks hn hW hE hdense hLocal K j).2.length =
      blocks hn hW hE hdense hLocal K j)
    (hSharp : ∀ i, CurrentSharpCentres W E (s.stage i).2) :
    ∀ L : Set X, IsCompact L → ∃ (U : Opens X) (N : ℕ), L ⊆ U ∧
      ∀ i, N ≤ i → ∀ z ∈ strictAlong (s.stage i).2 W, (s.stage i).2.proj z ∈ U →
        normalCrossingsAt (n := n) (strictAlong (s.stage i).2 W)
          (geoTransformAlong (geometricTemplate (univ : Set X) E) (s.stage i).2).E z :=
  growing_full_boundary_eventually_nc_on_compacts hW hE hLocal K s hBoundary hSharp

end Compatibility

end
end Hironaka.HironakaG4WindowSharpEndpoint
