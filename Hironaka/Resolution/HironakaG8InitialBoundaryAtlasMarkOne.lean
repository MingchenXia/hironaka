import Hironaka.Resolution.HironakaG8NoncompactInitialBoundaryMembers
import Hironaka.Resolution.HironakaCurrentStrictTransformIdeal
import Hironaka.Resolution.HironakaSharpActualCurveBirthBoundaryOverlaps

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8InitialBoundaryAtlasMarkOne

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings RestrictEmptyTower
  HironakaEmbeddedAnalytic HironakaStageCenters HironakaG8NoncompactInitialBoundaryAtlas
  HironakaG3RTowerClass HironakaG3RPureEmbedded AnalyticSubsetOpens
  HironakaActualSmoothBoundaryCleanup HironakaG8DenseBoundaryRestart HironakaG8UniverseBMTransport
  HomogenizedGlueingTower HironakaEmbeddedBoundary NormalCrossingsInvariance
  HironakaMixedDimensionalBoundaryFiniteResolution HironakaAdmissibleSequence
  HironakaCoherentTransformExtension HironakaSharpActualFiniteChronologicalHistory
  HironakaAdmissibleCalculus HironakaG4SharpTerminalAtlas HironakaG8LocalPureFinish
  HironakaNormalCrossingsOpenRestrictionSeparation HironakaG8UniverseDenseBoundary
  HironakaSharpActualCurveBirthBoundaryOverlaps HironakaG8LocalMixedPhaseAssembly

/-- On the literal mixed history, the full original mark-one record is
testable and the iterated strict transform equals the library strict carrier.
The same conclusion applies to each prefix with its inherited stage data. -/
theorem original_markOne_of_bm_positions {n : ℕ} {X Y : CMfd.{0} n}
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W) {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (T : BlowupTower X Y) (hStages : BMStages W E T)
    (hOver : CentresOver (singularSet (n := n) W ∪ (W ∩ ⋃ H ∈ E, H)) T) :
    IsGeoTestTower (actualSmoothBoundaryMarked W E) T ∧
      strictAlong T W = strictTransform n T.proj W := by
  let F := singularSet (n := n) W ∪ (W ∩ ⋃ H ∈ E, H)
  have hClosedE := isClosed_biUnion_of_forall_isClosed hE.1
  let O : Opens X := ⟨Fᶜ, ((isClosed_singularSet hW.isClosed).union
    (hW.isClosed.inter hClosedE)).isOpen_compl⟩
  have hGood : W ⊆ closure (W ∩ (O : Set X)) := by
    have h := dense_off_original_boundary_and_singular hW hClosedE hDense
    change W ⊆ closure (W ∩ Fᶜ)
    rw [← sdiff_eq]
    exact h.trans (closure_mono (sdiff_subset_sdiff_right
      (fun _ hx => hx.elim Or.inr (fun hb => Or.inl hb.2))))
  have hWF : (actualSmoothBoundaryMarked W E).IsWellFormed :=
    ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ, CartanIrreducible.cartanCoherence W hW,
      hE, SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  refine ⟨?_, strictAlong_eq_library_of_avoid W hW.isClosed O hGood T
    (centresAvoid_of_centresOver _ disjoint_compl_left T hOver)⟩
  induction T with
  | refl => trivial
  | step R C π hπ ih =>
      have hR := ih hStages.1 hOver.1
      have hAvoid : CentresAvoid O R := centresAvoid_of_centresOver _ disjoint_compl_left R hOver.1
      have hCos := HironakaCurrentStrictTransformIdeal.strictTransform_subset_cosupp_of_centresAvoid_wellFormed
        hW.isClosed hWF O hGood R hR hAvoid
      have hPos := hStages.2
      have hCarrier : C ⊆ strictTransform n R.proj W := fun x hx =>
        hPos.1.elim (fun hs => singularSet_subset _ (hs hx)) (fun hs => (hs.2 hx).1)
      have hEq : (geoTransformAlong (geometricTemplate univ E) R).E =
          (geoTransformAlong (actualSmoothBoundaryMarked W E) R).E :=
        geoTransformAlong_E_eq_of_E_eq (𝔍 := geometricTemplate univ E)
          (𝔪 := actualSmoothBoundaryMarked W E) rfl R
      exact ⟨hR, hπ.1, hCarrier.trans hCos, hEq ▸ hPos.2⟩

/-- Literal readback of the original TEST, strict carrier, and ordered slots
in one actual chart of an ordered initial-boundary atlas. -/
def InitialBoundaryChartMarkOne {n : ℕ} {X Z : CMfd.{0} n}
    {W : Set X} {E : List (Set X)} {C : SmoothTailCertificate n} {P : Z → X}
    (c : TowerChart (initialBoundaryClass C W E) Z P) : Prop :=
    let M := MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : c.U → X)
      (actualSmoothBoundaryMarked W E)
    let W₀ := (Subtype.val : c.U → X) ⁻¹' W
    IsGeoTestTower M c.T ∧
      strictAlong c.T W₀ = (chartIncl c) ⁻¹' strictTransform n P W ∧
      (fullChartBoundary c E).map ((Subtype.val : c.V → Z) ⁻¹' ·) =
        (geoTransformAlong M c.T).E.map (c.φ.symm ⁻¹' ·) ∧
      (∀ k, (Subtype.val : c.V → Z) ⁻¹' boundaryReadout (fullChartBoundary c E) k =
        c.φ.symm ⁻¹' boundaryReadout (geoTransformAlong M c.T).E k)

/-- The actual chart reads the original pulled-back mark-one record, the
physical strict carrier, and the complete ordered boundary at raw positions. -/
theorem initial_boundary_chart_original_markOne {n : ℕ} {X Z : CMfd.{0} n}
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W) {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    {C : SmoothTailCertificate n} {P : Z → X}
    (A : IsGluedFrom (initialBoundaryClass C W E) Z P)
    (c : TowerChart (initialBoundaryClass C W E) Z P) :
    InitialBoundaryChartMarkOne c := by
  dsimp only [InitialBoundaryChartMarkOne]
  let W₀ := (Subtype.val : c.U → X) ⁻¹' W
  let E₀ := E.map ((Subtype.val : c.U → X) ⁻¹' ·)
  let M := actualSmoothBoundaryMarked W E
  let G := geometricTemplate (univ : Set X) E
  let M₀ := actualSmoothBoundaryMarked (X := CMfd.of (n := n) c.U) W₀ E₀
  have hM : MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : c.U → X) M = M₀ :=
    HironakaEmbeddedBoundary.pullback_val_mk_vanishingIdeal c.U E W
  have hSNC := isSNCDivisor_map_preimage (pullsBackCoordinates_val c.U) continuous_subtype_val hE
  have hOver : CentresOver (singularSet (n := n) W₀ ∪ (W₀ ∩ ⋃ H ∈ E₀, H)) c.T := by
    apply centresOver_of_exceptionalDivisor_support_subset _ c.T
    rw [HironakaPrincipalizationBoundary.support_exceptionalDivisor_eq_biUnion_drop M₀ hSNC.1 c.T]
    exact (IsAdmissibleBlowupSequence.exceptionalLocus_subset_drop c.mem.geometry.1).2
  have hTest := original_markOne_of_bm_positions (isComplexAnalyticSubset_preimage_val hW c.U)
    hSNC (dense_complement_restrict W E hDense c.U) c.T c.mem.geometry.2.1 hOver
  have hList : (fullChartBoundary c E).map ((Subtype.val : c.V → Z) ⁻¹' ·) =
        (geoTransformAlong (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : c.U → X) M)
          c.T).E.map (c.φ.symm ⁻¹' ·) := by
    have h := chartBoundary_map_val c G
    have hEq : (geoTransformAlong (MarkedIdealBiholomorphism.MarkedIdeal.pullback
          (Subtype.val : c.U → X) G) c.T).E =
        (geoTransformAlong (MarkedIdealBiholomorphism.MarkedIdeal.pullback
          (Subtype.val : c.U → X) M) c.T).E :=
      geoTransformAlong_E_eq_of_E_eq
        (𝔍 := MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : c.U → X) G)
        (𝔪 := MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : c.U → X) M) rfl c.T
    rw [hEq] at h
    exact h
  refine ⟨hM.symm ▸ hTest.1, hTest.2.trans (strictTransform_chart c A.1 W), hList, ?_⟩
  intro k
  rw [← boundaryReadout_map_preimage, hList, boundaryReadout_map_preimage]

open HironakaG8NoncompactInitialBoundaryMembers HironakaActualLocallyFiniteBoundary
  HironakaActualIndexedBoundaryContinuation HironakaG3REmbeddedGlobalSNC HironakaG3REmbeddedNC

/-- The actual canonical-by-phase finite charts on the glued ordered atlas
carry the original mark-one TEST and exact raw readback, alongside locally
finite global SNC members and the regular isomorphism of the same projection. -/
theorem exists_locally_finite_initial_boundary_original_markOne_atlas
    {m : ℕ} {X : CMfd.{0} (m+1)} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := m+1) W) {E : List (Set X)}
    (hE : IsSNCDivisor (m+1) E) (hDense : W ⊆ closure (W \ ⋃ B ∈ E, B)) :
    ∃ (Z : CMfd.{0} (m+1)) (P : Z → X),
      IsGluedFrom (orderedInitialBoundaryClass W E) Z P ∧
      (∀ (U : Opens X) (K : Set X), IsCompact K → (U : Set X) ⊆ K →
        ∃ c : TowerChart (orderedInitialBoundaryClass W E) Z P, c.U = U) ∧
      (∀ c : TowerChart (orderedInitialBoundaryClass W E) Z P, InitialBoundaryChartMarkOne c) ∧
      IsClosedSubmanifold (m+1) (strictTransform (m+1) P W) ∧
      IsIsomorphismOver (m+1) P (singularSet (n := m+1) W ∪ (W ∩ ⋃ B ∈ E, B))ᶜ ∧
      ∃ Ex : SNCExhaustion Z,
        (∀ k, ∃ c : TowerChart (orderedInitialBoundaryClass W E) Z P,
          Ex.W k = c.V ∧ Ex.B k = fullChartBoundary c E) ∧
        let B : {D : Set Z // Ex.IsGlobalMember D} → Set Z := Subtype.val
        IsLocallyFiniteSNCDivisor (m+1) B ∧ (∀ j, (B j).Nonempty) ∧
        HasNormalCrossingsWithBoundary (strictTransform (m+1) P W) B := by
  obtain ⟨Z, P, hGlue, hWindows, hSmooth, hIso, hMembers⟩ :=
    exists_locally_finite_initial_boundary_resolution hW hE hDense
  exact ⟨Z, P, hGlue, hWindows, initial_boundary_chart_original_markOne hW hE hDense hGlue,
    hSmooth, hIso, hMembers⟩

end
end Hironaka.HironakaG8InitialBoundaryAtlasMarkOne
