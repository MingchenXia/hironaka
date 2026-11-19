import Hironaka.Resolution.HironakaG8PrincipalNativeAtlas
import Hironaka.Resolution.HironakaG8OccupiedAtlasRestart

/-! Exact native atlas data on a retained physical relative successor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8PrincipalNativeAtlasSuccessor
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal
  NormalCrossings HironakaEmbeddedAnalytic HironakaHolomorphicJetChartInvariance
  ResolutionInvariantSpec CanonicalCentres HironakaG8NativeRelativeClearing
  HironakaG8NativeRelativeSuccessor HironakaG8NativeSimultaneousCentre HironakaG8NativeSimultaneousTransport
  HironakaActualOpenEmbeddingVanishingIdeal HironakaBaseChange HironakaG8OpenHoloEmbeddingComposition
  HironakaStageCenters HironakaG11PresLineState HironakaG8NativePhaseCertificate
  HironakaG8OccupiedAtlasRestart HironakaG11InvCommonMark MaxLocusLocal
  HironakaOriginalTerminalOverlapComparison HironakaG11InvBMClass
  HironakaG8LocalHistory HironakaG1OriginalInvariantClassFunctorial

variable {n : ℕ} {X Y : CMfd.{0} n} {I : Type}
  {W D : Set X} {E : List (Set X)} {H : ℕ → ℕ}

private abbrev whole {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    (W : Set M) (E : List (Set M)) (q : ℕ) :
    MarkedIdeal n M := ⟨univ,E,vanishingIdeal (n := n) W,q⟩

/-- The full unpowered atlas records are the indicated whole principal
record restricted to each chart. -/
def ExactWholeAt (A : NativeWindows X I W E H D) (q : ℕ) : Prop :=
  ∀ i, A.record i = MarkedIdeal.pullback (Subtype.val : A.openSet i → X) (whole W E q)

private theorem pullback_whole {M Z : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
    [IsComplexManifold n Z] (f : Z → M) (hf : IsOpenHoloEmbedding n f)
    (V : Set M) (B : List (Set M)) (q : ℕ) :
    MarkedIdeal.pullback f (whole (n := n) V B q) = whole (n := n) (f ⁻¹' V) (B.map (f ⁻¹' ·)) q :=
  MarkedIdealOperationsTransform.MarkedIdeal.ext_of preimage_univ rfl
    (pullback_vanishingIdeal_of_isOpenHoloEmbedding f hf V) rfl

/-- Shrinking the ambient open leaves each whole record the exact
restriction of the same ambient ideal, mark and ordered boundary. -/
theorem exactWholeAt_restrictAmbient (A : NativeWindows X I W E H D) (q : ℕ)
    (hA : ExactWholeAt A q) (O : Opens X) :
    ExactWholeAt (A.restrictAmbient O) q := by
  intro i
  let L := O ⊓ A.openSet i
  let U := nestedOpens O L
  let V := nestedOpens (A.openSet i) L
  let e := overlapBaseEquiv (n := n) (show L ≤ O from inf_le_left)
    (show L ≤ A.openSet i from inf_le_right)
  change MarkedIdeal.pullback e (MarkedIdeal.pullback (Subtype.val : V → A.openSet i) (A.record i)) =
    MarkedIdeal.pullback (Subtype.val : U → O)
      (whole ((Subtype.val : O → X) ⁻¹' W) (E.map ((Subtype.val : O → X) ⁻¹' ·)) q)
  rw [hA i]
  rw [pullback_whole (Subtype.val : A.openSet i → X) (isOpenHoloEmbedding_val (A.openSet i)) W E q,
    pullback_whole (Subtype.val : V → A.openSet i) (isOpenHoloEmbedding_val V),
    pullback_whole (Subtype.val : U → O) (isOpenHoloEmbedding_val U)]
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · exact preimage_univ
  · change (((E.map ((Subtype.val : A.openSet i → X) ⁻¹' ·)).map
      ((Subtype.val : V → A.openSet i) ⁻¹' ·)).map ((e : U → V) ⁻¹' ·)) =
        (E.map ((Subtype.val : O → X) ⁻¹' ·)).map ((Subtype.val : U → O) ⁻¹' ·)
    simp only [List.map_map]
    rfl
  · change GermIdeal.pullback (m := n) e
      (vanishingIdeal (n := n) ((Subtype.val : V → A.openSet i) ⁻¹' ((Subtype.val : A.openSet i → X) ⁻¹' W))) = _
    rw [pullback_vanishingIdeal_of_biholomorphism]
    rfl
  · rfl


/-- Base biholomorphisms retain the full exact atlas record. -/
theorem exactWholeAt_transportBase {B : CMfd.{0} n} (A : NativeWindows X I W E H D)
    (q : ℕ) (hA : ExactWholeAt A q)
    (φ : B ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X) :
    ExactWholeAt (A.transportBase φ) q := by
  intro i
  let U := A.preimageOpen φ i
  let V := A.openSet i
  let ψ := A.windowEquiv φ i
  change MarkedIdeal.pullback ψ (A.record i) =
    MarkedIdeal.pullback (Subtype.val : U → B) (whole (φ ⁻¹' W) (E.map (φ ⁻¹' ·)) q)
  rw [hA i]
  change MarkedIdeal.pullback ψ (MarkedIdeal.pullback (Subtype.val : V → X) (whole W E q)) = _
  rw [pullback_whole (Subtype.val : V → X) (isOpenHoloEmbedding_val V),
    pullback_whole (Subtype.val : U → B) (isOpenHoloEmbedding_val U)]
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · exact preimage_univ
  · change ((E.map ((Subtype.val : V → X) ⁻¹' ·)).map ((ψ : U → V) ⁻¹' ·)) =
      (E.map (φ ⁻¹' ·)).map ((Subtype.val : U → B) ⁻¹' ·)
    simp only [List.map_map]
    rfl
  · change GermIdeal.pullback (m := n) ψ
      (vanishingIdeal (n := n) ((Subtype.val : V → X) ⁻¹' W)) = _
    rw [pullback_vanishingIdeal_of_biholomorphism]
    rfl
  · rfl

/-- The relative native successor preserves exact chart records and
simultaneous maxima on the actual restricted prefix with one new blowup. -/
theorem exists_exact_native_atlas_successor (hn : 0 < n)
    (hW : IsComplexAnalyticSubset (n := n) W) (hE : IsSNCDivisor n E)
    (hD : IsClosed D)
    (hLevel : D = {x | ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) W) x ℓ = H ℓ})
    (hNot : ∀ B ∈ E, ∀ x ∈ D, x ∈ B → ¬ ∀ᶠ z in 𝓝 x, z ∈ B → z ∈ W)
    (A : NativeWindows X I W E H D) (q : ℕ) (hExact : ExactWholeAt A q)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (whole W E 1) T)
    (hStage : StageCentres (fun S C => C ⊆ singularSet (n := n) (strictTransform n S.proj W)) T)
    (hCan : ∀ i, IsCanonical (A.powered i) ((canonicalInvariant n).inv (A.powered i))
      (restrict (A.openSet i) T))
    (hSync : NativeSimultaneousStages (canonicalInvariant n) A.openSet A.powered T)
    {K : Set X} (hK : IsCompact K)
    (hNe : (activeSupport T W D H ∩ T.proj ⁻¹' K).Nonempty) :
    ∃ O : Opens X, K ⊆ O ∧
      ∃ (C : Set (openPreimage T O)) (Z : CMfd.{0} n) (π : Z → openPreimage T O)
        (hπ : IsBlowupAlong n C π),
      let B := A.restrictAmbient O
      let S := BlowupTower.step (restrict O T) C π hπ
      C.Nonempty ∧
      IsGeoTestTower (whole ((Subtype.val : O → X) ⁻¹' W) (E.map ((Subtype.val : O → X) ⁻¹' ·)) 1) S ∧
      StageCentres (fun L C => C ⊆ singularSet (n := n)
        (strictTransform n L.proj ((Subtype.val : O → X) ⁻¹' W))) S ∧
      ExactWholeAt B q ∧
      (∀ i, IsCanonical (B.powered i) ((canonicalInvariant n).inv (B.powered i))
        (restrict (B.openSet i) S)) ∧
      NativeSimultaneousStages (canonicalInvariant n) B.openSet B.powered S := by
  let R : BMInvariant.{0,0} n (fun {M} P Q => LocWPEquiv (X := M) P Q) n (ValTy n) :=
    ⟨canonicalInvariant n, classFunctorialFor_canonicalInvariant n⟩
  let F := activeSupport T W D H
  have hF : IsClosed F := isClosed_activeSupport T hW hD
  have hR := nativeWindows_active_replay hn R hW hE hLevel hNot A T hT hStage hCan
  have hCover : ∀ y ∈ F, ∃ (i : I) (hy : y ∈ openPreimage T (A.openSet i)),
      (⟨y,hy⟩ : openPreimage T (A.openSet i)) ∈
        (geoTransformAlong (A.powered i) (restrict (A.openSet i) T)).cosupp := by
    intro y hy
    obtain ⟨i,hi⟩ := A.covers (T.proj y) hy.1
    exact ⟨i,hi,(hR.support i ⟨y,hi⟩).mpr hy⟩
  obtain ⟨v,O,hKO,_,hNext⟩ := exists_relative_native_successor_with_cut
    (canonicalInvariant n) hW E hE T hT hStage A.openSet F hF hK hNe A.powered A.powered_domain
    hCan hR.boundary H hR.currentCut hCover (fun i y => (hR.support i y).mp) hR.overlap
  dsimp only at hNext
  obtain ⟨C,Z,π,hπ,hC,_,_,hS,hSing,hLocal,_,hCut⟩ := hNext
  let B := A.restrictAmbient O
  refine ⟨O,hKO,C,Z,π,hπ,hC,hS,hSing,exactWholeAt_restrictAmbient A q hExact O,?_,?_⟩
  · intro i
    rw [A.restrictAmbient_powered O i]
    exact (hLocal i).2.1
  · refine ⟨A.simultaneous_restrictAmbient (canonicalInvariant n) T hCan hSync O,Or.inr ⟨v,?_⟩⟩
    have hRecords : B.powered = fun i => shrunkRecord (n := n) O (A.openSet i) (A.powered i) :=
      funext (A.restrictAmbient_powered O)
    change NativeSimultaneousCentre (canonicalInvariant n) B.openSet B.powered (restrict O T) C v
    rw [hRecords]
    exact hCut


/-- The exact retained simultaneous chart data feed the whole-record
canonicality comparison when the supported label contains the initial cosupport. -/
theorem hasExactCoveredNativeAtlas_of_retained
    {m : ℕ} {X Y : CMfd.{0} (m+1)} {W : Set X} {E : List (Set X)} {H : ℕ → ℕ}
    (A : NativeWindows X I W E H (phaseLevel W H)) (q : ℕ) (hExact : ExactWholeAt A q)
    (S : BlowupTower X Y) (hSync : NativeSimultaneousStages (canonicalInvariant (m+1)) A.openSet A.powered S)
    (hSupport : (whole W E q : MarkedIdeal (m+1) X).cosupp ⊆ phaseLevel W H) :
    HasExactCoveredNativeAtlas W E H S (whole W E q) :=
  exact_covered_atlas_of_profile_support A (whole W E q) S hSupport hExact hSync

end
end Hironaka.HironakaG8PrincipalNativeAtlasSuccessor
