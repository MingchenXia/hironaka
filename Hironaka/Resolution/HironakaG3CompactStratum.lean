import Hironaka.Resolution.HironakaG3Nonerasure

/-! Compact one-stratum finite resolution with genuine target non-erasure. -/
set_option autoImplicit false
open Set Filter Function TopologicalSpace Topology
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3CompactStratum
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  SubmanifoldChartedSpace HironakaDisjointFiniteControlledHistory
  HironakaG3ControlledHistorySubsetTransport HironakaG3EndpointNC
  HironakaG3StratumTerminalNC HironakaG3Nonerasure

/-- A compact analytic target with a dense smooth boundary-free open admits
an actual finite embedded tower whose strict target maps onto the whole target. -/
theorem exists_compact_lower_tower_with_nonerasure
    {n : ℕ} {X : CMfd.{0} n} {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W)
    (hK : IsCompact W) (hint : interior W = ∅) {E : List (Set X)}
    (hE : IsSNCDivisor n E) (O : Opens X) (hEO : ∀ H ∈ E, Disjoint H (O : Set X))
    {d : ℕ} (hreg : ∀ x ∈ W, x ∈ O → RegularAtDim (n := n) W x d)
    (hdense : W ⊆ closure (W ∩ (O : Set X))) :
    ∃ (Y : CMfd.{0} n) (T : BlowupTower X Y),
      IsGeoTestTower (fullMarked E (vanishingIdeal (n := n) W)) T ∧
      RestrictEmptyTower.CentresAvoid O T ∧
      IsClosedSubmanifold n (strictAlong T W) ∧
      (∀ x ∈ strictAlong T W, RegularAtDim (n := n) (strictAlong T W) x d) ∧
      HasNormalCrossings n (strictAlong T W)
        (geoTransformAlong (fullMarked E (vanishingIdeal (n := n) W)) T).E ∧
      T.proj '' strictAlong T W = W := by
  let M := fullMarked E (vanishingIdeal (n := n) W)
  have hDom : ResolutionInvariantSpec.IsInvDomain n M :=
    HironakaEmbeddedBoundary.isInvDomain_boundary hWa hint hE
  have hCos : M.cosupp = W := HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hWa.isClosed E
  have hCompact : IsCompact M.cosupp := by rw [hCos]; exact hK
  obtain ⟨Y₀,T₀,hCan,hRes⟩ :=
    HironakaAdmissibleSequence.exists_isGeoResolution_isCanonical_of_isCompact
      (CanonicalCentres.canonicalInvariant.{0} n) hDom hCompact
  obtain ⟨Y,T,hT,hAvoid,hSmooth,hDim,hNC⟩ :=
    HironakaEmbeddedBoundary.exists_tower_embedded_of_isCanonical
      (HironakaFromSeqInvariant.embeddingFields_of_seq (CanonicalCentres.canonicalInvariant.{0} n))
      hWa O hEO hreg hdense hDom T₀ hCan hRes
  have hEq := HironakaG8P1ArcTangentTrace.strictAlong_eq_conventional_of_centresAvoid
    W hWa.isClosed O hdense T hAvoid
  refine ⟨Y,T,hT,hAvoid,?_,?_,?_,projection_strictAlong_eq_of_centresAvoid W hWa.isClosed O hdense T hAvoid⟩
  · rwa [hEq]
  · simpa only [hEq] using hDim
  · simpa only [hEq, fullMarked] using hNC


/-- For a compact target in one proper stratum, ordinary intrinsic geometry
produces a full-boundary ambient history, terminal normal crossings, and exact
surjective projection of its strict target. -/
theorem exists_compact_stratum_resolution_with_nonerasure
    {d t : ℕ} {X : CMfd.{0} (d+t)} {N : Set X} (hNc : IsClosed N)
    (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d) (ht : 0 < t)
    {E B : List (Set X)} (hE : IsSNCDivisor (d+t) E) (hBsub : B.Sublist E)
    (hOmitted : ∀ H ∈ E, H ∉ B → N ⊆ H)
    (hTrans : IsTransverse (d+t) N B)
    {W : Set X} (hWa : IsComplexAnalyticSubset (n := d+t) W) (hWN : W ⊆ N) :
    letI := chartedSpace (Nat.le_add_right d t) hN
    letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
    let V : Set N := (Subtype.val : N → X) ⁻¹' W
    let B₀ := B.map fun H => (Subtype.val : N → X) ⁻¹' H
    IsComplexAnalyticSubset (n := d) V → IsCompact V → interior V = ∅ →
    IsSNCDivisor d B₀ →
    ∀ (O : Opens (CMfd.of (n := d) N)), (∀ H ∈ B₀, Disjoint H (O : Set N)) →
      (∃ m, (∀ x ∈ V, x ∈ O → RegularAtDim (n := d) V x m)) →
      V ⊆ closure (V ∩ (O : Set N)) →
      ∃ (Y : CMfd.{0} (d+t)) (U : BlowupTower X Y),
        IsGeoTestTower (fullMarked E (vanishingIdeal (n := d+t) W)) U ∧
        HasNormalCrossings (d+t) (strictAlong U W)
          (geoTransformAlong (fullMarked E (vanishingIdeal (n := d+t) W)) U).E ∧
        U.proj '' strictAlong U W = W := by
  let := chartedSpace (Nat.le_add_right d t) hN
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
  dsimp only
  intro hV hK hint hB O hEO ⟨m,hreg⟩ hdense
  obtain ⟨Q,T,hT,hAvoid,hSmooth,hDim,hNC,hImage⟩ :=
    exists_compact_lower_tower_with_nonerasure (X := CMfd.of (n := d) N)
      (W := (Subtype.val : N → X) ⁻¹' W) (d := m) hV hK hint hB O hEO hreg hdense
  obtain ⟨Y,U,η,hU,hLength,hHist,hUNC,hProj⟩ :=
    exists_full_boundary_history_with_terminal_nc hNc hN ht hE hBsub hOmitted hTrans hWa hWN T hT hNC
  have hW : (Subtype.val : N → X) '' ((Subtype.val : N → X) ⁻¹' W) = W := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hx
      exact ⟨⟨x,hWN hx⟩, hx, rfl⟩
  refine ⟨Y,U,hU,hUNC,?_⟩
  rw [hProj, hImage, hW]

end
end Hironaka.HironakaG3CompactStratum
