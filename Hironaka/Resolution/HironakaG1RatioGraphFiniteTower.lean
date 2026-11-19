import Hironaka.Resolution.HironakaG1RatioGraphNativeSource
import Hironaka.Resolution.HironakaActualNativeRecursiveValues
import Hironaka.Resolution.HironakaG1NativeChartCanonicalComparison

/-! Finite native descent on the actual supported ratio graph. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG1RatioGraphFiniteTower
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong.MarkedIdeal
  ResolutionInvariantSpec HironakaG11PresLineState NormalCrossings NormalCrossingsInvariance
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeHistoryExistence
  HironakaActualNativeRecursiveValues HironakaActualNativeSectionOrderHistory
  HironakaG1NormalGraphFlags HironakaG1IteratedNormalBlockIdeal HironakaBaseChange
  HironakaG1RatioSectionBlowup HironakaG1RatioGraphCentreGeometry HironakaG1RatioGraphNativeSource
  HironakaSmoothSubmersionCoefficientIdeals HironakaActualOpenEmbeddingCanonicalExtension
  CoefficientIdealRestriction MarkedIdealOpenBiholomorphism RelativePrincipalizationSpan
  HironakaG1ControlledCarrierRestriction RestrictLeCalculus RestrictedIdealWeight
  BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower MarkedIdealBiholomorphism

variable {n t : ℕ} {U : Opens (ComplexModel n)} {X : CMfd.{0} (n+t)}
    {e : X → blockOpen U t} {O : Opens (blockOpen U t)}
    (b : X ≃ₘ⟮𝓘(ℂ,ComplexModel (n+t)),𝓘(ℂ,ComplexModel (n+t))⟯ O)
    (hb : ∀ z, e z = (b z).val)
    {f : U → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel t) ∞ f)

private abbrev he : IsOpenHoloEmbedding (n+t) e := ⟨O,b,hb⟩

/-- The supported record is the pullback of the finite block record with
its graph carrier and empty extra divisor list. -/
theorem withN_blockAmbientMarked_eq (Q : MarkedIdeal n U) :
    let P := markedPullback (m := n+t) e (blockAmbientMarked f Q)
    withN P (P.N ∩ sectionSupport e f) =
      markedPullback (m := n+t) e (blockMarked f Q []) := by
  intro P
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · ext x
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,mem_univ _,h.2⟩⟩
  · rfl
  · rfl
  · rfl

include b hb hf in
/-- Both literal records have domains. The graph-supported version
already has the smaller source dimensional bound. -/
theorem ratioGraph_supported_domains (Q : MarkedIdeal n U) (hQ : IsInvDomain n Q)
    {D : Set U} {H : ℕ → ℕ} (hState : NativeHSState (X := CMfd.of (n := n) U) Q D H) :
    let W := sectionSupport e f
    let P := markedPullback (m := n+t) e (blockAmbientMarked f Q)
    let S := withN P (P.N ∩ W)
    IsInvDomain (n+t) P ∧ IsInvDomain n S ∧ IsTransverse (n+t) W S.E := by
  intro W P S
  let A := CMfd.of (n := n+t) (blockOpen U t)
  have hP := (blockAmbientMarked_nativeHSState f hf Q H hState hQ).1
  have hSN : IsSNCDivisor (n+t) (blockMarked f Q []).E := hP.isWellFormed.isSNCDivisor
  have hB : IsInvDomain n (blockMarked f Q []) :=
    blockMarked_isInvDomain hf Q hQ [] hSN (blockGraph_isTransverse hQ.isWellFormed.isTransverse hf)
  have hX := isInvDomain_pullback_of_isOpenHoloEmbedding (X := A) (Y := X) e (he b hb) hP
  have hS := isInvDomain_pullback_of_isOpenHoloEmbedding (X := A) (Y := X) e (he b hb) hB
  have hTr := blockGraph_isTransverse
    (SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hQ.isWellFormed.isSNCDivisor) hf
  refine ⟨hX, ?_, isTransverse_preimage (he b hb).pullsBackCoordinates hTr⟩
  rw [show S = _ from withN_blockAmbientMarked_eq (e := e) (f := f) Q]
  exact hS

set_option maxHeartbeats 1200000 in
/-- Every actual finite test of the graph-supported ratio record induces a
native tower along the same centres and projections. Its whole controlled
record is the section trace of the supported ambient transform. If the
same tower tests the full cylinder, the endpoint restricted marked
records also agree on the strict supported carrier. -/
theorem exists_ratioGraph_supported_finite_tower (hpos : 0 < n+t)
    (Q : MarkedIdeal n U) (hQ : IsInvDomain n Q)
    {D : Set U} {H : ℕ → ℕ} (hState : NativeHSState (X := CMfd.of (n := n) U) Q D H)
    {Y : CMfd.{0} (n+t)} (T : BlowupTower X Y) :
    let W := sectionSupport e f
    let hW := sectionSupport_regular (he b hb) hf
    let P := markedPullback (m := n+t) e (blockAmbientMarked f Q)
    let S := withN P (P.N ∩ W)
    let S₀ := nativePullback (Nat.le_add_right n t) W hW P
    let U₀ := sectionBaseOpen (O := O) hf
    ∀ (_hT : IsGeoTestTower S T),
      ∃ (V : Set Y) (hVc : IsClosed V) (hV : ∀ y ∈ V, RegularAtDim (n := n+t) V y n)
        (B : BlowupTower (nativeManifold (Nat.le_add_right n t) W hW)
          (nativeManifold (Nat.le_add_right n t) V hV)),
        Lift (Nat.le_add_right n t) W (sectionSupport_closed (he b hb) hf) hW P.E T V hVc hV B ∧
        B.length = T.length ∧ V = strictAlong T W ∧ IsGeoTestTower S₀ B ∧
        MarkedIdeal.pullback (sectionBaseEquiv b hb hf) S₀ =
          markedPullback (m := n) (Subtype.val : U₀ → U) Q ∧
        (∀ z : nativeManifold (Nat.le_add_right n t) V hV, T.proj z.val = (B.proj z).val) ∧
        geoTransformAlong S₀ B = nativePullback (Nat.le_add_right n t) V hV (geoTransformAlong S T) ∧
        (geoTransformAlong S₀ B).d = Q.d ∧
        (geoTransformAlong S₀ B).E =
          (geoTransformAlong P T).E.map ((Subtype.val : V → Y) ⁻¹' ·) ∧
        (geoTransformAlong S₀ B).cosupp =
          (Subtype.val : V → Y) ⁻¹' (geoTransformAlong S T).cosupp ∧
        (IsGeoTestTower P T →
          RestrictEquiv (withN (geoTransformAlong P T) (geoTransformAlong S T).N)
            (geoTransformAlong S T)) := by
  intro W hW P S S₀ U₀ hT
  obtain ⟨hP,hS,hTr⟩ := ratioGraph_supported_domains b hb hf Q hQ hState
  have hWc := sectionSupport_closed (he b hb) hf
  have hNW : S.N ⊆ W := inter_subset_right
  have hSN : nativePullback (Nat.le_add_right n t) W hW S = S₀ := nativePullback_withN_inter (Nat.le_add_right n t) hW P
  obtain ⟨V,hVc,hV,B,hLift,hTest⟩ := exists_native_history_of_original_test hpos
    (Nat.le_add_right n t) W hWc hW S hS hNW hTr T hT
  have hhol : ∀ x g, S.ideal.mem x g → HolomorphicAt (n+t) g x :=
    fun _ _ h => GermIdeal.IsCoherent.holomorphicAt_mem hS.isWellFormed.isCoherent h
  have hRecords := hLift.whole_records hpos hS.isWellFormed.isSNCDivisor hTr S rfl hNW hhol
  have hCos := HironakaActualNativeSectionOrderHistory.Lift.current_cosupport hLift hpos hS.isWellFormed.isSNCDivisor hTr S rfl hNW hhol
  rw [hSN] at hRecords hCos hTest
  have hE : (geoTransformAlong S T).E = (geoTransformAlong P T).E :=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq (𝔪 := S) (𝔫 := P) rfl T
  refine ⟨V,hVc,hV,B,hLift,hLift.length,hLift.carrier,hTest,
    sectionBaseEquiv_record b hb hf Q hQ.isWellFormed.isCoherent hQ.one_le_d,
    hLift.square,hRecords,?_,?_,hCos,?_⟩
  · rw [d_geoTransformAlong]
    rfl
  · rw [hRecords, ← hE]
    rfl
  · intro hTP
    have hI : RestrictLe S.N P.ideal P.ideal := restrictLe_refl hP.isWellFormed.isCoherent
    obtain ⟨_,hF,hB,_⟩ := geoTransformAlong_restricted_ideals P S
      hP.isWellFormed hS.isWellFormed inter_subset_left rfl hI hI T hTP hT
    refine ⟨rfl,hE.symm,?_,hF,hB⟩
    simp only [withN_d,d_geoTransformAlong]
    rfl

end
end Hironaka.HironakaG1RatioGraphFiniteTower
