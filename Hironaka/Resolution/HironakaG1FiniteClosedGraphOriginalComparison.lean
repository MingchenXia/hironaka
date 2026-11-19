import Hironaka.Resolution.HironakaG1FiniteNativeGraphSection
import Hironaka.Resolution.HironakaG1FiniteNativePaddingComposition

/-! Whole finite-normal supported comparison of the same original record. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG1FiniteClosedGraphOriginalComparison
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism ResolutionInvariantSpec
  ResolutionDriver CanonicalCentres BlowupTowerTransforms
  HironakaG1IteratedProperNormalNativeState HironakaG1IteratedNormalBlockIdeal
  HironakaG1ProperCarrierNormalContact HironakaG1FiniteSourceWeakClassGraphLift
  HironakaG1NormalGraphFlags HironakaG1FiniteNativeGraphSection HironakaG1RatioGraphCentreGeometry
  HironakaG1RatioGraphFiniteTestClass HironakaG8LocalHistory HironakaG1CrossAmbientNativeComparison
  HironakaActualNativeHistoryExistence HironakaActualNativeSectionFiniteHistory
  HironakaSmoothSubmersionCanonicalValueDimensionShift BlowupTowerIsomorphism MarkedIdealTowerTransport
  InvDomainTowerAlong NormalCrossings

/-- Whole finite graph padding has its actual invariant domain for any
ordinary source. The proof is independent of native Hilbert–Samuel data. -/
theorem blockAmbientMarked_isInvDomain {n q t : ℕ} {U : Opens (ComplexModel n)}
    {f : U → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel t) ∞ f)
    (Q : MarkedIdeal n U) (hQ : IsInvDomain q Q) :
    IsInvDomain (q+t) (blockAmbientMarked f Q) := by
  have hI : ∀ t, IsInvDomain (q+t) (iteratedNormalMarked Q t) := by
    intro t
    induction t with
    | zero => exact hQ
    | succ t ih => exact properNormalMarked_isInvDomain _ ih
  let e := iteratedNormalBlockEquiv U t
  have hZ := isInvDomain_pullback e (hI t)
  rw [iteratedNormalMarked_pullback_blockEquiv Q hQ.isWellFormed.isCoherent t] at hZ
  let b := blockChartEquiv (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (↥U) ∞)
    hf (contMDiff_const (c := (0 : ComplexModel t)))
  have hF := isInvDomain_pullback b hZ
  have hEq := blockAmbientMarked_pullback_shift f hf Q hQ.isWellFormed.isCoherent
  change MarkedIdeal.pullback b (blockAmbientMarked 0 Q) = blockAmbientMarked f Q at hEq
  rwa [hEq] at hF

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
/-- From the original record and a full cylindrical test, construct the
carrier-supported realization on the same actual finite upper tower.
The normalized source is the literal original record at its true mark.
No native profile, canonicality, support or lift certificate is supplied. -/
theorem exists_closed_graph_actual_native_realization {n t : ℕ} {U : Opens (ComplexModel n)}
    (hn : 0 < n) {f : U → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel t) ∞ f)
    (Q : MarkedIdeal n U) (hQ : IsInvDomain n Q)
    {Y : CMfd.{0} (n+t)} (T : BlowupTower (CMfd.of (n := n+t) (blockOpen U t)) Y)
    (hT : (blockAmbientMarked f Q).IsGeoTestTower T) :
    ∃ (Z : CMfd.{0} n) (S : BlowupTower (CMfd.of (n := n) U) Z)
      (L : NativeChartRealization Q S (n+t) n),
      L.base = CMfd.of (n := n+t) (blockOpen U t) ∧ L.target = Y ∧
      HEq L.record (blockMarked f Q []) ∧ HEq L.tower T ∧
      S.length = T.length ∧ Q.IsGeoTestTower S ∧
      ∃ i : Z → Y,
        Function.Injective i ∧
        (∀ z, T.proj (i z) = blockSection f (S.proj z)) ∧
        let F := (invFamily (hn.trans_le (Nat.le_add_right n t)) (((n+t)-n)+n)).inv (blockMarked f Q []) T
        let G := (invFamily hn n).inv Q S
        let D := (geoTransformAlong Q S).cosupp
        let C := (geoTransformAlong (blockMarked f Q []) T).cosupp
        (IsCanonical Q ((invFamily hn n).inv Q) S ↔
          IsCanonical (blockMarked f Q [])
            ((invFamily (hn.trans_le (Nat.le_add_right n t)) (((n+t)-n)+n)).inv (blockMarked f Q [])) T) ∧
        (IsCanonical Q ((invFamily hn n).inv Q) S →
          i '' D = C ∧ D = i ⁻¹' C ∧
          (∀ z ∈ D, F (i z) = familyDimensionMap ((n+t)-n) n (G z)) ∧
          maxLocus G D = i ⁻¹' maxLocus F C ∧
          i '' maxLocus G D = maxLocus F C) := by
  let X := CMfd.of (n := n+t) (blockOpen U t)
  let A := CMfd.of (n := n) U
  let W : Set X := blockGraph f univ
  let hW := nativeBlockGraph_regular hf
  let hk := Nat.le_add_right n t
  let H := blockMarked f Q []
  let e := nativeBlockGraphEquiv hf
  have hWc : IsClosed W := (blockGraph_closed_submanifold hf
    HomogenizedGlueingTower.isClosedSubmanifold_univ).1
  have hHN : H.N ⊆ W := fun _ hz => ⟨mem_univ _,hz.2⟩
  have hFull := blockAmbientMarked_isInvDomain hf Q hQ
  have hDom : IsInvDomain n H := blockMarked_isInvDomain hf Q hQ []
    hFull.isWellFormed.isSNCDivisor (blockGraph_isTransverse hQ.isWellFormed.isTransverse hf)
  have hTr : IsTransverse (n+t) W H.E := blockGraph_isTransverse
    (SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hQ.isWellFormed.isSNCDivisor) hf
  have hTest : H.IsGeoTestTower T :=
    ((blockAmbientMarked_locWPEquiv_blockMarked hf Q hQ).wEquiv.2 T).1.mp hT
  obtain ⟨V,hVc,hV,B,hLift,hB⟩ :=
    exists_native_history_of_original_test (hn.trans_le hk) hk W hWc hW H hDom hHN hTr T hTest
  let A' := nativeManifold hk W hW
  let Z' := nativeManifold hk V hV
  let S := transport (X := A') (X' := A) e B
  have hIso := transport_isTowerIso (X := A') (X' := A) e B
  let R := nativePullback hk W hW H
  have hSource : MarkedIdeal.pullback e R = Q := by
    have h := pullback_native_blockMarked hf Q hQ.isWellFormed.isCoherent hQ.one_le_d []
    change MarkedIdeal.pullback e R = {Q with E := List.map (blockSection f ⁻¹' ·) [] ++ Q.E} at h
    simpa only [List.map_nil,List.nil_append] using h
  have hBdom := HironakaActualNativeInvariantDomain.isInvDomain_nativePullback
    (X := X) (hn.trans_le hk) hk hW H hDom hHN hTr
  have hST := IsTowerIso.isGeoTestTower_iff (X := A') (X' := A) (Y := Z') (Y' := S.target)
    e (𝔪 := R) hBdom.isWellFormed.isClosedSubmanifold_N hBdom.isWellFormed.isCoherent hIso
  rw [hSource] at hST
  let L : NativeChartRealization Q S.tower (n+t) n :=
    ⟨X,Y,H,hDom,T,hk,W,hWc,hW,hHN,hTr,V,hVc,hV,B,hLift,e,S.back,hIso,hSource⟩
  obtain ⟨hCan,hCompare⟩ := L.compare hn
  refine ⟨S.target,S.tower,L,rfl,rfl,HEq.rfl,HEq.rfl,hIso.length_eq.trans hLift.length,hST.mpr hB,
    L.endpointMap,Subtype.val_injective.comp S.back.injective,?_,hCan,fun h => hCompare (hCan.mp h)⟩
  intro z
  exact (hLift.square (S.back z)).trans (congrArg Subtype.val (hIso.proj_comm z).symm)

end
end Hironaka.HironakaG1FiniteClosedGraphOriginalComparison
