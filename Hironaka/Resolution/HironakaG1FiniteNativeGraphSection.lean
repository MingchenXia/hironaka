import Hironaka.Resolution.HironakaG1NormalGraphFlags
import Hironaka.Resolution.HironakaG1NativeChartCanonicalComparison

/-! The actual native manifold of a finite normal graph and its full marked trace. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1FiniteNativeGraphSection

noncomputable section

open Hironaka.RegularLocusDense Hironaka.HolomorphicIdealSheaves RelativePrincipalizationSpan
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  SubmanifoldChartedSpace SubmanifoldCodRestrict
  HironakaG1NormalGraphFlags HironakaActualNativeSectionFiniteHistory
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionOrderedChoiceImageTrace
  HironakaActualPowerBoundaryExponents HironakaActualCentreJointJets HironakaActualIntrinsicStableAmbientIso

variable {n t : ℕ} {U : Opens (ComplexModel n)} {f : U → ComplexModel t}

private abbrev ambient (U : Opens (ComplexModel n)) (t : ℕ) :=
  CMfd.of (n := n + t) (blockOpen U t)

private theorem section_mem_graph (f : U → ComplexModel t) (x : U) :
    blockSection f x ∈ blockGraph f univ := by
  have hNorm : actualJointNormalProjection n t (blockSection f x).val = f x := by
    change actualJointNormalProjection n t (join x.val (f x)) = f x
    exact second_join _ _
  exact ⟨trivial, (blockProjection_blockSection f x).symm ▸ hNorm⟩

/-- The full actual graph is regular of the source dimension. -/
theorem nativeBlockGraph_regular
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ f) :
    ∀ z ∈ (blockGraph f univ : Set (ambient U t)),
      RegularAtDim (n := n + t) (blockGraph f univ) z n :=
  fun _ hz => regularAtDim_blockGraph_of hf hz (AnalyticIrreducibleComponents.regularAtDim_univ _)

/-- The geometric section and projection are inverse on the actual native
manifold of the full graph, with the native flattening atlas. -/
def nativeBlockGraphEquiv
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ f) :
    U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      nativeManifold (Y := ambient U t) (Nat.le_add_right n t) (blockGraph f univ)
        (nativeBlockGraph_regular hf) where
  toEquiv :=
    ⟨fun x => ⟨blockSection f x, section_mem_graph f x⟩,
      fun z => blockProjection z.val,
      blockProjection_blockSection f,
      fun z => by
        apply Subtype.ext
        apply Subtype.ext
        have hz : actualJointNormalProjection n t z.val.val = f (blockProjection z.val) := z.property.2
        change join (blockProjection z.val).val (f (blockProjection z.val)) = z.val.val
        rw [← hz]
        exact join_projections z.val.val⟩
  contMDiff_toFun := contMDiff_codRestrict (Nat.le_add_right n t) (nativeBlockGraph_regular hf)
    (blockSection_contMDiff hf) (section_mem_graph f)
  contMDiff_invFun := (blockProjection_contMDiff U t).comp
    (contMDiff_val (Nat.le_add_right n t) (nativeBlockGraph_regular hf))

set_option maxHeartbeats 500000 in
/-- The native marked record on the full finite graph, pulled back by its
actual biholomorphic section, is exactly the original source with each
extra boundary member restricted to the graph in order. -/
theorem pullback_native_blockMarked
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ f)
    (Q : MarkedIdeal n U) (hQ : Q.ideal.IsCoherent) (hd : 0 < Q.d)
    (F : List (Set (blockOpen U t))) :
    MarkedIdeal.pullback (nativeBlockGraphEquiv hf)
      (nativePullback (Y := ambient U t) (Nat.le_add_right n t) (blockGraph f univ) (nativeBlockGraph_regular hf)
        (blockMarked f Q F)) =
      { Q with E := F.map (blockSection f ⁻¹' ·) ++ Q.E } := by
  let W : Set (ambient U t) := blockGraph f univ
  let A := nativeManifold (Nat.le_add_right n t) W (nativeBlockGraph_regular hf)
  let i : A → ambient U t := Subtype.val
  let e := nativeBlockGraphEquiv hf
  have hi : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (n + t)) ∞ i :=
    contMDiff_val (Nat.le_add_right n t) (nativeBlockGraph_regular hf)
  change markedPullback (m := n) e (markedPullback (m := n) i (blockMarked f Q F)) = _
  rw [← whole_markedPullback_comp hi e.contMDiff _ (blockMarked_coherent hf hQ F)]
  change markedPullback (m := n) (blockSection f) (blockMarked f Q F) = _
  simpa only [powerMarked, Nat.mul_one,
    FactorizationFromResolution.idealPow_one_of_isCoherent hQ,
    FactorizationFromResolution.idealPow_one_of_isCoherent (blockMarked_coherent hf hQ F)]
    using markedPullback_power_blockSection hf Q hQ hd F 1

open BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdealTowerTransport
  ResolutionInvariantSpec ResolutionDriver
  NormalCrossings HironakaActualNativeRecursiveValues HironakaSmoothSubmersionCanonicalValueDimensionShift
  CanonicalCentres

set_option maxHeartbeats 900000 in
/-- An actual canonical history of a finite graph-supported record has a
canonical history on the literal source. The graph inclusion and its
biholomorphic section identify the original recursive values and maximum
loci, with the actual normal codimension as dimension shift. -/
theorem exists_original_native_block_history (hn : 0 < n)
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ f)
    (Q : MarkedIdeal n U) (hQ : IsInvDomain n Q)
    (F : List (Set (blockOpen U t)))
    (hSNC : IsSNCDivisor (n + t) (blockMarked f Q F).E)
    (hTr : IsTransverse (n + t) (blockMarked f Q F).N (blockMarked f Q F).E)
    (hTrans : IsTransverse (n + t) (blockGraph f univ) (blockMarked f Q F).E)
    {Y : CMfd.{0} (n + t)} (T : BlowupTower (ambient U t) Y)
    (hCan : IsCanonical (blockMarked f Q F)
      ((invFamily (Nat.lt_of_lt_of_le hn (Nat.le_add_right n t)) (n + t)).inv
        (blockMarked f Q F)) T) :
    let M := blockMarked f Q F
    let W : Set (ambient U t) := blockGraph f univ
    let hW := nativeBlockGraph_regular hf
    let hk := Nat.le_add_right n t
    let e := nativeBlockGraphEquiv hf
    let Q' : MarkedIdeal n (CMfd.of (n := n) U) :=
      { Q with E := F.map (blockSection f ⁻¹' ·) ++ Q.E }
    ∃ (V : Set Y) (hVc : IsClosed V) (hV : ∀ y ∈ V, RegularAtDim (n := n + t) V y n)
      (B : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)),
      let S := transport (X' := CMfd.of (n := n) U) e B
      let Fₐ := (invFamily (Nat.lt_of_lt_of_le hn hk) (((n + t) - n) + n)).inv M T
      let Fₛ := (invFamily hn n).inv Q' S.tower
      let ι := fun z : S.target => (S.back z).val
      ∃ hWc : IsClosed W,
        Lift hk W hWc hW M.E T V hVc hV B ∧ S.tower.length = T.length ∧
        IsInvDomain n Q' ∧ IsCanonical Q' ((invFamily hn n).inv Q') S.tower ∧
        (∀ z : S.target, ι z ∈ (geoTransformAlong M T).cosupp →
          Fₐ (ι z) = familyDimensionMap ((n + t) - n) n (Fₛ z)) ∧
        maxLocus Fₛ (geoTransformAlong Q' S.tower).cosupp =
          ι ⁻¹' maxLocus Fₐ (geoTransformAlong M T).cosupp ∧
        ι '' maxLocus Fₛ (geoTransformAlong Q' S.tower).cosupp =
          maxLocus Fₐ (geoTransformAlong M T).cosupp ∧
        (IsGeoResolution M T → IsGeoResolution Q' S.tower) := by
  intro M W hW hk e Q'
  have hWc : IsClosed W := (blockGraph_closed_submanifold hf
    (A := (univ : Set U)) HomogenizedGlueingTower.isClosedSubmanifold_univ).1
  have hMN : M.N ⊆ W := fun _ hz => ⟨trivial, hz.2⟩
  have hMQ := blockMarked_isInvDomain hf Q hQ F hSNC hTr
  have hM : IsInvDomain (n + t) M := by
    refine ⟨hMQ.isWellFormed, ?_, hMQ.one_le_d, hMQ.isNonzeroAlongAt⟩
    intro z hz
    obtain ⟨j, hj, hReg⟩ := hMQ.dimLE z hz
    exact ⟨j, hj.trans hk, hReg⟩
  obtain ⟨V, hVc, hV, B, hLift, hLen, hDom, _, _, _, hRes⟩ :=
    exists_original_native_canonical_history (Nat.lt_of_lt_of_le hn hk) hk W hWc hW
      M hM hMN hTrans T hCan
  let QN := nativePullback hk W hW M
  let S := transport (X' := CMfd.of (n := n) U) e B
  have hIso := transport_isTowerIso (X' := CMfd.of (n := n) U) e B
  have he : MarkedIdeal.pullback e QN = Q' :=
    pullback_native_blockMarked hf Q hQ.isWellFormed.isCoherent hQ.one_le_d F
  have hCompare := HironakaG1NativeChartCanonicalComparison.original_native_chart_comparison
    (Nat.lt_of_lt_of_le hn hk) hn M hMQ hMN hTrans hLift e S.tower S.back hIso
  dsimp only at hCompare
  have hRecord : MarkedIdeal.pullback e (nativePullback hk W hW M) = Q' := he
  rw [hRecord] at hCompare
  obtain ⟨hDomain, hEqCan, hEndpoint⟩ := hCompare
  have hCanOffset : IsCanonical M
      ((invFamily (Nat.lt_of_lt_of_le hn hk) (((n + t) - n) + n)).inv M) T := by
    exact Eq.mpr (congrArg (fun d => IsCanonical M
      ((invFamily (Nat.lt_of_lt_of_le hn hk) d).inv M) T) (Nat.sub_add_cancel hk)) hCan
  obtain ⟨_, _, hValue, hMaxPre, hMaxImage⟩ := hEndpoint hCanOffset
  refine ⟨V, hVc, hV, B, hWc, hLift, hIso.length_eq.trans hLen, hDomain,
    hEqCan.mpr hCanOffset, hValue, hMaxPre, hMaxImage, ?_⟩
  intro hResolved
  have hEnd := (IsTowerIso.isGeoResolution_iff (X' := CMfd.of (n := n) U) e
    hDom.isWellFormed.isClosedSubmanifold_N hDom.isWellFormed.isCoherent hIso).mpr (hRes hResolved)
  rwa [hRecord] at hEnd

end

end Hironaka.HironakaG1FiniteNativeGraphSection
