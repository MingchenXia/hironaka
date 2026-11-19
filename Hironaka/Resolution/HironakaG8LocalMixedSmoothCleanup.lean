import Hironaka.Resolution.HironakaG8LocalMixedPhaseAssembly
import Hironaka.Resolution.HironakaG8OrderedSmoothSuffix

/-! Finite local full-boundary cleanup of a smooth carrier of varying
dimensions. The finitely many dimension parts are
cleaned in succession and stay protected during the other parts' phases. -/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8LocalMixedSmoothCleanup

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms RestrictEmptyTower
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaEmbeddedAnalytic HironakaEmbeddedDimensionParts
  NormalCrossings NormalCrossingsInvariance HironakaEmbeddedBoundary
  HironakaG8SeparatedSmoothGeometry HironakaG8SeparatedSmoothPhases HironakaG8LocalMixedPhaseAssembly
  HironakaG8LocalPureFinish HironakaActualProcessedAllMasksDrop HironakaAdmissibleCalculus
  HironakaSharpActualFiniteChronologicalHistory HironakaG11PresTowerState HironakaG4MaximalMatrixFibreGeometry
  HironakaG8OrderedSmoothSuffix HironakaActualSmoothBoundaryCleanup MarkedIdealTowerTransport
  BlowupTowerIsomorphism

/-- Rank retention follows the literal open and physical rebase of each actual suffix. -/
def ordered_smooth_tail_certificate {n : ℕ} (ds : List (Fin (n + 1))) : SmoothTailCertificate n where
  holds := OrderedSmoothSuffix ds
  restrictOpen := ordered_smooth_suffix_restrict
  ofTowerIso hIso h := ordered_smooth_suffix_of_isTowerIso h _ hIso

/-- Every window uses the same ascending list of all possible dimensions. -/
def ascending_smooth_tail_certificate (n : ℕ) : SmoothTailCertificate n :=
  ordered_smooth_tail_certificate (List.finRange (n + 1))

private theorem smooth_unchanged_cleanup {n : ℕ} {X : CMfd.{0} n} {W : Set X}
    (hW : IsClosedSubmanifold n W) (E : List (Set X)) (hE : IsSNCDivisor n E)
    (hNC : HasNormalCrossings n W E) :
    let U : Opens X := ⊤
    SmoothBoundaryTower ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·))
      (.refl : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U)) := by
  intro U
  let A := (Subtype.val : U → X) ⁻¹' W
  have hA : IsClosed A := hW.1.preimage continuous_subtype_val
  have hOut : strictTransform n (BlowupTower.refl (X := CMfd.of (n := n) U)).proj A = A :=
    strictTransform_id hA
  refine ⟨trivial, trivial, trivial, ?_,
    isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hE, ?_⟩
  · rw [hOut]
    exact BlowupRestrictOpen.isClosedSubmanifold_preimage_val hW U
  · rw [hOut]
    exact hasNormalCrossings_preimage (pullsBackCoordinates_val U) hNC

private theorem smooth_full_rank_cleanup {n : ℕ} {X : CMfd.{0} n} {W : Set X}
    (hW : IsClosedSubmanifold n W) (hFull : ∀ x ∈ W, RegularAtDim (n := n) W x n)
    (E : List (Set X)) (hE : IsSNCDivisor n E) :
    let U : Opens X := ⊤
    SmoothBoundaryTower ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·))
      (.refl : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U)) := by
  apply smooth_unchanged_cleanup hW E hE
  intro x hx
  have hNear : ∀ᶠ y in 𝓝 x, y ∈ (univ : Set X) ↔ y ∈ W := by
    filter_upwards [EmbeddedFromResolution.mem_nhds_of_regularAtDim_self (hFull x hx)] with y hy
    simp [hy]
  exact normalCrossingsAt_of_eventually_carrier_iff hNear
    ((SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE).hasNormalCrossings x (mem_univ x))

/-- All remaining dimensions are represented by the smaller finite set when
one closed smooth dimension part is removed from the carrier. -/
private theorem split_smooth_dimensions {n : ℕ} {X : CMfd.{0} n} {W : Set X}
    (hW : IsClosedSubmanifold n W) (d : Fin (n + 1)) (s : Finset (Fin (n + 1))) (hd : d ∉ s)
    (hRanks : ∀ x ∈ W, ∃ e : Fin (n + 1), e ∈ insert d s ∧ RegularAtDim (n := n) W x e) :
    let A := dimensionPart (n := n) W d
    let B := ⋃ e ∈ s, dimensionPart (n := n) W (e : Fin (n + 1))
    W = A ∪ B ∧ Disjoint A B ∧ IsClosedSubmanifold n A ∧ IsClosedSubmanifold n B ∧
    (∀ x ∈ A, RegularAtDim (n := n) A x d) ∧
    (∀ x ∈ B, ∃ e : Fin (n + 1), e ∈ s ∧ RegularAtDim (n := n) B x e) := by
  let A := dimensionPart (n := n) W d
  let B := ⋃ e ∈ s, dimensionPart (n := n) W (e : Fin (n + 1))
  have hASub : A ⊆ W := dimensionPart_subset hW.1 d
  have hBSub : B ⊆ W := iUnion₂_subset fun e _ => dimensionPart_subset hW.1 e
  have hParts : W = A ∪ B := by
    apply Subset.antisymm ?_ (union_subset hASub hBSub)
    intro x hx
    obtain ⟨e, he, hReg⟩ := hRanks x hx
    rcases Finset.mem_insert.mp he with he | he
    · subst e
      exact Or.inl (subset_closure hReg)
    · exact Or.inr (mem_iUnion₂.mpr ⟨e, he, subset_closure hReg⟩)
  have hSep : Disjoint A B := by
    apply disjoint_left.mpr
    intro x hxA hxB
    obtain ⟨e, he, hxE⟩ := mem_iUnion₂.mp hxB
    have hReg : x ∈ regularLocus (n := n) W d := by
      rw [← dimensionPart_eq_regularLocus_of_smooth hW]
      exact hxA
    have hne : (d : ℕ) ≠ e := fun hh => hd (Fin.ext hh ▸ he)
    exact notMem_dimensionPart_of_regularAtDim hReg hne hxE
  have hAClosed : IsClosed A := isClosed_closure
  have hBClosed : IsClosed B := s.finite_toSet.isClosed_biUnion (fun _ _ => isClosed_closure)
  have hAPure : ∀ x ∈ A, RegularAtDim (n := n) A x d := by
    intro x hx
    have hReg : x ∈ regularLocus (n := n) W d := by
      rw [← dimensionPart_eq_regularLocus_of_smooth hW]
      exact hx
    exact regularAtDim_dimensionPart_of_regularAtDim hW.1 hReg
  have hBPure : ∀ x ∈ B, ∃ e : Fin (n + 1), e ∈ s ∧ RegularAtDim (n := n) B x e := by
    intro x hx
    obtain ⟨e, he, hxE⟩ := mem_iUnion₂.mp hx
    have hReg : x ∈ regularLocus (n := n) W e := by
      rw [← dimensionPart_eq_regularLocus_of_smooth hW]
      exact hxE
    have hNear := eventually_mem_union_iff_left (A := B) hAClosed (disjoint_left.mp hSep.symm hx)
    rw [union_comm B A, ← hParts] at hNear
    exact ⟨e, he, CodimOneSupport.regularAtDim_of_eventually_mem_iff (hNear.mono fun _ h => h.symm) hReg⟩
  exact ⟨hParts, hSep, ⟨hAClosed, fun x hx => ⟨d,hAPure x hx⟩⟩,
    ⟨hBClosed, fun x hx => let ⟨e,_,h⟩ := hBPure x hx; ⟨e,h⟩⟩, hAPure, hBPure⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1500000 in
private theorem append_and_flatten_retained_phase {n : ℕ} {X : CMfd.{0} n}
    {W : Set X} (hW : IsClosed W) (E : List (Set X)) (hE : IsSNCDivisor n E)
    (d : Fin (n + 1)) (ds : List (Fin (n + 1))) (K : Set X) (V : Opens X) (hKV : K ⊆ V) :
    let XV := CMfd.of (n := n) V
    let WV : Set XV := (Subtype.val : V → X) ⁻¹' W
    let EV : List (Set XV) := E.map ((Subtype.val : V → X) ⁻¹' ·)
    let KV : Set XV := (Subtype.val : V → X) ⁻¹' K
    let MV := geometricTemplate (univ : Set XV) EV
    ∀ {Y : CMfd.{0} n} (T : BlowupTower XV Y) (hEV : IsSNCDivisor n EV),
      IsGeoTestTower MV T → CentresOver (WV ∩ ⋃ H ∈ EV, H) T → SmoothBoundaryStages WV EV T →
      SmoothRankPhase WV EV hEV d T → IsClosed (WV \ dimensionPart (n := n) WV d) →
      LocalSmoothTowerWithCarriers (ordered_smooth_tail_certificate ds)
        (strictTransform n T.proj WV) (strictTransform n T.proj (WV \ dimensionPart (n := n) WV d))
        (geoTransformAlong MV T).E (T.proj ⁻¹' KV) →
      LocalSmoothTowerWith (ordered_smooth_tail_certificate (d :: ds)) W E K := by
  intro XV WV EV KV MV Y T hEV hTA hOldFoot hOldStages hRankT hRem hLocal
  obtain ⟨O, hKO, Y', R, hTail, hRankR⟩ :=
    restrict_local_smooth_phase_with_certified_carrier (W := WV) (WCert := WV \ dimensionPart (n := n) WV d)
      (ordered_smooth_tail_certificate ds) EV hEV T hTA KV hLocal
  let L := restrict O T
  let XVO := CMfd.of (n := n) O
  let WVO : Set XVO := (Subtype.val : O → V) ⁻¹' WV
  let EVO : List (Set XVO) := EV.map ((Subtype.val : O → V) ⁻¹' ·)
  have hEVO : IsSNCDivisor n EVO :=
    isSNCDivisor_map_preimage (pullsBackCoordinates_val O) continuous_subtype_val hEV
  have hRemO : WVO \ dimensionPart (n := n) WVO d =
      (Subtype.val : O → V) ⁻¹' (WV \ dimensionPart (n := n) WV d) := by
    dsimp only [WVO]
    rw [dimensionPart_restrict (X := CMfd.of (n := n) V) O WV d, ← preimage_sdiff]
  have hRestO : OrderedSmoothSuffix ds (strictTransform n L.proj (WVO \ dimensionPart (n := n) WVO d))
      (geoTransformAlong (geometricTemplate (univ : Set XVO) EVO) L).E R := by
    rw [hRemO]
    exact hRankR
  have hClosedRemO : IsClosed (WVO \ dimensionPart (n := n) WVO d) := by
    rw [hRemO]
    exact hRem.preimage continuous_subtype_val
  have hJoinedRank : OrderedSmoothSuffix (d :: ds) WVO EVO (L.append R) :=
    .cons hEVO hClosedRemO (smooth_rank_restrict hRankT O hEVO) hRestO (IsTowerIso.refl_self _)
  have hJoined := append_smooth_phase_on_open (hW.preimage continuous_subtype_val) EV hEV T hOldFoot hOldStages O R hTail
  obtain ⟨D, hKD, e, he, hFlat⟩ :=
    flatten_local_smooth_tower_with_tower hW E hE V hKV O hKO (L.append R) hJoined
  have hFlatRank := ordered_smooth_suffix_of_isTowerIso hJoinedRank e (transport_isTowerIso e (L.append R))
  have hCarFlat : e ⁻¹' WVO = (Subtype.val : D → X) ⁻¹' W := by
    ext x
    change (e x).val.val ∈ W ↔ x.val ∈ W
    rw [he x]
  have hBdyFlat : EVO.map (e ⁻¹' ·) = E.map ((Subtype.val : D → X) ⁻¹' ·) := by
    dsimp only [EVO, EV]
    simp only [List.map_map]
    apply List.map_congr_left
    intro H _
    ext x
    change (e x).val.val ∈ H ↔ x.val ∈ H
    rw [he x]
  rw [hCarFlat, hBdyFlat] at hFlatRank
  exact ⟨D, hKD, _, _, hFlat, hFlatRank⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1500000 in
private theorem follow_dimension_phase {n : ℕ} {X : CMfd.{0} n} {W A B : Set X}
    {d : Fin (n + 1)} (ds : List (Fin (n + 1))) (hDim : A = dimensionPart (n := n) W d)
    (hParts : W = A ∪ B) (hSep : Disjoint A B)
    (hA : IsClosedSubmanifold n A) (hB : IsClosedSubmanifold n B)
    (hAPure : ∀ x ∈ A, RegularAtDim (n := n) A x d)
    (hBRanks : ∀ x ∈ B, ∃ e : Fin (n + 1), e ∈ ds ∧ RegularAtDim (n := n) B x e)
    (E : List (Set X)) (hE : IsSNCDivisor n E) (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (K : Set X) (hK : IsCompact K)
    (finishRest : ∀ {Y : CMfd.{0} n} {D : Set Y}, IsClosedSubmanifold n D →
      (∀ y ∈ D, ∃ e : Fin (n + 1), e ∈ ds ∧ RegularAtDim (n := n) D y e) →
      ∀ (B : List (Set Y)), IsSNCDivisor n B → (D ⊆ closure (D \ ⋃ H ∈ B, H)) →
        ∀ (L : Set Y), IsCompact L → LocalSmoothTowerWith (ordered_smooth_tail_certificate ds) D B L) :
    LocalSmoothTowerWith (ordered_smooth_tail_certificate (d :: ds)) W E K := by
  have hW : IsClosed W := by rw [hParts]; exact hA.1.union hB.1
  have hABDense : A ∪ B ⊆ closure ((A ∪ B) \ ⋃ H ∈ E, H) := by rwa [← hParts]
  have hBADense : B ∪ A ⊆ closure ((B ∪ A) \ ⋃ H ∈ E, H) := by rwa [union_comm B A]
  have hADense : A ⊆ closure (A \ ⋃ H ∈ E, H) :=
    dense_complement_left_of_disjoint hB.1 hSep hABDense
  have hBDense : B ⊆ closure (B \ ⋃ H ∈ E, H) :=
    dense_complement_left_of_disjoint hA.1 hSep.symm hBADense
  have hPhase :
      ∃ V : Opens X, K ⊆ V ∧
        let XV := CMfd.of (n := n) V
        let AV : Set XV := (Subtype.val : V → X) ⁻¹' A
        let WV : Set XV := (Subtype.val : V → X) ⁻¹' W
        let EV : List (Set XV) := E.map ((Subtype.val : V → X) ⁻¹' ·)
        ∃ (Y : CMfd.{0} n) (T : BlowupTower XV Y) (hEV : IsSNCDivisor n EV),
          SmoothBoundaryTower AV EV T ∧ SmoothRankPhase WV EV hEV d T := by
    by_cases hlt : (d : ℕ) < n
    · obtain ⟨V, hKV, Y, T, hEV, hClean, hT⟩ :=
        pure_local_smooth_tower_with_cleanup hA hAPure hlt E hE hADense K hK
      have hDimV : dimensionPart (n := n) ((Subtype.val : V → X) ⁻¹' W) d =
          (Subtype.val : V → X) ⁻¹' A := by rw [dimensionPart_restrict, hDim]
      refine ⟨V, hKV, Y, T, hEV, hT, SmoothRankPhase.proper hlt ?_ ?_ ?_ ?_⟩
      · rw [hDimV]
        exact BlowupRestrictOpen.isClosedSubmanifold_preimage_val hA V
      · rw [hDimV]
        intro x hx
        exact AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr (hAPure x.val hx)
      · rw [hDimV]
        exact dense_complement_restrict A E hADense V
      · rw [hDimV]
        exact hClean
    · have hdEq : (d : ℕ) = n := le_antisymm (Nat.le_of_lt_succ d.isLt) (Nat.le_of_not_gt hlt)
      have hFull : ∀ x ∈ A, RegularAtDim (n := n) A x n := by
        intro x hx
        exact Eq.mp (congrArg (fun k : ℕ => RegularAtDim (n := n) A x k) hdEq) (hAPure x hx)
      let V : Opens X := ⊤
      have hEV : IsSNCDivisor n (E.map ((Subtype.val : V → X) ⁻¹' ·)) :=
        isSNCDivisor_map_preimage (pullsBackCoordinates_val V) continuous_subtype_val hE
      exact ⟨V, fun _ _ => trivial, CMfd.of (n := n) V, .refl, hEV,
        smooth_full_rank_cleanup hA hFull E hE, .ambient hdEq⟩
  obtain ⟨V, hKV, Y, T, hEV, hT, hRankT⟩ := hPhase
  let AV := (Subtype.val : V → X) ⁻¹' A
  let BV := (Subtype.val : V → X) ⁻¹' B
  let WV := (Subtype.val : V → X) ⁻¹' W
  let EV := E.map ((Subtype.val : V → X) ⁻¹' ·)
  let MV := geometricTemplate (univ : Set (CMfd.of (n := n) V)) EV
  let KV := (Subtype.val : V → X) ⁻¹' K
  let F := AV ∩ ⋃ H ∈ EV, H
  let A₁ := strictTransform n T.proj AV
  let B₁ := strictTransform n T.proj BV
  let E₁ := (geoTransformAlong MV T).E
  let K₁ := T.proj ⁻¹' KV
  have hWV : WV = AV ∪ BV := by dsimp only [WV,AV,BV]; rw [hParts, preimage_union]
  have hAV : IsClosed AV := hA.1.preimage continuous_subtype_val
  have hBV : IsClosedSubmanifold n BV := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hB V
  have hSepV : Disjoint AV BV := disjoint_left.mpr fun x hxA hxB => disjoint_left.mp hSep hxA hxB
  have hF : IsClosed F := hAV.inter (isClosed_biUnion_of_forall_isClosed hEV.1)
  obtain ⟨hProjB, hB₁, hSep₁, hReg, hDenseB, _⟩ := protected_smooth_part hAV hBV hSepV hF
    inter_subset_left MV hEV.1 T hT.test hT.footprint
  have hB₁Ranks : ∀ y ∈ B₁, ∃ e : Fin (n + 1), e ∈ ds ∧ RegularAtDim (n := n) B₁ y e := by
    intro y hy
    have hyV : y ∈ T.proj ⁻¹' BV := hProjB ▸ hy
    obtain ⟨e, he, hyReg⟩ := hBRanks (T.proj y).val hyV
    exact ⟨e, he, hReg y e (AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hyReg)⟩
  have hKVC : IsCompact KV := by
    rw [Subtype.isCompact_iff, image_preimage_eq_inter_range, Subtype.range_coe, inter_eq_left.mpr hKV]
    exact hK
  have hK₁C : IsCompact K₁ := (HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage hKVC
  have hBVDense : BV ⊆ closure (BV \ ⋃ H ∈ EV, H) := dense_complement_restrict B E hBDense V
  obtain ⟨P, hKP, Z, Q, hQ, hRankQ⟩ := finishRest (Y := Y) (D := B₁) hB₁ hB₁Ranks E₁ hT.snc
    (hDenseB hBVDense) K₁ hK₁C
  have hSepP : Disjoint ((Subtype.val : P → Y) ⁻¹' B₁) ((Subtype.val : P → Y) ⁻¹' A₁) :=
    disjoint_left.mpr fun _ hb ha => disjoint_left.mp hSep₁ ha hb
  have hEP := isSNCDivisor_map_preimage (pullsBackCoordinates_val P) continuous_subtype_val hT.snc
  have hQwhole := SmoothBoundaryTower.union_of_protected
    (hB₁.1.preimage (continuous_subtype_val : Continuous (Subtype.val : P → Y)))
    (BlowupRestrictOpen.isClosedSubmanifold_preimage_val hT.smooth P) hSepP hEP
    (hasNormalCrossings_preimage (pullsBackCoordinates_val P) hT.nc) hQ
  have hRead : (Subtype.val : P → Y) ⁻¹' strictTransform n T.proj WV =
      (Subtype.val : P → Y) ⁻¹' B₁ ∪ (Subtype.val : P → Y) ⁻¹' A₁ := by
    rw [hWV, strictTransform_union T.proj AV BV, preimage_union]
    exact union_comm _ _
  have hLocal : LocalSmoothTowerWithCarriers (ordered_smooth_tail_certificate ds)
      (strictTransform n T.proj WV) B₁ E₁ K₁ :=
    ⟨P, hKP, Z, Q, hRead.symm ▸ hQwhole, hRankQ⟩
  have hFA : F ⊆ AV := inter_subset_left
  have hTA : IsGeoTestTower MV T := hT.test
  have hTF : CentresOver F T := hT.footprint
  have hTStage : SmoothBoundaryStages AV EV T := hT.stages
  have hEnlarged : SmoothBoundaryStages (AV ∪ BV) EV T :=
    smoothBoundaryStages_union_of_protected (X := CMfd.of (n := n) V) (A := AV) (B := BV) (F := F)
      hAV hBV hSepV hF hFA EV hEV T hTA hTF hTStage
  have hOldStages : SmoothBoundaryStages WV EV T := hWV.symm ▸ hEnlarged
  have hFoot : F ⊆ WV ∩ ⋃ H ∈ EV, H := by
    intro x hx
    have hxW : x ∈ WV := by rw [hWV]; exact Or.inl hx.1
    exact ⟨hxW, hx.2⟩
  have hWVClosed : IsClosed WV := hW.preimage continuous_subtype_val
  have hOldFoot : CentresOver (WV ∩ ⋃ H ∈ EV, H) T := centresOver_mono_local hFoot T hT.footprint
  have hRemV : WV \ dimensionPart (n := n) WV d = BV := by
    have hPart : dimensionPart (n := n) WV d = AV := by
      dsimp only [WV, AV]
      rw [dimensionPart_restrict, hDim]
    rw [hPart, hWV]
    ext x
    constructor
    · rintro ⟨hx, hn⟩
      change x ∈ AV ∨ x ∈ BV at hx
      exact hx.resolve_left hn
    · intro hx
      exact ⟨Or.inr hx, fun ha => disjoint_left.mp hSepV ha hx⟩
  have hLocal' : LocalSmoothTowerWithCarriers (ordered_smooth_tail_certificate ds)
      (strictTransform n T.proj WV) (strictTransform n T.proj (WV \ dimensionPart (n := n) WV d)) E₁ K₁ := by
    rw [hRemV]
    exact hLocal
  exact append_and_flatten_retained_phase hW E hE d ds K V hKV T hEV hTA hOldFoot hOldStages hRankT
    (hRemV.symm ▸ hBV.1) hLocal'

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
/-- The supplied rank list is processed in its literal order. Every rank's actual stopped or
identity history remains paired with the same geometric cleanup on the resulting open. -/
theorem local_mixed_smooth_boundary_cleanup_list {n : ℕ} :
    ∀ (ds : List (Fin (n + 1))), ds.Nodup → ∀ {X : CMfd.{0} n} {W : Set X},
      IsClosedSubmanifold n W →
      (∀ x ∈ W, ∃ d : Fin (n + 1), d ∈ ds ∧ RegularAtDim (n := n) W x d) →
      ∀ (E : List (Set X)), IsSNCDivisor n E → (W ⊆ closure (W \ ⋃ H ∈ E, H)) →
        ∀ (K : Set X), IsCompact K → LocalSmoothTowerWith (ordered_smooth_tail_certificate ds) W E K := by
  classical
  intro ds
  induction ds with
  | nil =>
    intro _ X W hW hRank E hE hDense K hK
    have hEmpty : W = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx => by
      obtain ⟨d, hd, _⟩ := hRank x hx
      exact List.not_mem_nil hd
    have hNC : HasNormalCrossings n W E := by rw [hEmpty]; exact fun _ h => h.elim
    let U : Opens X := ⊤
    exact ⟨U, fun _ _ => trivial, CMfd.of (n := n) U, .refl, smooth_unchanged_cleanup hW E hE hNC, .nil _ _⟩
  | cons d ds ih =>
    intro hds X W hW hRanks E hE hDense K hK
    have hn := List.nodup_cons.mp hds
    have hd : d ∉ ds.toFinset := by simpa using hn.1
    have hRanks' : ∀ x ∈ W, ∃ e : Fin (n + 1), e ∈ insert d ds.toFinset ∧ RegularAtDim (n := n) W x e := by
      intro x hx
      obtain ⟨e, he, hReg⟩ := hRanks x hx
      exact ⟨e, by simpa only [Finset.mem_insert, List.mem_toFinset, List.mem_cons] using he, hReg⟩
    obtain ⟨hParts, hSep, hA, hB, hAPure, hBRanks⟩ := split_smooth_dimensions hW d ds.toFinset hd hRanks'
    exact follow_dimension_phase ds rfl hParts hSep hA hB hAPure
      (by simpa only [List.mem_toFinset] using hBRanks) E hE hDense K hK (ih hn.2)

/-- The previous finite-set API is the geometric projection of the rank-retaining producer. -/
theorem local_mixed_smooth_boundary_cleanup_finset {n : ℕ}
    (s : Finset (Fin (n + 1))) {X : CMfd.{0} n} {W : Set X}
    (hW : IsClosedSubmanifold n W)
    (hRanks : ∀ x ∈ W, ∃ d : Fin (n + 1), d ∈ s ∧ RegularAtDim (n := n) W x d)
    (E : List (Set X)) (hE : IsSNCDivisor n E) (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (K : Set X) (hK : IsCompact K) : LocalSmoothTower W E K := by
  obtain ⟨O, hKO, Y, T, hT, _⟩ :=
    local_mixed_smooth_boundary_cleanup_list (s.sort (· ≤ ·)) (s.sort_nodup _) hW
      (by simpa only [Finset.mem_sort] using hRanks) E hE hDense K hK
  exact ⟨O, hKO, Y, T, hT⟩

/-- A compact task is served by one actual smooth suffix and its complete ascending rank tape. -/
theorem local_mixed_smooth_boundary_cleanup_ordered {n : ℕ} {X : CMfd.{0} n}
    {W : Set X} (hW : IsClosedSubmanifold n W)
    (E : List (Set X)) (hE : IsSNCDivisor n E) (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (K : Set X) (hK : IsCompact K) :
    LocalSmoothTowerWith (ascending_smooth_tail_certificate n) W E K := by
  apply local_mixed_smooth_boundary_cleanup_list (List.finRange (n + 1)) (List.nodup_finRange _) hW ?_ E hE hDense K hK
  intro x hx
  obtain ⟨d, hd⟩ := hW.2 x hx
  exact ⟨⟨d, Nat.lt_succ_of_le hd.1⟩, List.mem_finRange _, hd⟩

/-- The original mixed endpoint retains its existing public statement. -/
theorem local_mixed_smooth_boundary_cleanup {n : ℕ} {X : CMfd.{0} n}
    {W : Set X} (hW : IsClosedSubmanifold n W)
    (E : List (Set X)) (hE : IsSNCDivisor n E) (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (K : Set X) (hK : IsCompact K) : LocalSmoothTower W E K := by
  obtain ⟨O, hKO, Y, T, hT, _⟩ := local_mixed_smooth_boundary_cleanup_ordered hW E hE hDense K hK
  exact ⟨O, hKO, Y, T, hT⟩

end
end Hironaka.HironakaG8LocalMixedSmoothCleanup
