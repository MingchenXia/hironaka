import Hironaka.Resolution.HironakaG8PrincipalExactRelativeClearing
import Hironaka.Resolution.HironakaG8PrincipalEpochSuccession
import Hironaka.Resolution.HironakaG8SaturatedPrefixAppend

/-! Clip an occupied principal prefix by saturation of the compact base task. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8PrincipalPrefixCompactClipping
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal MarkedIdealRestrictOpen
  ResolutionInvariantSpec CanonicalCentres NonmonomialOrderLocal NonmonomialOrderRegime
  HironakaLocalPrincipalization HironakaEmbeddedAnalytic HironakaBaseChange
  HironakaNormalCrossingsOpenRestrictionSeparation HironakaActualOpenEmbeddingVanishingIdeal
  HironakaG8PrincipalEpochSuccession HironakaG8PrincipalExactRelativeClearing
  HironakaG8NativePhaseCertificate HironakaG8OccupiedAtlasRestart
  HironakaG8OccupiedRetainedRestart AnalyticDimensionBasics HironakaSharpActualChronologicalResidualDictionary

variable {n : ℕ} {X Y : CMfd.{0} (n+1)}

theorem centresOrdGt_restrict_canonical (M : MarkedIdeal (n+1) X)
    (hM : IsInvDomain (n+1) M) (V : Opens X) (r : ℕ)
    (P : BlowupTower X Y) (hT : IsGeoTestTower M P)
    (hHigher : CentresOrdGt M r P) :
    CentresOrdGt (MarkedIdeal.pullback (Subtype.val : V → X) M) r (restrict V P) := by
  induction P with
  | refl => trivial
  | step P C π hπ ih =>
    refine ⟨ih hT.1 hHigher.1,?_⟩
    intro z hz
    have hD := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM P hT.1
    rw [geoTransformAlong_restrict V hM.isWellFormed.isClosedSubmanifold_N
      hM.isWellFormed.isCoherent P hT.1]
    exact (mem_ordGe_pullback_val_iff (Nat.succ_pos n) hD.isWellFormed hD.isNonzeroAlongAt
      (openPreimage P V) (r+1) z).2 (hHigher.2 hz)

open NonmonomialTransformAlong MonomialPartAlong

/-- The original nonmonomial residual follows the actual strict carrier
on a saturated literal restriction of a canonical prefix. -/
theorem prefix_residual_restrict (M : MarkedIdeal (n+1) X) (hM : IsInvDomain (n+1) M)
    (W : Set X) (V : Opens X) (P : BlowupTower X Y) (hT : IsGeoTestTower M P)
    (hResidual : nmPart (geoTransformAlong M P) = vanishingIdeal (n := n+1)
      (strictTransform (n+1) P.proj W)) :
    nmPart (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : V → X) M) (restrict V P)) =
      vanishingIdeal (n := n+1)
        (strictTransform (n+1) (restrict V P).proj ((Subtype.val : V → X) ⁻¹' W)) := by
  let A := geoTransformAlong M P
  let O := openPreimage P V
  let f := (Subtype.val : O → Y)
  have hA : IsInvDomain (n+1) A := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM P hT
  have hw := hA.isWellFormed
  have hmon := isCoherent_monomialPartAlong (Nat.succ_pos n) hw.isClosedSubmanifold_N
    hw.isSNCDivisor hw.isTransverse hw.isCoherent hA.isNonzeroAlongAt
  have hnm := isCoherent_nonmonomialPartAlong (Nat.succ_pos n) hw.isClosedSubmanifold_N
    hw.isSNCDivisor hw.isTransverse hw.isCoherent hA.isNonzeroAlongAt
  have hPull : GermIdeal.pullback (m := n+1) f (nmPart A) =
      nmPart (M := CMfd.of (n := n+1) O) (MarkedIdeal.pullback f A) :=
    MonomialPartEtale.pullback_nonmonomialPartAlong
      (fun y => ⟨DerivativeIdealAlongEtale.openInv O y,DerivativeIdealAlongEtale.isLocalInverseAt_val O y⟩)
      hw.isCoherent hmon hnm
  rw [geoTransformAlong_restrict V hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent P hT,
    ← hPull, hResidual, strictTransform_restricted_tower]
  exact pullback_vanishingIdeal_of_isOpenHoloEmbedding f (isOpenHoloEmbedding_val O) _


open HironakaG8PrincipalRetainedEpochFinite
  RelativePrincipalizationSpan

private abbrev whole {A : CMfd.{0} (n+1)} (W : Set A) (E : List (Set A)) (q : ℕ) :
    MarkedIdeal (n+1) A := ⟨univ,E,vanishingIdeal (n := n+1) W,q⟩

/-- Each old boundary factor witness persists as a germ on any literal open. -/
theorem whole_noFactor_open (W : Set Y) (E : List (Set Y)) (q : ℕ)
    (h : HasNoBoundaryFactor (whole W E q)) (O : Opens Y) :
    HasNoBoundaryFactor (whole (A := CMfd.of (n := n+1) O)
      ((Subtype.val : O → Y) ⁻¹' W) (E.map ((Subtype.val : O → Y) ⁻¹' ·)) q) := by
  intro y _ i hy
  let j : Fin E.length := ⟨i.val,by simpa using i.isLt⟩
  have hSlot : (E.map ((Subtype.val : O → Y) ⁻¹' ·)).get i =
      (Subtype.val : O → Y) ⁻¹' E.get j := by
    simp [List.get_eq_getElem, j]
  change y ∈ (E.map ((Subtype.val : O → Y) ⁻¹' ·)).get i at hy
  rw [hSlot] at hy
  obtain ⟨g,hg,hNo⟩ := h y.val (mem_univ _) j hy
  refine ⟨g ∘ Subtype.val, ?_,?_⟩
  · exact (BlowupRestrictOpen.vanishingIdeal_opens_mem_iff O).mpr (by
      refine ⟨?_,?_⟩
      · exact hg.1.congr (by
          filter_upwards [O.isOpen.mem_nhds y.property] with z hz
          exact (extendOpens_val O (g ∘ Subtype.val) (⟨z,hz⟩ : O)).symm)
      · filter_upwards [O.isOpen.mem_nhds y.property,hg.2] with z hz hz' hzW
        exact (extendOpens_val O (g ∘ Subtype.val) (⟨z,hz⟩ : O)).trans (hz' hzW))
  · intro hs
    apply hNo
    change IsInSpanOnAt (n := n+1) univ
      ((vanishingIdeal (n := n+1) ((E.map ((Subtype.val : O → Y) ⁻¹' ·)).get i)).mem y) y
      (g ∘ Subtype.val) at hs
    rw [hSlot] at hs
    obtain ⟨k,s,a,hs,ha,he⟩ := hs
    refine ⟨k,fun i => extendOpens O (s i),fun i => extendOpens O (a i),
      fun i => (BlowupRestrictOpen.vanishingIdeal_opens_mem_iff O).mp (hs i),
      fun i => (holomorphicAt_iff_extendOpens O).mp (ha i),?_⟩
    exact (eventually_nhds_val_iff O).mpr (by
      filter_upwards [he] with z hz _
      simp only [extendOpens_val]
      exact hz (mem_univ _))


open NormalCrossings HironakaActualHSSingularBlowupRestart HironakaG8PrincipalEpochLabels
  HomogenizedIdealAlong BlowupTowerIsomorphism MarkedIdealTowerTransport MaxLocusLocal HironakaHolomorphicJetChartInvariance

private theorem pullback_whole_open {A : CMfd.{0} (n+1)} (O : Opens A)
    (W : Set A) (E : List (Set A)) (q : ℕ) :
    MarkedIdeal.pullback (Subtype.val : O → A) (whole W E q) = whole (A := CMfd.of (n := n+1) O)
      ((Subtype.val : O → A) ⁻¹' W) (E.map ((Subtype.val : O → A) ⁻¹' ·)) q :=
  MarkedIdealOperationsTransform.MarkedIdeal.ext_of preimage_univ rfl
    (pullback_vanishingIdeal_of_isOpenHoloEmbedding _ (isOpenHoloEmbedding_val O) W) rfl

/-- Produce the next principal native phase over the full compact inverse
image, then append its saturated restriction to the original chronological
canonical prefix. The returned native atlas and tail use that same phase. -/
theorem exists_compact_principal_canonical_continuation
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (E : List (Set X)) (hM : IsInvDomain (n+1) (whole W E 1))
    (P : BlowupTower X Y) {cap : ℕ} (hP : PrincipalPrefixState (whole W E 1) W P cap)
    (K : Set X) (hK : IsCompact K) (a : Y) (q : ℕ) (hq : 2 ≤ q) (hqcap : q < cap) :
    let M := whole W E 1
    let U := strictTransform (n+1) P.proj W
    let B := (geoTransformAlong M P).E
    let H := hilbertSamuelAt (vanishingIdeal (n := n+1) U) a
    a ∈ singularSet (n := n+1) U →
    GermIdealOrder.order (n+1) univ (vanishingIdeal (n := n+1) U) a = q →
    (∀ x, toLex (hilbertSamuelAt (vanishingIdeal (n := n+1) U) x) ≤ toLex H) →
    ∃ (O : Opens Y), P.proj ⁻¹' K ⊆ O ∧
      ∃ (Z : CMfd.{0} (n+1)) (S : BlowupTower (CMfd.of (n := n+1) O) Z),
      let UO := (Subtype.val : O → Y) ⁻¹' U
      let BO := B.map ((Subtype.val : O → Y) ⁻¹' ·)
      ActualNativePhase (X := CMfd.of (n := n+1) O) UO BO H S ∧
      HasExactCoveredNativeAtlas UO BO H S (whole (A := CMfd.of (n := n+1) O) UO BO q) ∧
      ∃ (V : Opens X), K ⊆ V ∧ ∃ (hVO : openPreimage P V ≤ O),
        let D := nestedOpens O (openPreimage P V)
        let e := (nestedOpensDiffeo (n := n+1) hVO).symm
        let T := (restrict V P).append (transport e (restrict D S)).tower
        let MV := MarkedIdeal.pullback (Subtype.val : V → X) M
        PrincipalPrefixState MV ((Subtype.val : V → X) ⁻¹' W) T q := by
  dsimp only
  intro ha hOrd hHighest
  let M := whole W E 1
  let A := geoTransformAlong M P
  let U := strictTransform (n+1) P.proj W
  let H := hilbertSamuelAt (vanishingIdeal (n := n+1) U) a
  let R := canonicalInvariant.{0} (n+1)
  have hTest := R.isInvValue.isGeoTestTower_of_isCanonical hM P hP.canonical
  have hAD := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM P hTest
  have hU := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hW P
  have hDense := actualPure_subset_closure_regularLocus hU hP.pure
  have hBase := HironakaEmbeddedReducible.isInvDomain_vanishingIdeal_of_pure le_rfl hU (Nat.lt_succ_self n) hDense
  let F := whole U A.E q
  have hF : IsInvDomain (n+1) F :=
    ⟨⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,hBase.isWellFormed.isCoherent,
      hAD.isWellFormed.isSNCDivisor,
      SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hAD.isWellFormed.isSNCDivisor⟩,
      hBase.dimLE,by change 1 ≤ q; omega,hBase.isNonzeroAlongAt⟩
  have hCap := principal_order_cap_of_maximal_profile F.ideal hP.invertible hF.isWellFormed.isCoherent a q
    hOrd hHighest
  have hNot : ∀ F ∈ A.E, ∀ x ∈ phaseLevel U H, x ∈ F →
      ¬ ∀ᶠ z in 𝓝 x, z ∈ F → z ∈ U := by
    intro B hB x _ hx hInside
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hB
    obtain ⟨g,hg,hNo⟩ := hP.noFactor x (mem_univ _) i hx
    apply hNo
    have hmem : (vanishingIdeal (n := n+1) (A.E.get i)).mem x g :=
      ⟨hg.1, by
        filter_upwards [hg.2,hInside] with z hz hz' hzB
        exact hz (hz' hzB)⟩
    exact IsInSpanOnAt.mono (fun f hf => (show f = g from hf).symm ▸ hmem)
      NonmonomialStepAlong.isInSpanOnAt_self_eq
  obtain ⟨O,hKO,Z,S,hPhase,hAtlas⟩ := exists_principal_exact_native_phase_near_compact
    U hU A.E hAD.isWellFormed.isSNCDivisor hP.invertible (P.proj ⁻¹' K)
    ((isProperMap_proj P).isCompact_preimage hK) a ha q hOrd hHighest hNot
  obtain ⟨V,hKV,hVO,_,hSing,_,_,_,_⟩ :=
    HironakaG8SaturatedPrefixAppend.exists_saturated_singular_phase_append hW E
      hM.isWellFormed.isSNCDivisor P hTest hP.singular K O hKO S hPhase.test hPhase.singular
  let J := openPreimage P V
  let D := nestedOpens O J
  let e := (nestedOpensDiffeo (n := n+1) hVO).symm
  let L := restrict V P
  let G := restrict D S
  let T := (transport e G).tower
  let MV := MarkedIdeal.pullback (Subtype.val : V → X) M
  let AO := MarkedIdeal.pullback (Subtype.val : O → Y) F
  let AJ := MarkedIdeal.pullback (Subtype.val : J → Y) F
  have hAO : IsInvDomain (n+1) AO := InvDomainTowerAlong.isInvDomain_pullback_val O hF
  have hCanO : IsCanonical AO (R.inv AO) S := by
    have he := pullback_whole_open O U A.E q
    change AO = _ at he
    rw [he] at hAO ⊢
    exact canonical_of_exact_covered_native_atlas _ _ H S _ hAO hAtlas
  have hCanD := Seq.ResolutionInvariantExt.isCanonical_restrict R hAO D S hCanO
  let AD := MarkedIdeal.pullback (Subtype.val : D → O) AO
  have hAD' : IsInvDomain (n+1) AD := InvDomainTowerAlong.isInvDomain_pullback_val D hAO
  have hTail := Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso R hAD' e
    (transport_isTowerIso e G) hCanD
  have hRec : MarkedIdeal.pullback e AD = AJ := by
    dsimp only [AD,AO,AJ]
    rw [pullback_whole_open (A := Y) O,
      pullback_whole_open (A := CMfd.of (n := n+1) O) D,
      pullback_whole_open (A := Y) J]
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · exact preimage_univ
    · change ((_ : List (Set D)).map ((e : J → D) ⁻¹' ·)) = _
      simp only [List.map_map]
      rfl
    · change GermIdeal.pullback (m := n+1) e (vanishingIdeal (n := n+1)
        ((Subtype.val : D → O) ⁻¹' ((Subtype.val : O → Y) ⁻¹' U))) = _
      rw [pullback_vanishingIdeal_of_biholomorphism]
      rfl
    · rfl
  rw [hRec] at hTail
  have hCanL := Seq.ResolutionInvariantExt.isCanonical_restrict R hM V P hP.canonical
  have hMD := InvDomainTowerAlong.isInvDomain_pullback_val V hM
  have hJ := InvDomainTowerAlong.isInvDomain_pullback_val J hF
  have hCapJ : IsMaximalOrderAlong AJ.N AJ.ideal AJ.d := by
    intro x hx
    let Q : MarkedIdeal (n+1) Y := {F with d := q+1}
    have hh : x ∈ (MarkedIdeal.pullback (Subtype.val : J → Y) Q).cosupp := hx
    rw [cosupp_pullback_val Q (fun _ _ hg => hg.1) J] at hh
    exact hCap x.val hh
  have hNoJ : HasNoBoundaryFactor (A := CMfd.of (n := n+1) J) AJ := by
    change HasNoBoundaryFactor (A := CMfd.of (n := n+1) J)
      (MarkedIdeal.pullback (Subtype.val : J → Y) (whole U A.E q))
    rw [pullback_whole_open]
    exact whole_noFactor_open U A.E q hP.noFactor J
  have hOld := centresOrdGt_restrict_canonical M hM V q P hTest (hP.higher q hqcap)
  have hL : geoTransformAlong MV L = MarkedIdeal.pullback (Subtype.val : J → Y) A :=
    geoTransformAlong_restrict V hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent P hTest
  have hAN : A.N = univ := (pullback_eq_mul_geoTransformAlong M rfl hM.isWellFormed.isCoherent P hTest).1
  have hN : (geoTransformAlong MV L).N = univ := by
    rw [hL]
    change (Subtype.val : J → Y) ⁻¹' A.N = univ
    rw [hAN,preimage_univ]
  have hE : (geoTransformAlong MV L).E = AJ.E := by rw [hL]; rfl
  have hD : (geoTransformAlong MV L).d ≤ AJ.d := by
    rw [hL]
    change A.d ≤ q
    rw [d_geoTransformAlong]
    change 1 ≤ q
    omega
  have hPart := prefix_residual_restrict M hM W V P hTest hP.residual
  have hExact : nmPart (geoTransformAlong MV L) = AJ.ideal := by
    rw [hPart,strictTransform_restricted_tower]
    exact (pullback_vanishingIdeal_of_isOpenHoloEmbedding _ (isOpenHoloEmbedding_val J) U).symm
  obtain ⟨hCAN,hHigh,hPartFinal⟩ := append_whole_canonical_of_principal_residual_epoch
    MV hMD L hCanL AJ hJ preimage_univ hNoJ hCapJ hOld T hTail hN hE hD hExact
  let UJ := (Subtype.val : J → Y) ⁻¹' U
  let WO := (Subtype.val : V → X) ⁻¹' W
  have hUL : strictTransform (n+1) L.proj WO = UJ := strictTransform_restricted_tower V P W
  have hUJ := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hU J
  have hInvJ : (vanishingIdeal (n := n+1) UJ).IsInvertible := by
    rw [← pullback_vanishingIdeal_of_isOpenHoloEmbedding _ (isOpenHoloEmbedding_val J) U]
    apply GermIdealTotalTransform.isInvertible_pullback contMDiff_subtype_val _ hP.invertible
    rw [(isOpenHoloEmbedding_val J).exceptionalLocus_eq_empty,interior_empty]
  have hPureJ : IsPureDim (n := n+1) UJ n := by
    intro x k hx
    exact hP.pure x.val k (AnalyticSubsetOpens.regularAtDim_preimage_val_iff.1 hx)
  have hAJ : AJ = whole (A := CMfd.of (n := n+1) J) UJ AJ.E q :=
    pullback_whole_open J U A.E q
  obtain ⟨hIdeal,hInv,hPure⟩ := principal_epoch_strict_ideal UJ hUJ hPureJ hInvJ AJ.E q hq
      AJ hAJ hJ hNoJ hCapJ T hTail
  let F' := geoTransformAlong AJ T
  have hTF := R.isInvValue.isGeoTestTower_of_isCanonical hJ T hTail
  have hFD := InvDomainTowerAlong.isInvDomain_geoTransformAlong hJ T hTF
  have hFN : F'.N = univ :=
    (pullback_eq_mul_geoTransformAlong AJ preimage_univ hJ.isWellFormed.isCoherent T hTF).1
  have hNo := no_boundary_factor_along_lower_native_epoch AJ hJ hNoJ hCapJ T hTail
  have hNonmon := nonmonomialPartAlong_eq_restrictOn_of_no_member_factor hFD.isWellFormed.1
    hFD.isWellFormed.3 hFD.isWellFormed.4 hFD.isWellFormed.2 hNo
  change nmPart F' = RestrictedIdealExtension.restrictOn (n+1) F'.N F'.ideal at hNonmon
  rw [hFN,BlowupTowerTransforms.restrictOn_univ hFD.isWellFormed.isCoherent] at hNonmon
  have hStrict : strictTransform (n+1) (L.append T).proj WO = strictTransform (n+1) T.proj UJ := by
    rw [BlowupTower.proj_append,StrictTransformComposition.strictTransform_comp
      L.contMDiff_proj T.contMDiff_proj,hUL]
  have hEF : (geoTransformAlong MV (L.append T)).E = F'.E := by
    rw [geoTransformAlong_append]
    exact HironakaCoherentTransformExtension.geoTransformAlong_E_eq_of_E_eq
      (𝔍 := geoTransformAlong MV L) (𝔪 := AJ) hE T
  refine ⟨O,hKO,Z,S,hPhase,hAtlas,V,hKV,hVO,?_⟩
  change PrincipalPrefixState MV WO (L.append T) q
  refine ⟨hCAN,hSing,hHigh,?_,?_,?_,?_⟩
  · rw [hPartFinal,hNonmon,hStrict]
    exact hIdeal
  · rwa [hStrict]
  · rwa [hStrict]
  · rw [hStrict,hEF]
    unfold HasNoBoundaryFactor at hNo ⊢
    change ∀ x ∈ univ, ∀ i : Fin F'.E.length, x ∈ F'.E.get i →
      ∃ g, (vanishingIdeal (n := n+1) (strictTransform (n+1) T.proj UJ)).mem x g ∧
        ¬ IsInSpanOnAt (n := n+1) univ ((vanishingIdeal (n := n+1) (F'.E.get i)).mem x) x g
    change F'.ideal = _ at hIdeal
    rwa [hFN,hIdeal] at hNo

end
end Hironaka.HironakaG8PrincipalPrefixCompactClipping
