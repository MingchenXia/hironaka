import Hironaka.Resolution.HironakaG8PrincipalPrefixCompactClipping
import Hironaka.Resolution.HironakaG8ProfileOpenProtection
import Hironaka.Resolution.HironakaG8PrincipalEpochLabels

/-! Select a principal compact-fibre anchor and retain its physical prefix. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8PrincipalCompactAnchor
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal MarkedIdealRestrictOpen
  ResolutionInvariantSpec CanonicalCentres NonmonomialOrderLocal NonmonomialOrderRegime
  HironakaLocalPrincipalization HironakaEmbeddedAnalytic HironakaBaseChange
  HironakaNormalCrossingsOpenRestrictionSeparation HironakaActualOpenEmbeddingVanishingIdeal
  HironakaG8PrincipalEpochSuccession HironakaG8PrincipalPrefixCompactClipping
  HironakaG8NativePhaseCertificate HironakaG8OccupiedAtlasRestart
  HironakaG8FiniteSingularTowerMerge AnalyticDimensionBasics HironakaG8PrincipalRetainedEpochFinite
  HironakaActualCompactHSMaximalProfile HironakaG8ProfileOpenProtection
  HironakaG1RHypersurfaceRecord HironakaG8PrincipalEpochLabels HironakaHolomorphicJetChartInvariance
  HironakaActualVanishingIntrinsicHSTransport HironakaResolutionSpaceLocal GermIdealOrder
  HironakaHypersurfaceStageCenters HironakaHypersurfaceMultiplicityDescent
  MarkedIdealTowerTransport MaxLocusLocal

variable {n : ℕ} {X Y : CMfd.{0} (n+1)}

private abbrev whole {A : CMfd.{0} (n+1)} (W : Set A) (E : List (Set A)) (q : ℕ) :
    MarkedIdeal (n+1) A := ⟨univ,E,vanishingIdeal (n := n+1) W,q⟩

/-- A geometric restriction retains all principal prefix data, including
the intrinsic strict residual and its witness against each inherited factor. -/
theorem principalPrefixState_restrict
    (W : Set X) (E : List (Set X)) (hM : IsInvDomain (n+1) (whole W E 1))
    (P : BlowupTower X Y) {cap : ℕ} (hP : PrincipalPrefixState (whole W E 1) W P cap)
    (V : Opens X) :
    let WO := (Subtype.val : V → X) ⁻¹' W
    let EO := E.map ((Subtype.val : V → X) ⁻¹' ·)
    PrincipalPrefixState (whole (A := CMfd.of (n := n+1) V) WO EO 1) WO (restrict V P) cap := by
  dsimp only
  let M := whole W E 1
  let U := strictTransform (n+1) P.proj W
  let J := openPreimage P V
  let WO := (Subtype.val : V → X) ⁻¹' W
  let EO := E.map ((Subtype.val : V → X) ⁻¹' ·)
  let MV := whole (A := CMfd.of (n := n+1) V) WO EO 1
  let L := restrict V P
  let R := canonicalInvariant.{0} (n+1)
  have hTest := R.isInvValue.isGeoTestTower_of_isCanonical hM P hP.canonical
  have hRec : MarkedIdeal.pullback (Subtype.val : V → X) M = MV :=
    HironakaEmbeddedBoundary.pullback_val_mk_vanishingIdeal V E W
  have hStrict : strictTransform (n+1) L.proj WO = (Subtype.val : J → Y) ⁻¹' U :=
    strictTransform_restricted_tower V P W
  have hL : geoTransformAlong MV L =
      MarkedIdeal.pullback (Subtype.val : J → Y) (geoTransformAlong M P) := by
    rw [← hRec]
    exact geoTransformAlong_restrict V hM.isWellFormed.isClosedSubmanifold_N
      hM.isWellFormed.isCoherent P hTest
  change PrincipalPrefixState MV WO L cap
  refine ⟨?_,singular_stages_restrict W V P hP.singular,?_,?_,?_,?_,?_⟩
  · rw [← hRec]
    exact Seq.ResolutionInvariantExt.isCanonical_restrict R hM V P hP.canonical
  · intro r hr
    rw [← hRec]
    exact centresOrdGt_restrict_canonical M hM V r P hTest (hP.higher r hr)
  · rw [← hRec]
    exact prefix_residual_restrict M hM W V P hTest hP.residual
  · rw [hStrict,← pullback_vanishingIdeal_of_isOpenHoloEmbedding _ (isOpenHoloEmbedding_val J) U]
    apply GermIdealTotalTransform.isInvertible_pullback contMDiff_subtype_val _ hP.invertible
    rw [(isOpenHoloEmbedding_val J).exceptionalLocus_eq_empty,interior_empty]
  · rw [hStrict]
    intro x j hx
    exact hP.pure x.val j (AnalyticSubsetOpens.regularAtDim_preimage_val_iff.1 hx)
  · rw [hStrict,hL]
    exact whole_noFactor_open U (geoTransformAlong M P).E 1 hP.noFactor J

private theorem order_two_of_principal_singular (U : Set Y)
    (hU : IsClosed U) (hI : (vanishingIdeal (n := n+1) U).IsInvertible)
    {a : Y} (ha : a ∈ singularSet (n := n+1) U) :
    (2 : ℕ∞) ≤ order (n+1) univ (vanishingIdeal (n := n+1) U) a := by
  obtain ⟨haU,hReg⟩ := mem_singularSet_iff.mp ha
  by_contra h
  exact hReg n (regularAtDim_of_order_lt_two_of_isInvertible hU hI haU (lt_of_not_ge h))

/-- A strict label bound survives every point in the serviced compact
fibre. Points on the serviced level use the actual phase's strict drop. -/
theorem native_phase_strict_profile_bound_on_fibre
    (U : Set X) (E : List (Set X)) (H : ℕ → ℕ)
    (P : BlowupTower X Y) (hP : ActualNativePhase U E H P)
    (K : Set X)
    (hUpper : ∀ x ∈ K, toLex (hilbertSamuelAt (vanishingIdeal (n := n+1) U) x) ≤ toLex H) :
    ∀ z ∈ P.proj ⁻¹' K,
      toLex (hilbertSamuelAt (vanishingIdeal (n := n+1) (strictTransform (n+1) P.proj U)) z) < toLex H := by
  intro z hz
  by_cases he : hilbertSamuelAt (vanishingIdeal (n := n+1) U) (P.proj z) = H
  · exact hP.strictDrop z he
  · exact (Pi.toLex_monotone (hP.nonincrease z)).trans_lt
      (lt_of_le_of_ne (hUpper _ hz) (fun hh => he (congrArg ofLex hh)))


/-- A compact nonempty singular fibre selects its own highest principal
label. Its weak bound extends to every point of the saturated base open. -/
theorem exists_principal_anchor_on_compact_fibre
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (E : List (Set X)) (P : BlowupTower X Y) {cap : ℕ}
    (hP : PrincipalPrefixState (whole W E 1) W P cap)
    (K : Set X) (hK : IsCompact K) :
    let U := strictTransform (n+1) P.proj W
    let F := P.proj ⁻¹' K ∩ singularSet (n := n+1) U
    F.Nonempty →
    (∀ x ∈ F, order (n+1) univ (vanishingIdeal (n := n+1) U) x < (cap : ℕ∞)) →
    ∃ a ∈ F, ∃ q : ℕ, 2 ≤ q ∧ q < cap ∧
      order (n+1) univ (vanishingIdeal (n := n+1) U) a = q ∧
      ∃ V : Opens X, K ⊆ V ∧
        ∀ x ∈ openPreimage P V, toLex (hilbertSamuelAt (vanishingIdeal (n := n+1) U) x) ≤
          toLex (hilbertSamuelAt (vanishingIdeal (n := n+1) U) a) := by
  dsimp only
  intro hNe hCap
  let U := strictTransform (n+1) P.proj W
  let F := P.proj ⁻¹' K ∩ singularSet (n := n+1) U
  let I := vanishingIdeal (n := n+1) U
  have hU : IsComplexAnalyticSubset (n := n+1) U :=
    HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hW P
  have hProp := isProperMap_proj P
  have hComp : IsCompact F := (hProp.isCompact_preimage hK).inter_right (isClosed_singularSet hU.isClosed)
  obtain ⟨a,ha,hMax⟩ :=
    exists_actual_compact_hs_lex_maximum I (CartanIrreducible.cartanCoherence U hU) F hComp hNe
  obtain ⟨q,hq,_⟩ := exists_order_hilbertSamuelAt_eq_hypersurfaceHS I hP.invertible a
  have hq2 := order_two_of_principal_singular U hU.isClosed hP.invertible ha.2
  have hqc := hCap a ha
  change (2 : ℕ∞) ≤ order (n+1) univ I a at hq2
  change order (n+1) univ I a < (cap : ℕ∞) at hqc
  rw [hq] at hq2 hqc
  have hqTwo : 2 ≤ q := by exact_mod_cast hq2
  have hqCap : q < cap := by exact_mod_cast hqc
  obtain ⟨V,hKV,_,hBound⟩ := exists_open_singular_hs_profile_upper_bound hProp hU
    (hilbertSamuelAt I a) K ⊤ (by simp) hMax
  refine ⟨a,ha,q,hqTwo,hqCap,hq,V,hKV,?_⟩
  intro x hx
  apply le_of_not_gt
  intro hHigher
  have ho := (principal_profile_lt_iff_order_lt I I hP.invertible hP.invertible a x).1 hHigher
  have hTwo : (2 : ℕ∞) ≤ order (n+1) univ I x := hq2.trans (hq ▸ ho).le
  have hTwoGE := (le_order_iff (𝔞 := I) (fun _ hg => hg.1) (q := 2)).1 hTwo
  have hxU := cosupport_high_mark_subset_diff_regularLocus hU.isClosed (Nat.lt_succ_self n)
    (Nat.le_refl 2) (show x ∈ cosupport (n+1) univ I 2 from ⟨mem_univ _,hTwoGE⟩)
  have hxSing : x ∈ singularSet (n := n+1) U := by
    apply mem_singularSet_iff.mpr
    refine ⟨hxU.1,?_⟩
    intro d hd
    have hd' := hP.pure x d hd
    subst d
    exact hxU.2 hd
  exact (not_lt_of_ge (hBound x ⟨hx,hxSing⟩)) hHigher

/-- A strict bound by the preceding serviced principal profile supplies
the chronological cap at each point of the next compact fibre. -/
theorem principal_fibre_below_cap_of_profile_drop
    {Z : CMfd.{0} (n+1)} (U : Set Y) (U₀ : Set Z) (a₀ : Z) (cap : ℕ)
    (hI : (vanishingIdeal (n := n+1) U).IsInvertible)
    (hI₀ : (vanishingIdeal (n := n+1) U₀).IsInvertible)
    (ha₀ : order (n+1) univ (vanishingIdeal (n := n+1) U₀) a₀ = cap)
    (x : Y)
    (hLt : toLex (hilbertSamuelAt (vanishingIdeal (n := n+1) U) x) <
      toLex (hilbertSamuelAt (vanishingIdeal (n := n+1) U₀) a₀)) :
    order (n+1) univ (vanishingIdeal (n := n+1) U) x < (cap : ℕ∞) := by
  rw [← ha₀]
  exact (principal_profile_lt_iff_order_lt _ _ hI hI₀ x a₀).1 hLt


/-- A serviced principal label strictly lowers the actual ordinary order
everywhere on the serviced fibre, when both reduced ideals are invertible. -/
theorem native_phase_principal_order_strict_on_fibre
    (U : Set X) (E : List (Set X)) (a : X) (cap : ℕ)
    (hI : (vanishingIdeal (n := n+1) U).IsInvertible)
    (hOrd : order (n+1) univ (vanishingIdeal (n := n+1) U) a = cap)
    (P : BlowupTower X Y)
    (hPhase : ActualNativePhase U E (hilbertSamuelAt (vanishingIdeal (n := n+1) U) a) P)
    (hEnd : (vanishingIdeal (n := n+1) (strictTransform (n+1) P.proj U)).IsInvertible)
    (K : Set X)
    (hUpper : ∀ x ∈ K, toLex (hilbertSamuelAt (vanishingIdeal (n := n+1) U) x) ≤
      toLex (hilbertSamuelAt (vanishingIdeal (n := n+1) U) a)) :
    ∀ z ∈ P.proj ⁻¹' K,
      order (n+1) univ (vanishingIdeal (n := n+1) (strictTransform (n+1) P.proj U)) z <
        (cap : ℕ∞) := by
  intro z hz
  exact principal_fibre_below_cap_of_profile_drop _ U a cap hEnd hI hOrd z
    (native_phase_strict_profile_bound_on_fibre U E _ P hPhase K hUpper z hz)

/-- A compact nonempty principal singular fibre serves its own next
label. The same inherited physical prefix is restricted twice, first
for the profile bound and then for the actual produced phase. -/
theorem exists_compact_principal_continuation_of_singular_fibre
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (E : List (Set X)) (hM : IsInvDomain (n+1) (whole W E 1))
    (P : BlowupTower X Y) {cap : ℕ} (hP : PrincipalPrefixState (whole W E 1) W P cap)
    (K : Set X) (hK : IsCompact K) :
    let U := strictTransform (n+1) P.proj W
    let F := P.proj ⁻¹' K ∩ singularSet (n := n+1) U
    F.Nonempty →
    (∀ x ∈ F, order (n+1) univ (vanishingIdeal (n := n+1) U) x < (cap : ℕ∞)) →
    ∃ a ∈ F, ∃ q : ℕ, 2 ≤ q ∧ q < cap ∧
      order (n+1) univ (vanishingIdeal (n := n+1) U) a = q ∧
      ∃ (V : Opens X), K ⊆ V ∧
      let WO := (Subtype.val : V → X) ⁻¹' W
      let EO := E.map ((Subtype.val : V → X) ⁻¹' ·)
      let MV := whole (A := CMfd.of (n := n+1) V) WO EO 1
      let L := restrict V P
      let J := openPreimage P V
      let K' := (Subtype.val : V → X) ⁻¹' K
      let U' := strictTransform (n+1) L.proj WO
      let E' := (geoTransformAlong MV L).E
      ∃ H : ℕ → ℕ, H = hilbertSamuelAt (vanishingIdeal (n := n+1) U) a ∧
      ∃ (O : Opens J), L.proj ⁻¹' K' ⊆ O ∧
        ∃ (Z : CMfd.{0} (n+1)) (S : BlowupTower (CMfd.of (n := n+1) O) Z),
        let UO := (Subtype.val : O → J) ⁻¹' U'
        let BO := E'.map ((Subtype.val : O → J) ⁻¹' ·)
        ActualNativePhase (X := CMfd.of (n := n+1) O) UO BO H S ∧
        HasExactCoveredNativeAtlas UO BO H S (whole (A := CMfd.of (n := n+1) O) UO BO q) ∧
        ∃ (V' : Opens V), K' ⊆ V' ∧ ∃ (hVO : openPreimage L V' ≤ O),
          let D := nestedOpens O (openPreimage L V')
          let e := (nestedOpensDiffeo (n := n+1) hVO).symm
          let T := (restrict V' L).append (transport e (restrict D S)).tower
          let M' := MarkedIdeal.pullback (Subtype.val : V' → V) MV
          PrincipalPrefixState M' ((Subtype.val : V' → V) ⁻¹' WO) T q := by
  dsimp only
  intro hNe hBelow
  let U := strictTransform (n+1) P.proj W
  obtain ⟨a,ha,q,hq,hqc,hOrd,V,hKV,hHighest⟩ :=
    exists_principal_anchor_on_compact_fibre W hW E P hP K hK hNe hBelow
  let J := openPreimage P V
  let WO := (Subtype.val : V → X) ⁻¹' W
  let EO := E.map ((Subtype.val : V → X) ⁻¹' ·)
  let MV := whole (A := CMfd.of (n := n+1) V) WO EO 1
  let L := restrict V P
  let U' := strictTransform (n+1) L.proj WO
  let K' := (Subtype.val : V → X) ⁻¹' K
  let a' : J := ⟨a,hKV ha.1⟩
  have hK' : IsCompact K' :=
    (Topology.IsInducing.subtypeVal.isCompact_preimage_iff
      (fun x hx => ⟨⟨x,hKV hx⟩,rfl⟩)).mpr hK
  have hWO := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW V
  have hMO : MarkedIdeal.pullback (Subtype.val : V → X) (whole W E 1) = MV :=
    HironakaEmbeddedBoundary.pullback_val_mk_vanishingIdeal V E W
  have hM' : IsInvDomain (n+1) MV :=
    hMO ▸ InvDomainTowerAlong.isInvDomain_pullback_val V hM
  have hP' : PrincipalPrefixState MV WO L cap := principalPrefixState_restrict W E hM P hP V
  have hU' : U' = (Subtype.val : J → Y) ⁻¹' U := strictTransform_restricted_tower V P W
  have hSing : a' ∈ singularSet (n := n+1) U' := by
    rw [hU',singularSet_preimage_val J]
    exact ha.2
  have hRead (x : J) : hilbertSamuelAt (vanishingIdeal (n := n+1) U') x =
      hilbertSamuelAt (vanishingIdeal (n := n+1) U) x.val := by
    rw [hU']
    exact funext (hilbertSamuelAt_vanishing_actual_open_any J U x)
  have hInv' : (vanishingIdeal (n := n+1) U').IsInvertible := hP'.invertible
  have hOrd' : order (n+1) univ (vanishingIdeal (n := n+1) U') a' = q := by
    obtain ⟨r,hr,hR⟩ := exists_order_hilbertSamuelAt_eq_hypersurfaceHS
      (vanishingIdeal (n := n+1) U') hInv' a'
    obtain ⟨s,hs,hS⟩ := exists_order_hilbertSamuelAt_eq_hypersurfaceHS
      (vanishingIdeal (n := n+1) U) hP.invertible a
    have hrs : r = s := eq_of_hypersurfaceHS_eq (n+1)
      (fun k => (hR k).symm.trans ((congrFun (hRead a') k).trans (hS k)))
    rw [hr,hrs,← hs,hOrd]
  have hMax' (x : J) : toLex (hilbertSamuelAt (vanishingIdeal (n := n+1) U') x) ≤
      toLex (hilbertSamuelAt (vanishingIdeal (n := n+1) U') a') := by
    rw [hRead x,hRead a']
    exact hHighest x.val x.property
  have hResult := exists_compact_principal_canonical_continuation
    (X := CMfd.of (n := n+1) V) (Y := CMfd.of (n := n+1) J) WO hWO EO hM' L hP'
      K' hK' a' q hq hqc hSing hOrd' hMax'
  refine ⟨a,ha,q,hq,hqc,hOrd,V,hKV,_,hRead a',?_⟩
  exact hResult

end
end Hironaka.HironakaG8PrincipalCompactAnchor
