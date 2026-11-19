import Hironaka.Resolution.HironakaG8PrincipalCompactRepeat
import Hironaka.Resolution.HironakaG8LocalMixedEmbeddedResolution
import Hironaka.Resolution.HironakaG8PrincipalCompactAnchor

/-! Terminal SNC cleanup after the compact canonical principal service. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8PrincipalCompactSNCFinish
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal MarkedIdealRestrictOpen
  ResolutionInvariantSpec CanonicalCentres HironakaEmbeddedAnalytic HironakaBaseChange
  HironakaG8PrincipalCompactRepeat HironakaG8PrincipalCompactAnchor
  HironakaG8PrincipalEpochSuccession HironakaG8LocalMixedEmbeddedResolution
  HironakaG8LocalMixedPhaseAssembly HironakaG8LocalMixedSmoothCleanup
  HironakaG8UniverseDenseBoundary HironakaActualSmoothBoundaryCleanup
  HironakaNormalCrossingsOpenRestrictionSeparation HironakaActualOpenEmbeddingVanishingIdeal
  HironakaLocalPrincipalization HironakaResolutionSpaceLocal HironakaG8LocalPureFinish
  HironakaG8OpenHoloEmbeddingComposition NormalCrossings

variable {n : ℕ} {X Y : CMfd.{0} (n+1)}
private abbrev whole {A : CMfd.{0} (n+1)} (W : Set A) (E : List (Set A)) : MarkedIdeal (n+1) A :=
  ⟨univ,E,vanishingIdeal (n := n+1) W,1⟩

private theorem whole_domain_open_embedding (W : Set X) (E : List (Set X))
    (hM : IsInvDomain (n+1) (whole W E)) (j : Y → X) (hj : IsOpenHoloEmbedding (n+1) j) :
    IsInvDomain (n+1) (whole (j ⁻¹' W) (E.map (j ⁻¹' ·))) := by
  obtain ⟨O,e,he⟩ := hj
  let M := whole W E
  let N := MarkedIdeal.pullback (Subtype.val : O → X) M
  have hN : IsInvDomain (n+1) N := InvDomainTowerAlong.isInvDomain_pullback_val O hM
  have hNe : N = whole (A := CMfd.of (n := n+1) O)
        ((Subtype.val : O → X) ⁻¹' W) (E.map ((Subtype.val : O → X) ⁻¹' ·)) :=
    HironakaEmbeddedBoundary.pullback_val_mk_vanishingIdeal O E W
  have hRec : MarkedIdeal.pullback e N = whole (j ⁻¹' W) (E.map (j ⁻¹' ·)) := by
    rw [hNe]
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · exact preimage_univ
    · change (E.map ((Subtype.val : O → X) ⁻¹' ·)).map (e ⁻¹' ·) = _
      rw [List.map_map]
      apply List.map_congr_left
      intro B _
      ext x
      exact Iff.of_eq (congrArg (fun y => y ∈ B) (he x).symm)
    · change GermIdeal.pullback (m := n+1) e
        (vanishingIdeal (n := n+1) ((Subtype.val : O → X) ⁻¹' W)) = _
      rw [pullback_vanishingIdeal_of_biholomorphism]
      apply congrArg (vanishingIdeal (n := n+1))
      ext x
      exact Iff.of_eq (congrArg (fun y => y ∈ W) (he x).symm)
    · rfl
  exact hRec ▸ InvDomainTowerAlong.isInvDomain_pullback e hN

/-- The compact task sees a smooth actual strict transform after
restricting the same physical terminal tower along a saturated base open. -/
theorem exists_smooth_restriction_of_empty_singular_fibre
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n+1) W)
    (P : BlowupTower X Y) (K : Set X)
    (hClear : Disjoint (P.proj ⁻¹' K) (singularSet (n := n+1) (strictTransform (n+1) P.proj W))) :
    ∃ O : Opens X, K ⊆ O ∧
      IsClosedSubmanifold (n+1) (strictTransform (n+1) (restrict O P).proj ((Subtype.val : O → X) ⁻¹' W)) := by
  let U := strictTransform (n+1) P.proj W
  let F := singularSet (n := n+1) U
  have hU := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hW P
  let O : Opens X := ⟨(P.proj '' F)ᶜ,
    ((isProperMap_proj P).isClosedMap _ (isClosed_singularSet hU.isClosed)).isOpen_compl⟩
  refine ⟨O,?_,?_⟩
  · intro x hx
    rintro ⟨y,hy,rfl⟩
    exact Set.disjoint_left.mp hClear hx hy
  · rw [strictTransform_restricted_tower]
    refine ⟨hU.isClosed.preimage continuous_subtype_val,?_⟩
    intro y hy
    have hn : y.val ∉ F := fun h => y.property ⟨y.val,h,rfl⟩
    have hr : ∃ k, RegularAtDim (n := n+1) U y.val k := by
      by_contra h
      apply hn
      exact mem_singularSet_iff.mpr ⟨hy,fun k hk => h ⟨k,hk⟩⟩
    obtain ⟨k,hk⟩ := hr
    exact ⟨k,AnalyticSubsetOpens.regularAtDim_preimage_val_iff.2 hk⟩


/-- The finite canonical principal trace admits a geometric SNC finish
on a restriction of its actual terminal physical prefix. The original
invariant remains canonical on the singular service part. -/
theorem CompactPrincipalServiceTrace.exists_snc_finish
    {W : Set X} {E : List (Set X)} (hW : IsComplexAnalyticSubset (n := n+1) W)
    (hM : IsInvDomain (n+1) (whole W E))
    (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    {P : BlowupTower X Y} {K : Set X} {cap : ℕ} {labels : List (ℕ × (ℕ → ℕ))}
    (hK : IsCompact K) (h : CompactPrincipalServiceTrace W E P K cap labels) :
    ∃ (A : CMfd.{0} (n+1)) (j : A → X), IsOpenHoloEmbedding (n+1) j ∧ K ⊆ range j ∧
      ∃ (B : CMfd.{0} (n+1)) (L : BlowupTower A B) (C : CMfd.{0} (n+1)) (R : BlowupTower B C),
        let U := j ⁻¹' W
        let F := E.map (j ⁻¹' ·)
        let M := whole (A := A) U F
        IsCanonical M ((canonicalInvariant (n+1)).inv M) L ∧
        IsClosedSubmanifold (n+1) (strictTransform (n+1) L.proj U) ∧
        DenseBoundaryResolution U F (L.append R) := by
  obtain ⟨A,j,hj,hKA,B,T,last,hState,hClear⟩ := h.endpoint
  let U := j ⁻¹' W
  let F := E.map (j ⁻¹' ·)
  let K' := j ⁻¹' K
  let M := whole (A := A) U F
  have hK' : IsCompact K' :=
    (hj.isOpenEmbedding.toIsInducing.isCompact_preimage_iff (fun x hx => hKA hx)).mpr hK
  have hU := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hj.contMDiff hW
  have hDom : IsInvDomain (n+1) M := whole_domain_open_embedding W E hM j hj
  have hUDense : U ⊆ closure (U \ ⋃ H ∈ F, H) := by
    have h := preimage_mono (f := j) hDense
    rw [hj.preimage_closure,preimage_sdiff,HironakaEmbeddedBoundary.preimage_biUnion_list] at h
    exact h
  obtain ⟨V,hKV,hSmooth⟩ := exists_smooth_restriction_of_empty_singular_fibre hU T K' hClear
  let U₀ := (Subtype.val : V → A) ⁻¹' U
  let F₀ := F.map ((Subtype.val : V → A) ⁻¹' ·)
  let M₀ := whole (A := CMfd.of (n := n+1) V) U₀ F₀
  let P₀ := restrict V T
  have hState₀ : PrincipalPrefixState M₀ U₀ P₀ last :=
    principalPrefixState_restrict U F hDom T hState V
  have hRec₀ : MarkedIdeal.pullback (Subtype.val : V → A) M = M₀ :=
    HironakaEmbeddedBoundary.pullback_val_mk_vanishingIdeal V F U
  have hDom₀ : IsInvDomain (n+1) M₀ :=
    hRec₀ ▸ InvDomainTowerAlong.isInvDomain_pullback_val V hDom
  have hTest₀ := (canonicalInvariant (n+1)).isInvValue.isGeoTestTower_of_isCanonical
    hDom₀ P₀ hState₀.canonical
  let K₀ := (Subtype.val : V → A) ⁻¹' K'
  have hK₀ : IsCompact K₀ :=
    (Topology.IsInducing.subtypeVal.isCompact_preimage_iff
      (fun x hx => ⟨⟨x,hKV hx⟩,rfl⟩)).mpr hK'
  have hU₀ := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hU V
  have hDense₀ := dense_complement_restrict U F hUDense V
  have hProduce : ProducesLocalSmoothCertificates (SmoothTailCertificate.none (n + 1)) := by
    intro D W hW E hE hDense K hK
    exact (local_mixed_smooth_boundary_cleanup hW E hE hDense K hK).withoutExtra
  obtain ⟨D,hKD,C,R,_,hFinish⟩ := exists_local_mixed_finish_with_certificate
    (X := CMfd.of (n := n+1) V) (Y := CMfd.of (n := n+1) (openPreimage T V)) (W := U₀)
    (SmoothTailCertificate.none (n+1)) hProduce hU₀ F₀ hDom₀.isWellFormed.isSNCDivisor
    hDense₀ P₀ hTest₀ hState₀.singular hSmooth K₀ hK₀
  let i : D → X := j ∘ (Subtype.val : V → A) ∘ (Subtype.val : D → V)
  have hi : IsOpenHoloEmbedding (n+1) i :=
    isOpenHoloEmbedding_comp (A := X) (B := A) (C := CMfd.of (n := n+1) D) hj
      (isOpenHoloEmbedding_comp (A := A) (B := CMfd.of (n := n+1) V)
        (C := CMfd.of (n := n+1) D) (isOpenHoloEmbedding_val V) (isOpenHoloEmbedding_val D))
  have hCover : K ⊆ range i := by
    intro x hx
    obtain ⟨a,ha⟩ := hKA hx
    have ha' : a ∈ K' := by
      change j a ∈ K
      rwa [ha]
    let v : V := ⟨a,hKV ha'⟩
    let d : D := ⟨v,hKD ha'⟩
    exact ⟨d,ha⟩
  let M₁ := whole (A := CMfd.of (n := n+1) D) ((Subtype.val : D → V) ⁻¹' U₀)
    (F₀.map ((Subtype.val : D → V) ⁻¹' ·))
  have hState₁ : PrincipalPrefixState M₁ ((Subtype.val : D → V) ⁻¹' U₀) (restrict D P₀) last :=
    principalPrefixState_restrict U₀ F₀ hDom₀ P₀ hState₀ D
  have hSmooth₁ : IsClosedSubmanifold (n+1) (strictTransform (n+1) (restrict D P₀).proj (i ⁻¹' W)) := by
    change IsClosedSubmanifold (n+1)
      (strictTransform (n+1) (restrict D P₀).proj ((Subtype.val : D → V) ⁻¹' U₀))
    rw [strictTransform_restricted_tower]
    exact BlowupRestrictOpen.isClosedSubmanifold_preimage_val hSmooth _
  have hBoundary : F₀.map ((Subtype.val : D → V) ⁻¹' ·) = E.map (i ⁻¹' ·) := by
    simp only [F₀,F,List.map_map]
    rfl
  refine ⟨CMfd.of (n := n+1) D,i,hi,hCover,_,restrict D P₀,C,R,?_,hSmooth₁,?_⟩
  · have hc := hState₁.canonical
    dsimp only [M₁] at hc
    rw [hBoundary] at hc
    exact hc
  · rwa [hBoundary] at hFinish

open AnalyticDimensionBasics HironakaG8PrincipalRetainedEpochFinite

/-- Start with a pure invertible hypersurface and finish the same finite
canonical singular service by the available geometric boundary cleanup. -/
theorem exists_compact_principal_history_with_snc_finish
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (E : List (Set X)) (hM : IsInvDomain (n+1) (whole W E))
    (hPure : IsPureDim (n := n+1) W n)
    (hI : (vanishingIdeal (n := n+1) W).IsInvertible)
    (hNo : HasNoBoundaryFactor (whole W E))
    (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (K : Set X) (hK : IsCompact K) :
    ∃ (A : CMfd.{0} (n+1)) (j : A → X), IsOpenHoloEmbedding (n+1) j ∧ K ⊆ range j ∧
      ∃ (B : CMfd.{0} (n+1)) (L : BlowupTower A B) (C : CMfd.{0} (n+1)) (R : BlowupTower B C),
        let U := j ⁻¹' W
        let F := E.map (j ⁻¹' ·)
        let M := whole (A := A) U F
        IsCanonical M ((canonicalInvariant (n+1)).inv M) L ∧
        IsClosedSubmanifold (n+1) (strictTransform (n+1) L.proj U) ∧
        DenseBoundaryResolution U F (L.append R) := by
  obtain ⟨_,_,hTrace⟩ := exists_finite_compact_principal_service_from_refl
    W hW E hM hPure hI hNo K hK
  exact CompactPrincipalServiceTrace.exists_snc_finish hW hM hDense hK hTrace


open HironakaG8NativePhaseCertificate MarkedIdealTowerTransport MaxLocusLocal
  HironakaHolomorphicJetChartInvariance HironakaActualVanishingIntrinsicHSTransport

/-- The Hilbert--Samuel drop through the actual clipped append needs
neither a principal carrier nor any comparison with ordinary order. -/
theorem clipped_native_phase_strict_profile_drop
    {Z : CMfd.{0} (n+1)} (P : BlowupTower X Y) (W : Set X)
    (O : Opens Y) (S : BlowupTower (CMfd.of (n := n+1) O) Z)
    (V : Opens X) (hVO : openPreimage P V ≤ O) (K : Set X)
    (E : List (Set O)) (H : ℕ → ℕ) :
    let U := (Subtype.val : O → Y) ⁻¹' strictTransform (n+1) P.proj W
    let J := openPreimage P V
    let D := nestedOpens O J
    let e := (nestedOpensDiffeo (n := n+1) hVO).symm
    let tail := transport e (restrict D S)
    let T := (restrict V P).append tail.tower
    ActualNativePhase (X := CMfd.of (n := n+1) O) U E H S →
    (∀ x : O, P.proj x.val ∈ K →
      toLex (hilbertSamuelAt (vanishingIdeal (n := n+1) U) x) ≤ toLex H) →
    ∀ z, (T.proj z).val ∈ K →
      toLex (hilbertSamuelAt (vanishingIdeal (n := n+1)
        (strictTransform (n+1) T.proj ((Subtype.val : V → X) ⁻¹' W))) z) < toLex H := by
  dsimp only
  intro hPhase hUpper
  let U := (Subtype.val : O → Y) ⁻¹' strictTransform (n+1) P.proj W
  let J := openPreimage P V
  let D := nestedOpens O J
  let e := (nestedOpensDiffeo (n := n+1) hVO).symm
  let tail := transport e (restrict D S)
  let T := (restrict V P).append tail.tower
  let UEnd := strictTransform (n+1) T.proj ((Subtype.val : V → X) ⁻¹' W)
  let b : tail.target → Z := fun z => (tail.back z).val
  change ∀ z : tail.target, (T.proj z).val ∈ K →
    toLex (hilbertSamuelAt (vanishingIdeal (n := n+1) UEnd) z) < toLex H
  intro z hz
  obtain ⟨hProj,hStrict⟩ := clipped_tail_geometry P O S V hVO W
  have hOn : P.proj (S.proj (b z)).val ∈ K := (hProj z) ▸ hz
  have hp := native_phase_strict_profile_bound_on_fibre (X := CMfd.of (n := n+1) O) (Y := Z)
    U E H S hPhase ((fun x : O => P.proj x.val) ⁻¹' K) hUpper (b z) hOn
  have hEq : UEnd = b ⁻¹' strictTransform (n+1) S.proj U := hStrict
  have hRead : hilbertSamuelAt (vanishingIdeal (n := n+1) UEnd) z =
      hilbertSamuelAt (vanishingIdeal (n := n+1) (strictTransform (n+1) S.proj U)) (b z) := by
    rw [hEq]
    apply funext
    intro ℓ
    exact (hilbertSamuelAt_vanishing_actual_biholomorphic_any tail.back
      ((Subtype.val : openPreimage S D → Z) ⁻¹' strictTransform (n+1) S.proj U) z ℓ).trans
      (hilbertSamuelAt_vanishing_actual_open_any (openPreimage S D) _ (tail.back z) ℓ)
  rw [hRead]
  exact hp

open NonmonomialOrderRegime HomogenizedIdealAlong HironakaActualHSSingularBlowupRestart
  HironakaHypersurfaceStageCenters

/-- The precise remaining canonicality input for the smooth cleanup is
canonicality of its fresh whole mark-one tower. That certificate would
rebase to the original occupied chronological history. -/
theorem canonical_append_of_canonical_smooth_whole_tail
    {Z : CMfd.{0} (n+1)} (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (E : List (Set X)) (hM : IsInvDomain (n+1) (whole W E))
    (P : BlowupTower X Y) {cap : ℕ} (hP : PrincipalPrefixState (whole W E) W P cap)
    (hHigh : CentresOrdGt (whole W E) 1 P)
    (S : BlowupTower Y Z) :
    let M := whole W E
    let U := strictTransform (n+1) P.proj W
    let F := whole U (geoTransformAlong M P).E
    IsClosedSubmanifold (n+1) U →
    IsCanonical F ((canonicalInvariant (n+1)).inv F) S →
    IsCanonical M ((canonicalInvariant (n+1)).inv M) (P.append S) := by
  dsimp only
  intro hSmooth hCan
  let M := whole W E
  let U := strictTransform (n+1) P.proj W
  let A := geoTransformAlong M P
  let F := whole U A.E
  let R := canonicalInvariant.{0} (n+1)
  have hTest := R.isInvValue.isGeoTestTower_of_isCanonical hM P hP.canonical
  have hAD := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM P hTest
  have hU := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hW P
  have hDense := actualPure_subset_closure_regularLocus hU hP.pure
  have hBase := HironakaEmbeddedReducible.isInvDomain_vanishingIdeal_of_pure
    le_rfl hU (Nat.lt_succ_self n) hDense
  have hF : IsInvDomain (n+1) F :=
    ⟨⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,hBase.isWellFormed.isCoherent,
      hAD.isWellFormed.isSNCDivisor,
      SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hAD.isWellFormed.isSNCDivisor⟩,
      hBase.dimLE,le_rfl,hBase.isNonzeroAlongAt⟩
  have hCap : IsMaximalOrderAlong F.N F.ideal F.d := by
    intro x hx
    have hUx := cosupport_high_mark_subset_diff_regularLocus hU.isClosed
      (Nat.lt_succ_self n) (by decide : 2 ≤ 2) hx
    obtain ⟨k,hk⟩ := hSmooth.2 x hUx.1
    have he := hP.pure x k hk
    subst k
    exact hUx.2 hk
  have hAN : A.N = univ := (pullback_eq_mul_geoTransformAlong M rfl hM.isWellFormed.isCoherent P hTest).1
  have hAd : A.d ≤ F.d := by
    change (geoTransformAlong M P).d ≤ 1
    rw [d_geoTransformAlong]
  exact (append_whole_canonical_of_principal_residual_epoch M hM P hP.canonical F hF rfl
    hP.noFactor hCap hHigh S hCan hAN rfl hAd hP.residual).1

end
end Hironaka.HironakaG8PrincipalCompactSNCFinish
