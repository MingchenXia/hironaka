import Hironaka.Resolution.HironakaG8PrincipalCompactAnchor
import Hironaka.Resolution.HironakaG8PrincipalPrefixCompactClipping
import Hironaka.Resolution.HironakaG8PrincipalEpochSuccession
import Hironaka.Resolution.HironakaG8PrincipalEpochLabels
import Hironaka.Resolution.HironakaG8OccupiedAtlasRestart
import Hironaka.Resolution.HironakaSaturatedTowerAppend

/-! The compact principal order cap on the literal appended tower. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8PrincipalCompactRepeat
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal MarkedIdealRestrictOpen
  ResolutionInvariantSpec CanonicalCentres HironakaEmbeddedAnalytic HironakaBaseChange
  HironakaNormalCrossingsOpenRestrictionSeparation HironakaNormalCrossingsSeparationChoiceComparison
  HironakaActualOpenEmbeddingVanishingIdeal HironakaActualVanishingIntrinsicHSTransport
  HironakaG8PrincipalEpochSuccession HironakaG8PrincipalPrefixCompactClipping HironakaG8PrincipalCompactAnchor
  HironakaG8NativePhaseCertificate HironakaG8OccupiedAtlasRestart HironakaG8PrincipalEpochLabels
  HironakaHolomorphicJetChartInvariance HironakaG8NativeRelativeClearing
  GermIdealOrder MarkedIdealTowerTransport MaxLocusLocal

variable {n : ℕ} {X Y Z : CMfd.{0} (n+1)}
private abbrev whole {A : CMfd.{0} (n+1)} (W : Set A) (E : List (Set A)) (q : ℕ) :
    MarkedIdeal (n+1) A := ⟨univ,E,vanishingIdeal (n := n+1) W,q⟩

/-- The equations for any given saturated clip, with its actual endpoint
map into the same phase tower. -/
theorem clipped_tail_geometry
    (P : BlowupTower X Y) (O : Opens Y) (S : BlowupTower (CMfd.of (n := n+1) O) Z)
    (V : Opens X) (hVO : openPreimage P V ≤ O) (W : Set X) :
    let J := openPreimage P V
    let D := nestedOpens O J
    let e := (nestedOpensDiffeo (n := n+1) hVO).symm
    let tail := transport e (restrict D S)
    let T := (restrict V P).append tail.tower
    let b : tail.target → Z := fun z => (tail.back z).val
    (∀ z, (T.proj z).val = P.proj (S.proj (b z)).val) ∧
    strictTransform (n+1) T.proj ((Subtype.val : V → X) ⁻¹' W) =
      b ⁻¹' strictTransform (n+1) S.proj ((Subtype.val : O → Y) ⁻¹' strictTransform (n+1) P.proj W) := by
  dsimp only
  let J := openPreimage P V
  let D := nestedOpens O J
  let e := (nestedOpensDiffeo (n := n+1) hVO).symm
  let L := restrict V P
  let R := restrict D S
  let tail := transport e R
  let T := L.append tail.tower
  let b : tail.target → Z := fun z => (tail.back z).val
  let U := (Subtype.val : O → Y) ⁻¹' strictTransform (n+1) P.proj W
  refine ⟨?_,?_⟩
  · intro z
    have hp := congrArg (fun q : D => q.val.val) (proj_transport e R z)
    change ((tail.tower.proj z : J) : Y) = ((R.proj (tail.back z)).val : Y) at hp
    have hProj : ((tail.tower.proj z : J) : Y) = (S.proj (b z)).val := by
      simpa only [R,proj_restrict,b] using hp
    simpa only [T,L,BlowupTower.proj_append,Function.comp_apply,proj_restrict] using
      congrArg P.proj hProj
  · have hCarrier : strictTransform (n+1) L.proj ((Subtype.val : V → X) ⁻¹' W) =
        e ⁻¹' ((Subtype.val : D → O) ⁻¹' U) := strictTransform_restricted_tower V P W
    have h := strictTransform_preimage_of_square e tail.back tail.tower.contMDiff_proj
      R.contMDiff_proj ((Subtype.val : D → O) ⁻¹' U)
      (isClosed_closure.preimage (continuous_subtype_val.comp continuous_subtype_val))
      (fun z => (proj_transport e R z).symm)
    rw [← hCarrier,strictTransform_restricted_tower D S U] at h
    change strictTransform (n+1) T.proj ((Subtype.val : V → X) ⁻¹' W) =
      b ⁻¹' strictTransform (n+1) S.proj U
    rw [BlowupTower.proj_append,StrictTransformComposition.strictTransform_comp
      L.contMDiff_proj tail.tower.contMDiff_proj]
    exact h

/-- Exact chart coverage bounds the initial profile of the whole
principal source by the serviced label. The anchor can lie on an earlier
ambient space when its actual order and profile are known. -/
theorem principal_profile_upper_of_exact_atlas
    {B : CMfd.{0} (n+1)} (U : Set X) (E : List (Set X)) (U₀ : Set B) (a : B) (q : ℕ)
    (hI : (vanishingIdeal (n := n+1) U).IsInvertible)
    (hI₀ : (vanishingIdeal (n := n+1) U₀).IsInvertible)
    (hOrd : order (n+1) univ (vanishingIdeal (n := n+1) U₀) a = q)
    (S : BlowupTower X Y)
    (hAtlas : HasExactCoveredNativeAtlas U E (hilbertSamuelAt (vanishingIdeal (n := n+1) U₀) a)
      S (whole U E q)) :
    ∀ x, toLex (hilbertSamuelAt (vanishingIdeal (n := n+1) U) x) ≤
      toLex (hilbertSamuelAt (vanishingIdeal (n := n+1) U₀) a) := by
  obtain ⟨ι,A,_,_,hCover⟩ := hAtlas
  intro x
  apply le_of_not_gt
  intro hLt
  have hOrd' := (principal_profile_lt_iff_order_lt _ _ hI₀ hI a x).1 hLt
  rw [hOrd] at hOrd'
  have hCos : x ∈ (whole U E q).cosupp :=
    ⟨mem_univ _,(le_order_iff (𝔞 := vanishingIdeal (n := n+1) U) (fun _ hg => hg.1)).1 hOrd'.le⟩
  obtain ⟨i,hi⟩ := hCover x hCos
  let z : A.openSet i := ⟨x,hi⟩
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,hUpper,_⟩ := A.native i
  have hUpper' := Pi.toLex_monotone (hUpper z)
  rw [funext (hilbertSamuelAt_vanishing_actual_open_any (A.openSet i) U z)] at hUpper'
  exact (not_lt_of_ge hUpper') hLt


/-- The phase's strict multiplicity bound passes through the actual
transported clipped append. All ranks are measured on the reduced strict
carriers of the indicated physical towers. -/
theorem clipped_tail_principal_order_drop {B : CMfd.{0} (n+1)}
    (P : BlowupTower X Y) (W : Set X) (O : Opens Y)
    (S : BlowupTower (CMfd.of (n := n+1) O) Z)
    (V : Opens X) (hVO : openPreimage P V ≤ O)
    (E : List (Set O)) (U₀ : Set B) (a : B) (q : ℕ)
    (hI₀ : (vanishingIdeal (n := n+1) U₀).IsInvertible)
    (hOrd : order (n+1) univ (vanishingIdeal (n := n+1) U₀) a = q) :
    let U := (Subtype.val : O → Y) ⁻¹' strictTransform (n+1) P.proj W
    let H := hilbertSamuelAt (vanishingIdeal (n := n+1) U₀) a
    let J := openPreimage P V
    let D := nestedOpens O J
    let e := (nestedOpensDiffeo (n := n+1) hVO).symm
    let tail := transport e (restrict D S)
    let T := (restrict V P).append tail.tower
    let UEnd := strictTransform (n+1) T.proj ((Subtype.val : V → X) ⁻¹' W)
    (vanishingIdeal (n := n+1) U).IsInvertible →
    (vanishingIdeal (n := n+1) UEnd).IsInvertible →
    ActualNativePhase (X := CMfd.of (n := n+1) O) U E H S →
    HasExactCoveredNativeAtlas U E H S (whole (A := CMfd.of (n := n+1) O) U E q) →
    ∀ z, order (n+1) univ (vanishingIdeal (n := n+1) UEnd) z < (q : ℕ∞) := by
  dsimp only
  intro hI hEnd hPhase hAtlas
  let U := (Subtype.val : O → Y) ⁻¹' strictTransform (n+1) P.proj W
  let J := openPreimage P V
  let D := nestedOpens O J
  let e := (nestedOpensDiffeo (n := n+1) hVO).symm
  let tail := transport e (restrict D S)
  let T := (restrict V P).append tail.tower
  let UEnd := strictTransform (n+1) T.proj ((Subtype.val : V → X) ⁻¹' W)
  let b : tail.target → Z := fun x => (tail.back x).val
  change ∀ z : tail.target, order (n+1) univ (vanishingIdeal (n := n+1) UEnd) z < (q : ℕ∞)
  intro z
  have hUpper := principal_profile_upper_of_exact_atlas (X := CMfd.of (n := n+1) O) (Y := Z)
    U E U₀ a q hI hI₀ hOrd S hAtlas
  have hp := native_phase_strict_profile_bound_on_fibre (X := CMfd.of (n := n+1) O) (Y := Z)
    U E _ S hPhase univ
    (fun x _ => hUpper x) (b z) (mem_univ _)
  have hEq : UEnd = b ⁻¹' strictTransform (n+1) S.proj U :=
    (clipped_tail_geometry P O S V hVO W).2
  have hRead : hilbertSamuelAt (vanishingIdeal (n := n+1) UEnd) z =
      hilbertSamuelAt (vanishingIdeal (n := n+1) (strictTransform (n+1) S.proj U)) (b z) := by
    rw [hEq]
    apply funext
    intro ℓ
    exact (hilbertSamuelAt_vanishing_actual_biholomorphic_any tail.back
      ((Subtype.val : openPreimage S D → Z) ⁻¹' strictTransform (n+1) S.proj U) z ℓ).trans
      (hilbertSamuelAt_vanishing_actual_open_any (openPreimage S D) _ (tail.back z) ℓ)
  exact principal_fibre_below_cap_of_profile_drop (Y := tail.target) UEnd U₀ a q hEnd hI₀ hOrd z
    (by rw [hRead]; exact hp)


open HironakaG8PrincipalRetainedEpochFinite AnalyticDimensionBasics

/-- One serviced principal label with the two literal open restrictions
leading from the inherited physical prefix to the appended tower. -/
structure CompactPrincipalServiceStep
    (W : Set X) (E : List (Set X)) (P : BlowupTower X Y) (K : Set X) (cap : ℕ) where
  mark : ℕ
  lower : mark < cap
  anchor : Y
  anchorOnFibre : anchor ∈ P.proj ⁻¹' K ∩ singularSet (n := n+1) (strictTransform (n+1) P.proj W)
  anchorOrder : order (n+1) univ (vanishingIdeal (n := n+1) (strictTransform (n+1) P.proj W)) anchor = mark
  baseOpen : Opens X
  covers : K ⊆ baseOpen
  phaseOpen : Opens (openPreimage P baseOpen)
  phaseTarget : CMfd.{0} (n+1)
  phaseTower : BlowupTower (CMfd.of (n := n+1) phaseOpen) phaseTarget
  phase :
    let V := baseOpen
    let L := restrict V P
    let U := strictTransform (n+1) L.proj ((Subtype.val : V → X) ⁻¹' W)
    let B := (geoTransformAlong (whole (A := CMfd.of (n := n+1) V)
      ((Subtype.val : V → X) ⁻¹' W) (E.map ((Subtype.val : V → X) ⁻¹' ·)) 1) L).E
    let UO := (Subtype.val : phaseOpen → openPreimage P V) ⁻¹' U
    let BO := B.map ((Subtype.val : phaseOpen → openPreimage P V) ⁻¹' ·)
    let H := hilbertSamuelAt (vanishingIdeal (n := n+1) (strictTransform (n+1) P.proj W)) anchor
    ActualNativePhase (X := CMfd.of (n := n+1) phaseOpen) UO BO H phaseTower ∧
      HasExactCoveredNativeAtlas UO BO H phaseTower (whole (A := CMfd.of (n := n+1) phaseOpen) UO BO mark)
  finalOpen : Opens baseOpen
  coversFinal : (Subtype.val : baseOpen → X) ⁻¹' K ⊆ finalOpen
  saturated : openPreimage (restrict baseOpen P) finalOpen ≤ phaseOpen

namespace CompactPrincipalServiceStep

variable {W : Set X} {E : List (Set X)} {P : BlowupTower X Y} {K : Set X} {cap : ℕ}
    (s : CompactPrincipalServiceStep W E P K cap)

abbrev source := CMfd.of (n := n+1) s.finalOpen
abbrev inclusion : s.source → X := fun x => x.val.val
abbrev nextCarrier : Set s.source := s.inclusion ⁻¹' W
abbrev nextBoundary : List (Set s.source) := E.map (s.inclusion ⁻¹' ·)
abbrev nextTask : Set s.source := s.inclusion ⁻¹' K

abbrev tail :=
  transport (nestedOpensDiffeo (n := n+1) s.saturated).symm
    (restrict (nestedOpens s.phaseOpen (openPreimage (restrict s.baseOpen P) s.finalOpen)) s.phaseTower)

abbrev tower : BlowupTower s.source s.tail.target :=
  (restrict s.finalOpen (restrict s.baseOpen P)).append s.tail.tower

end CompactPrincipalServiceStep

/-- Obtain the next finite physical phase and its strict successor cap.
The output bound holds on the actual clipped endpoint. -/
theorem exists_compact_principal_service_step
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (E : List (Set X)) (hM : IsInvDomain (n+1) (whole W E 1))
    (P : BlowupTower X Y) {cap : ℕ} (hP : PrincipalPrefixState (whole W E 1) W P cap)
    (K : Set X) (hK : IsCompact K) :
    let U := strictTransform (n+1) P.proj W
    let F := P.proj ⁻¹' K ∩ singularSet (n := n+1) U
    F.Nonempty →
    (∀ x ∈ F, order (n+1) univ (vanishingIdeal (n := n+1) U) x < (cap : ℕ∞)) →
    ∃ s : CompactPrincipalServiceStep W E P K cap,
      PrincipalPrefixState (whole s.nextCarrier s.nextBoundary 1) s.nextCarrier s.tower s.mark ∧
      ∀ z, order (n+1) univ (vanishingIdeal (n := n+1)
        (strictTransform (n+1) s.tower.proj s.nextCarrier)) z < (s.mark : ℕ∞) := by
  dsimp only
  intro hNe hBelow
  let U := strictTransform (n+1) P.proj W
  obtain ⟨a,ha,q,_,hq,hOrd,V,hKV,H,hH,O,_,Z',S,hPhase,hAtlas,V',hV',hClip,hState⟩ :=
    exists_compact_principal_continuation_of_singular_fibre W hW E hM P hP K hK hNe hBelow
  rw [hH] at hPhase hAtlas
  let s : CompactPrincipalServiceStep W E P K cap :=
    ⟨q,hq,a,ha,hOrd,V,hKV,O,Z',S,⟨hPhase,hAtlas⟩,V',hV',hClip⟩
  let WV := (Subtype.val : V → X) ⁻¹' W
  let EV := E.map ((Subtype.val : V → X) ⁻¹' ·)
  let L := restrict V P
  let J := openPreimage P V
  let U' := strictTransform (n+1) L.proj WV
  let UO := (Subtype.val : O → J) ⁻¹' U'
  let EO := (geoTransformAlong (whole (A := CMfd.of (n := n+1) V) WV EV 1) L).E.map
    ((Subtype.val : O → J) ⁻¹' ·)
  have hI' : (vanishingIdeal (n := n+1) U').IsInvertible :=
    (principalPrefixState_restrict W E hM P hP V).invertible
  have hIO : (vanishingIdeal (n := n+1) UO).IsInvertible := by
    change (vanishingIdeal (n := n+1) ((Subtype.val : O → J) ⁻¹' U')).IsInvertible
    rw [← pullback_vanishingIdeal_of_isOpenHoloEmbedding _ (isOpenHoloEmbedding_val O) U']
    apply GermIdealTotalTransform.isInvertible_pullback contMDiff_subtype_val _ hI'
    rw [(isOpenHoloEmbedding_val O).exceptionalLocus_eq_empty,interior_empty]
  have hRec : MarkedIdeal.pullback (Subtype.val : V' → V)
      (whole (A := CMfd.of (n := n+1) V) WV EV 1) = whole s.nextCarrier s.nextBoundary 1 := by
    trans (⟨univ,EV.map ((Subtype.val : V' → V) ⁻¹' ·),
      vanishingIdeal (n := n+1) ((Subtype.val : V' → V) ⁻¹' WV),1⟩ : MarkedIdeal (n+1) V')
    · exact HironakaEmbeddedBoundary.pullback_val_mk_vanishingIdeal
        (X := CMfd.of (n := n+1) V) V' EV WV
    · have hBoundary : EV.map ((Subtype.val : V' → V) ⁻¹' ·) = s.nextBoundary := by
        simp only [EV,List.map_map]
        rfl
      exact congrArg (fun B => (⟨univ,B,vanishingIdeal (n := n+1) s.nextCarrier,1⟩ :
        MarkedIdeal (n+1) V')) hBoundary
  have hNext : PrincipalPrefixState (whole s.nextCarrier s.nextBoundary 1) s.nextCarrier s.tower s.mark :=
    hRec ▸ hState
  refine ⟨s,hNext,?_⟩
  exact clipped_tail_principal_order_drop L WV O S V' hClip EO U a q hP.invertible hOrd
    hIO hNext.invertible hPhase hAtlas


/-- Finite principal service on a fixed compact task. Each step records
its own physical extension and exact native atlas. A terminal node has a
canonical inherited tower and an empty singular fibre. -/
inductive CompactPrincipalServiceTrace :
    {A B : CMfd.{0} (n+1)} → (W : Set A) → List (Set A) →
      BlowupTower A B → Set A → ℕ → List (ℕ × (ℕ → ℕ)) → Prop
  | done {A B : CMfd.{0} (n+1)} {W : Set A} {E : List (Set A)}
      {P : BlowupTower A B} {K : Set A} {cap : ℕ}
      (state : PrincipalPrefixState (whole W E 1) W P cap)
      (clear : Disjoint (P.proj ⁻¹' K) (singularSet (n := n+1) (strictTransform (n+1) P.proj W))) :
      CompactPrincipalServiceTrace W E P K cap []
  | next {A B : CMfd.{0} (n+1)} {W : Set A} {E : List (Set A)}
      {P : BlowupTower A B} {K : Set A} {cap : ℕ} {labels : List (ℕ × (ℕ → ℕ))}
      (s : CompactPrincipalServiceStep W E P K cap)
      (state : PrincipalPrefixState (whole s.nextCarrier s.nextBoundary 1) s.nextCarrier s.tower s.mark)
      (orderDrop : ∀ z, order (n+1) univ (vanishingIdeal (n := n+1)
        (strictTransform (n+1) s.tower.proj s.nextCarrier)) z < (s.mark : ℕ∞))
      (rest : CompactPrincipalServiceTrace s.nextCarrier s.nextBoundary s.tower s.nextTask s.mark labels) :
      CompactPrincipalServiceTrace W E P K cap
        ((s.mark,hilbertSamuelAt (vanishingIdeal (n := n+1) (strictTransform (n+1) P.proj W)) s.anchor) :: labels)

/-- Every strictly ranked canonical principal prefix serves all of its
remaining compact singular fibre in a finite trace. -/
theorem exists_finite_compact_principal_service (cap : ℕ) :
    ∀ {A B : CMfd.{0} (n+1)} (W : Set A) (_hW : IsComplexAnalyticSubset (n := n+1) W)
      (E : List (Set A)) (_hM : IsInvDomain (n+1) (whole W E 1))
      (P : BlowupTower A B) (_hP : PrincipalPrefixState (whole W E 1) W P cap)
      (K : Set A) (_hK : IsCompact K),
      (∀ x ∈ P.proj ⁻¹' K ∩ singularSet (n := n+1) (strictTransform (n+1) P.proj W),
        order (n+1) univ (vanishingIdeal (n := n+1) (strictTransform (n+1) P.proj W)) x <
          (cap : ℕ∞)) →
      ∃ labels, CompactPrincipalServiceTrace W E P K cap labels := by
  induction cap using Nat.strong_induction_on with
  | h cap ih =>
    intro A B W hW E hM P hP K hK hBelow
    by_cases hClear : Disjoint (P.proj ⁻¹' K) (singularSet (n := n+1) (strictTransform (n+1) P.proj W))
    · exact ⟨[],.done hP hClear⟩
    have hNe : (P.proj ⁻¹' K ∩ singularSet (n := n+1) (strictTransform (n+1) P.proj W)).Nonempty :=
      not_disjoint_iff_nonempty_inter.mp hClear
    obtain ⟨s,hs,hNext⟩ := exists_compact_principal_service_step W hW E hM P hP K hK hNe hBelow
    let K₁ := (Subtype.val : s.baseOpen → A) ⁻¹' K
    have hK₁ : IsCompact K₁ :=
      (Topology.IsInducing.subtypeVal.isCompact_preimage_iff
        (fun x hx => ⟨⟨x,s.covers hx⟩,rfl⟩)).mpr hK
    have hK₂ : IsCompact s.nextTask :=
      (Topology.IsInducing.subtypeVal.isCompact_preimage_iff
        (fun x hx => ⟨⟨x,s.coversFinal hx⟩,rfl⟩)).mpr hK₁
    have hW₁ := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW s.baseOpen
    have hW₂ : IsComplexAnalyticSubset (n := n+1) s.nextCarrier :=
      AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW₁ s.finalOpen
    let W₁ : Set s.baseOpen := (Subtype.val : s.baseOpen → A) ⁻¹' W
    let E₁ : List (Set s.baseOpen) := E.map ((Subtype.val : s.baseOpen → A) ⁻¹' ·)
    let J := CMfd.of (n := n+1) s.baseOpen
    let M₁ := whole (A := J) W₁ E₁ 1
    have hRec₁ : MarkedIdeal.pullback (Subtype.val : s.baseOpen → A) (whole W E 1) = M₁ :=
      HironakaEmbeddedBoundary.pullback_val_mk_vanishingIdeal s.baseOpen E W
    have hM₁ : IsInvDomain (n+1) M₁ :=
      hRec₁ ▸ InvDomainTowerAlong.isInvDomain_pullback_val s.baseOpen hM
    have hRec₂ : MarkedIdeal.pullback (Subtype.val : s.finalOpen → s.baseOpen) M₁ =
        whole s.nextCarrier s.nextBoundary 1 := by
      trans (⟨univ,E₁.map ((Subtype.val : s.finalOpen → s.baseOpen) ⁻¹' ·),
        vanishingIdeal (n := n+1) s.nextCarrier,1⟩ : MarkedIdeal (n+1) s.source)
      · exact HironakaEmbeddedBoundary.pullback_val_mk_vanishingIdeal (X := J) s.finalOpen E₁ W₁
      · have hBoundary : E₁.map ((Subtype.val : s.finalOpen → s.baseOpen) ⁻¹' ·) =
            s.nextBoundary := by
          simp only [E₁,List.map_map]
          rfl
        exact congrArg (fun B => (⟨univ,B,vanishingIdeal (n := n+1) s.nextCarrier,1⟩ :
          MarkedIdeal (n+1) s.source)) hBoundary
    have hM₂ : IsInvDomain (n+1) (whole s.nextCarrier s.nextBoundary 1) :=
      hRec₂ ▸ InvDomainTowerAlong.isInvDomain_pullback_val s.finalOpen hM₁
    obtain ⟨labels,hTrace⟩ := ih s.mark s.lower s.nextCarrier hW₂ s.nextBoundary hM₂ s.tower hs
      s.nextTask hK₂ (fun x _ => hNext x)
    exact ⟨_,.next s hs hNext hTrace⟩


open HironakaActualCompactHSMaximalProfile HironakaG1RHypersurfaceRecord

/-- The compact principal branch terminates from the actual mark-one
record, with no prescribed initial cap or selected profile. -/
theorem exists_finite_compact_principal_service_from_refl
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (E : List (Set X)) (hM : IsInvDomain (n+1) (whole W E 1))
    (hPure : IsPureDim (n := n+1) W n)
    (hI : (vanishingIdeal (n := n+1) W).IsInvertible)
    (hNo : HasNoBoundaryFactor (whole W E 1))
    (K : Set X) (hK : IsCompact K) :
    ∃ cap labels, CompactPrincipalServiceTrace W E (.refl : BlowupTower X X) K cap labels := by
  by_cases hEmpty : Disjoint K (singularSet (n := n+1) W)
  · have hP := initial_principal_prefix_state W hW E hPure hI hM hNo 0
    refine ⟨0,[],.done hP ?_⟩
    rwa [BlowupTower.proj_refl,preimage_id,HironakaG11PresTowerState.strictTransform_id hW.isClosed]
  have hNe := not_disjoint_iff_nonempty_inter.mp hEmpty
  have hComp := hK.inter_right (HironakaEmbeddedAnalytic.isClosed_singularSet (n := n+1) hW.isClosed)
  let I := vanishingIdeal (n := n+1) W
  obtain ⟨a,_,hMax⟩ := exists_actual_compact_hs_lex_maximum I
    hM.isWellFormed.isCoherent _ hComp hNe
  obtain ⟨q,hq,_⟩ := exists_order_hilbertSamuelAt_eq_hypersurfaceHS I hI a
  let cap := q+1
  have hP := initial_principal_prefix_state W hW E hPure hI hM hNo cap
  refine ⟨cap,exists_finite_compact_principal_service cap W hW E hM .refl hP K hK ?_⟩
  rw [BlowupTower.proj_refl,preimage_id,HironakaG11PresTowerState.strictTransform_id hW.isClosed]
  intro x hx
  have hLe : order (n+1) univ I x ≤ order (n+1) univ I a := by
    apply le_of_not_gt
    intro hlt
    exact (not_lt_of_ge (hMax x hx)) ((principal_profile_lt_iff_order_lt I I hI hI a x).2 hlt)
  rw [hq] at hLe
  exact hLe.trans_lt (by exact_mod_cast Nat.lt_succ_self q)


open HironakaG8OpenHoloEmbeddingComposition

/-- The finite trace exposes a single terminal tower over an actual open
embedding into the original base, with the untouched compact task and
the original chronological canonical invariant on its restricted record. -/
theorem CompactPrincipalServiceTrace.endpoint
    {W : Set X} {E : List (Set X)} {P : BlowupTower X Y} {K : Set X}
    {cap : ℕ} {labels : List (ℕ × (ℕ → ℕ))}
    (h : CompactPrincipalServiceTrace W E P K cap labels) :
    ∃ (A : CMfd.{0} (n+1)) (j : A → X), IsOpenHoloEmbedding (n+1) j ∧ K ⊆ range j ∧
      ∃ (B : CMfd.{0} (n+1)) (T : BlowupTower A B) (last : ℕ),
      let U := j ⁻¹' W
      let F := E.map (j ⁻¹' ·)
      PrincipalPrefixState (whole U F 1) U T last ∧
      Disjoint (T.proj ⁻¹' (j ⁻¹' K)) (singularSet (n := n+1) (strictTransform (n+1) T.proj U)) := by
  induction h with
  | @done A B W E P K cap state clear =>
    let e : A ≃ₘ⟮𝓘(ℂ,ComplexModel (n+1)),𝓘(ℂ,ComplexModel (n+1))⟯
        CMfd.of (n := n+1) (⊤ : Opens A) :=
      { toFun := fun y => ⟨y,trivial⟩
        invFun := Subtype.val
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        contMDiff_toFun := BlowupRestrictOpen.contMDiff_opens_mk (V := (⊤ : Opens A))
          contMDiff_id (fun _ => trivial)
        contMDiff_invFun := contMDiff_subtype_val }
    refine ⟨A,id,⟨⊤,e,fun _ => rfl⟩,fun x _ => ⟨x,rfl⟩,B,P,cap,?_,?_⟩
    · simpa only [preimage_id,List.map_id'] using state
    · simpa only [preimage_id] using clear
  | @next A B W E P K cap labels s _ _ rest ih =>
    obtain ⟨C,j,hj,hCover,D,T,last,hState,hClear⟩ := ih
    have hi : IsOpenHoloEmbedding (n+1) s.inclusion := by
      change IsOpenHoloEmbedding (n+1)
        ((Subtype.val : s.baseOpen → A) ∘ (Subtype.val : s.finalOpen → s.baseOpen))
      exact isOpenHoloEmbedding_comp (A := A) (B := CMfd.of (n := n+1) s.baseOpen)
        (C := s.source) (isOpenHoloEmbedding_val s.baseOpen) (isOpenHoloEmbedding_val s.finalOpen)
    refine ⟨C,s.inclusion ∘ j,isOpenHoloEmbedding_comp hi hj,?_,D,T,last,?_,hClear⟩
    · intro x hx
      let x₀ : s.baseOpen := ⟨x,s.covers hx⟩
      let x₁ : s.source := ⟨x₀,s.coversFinal hx⟩
      obtain ⟨y,hy⟩ := hCover (show x₁ ∈ s.nextTask from hx)
      exact ⟨y,congrArg s.inclusion hy⟩
    · have he : s.nextBoundary.map (j ⁻¹' ·) = E.map ((s.inclusion ∘ j) ⁻¹' ·) := by
        simp only [CompactPrincipalServiceStep.nextBoundary,List.map_map]
        rfl
      rw [he] at hState
      exact hState

end
end Hironaka.HironakaG8PrincipalCompactRepeat
