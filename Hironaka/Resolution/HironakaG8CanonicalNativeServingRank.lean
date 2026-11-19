import Hironaka.Resolution.HironakaG8PrincipalCompactSNCFinish
import Hironaka.Resolution.HironakaG8PrincipalCompactRepeat
import Hironaka.Resolution.HironakaActualHilbertSamuelLexOrder
import Hironaka.Resolution.HironakaG8RelativeLexInduction
import Hironaka.Resolution.HironakaG8ChronologicalNativeClassAtlas

/-! Realized Hilbert--Samuel rank for canonical serving on an actual clipped tower. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8CanonicalNativeServingRank
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal MarkedIdealRestrictOpen
  ResolutionInvariantSpec CanonicalCentres HironakaEmbeddedAnalytic HironakaBaseChange
  HironakaG8PrincipalCompactRepeat HironakaG8PrincipalCompactSNCFinish
  HironakaG8NativePhaseCertificate HironakaG8IntrinsicSingularBlockSchedule
  HironakaUniformHistoricalSuccessorOriginalRegular HironakaResolutionSpaceLocal
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetRankLoci HironakaActualVanishingIntrinsicHSTransport
  HironakaActualHilbertSamuelLexOrder HironakaActualCompactHSMaximalProfile
  HironakaLocalPrincipalization HironakaG8OpenHoloEmbeddingComposition MarkedIdealTowerTransport MaxLocusLocal
  HironakaG8ChronologicalNativeClassAtlas HironakaG8FiniteSingularTowerMerge
  HironakaG8SingularFootprintExtension BlowupTowerIsomorphism HironakaNormalCrossingsOpenRestrictionSeparation

variable {n : ℕ} {X Y : CMfd.{0} (n+1)}

local notation "HS[" U "]" => hilbertSamuelAt (vanishingIdeal (n := n+1) U)

private abbrev whole {A : CMfd.{0} (n+1)} (W : Set A) (E : List (Set A)) :
    MarkedIdeal (n+1) A := ⟨univ,E,vanishingIdeal (n := n+1) W,1⟩

/-- The actual coherent full analytic stalk is an attainable lex label. -/
def realizedProfile {A : CMfd.{0} (n+1)} (W : Set A) (a : A) :
    ActualAnalyticLexHilbertSamuelProfile (n+1) :=
  ⟨toLex (HS[W] a), ⟨wholeChartStalkIdeal (vanishingIdeal (n := n+1) W) a a
    (mem_chart_source (ComplexModel (n+1)) a),rfl⟩⟩

/-- A clipped native phase decreases the actual profile of every still
singular point over the compact task. The source upper bound is needed
only on the singular fibre, even for carriers of mixed dimension. -/
theorem clipped_singular_native_profile_drop
    {Z : CMfd.{0} (n+1)} (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (P : BlowupTower X Y) (O : Opens Y) (S : BlowupTower (CMfd.of (n := n+1) O) Z)
    (V : Opens X) (hVO : openPreimage P V ≤ O) (K : Set X)
    (E : List (Set O)) (H : ℕ → ℕ) :
    let U := (Subtype.val : O → Y) ⁻¹' strictTransform (n+1) P.proj W
    let D := nestedOpens O (openPreimage P V)
    let e := (nestedOpensDiffeo (n := n+1) hVO).symm
    let tail := transport e (restrict D S)
    let T := (restrict V P).append tail.tower
    ActualNativePhase (X := CMfd.of (n := n+1) O) U E H S →
    (∀ x ∈ P.proj ⁻¹' K ∩ singularSet (n := n+1) (strictTransform (n+1) P.proj W),
      toLex (HS[strictTransform (n+1) P.proj W] x) ≤ toLex H) →
    ∀ z, (T.proj z).val ∈ K →
      z ∈ singularSet (n := n+1) (strictTransform (n+1) T.proj ((Subtype.val : V → X) ⁻¹' W)) →
      toLex (HS[strictTransform (n+1) T.proj ((Subtype.val : V → X) ⁻¹' W)] z) < toLex H := by
  dsimp only
  intro hPhase hUpper
  let U₀ := strictTransform (n+1) P.proj W
  let U := (Subtype.val : O → Y) ⁻¹' U₀
  let D := nestedOpens O (openPreimage P V)
  let e := (nestedOpensDiffeo (n := n+1) hVO).symm
  let tail := transport e (restrict D S)
  let T := (restrict V P).append tail.tower
  let UEnd := strictTransform (n+1) T.proj ((Subtype.val : V → X) ⁻¹' W)
  let US := strictTransform (n+1) S.proj U
  let b : tail.target → Z := fun z => (tail.back z).val
  change ∀ z : tail.target, (T.proj z).val ∈ K → z ∈ singularSet (n := n+1) UEnd →
    toLex (HS[UEnd] z) < toLex H
  intro z hz hSing
  obtain ⟨hProj,hEq⟩ := clipped_tail_geometry P O S V hVO W
  have hStrict : UEnd = b ⁻¹' US := hEq
  have hb : IsOpenHoloEmbedding (n+1) b := ⟨openPreimage S D,tail.back,fun _ => rfl⟩
  have hSingB : b z ∈ singularSet (n := n+1) US := by
    rw [hStrict] at hSing
    obtain ⟨hm,hn⟩ := mem_singularSet_iff.mp hSing
    exact mem_singularSet_iff.mpr ⟨hm, fun k hk => hn k (hb.regularAtDim_preimage hk)⟩
  have hU₀ := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hW P
  have hU : IsComplexAnalyticSubset (n := n+1) U :=
    AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hU₀ O
  have hProject := (actual_singular_history_original_regular_protection U hU S
    (intrinsic_stage_native_history U S hPhase.singular)).2.2.2.2.2.1
  have hSource : S.proj (b z) ∈ singularSet (n := n+1) U := hProject hSingB
  have hOn : P.proj (S.proj (b z)).val ∈ K := (hProj z) ▸ hz
  have hOld : (S.proj (b z)).val ∈ singularSet (n := n+1) U₀ := by
    rwa [show U = (Subtype.val : O → Y) ⁻¹' U₀ from rfl,singularSet_preimage_val O] at hSource
  have hReadSource := funext (hilbertSamuelAt_vanishing_actual_open_any (n := n+1) O U₀ (S.proj (b z)))
  have hLe : toLex (HS[U] (S.proj (b z))) ≤ toLex H := by
    rw [show HS[U] (S.proj (b z)) = _ from hReadSource]
    exact hUpper _ ⟨hOn,hOld⟩
  have hDrop : toLex (HS[US] (b z)) < toLex H := by
    by_cases he : HS[U] (S.proj (b z)) = H
    · exact hPhase.strictDrop _ he
    · exact (Pi.toLex_monotone (hPhase.nonincrease (b z))).trans_lt
        (lt_of_le_of_ne hLe (fun h => he (congrArg ofLex h)))
  have hRead : HS[UEnd] z = HS[US] (b z) := by
    rw [hStrict]
    apply funext
    intro ℓ
    exact (hilbertSamuelAt_vanishing_actual_biholomorphic_any tail.back
      ((Subtype.val : openPreimage S D → Z) ⁻¹' US) z ℓ).trans
      (hilbertSamuelAt_vanishing_actual_open_any (openPreimage S D) US (tail.back z) ℓ)
  rw [hRead]
  exact hDrop


/-- An original mark-one canonical prefix with intrinsic singular centres,
without a principal residual condition. -/
structure CanonicalSingularState (W : Set X) (E : List (Set X)) (P : BlowupTower X Y) : Prop where
  analytic : IsComplexAnalyticSubset (n := n+1) W
  domain : IsInvDomain (n+1) (whole W E)
  canonical : IsCanonical (whole W E) ((canonicalInvariant (n+1)).inv (whole W E)) P
  singular : HironakaStageCenters.StageCentres
    (fun T C => C ⊆ singularSet (n := n+1) (strictTransform (n+1) T.proj W)) P

/-- The physical data of a single chosen native phase and its saturated
append. The next chronological certificate is a separate local serving law. -/
structure NativeServingStep (W : Set X) (E : List (Set X)) (P : BlowupTower X Y)
    (K : Set X) (H : ℕ → ℕ) where
  phaseOpen : Opens Y
  phaseTarget : CMfd.{0} (n+1)
  phaseTower : BlowupTower (CMfd.of (n := n+1) phaseOpen) phaseTarget
  phase : ActualNativePhase (X := CMfd.of (n := n+1) phaseOpen)
    ((Subtype.val : phaseOpen → Y) ⁻¹' strictTransform (n+1) P.proj W)
    ((geoTransformAlong (whole W E) P).E.map ((Subtype.val : phaseOpen → Y) ⁻¹' ·)) H phaseTower
  baseOpen : Opens X
  covers : K ⊆ baseOpen
  saturation : openPreimage P baseOpen ≤ phaseOpen

namespace NativeServingStep
variable {W : Set X} {E : List (Set X)} {P : BlowupTower X Y} {K : Set X} {H : ℕ → ℕ}
    (s : NativeServingStep W E P K H)
abbrev source := CMfd.of (n := n+1) s.baseOpen
abbrev nextCarrier : Set s.source := (Subtype.val : s.baseOpen → X) ⁻¹' W
abbrev nextBoundary : List (Set s.source) := E.map ((Subtype.val : s.baseOpen → X) ⁻¹' ·)
abbrev nextTask : Set s.source := (Subtype.val : s.baseOpen → X) ⁻¹' K
abbrev tail :=
  transport (nestedOpensDiffeo (n := n+1) s.saturation).symm
    (restrict (nestedOpens s.phaseOpen (openPreimage P s.baseOpen)) s.phaseTower)
abbrev tower : BlowupTower s.source s.tail.target :=
  (restrict s.baseOpen P).append s.tail.tower

/-- The exact singular-fibre rank decreases for this actual phase,
irrespective of how its original canonical centre comparison is proved. -/
theorem profile_decreases
    (hs : CanonicalSingularState W E P)
    (hBound : ∀ x ∈ P.proj ⁻¹' K ∩ singularSet (n := n+1) (strictTransform (n+1) P.proj W),
      toLex (HS[strictTransform (n+1) P.proj W] x) ≤ toLex H) :
    ∀ z ∈ s.tower.proj ⁻¹' s.nextTask ∩ singularSet (n := n+1)
      (strictTransform (n+1) s.tower.proj s.nextCarrier),
      toLex (HS[strictTransform (n+1) s.tower.proj s.nextCarrier] z) < toLex H :=
  fun z hz => clipped_singular_native_profile_drop W hs.analytic P s.phaseOpen s.phaseTower
    s.baseOpen s.saturation K _ H s.phase hBound z hz.1 hz.2

/-- The serving law only needs to provide chronological CAN for the actual
append. The other next-state fields follow from its physical phase. -/
theorem nextState_of_canonical (hs : CanonicalSingularState W E P)
    (hCan : IsCanonical (whole s.nextCarrier s.nextBoundary)
      ((canonicalInvariant (n+1)).inv (whole s.nextCarrier s.nextBoundary)) s.tower) :
    CanonicalSingularState s.nextCarrier s.nextBoundary s.tower := by
  let V := s.baseOpen
  let L := restrict V P
  let O := s.phaseOpen
  let D := nestedOpens O (openPreimage P V)
  let e := (nestedOpensDiffeo (n := n+1) s.saturation).symm
  let S := s.phaseTower
  let R := restrict D S
  let T := (transport e R).tower
  let U := (Subtype.val : O → Y) ⁻¹' strictTransform (n+1) P.proj W
  let U' := strictTransform (n+1) L.proj s.nextCarrier
  have hU := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hs.analytic P
  have hQ := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hs.analytic V
  have hRec : MarkedIdeal.pullback (Subtype.val : V → X) (whole W E) =
      whole s.nextCarrier s.nextBoundary :=
    HironakaEmbeddedBoundary.pullback_val_mk_vanishingIdeal V E W
  have hM : IsInvDomain (n+1) (whole s.nextCarrier s.nextBoundary) :=
    hRec ▸ InvDomainTowerAlong.isInvDomain_pullback_val V hs.domain
  refine ⟨hQ,hM,hCan,?_⟩
  have hL := singular_stages_restrict W V P hs.singular
  have hRU := singular_stages_restrict U D S s.phase.singular
  have hUJ : U' = ((Subtype.val : openPreimage P V → Y) ⁻¹' strictTransform (n+1) P.proj W) :=
    strictTransform_restricted_tower V P W
  have hUT : e.symm ⁻¹' U' = (Subtype.val : D → O) ⁻¹' U := by
    rw [hUJ]
    rfl
  have hUclosed : IsClosed U' := by rw [hUJ]; exact hU.isClosed.preimage continuous_subtype_val
  have hRT := singular_stages_of_tower_iso U' hUclosed e.symm (transport_isTowerIso e R).symm
  rw [hUT] at hRT
  have hTS : HironakaStageCenters.StageCentres
      (fun B C => C ⊆ singularSet (n := n+1) (strictTransform (n+1) B.proj U')) T :=
    hRT hRU
  change HironakaStageCenters.StageCentres
    (fun B C => C ⊆ singularSet (n := n+1) (strictTransform (n+1) B.proj s.nextCarrier)) (L.append T)
  exact intrinsic_stage_append s.nextCarrier L T hL hTS


open HironakaG8NativeRelativeClearing HironakaG8NativeSimultaneousCentre NonmonomialOrderRegime
  NonmonomialOrderLocal GermIdealOrder in
/-- The checked weighted quotient-chart atlas gives the missing actual
chronological comparison for a clipped serving step. The atlas data
are read on the very same restricted prefix and physical native tail. -/
theorem nextState_of_weighted_quotient_atlas
    (hs : CanonicalSingularState W E P) {I : Type} {ι : I → Type} [∀ i, Fintype (ι i)]
    {U F : Set (openPreimage P s.baseOpen)} {B : List (Set (openPreimage P s.baseOpen))}
    (A : NativeWindows (CMfd.of (n := n+1) (openPreimage P s.baseOpen)) I U B H F)
    (d e : ℕ) (hd : 1 < d) (he : 1 ≤ e) (hMark : A.mark = d * e) :
    let M := whole s.nextCarrier s.nextBoundary
    let P' := restrict s.baseOpen P
    let L := geoTransformAlong M P'
    CentresOrdGt M d P' →
    NativeSimultaneousStages (canonicalInvariant (n+1)) A.openSet A.powered s.tail.tower →
    cosupport (n+1) univ (nmPart L) d ⊆ F →
    (∀ i, NativeRestartQuotientChart (ι := ι i)
      (Y := CMfd.of (n := n+1) (A.openSet i))
      (MarkedIdeal.pullback (Subtype.val : A.openSet i → openPreimage P s.baseOpen) L)
      (A.record i) d) →
    CanonicalSingularState s.nextCarrier s.nextBoundary s.tower := by
  dsimp only
  intro hHigh hSync hContains hCharts
  let M := whole s.nextCarrier s.nextBoundary
  let P' := restrict s.baseOpen P
  let R := canonicalInvariant.{0} (n+1)
  have hPull : MarkedIdeal.pullback (Subtype.val : s.baseOpen → X) (whole W E) = M :=
    HironakaEmbeddedBoundary.pullback_val_mk_vanishingIdeal s.baseOpen E W
  have hM : IsInvDomain (n+1) M := hPull ▸
    InvDomainTowerAlong.isInvDomain_pullback_val s.baseOpen hs.domain
  have hCan : IsCanonical M (R.inv M) P' := hPull ▸
    Seq.ResolutionInvariantExt.isCanonical_restrict R hs.domain s.baseOpen P hs.canonical
  exact s.nextState_of_canonical hs
    (append_chronological_canonical_of_weighted_quotient_atlas A M hM rfl P' hCan d e
      (Nat.le_of_lt hd) hd he hMark hHigh s.tail.tower hSync hContains hCharts)

end NativeServingStep

variable (n) in
/-- A serving law supplies a chronological CAN step for the actual
largest compact-fibre label. The law has no numerical decrease premise. -/
def HasCanonicalNativeServing : Prop :=
  ∀ {X Y : CMfd.{0} (n+1)} {W : Set X} {E : List (Set X)} {P : BlowupTower X Y},
  CanonicalSingularState W E P →
  ∀ {K : Set X}, IsCompact K → ∀ a ∈ P.proj ⁻¹' K ∩ singularSet (n := n+1) (strictTransform (n+1) P.proj W),
    (∀ x ∈ P.proj ⁻¹' K ∩ singularSet (n := n+1) (strictTransform (n+1) P.proj W),
      toLex (HS[strictTransform (n+1) P.proj W] x) ≤ toLex (HS[strictTransform (n+1) P.proj W] a)) →
    ∃ s : NativeServingStep W E P K (HS[strictTransform (n+1) P.proj W] a),
      CanonicalSingularState s.nextCarrier s.nextBoundary s.tower

/-- A finite physical trace of canonical native phases, with actual
label realizations at every step and a singular-free compact terminal fibre. -/
inductive CanonicalNativeServingTrace :
    {A B : CMfd.{0} (n+1)} → (W : Set A) → List (Set A) → BlowupTower A B → Set A →
      List (ActualAnalyticLexHilbertSamuelProfile (n+1)) → Prop
  | done {A B : CMfd.{0} (n+1)} {W : Set A} {E : List (Set A)} {P : BlowupTower A B} {K : Set A}
      (state : CanonicalSingularState W E P)
      (clear : Disjoint (P.proj ⁻¹' K) (singularSet (n := n+1) (strictTransform (n+1) P.proj W))) :
      CanonicalNativeServingTrace W E P K []
  | next {A B : CMfd.{0} (n+1)} {W : Set A} {E : List (Set A)} {P : BlowupTower A B} {K : Set A}
      {labels : List (ActualAnalyticLexHilbertSamuelProfile (n+1))}
      (a : B) (aOn : a ∈ P.proj ⁻¹' K ∩ singularSet (n := n+1) (strictTransform (n+1) P.proj W))
      (s : NativeServingStep W E P K (HS[strictTransform (n+1) P.proj W] a))
      (state : CanonicalSingularState s.nextCarrier s.nextBoundary s.tower)
      (rest : CanonicalNativeServingTrace s.nextCarrier s.nextBoundary s.tower s.nextTask labels) :
      CanonicalNativeServingTrace W E P K (realizedProfile (strictTransform (n+1) P.proj W) a :: labels)

/-- Realized analytic Hilbert--Samuel labels stop the actual canonical
service whenever the local chronological serving law is available. -/
theorem canonical_native_serving_terminates
    (serve : HasCanonicalNativeServing n)
    {W : Set X} {E : List (Set X)} (P : BlowupTower X Y)
    (state : CanonicalSingularState W E P) (K : Set X) (hK : IsCompact K) :
    ∃ labels, CanonicalNativeServingTrace W E P K labels := by
  classical
  have solve : ∀ bound : ActualAnalyticLexHilbertSamuelProfile (n+1),
      ∀ {A B : CMfd.{0} (n+1)} {W : Set A} {E : List (Set A)} (P : BlowupTower A B)
        (_state : CanonicalSingularState W E P) (K : Set A) (_hK : IsCompact K),
        (∀ x ∈ P.proj ⁻¹' K ∩ singularSet (n := n+1) (strictTransform (n+1) P.proj W),
          realizedProfile (strictTransform (n+1) P.proj W) x ≤ bound) →
        ∃ labels, CanonicalNativeServingTrace W E P K labels := by
    intro bound
    induction bound using (actual_analyticHilbertSamuel_lex_wellFounded (n+1)).wf.induction with
    | h bound ih =>
      intro A B W E P hs K hK hBound
      by_cases hClear : Disjoint (P.proj ⁻¹' K) (singularSet (n := n+1) (strictTransform (n+1) P.proj W))
      · exact ⟨[],.done hs hClear⟩
      let U := strictTransform (n+1) P.proj W
      let F := P.proj ⁻¹' K ∩ singularSet (n := n+1) U
      have hU := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hs.analytic P
      have hComp : IsCompact F := ((isProperMap_proj P).isCompact_preimage hK).inter_right
        (isClosed_singularSet hU.isClosed)
      obtain ⟨a,ha,hMax⟩ := exists_actual_compact_hs_lex_maximum (vanishingIdeal (n := n+1) U)
        (CartanIrreducible.cartanCoherence U hU) F hComp (not_disjoint_iff_nonempty_inter.mp hClear)
      obtain ⟨s,hNext⟩ := serve hs hK a ha hMax
      have hK' : IsCompact s.nextTask :=
        (Topology.IsInducing.subtypeVal.isCompact_preimage_iff
          (fun x hx => ⟨⟨x,s.covers hx⟩,rfl⟩)).mpr hK
      let U' := strictTransform (n+1) s.tower.proj s.nextCarrier
      let F' := s.tower.proj ⁻¹' s.nextTask ∩ singularSet (n := n+1) U'
      by_cases hNe' : F'.Nonempty
      · have hU' := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj
          hNext.analytic s.tower
        have hComp' : IsCompact F' := ((isProperMap_proj s.tower).isCompact_preimage hK').inter_right
          (isClosed_singularSet hU'.isClosed)
        obtain ⟨b,hb,hMax'⟩ := exists_actual_compact_hs_lex_maximum (vanishingIdeal (n := n+1) U')
          (CartanIrreducible.cartanCoherence U' hU') F' hComp' hNe'
        have hLt : realizedProfile U' b < realizedProfile U a := s.profile_decreases hs hMax b hb
        obtain ⟨ls,hls⟩ := ih (realizedProfile U' b) (hLt.trans_le (hBound a ha))
          s.tower hNext s.nextTask hK' hMax'
        exact ⟨_,.next a ha s hNext hls⟩
      · exact ⟨_,.next a ha s hNext (.done hNext (by
          by_contra hh
          exact hNe' (not_disjoint_iff_nonempty_inter.mp hh)))⟩
  by_cases hClear : Disjoint (P.proj ⁻¹' K) (singularSet (n := n+1) (strictTransform (n+1) P.proj W))
  · exact ⟨[],.done state hClear⟩
  let U := strictTransform (n+1) P.proj W
  let F := P.proj ⁻¹' K ∩ singularSet (n := n+1) U
  have hU := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj state.analytic P
  have hComp : IsCompact F := ((isProperMap_proj P).isCompact_preimage hK).inter_right
    (isClosed_singularSet hU.isClosed)
  obtain ⟨a,_,hm⟩ := exists_actual_compact_hs_lex_maximum (vanishingIdeal (n := n+1) U)
    (CartanIrreducible.cartanCoherence U hU) F hComp (not_disjoint_iff_nonempty_inter.mp hClear)
  exact solve (realizedProfile U a) P state K hK hm

end
end Hironaka.HironakaG8CanonicalNativeServingRank
