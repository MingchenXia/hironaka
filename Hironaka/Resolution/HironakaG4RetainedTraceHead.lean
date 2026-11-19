import Hironaka.Resolution.HironakaG4OrderedRetainedDefectTrace
import Hironaka.Resolution.HironakaG4RetainedCrestPhaseIsomorphism

/-! A first-phase view on the actual source of an ordered retained trace. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4RetainedTraceHead
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism BlowupTowerIsoTail
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  MarkedIdealTowerTransport HomogenizedGlueingTower IdealWeightPowers
  NormalCrossings StepOneTangentChange
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalDistinctDefect
  HironakaG4RetainedDefectRelativeDecrease HironakaG4OrderedRetainedDefectTrace
  HironakaG4RetainedCrestPhaseRestriction HironakaG4RetainedCrestPhaseIsomorphism
  HironakaG4RetainedCurrentStamp HironakaG4PreparedCentreCoordinates
  HironakaActualRetainedBornResidualHistory

/-- The next actual phase and exact continuation on the current source.
A zero count gives a literal empty history up to an actual tower isomorphism. -/
inductive OrderedRetainedTraceHead {n : ℕ} (hn : 0 < n) {X Y : CMfd.{u} n}
    (N : Set X) (old born : List (Set X)) (μ : WithTop RetainedStampRank) (T : BlowupTower X Y) :
    ℕ → Type (u+1)
  | done (defect_empty : actualFamilyDistinctDefect N (oldResidualPart N old born) = ∅)
      (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
      (iso : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)
        T (BlowupTower.refl : BlowupTower X X) e) :
      OrderedRetainedTraceHead hn N old born μ T 0
  | phase {A Z : CMfd.{u} n} (Q : BlowupTower X A) (S : BlowupTower A Z)
      (crest : RetainedDefectCrestPhase hn N old born Q) (bound : (crest.rank : WithTop _) < μ)
      (carrier_test : IsGeoTestTower (geometricTemplate N born) Q)
      (full_test : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) Q)
      (continuation : OrderedRetainedDefectTrace hn
        (geoTransformAlong (geometricTemplate N born) Q).N (old.map (strictAlong Q))
        (geoTransformAlong (geometricTemplate N born) Q).E crest.rank S)
      (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z)
      (iso : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T (Q.append S) e) :
      OrderedRetainedTraceHead hn N old born μ T (continuation.phaseCount + 1)

variable {n : ℕ} {X Y : CMfd.{u} n} {N : Set X} {old born : List (Set X)}
  {μ : WithTop RetainedStampRank} {T : BlowupTower X Y} {k : ℕ}

theorem restrict_iso_same_source {Z : CMfd.{u} n} {S : BlowupTower X Z}
    {e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z}
    (h : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T S e) (U : Opens X) :
    let hU : ∀ p : Y, p ∈ openPreimage T U ↔ e p ∈ openPreimage S U :=
      isTowerIso_mem_openPreimage_iff (V' := U) (V := U) h (fun _ => Iff.rfl)
    IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
      (restrict U T) (restrict U S) (diffeoOpens e (openPreimage T U) (openPreimage S U) hU) := by
  intro hU
  have hh : ∀ p : X, p ∈ U ↔ (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) p ∈ U := fun _ => Iff.rfl
  have hIso := isTowerIso_restrictOpens hh h hU
  have hBase : diffeoOpens (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) U U hh =
      Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞ := Diffeomorph.ext fun _ => rfl
  rw [hBase] at hIso
  exact hIso

theorem phaseCount_cast {hn : 0 < n} {N' : Set X}
    {old' born' : List (Set X)} {μ' : WithTop RetainedStampRank}
    (hN : N = N') (hOld : old = old') (hBorn : born = born') (hRank : μ = μ')
    (trace : OrderedRetainedDefectTrace hn N old born μ T) :
    (show OrderedRetainedDefectTrace hn N' old' born' μ' T from
      hN ▸ hOld ▸ hBorn ▸ hRank ▸ trace).phaseCount = trace.phaseCount := by
  subst N'
  subst old'
  subst born'
  subst μ'
  rfl

set_option maxHeartbeats 1000000 in
private def OrderedRetainedTraceHead.restrictOpen {hn : 0 < n}
    (V : OrderedRetainedTraceHead hn N old born μ T k) (U : Opens X)
    (hG : NativeRetainedGeometry N old born) :
    let u := (Subtype.val : U → X)
    OrderedRetainedTraceHead hn (u ⁻¹' N) (old.map (u ⁻¹' ·)) (born.map (u ⁻¹' ·))
      μ (restrict U T) k := by
  intro u
  let XU := CMfd.of (n := n) U
  let NU := u ⁻¹' N
  let OU := old.map (u ⁻¹' ·)
  let BU := born.map (u ⁻¹' ·)
  cases V with
  | done hDef e hIso =>
    have hD := (actual_retained_defect_and_rank_open hn hG.carrier hG.full hG.born_transverse hG.dense U).1
    rw [hDef,preimage_empty] at hD
    exact .done hD _ (restrict_iso_same_source hIso U)
  | @phase A Z Q S P hRank hQ hFullQ history e hIso =>
    let V := openPreimage Q U
    let v := (Subtype.val : V → A)
    let Q' := restrict U Q
    let S' := restrict V S
    let M := geometricTemplate N born
    let M' := geometricTemplate (X := XU) NU BU
    let A₀ := geoTransformAlong M Q
    let A' := geoTransformAlong M' Q'
    let L := old.map (strictAlong Q)
    let L' := OU.map (strictAlong Q')
    let P' := restrictRetainedCrestPhase hn hG.carrier hG.full hG.born_transverse hG.dense P U
    have hR : P'.rank = P.rank :=
      restrictRetainedCrestPhase_rank hn hG.carrier hG.full hG.born_transverse hG.dense P U
    have hBound : (P'.rank : WithTop RetainedStampRank) < μ := hR.symm ▸ hRank
    have hRec := actual_retained_born_recorded_residual_dictionary hn hG.carrier hG.full
      hG.born_transverse hG.dense Q hQ hFullQ
    let hCur : NativeRetainedGeometry A₀.N L A₀.E :=
      ⟨hRec.1,hRec.2.1,hRec.2.2.1,hRec.2.2.2.1⟩
    let tail := history.restrictOpen V hCur
    have hCarrier := geoTransformAlong_restrict U hG.carrier isCoherent_unitIdeal Q hQ
    rw [HironakaG34NonPureLowDim.template_pullback (X := X) (Y := XU)] at hCarrier
    have hN : v ⁻¹' A₀.N = A'.N := (congrArg (fun M : MarkedIdeal n V => M.N) hCarrier).symm
    have hB : A₀.E.map (v ⁻¹' ·) = A'.E := (congrArg (fun M : MarkedIdeal n V => M.E) hCarrier).symm
    have hL : L.map (v ⁻¹' ·) = L' := by
      simp only [L,L',OU,List.map_map]
      apply List.map_congr_left
      intro F _hF
      exact (strictAlong_restrict U Q F).symm
    have hRankEq : (P.rank : WithTop RetainedStampRank) = P'.rank :=
      congrArg (fun r : RetainedStampRank => (r : WithTop RetainedStampRank)) hR.symm
    let tail' : OrderedRetainedDefectTrace hn A'.N L' A'.E P'.rank S' :=
      hN ▸ hL ▸ hB ▸ hRankEq ▸ tail
    have hCount : tail'.phaseCount = history.phaseCount :=
      phaseCount_cast hN hL hB hRankEq tail
    have hQ' : IsGeoTestTower M' Q' := by
      have h := isGeoTestTower_restrict U hG.carrier isCoherent_unitIdeal Q hQ
      rw [HironakaG34NonPureLowDim.template_pullback (X := X) (Y := XU)] at h
      exact h
    have hFullQ' : IsGeoTestTower (geometricTemplate (X := XU) (univ : Set U) (OU ++ BU)) Q' := by
      have h := isGeoTestTower_restrict U isClosedSubmanifold_univ isCoherent_unitIdeal Q hFullQ
      rw [HironakaG34NonPureLowDim.template_pullback (X := X) (Y := XU),preimage_univ,List.map_append] at h
      exact h
    have hIso' := (restrict_iso_same_source hIso U).trans (isTowerIso_restrict_append U Q S)
    have hCompose : (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) XU ∞).trans
        (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) XU ∞) =
          Diffeomorph.refl 𝓘(ℂ,ComplexModel n) XU ∞ := Diffeomorph.ext fun _ => rfl
    rw [hCompose] at hIso'
    rw [←hCount]
    exact .phase Q' S' P' hBound hQ' hFullQ' tail' _ hIso'

theorem rebase_iso_same_source {X' Z Z' : CMfd.{u} n} {S : BlowupTower X Z}
    {S' : BlowupTower X' Z'} {e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z}
    (h : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T S e)
    (φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {e' : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z} (h' : IsTowerIso φ S' S e') :
    IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X' ∞)
      (transport φ T).tower S' (((transport φ T).back.trans e).trans e'.symm) := by
  have hIso := ((transport_isTowerIso φ T).trans h).trans h'.symm
  have hBase : (φ.trans (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)).trans φ.symm =
      Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X' ∞ := by
    ext z
    exact φ.symm_apply_apply z
  rw [hBase] at hIso
  exact hIso

set_option maxHeartbeats 1000000 in
private def OrderedRetainedTraceHead.rebase {hn : 0 < n} {X' : CMfd.{u} n}
    (V : OrderedRetainedTraceHead hn N old born μ T k)
    (φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X) (hG : NativeRetainedGeometry N old born) :
    OrderedRetainedTraceHead hn (φ ⁻¹' N) (old.map (φ ⁻¹' ·)) (born.map (φ ⁻¹' ·))
      μ (transport φ T).tower k := by
  let N' := φ ⁻¹' N
  let O' := old.map (φ ⁻¹' ·)
  let B' := born.map (φ ⁻¹' ·)
  cases V with
  | done hDef e hIso =>
    have hD := (actual_retained_defect_and_rank_biholomorph hn hG.carrier hG.full
      hG.born_transverse hG.dense φ).1
    rw [hDef,preimage_empty] at hD
    exact .done hD _ (rebase_iso_same_source hIso φ (transport_isTowerIso φ (.refl : BlowupTower X X)))
  | @phase A Z Q S P hRank hQ hFullQ history e hIso =>
    let Q' := transport φ Q
    let ψ := Q'.back
    let S' := transport ψ S
    let M := geometricTemplate N born
    let M' := geometricTemplate N' B'
    let A₀ := geoTransformAlong M Q
    let A' := geoTransformAlong M' Q'.tower
    let L := old.map (strictAlong Q)
    let L' := O'.map (strictAlong Q'.tower)
    have hIsoQ := transport_isTowerIso φ Q
    let P' := rebaseRetainedCrestPhase hn hG.carrier hG.full hG.born_transverse hG.dense φ hIsoQ P
    have hR : P'.rank = P.rank :=
      rebaseRetainedCrestPhase_rank hn hG.carrier hG.full hG.born_transverse hG.dense φ hIsoQ P
    have hBound : (P'.rank : WithTop RetainedStampRank) < μ := hR.symm ▸ hRank
    have hRec := actual_retained_born_recorded_residual_dictionary hn hG.carrier hG.full
      hG.born_transverse hG.dense Q hQ hFullQ
    let hCur : NativeRetainedGeometry A₀.N L A₀.E :=
      ⟨hRec.1,hRec.2.1,hRec.2.2.1,hRec.2.2.2.1⟩
    let tail := history.rebase ψ hCur
    have hCarrier := IsTowerIso.geoTransformAlong_eq φ hG.carrier isCoherent_unitIdeal hIsoQ hQ
    rw [HironakaG34NonPureLowDim.template_pullback (X := X) (Y := X')] at hCarrier
    have hN : ψ ⁻¹' A₀.N = A'.N :=
      (congrArg (fun M : MarkedIdeal n Q'.target => M.N) hCarrier).symm
    have hB : A₀.E.map (ψ ⁻¹' ·) = A'.E :=
      (congrArg (fun M : MarkedIdeal n Q'.target => M.E) hCarrier).symm
    have hL : L.map (ψ ⁻¹' ·) = L' := by
      simp only [L,L',O',List.map_map]
      apply List.map_congr_left
      intro F _hF
      exact (hIsoQ.strictAlong_eq F).symm
    have hRankEq : (P.rank : WithTop RetainedStampRank) = P'.rank :=
      congrArg (fun r : RetainedStampRank => (r : WithTop RetainedStampRank)) hR.symm
    let tail' : OrderedRetainedDefectTrace hn A'.N L' A'.E P'.rank S'.tower :=
      hN ▸ hL ▸ hB ▸ hRankEq ▸ tail
    have hCount : tail'.phaseCount = history.phaseCount :=
      phaseCount_cast hN hL hB hRankEq tail
    have hQ' : IsGeoTestTower M' Q'.tower := by
      have h := (IsTowerIso.isGeoTestTower_iff φ hG.carrier isCoherent_unitIdeal hIsoQ).mpr hQ
      rw [HironakaG34NonPureLowDim.template_pullback (X := X) (Y := X')] at h
      exact h
    have hFullQ' : IsGeoTestTower (geometricTemplate (X := X') (univ : Set X') (O' ++ B')) Q'.tower := by
      have h := (IsTowerIso.isGeoTestTower_iff φ isClosedSubmanifold_univ isCoherent_unitIdeal hIsoQ).mpr hFullQ
      rw [HironakaG34NonPureLowDim.template_pullback (X := X) (Y := X'),preimage_univ,List.map_append] at h
      exact h
    have hIso' := rebase_iso_same_source hIso φ (hIsoQ.append (transport_isTowerIso ψ S))
    rw [←hCount]
    exact .phase Q'.tower S'.tower P' hBound hQ' hFullQ' tail' _ hIso'

/-- Extract the first native crest on the actual source, keeping the exact
remaining tower and reducing the number of selected phases by one. -/
def orderedRetainedTraceHead {hn : 0 < n} (trace : OrderedRetainedDefectTrace hn N old born μ T) :
    OrderedRetainedTraceHead hn N old born μ T trace.phaseCount := by
  induction trace with
  | done hDef => exact .done hDef _ (IsTowerIso.refl_self _)
  | phase T S crest hBound hT hFull tail _ih =>
    exact .phase T S crest hBound hT hFull tail _ (IsTowerIso.refl_self _)
  | restrictOpen O hG _trace ih => exact ih.restrictOpen O hG
  | rebase e hG _trace ih => exact ih.rebase e hG

end
end Hironaka.HironakaG4RetainedTraceHead
