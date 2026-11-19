import Hironaka.Resolution.HironakaG4RetainedPreparationEvent
import Hironaka.Resolution.HironakaG4RetainedTraceHead

/-! Read the actual first event of a preparation tape after its recorded
restrictions, rebases, and concatenations. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4RetainedPreparationHead
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism BlowupTowerIsoTail
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealTowerTransport HomogenizedGlueingTower
  HironakaSharpActualFiniteChronologicalHistory HironakaG4OrderedRetainedDefectTrace
  HironakaG4RetainedPreparationTrace HironakaG4RetainedPreparationEvent
  HironakaG4RetainedPreparationHeadTests HironakaG4RetainedTraceHead
  HironakaG4SaturatedRetainedEquivariance HironakaG4RetainedPreparationLowerHistory

variable {n : ℕ}

/-- A preparation continuation either contains another actual event or is
the literal identity tower on the current source. -/
inductive RetainedPreparationTail (hn : 0 < n) {X : CMfd.{u} n}
    (N : Set X) (old born : List (Set X)) :
    {Y : CMfd.{u} n} → List RetainedPreparationPhase → BlowupTower X Y → Type (u+1)
  | nil : RetainedPreparationTail hn N old born [] (BlowupTower.refl : BlowupTower X X)
  | trace {Y : CMfd.{u} n} {phases : List RetainedPreparationPhase} {T : BlowupTower X Y}
      (tape : RetainedPreparationTrace hn N old born phases T) :
      RetainedPreparationTail hn N old born phases T

variable {hn : 0 < n} {X Y Z X' : CMfd.{u} n} {N : Set X} {old born : List (Set X)}
  {T : BlowupTower X Y} {phases : List RetainedPreparationPhase}

/-- A nonempty continuation carries the lower witnesses of its actual
recorded trace. The identity continuation requires no lower witnesses. -/
def RetainedPreparationTail.usesLowerHistory (P : SharpHistoryPredicate.{u} n)
    (tail : RetainedPreparationTail hn N old born phases T) : Prop :=
  match tail with
  | .nil => True
  | .trace tape => HironakaG4RetainedPreparationLowerHistory.usesLowerHistory P tape

variable {P : SharpHistoryPredicate.{u} n}

private def RetainedPreparationTail.restrictOpenWithLower (tail : RetainedPreparationTail hn N old born phases T)
    (hUses : tail.usesLowerHistory P) (g : NativeRetainedGeometry N old born) (O : Opens X) :
    let f := (Subtype.val : O → X)
    { R : RetainedPreparationTail hn (f ⁻¹' N) (old.map (f ⁻¹' ·)) (born.map (f ⁻¹' ·))
        phases (restrict O T) // R.usesLowerHistory P } := by
  intro f
  cases tail with
  | nil => exact ⟨.nil,trivial⟩
  | trace tape => exact ⟨.trace (tape.restrictOpen O g),hUses⟩

private def RetainedPreparationTail.rebaseWithLower (tail : RetainedPreparationTail hn N old born phases T)
    (hUses : tail.usesLowerHistory P) (g : NativeRetainedGeometry N old born)
    (e : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X) :
    { R : RetainedPreparationTail hn (e ⁻¹' N) (old.map (e ⁻¹' ·)) (born.map (e ⁻¹' ·))
        phases (transport e T).tower // R.usesLowerHistory P } := by
  cases tail with
  | nil => exact ⟨.nil,trivial⟩
  | trace tape => exact ⟨.trace (tape.rebase e g),hUses⟩

/-- Literal current-record equalities transport the continuation and its
lower witnesses together. -/
def RetainedPreparationTail.castWithLower {N' : Set X} {old' born' : List (Set X)}
    (hN : N = N') (hOld : old = old') (hBorn : born = born')
    (tail : { R : RetainedPreparationTail hn N old born phases T // R.usesLowerHistory P }) :
    { R : RetainedPreparationTail hn N' old' born' phases T // R.usesLowerHistory P } := by
  subst N'
  subst old'
  subst born'
  exact tail

private def castTraceWithLower {N' : Set X} {old' born' : List (Set X)}
    (hN : N = N') (hOld : old = old') (hBorn : born = born')
    (tape : { R : RetainedPreparationTrace hn N old born phases T // usesLowerHistory P R }) :
    { R : RetainedPreparationTrace hn N' old' born' phases T // usesLowerHistory P R } := by
  subst N'
  subst old'
  subst born'
  exact tape

/-- The first event and its exact actual continuation. The comparison map
is a physical tower isomorphism over the identity of the current source. -/
inductive RetainedPreparationHead (hn : 0 < n) {X Y : CMfd.{u} n}
    (N : Set X) (old born : List (Set X)) (T : BlowupTower X Y) :
    List RetainedPreparationPhase → Type (u+1)
  | cons {phase : RetainedPreparationPhase} {later : List RetainedPreparationPhase}
      {A B : CMfd.{u} n} (Q : BlowupTower X A) (S : BlowupTower A B)
      (event : RetainedPreparationEvent hn N old born Q phase)
      (tail : RetainedPreparationTail hn (geoTransformAlong (geometricTemplate N born) Q).N
        (old.map (strictAlong Q)) (geoTransformAlong (geometricTemplate N born) Q).E later S)
      (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B)
      (iso : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T (Q.append S) e) :
      RetainedPreparationHead hn N old born T (phase :: later)

/-- The extracted first event and its literal continuation both preserve
the lower-history witnesses of the input tape. -/
def RetainedPreparationHead.usesLowerHistory (P : SharpHistoryPredicate.{u} n)
    (head : RetainedPreparationHead hn N old born T phases) : Prop :=
  match head with
  | .cons _ _ event tail _ _ => event.usesLowerHistory P ∧ tail.usesLowerHistory P

set_option maxHeartbeats 650000 in
private def RetainedPreparationHead.restrictOpenWithLower (head : RetainedPreparationHead hn N old born T phases)
    (actions : LowerHistoryActions P) (hUses : head.usesLowerHistory P)
    (g : NativeRetainedGeometry N old born) (O : Opens X) :
    let f := (Subtype.val : O → X)
    { H : RetainedPreparationHead hn (f ⁻¹' N) (old.map (f ⁻¹' ·)) (born.map (f ⁻¹' ·))
        (restrict O T) phases // H.usesLowerHistory P } := by
  intro f
  cases head with
  | @cons phase later A B Q S event tail e he =>
    let U := openPreimage Q O
    have hQ := event.tests
    have hCur := hQ.current_geometry (hn := hn) g
    obtain ⟨_,_,hN,hOld,hBorn⟩ := saturated_retained_restricted_head g Q hQ.carrier hQ.full O
    let event' := event.restrictOpenWithLower actions hUses.1 g O
    let tail' := RetainedPreparationTail.castWithLower hN.symm hOld.symm hBorn.symm
      (tail.restrictOpenWithLower hUses.2 hCur U)
    have hIso := (restrict_iso_same_source he O).trans (isTowerIso_restrict_append O Q S)
    have hBase : (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) O) ∞).trans
        (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) O) ∞) =
        Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) O) ∞ := Diffeomorph.ext fun _ => rfl
    rw [hBase] at hIso
    exact ⟨.cons (restrict O Q) (restrict U S) event'.val tail'.val _ hIso,event'.property,tail'.property⟩

set_option maxHeartbeats 650000 in
private def RetainedPreparationHead.rebaseWithLower (head : RetainedPreparationHead hn N old born T phases)
    (actions : LowerHistoryActions P) (hUses : head.usesLowerHistory P)
    (g : NativeRetainedGeometry N old born)
    (e : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X) :
    { H : RetainedPreparationHead hn (e ⁻¹' N) (old.map (e ⁻¹' ·)) (born.map (e ⁻¹' ·))
        (transport e T).tower phases // H.usesLowerHistory P } := by
  cases head with
  | cons Q S event tail η hη =>
    let Q' := transport e Q
    let S' := transport Q'.back S
    have hQ := event.tests
    have hCur := hQ.current_geometry (hn := hn) g
    have hIsoQ := transport_isTowerIso e Q
    obtain ⟨_,hN,hOld,hBorn⟩ := blockTests_of_actualIso g hIsoQ hQ
    let event' := event.rebaseWithLower actions hUses.1 g e
    let tail' := RetainedPreparationTail.castWithLower hN.symm hOld.symm hBorn.symm
      (tail.rebaseWithLower hUses.2 hCur Q'.back)
    have hIso := rebase_iso_same_source hη e (hIsoQ.append (transport_isTowerIso Q'.back S))
    exact ⟨.cons Q'.tower S'.tower event'.val tail'.val _ hIso,event'.property,tail'.property⟩

set_option maxHeartbeats 900000 in
private def RetainedPreparationHead.appendWithLower {later : List RetainedPreparationPhase}
    (head : RetainedPreparationHead hn N old born T phases) (hUses : head.usesLowerHistory P)
    (g : NativeRetainedGeometry N old born) (hT : BlockTests N old born T)
    (U : BlowupTower Y Z)
    (next : RetainedPreparationTrace hn (geoTransformAlong (geometricTemplate N born) T).N
      (old.map (strictAlong T)) (geoTransformAlong (geometricTemplate N born) T).E later U)
    (hNext : HironakaG4RetainedPreparationLowerHistory.usesLowerHistory P next) :
    { H : RetainedPreparationHead hn N old born (T.append U) (phases ++ later) // H.usesLowerHistory P } := by
  cases head with
  | @cons phase firstLater A B Q S event tail e he =>
    let U' := transport e.symm U
    have hCur := hT.current_geometry (hn := hn) g
    have hData := blockTests_of_actualIso g he.symm hT
    have hIdentity : ((Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞).symm : X → X) = id := rfl
    simp only [hIdentity,preimage_id,List.map_id'] at hData
    obtain ⟨hTS,hN,hOld,hBorn⟩ := hData
    let next' := castTraceWithLower hN.symm hOld.symm hBorn.symm ⟨next.rebase e.symm hCur,hNext⟩
    have hIso := he.append (transport_isTowerIso e.symm U).symm
    cases tail with
    | nil => exact ⟨.cons Q U'.tower event (.trace next'.val) _ hIso,hUses.1,next'.property⟩
    | trace tail =>
      obtain ⟨hQ,hS⟩ := (blockTests_append_iff Q S).mp hTS
      have hCurQ := hQ.current_geometry (hn := hn) g
      obtain ⟨hWhole,hList⟩ := current_retained_records_append N old born Q S
      let next'' := castTraceWithLower (congrArg MarkedIdeal.N hWhole) hList
        (congrArg MarkedIdeal.E hWhole) next'
      let tail' := RetainedPreparationTrace.append S U'.tower hCurQ hS.carrier hS.full tail next''.val
      rw [BlowupTower.append_assoc] at hIso
      exact ⟨.cons Q (S.append U'.tower) event (.trace tail') _ hIso,hUses.1,hUses.2,next''.property⟩

/-- Normalize the actual first phase, preserving any transport-stable
lower-history predicate through the split of the literal continuation. -/
def retainedPreparationHeadWithLower (actions : LowerHistoryActions P)
    (tape : RetainedPreparationTrace hn N old born phases T) (hUses : usesLowerHistory P tape) :
    { H : RetainedPreparationHead hn N old born T phases // H.usesLowerHistory P } := by
  induction tape with
  | @defect _ _ _ _ _ T trace =>
    exact ⟨.cons T .refl (.defect trace) .nil _ (IsTowerIso.refl_self T),trivial,trivial⟩
  | @lower _ _ _ _ _ T g hDef i terminal hEq =>
    exact ⟨.cons T .refl (.lower g hDef i terminal hEq) .nil _ (IsTowerIso.refl_self T),hUses,trivial⟩
  | append T S g hT hFull _ next ih _ =>
    let head := ih hUses.1
    exact head.val.appendWithLower head.property g ⟨hT,hFull⟩ S next hUses.2
  | restrictOpen O g _ ih =>
    let head := ih hUses
    exact head.val.restrictOpenWithLower actions head.property g O
  | rebase e g _ ih =>
    let head := ih hUses
    exact head.val.rebaseWithLower actions head.property g e

/-- Normalize the actual first phase of any proof-relevant native
preparation tape, without changing or reassociating chronological labels. -/
def retainedPreparationHead (tape : RetainedPreparationTrace hn N old born phases T) :
    RetainedPreparationHead hn N old born T phases :=
  (retainedPreparationHeadWithLower unrestrictedLowerHistoryActions tape (usesLowerHistory_unrestricted tape)).val

end
end Hironaka.HironakaG4RetainedPreparationHead
