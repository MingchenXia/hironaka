import Hironaka.Resolution.HironakaG8InitialFullWindowTies
import Hironaka.Resolution.HironakaG8NativePhaseCertificate

/-! Read original canonicality directly from the first retained native epoch. -/
set_option autoImplicit false
open Set TopologicalSpace

namespace Hironaka.HironakaG8NativeEpochUniformTopRead

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  ResolutionInvariantSpec CanonicalCentres HironakaStageCenters
  HironakaG8NativePhaseCertificate HironakaG8NativeRelativeClearing
  HironakaG8NativeSimultaneousCentre HironakaG8InitialFullWindowTies
  HironakaActualPowerBoundaryExponents HironakaSharpOriginalProductTraceOrder

private theorem stageCentres_prefix {n : ℕ} {X Y Z : CMfd.{0} n}
    (F : ∀ {A : CMfd.{0} n}, BlowupTower X A → Set A → Prop)
    (T : BlowupTower X Y) (S : BlowupTower Y Z) (h : StageCentres F (T.append S)) :
    StageCentres F T := by
  induction S with
  | refl => exact h
  | step S C π hπ ih => exact ih h.1

/-- The phase's own recorded windows cover the top ordinary order if that
whole stratum lies on the phase label, and the same witnesses supply the
first simultaneous maximum. A uniform comparison of their literal
powered records gives original mark-one canonicality of the first step. -/
theorem native_phase_first_canonical_of_uniform_top_records
    {n : ℕ} {X Y Z : CMfd.{0} (n+1)}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (hInt : interior W = ∅) (H : ℕ → ℕ)
    (q : ℕ) (hq : 1 ≤ q)
    (hUpper : ∀ x : X, ordinaryTraceOrder (X := X) univ (vanishingIdeal (n := n+1) W) x ≤ q)
    (hLevel : ∀ x : X, ordinaryTraceOrder (X := X) univ (vanishingIdeal (n := n+1) W) x = q →
      x ∈ phaseLevel W H)
    (e : ℕ) (he : 1 ≤ e) (D : Set X) (hD : D.Nonempty)
    (π : Y → X) (hπ : IsBlowupAlong (n+1) D π) (S : BlowupTower Y Z) :
    let T := (BlowupTower.step .refl D π hπ).append S
    let M : MarkedIdeal (n+1) X := ⟨univ, [], vanishingIdeal (n := n+1) W, 1⟩
    let Q : MarkedIdeal (n+1) X := ⟨univ, [], vanishingIdeal (n := n+1) W, q⟩
    ActualNativePhase W [] H T →
    (∀ (I : Type) (A : NativeWindows X I W [] H (phaseLevel W H)),
      (∀ i, IsCanonical (A.powered i) ((canonicalInvariant (n+1)).inv (A.powered i))
        (restrict (A.openSet i) T)) →
      ∀ i, A.powered i = MarkedIdeal.pullback (Subtype.val : A.openSet i → X) (powerMarked Q e)) →
    IsCanonical M ((canonicalInvariant (n+1)).inv M) (.step .refl D π hπ) := by
  intro T M Q hPhase hUniform
  obtain ⟨I,A,hEnds,hStages⟩ := hPhase.nativeStages
  have hFirst := stageCentres_prefix _ (.step .refl D π hπ) S (hStages trivial)
  obtain ⟨m,hm⟩ := hFirst.2.resolve_left hD.ne_empty
  have hp := hUniform I A (fun i => (hEnds i).1)
  have hm' : NativeSimultaneousCentre (canonicalInvariant (n+1)) A.openSet
      (fun i => MarkedIdeal.pullback (Subtype.val : A.openSet i → X) (powerMarked Q e))
      (.refl : BlowupTower X X) D m := by
    rw [← funext hp]
    exact hm
  exact initial_canonical_of_uniform_top_mark_cover W hW hInt q hq hUpper e he A.openSet
    (fun x hx => A.covers x (hLevel x hx)) D hD m π hπ hm'

end Hironaka.HironakaG8NativeEpochUniformTopRead
