import Hironaka.Resolution.HironakaG8SharedResidualInitialFactorFree
import Hironaka.Resolution.HironakaG8NativePrefixOriginalCanonical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG8NativeSharedResidualCanonical
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionDriver ResolutionInvariantSpec NonmonomialOrderLocal CanonicalCentres
  HironakaG8NativeSimultaneousCentre HironakaG8NativePrefixOriginalCanonical
  HironakaG8SharedResidualInitialFactorFree HironakaG8PrincipalRetainedEpochFinite
  HironakaActualPowerBoundaryExponents HironakaSharpActualChronologicalResidualDictionary

/-- Simultaneous maxima for the actual powered native atlas supply original
canonicality for its unpowered high record on the literal window tower.
The retained comparison then gives original canonicality for the low record. -/
theorem native_simultaneous_shared_residual_canonical
    {n : ℕ} {X Y : CMfd.{0} (n+1)} {I : Type}
    (U : I → Opens X) (Q : ∀ i, MarkedIdeal (n+1) (CMfd.of (n := n+1) (U i)))
    (hq : ∀ i, IsInvDomain (n+1) (Q i)) (e : I → ℕ) (he : ∀ i, 1 ≤ e i)
    (T : BlowupTower X Y)
    (hSync : NativeSimultaneousStages (canonicalInvariant (n+1)) U (fun i => powerMarked (Q i) (e i)) T)
    (i : I) (P : MarkedIdeal (n+1) (CMfd.of (n := n+1) (U i))) (hp : IsInvDomain (n+1) P)
    (hPN : P.N = univ) (hQN : (Q i).N = univ) (hE : P.E = (Q i).E)
    (hI : P.ideal.Le (Q i).ideal) (hd : P.d ≤ (Q i).d) (hPart : nmPart P = nmPart (Q i))
    (hNo : HasNoBoundaryFactor (Q i)) (hCap : ∀ x, nmOrd (Q i) x ≤ (Q i).d) :
    IsCanonical P ((canonicalInvariant (n+1)).inv P) (restrict (U i) T) := by
  have hc := simultaneous_powered_prefix_raw_canonical (Nat.succ_pos n) U Q hq e he T hSync i
  have hqCan : IsCanonical (Q i) ((canonicalInvariant (n+1)).inv (Q i)) (restrict (U i) T) := by
    rwa [HironakaSmoothSubmersionOriginalAmbientCanonical.canonicalInvariant_eq_invFamily (Nat.succ_pos n)]
  exact shared_residual_phase_isCanonical_of_initial_factor_free P (Q i) hp (hq i)
    hPN hQN hE hI hd hPart hNo hCap (restrict (U i) T) hqCan

/-- If the starting raw native ideal is the actual normalized low residual,
both initial ideal containment and shared nonmonomial part follow. This
form uses the single geometric ideal identity on the adopted window. -/
theorem native_simultaneous_residual_record_canonical
    {n : ℕ} {X Y : CMfd.{0} (n+1)} {I : Type}
    (U : I → Opens X) (Q : ∀ i, MarkedIdeal (n+1) (CMfd.of (n := n+1) (U i)))
    (hq : ∀ i, IsInvDomain (n+1) (Q i)) (e : I → ℕ) (he : ∀ i, 1 ≤ e i)
    (T : BlowupTower X Y)
    (hSync : NativeSimultaneousStages (canonicalInvariant (n+1)) U (fun i => powerMarked (Q i) (e i)) T)
    (i : I) (P : MarkedIdeal (n+1) (CMfd.of (n := n+1) (U i))) (hp : IsInvDomain (n+1) P)
    (hPN : P.N = univ) (hQN : (Q i).N = univ) (hE : P.E = (Q i).E)
    (hResidual : nmPart P = (Q i).ideal) (hd : P.d ≤ (Q i).d)
    (hCap : ∀ x, nmOrd P x ≤ (Q i).d) :
    IsCanonical P ((canonicalInvariant (n+1)).inv P) (restrict (U i) T) := by
  have hNo : HasNoBoundaryFactor (Q i) := by
    have hWitness := (NonmonomialTransformAlong.parts_hypotheses (Nat.succ_pos n)
      P hp.isWellFormed hp.isNonzeroAlongAt).2.2.2.2.1
    change ∀ x ∈ P.N, ∀ j : Fin P.E.length, x ∈ P.E.get j →
      ∃ a, (nmPart P).mem x a ∧
        ¬ IsInSpanOnAt (n := n+1) P.N
          ((vanishingIdeal (n := n+1) (P.E.get j)).mem x) x a at hWitness
    rw [hPN.trans hQN.symm, hE, hResidual] at hWitness
    exact hWitness
  have hI : P.ideal.Le (Q i).ideal := by
    rw [← hResidual]
    exact NonmonomialTransformAlong.le_nonmonomialPartAlong_self hp.isWellFormed.isCoherent
  have hPart : nmPart P = nmPart (Q i) := by
    have hw := (hq i).isWellFormed
    have h := nonmonomialPartAlong_eq_restrictOn_of_no_member_factor
      hw.isClosedSubmanifold_N hw.isSNCDivisor hw.isTransverse hw.isCoherent hNo
    change nmPart (Q i) = RestrictedIdealExtension.restrictOn _ (Q i).N (Q i).ideal at h
    rw [hQN, BlowupTowerTransforms.restrictOn_univ hw.isCoherent] at h
    exact hResidual.trans h.symm
  have hCapQ (x : CMfd.of (n := n+1) (U i)) : nmOrd (Q i) x ≤ (Q i).d := by
    have hOrd : nmOrd (Q i) x = nmOrd P x := nmOrd_congr fun j => by
      change x ∈ GermIdealOrder.cosupport (n+1) (Q i).N (nmPart (Q i)) j ↔
        x ∈ GermIdealOrder.cosupport (n+1) P.N (nmPart P) j
      rw [hPN,hQN,hPart]
    rw [hOrd]
    exact hCap x
  exact native_simultaneous_shared_residual_canonical U Q hq e he T hSync i P hp
    hPN hQN hE hI hd hPart hNo hCapQ

end
end Hironaka.HironakaG8NativeSharedResidualCanonical
