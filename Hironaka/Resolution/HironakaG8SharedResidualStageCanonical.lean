import Hironaka.Resolution.HironakaG8SharedResidualRetainedPhase
import Hironaka.Resolution.HironakaStageCenters

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG8SharedResidualStageCanonical
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal RelativePrincipalizationSpan
  ResolutionInvariantSpec ResolutionDriver CanonicalCentres NonmonomialOrderLocal
  HironakaStageCenters HironakaG8SharedResidualRetainedPhase

/-- At each occupied step, the high controlled ideal at the actual prefix
has a nonfactor witness at every point of each touching ordered boundary slot. -/
def HighBoundaryFreeAtOccupiedCentres {n : ℕ} {X Y : CMfd.{0} n}
    (Q : MarkedIdeal n X) (T : BlowupTower X Y) : Prop :=
  StageCentres (fun S C => C.Nonempty →
    let B := geoTransformAlong Q S
    ∀ z ∈ B.N, ∀ i : Fin B.E.length, z ∈ B.E.get i →
      ∃ g, B.ideal.mem z g ∧
        ¬ IsInSpanOnAt (n := n) B.N ((vanishingIdeal (n := n) (B.E.get i)).mem z) z g) T

set_option maxHeartbeats 1200000 in
/-- Within the retained epoch, every actual high canonical centre is also
an original low canonical centre. A nonempty centre supplies active high
cosupport at its own prefix, and the preceding low canonicality follows
from the induction on the same tower. -/
theorem shared_residual_phase_isCanonical
    {n : ℕ} {X Y : CMfd.{0} (n+1)}
    (P Q : MarkedIdeal (n+1) X) (hp : IsInvDomain (n+1) P) (hq : IsInvDomain (n+1) Q)
    (hPN : P.N = univ) (hQN : Q.N = univ) (hE : P.E = Q.E)
    (hI : P.ideal.Le Q.ideal) (hd : P.d ≤ Q.d) (hPart : nmPart P = nmPart Q)
    (hCap : ∀ x, nmOrd Q x ≤ Q.d)
    (T : BlowupTower X Y)
    (hqCan : IsCanonical Q ((canonicalInvariant (n+1)).inv Q) T)
    (hStages : HighBoundaryFreeAtOccupiedCentres Q T) :
    IsCanonical P ((canonicalInvariant (n+1)).inv P) T := by
  induction T with
  | refl => trivial
  | step S C π hπ ih =>
    have hpCan := ih hqCan.1 hStages.1
    refine ⟨hpCan, ?_⟩
    rcases hqCan.2 with hEmpty | hCentre
    · exact Or.inl hEmpty
    by_cases hOcc : C.Nonempty
    · obtain ⟨z, hz⟩ := hOcc
      have hzMax : z ∈ maxLocus ((canonicalInvariant (n+1)).inv Q S)
          (geoTransformAlong Q S).cosupp := hCentre ▸ hz
      have hMax := finite_shared_residual_maximum_eq P Q hp hq hPN hQN hE hI hd hPart hCap
        S hpCan hqCan.1 (hStages.2 ⟨z, hz⟩) ⟨z, hzMax.1⟩
      exact Or.inr (hCentre.trans hMax.symm)
    · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hOcc)

end
end Hironaka.HironakaG8SharedResidualStageCanonical
