import Hironaka.Resolution.HironakaG8SharedResidualStageCanonical
import Hironaka.Resolution.HironakaG8PrincipalRetainedEpochFinite

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

namespace Hironaka.HironakaG8SharedResidualInitialFactorFree
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionDriver
  ResolutionInvariantSpec NonmonomialOrderLocal HomogenizedIdealAlong GermIdealOrder
  CanonicalCentres GeneralValue NonmonomialOrderCanonical
  HironakaG8SharedResidualStageCanonical HironakaG8PrincipalRetainedEpochFinite

variable {n : ℕ} {X Y : CMfd.{0} (n+1)}

private abbrev evaluator : ∀ {A : CMfd.{0} (n+1)}, MarkedIdeal (n+1) A →
    ∀ {B : CMfd.{0} (n+1)}, BlowupTower A B → B → ℕ ×ₗ WithTop (ValTy n) :=
  fun {_} M {_} S z => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) n) M S z

/-- At a factor-free canonical prefix, the initial global nonmonomial
order cap is also the current ordinary order cap. -/
theorem factor_free_canonical_prefix_cap
    (Q : MarkedIdeal (n+1) X) (hq : IsInvDomain (n+1) Q)
    (hCap : ∀ x, nmOrd Q x ≤ Q.d) (T : BlowupTower X Y)
    (hCan : IsCanonical Q ((canonicalInvariant (n+1)).inv Q) T)
    (hNo : HasNoBoundaryFactor (geoTransformAlong Q T)) :
    let B := geoTransformAlong Q T
    IsMaximalOrderAlong B.N B.ideal B.d := by
  intro B
  have hTest := (canonicalInvariant (n+1)).isInvValue.isGeoTestTower_of_isCanonical hq T hCan
  have hB := InvDomainTowerAlong.isInvDomain_geoTransformAlong hq T hTest
  have hMark : B.d = Q.d := d_geoTransformAlong Q T
  intro z hz
  have hzB : z ∈ B.cosupp := cosupport_anti (Nat.le_succ B.d) hz
  have hzG : z ∈ ordGe B (B.d+1) := by
    rw [ordGe_eq_cosupport_of_hasNoBoundaryFactor B hB.isWellFormed hNo]
    exact hz
  have hzOrd := (mem_ordGe_iff hB.isWellFormed hB.isNonzeroAlongAt (B.cosupp_subset_N hzB) _).mp hzG
  change IsCanonical Q (genInv evaluator Q) T at hCan
  have hMono := nmOrd_le_nmOrd_proj (Nat.succ_pos n) hq (ordMonotone_genInv evaluator Q) .refl T
  simp only [BlowupTower.refl_append, geoTransformAlong_refl] at hMono
  have hBound := (hMono hTest hCan z hzB).2.trans (hCap (T.proj z))
  exact Nat.not_succ_le_self B.d (hzOrd.trans (hMark ▸ hBound))

/-- Initial witnesses for all ordered slots, together with the global
order cap, persist through the original canonical tower. -/
theorem canonical_tower_hasNoBoundaryFactor
    (Q : MarkedIdeal (n+1) X) (hq : IsInvDomain (n+1) Q)
    (hNo : HasNoBoundaryFactor Q) (hCap : ∀ x, nmOrd Q x ≤ Q.d)
    (T : BlowupTower X Y) (hCan : IsCanonical Q ((canonicalInvariant (n+1)).inv Q) T) :
    HasNoBoundaryFactor (geoTransformAlong Q T) := by
  induction T with
  | refl => exact hNo
  | step S C π hπ ih =>
    have hTest := (canonicalInvariant (n+1)).isInvValue.isGeoTestTower_of_isCanonical hq _ hCan
    have hB := InvDomainTowerAlong.isInvDomain_geoTransformAlong hq S hTest.1
    have hPrev := ih hCan.1
    exact hasNoBoundaryFactor_step _ hB.isWellFormed hPrev hπ hTest.2
      (factor_free_canonical_prefix_cap Q hq hCap S hCan.1 hPrev)

/-- Initial factor-free high canonicality supplies every occupied
prefix witness needed for the low canonical history. -/
theorem shared_residual_phase_isCanonical_of_initial_factor_free
    (P Q : MarkedIdeal (n+1) X) (hp : IsInvDomain (n+1) P) (hq : IsInvDomain (n+1) Q)
    (hPN : P.N = univ) (hQN : Q.N = univ) (hE : P.E = Q.E)
    (hI : P.ideal.Le Q.ideal) (hd : P.d ≤ Q.d) (hPart : nmPart P = nmPart Q)
    (hNo : HasNoBoundaryFactor Q) (hCap : ∀ x, nmOrd Q x ≤ Q.d)
    (T : BlowupTower X Y) (hCan : IsCanonical Q ((canonicalInvariant (n+1)).inv Q) T) :
    IsCanonical P ((canonicalInvariant (n+1)).inv P) T := by
  apply shared_residual_phase_isCanonical P Q hp hq hPN hQN hE hI hd hPart hCap T hCan
  induction T with
  | refl => trivial
  | step S C π hπ ih =>
    exact ⟨ih hCan.1, fun _ => canonical_tower_hasNoBoundaryFactor Q hq hNo hCap S hCan.1⟩

end
end Hironaka.HironakaG8SharedResidualInitialFactorFree
