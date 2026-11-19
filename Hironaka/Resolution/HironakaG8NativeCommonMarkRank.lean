import Hironaka.Resolution.HironakaG1OriginalUnequalMarkCanonical

/-! Uniform positive powering preserves all comparisons between local
native cuts having the same initial mark, across their actual ambients. -/

set_option autoImplicit false

open Set

namespace Hironaka.HironakaG8NativeCommonMarkRank

noncomputable section

open Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec CanonicalCentres
  HironakaG8LocalHistory HironakaG8LocalPower HironakaG11InvBMClass
  HironakaActualPowerBoundaryExponents HironakaG1OriginalUnequalMarkCanonical
  DivisorExponentAlong IdealWeightPowers

variable {n : ℕ}

private theorem recoded_boundary_exponents {X : CMfd.{0} n} (P : MarkedIdeal n X)
    (hP : IsInvDomain n P) (e : ℕ) (he : 1 ≤ e) :
    ∀ B ∈ P.E, ∀ x ∈ P.cosupp, x ∈ B →
      (powerMarked P e).d * divExpAlong n P.N P.ideal B x =
        P.d * divExpAlong n (powerMarked P e).N (powerMarked P e).ideal B x := by
  intro B _ x _ _
  change (P.d * e) * divExpAlong n P.N P.ideal B x =
    P.d * divExpAlong n P.N (idealPow P.ideal e) B x
  rw [divExpAlong_idealPow hP.isWellFormed.isClosedSubmanifold_N hP.isWellFormed.isCoherent he]
  exact Nat.mul_assoc _ _ _

/-- Uniform recoding of a common mark preserves actual cross-chart strict
order at every pair of active points, on independent canonical towers. -/
theorem canonical_common_mark_power_lt_iff
    {X₁ X₂ Y₁ Y₂ : CMfd.{0} n}
    (P : MarkedIdeal n X₁) (Q : MarkedIdeal n X₂)
    (hP : IsInvDomain n P) (hQ : IsInvDomain n Q) (hMark : P.d = Q.d)
    (e : ℕ) (he : 1 ≤ e) (T : BlowupTower X₁ Y₁) (S : BlowupTower X₂ Y₂)
    (hCanP : IsCanonical P ((canonicalInvariant n).inv P) T)
    (hCanQ : IsCanonical Q ((canonicalInvariant n).inv Q) S)
    {x : Y₁} (hx : x ∈ (geoTransformAlong P T).cosupp)
    {y : Y₂} (hy : y ∈ (geoTransformAlong Q S).cosupp) :
    ((canonicalInvariant n).inv P T x < (canonicalInvariant n).inv Q S y) ↔
      ((canonicalInvariant n).inv (powerMarked P e) T x <
        (canonicalInvariant n).inv (powerMarked Q e) S y) := by
  have hPowP := powerMarked_isInvDomain P hP he
  have hPowQ := powerMarked_isInvDomain Q hQ he
  have hMarkPow : (powerMarked P e).d = (powerMarked Q e).d := congrArg (· * e) hMark
  exact canonicalTwoPairCuts_canonicalInvariant n P (powerMarked P e) Q (powerMarked Q e)
    hP hPowP hQ hPowQ
    (locEquiv_powerMarked (κ := Kinds.wp) rfl P hP he) (SameCarrierDim.of_N_eq rfl)
    (recoded_boundary_exponents P hP e he)
    (locEquiv_powerMarked (κ := Kinds.wp) rfl Q hQ he) (SameCarrierDim.of_N_eq rfl)
    (recoded_boundary_exponents Q hQ e he)
    hMark hMarkPow trivial trivial trivial trivial T S
    hCanP ((canonicalInvariant_isCanonical_power_iff P hP e he T).mp hCanP)
    hCanQ ((canonicalInvariant_isCanonical_power_iff Q hQ e he S).mp hCanQ) x hx y hy

end
end Hironaka.HironakaG8NativeCommonMarkRank
