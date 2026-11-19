import Hironaka.Resolution.HironakaG1OriginalGeneralCanonicalCuts
import Hironaka.Resolution.HironakaG1OriginalMaxOrderTwoPairCuts
import Hironaka.Resolution.HironakaG8LocalPower
import Hironaka.Resolution.HironakaG8GuardedCanonicality

/-! Complete unequal-native-mark canonicality for the LITERAL ORIGINAL engine.
Blueprint FIRST: hironaka-g1-original-unequal-mark-canonical.tex.
Actual whole boundaries and proper carriers remain literal. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1OriginalUnequalMarkCanonical
noncomputable section
open Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism ResolutionInvariantSpec
  HironakaG8LocalHistory HironakaG11InvBMClass HironakaG8LocalPower
  HironakaActualPowerBoundaryExponents HironakaG1OriginalTwoPairCanonicalCuts
  HironakaG1OriginalGeneralCanonicalCuts HironakaG1OriginalMaxOrderTwoPairCuts
  CanonicalCentres ResolutionDriver DivisorExponentAlong IdealWeightPowers

private theorem maxLocus_eq_of_pairCuts {n k : ℕ} {Λ : Type} [LinearOrder Λ]
    (I : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n k Λ) (hCuts : CanonicalTwoPairCuts k I.inv)
    {X Y : CMfd.{0} n} (P Q : MarkedIdeal n X) (hP : IsInvDomain k P) (hQ : IsInvDomain k Q)
    (hL : LocWPEquiv P Q) (hDim : SameCarrierDim P Q)
    (hInitial : ∀ H ∈ P.E, ∀ x ∈ P.cosupp, x ∈ H →
      Q.d * divExpAlong n P.N P.ideal H x = P.d * divExpAlong n Q.N Q.ideal H x)
    (T : BlowupTower X Y) (hcP : IsCanonical P (I.inv P) T) (hcQ : IsCanonical Q (I.inv Q) T) :
    maxLocus (I.inv P T) (geoTransformAlong P T).cosupp =
      maxLocus (I.inv Q T) (geoTransformAlong Q T).cosupp := by
  exact HironakaG8GuardedCanonicality.maxLocus_eq_of_guarded_pairCuts (fun {_} _ => True) I.inv hCuts
    P Q hP hQ trivial trivial hL hDim hInitial T (I.isInvValue.isGeoTestTower_of_isCanonical hP T hcP) hcP hcQ

private theorem isCanonical_iff_of_pairCuts {n k : ℕ} {Λ : Type} [LinearOrder Λ]
    (I : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n k Λ) (hCuts : CanonicalTwoPairCuts k I.inv)
    {X : CMfd.{0} n} (P Q : MarkedIdeal n X) (hP : IsInvDomain k P) (hQ : IsInvDomain k Q)
    (hL : LocWPEquiv P Q) (hDim : SameCarrierDim P Q)
    (hInitial : ∀ H ∈ P.E, ∀ x ∈ P.cosupp, x ∈ H →
      Q.d * divExpAlong n P.N P.ideal H x = P.d * divExpAlong n Q.N Q.ideal H x) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsCanonical P (I.inv P) T ↔ IsCanonical Q (I.inv Q) T
  := HironakaG8GuardedCanonicality.isCanonical_iff_of_guarded_pairCuts (fun {_} _ => True) I.inv hCuts
    P Q hP hQ trivial trivial hL hDim hInitial (fun T hcan => I.isInvValue.isGeoTestTower_of_isCanonical hP T hcan)

private theorem power_initial_native_exponents {n k : ℕ} {X : CMfd.{0} n}
    (P : MarkedIdeal n X) (hP : IsInvDomain k P) (e : ℕ) (he : 1 ≤ e) :
    ∀ H ∈ P.E, ∀ x ∈ P.cosupp, x ∈ H →
      (powerMarked P e).d * divExpAlong n P.N P.ideal H x =
        P.d * divExpAlong n (powerMarked P e).N (powerMarked P e).ideal H x := by
  intro H _hH x _hx _hxH
  change (P.d * e) * divExpAlong n P.N P.ideal H x = P.d * divExpAlong n P.N (idealPow P.ideal e) H x
  rw [divExpAlong_idealPow hP.isWellFormed.isClosedSubmanifold_N hP.isWellFormed.isCoherent he]
  exact Nat.mul_assoc _ _ _

/-- The FULL unequal-native-mark two-pair cut property for EVERY literal
original family member, with all lower cut IHs discharged internally. -/
theorem canonicalTwoPairCuts_invFamily {n : ℕ} (hn : 0 < n) (k : ℕ) :
    CanonicalTwoPairCuts k (invFamily.{0} hn k).inv := by
  induction k with
  | zero => exact canonicalTwoPairCuts_ofDimZero (0 : ℕ)
  | succ k ih =>
      exact canonicalTwoPairCuts_genInv
        (fun {X} J {Y} T y => Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J T y)
        (StepOneSeq.isMaxOrderValue_stepOneInvM (k := k+1) (invFamily hn k) hn) hn
        (canonicalMaxOrderTwoPairCuts_stepOneInvM (k := k+1) hn (invFamily hn k) ih)

/-- The literal ambient canonical invariant has full native unequal-mark
two-pair cuts, including ambient dimension zero. -/
theorem canonicalTwoPairCuts_canonicalInvariant (n : ℕ) :
    CanonicalTwoPairCuts n (canonicalInvariant.{0} n).inv := by
  cases n with
  | zero => exact canonicalTwoPairCuts_ofDimZero (0 : ℕ)
  | succ n => exact canonicalTwoPairCuts_invFamily (Nat.succ_pos n) (n+1)

/-- Actual original canonical histories agree at UNEQUAL native marks;
the second-side canonicality is a conclusion, not an input packet. -/
theorem invFamily_isCanonical_iff_of_local {n k : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (P Q : MarkedIdeal n X) (hP : IsInvDomain k P) (hQ : IsInvDomain k Q)
    (hL : LocWPEquiv P Q) (hDim : SameCarrierDim P Q)
    (hInitial : ∀ H ∈ P.E, ∀ x ∈ P.cosupp, x ∈ H →
      Q.d * divExpAlong n P.N P.ideal H x = P.d * divExpAlong n Q.N Q.ideal H x)
    (T : BlowupTower X Y) :
    IsCanonical P ((invFamily hn k).inv P) T ↔ IsCanonical Q ((invFamily hn k).inv Q) T :=
  isCanonical_iff_of_pairCuts (invFamily hn k) (canonicalTwoPairCuts_invFamily hn k)
    P Q hP hQ hL hDim hInitial T

/-- The actual ambient original invariant has the full unequal-mark
canonicality theorem on arbitrary proper equal-dimensional carriers. -/
theorem canonicalInvariant_isCanonical_iff_of_local {n : ℕ} {X Y : CMfd.{0} n}
    (P Q : MarkedIdeal n X) (hP : IsInvDomain n P) (hQ : IsInvDomain n Q)
    (hL : LocWPEquiv P Q) (hDim : SameCarrierDim P Q)
    (hInitial : ∀ H ∈ P.E, ∀ x ∈ P.cosupp, x ∈ H →
      Q.d * divExpAlong n P.N P.ideal H x = P.d * divExpAlong n Q.N Q.ideal H x)
    (T : BlowupTower X Y) :
    IsCanonical P ((canonicalInvariant n).inv P) T ↔ IsCanonical Q ((canonicalInvariant n).inv Q) T :=
  isCanonical_iff_of_pairCuts (canonicalInvariant n) (canonicalTwoPairCuts_canonicalInvariant n)
    P Q hP hQ hL hDim hInitial T

/-- Positive WHOLE-power recoding preserves all actual original family
canonical histories; its class and initial exponents are derived internally. -/
theorem invFamily_isCanonical_power_iff {n k : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (P : MarkedIdeal n X) (hP : IsInvDomain k P) (e : ℕ) (he : 1 ≤ e) (T : BlowupTower X Y) :
    IsCanonical P ((invFamily hn k).inv P) T ↔
      IsCanonical (powerMarked P e) ((invFamily hn k).inv (powerMarked P e)) T := by
  have hQ := powerMarked_isInvDomain P hP he
  have hL := locEquiv_powerMarked (κ := Kinds.wp) rfl P hP he
  exact invFamily_isCanonical_iff_of_local hn P (powerMarked P e) hP hQ hL
    (SameCarrierDim.of_N_eq rfl) (power_initial_native_exponents P hP e he) T

/-- The ambient ORIGINAL canonical invariant is invariant under positive
whole-power recoding at every ambient dimension, including zero. -/
theorem canonicalInvariant_isCanonical_power_iff {n : ℕ} {X Y : CMfd.{0} n}
    (P : MarkedIdeal n X) (hP : IsInvDomain n P) (e : ℕ) (he : 1 ≤ e) (T : BlowupTower X Y) :
    IsCanonical P ((canonicalInvariant n).inv P) T ↔
      IsCanonical (powerMarked P e) ((canonicalInvariant n).inv (powerMarked P e)) T := by
  have hQ := powerMarked_isInvDomain P hP he
  have hL := locEquiv_powerMarked (κ := Kinds.wp) rfl P hP he
  exact canonicalInvariant_isCanonical_iff_of_local P (powerMarked P e) hP hQ hL
    (SameCarrierDim.of_N_eq rfl) (power_initial_native_exponents P hP e he) T

/-- Full actual original maximum-centre equality under positive whole
powers, without any special-companion or maximum-stratum packet. -/
theorem canonicalInvariant_maxLocus_power {n : ℕ} {X Y : CMfd.{0} n}
    (P : MarkedIdeal n X) (hP : IsInvDomain n P) (e : ℕ) (he : 1 ≤ e)
    (T : BlowupTower X Y) (hcP : IsCanonical P ((canonicalInvariant n).inv P) T) :
    maxLocus ((canonicalInvariant n).inv P T) (geoTransformAlong P T).cosupp =
      maxLocus ((canonicalInvariant n).inv (powerMarked P e) T) (geoTransformAlong (powerMarked P e) T).cosupp := by
  have hQ := powerMarked_isInvDomain P hP he
  have hL := locEquiv_powerMarked (κ := Kinds.wp) rfl P hP he
  have hcQ := (canonicalInvariant_isCanonical_power_iff P hP e he T).mp hcP
  exact maxLocus_eq_of_pairCuts (canonicalInvariant n) (canonicalTwoPairCuts_canonicalInvariant n)
    P (powerMarked P e) hP hQ hL (SameCarrierDim.of_N_eq rfl) (power_initial_native_exponents P hP e he) T hcP hcQ

end
end Hironaka.HironakaG1OriginalUnequalMarkCanonical
