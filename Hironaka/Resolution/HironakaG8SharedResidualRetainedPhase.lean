import Hironaka.Invariant.CanonicalCentres
import Hironaka.Resolution.HironakaSharpActualChronologicalResidualDictionary
import Hironaka.Resolution.HironakaSharpActualControlledAccumulatedResidual
import Hironaka.Resolution.HironakaSharpOriginalProductTraceOrder
import Hironaka.Resolution.HironakaG8CommonTowerNonmonomialOrders
import Hironaka.Invariant.StepOneEmptyPrefix

import Hironaka.Resolution.HironakaG8SharedResidualActiveOrder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8SharedResidualRetainedPhase
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerSplit BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  CanonicalCentres ResolutionDriver ResolutionInvariantSpec
  NonmonomialOrderLocal NonmonomialOrderTail NonmonomialOrderRegime NonmonomialOrderCanonical
  GeneralValue MarkedIdealRestrictOpen CompanionRebase CompanionReductionAlong StepOneRegime StepOneEmptyPrefix
  GermIdealOrder RelativePrincipalizationSpan RestrictedIdealExtension HomogenizedIdealAlong
  HironakaSharpActualChronologicalResidualDictionary HironakaSharpActualChronologicalNoOldFactor
  HironakaSharpActualControlledAccumulatedResidual
  BlowupStrictSubmanifold BlowupSNCTransform HironakaSharpOriginalProductTraceOrder

variable {n : ℕ} {X Y : CMfd.{0} (n+1)}

private abbrev evaluator : ∀ {A : CMfd.{0} (n+1)}, MarkedIdeal (n+1) A →
    ∀ {B : CMfd.{0} (n+1)}, BlowupTower A B → B → ℕ ×ₗ WithTop (ValTy n) :=
  fun {_} M {_} S z => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) n) M S z

private theorem order_bound_from_source
    (P : MarkedIdeal (n+1) X) (hP : IsInvDomain (n+1) P) (T : BlowupTower X Y)
    (hTest : IsGeoTestTower P T) (hCan : IsCanonical P (genInv evaluator P) T)
    (y : Y) (hy : y ∈ (geoTransformAlong P T).cosupp) :
    nmOrd (geoTransformAlong P T) y ≤ nmOrd P (T.proj y) := by
  have h := nmOrd_le_nmOrd_proj (Nat.succ_pos n) hP (ordMonotone_genInv evaluator P) .refl T
  simp only [BlowupTower.refl_append,geoTransformAlong_refl] at h
  exact (h hTest hCan y hy).2

/-- A surviving point at the initial order bound has kept that order on
the entire canonical tower. Its order run therefore has full length. -/
theorem regimeRun_eq_length_of_initial_order_bound
    (P : MarkedIdeal (n+1) X) (hP : IsInvDomain (n+1) P) (q : ℕ)
    (hCap : ∀ x : X, nmOrd P x ≤ q)
    (T : BlowupTower X Y) (hCan : IsCanonical P (genInv evaluator P) T)
    (hTest : IsGeoTestTower P T) (y : Y) (hy : y ∈ (geoTransformAlong P T).cosupp)
    (hOrder : nmOrd (geoTransformAlong P T) y = q) :
    regimeRun (OrdRegime P q) T y = T.length := by
  induction T with
  | refl => rfl
  | step T C π hπ ih =>
    have hPred := nmOrd_step_le_of_canonical (Nat.succ_pos n) hP (ordMonotone_genInv evaluator P)
      T C π hπ hTest hCan.2 hy
    have hOldBound := order_bound_from_source P hP T hTest.1 hCan.1 (π y) hPred.1
    have hOld : nmOrd (geoTransformAlong P T) (π y) = q :=
      le_antisymm (hOldBound.trans (hCap (T.proj (π y)))) (hOrder ▸ hPred.2)
    rw [regimeRun_step_of (OrdRegime P q) T C π hπ ⟨hPred.1,hOld⟩]
    rw [ih hCan.1 hTest.1 (π y) hPred.1 hOld]
    rfl

/-- Both whole records at their common positive attained bound read the
same literal initial companion along the entire shared tail. -/
theorem finite_retained_value_eq
    (P Q : MarkedIdeal (n+1) X) (hp : IsInvDomain (n+1) P) (hq : IsInvDomain (n+1) Q) {o : ℕ} (hd : P.d ≤ o) (he : Q.d ≤ o) (ho : o ≠ 0)
    (hN : P.N = Q.N) (hE : P.E = Q.E) (hPart : nmPart P = nmPart Q)
    (T : BlowupTower X Y) (y : Y)
    (hRunP : regimeRun (OrdRegime P o) T y = T.length)
    (hRunQ : regimeRun (OrdRegime Q o) T y = T.length)
    (hA : nmOrd (geoTransformAlong P T) y = o)
    (hB : nmOrd (geoTransformAlong Q T) y = o) :
    (canonicalInvariant (n+1)).inv P T y =
      (canonicalInvariant (n+1)).inv Q T y := by
  classical
  change genInv evaluator P T y = genInv evaluator Q T y
  rw [genInv_of_nmOrd_ne_zero evaluator P T hA ho,genInv_of_nmOrd_ne_zero evaluator Q T hB ho]
  rw [hRunP,hRunQ]
  let lower (M : MarkedIdeal (n+1) X) (s : Σ Z : CMfd.{0} (n+1), BlowupTower X Z × BlowupTower Z Y) :=
    genLowerValue evaluator M o s.2.1 s.2.2 y
  change toLex (o,toLex (Sum.inr (lower P (split T T.length)))) =
    toLex (o,toLex (Sum.inr (lower Q (split T T.length))))
  rw [split_of_length_le T T.length le_rfl]
  have hComp : companionOf (n+1) P o = companionOf (n+1) Q o := by
    change companionAlong _ _ _ _ o P.d = companionAlong _ _ _ _ o Q.d
    unfold companionAlong
    rw [if_neg (Nat.not_lt.mpr hd),if_neg (Nat.not_lt.mpr he)]
    change (⟨P.N, P.E, nmPart P, o⟩ : MarkedIdeal (n+1) X) = ⟨Q.N, Q.E, nmPart Q, o⟩
    rw [hN,hE,hPart]
  have hLower : lower P ⟨X,.refl,T⟩ = lower Q ⟨X,.refl,T⟩ := by
    change genLowerValue evaluator P o .refl T y = genLowerValue evaluator Q o .refl T y
    let read (W : Opens X) (J : MarkedIdeal (n+1) X) :=
      if h : T.proj y ∈ W then
        ((evaluator (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : W → X) J)
          (restrict W T) ⟨y,h⟩ : ℕ ×ₗ WithTop (ValTy n)) : WithTop (ℕ ×ₗ WithTop (ValTy n)))
      else ⊤
    have hMask : ordMask P o = ordMask Q o := by
      ext x
      change x ∈ (closure (ordGe P (o+1)))ᶜ ↔ x ∈ (closure (ordGe Q (o+1)))ᶜ
      have hGe : ordGe P (o+1) = ordGe Q (o+1) := by
        change cosupport (n+1) P.N (nmPart P) (o+1) = cosupport (n+1) Q.N (nmPart Q) (o+1)
        rw [hN,hPart]
      rw [hGe]
    unfold genLowerValue
    rw [GeneralCompare.compAt_eq_pullback (Nat.succ_pos n) o .refl hp,
      GeneralCompare.compAt_eq_pullback (Nat.succ_pos n) o .refl hq]
    change read (ordMask P o) (companionOf (n+1) P o) = read (ordMask Q o) (companionOf (n+1) Q o)
    rw [hMask,hComp]
  rw [hLower]

/-- Within a common active phase, initial residual equality and compatible
ordered boundary make the full original invariant agree at the high active
stratum. The canonical histories supply the two full order runs from their
common initial companion. -/
theorem finite_shared_residual_support_and_values
    (P Q : MarkedIdeal (n+1) X) (hp : IsInvDomain (n+1) P) (hq : IsInvDomain (n+1) Q)
    (hPN : P.N = univ) (hQN : Q.N = univ) (hE : P.E = Q.E)
    (hI : P.ideal.Le Q.ideal) (hd : P.d ≤ Q.d) (hPart : nmPart P = nmPart Q)
    (hCap : ∀ x, nmOrd Q x ≤ Q.d)
    (T : BlowupTower X Y)
    (hpCan : IsCanonical P ((canonicalInvariant (n+1)).inv P) T)
    (hqCan : IsCanonical Q ((canonicalInvariant (n+1)).inv Q) T)
    (hNo : let B := geoTransformAlong Q T
      ∀ z ∈ B.N, ∀ i : Fin B.E.length, z ∈ B.E.get i →
        ∃ g, B.ideal.mem z g ∧
          ¬ IsInSpanOnAt (n := n+1) B.N ((vanishingIdeal (n := n+1) (B.E.get i)).mem z) z g) :
    let A := geoTransformAlong P T
    let B := geoTransformAlong Q T
    (∀ y, y ∈ B.cosupp ↔ y ∈ A.cosupp ∧ nmOrd A y = Q.d) ∧
    (∀ y ∈ B.cosupp, (canonicalInvariant (n+1)).inv P T y =
      (canonicalInvariant (n+1)).inv Q T y) ∧
    (∀ y ∈ A.cosupp, nmOrd A y ≤ Q.d) := by
  intro A B
  let R := canonicalInvariant (n+1)
  have hpT := R.isInvValue.isGeoTestTower_of_isCanonical hp T hpCan
  have hqT := R.isInvValue.isGeoTestTower_of_isCanonical hq T hqCan
  change IsCanonical P (genInv evaluator P) T at hpCan
  change IsCanonical Q (genInv evaluator Q) T at hqCan
  have hN := hPN.trans hQN.symm
  have hNA : A.N = B.N := HironakaCoherentTransformExtension.geoTransformAlong_N_eq_of_N_eq hN T
  have hRes : nmPart A = nmPart B := HironakaG8CommonTowerNonmonomialOrders.common_test_tower_nonmonomial_part (Nat.succ_pos n)
    P Q hp.isWellFormed hq.isWellFormed hp.isNonzeroAlongAt hq.isNonzeroAlongAt hN hE hPart T hpT hqT
  have hIncl : B.cosupp ⊆ A.cosupp :=
    (HironakaG8SharedResidualActiveOrder.controlled_ideal_le_of_initial_le
      P Q hPN hQN hp.isWellFormed.isCoherent hq.isWellFormed.isCoherent hI hd T hpT hqT).2
  have hAD := InvDomainTowerAlong.isInvDomain_geoTransformAlong hp T hpT
  have hBD := InvDomainTowerAlong.isInvDomain_geoTransformAlong hq T hqT
  have hGe : ordGe A Q.d = ordGe B Q.d := by
    change cosupport (n+1) A.N (nmPart A) Q.d = cosupport (n+1) B.N (nmPart B) Q.d
    rw [hNA,hRes]
  have hB : nmPart B = B.ideal := by
    have he : nmPart B = restrictOn (n+1) B.N B.ideal :=
      nonmonomialPartAlong_eq_restrictOn_of_no_member_factor hBD.isWellFormed.isClosedSubmanifold_N
        hBD.isWellFormed.isSNCDivisor hBD.isWellFormed.isTransverse hBD.isWellFormed.isCoherent hNo
    have hBN : B.N = univ := (pullback_eq_mul_geoTransformAlong (𝔪 := Q) hQN hq.isWellFormed.isCoherent T hqT).1
    rw [he,hBN,BlowupTowerTransforms.restrictOn_univ hBD.isWellFormed.isCoherent]
  have hGeB : ordGe B Q.d = B.cosupp := by
    change cosupport (n+1) B.N (nmPart B) Q.d = cosupport (n+1) B.N B.ideal B.d
    rw [hB,show B.d = Q.d from d_geoTransformAlong Q T]
  have hCapP (x : X) : nmOrd P x ≤ Q.d := by
    have he : nmOrd P x = nmOrd Q x := nmOrd_congr fun j => by
      change x ∈ cosupport (n+1) P.N (nmPart P) j ↔ x ∈ cosupport (n+1) Q.N (nmPart Q) j
      rw [hN,hPart]
    rw [he]
    exact hCap x
  have hBound (y : Y) (hy : y ∈ A.cosupp) : nmOrd A y ≤ Q.d :=
    (order_bound_from_source P hp T hpT hpCan y hy).trans (hCapP (T.proj y))
  have hLevel (y : Y) : y ∈ B.cosupp ↔ y ∈ A.cosupp ∧ nmOrd A y = Q.d := by
    rw [← hGeB,← hGe]
    constructor
    · intro hy
      have hyA := hIncl (by rwa [← hGeB,← hGe])
      exact ⟨hyA,le_antisymm (hBound y hyA)
        ((mem_ordGe_iff hAD.isWellFormed hAD.isNonzeroAlongAt (A.cosupp_subset_N hyA) Q.d).mp hy)⟩
    · rintro ⟨hyA,hyq⟩
      exact (mem_ordGe_iff hAD.isWellFormed hAD.isNonzeroAlongAt (A.cosupp_subset_N hyA) Q.d).mpr
        (le_of_eq hyq.symm)
  refine ⟨hLevel,fun y hy => ?_,hBound⟩
  obtain ⟨hyA,hyq⟩ := (hLevel y).mp hy
  have he : nmOrd A y = nmOrd B y := nmOrd_congr fun j => by
    change y ∈ cosupport (n+1) A.N (nmPart A) j ↔ y ∈ cosupport (n+1) B.N (nmPart B) j
    rw [hNA,hRes]
  have hyQ := he.symm.trans hyq
  exact finite_retained_value_eq P Q hp hq hd le_rfl (by have := hq.one_le_d; omega) hN hE hPart T y
    (regimeRun_eq_length_of_initial_order_bound P hp Q.d hCapP T hpCan hpT y hyA hyq)
    (regimeRun_eq_length_of_initial_order_bound Q hq Q.d hCap T hqCan hqT y hy hyQ) hyq hyQ

/-- At a surviving retained active phase, the original maximum loci of both
records are literally equal on their common endpoint chart. -/
theorem finite_shared_residual_maximum_eq
    (P Q : MarkedIdeal (n+1) X) (hp : IsInvDomain (n+1) P) (hq : IsInvDomain (n+1) Q)
    (hPN : P.N = univ) (hQN : Q.N = univ) (hE : P.E = Q.E)
    (hI : P.ideal.Le Q.ideal) (hd : P.d ≤ Q.d) (hPart : nmPart P = nmPart Q)
    (hCap : ∀ x, nmOrd Q x ≤ Q.d)
    (T : BlowupTower X Y)
    (hpCan : IsCanonical P ((canonicalInvariant (n+1)).inv P) T)
    (hqCan : IsCanonical Q ((canonicalInvariant (n+1)).inv Q) T)
    (hNo : let B := geoTransformAlong Q T
      ∀ z ∈ B.N, ∀ i : Fin B.E.length, z ∈ B.E.get i →
        ∃ g, B.ideal.mem z g ∧
          ¬ IsInSpanOnAt (n := n+1) B.N ((vanishingIdeal (n := n+1) (B.E.get i)).mem z) z g)
    (hSurvive : (geoTransformAlong Q T).cosupp.Nonempty) :
    let R := canonicalInvariant (n+1)
    maxLocus (R.inv P T) (geoTransformAlong P T).cosupp =
      maxLocus (R.inv Q T) (geoTransformAlong Q T).cosupp := by
  let R := canonicalInvariant (n+1)
  let A := geoTransformAlong P T
  let B := geoTransformAlong Q T
  have hReads := finite_shared_residual_support_and_values P Q hp hq hPN hQN hE hI hd hPart hCap T hpCan hqCan hNo
  dsimp only at hReads
  obtain ⟨hLevel,hValue,hBound⟩ := hReads
  have hIncl : B.cosupp ⊆ A.cosupp := fun {_} hy => ((hLevel _).mp hy).1
  have hLt {z y : Y} (h : nmOrd A z < nmOrd A y) : R.inv P T z < R.inv P T y :=
    genInv_lt_of_nmOrd_lt evaluator P h
  obtain ⟨a,ha⟩ := hSurvive
  obtain ⟨haA,haq⟩ := (hLevel a).mp ha
  change maxLocus (R.inv P T) A.cosupp = maxLocus (R.inv Q T) B.cosupp
  ext y
  constructor
  · intro hy
    have hyq : nmOrd A y = Q.d := le_antisymm (hBound y hy.1) (by
      by_contra hn
      exact (not_lt_of_ge (hy.2 a haA)) (hLt (by rw [haq]; exact Nat.lt_of_not_ge hn)))
    have hyB := (hLevel y).mpr ⟨hy.1,hyq⟩
    refine ⟨hyB,fun z hz => ?_⟩
    rw [← hValue z hz,← hValue y hyB]
    exact hy.2 z (hIncl hz)
  · intro hy
    obtain ⟨hyA,hyq⟩ := (hLevel y).mp hy.1
    refine ⟨hyA,fun z hz => ?_⟩
    by_cases hzB : z ∈ B.cosupp
    · rw [hValue z hzB,hValue y hy.1]
      exact hy.2 z hzB
    · have hzq : nmOrd A z ≠ Q.d := fun h => hzB ((hLevel z).mpr ⟨hz,h⟩)
      exact le_of_lt (hLt (by rw [hyq]; exact lt_of_le_of_ne (hBound z hz) hzq))


end
end Hironaka.HironakaG8SharedResidualRetainedPhase
