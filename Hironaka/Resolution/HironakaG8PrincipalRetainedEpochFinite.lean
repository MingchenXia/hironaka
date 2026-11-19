import Hironaka.Invariant.CanonicalCentres
import Hironaka.Resolution.HironakaSharpActualChronologicalResidualDictionary
import Hironaka.Resolution.HironakaSharpActualControlledAccumulatedResidual
import Hironaka.Resolution.HironakaSharpOriginalProductTraceOrder
import Hironaka.Resolution.HironakaG8CommonTowerNonmonomialOrders
import Hironaka.Resolution.HironakaG8LabelledOriginalCanonicalPrefixes
import Hironaka.Invariant.StepOneEmptyPrefix

/-! Compare native and whole mark-one histories during the initial active
maximal-order epoch on a shared boundary-free ideal. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8PrincipalRetainedEpochFinite
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerSplit BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  CanonicalCentres ResolutionDriver ResolutionInvariantSpec
  NonmonomialOrderLocal NonmonomialOrderTail NonmonomialOrderRegime NonmonomialOrderCanonical
  GeneralValue CompanionRebase CompanionReductionAlong StepOneRegime StepOneEmptyPrefix
  GermIdealOrder RelativePrincipalizationSpan RestrictedIdealExtension HomogenizedIdealAlong
  HironakaSharpActualChronologicalResidualDictionary HironakaSharpActualChronologicalNoOldFactor
  HironakaSharpActualControlledAccumulatedResidual
  BlowupStrictSubmanifold BlowupSNCTransform HironakaSharpOriginalProductTraceOrder

variable {n : ℕ} {X Y : CMfd.{0} (n+1)}

private abbrev record (I : GermIdeal (n+1) X) (d : ℕ) : MarkedIdeal (n+1) X := ⟨univ,[],I,d⟩
private abbrev evaluator : ∀ {A : CMfd.{0} (n+1)}, MarkedIdeal (n+1) A →
    ∀ {B : CMfd.{0} (n+1)}, BlowupTower A B → B → ℕ ×ₗ WithTop (ValTy n) :=
  fun {_} M {_} S z => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) n) M S z

/-- Actual germs witnessing that no ordered boundary member is a factor
of the entire current controlled ideal. -/
def HasNoBoundaryFactor {A : CMfd.{0} (n+1)} (P : MarkedIdeal (n+1) A) : Prop :=
  ∀ x ∈ P.N, ∀ i : Fin P.E.length, x ∈ P.E.get i →
    ∃ g, P.ideal.mem x g ∧
      ¬ IsInSpanOnAt (n := n+1) P.N ((vanishingIdeal (n := n+1) (P.E.get i)).mem x) x g

theorem ordGe_eq_cosupport_of_hasNoBoundaryFactor
    {A : CMfd.{0} (n+1)} (P : MarkedIdeal (n+1) A) (hP : P.IsWellFormed)
    (h : HasNoBoundaryFactor P) (j : ℕ) :
    ordGe P j = cosupport (n+1) P.N P.ideal j := by
  have he := nonmonomialPartAlong_eq_restrictOn_of_no_member_factor
    hP.isClosedSubmanifold_N hP.isSNCDivisor hP.isTransverse hP.isCoherent h
  change cosupport (n+1) P.N (nmPart P) j = _
  change nmPart P = restrictOn (n+1) P.N P.ideal at he
  rw [he]
  exact Subset.antisymm
    (MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe (restrictLe_self_restrictOn hP.isCoherent) j)
    (MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe restrictLe_restrictOn j)

/-- Old nonfactor witnesses persist and exact order prevents the new
exceptional member from factoring the high controlled transform. -/
theorem hasNoBoundaryFactor_step
    (P : MarkedIdeal (n+1) X) (hP : P.IsWellFormed) (hOld : HasNoBoundaryFactor P)
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong (n+1) C π)
    (hC : P.IsAdmissibleCentre C) (hCap : IsMaximalOrderAlong P.N P.ideal P.d) :
    HasNoBoundaryFactor (P.geoTransform C π) := by
  intro y hy i hi
  let E := P.E
  have hiType : i.val < (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).length := i.isLt
  have hget := get_map_append_singleton E (geoStrictTransform π C) (π ⁻¹' C) ⟨i.val,hiType⟩
  change (P.geoTransform C π).E.get i =
    (if h : i.val < E.length then geoStrictTransform π C (E.get ⟨i.val,h⟩) else π ⁻¹' C) at hget
  by_cases hiOld : i.val < E.length
  · rw [dif_pos hiOld] at hget
    rw [hget] at hi ⊢
    obtain ⟨g,hg,hnot⟩ := nextTotal_old_strict_member_not_factor hP.isClosedSubmanifold_N
      hP.isSNCDivisor hP.isTransverse hP.isCoherent hπ hC.subset_N hC.2.2 hOld hy
      ⟨i.val,hiOld⟩ hi
    exact ⟨g,actual_total_le_controlled P hπ y g hg,hnot⟩
  · rw [dif_neg hiOld] at hget
    rw [hget] at hi ⊢
    obtain ⟨g,hg,hnot⟩ := ExceptionalPushforwardAlong.exists_not_isInSpanOnAt_exceptionalDivisor
      hπ hP.isClosedSubmanifold_N hP.isCoherent hC.2.1 hi hy (hCap (π y))
    refine ⟨g,hg,?_⟩
    rintro ⟨k,s,a,hs,ha,he⟩
    apply hnot
    exact ⟨k,s,a,fun j => NonmonomialTransformTower.exceptionalDivisor_mem_of_vanishingIdeal_mem
      hπ hP.isSNCDivisor hC.2.2 hi (hs j),ha,he⟩

private theorem original_order_cap (I : GermIdeal (n+1) X) (q : ℕ)
    (hQ : IsInvDomain (n+1) (record I q))
    (hCap : IsMaximalOrderAlong (record I q).N I q) (x : X) : nmOrd (record I q) x ≤ q := by
  apply nmOrd_le_of_notMem
  have hEq := ordGe_ordinaryTraceMarked_eq_cosupport (univ : Set X) I hQ.isWellFormed.isCoherent (q+1)
  change ordGe (record I q) (q+1) = cosupport (n+1) univ I (q+1) at hEq
  rw [hEq]
  exact hCap x

private theorem order_bound_from_source
    (P : MarkedIdeal (n+1) X) (hP : IsInvDomain (n+1) P) (T : BlowupTower X Y)
    (hTest : IsGeoTestTower P T) (hCan : IsCanonical P (genInv evaluator P) T)
    (y : Y) (hy : y ∈ (geoTransformAlong P T).cosupp) :
    nmOrd (geoTransformAlong P T) y ≤ nmOrd P (T.proj y) := by
  have h := nmOrd_le_nmOrd_proj (Nat.succ_pos n) hP (ordMonotone_genInv evaluator P) .refl T
  simp only [BlowupTower.refl_append,geoTransformAlong_refl] at h
  exact (h hTest hCan y hy).2

private theorem native_prefix_cap
    (I : GermIdeal (n+1) X) (q : ℕ) (hQ : IsInvDomain (n+1) (record I q))
    (hCap : IsMaximalOrderAlong (record I q).N I q)
    (T : BlowupTower X Y)
    (hCan : IsCanonical (record I q) (genInv evaluator (record I q)) T)
    (hTest : IsGeoTestTower (record I q) T)
    (hNo : HasNoBoundaryFactor (geoTransformAlong (record I q) T)) :
    let B := geoTransformAlong (record I q) T
    IsMaximalOrderAlong B.N B.ideal B.d := by
  let Q := record I q
  let B := geoTransformAlong Q T
  have hBD : IsInvDomain (n+1) B := InvDomainTowerAlong.isInvDomain_geoTransformAlong hQ T hTest
  have hMark : B.d = q := d_geoTransformAlong Q T
  change IsMaximalOrderAlong B.N B.ideal B.d
  intro z hz
  have hz' : z ∈ cosupport (n+1) B.N B.ideal (q+1) := by rwa [hMark] at hz
  have hLeMark : B.d ≤ q+1 := by rw [hMark]; omega
  have hzB : z ∈ B.cosupp := cosupport_anti hLeMark hz'
  have hzG : z ∈ ordGe B (q+1) := by
    rw [ordGe_eq_cosupport_of_hasNoBoundaryFactor B hBD.isWellFormed hNo]
    exact hz'
  have hzOrd := (mem_ordGe_iff hBD.isWellFormed hBD.isNonzeroAlongAt (B.cosupp_subset_N hzB) _).mp hzG
  have hLe : nmOrd B z ≤ nmOrd Q (T.proj z) :=
    order_bound_from_source Q hQ T hTest hCan z hzB
  exact (Nat.not_succ_le_self q) (hzOrd.trans (hLe.trans (original_order_cap I q hQ hCap _)))

/-- The entire native top-mark history preserves absence of boundary
factors, including every inherited slot and stages with empty centres. -/
theorem native_tower_hasNoBoundaryFactor
    (I : GermIdeal (n+1) X) (q : ℕ)
    (hQ : IsInvDomain (n+1) (record I q))
    (hCap : IsMaximalOrderAlong (record I q).N I q)
    (T : BlowupTower X Y)
    (hCan : IsCanonical (record I q) ((canonicalInvariant (n+1)).inv (record I q)) T) :
    HasNoBoundaryFactor (geoTransformAlong (record I q) T) := by
  let Q := record I q
  let R := canonicalInvariant (n+1)
  have hTest := R.isInvValue.isGeoTestTower_of_isCanonical hQ T hCan
  change IsCanonical Q (genInv evaluator Q) T at hCan
  induction T with
  | refl => exact fun _ _ i => Fin.elim0 i
  | step T C π hπ ih =>
    let B := geoTransformAlong Q T
    have hNo : HasNoBoundaryFactor B := ih hTest.1 hCan.1
    have hB := InvDomainTowerAlong.isInvDomain_geoTransformAlong hQ T hTest.1
    have hCentre : B.IsAdmissibleCentre C := ⟨hTest.2.1,hTest.2.2.1,hTest.2.2.2⟩
    exact hasNoBoundaryFactor_step B hB.isWellFormed hNo hπ hCentre
      (native_prefix_cap I q hQ hCap T hCan.1 hTest.1 hNo)

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
    (I : GermIdeal (n+1) X) {d e o : ℕ} (hd : d ≤ o) (he : e ≤ o) (ho : o ≠ 0)
    (T : BlowupTower X Y) (y : Y)
    (hRunP : regimeRun (OrdRegime (record I d) o) T y = T.length)
    (hRunQ : regimeRun (OrdRegime (record I e) o) T y = T.length)
    (hA : nmOrd (geoTransformAlong (record I d) T) y = o)
    (hB : nmOrd (geoTransformAlong (record I e) T) y = o) :
    (canonicalInvariant (n+1)).inv (record I d) T y =
      (canonicalInvariant (n+1)).inv (record I e) T y := by
  let P := record I d
  let Q := record I e
  change genInv evaluator P T y = genInv evaluator Q T y
  rw [genInv_of_nmOrd_ne_zero evaluator P T hA ho,genInv_of_nmOrd_ne_zero evaluator Q T hB ho]
  rw [hRunP,hRunQ]
  let lower (M : MarkedIdeal (n+1) X) (s : Σ Z : CMfd.{0} (n+1), BlowupTower X Z × BlowupTower Z Y) :=
    genLowerValue evaluator M o s.2.1 s.2.2 y
  change toLex (o,toLex (Sum.inr (lower P (split T T.length)))) =
    toLex (o,toLex (Sum.inr (lower Q (split T T.length))))
  rw [split_of_length_le T T.length le_rfl]
  have hComp : compAt P o .refl = compAt Q o .refl := by
    change companionAlong _ _ _ _ o d = companionAlong _ _ _ _ o e
    unfold companionAlong
    rw [if_neg (Nat.not_lt.mpr hd),if_neg (Nat.not_lt.mpr he)]
    rfl
  have hLower : lower P ⟨X,.refl,T⟩ = lower Q ⟨X,.refl,T⟩ := by
    change genLowerValue evaluator P o .refl T y = genLowerValue evaluator Q o .refl T y
    unfold genLowerValue
    rw [hComp]
    rfl
  rw [hLower]

/-- The native cosupport is the exact top-order stratum of the whole
mark-one record. Their full original values agree there along the same
literal prefix. -/
theorem finite_retained_support_and_values
    (I : GermIdeal (n+1) X) (q : ℕ)
    (hQ : IsInvDomain (n+1) (record I q))
    (hCap : IsMaximalOrderAlong (record I q).N I q)
    (T : BlowupTower X Y)
    (hCanP : IsCanonical (record I 1) ((canonicalInvariant (n+1)).inv (record I 1)) T)
    (hCanQ : IsCanonical (record I q) ((canonicalInvariant (n+1)).inv (record I q)) T) :
    let P := record I 1
    let Q := record I q
    let R := canonicalInvariant (n+1)
    let A := geoTransformAlong P T
    let B := geoTransformAlong Q T
    (∀ y : Y, y ∈ B.cosupp ↔ y ∈ A.cosupp ∧ nmOrd A y = q) ∧
    (∀ y ∈ B.cosupp, R.inv P T y = R.inv Q T y) ∧
    (∀ y ∈ A.cosupp, nmOrd A y ≤ q) := by
  let P := record I 1
  let Q := record I q
  let R := canonicalInvariant (n+1)
  let A := geoTransformAlong P T
  let B := geoTransformAlong Q T
  have hP : IsInvDomain (n+1) P :=
    ⟨⟨hQ.isWellFormed.1,hQ.isWellFormed.2,hQ.isWellFormed.3,hQ.isWellFormed.4⟩,
      hQ.dimLE,le_rfl,hQ.isNonzeroAlongAt⟩
  have hq : 1 ≤ q := hQ.one_le_d
  have hTP := R.isInvValue.isGeoTestTower_of_isCanonical hP T hCanP
  have hTQ := R.isInvValue.isGeoTestTower_of_isCanonical hQ T hCanQ
  have hAD : IsInvDomain (n+1) A := InvDomainTowerAlong.isInvDomain_geoTransformAlong hP T hTP
  have hBD : IsInvDomain (n+1) B := InvDomainTowerAlong.isInvDomain_geoTransformAlong hQ T hTQ
  have hMarkA : A.d = 1 := d_geoTransformAlong P T
  have hMarkB : B.d = q := d_geoTransformAlong Q T
  have hCapQ : ∀ x : X, nmOrd Q x ≤ q := original_order_cap I q hQ hCap
  have hCapP : ∀ x : X, nmOrd P x ≤ q := hCapQ
  change IsCanonical P (genInv evaluator P) T at hCanP
  change IsCanonical Q (genInv evaluator Q) T at hCanQ
  obtain ⟨hN,_hE,hParts,hOrder⟩ :=
    HironakaG8CommonTowerNonmonomialOrders.common_mark_tower_orders
      (Nat.succ_pos n) P hP.isWellFormed hP.isNonzeroAlongAt q T hTP hTQ
  change A.N = B.N at hN
  change nmPart A = nmPart B at hParts
  change ∀ y : Y, nmOrd A y = nmOrd B y at hOrder
  have hGe : ordGe A q = ordGe B q := by
    change cosupport (n+1) A.N (nmPart A) q = cosupport (n+1) B.N (nmPart B) q
    rw [hN,hParts]
  have hNo : HasNoBoundaryFactor B := native_tower_hasNoBoundaryFactor I q hQ hCap T hCanQ
  have hGeB : ordGe B q = B.cosupp := by
    rw [ordGe_eq_cosupport_of_hasNoBoundaryFactor B hBD.isWellFormed hNo]
    unfold MarkedIdeal.cosupp
    rw [hMarkB]
  have hIncl : B.cosupp ⊆ A.cosupp := by
    rw [← hGeB,← hGe]
    have hmark : A.d ≤ q := by rw [hMarkA]; exact hq
    exact (cosupport_anti hmark).trans (DerivativeIdealTower.cosupport_subset_of_le
      (NonmonomialTransformAlong.le_nonmonomialPartAlong_self hAD.isWellFormed.isCoherent) A.d)
  have hBound (y : Y) (hy : y ∈ A.cosupp) : nmOrd A y ≤ q :=
    (order_bound_from_source P hP T hTP hCanP y hy).trans (hCapP (T.proj y))
  have hLevel (y : Y) : y ∈ B.cosupp ↔ y ∈ A.cosupp ∧ nmOrd A y = q := by
    rw [← hGeB,← hGe]
    constructor
    · intro hy
      have hyA := hIncl (by rwa [← hGeB,← hGe])
      exact ⟨hyA,le_antisymm (hBound y hyA)
        ((mem_ordGe_iff hAD.isWellFormed hAD.isNonzeroAlongAt (A.cosupp_subset_N hyA) q).mp hy)⟩
    · rintro ⟨hyA,hyq⟩
      exact (mem_ordGe_iff hAD.isWellFormed hAD.isNonzeroAlongAt (A.cosupp_subset_N hyA) q).mpr
        (le_of_eq hyq.symm)
  have hValue (y : Y) (hy : y ∈ B.cosupp) : R.inv P T y = R.inv Q T y := by
    obtain ⟨hyA,hyq⟩ := (hLevel y).mp hy
    have hyQ : nmOrd B y = q := (hOrder y).symm.trans hyq
    exact finite_retained_value_eq I hq le_rfl (by omega) T y
      (regimeRun_eq_length_of_initial_order_bound P hP q hCapP T hCanP hTP y hyA hyq)
      (regimeRun_eq_length_of_initial_order_bound Q hQ q hCapQ T hCanQ hTQ y hy hyQ) hyq hyQ
  exact ⟨hLevel,hValue,hBound⟩

/-- At every actual common canonical prefix in the retained epoch, the
whole mark-one maximum and native maximum coincide while the native
cosupport survives. -/
theorem finite_retained_maximum_eq
    (I : GermIdeal (n+1) X) (q : ℕ)
    (hQ : IsInvDomain (n+1) (record I q))
    (hCap : IsMaximalOrderAlong (record I q).N I q)
    (T : BlowupTower X Y)
    (hCanP : IsCanonical (record I 1) ((canonicalInvariant (n+1)).inv (record I 1)) T)
    (hCanQ : IsCanonical (record I q) ((canonicalInvariant (n+1)).inv (record I q)) T)
    (hSurvive : (geoTransformAlong (record I q) T).cosupp.Nonempty) :
    let P := record I 1
    let Q := record I q
    let R := canonicalInvariant (n+1)
    maxLocus (R.inv P T) (geoTransformAlong P T).cosupp =
      maxLocus (R.inv Q T) (geoTransformAlong Q T).cosupp := by
  let P := record I 1
  let Q := record I q
  let R := canonicalInvariant (n+1)
  let A := geoTransformAlong P T
  let B := geoTransformAlong Q T
  have hReads := finite_retained_support_and_values I q hQ hCap T hCanP hCanQ
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
    have hyq : nmOrd A y = q := le_antisymm (hBound y hy.1) (by
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
    · have hzq : nmOrd A z ≠ q := fun h => hzB ((hLevel z).mpr ⟨hz,h⟩)
      exact le_of_lt (hLt (by rw [hyq]; exact lt_of_le_of_ne (hBound z hz) hzq))

/-- Every literal native canonical tower in the initial whole-ideal
top-mark epoch is canonical for the original mark-one record. A nonempty
next native centre witnesses survival of its own epoch. -/
theorem finite_native_retained_epoch_whole_markOne_canonical
    (I : GermIdeal (n+1) X) (q : ℕ)
    (hQ : IsInvDomain (n+1) (record I q))
    (hCap : IsMaximalOrderAlong (record I q).N I q)
    (T : BlowupTower X Y)
    (hCan : IsCanonical (record I q) ((canonicalInvariant (n+1)).inv (record I q)) T) :
    IsCanonical (record I 1) ((canonicalInvariant (n+1)).inv (record I 1)) T := by
  induction T with
  | refl => trivial
  | step T C π hπ ih =>
    have hBefore := ih hCan.1
    refine ⟨hBefore,?_⟩
    rcases hCan.2 with he | hc
    · exact Or.inl he
    · by_cases hne : C.Nonempty
      · obtain ⟨c,hc'⟩ := hne
        have hSurvive : (geoTransformAlong (record I q) T).cosupp.Nonempty := by
          rw [hc] at hc'
          exact ⟨c,hc'.1⟩
        have hEq := finite_retained_maximum_eq I q hQ hCap T hBefore hCan.1 hSurvive
        dsimp only at hEq
        exact Or.inr (hc.trans hEq.symm)
      · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hne)

/-- A literal chart of the certified native phase gives whole mark-one
canonicality when its raw record has the whole vanishing ideal at maximal
order. The simultaneous certificate supplies the chart's canonicality. -/
theorem whole_markOne_of_retained_native_chart
    {ι : Type} (W : Set X) (H : ℕ → ℕ) (S : Set X)
    (A : HironakaG8NativeRelativeClearing.NativeWindows X ι W [] H S)
    (T : BlowupTower X Y)
    (hStages : HironakaG8NativeSimultaneousCentre.NativeSimultaneousStages
      (canonicalInvariant (n+1)) A.openSet A.powered T)
    (i : ι)
    (hIdeal : (A.record i).ideal =
      vanishingIdeal (n := n+1) ((Subtype.val : A.openSet i → X) ⁻¹' W))
    (hCap : IsMaximalOrderAlong (A.record i).N (A.record i).ideal (A.record i).d) :
    let U := A.openSet i
    let I := vanishingIdeal (n := n+1) ((Subtype.val : U → X) ⁻¹' W)
    let P : MarkedIdeal (n+1) (CMfd.of (n := n+1) U) := ⟨univ, [], I, 1⟩
    IsCanonical P ((canonicalInvariant (n+1)).inv P) (restrict U T) := by
  intro U I P
  let XU := CMfd.of (n := n+1) U
  let Q : MarkedIdeal (n+1) XU := ⟨univ, [], I, (A.record i).d⟩
  have hN : (A.record i).N = univ := (A.native i).2.2.1
  have hE : (A.record i).E = [] := A.boundary i
  have hQ : A.record i = Q :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of hN hE hIdeal rfl
  have hDom := A.domain i
  have hCan := HironakaG8NativePrefixOriginalCanonical.simultaneous_powered_prefix_raw_canonical
    (Nat.succ_pos n) A.openSet A.record A.domain A.exponent A.positive T hStages i
  rw [← HironakaSmoothSubmersionOriginalAmbientCanonical.canonicalInvariant_eq_invFamily (Nat.succ_pos n)] at hCan
  rw [hQ] at hDom hCap hCan
  exact finite_native_retained_epoch_whole_markOne_canonical I (A.record i).d
    hDom hCap (restrict U T) hCan

end
end Hironaka.HironakaG8PrincipalRetainedEpochFinite
