import Hironaka.Resolution.HironakaG8CommonIdealControlledOrders
import Hironaka.Resolution.HironakaG8InitialCommonIdealMaximum
import Hironaka.Resolution.HironakaSharpActualChronologicalResidualDictionary

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8PrincipalRetainedEpoch
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerSplit BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism CanonicalCentres ResolutionDriver ResolutionInvariantSpec
  NonmonomialOrderLocal NonmonomialOrderTail NonmonomialOrderRegime NonmonomialOrderCanonical
  GeneralValue CompanionRebase CompanionReductionAlong StepOneRegime
  GermIdealOrder RelativePrincipalizationSpan RestrictedIdealExtension HomogenizedIdealAlong

variable {n : ℕ} {X Y : CMfd.{0} (n+1)}

private abbrev record (I : GermIdeal (n+1) X) (d : ℕ) : MarkedIdeal (n+1) X := ⟨univ,[],I,d⟩

/-- Positive order retained through the first blowup makes both evaluators
read the same initial companion along the literal same one-step tail. -/
theorem first_step_value_eq_of_retained_order
    (I : GermIdeal (n+1) X) {d e o : ℕ} (hd : d ≤ o) (he : e ≤ o) (ho : o ≠ 0)
    (C : Set X) (π : Y → X) (hπ : IsBlowupAlong (n+1) C π) (y : Y)
    (hP : OrdRegime (record I d) o (.refl : BlowupTower X X) (π y))
    (hQ : OrdRegime (record I e) o (.refl : BlowupTower X X) (π y))
    (hA : nmOrd ((record I d).geoTransform C π) y = o)
    (hB : nmOrd ((record I e).geoTransform C π) y = o) :
    let T : BlowupTower X Y := .step .refl C π hπ
    (canonicalInvariant (n+1)).inv (record I d) T y =
      (canonicalInvariant (n+1)).inv (record I e) T y := by
  let P := record I d
  let Q := record I e
  let T : BlowupTower X Y := .step .refl C π hπ
  change genInv _ P T y = genInv _ Q T y
  rw [genInv_of_nmOrd_ne_zero _ P T hA ho, genInv_of_nmOrd_ne_zero _ Q T hB ho]
  have hRunP : regimeRun (OrdRegime P o) T y = 1 :=
    regimeRun_step_of (OrdRegime P o) .refl C π hπ hP
  have hRunQ : regimeRun (OrdRegime Q o) T y = 1 :=
    regimeRun_step_of (OrdRegime Q o) .refl C π hπ hQ
  rw [hRunP,hRunQ]
  have hComp : compAt P o .refl = compAt Q o .refl := by
    change companionAlong _ _ _ _ o d = companionAlong _ _ _ _ o e
    unfold companionAlong
    rw [if_neg (Nat.not_lt.mpr hd),if_neg (Nat.not_lt.mpr he)]
    rfl
  let F : ∀ {A : CMfd.{0} (n+1)}, MarkedIdeal (n+1) A →
      ∀ {B : CMfd.{0} (n+1)}, BlowupTower A B → B → ℕ ×ₗ WithTop (ValTy n) :=
    fun {_} M {_} S z => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) n) M S z
  have hLow : genLowerValue F P o .refl T y = genLowerValue F Q o .refl T y := by
    unfold genLowerValue
    rw [hComp]
    rfl
  exact congrArg (fun w => toLex (o, toLex (Sum.inr w))) hLow

/-- Exact order on the first centre prevents the high controlled ideal
from acquiring a factor in its only born boundary slot. -/
private theorem first_high_ordGe_eq_cosupport
    (I : GermIdeal (n+1) X) (q : ℕ) (hQ : IsInvDomain (n+1) (record I q))
    (hUpper : IsMaximalOrderAlong (record I q).N I q)
    (C : Set X) (π : Y → X) (hπ : IsBlowupAlong (n+1) C π)
    (hCentre : (record I q).IsAdmissibleCentre C) (j : ℕ) :
    let B := (record I q).geoTransform C π
    ordGe B j = cosupport (n+1) B.N B.ideal j := by
  let Q := record I q
  let B := Q.geoTransform C π
  have hWF := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre
    hQ.isWellFormed hCentre hπ
  have hNo : ∀ z ∈ B.N, ∀ i : Fin B.E.length, z ∈ B.E.get i →
      ∃ g, B.ideal.mem z g ∧
        ¬ IsInSpanOnAt (n := n+1) B.N ((vanishingIdeal (n := n+1) (B.E.get i)).mem z) z g := by
    intro z hz i hi
    have hE : B.E = [π ⁻¹' C] := rfl
    have hMember : B.E.get i = π ⁻¹' C := by
      simp [hE]
    rw [hMember] at hi ⊢
    obtain ⟨g,hg,hNoEx⟩ := ExceptionalPushforwardAlong.exists_not_isInSpanOnAt_exceptionalDivisor
      hπ hQ.isWellFormed.isClosedSubmanifold_N hQ.isWellFormed.isCoherent hCentre.2.1 hi hz (hUpper (π z))
    refine ⟨g,hg,?_⟩
    rintro ⟨k,s,a,hs,ha,he⟩
    apply hNoEx
    exact ⟨k,s,a,fun i => NonmonomialTransformTower.exceptionalDivisor_mem_of_vanishingIdeal_mem
      hπ hQ.isWellFormed.isSNCDivisor hCentre.2.2 hi (hs i),ha,he⟩
  have hEq := HironakaSharpActualChronologicalResidualDictionary.nonmonomialPartAlong_eq_restrictOn_of_no_member_factor
    hWF.isClosedSubmanifold_N hWF.isSNCDivisor hWF.isTransverse hWF.isCoherent hNo
  change nmPart B = restrictOn (n+1) B.N B.ideal at hEq
  change cosupport (n+1) B.N (nmPart B) j = cosupport (n+1) B.N B.ideal j
  rw [hEq]
  exact Subset.antisymm
    (MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe (restrictLe_self_restrictOn hWF.isCoherent) j)
    (MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe restrictLe_restrictOn j)

/-- On the surviving first maximal-order epoch, the next literal maximum
of the native top-mark record equals the original mark-one maximum. The
shared principal residual supplies the first-order agreement, while the
retained original companion supplies every tie comparison. -/
theorem first_successor_maxLocus_markOne_eq_topMark
    (I : GermIdeal (n+1) X) {q : ℕ} (hq : 1 ≤ q)
    (hQ : IsInvDomain (n+1) (record I q))
    (hUpper : IsMaximalOrderAlong (record I q).N I q)
    (hPrincipal : ∀ x : X, ∃ f : X → ℂ, HolomorphicAt (n+1) f x ∧
      ∀ g, I.mem x g ↔ HolomorphicAt (n+1) g x ∧
        IsInSpanOnAt (n := n+1) univ (· = f) x g)
    (C : Set X) (π : Y → X) (hπ : IsBlowupAlong (n+1) C π)
    (hLow : IsCanonical (record I 1) ((canonicalInvariant (n+1)).inv (record I 1))
      (.step .refl C π hπ))
    (hHigh : IsCanonical (record I q) ((canonicalInvariant (n+1)).inv (record I q))
      (.step .refl C π hπ))
    (hSurvive : ((record I q).geoTransform C π).cosupp.Nonempty) :
    let T : BlowupTower X Y := .step .refl C π hπ
    let R := canonicalInvariant (n+1)
    let P := record I 1
    let Q := record I q
    maxLocus (R.inv P T) (P.geoTransform C π).cosupp =
      maxLocus (R.inv Q T) (Q.geoTransform C π).cosupp := by
  let P := record I 1
  let Q := record I q
  let R := canonicalInvariant (n+1)
  let T : BlowupTower X Y := .step .refl C π hπ
  let A := P.geoTransform C π
  let B := Q.geoTransform C π
  have hP : IsInvDomain (n+1) P :=
    ⟨⟨hQ.isWellFormed.1,hQ.isWellFormed.2,hQ.isWellFormed.3,hQ.isWellFormed.4⟩,
      hQ.dimLE,le_rfl,hQ.isNonzeroAlongAt⟩
  have hTL := R.isInvValue.isGeoTestTower_of_isCanonical hP T hLow
  have hTH := R.isInvValue.isGeoTestTower_of_isCanonical hQ T hHigh
  have hLC : P.IsAdmissibleCentre C := ⟨hTL.2.1,hTL.2.2.1,hTL.2.2.2⟩
  have hHC : Q.IsAdmissibleCentre C := ⟨hTH.2.1,hTH.2.2.1,hTH.2.2.2⟩
  have hPrincipalP : ∀ x ∈ P.N, ∃ f : X → ℂ, HolomorphicAt (n+1) f x ∧
      ∀ g, P.ideal.mem x g ↔ HolomorphicAt (n+1) g x ∧
        IsInSpanOnAt (n := n+1) P.N (· = f) x g := fun x _ => hPrincipal x
  have hNoOld : ∀ x ∈ P.N, ∀ i : Fin P.E.length, x ∈ P.E.get i →
      ∃ g, P.ideal.mem x g ∧
        ¬ IsInSpanOnAt (n := n+1) P.N ((vanishingIdeal (n := n+1) (P.E.get i)).mem x) x g :=
    fun _ _ i => Fin.elim0 i
  obtain ⟨hN,_hE,_hFac,hCos,_hNm,hOrd⟩ :=
    HironakaG8CommonIdealControlledOrders.common_principal_ideal_next_nonmonomial_order
      (Nat.succ_pos n) P hP.isWellFormed rfl hP.isNonzeroAlongAt hPrincipalP hNoOld hq hπ hLC hHC
  change A.N = B.N at hN
  change B.cosupp ⊆ A.cosupp at hCos
  change ∀ y : Y, nmOrd A y = nmOrd B y at hOrd
  have hInit (x : X) : nmOrd P x ≤ q := by
    apply nmOrd_le_of_notMem
    have hEq := HironakaSharpOriginalProductTraceOrder.ordGe_ordinaryTraceMarked_eq_cosupport
      (univ : Set X) I hP.isWellFormed.isCoherent (q+1)
    change ordGe P (q+1) = cosupport (n+1) univ I (q+1) at hEq
    rw [hEq]
    exact hUpper x
  let F : ∀ {A : CMfd.{0} (n+1)}, MarkedIdeal (n+1) A →
      ∀ {B : CMfd.{0} (n+1)}, BlowupTower A B → B → ℕ ×ₗ WithTop (ValTy n) :=
    fun {_} M {_} S z => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) n) M S z
  have hLCan : IsCanonical P (genInv F P) T := hLow
  have hHCan : IsCanonical Q (genInv F Q) T := hHigh
  have hBound (y : Y) (hy : y ∈ A.cosupp) :
      π y ∈ P.cosupp ∧ nmOrd A y ≤ nmOrd P (π y) :=
    nmOrd_step_le_of_canonical (Nat.succ_pos n) hP (ordMonotone_genInv F P)
      .refl C π hπ hTL hLCan.2 hy
  have hBoundQ (y : Y) (hy : y ∈ B.cosupp) :
      π y ∈ Q.cosupp ∧ nmOrd B y ≤ nmOrd Q (π y) :=
    nmOrd_step_le_of_canonical (Nat.succ_pos n) hQ (ordMonotone_genInv F Q)
      .refl C π hπ hTH hHCan.2 hy
  have hOrdGe := first_high_ordGe_eq_cosupport I q hQ hUpper C π hπ hHC q
  change ordGe B q = B.cosupp at hOrdGe
  have hBD : IsInvDomain (n+1) B := InvDomainTowerAlong.isInvDomain_geoTransformAlong hQ T hTH
  have hLevel (y : Y) : y ∈ B.cosupp ↔ y ∈ A.cosupp ∧ nmOrd A y = q := by
    constructor
    · intro hy
      have hyA := hCos hy
      have hlo : q ≤ nmOrd B y := (mem_ordGe_iff hBD.isWellFormed hBD.isNonzeroAlongAt
        (B.cosupp_subset_N hy) q).mp (hOrdGe.symm ▸ hy)
      exact ⟨hyA,le_antisymm ((hBound y hyA).2.trans (hInit (π y))) (by rw [hOrd y]; exact hlo)⟩
    · rintro ⟨hyA,hyq⟩
      have hyN : y ∈ B.N := hN ▸ A.cosupp_subset_N hyA
      rw [← hOrdGe]
      apply (mem_ordGe_iff hBD.isWellFormed hBD.isNonzeroAlongAt hyN q).mpr
      rw [← hOrd y,hyq]
  have hValue (y : Y) (hy : y ∈ B.cosupp) : R.inv P T y = R.inv Q T y := by
    obtain ⟨hyA,hyq⟩ := (hLevel y).mp hy
    have hyQ : nmOrd B y = q := (hOrd y).symm.trans hyq
    have hp := hBound y hyA
    have hHighP := hBoundQ y hy
    have hπOrd : nmOrd P (π y) = q :=
      le_antisymm (hInit (π y)) (hyq ▸ hp.2)
    have hπOrdQ : nmOrd Q (π y) = q := hπOrd
    exact first_step_value_eq_of_retained_order I hq le_rfl (by omega)
      C π hπ y ⟨hp.1,hπOrd⟩ ⟨hHighP.1,hπOrdQ⟩ hyq hyQ
  have hLt {z y : Y} (h : nmOrd A z < nmOrd A y) : R.inv P T z < R.inv P T y := by
    change genInv F P T z < genInv F P T y
    exact genInv_lt_of_nmOrd_lt F P h
  obtain ⟨a,ha⟩ := hSurvive
  obtain ⟨haA,haq⟩ := (hLevel a).mp ha
  change maxLocus (R.inv P T) A.cosupp = maxLocus (R.inv Q T) B.cosupp
  ext y
  constructor
  · intro hy
    have hyq : nmOrd A y = q := le_antisymm ((hBound y hy.1).2.trans (hInit (π y))) (by
      by_contra hn
      exact (not_lt_of_ge (hy.2 a haA)) (hLt (by rw [haq]; exact Nat.lt_of_not_ge hn)))
    have hyB := (hLevel y).mpr ⟨hy.1,hyq⟩
    refine ⟨hyB,fun z hz => ?_⟩
    rw [← hValue z hz,← hValue y hyB]
    exact hy.2 z (hCos hz)
  · intro hy
    obtain ⟨hyA,hyq⟩ := (hLevel y).mp hy.1
    refine ⟨hyA,fun z hz => ?_⟩
    by_cases hzB : z ∈ B.cosupp
    · rw [hValue z hzB,hValue y hy.1]
      exact hy.2 z hzB
    · have hzq : nmOrd A z ≠ q := fun h => hzB ((hLevel z).mpr ⟨hz,h⟩)
      exact le_of_lt (hLt (by
        rw [hyq]
        exact lt_of_le_of_ne ((hBound z hz).2.trans (hInit (π z))) hzq))

/-- Two literal native steps from a boundary-free principal maximal-order
record are whole mark-one canonical whenever the second centre is taken
while that native epoch is active. A nonempty second centre witnesses
activity itself. -/
theorem two_native_steps_whole_markOne_canonical
    {Z : CMfd.{0} (n+1)} (I : GermIdeal (n+1) X) {q : ℕ} (hq : 1 ≤ q)
    (hQ : IsInvDomain (n+1) (record I q))
    (hUpper : IsMaximalOrderAlong (record I q).N I q)
    (hPrincipal : ∀ x : X, ∃ f : X → ℂ, HolomorphicAt (n+1) f x ∧
      ∀ g, I.mem x g ↔ HolomorphicAt (n+1) g x ∧
        IsInSpanOnAt (n := n+1) univ (· = f) x g)
    (C : Set X) (hC : C.Nonempty) (π : Y → X) (hπ : IsBlowupAlong (n+1) C π)
    (D : Set Y) (σ : Z → Y) (hσ : IsBlowupAlong (n+1) D σ)
    (hNative : IsCanonical (record I q) ((canonicalInvariant (n+1)).inv (record I q))
      (.step (.step .refl C π hπ) D σ hσ)) :
    IsCanonical (record I 1) ((canonicalInvariant (n+1)).inv (record I 1))
      (.step (.step .refl C π hπ) D σ hσ) := by
  let P := record I 1
  let Q := record I q
  let T : BlowupTower X Y := .step .refl C π hπ
  let R := canonicalInvariant (n+1)
  have hP : IsInvDomain (n+1) P :=
    ⟨⟨hQ.isWellFormed.1,hQ.isWellFormed.2,hQ.isWellFormed.3,hQ.isWellFormed.4⟩,
      hQ.dimLE,le_rfl,hQ.isNonzeroAlongAt⟩
  have hCos (x : X) (d : ℕ) :
      x ∈ cosupport (n+1) univ I d ↔ d ≤ HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder univ I x :=
    HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder_cosupport_iff
      hP.isWellFormed.isClosedSubmanifold_N hP.isWellFormed.isCoherent hP.isNonzeroAlongAt (mem_univ x) d
  have hOrdBound (x : X) : HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder univ I x ≤ q :=
    Nat.le_of_lt_succ (Nat.lt_of_not_ge (mt (hCos x (q+1)).mpr (hUpper x)))
  have hBefore : IsCanonical Q (R.inv Q) T := hNative.1
  have hFirst : C = maxLocus (R.inv Q (.refl : BlowupTower X X)) Q.cosupp := by
    rcases hBefore.2 with hEmpty | hFirst
    · exact False.elim ((not_nonempty_iff_eq_empty.mpr hEmpty) hC)
    · exact hFirst
  obtain ⟨a,ha⟩ := hC
  have haQ : a ∈ Q.cosupp := (hFirst ▸ ha :
    a ∈ maxLocus (R.inv Q (.refl : BlowupTower X X)) Q.cosupp).1
  have hTop : ∃ x : X, HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder univ I x = q :=
    ⟨a,le_antisymm (hOrdBound a) ((hCos a q).mp haQ)⟩
  have hInit := HironakaG8InitialCommonIdealMaximum.initial_maxLocus_markOne_eq_topMark
    (X := X) I hP hq hOrdBound hTop
  have hLow : IsCanonical P (R.inv P) T := ⟨trivial,Or.inr (hFirst.trans hInit.symm)⟩
  refine ⟨hLow,?_⟩
  rcases hNative.2 with hEmpty | hNext
  · exact Or.inl hEmpty
  · by_cases hD : D.Nonempty
    · obtain ⟨z,hz⟩ := hD
      have hzB : z ∈ (Q.geoTransform C π).cosupp :=
        (hNext ▸ hz : z ∈ maxLocus (R.inv Q T) (Q.geoTransform C π).cosupp).1
      have hMax := first_successor_maxLocus_markOne_eq_topMark I hq hQ hUpper hPrincipal
        C π hπ hLow hBefore ⟨z,hzB⟩
      dsimp only at hMax
      exact Or.inr (hNext.trans hMax.symm)
    · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hD)

end
end Hironaka.HironakaG8PrincipalRetainedEpoch
