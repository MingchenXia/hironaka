import Hironaka.Resolution.HironakaG8OccupiedOrderReset
import Hironaka.Resolution.HironakaG8PrincipalRetainedEpochFinite
import Hironaka.Resolution.HironakaG8CommonTowerNonmonomialOrders
import Hironaka.Resolution.HironakaHypersurfaceStrictIdeal
import Hironaka.Invariant.MonomialPartEtale

/-! On an occupied hypersurface step, the mark-one controlled remainder
and the fresh strict ideal retain the same nonmonomial part. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8OccupiedPrincipalResidual
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings HironakaEmbeddedAnalytic ResolutionInvariantSpec GermIdealOrder
  NonmonomialOrderLocal NonmonomialOrderTail CompanionRebase CompanionReductionAlong
  NonmonomialOrderRegime GeneralValue StepOneRegime StepOneEmptyPrefix BlowupTowerSplit
  CanonicalCentres HironakaG8OccupiedOrderReset
  MarkedIdealBiholomorphism MonomialPartAlong HironakaHypersurfaceStrictIdeal
  HironakaSharpActualChronologicalResidualDictionary HomogenizedIdealAlong
  HironakaG8CommonTowerNonmonomialOrders HironakaG8PrincipalRetainedEpochFinite

variable {n : ℕ} {X Y : CMfd.{0} (n+1)}

private abbrev whole (W : Set X) (E : List (Set X)) (d : ℕ) : MarkedIdeal (n+1) X :=
  ⟨univ,E,vanishingIdeal (n := n+1) W,d⟩

/-- The actual lower-order restart on a strict hypersurface shares the
entire nonmonomial ideal of the mark-one controlled history. Exact high
order prevents a new factor, and old nonfactor witnesses survive with
the boundary still in its actual order. -/
theorem occupied_hypersurface_residual_eq_fresh_ideal
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (hI : (vanishingIdeal (n := n+1) W).IsInvertible)
    (hPure : W ⊆ closure (regularLocus (n := n+1) W n))
    (E : List (Set X)) (μ : ℕ) (hμ : 2 ≤ μ)
    (hDom : IsInvDomain (n+1) (whole W E 1))
    (hOld : HasNoBoundaryFactor (whole W E 1))
    (hBound : ∀ x ∈ W, order (n+1) univ (vanishingIdeal (n := n+1) W) x ≤ (μ : ℕ∞))
    (C : Set X) (π : Y → X) (hπ : IsBlowupAlong (n+1) C π)
    (hHigh : (whole W E μ).IsAdmissibleCentre C) :
    let A := (whole W E 1).geoTransform C π
    let B := (whole W E μ).geoTransform C π
    let J := vanishingIdeal (n := n+1) (strictTransform (n+1) π W)
    B.ideal = J ∧ HasNoBoundaryFactor B ∧ A.N = univ ∧ A.E = B.E ∧ nmPart A = J := by
  let P := whole W E 1
  let Q := whole W E μ
  let A := P.geoTransform C π
  let B := Q.geoTransform C π
  let J := vanishingIdeal (n := n+1) (strictTransform (n+1) π W)
  have hLow : P.IsAdmissibleCentre C := ⟨hHigh.1,
    hHigh.2.1.trans (cosupport_anti (show 1 ≤ μ by omega)),hHigh.2.2⟩
  have hWF : Q.IsWellFormed :=
    ⟨hDom.isWellFormed.1,hDom.isWellFormed.2,hDom.isWellFormed.3,hDom.isWellFormed.4⟩
  have hCap : IsMaximalOrderAlong Q.N Q.ideal Q.d := by
    intro x hx
    have hxP : x ∈ P.cosupp := cosupport_anti (show 1 ≤ μ+1 by omega) hx
    have hxW : x ∈ W := by
      change x ∈ (⟨univ,E,vanishingIdeal (n := n+1) W,1⟩ : MarkedIdeal (n+1) X).cosupp at hxP
      rwa [HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hW.isClosed] at hxP
    have hOrd := (le_order_iff (𝔞 := Q.ideal) (fun _ hf => hf.1)).mpr hx.2
    have hBad : μ+1 ≤ μ := by
      have h := hOrd.trans (hBound x hxW)
      exact_mod_cast h
    omega
  have hNo : HasNoBoundaryFactor B := hasNoBoundaryFactor_step Q hWF hOld hπ hHigh hCap
  have hB : B.ideal = J := by
    change (Q.geoTransform C π).ideal = J
    rw [geoTransform_ideal_eq_controlledTransform (𝔪 := Q) rfl hWF.isCoherent hπ]
    exact controlledTransform_vanishingIdeal_eq_strictTransform hW hI hPure hWF.isSNCDivisor hμ
      hBound hHigh hπ
  let T : BlowupTower X Y := .step .refl C π hπ
  obtain ⟨_hN,hE,hPart,_hOrder⟩ :=
    common_mark_tower_orders (Nat.succ_pos n) P hDom.isWellFormed hDom.isNonzeroAlongAt μ T
      ⟨trivial,hLow⟩ ⟨trivial,hHigh⟩
  have hBW := GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hWF hHigh hπ
  have hBN : B.N = univ := geoTransform_N_eq_univ (𝔪 := Q) rfl hπ
  have hRes := nonmonomialPartAlong_eq_restrictOn_of_no_member_factor hBW.isClosedSubmanifold_N
    hBW.isSNCDivisor hBW.isTransverse hBW.isCoherent hNo
  change nmPart B = RestrictedIdealExtension.restrictOn (n+1) B.N B.ideal at hRes
  rw [hBN,BlowupTowerTransforms.restrictOn_univ hBW.isCoherent,hB] at hRes
  exact ⟨hB,hNo,hBN,hE,hPart.trans hRes⟩

/-- The exact companion on a specified literal open, before evaluating
any further native invariant. -/
abbrev companionOn (M : MarkedIdeal (n+1) X) (U : Opens X) (q : ℕ) :=
  companionOf (n+1) (M := CMfd.of (n := n+1) U)
    (MarkedIdeal.pullback (Subtype.val : U → X) M) q

/-- In the positive range at or above both marks, agreement of the whole
nonmonomial parts and full ordered boundary identifies both masks and both
literal companions on each common open. -/
theorem companionOn_eq_of_common_nonmonomial
    (A B : MarkedIdeal (n+1) X) (hA : IsInvDomain (n+1) A) (hB : IsInvDomain (n+1) B)
    (hN : A.N = B.N) (hE : A.E = B.E) (hPart : nmPart A = nmPart B)
    (q : ℕ) (hqA : A.d ≤ q) (hqB : B.d ≤ q) :
    ordMask A q = ordMask B q ∧ ∀ U : Opens X, companionOn A U q = companionOn B U q := by
  constructor
  · have hGe : ordGe A (q+1) = ordGe B (q+1) := by
      change cosupport (n+1) A.N (nmPart A) (q+1) = cosupport (n+1) B.N (nmPart B) (q+1)
      rw [hN,hPart]
    ext y
    change y ∈ (closure (ordGe A (q+1)))ᶜ ↔ y ∈ (closure (ordGe B (q+1)))ᶜ
    rw [hGe]
  · intro U
    let f := (Subtype.val : U → X)
    let A' : MarkedIdeal (n+1) U := MarkedIdeal.pullback f A
    let B' : MarkedIdeal (n+1) U := MarkedIdeal.pullback f B
    have pull (M : MarkedIdeal (n+1) X) (h : IsInvDomain (n+1) M) :
        GermIdeal.pullback (m := n+1) f (nmPart M) =
          nmPart (M := CMfd.of (n := n+1) U) (MarkedIdeal.pullback f M) := by
      have hw := h.isWellFormed
      have hmon := isCoherent_monomialPartAlong (Nat.succ_pos n) hw.isClosedSubmanifold_N
        hw.isSNCDivisor hw.isTransverse hw.isCoherent h.isNonzeroAlongAt
      have hnm := isCoherent_nonmonomialPartAlong (Nat.succ_pos n) hw.isClosedSubmanifold_N
        hw.isSNCDivisor hw.isTransverse hw.isCoherent h.isNonzeroAlongAt
      exact MonomialPartEtale.pullback_nonmonomialPartAlong (fun y =>
        ⟨DerivativeIdealAlongEtale.openInv U y,DerivativeIdealAlongEtale.isLocalInverseAt_val U y⟩)
        hw.isCoherent hmon hnm
    have hN' : A'.N = B'.N := congrArg (f ⁻¹' ·) hN
    have hE' : A'.E = B'.E := congrArg (List.map (f ⁻¹' ·)) hE
    have hPart' : nmPart (M := CMfd.of (n := n+1) U) A' =
        nmPart (M := CMfd.of (n := n+1) U) B' := by
      change nmPart (M := CMfd.of (n := n+1) U) (MarkedIdeal.pullback f A) =
        nmPart (M := CMfd.of (n := n+1) U) (MarkedIdeal.pullback f B)
      rw [← pull A hA,← pull B hB,hPart]
    change companionAlong A'.N A'.E (nmPart (M := CMfd.of (n := n+1) U) A') _ q A.d =
      companionAlong B'.N B'.E (nmPart (M := CMfd.of (n := n+1) U) B') _ q B.d
    unfold companionAlong
    rw [if_neg (Nat.not_lt.mpr hqA),if_neg (Nat.not_lt.mpr hqB),hN',hE',hPart']

/-- The exact residual identity supplies a comparison of the actual
companion on the controlled history with the companion of the fresh
strict vanishing record at any positive lower mark. -/
theorem occupied_hypersurface_companion_eq_fresh_companion
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (hI : (vanishingIdeal (n := n+1) W).IsInvertible)
    (hPure : W ⊆ closure (regularLocus (n := n+1) W n))
    (E : List (Set X)) (μ : ℕ) (hμ : 2 ≤ μ)
    (hDom : IsInvDomain (n+1) (whole W E 1))
    (hOld : HasNoBoundaryFactor (whole W E 1))
    (hBound : ∀ x ∈ W, order (n+1) univ (vanishingIdeal (n := n+1) W) x ≤ (μ : ℕ∞))
    (C : Set X) (π : Y → X) (hπ : IsBlowupAlong (n+1) C π)
    (hHigh : (whole W E μ).IsAdmissibleCentre C) (q : ℕ) (hq : 1 ≤ q) :
    let A := (whole W E 1).geoTransform C π
    let F := whole (strictTransform (n+1) π W) A.E q
    IsInvDomain (n+1) F ∧ HasNoBoundaryFactor F ∧
    ordMask A q = ordMask F q ∧ ∀ U : Opens Y, companionOn A U q = companionOn F U q := by
  let P := whole W E 1
  let Q := whole W E μ
  let A := P.geoTransform C π
  let B := Q.geoTransform C π
  let F := whole (strictTransform (n+1) π W) A.E q
  have hLow : P.IsAdmissibleCentre C := ⟨hHigh.1,
    hHigh.2.1.trans (cosupport_anti (show 1 ≤ μ by omega)),hHigh.2.2⟩
  have hQ : IsInvDomain (n+1) Q :=
    ⟨⟨hDom.isWellFormed.1,hDom.isWellFormed.2,hDom.isWellFormed.3,hDom.isWellFormed.4⟩,
      hDom.dimLE,by change 1 ≤ μ; omega,hDom.isNonzeroAlongAt⟩
  have hA : IsInvDomain (n+1) A :=
    InvDomainTowerAlong.isInvDomain_geoTransformAlong hDom (.step .refl C π hπ) ⟨trivial,hLow⟩
  have hB : IsInvDomain (n+1) B :=
    InvDomainTowerAlong.isInvDomain_geoTransformAlong hQ (.step .refl C π hπ) ⟨trivial,hHigh⟩
  obtain ⟨hIeq,hNo,hN,hE,hPart⟩ :=
    occupied_hypersurface_residual_eq_fresh_ideal W hW hI hPure E μ hμ hDom hOld hBound C π hπ hHigh
  have hNB : B.N = univ := geoTransform_N_eq_univ (𝔪 := Q) rfl hπ
  have hF : F = { B with d := q } :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of hNB.symm hE hIeq.symm rfl
  have hDF : IsInvDomain (n+1) F := by
    rw [hF]
    exact ⟨⟨hB.isWellFormed.1,hB.isWellFormed.2,hB.isWellFormed.3,hB.isWellFormed.4⟩,
      hB.dimLE,hq,hB.isNonzeroAlongAt⟩
  have hNoF : HasNoBoundaryFactor F := by rw [hF]; exact hNo
  have hNorm := nonmonomialPartAlong_eq_restrictOn_of_no_member_factor hDF.isWellFormed.1
    hDF.isWellFormed.3 hDF.isWellFormed.4 hDF.isWellFormed.2 hNoF
  change nmPart F = RestrictedIdealExtension.restrictOn (n+1) univ F.ideal at hNorm
  rw [BlowupTowerTransforms.restrictOn_univ hDF.isWellFormed.isCoherent] at hNorm
  have hSame : nmPart A = nmPart F := hPart.trans hNorm.symm
  exact ⟨hDF,hNoF,companionOn_eq_of_common_nonmonomial A F hA hDF hN rfl hSame q hq le_rfl⟩

private abbrev evaluator : ∀ {A : CMfd.{0} (n+1)}, MarkedIdeal (n+1) A →
    ∀ {B : CMfd.{0} (n+1)}, BlowupTower A B → B → ℕ ×ₗ WithTop (ValTy n) :=
  fun {_} M {_} S z => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) n) M S z

open Classical in
private def readOn (U : Opens X) (M : MarkedIdeal (n+1) U) (T : BlowupTower X Y) (y : Y) :
    WithTop (ℕ ×ₗ WithTop (ValTy n)) :=
  if h : T.proj y ∈ U then ↑(evaluator M (restrict U T) (⟨y,h⟩ : openPreimage T U)) else ⊤

private theorem readOn_eq_value_of_mask (A : MarkedIdeal (n+1) X) (U : Opens X)
    (T : BlowupTower X Y) (y : Y) (q : ℕ) (hU : ordMask A q = U)
    (hOrder : nmOrd (geoTransformAlong A T) y = q) (hq : 1 ≤ q)
    (hRun : regimeRun (OrdRegime A q) T y = T.length) :
    (canonicalInvariant (n+1)).inv A T y =
      toLex (q,toLex (Sum.inr (readOn U (companionOn A U q) T y))) := by
  subst U
  change genInv evaluator A T y = _
  have hne : q ≠ 0 := by omega
  rw [genInv_of_nmOrd_ne_zero evaluator A T hOrder hne,hRun]
  let f (s : Σ Z : CMfd.{0} (n+1), BlowupTower X Z × BlowupTower Z Y) :=
    genLowerValue evaluator A q s.2.1 s.2.2 y
  change toLex (q,toLex (Sum.inr (f (split T T.length)))) = _
  rw [split_of_length_le T T.length le_rfl]
  rfl

/-- The occupied chronological value reads the same native companion as
the fresh strict record on a common suffix that stays at its new order.
Every inherited boundary slot remains in the two compared records. -/
theorem occupied_hypersurface_restart_value_eq_fresh
    {Z : CMfd.{0} (n+1)}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (hI : (vanishingIdeal (n := n+1) W).IsInvertible)
    (hPure : W ⊆ closure (regularLocus (n := n+1) W n))
    (E : List (Set X)) (μ : ℕ) (hμ : 2 ≤ μ)
    (hDom : IsInvDomain (n+1) (whole W E 1))
    (hOld : HasNoBoundaryFactor (whole W E 1))
    (hBound : ∀ x ∈ W, order (n+1) univ (vanishingIdeal (n := n+1) W) x ≤ (μ : ℕ∞))
    (C : Set X) (π : Y → X) (hπ : IsBlowupAlong (n+1) C π)
    (hHigh : (whole W E μ).IsAdmissibleCentre C) (q : ℕ) (hq : 1 ≤ q)
    (S : BlowupTower Y Z) (z : Z) :
    let M := whole W E 1
    let H : BlowupTower X Y := .step .refl C π hπ
    let A := geoTransformAlong M H
    let F := whole (strictTransform (n+1) π W) A.E q
    nmOrd (geoTransformAlong M (H.append S)) z = q →
    nmOrd (geoTransformAlong F S) z = q →
    q < nmOrd M (π (S.proj z)) →
    regimeRun (OrdRegime A q) S z = S.length →
    regimeRun (OrdRegime F q) S z = S.length →
    (canonicalInvariant (n+1)).inv M (H.append S) z =
      (canonicalInvariant (n+1)).inv F S z := by
  dsimp only
  intro hChron hFresh hDrop hRunA hRunF
  let M := whole W E 1
  let H : BlowupTower X Y := .step .refl C π hπ
  let A := geoTransformAlong M H
  let F := whole (strictTransform (n+1) π W) A.E q
  have hOrdA : nmOrd (geoTransformAlong A S) z = q := by
    change nmOrd (geoTransformAlong (geoTransformAlong M H) S) z = q
    rw [← geoTransformAlong_append]
    exact hChron
  obtain ⟨_hDF,_hNF,hMask,hComp⟩ :=
    occupied_hypersurface_companion_eq_fresh_companion W hW hI hPure E μ hμ hDom hOld hBound
      C π hπ hHigh q hq
  let U := ordMask A q
  have hUF : ordMask F q = U := hMask.symm
  rw [canonical_value_after_occupied_order_drop M .refl C π hπ S z q hChron hDrop]
  rw [readOn_eq_value_of_mask A U S z q rfl hOrdA hq hRunA,
    readOn_eq_value_of_mask F U S z q hUF hFresh hq hRunF]
  have hEq : companionOn A U q = companionOn F U q := hComp U
  exact congrArg (fun J => (toLex (q,toLex (Sum.inr (readOn U J S z))) : ValTy (n+1))) hEq

end
end Hironaka.HironakaG8OccupiedPrincipalResidual
