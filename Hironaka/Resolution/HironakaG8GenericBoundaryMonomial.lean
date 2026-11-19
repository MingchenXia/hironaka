import Hironaka.Resolution.HironakaG8BoundaryGenericOrder
import Hironaka.Resolution.HironakaG8ExceptionalProbeDensity
import Hironaka.Resolution.HironakaActualCoefficientNonmonomialHistoryOrder
import Hironaka.Blowup.NormalCrossingsComparison
import Hironaka.Invariant.NonmonomialOrderZero
import Hironaka.Invariant.NonmonomialOrderMonomialCanonical

/-! Generic zero nonmonomial order for a single original boundary member.
Blueprint: `hironaka-g8-generic-boundary-monomial.tex`. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8GenericBoundaryMonomial
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  DivisorExponentAlong NormalCrossings NormalCrossingsComparison SimultaneousNormalCrossings
  MonomialCase MonomialCaseAlong NonmonomialOrderLocal
  HironakaSharpOriginalProductTraceOrder HironakaActualCoefficientNonmonomialHistoryOrder
  HironakaG8BoundaryGenericOrder HironakaG8ExceptionalProbeDensity
  HironakaG8ExceptionalProbeFamily HironakaActualMixedTestPowerNormalization
  NonmonomialOrderZero NonmonomialOrderMonomialCanonical MonomialPartAlong
  MarkedIdealBiholomorphism

variable {n k : ℕ} {X : CMfd.{0} n}

/-- The same literal source ideal with only the selected boundary member. -/
def singleBoundary (M : MarkedIdeal n X) (i : Fin M.E.length) : MarkedIdeal n X :=
  ⟨M.N,[M.E.get i],M.ideal,M.d⟩

theorem singleBoundary_isInvDomain (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (hN : M.N = univ) (i : Fin M.E.length) : IsInvDomain k (singleBoundary M i) := by
  have hE : IsSNCDivisor n [M.E.get i] :=
    isSNCDivisor_of_sublist hM.isWellFormed.isSNCDivisor (List.singleton_sublist.mpr (List.get_mem _ _))
  have hT : IsTransverse n M.N [M.E.get i] := by
    rw [hN]
    exact isTransverse_univ_of_isSNCDivisor hE
  exact ⟨⟨hM.isWellFormed.isClosedSubmanifold_N,hM.isWellFormed.isCoherent,hE,hT⟩,
    hM.dimLE,hM.one_le_d,hM.isNonzeroAlongAt⟩

/-- Equality of ordinary order and the selected member exponent forces the
single-boundary nonmonomial order to vanish. -/
theorem singleBoundary_nmOrd_eq_zero (hn : 0 < n) (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (hN : M.N = univ) (i : Fin M.E.length) {y : X} (hy : y ∈ M.E.get i)
    (hord : ordinaryTraceOrder M.N M.ideal y = divExpAlong n M.N M.ideal (M.E.get i) y) :
    nmOrd (singleBoundary M i) y = 0 := by
  let B := singleBoundary M i
  have hB := singleBoundary_isInvDomain M hM hN i
  have hyN : y ∈ B.N := by change y ∈ M.N; rw [hN]; exact mem_univ _
  have hIdx : memberIdx B.E y = {0} := by
    ext a
    rw [mem_memberIdx]
    have hy' : y ∈ M.E[i.val] := by simpa [List.get_eq_getElem] using hy
    simp [B,singleBoundary,hy']
  have hSum : (∑ a ∈ memberIdx B.E y, expDataAlong n B.N B.ideal B.E y a) =
      divExpAlong n M.N M.ideal (M.E.get i) y := by
    rw [hIdx]
    simp [expDataAlong,B,singleBoundary]
  obtain ⟨_,_,hfactor,_⟩ := whole_factor_order hn B hB.isWellFormed hB.isNonzeroAlongAt y hyN
  rw [hSum] at hfactor
  change ordinaryTraceOrder M.N M.ideal y =
    divExpAlong n M.N M.ideal (M.E.get i) y + nmOrd B y at hfactor
  rw [hord] at hfactor
  change nmOrd B y = 0
  omega

/-- Points on the source member with zero nonmonomial order for the literal
single-boundary record are frequent near the chosen source point. -/
theorem frequently_single_boundary_monomial (hn : 0 < n) (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (hN : M.N = univ) (i : Fin M.E.length) {x : X} (hx : x ∈ M.E.get i) :
    ∃ᶠ y in 𝓝 x, y ∈ M.E.get i ∧ nmOrd (singleBoundary M i) y = 0 := by
  have hxN : x ∈ M.N := by rw [hN]; exact mem_univ _
  have hf := frequently_order_eq_divisor_exponent M hM (M.E.get i) hxN hx
  have he := eventually_divExpAlong_get_eq hn hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isSNCDivisor hM.isWellFormed.isTransverse hM.isWellFormed.isCoherent
    hM.isNonzeroAlongAt i hxN hx
  refine (hf.and_eventually he).mono ?_
  intro y ⟨⟨hyN,hyH,hyOrd⟩,hyExp⟩
  refine ⟨hyH,singleBoundary_nmOrd_eq_zero hn M hM hN i hyH ?_⟩
  rw [hyOrd,hyExp hyN hyH]
/-- Every literal probe trace frequently maps to source points where the
original ideal is monomial with respect to the selected single member. -/
theorem original_probe_frequently_source_monomial (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (hN : M.N = univ) (i : Fin M.E.length) (x : X) (hx : x ∈ M.E.get i) (q : ℕ) :
    let s := initialProbeState M i x hx
    let p := probeFamily (Nat.succ_pos n) M hM s q
    ∃ᶠ v in 𝓝 p.point, v ∈ p.F.get p.old ∧ v ∈ p.F.get p.newest ∧
      nmOrd (singleBoundary M i) (baseMap p.H v) = 0 := by
  obtain ⟨F,_,hCard,_⟩ := hM.isWellFormed.isSNCDivisor.2 x
  have hpos : 0 < (F i).card := by rw [hCard i hx]; decide
  obtain ⟨j,_⟩ := Finset.card_pos.mp hpos
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
  let A : Set X := {y | nmOrd (singleBoundary M i) y = 0}
  have hA : ∃ᶠ y in 𝓝 x, y ∈ M.E.get i ∧ y ∈ A :=
    frequently_single_boundary_monomial hn M hM hN i hx
  exact original_probe_lift_frequently M hM i x hx A hA q
/-- At a zero-order source point, the actual singleton-boundary record is
monomial on a genuine open neighbourhood. -/
theorem singleBoundary_monomial_open (hn : 0 < n) (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (hN : M.N = univ) (i : Fin M.E.length) {y : X} (hy : nmOrd (singleBoundary M i) y = 0) :
    ∃ W : Opens X, y ∈ W ∧
      let Q := MarkedIdeal.pullback (Subtype.val : W → X) (singleBoundary M i)
      IsMonomialAlong n Q.N Q.ideal Q.E := by
  let B := singleBoundary M i
  have hB := singleBoundary_isInvDomain M hM hN i
  let W : Opens X := ⟨_,isOpen_compl_cosupport_one hn hB.isWellFormed hB.isNonzeroAlongAt⟩
  have hyW : y ∈ W := notMem_ordGe_one_of_nmOrd_eq_zero hB.isWellFormed hB.isNonzeroAlongAt hy
  exact ⟨W,hyW,isMonomialAlong_pullback_val_compl hn hB.isWellFormed hB.isNonzeroAlongAt⟩

/-- Along every literal probe trace there are frequent points mapping to
source neighbourhoods where the selected singleton-boundary ideal is monomial. -/
theorem original_probe_frequently_monomial_open (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (hN : M.N = univ) (i : Fin M.E.length) (x : X) (hx : x ∈ M.E.get i) (q : ℕ) :
    let s := initialProbeState M i x hx
    let p := probeFamily (Nat.succ_pos n) M hM s q
    ∃ᶠ v in 𝓝 p.point, v ∈ p.F.get p.old ∧ v ∈ p.F.get p.newest ∧
      ∃ W : Opens X, baseMap p.H v ∈ W ∧
        let Q := MarkedIdeal.pullback (Subtype.val : W → X) (singleBoundary M i)
        IsMonomialAlong n Q.N Q.ideal Q.E := by
  obtain ⟨F,_,hCard,_⟩ := hM.isWellFormed.isSNCDivisor.2 x
  have hpos : 0 < (F i).card := by rw [hCard i hx]; decide
  obtain ⟨j,_⟩ := Finset.card_pos.mp hpos
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
  refine (original_probe_frequently_source_monomial M hM hN i x hx q).mono ?_
  intro v hv
  exact ⟨hv.1,hv.2.1,singleBoundary_monomial_open hn M hM hN i hv.2.2⟩
end
end Hironaka.HironakaG8GenericBoundaryMonomial
