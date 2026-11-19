import Hironaka.Resolution.HironakaG8GenericBoundaryMonomial
import Hironaka.Resolution.HironakaG8MixedBoundaryExponents

/-! Generic local monomiality with the full original ordered boundary.
Blueprint: `hironaka-g8-generic-full-monomial.tex`. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8GenericFullMonomial
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  DivisorExponentAlong MonomialCase MonomialCaseAlong NonmonomialOrderLocal
  HironakaSharpOriginalProductTraceOrder HironakaActualCoefficientNonmonomialHistoryOrder
  HironakaG8BoundaryGenericOrder HironakaG8ExceptionalProbeDensity
  HironakaG8ExceptionalProbeFamily HironakaActualMixedTestPowerNormalization
  NonmonomialOrderZero NonmonomialOrderMonomialCanonical MonomialPartAlong
  MarkedIdealBiholomorphism HironakaG8MixedBoundaryExponents

variable {n k : ℕ} {X : CMfd.{0} n}

/-- If the full source order is already one member's exponent, its entire
nonmonomial order vanishes, even in the presence of the full boundary. -/
theorem full_nmOrd_zero_of_order_eq_member (hn : 0 < n) (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (i : Fin M.E.length) {y : X} (hyN : y ∈ M.N)
    (hyH : y ∈ M.E.get i)
    (hord : ordinaryTraceOrder M.N M.ideal y = divExpAlong n M.N M.ideal (M.E.get i) y) :
    nmOrd M y = 0 := by
  have hi : i.val ∈ memberIdx M.E y := (mem_memberIdx M.E).mpr ⟨i.isLt,hyH⟩
  have hle := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
    (f := expDataAlong n M.N M.ideal M.E y)
  have hle' : divExpAlong n M.N M.ideal (M.E.get i) y ≤
      ∑ a ∈ memberIdx M.E y, expDataAlong n M.N M.ideal M.E y a := by
    simpa [expDataAlong,i.isLt] using hle
  obtain ⟨_,_,hfactor,_⟩ := whole_factor_order hn M hM.isWellFormed hM.isNonzeroAlongAt y hyN
  rw [hord] at hfactor
  omega

/-- If the entire order is already contributed by one member, any other
boundary member through that point has exponent zero. -/
theorem other_exp_zero_of_order_eq_member (hn : 0 < n) (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (i j : Fin M.E.length) (hij : i ≠ j) {y : X}
    (hyN : y ∈ M.N) (hyi : y ∈ M.E.get i) (hyj : y ∈ M.E.get j)
    (hord : ordinaryTraceOrder M.N M.ideal y = divExpAlong n M.N M.ideal (M.E.get i) y) :
    divExpAlong n M.N M.ideal (M.E.get j) y = 0 := by
  have hi : i.val ∈ memberIdx M.E y := (mem_memberIdx M.E).mpr ⟨i.isLt,hyi⟩
  have hj : j.val ∈ memberIdx M.E y := (mem_memberIdx M.E).mpr ⟨j.isLt,hyj⟩
  have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hsub : ({i.val,j.val} : Finset ℕ) ⊆ memberIdx M.E y := by
    intro t ht
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact hi
    · exact hj
  have hs := Finset.sum_le_sum_of_subset (f := expDataAlong n M.N M.ideal M.E y) hsub
  have hsum : divExpAlong n M.N M.ideal (M.E.get i) y +
      divExpAlong n M.N M.ideal (M.E.get j) y ≤
      ∑ t ∈ memberIdx M.E y, expDataAlong n M.N M.ideal M.E y t := by
    simpa [Finset.sum_insert,hval,expDataAlong,i.isLt,j.isLt] using hs
  obtain ⟨_,_,hfactor,_⟩ := whole_factor_order hn M hM.isWellFormed hM.isNonzeroAlongAt y hyN
  rw [hord] at hfactor
  omega

/-- Such full-boundary zero-order points are frequent along the selected
source member, without deleting any other source boundary slots. -/
theorem frequently_full_boundary_monomial (hn : 0 < n) (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (i : Fin M.E.length) {x : X} (hxN : x ∈ M.N)
    (hx : x ∈ M.E.get i) : ∃ᶠ y in 𝓝 x, y ∈ M.E.get i ∧ nmOrd M y = 0 := by
  have hf := frequently_order_eq_divisor_exponent M hM (M.E.get i) hxN hx
  have he := eventually_divExpAlong_get_eq hn hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isSNCDivisor hM.isWellFormed.isTransverse hM.isWellFormed.isCoherent
    hM.isNonzeroAlongAt i hxN hx
  refine (hf.and_eventually he).mono ?_
  intro y ⟨⟨hyN,hyH,hyOrd⟩,hyExp⟩
  refine ⟨hyH,full_nmOrd_zero_of_order_eq_member hn M hM i hyN hyH ?_⟩
  rw [hyOrd,hyExp hyN hyH]

/-- The full source exponent profile is generically supported on the
selected member alone, with its original exponent. -/
theorem frequently_full_boundary_profile (hn : 0 < n) (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (i : Fin M.E.length) {x : X} (hxN : x ∈ M.N)
    (hx : x ∈ M.E.get i) : ∃ᶠ y in 𝓝 x, y ∈ M.E.get i ∧ nmOrd M y = 0 ∧
      divExpAlong n M.N M.ideal (M.E.get i) y = divExpAlong n M.N M.ideal (M.E.get i) x ∧
      ∀ j : Fin M.E.length, j ≠ i → divExpAlong n M.N M.ideal (M.E.get j) y = 0 := by
  have hf := frequently_order_eq_divisor_exponent M hM (M.E.get i) hxN hx
  have he := eventually_divExpAlong_get_eq hn hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isSNCDivisor hM.isWellFormed.isTransverse hM.isWellFormed.isCoherent
    hM.isNonzeroAlongAt i hxN hx
  refine (hf.and_eventually he).mono ?_
  intro y ⟨⟨hyN,hyH,hyOrd⟩,hyExp⟩
  have hEq : ordinaryTraceOrder M.N M.ideal y = divExpAlong n M.N M.ideal (M.E.get i) y := by
    rw [hyOrd,hyExp hyN hyH]
  refine ⟨hyH,full_nmOrd_zero_of_order_eq_member hn M hM i hyN hyH hEq,hyExp hyN hyH,?_⟩
  intro j hji
  by_cases hyj : y ∈ M.E.get j
  · exact other_exp_zero_of_order_eq_member hn M hM i j hji.symm hyN hyH hyj hEq
  · have hc : IsClosed (M.N ∩ M.E.get j) := hM.isWellFormed.isClosedSubmanifold_N.1.inter
      (hM.isWellFormed.isSNCDivisor.1 _ (List.get_mem _ _))
    exact divExpAlong_eq_zero_of_notMem hc (fun h => hyj h.2)

/-- Every actual pointed probe double trace frequently maps to a source
point with a genuine open neighbourhood where the full source record is monomial. -/
theorem original_probe_frequently_full_monomial_open (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (hN : M.N = univ) (i : Fin M.E.length) (x : X) (hx : x ∈ M.E.get i) (q : ℕ) :
    let s := initialProbeState M i x hx
    let p := probeFamily (Nat.succ_pos n) M hM s q
    ∃ᶠ v in 𝓝 p.point, v ∈ p.F.get p.old ∧ v ∈ p.F.get p.newest ∧
      ∃ W : Opens X, baseMap p.H v ∈ W ∧
        let Q := MarkedIdeal.pullback (Subtype.val : W → X) M
        IsMonomialAlong n Q.N Q.ideal Q.E := by
  obtain ⟨F,_,hCard,_⟩ := hM.isWellFormed.isSNCDivisor.2 x
  have hpos : 0 < (F i).card := by rw [hCard i hx]; decide
  obtain ⟨j,_⟩ := Finset.card_pos.mp hpos
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
  have hxN : x ∈ M.N := by rw [hN]; exact mem_univ _
  let A : Set X := {y | nmOrd M y = 0}
  have hA : ∃ᶠ y in 𝓝 x, y ∈ M.E.get i ∧ y ∈ A :=
    frequently_full_boundary_monomial hn M hM i hxN hx
  refine (original_probe_lift_frequently M hM i x hx A hA q).mono ?_
  intro v hv
  have hzero : nmOrd M (baseMap (probeFamily (Nat.succ_pos n) M hM (initialProbeState M i x hx) q).H v) = 0 := hv.2.2
  let W : Opens X := ⟨_,isOpen_compl_cosupport_one hn hM.isWellFormed hM.isNonzeroAlongAt⟩
  have hvW : _ ∈ W := notMem_ordGe_one_of_nmOrd_eq_zero hM.isWellFormed hM.isNonzeroAlongAt hzero
  exact ⟨hv.1,hv.2.1,W,hvW,isMonomialAlong_pullback_val_compl hn hM.isWellFormed hM.isNonzeroAlongAt⟩
/-- The exact full-boundary exponent profile and a genuine monomial open
occur together frequently on every actual pointed probe trace. -/
theorem original_probe_frequently_full_monomial_profile (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (hN : M.N = univ) (i : Fin M.E.length) (x : X) (hx : x ∈ M.E.get i) (q : ℕ) :
    let s := initialProbeState M i x hx
    let p := probeFamily (Nat.succ_pos n) M hM s q
    ∃ᶠ v in 𝓝 p.point, v ∈ p.F.get p.old ∧ v ∈ p.F.get p.newest ∧
      divExpAlong n M.N M.ideal (M.E.get i) (baseMap p.H v) = divExpAlong n M.N M.ideal (M.E.get i) x ∧
      (∀ j : Fin M.E.length, j ≠ i → divExpAlong n M.N M.ideal (M.E.get j) (baseMap p.H v) = 0) ∧
      ∃ W : Opens X, baseMap p.H v ∈ W ∧
        let Q := MarkedIdeal.pullback (Subtype.val : W → X) M
        IsMonomialAlong n Q.N Q.ideal Q.E := by
  obtain ⟨F,_,hCard,_⟩ := hM.isWellFormed.isSNCDivisor.2 x
  have hpos : 0 < (F i).card := by rw [hCard i hx]; decide
  obtain ⟨j,_⟩ := Finset.card_pos.mp hpos
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
  have hxN : x ∈ M.N := by rw [hN]; exact mem_univ _
  let A : Set X := {y | nmOrd M y = 0 ∧
    divExpAlong n M.N M.ideal (M.E.get i) y = divExpAlong n M.N M.ideal (M.E.get i) x ∧
    ∀ j : Fin M.E.length, j ≠ i → divExpAlong n M.N M.ideal (M.E.get j) y = 0}
  have hA : ∃ᶠ y in 𝓝 x, y ∈ M.E.get i ∧ y ∈ A := frequently_full_boundary_profile hn M hM i hxN hx
  refine (original_probe_lift_frequently M hM i x hx A hA q).mono ?_
  intro v hv
  have hzero : nmOrd M (baseMap (probeFamily (Nat.succ_pos n) M hM (initialProbeState M i x hx) q).H v) = 0 := hv.2.2.1
  let W : Opens X := ⟨_,isOpen_compl_cosupport_one hn hM.isWellFormed hM.isNonzeroAlongAt⟩
  have hvW : _ ∈ W := notMem_ordGe_one_of_nmOrd_eq_zero hM.isWellFormed hM.isNonzeroAlongAt hzero
  exact ⟨hv.1,hv.2.1,hv.2.2.2.1,hv.2.2.2.2,W,hvW,
    isMonomialAlong_pullback_val_compl hn hM.isWellFormed hM.isNonzeroAlongAt⟩
end
end Hironaka.HironakaG8GenericFullMonomial
