import Hironaka.Resolution.HironakaActualOriginalHistoricalBarWeightedThreshold
import Hironaka.MarkedIdeal.CoefficientIdealAlongRestriction

/-! Genuine whole coefficient support gap and native divisor-exponent dichotomy.
Blueprint FIRST: hironaka-actual-coefficient-divisor-exponent-gap.tex.
Native unbounded/default zero is retained; no lower-domain or nonzero packet. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaActualCoefficientDivisorExponentGap
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan GermIdealOrder IdealWeightPowers DivisorExponentAlong
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  HomogenizedIdealAlong CoefficientIdeal CoefficientIdealRestriction CoefficientIdealAlongRestriction
  DerivativeIdealAlong GiraudAlong ContactIndependenceAlong GermIdealPullbackCalculus
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower ContactStageKept
  HironakaActualOriginalHistoricalBarWeightedThreshold ResolutionInvariantSpec

variable {n : ℕ} {X : CMfd.{u} n}

private theorem hol {Y : CMfd.{u} n} {I : GermIdeal n Y} (hI : I.IsCoherent) :
    ∀x f,I.mem x f→HolomorphicAt n f x := fun _ _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem hI hf

/-- Every genuine member of the last derivative contributes its WHOLE positive power. -/
theorem coefficient_restriction_cosupport_gap (M : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent) (hd : 1≤M.d)
    (S : Set X) (hS : S⊆M.N) :
    cosupport n S (coeffMarkedAlong M).ideal 1=
      cosupport n S (coeffMarkedAlong M).ideal (coeffMarkedAlong M).d := by
  apply Subset.antisymm
  · intro x hx
    have hSource : x∈M.cosupp:=by
      have hGiraud:=cosupport_succ_eq_inter_zeroLocus_iterDerivIdealAlong (hol hI) hN.2 (M.d-1)
      rw [Nat.sub_add_cancel hd] at hGiraud
      change x∈cosupport n M.N M.ideal M.d
      rw [hGiraud]
      refine ⟨hS hx.1,?_⟩
      intro g hg
      let p:=sumExp (fun j=>M.d-j) M.d (M.d-1)
      have hp : 1≤p:=one_le_sumExp (fun j hj=>by omega) _
      have hghol:=holomorphicAt_of_mem_iterDerivIdealAlong (hol hI) (M.d-1) x g hg
      have hPower : (idealPow (derivMarkedAlong M (M.d-1)).ideal p).mem x (fun y=>g y^p):=
        OrderMultiplicativity.pow_mem_idealPow hg hghol p
      have hWhole : (coeffMarkedAlong M).ideal.mem x (fun y=>g y^p):=
        (InvertibleIdealQuotient.isInSpanAt_self
          (S:=fun f=>∃i,i<M.d ∧ (idealPow (derivMarkedAlong M i).ideal
            (sumExp (fun j=>(derivMarkedAlong M j).d) M.d i)).mem x f)
          ⟨M.d-1,by omega,hPower⟩ (holomorphicAt_of_mem_idealPow hPower) : IsInSpanAt (n:=n) _ x _)
      have hZero:=(vanishesToOrderOn_one_iff hx.1 (BlowupDerivativeIdeal.holomorphicAt_pow hghol p)).mp
        (hx.2 _ hWhole)
      exact (pow_eq_zero_iff (by omega : p≠0)).mp hZero
    have hCoeff : x∈(coeffMarkedAlong M).cosupp:=by
      rw [cosupp_coeffMarkedAlong hN.2 (hol hI) hd]
      exact hSource
    exact ⟨hx.1,fun g hg=>(hCoeff.2 g hg).mono_set hS⟩
  · exact cosupport_anti (one_le_coeffMarkedAlong_d M)

/- A private logical composition of the ACTUAL nearby-cosupport definition.
The public endpoints derive the gap; no incoming target gap is public. -/
private theorem exponent_gap {N : Set X} {I : GermIdeal n X}
    (hI : ∀x f,I.mem x f→HolomorphicAt n f x) (d : ℕ)
    (hGap : cosupport n N I 1⊆cosupport n N I d) (H : Set X) (x : X) :
    divExpAlong n N I H x=0 ∨ d≤divExpAlong n N I H x := by
  by_cases hEx : ∃e,¬IsDivNearAlong n N I H (e+1) x
  · unfold divExpAlong
    rw [dif_pos hEx]
    by_cases hZero : Nat.find hEx=0
    · exact Or.inl hZero
    · right
      have hDiv:=isDivNearAlong_divExpAlong (N:=N) (H:=H) hI x
      unfold divExpAlong at hDiv
      rw [dif_pos hEx] at hDiv
      have hOne:=hDiv.mono (Nat.one_le_iff_ne_zero.mpr hZero)
      have hHigh : IsDivNearAlong n N I H d x:=by
        filter_upwards [hOne] with y hy hyN hyH
        exact hGap (hy hyN hyH)
      by_contra hSmall
      exact Nat.find_spec hEx (hHigh.mono (by omega))
  · left
    unfold divExpAlong
    rw [dif_neg hEx]

/-- Genuine open restriction, ANY H and every native finite/unbounded/default branch. -/
theorem coefficient_open_divisor_exponent_gap (M : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent) (hd : 1≤M.d)
    (S : Set X) (hS : S⊆M.N) (U : TopologicalSpace.Opens X) (H : Set U) (x : U) :
    let R:=MarkedIdeal.pullback (Subtype.val : U→X) (withN (coeffMarkedAlong M) S)
    divExpAlong n R.N R.ideal H x=0 ∨ R.d≤divExpAlong n R.N R.ideal H x := by
  let C:=coeffMarkedAlong M
  let A:=withN C S
  let A₁ : MarkedIdeal n X:={A with d:=1}
  let R:=MarkedIdeal.pullback (Subtype.val : U→X) A
  have hC : C.ideal.IsCoherent:=isCoherent_coeffMarkedAlong hI hN
  have hR : R.ideal.IsCoherent:=isCoherent_pullback contMDiff_subtype_val hC
  have hGap : cosupport n R.N R.ideal 1=cosupport n R.N R.ideal R.d:=by
    change (MarkedIdeal.pullback (Subtype.val : U→X) A₁).cosupp=
      (MarkedIdeal.pullback (Subtype.val : U→X) A).cosupp
    rw [cosupp_pullback_val A₁ (hol hC) U,cosupp_pullback_val A (hol hC) U]
    exact congrArg (fun V : Set X=>(Subtype.val : U→X) ⁻¹' V)
      (coefficient_restriction_cosupport_gap M hN hI hd S hS)
  exact exponent_gap (X:=CMfd.of (n:=n) U) (N:=R.N) (I:=R.ideal)
    (hol (Y:=CMfd.of (n:=n) U) hR) R.d (le_of_eq hGap) H x

/-- ACTUAL ORIGINAL contact lower ideal, with literal DOUBLE mark and full chronology. -/
theorem original_contact_divisor_exponent_gap {k : ℕ} (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (w : X→ℂ) (U : TopologicalSpace.Opens Y) :
    let R:=contactMarkedKept M w T U
    R.d=(Finset.range ((Finset.range M.d).prod (fun j=>M.d-j))).prod
      (fun j=>(Finset.range M.d).prod (fun j=>M.d-j)-j) ∧
    R.E=(geoTransformAlong M T).E.map ((Subtype.val : U→Y) ⁻¹' ·) ∧
    R.E.length=M.E.length+T.length ∧
    ∀(H : Set U)(x : U),divExpAlong n R.N R.ideal H x=0 ∨ R.d≤divExpAlong n R.N R.ideal H x := by
  let B:=geoTransformAlong (coeffMarkedAlong (homMarkedAlong M)) T
  let S:=strictAlong T (M.N∩{y | w y=0})
  obtain ⟨_hBar,hB,_hBT,hBN,hBE,hBd,hBLen,_hWeighted⟩:=original_bar_weighted_history M hM T hT
  have hS : S⊆B.N:=by
    rw [hBN]
    exact MaximalContactAlongTower.strictAlong_subset_N M (fun _ hy=>hy.1) T
  refine ⟨?_,?_,?_,?_⟩
  · change (Finset.range B.d).prod (fun j=>B.d-j)=_
    rw [hBd]
  · change B.E.map ((Subtype.val : U→Y) ⁻¹' ·)=_
    rw [hBE]
  · change (B.E.map ((Subtype.val : U→Y) ⁻¹' ·)).length=_
    rw [List.length_map]
    exact hBLen
  · intro H x
    exact coefficient_open_divisor_exponent_gap B hB.isWellFormed.isClosedSubmanifold_N
      hB.isWellFormed.isCoherent hB.one_le_d S hS U H x

end
end Hironaka.HironakaActualCoefficientDivisorExponentGap
