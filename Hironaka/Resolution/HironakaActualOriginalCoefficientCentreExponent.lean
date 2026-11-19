import Hironaka.Resolution.HironakaActualOriginalCoefficientHistoryAlong
import Hironaka.Invariant.InvDomainTowerAlong

/-! Exact exponent of the ORIGINAL coefficient transform along an actual
admissible next centre. Blueprint FIRST. No born-factor or raw nmOrd claim. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualOriginalCoefficientCentreExponent
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  DivisorExponentAlong GermIdealOrder IdealWeightPowers MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms ResolutionInvariantSpec InvDomainTowerAlong
  HomogenizedIdealAlong HomogenizedIdealAlongTower CoefficientIdeal
  MarkedIdealRestrictOpen HironakaActualOriginalCoefficientHistoryAlong

variable {n : ℕ} {X : CMfd.{0} n}

private theorem hol {I : GermIdeal n X} (hI : I.IsCoherent) :
    ∀x f,I.mem x f→HolomorphicAt n f x :=
  fun _ _ hf=>RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hf

private theorem exponent_of_orders (N C : Set X) (A B : GermIdeal n X)
    (hA : ∀y f,A.mem y f→HolomorphicAt n f y)
    (hB : ∀y f,B.mem y f→HolomorphicAt n f y)
    (x : X) (r : X→X) (hr : IsLocalRetraction n N r x) (hx : x∈C)
    (hne : IsNonzeroAlongAt N A x) (e : ℕ)
    (hOrder : ∀y,y∈N→y∈C→GermIdealOrder.order n N B y=
      (e : ℕ∞)*GermIdealOrder.order n N A y) :
    divExpAlong n N B C x=e*divExpAlong n N A C x := by
  let a:=divExpAlong n N A C x
  have hSource : IsDivNearAlong n N A C a x:=isDivNearAlong_divExpAlong hA x
  have hSourceNot : ¬IsDivNearAlong n N A C (a+1) x:=
    not_isDivNearAlong_divExpAlong_succ hr hx hne hA
  have hLower : IsDivNearAlong n N B C (e*a) x := by
    filter_upwards [hSource] with y hy hyN hyC
    refine ⟨hyN,(le_order_iff (hB y)).mp ?_⟩
    have hLe : (a : ℕ∞)≤GermIdealOrder.order n N A y:=
      (le_order_iff (hA y)).mpr (hy hyN hyC).2
    rw [hOrder y hyN hyC]
    have hMul : (e : ℕ∞)*(a : ℕ∞)≤(e : ℕ∞)*GermIdealOrder.order n N A y:=by gcongr
    simpa only [Nat.cast_mul] using hMul
  have hNot : ¬IsDivNearAlong n N B C (e*a+1) x := by
    intro hHigh
    apply hSourceNot
    filter_upwards [hHigh] with y hy hyN hyC
    refine ⟨hyN,(le_order_iff (hA y)).mp ?_⟩
    by_contra hBad
    have hUpper : GermIdealOrder.order n N A y≤(a : ℕ∞):=
      ENat.lt_natCast_add_one_iff.mp (lt_of_not_ge (by
        simpa only [Nat.cast_add,Nat.cast_one] using hBad))
    have hAt : ((e*a+1 : ℕ) : ℕ∞)≤GermIdealOrder.order n N B y:=
      (le_order_iff (hB y)).mpr (hy hyN hyC).2
    rw [hOrder y hyN hyC] at hAt
    have hMul : (e : ℕ∞)*GermIdealOrder.order n N A y≤(e : ℕ∞)*(a : ℕ∞):=by gcongr
    have hImpossible : ((e*a+1 : ℕ) : ℕ∞)≤((e*a : ℕ) : ℕ∞):=
      hAt.trans (by simpa only [Nat.cast_mul] using hMul)
    have hNat : e*a+1≤e*a:=by exact_mod_cast hImpossible
    omega
  have hExists : ∃q,¬IsDivNearAlong n N B C (q+1) x:=⟨e*a,hNot⟩
  change divExpAlong n N B C x=e*a
  unfold divExpAlong
  rw [dif_pos hExists]
  apply Nat.le_antisymm (Nat.find_min' hExists hNot)
  by_contra hBad
  exact Nat.find_spec hExists (hLower.mono (by omega))

/-- Exact exponent of the ORIGINAL coefficient transform at the actual next
admissible centre. The original proper carrier and entire history are retained. -/
theorem original_coefficient_history_centre_exponent (Q : MarkedIdeal n X)
    {k : ℕ} (hQ : IsInvDomain k Q) {Y : CMfd.{0} n}
    (T : BlowupTower X Y) (hT : IsGeoTestTower Q T) (C : Set Y)
    (hC : (geoTransformAlong Q T).IsAdmissibleCentre C) (x : Y) (hx : x∈C) :
    let e:=sumExp (fun j=>Q.d-j) Q.d 0
    divExpAlong n (geoTransformAlong Q T).N (geoTransformAlong (coeffMarkedAlong Q) T).ideal C x=
      e*divExpAlong n (geoTransformAlong Q T).N (geoTransformAlong Q T).ideal C x := by
  let e:=sumExp (fun j=>Q.d-j) Q.d 0
  have hCurrent:=isInvDomain_geoTransformAlong hQ T hT
  have hNC:=hQ.isWellFormed.isClosedSubmanifold_N
  have hIC:=hQ.isWellFormed.isCoherent
  have hCoeffTest:=(coeffAlong_tower Q hNC hIC hQ.one_le_d T).1.mpr hT
  have hB:=(isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
    (𝔪:=coeffMarkedAlong Q) hNC (isCoherent_coeffMarkedAlong hIC hNC) T hCoeffTest).2
  have hxN : x∈(geoTransformAlong Q T).N:=hC.subset_N hx
  obtain ⟨m,hm⟩:=hCurrent.isWellFormed.isClosedSubmanifold_N.2 x hxN
  obtain ⟨r,hr⟩:=exists_isLocalRetraction hm
  exact exponent_of_orders (geoTransformAlong Q T).N C (geoTransformAlong Q T).ideal
    (geoTransformAlong (coeffMarkedAlong Q) T).ideal (hol hCurrent.isWellFormed.isCoherent)
    (hol hB) x r hr hx (hCurrent.isNonzeroAlongAt x hxN) e fun y _hyN hyC=>
      original_coefficient_history_order_along Q hNC hIC hQ.one_le_d T hT y (hC.2.1 hyC)

end
end Hironaka.HironakaActualOriginalCoefficientCentreExponent
