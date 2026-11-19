import Hironaka.Resolution.HironakaActualPowerBoundaryExponents
import Hironaka.Invariant.NonmonomialTransformAlong

/-! Actual residual input, literal zeroth coefficient summand, and every
initial ordered-boundary exponent. Blueprint FIRST; no history or below-mark
ordinary/coefficient-order comparison is inferred. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualInitialNonmonomialCoefficientBoundary
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan GermIdealOrder IdealWeightPowers DivisorExponentAlong
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec BlowupTowers
  MarkedIdealOperationsAlong HomogenizedIdealAlong CoefficientIdeal
  MonomialPartAlong NonmonomialTransformAlong OrderTaylor
  HironakaActualPowerBoundaryExponents HomogenizedIdealAlongTower GermIdealPullbackCalculus NormalCrossings

variable {n : ℕ} {X : CMfd.{u} n}

private theorem hol {I : GermIdeal n X} (hI : I.IsCoherent) :
    ∀x g,I.mem x g→HolomorphicAt n g x :=
  fun _ _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hI hg

/-- The ENTIRE zeroth ideal-power summand lies in the actual coefficient. -/
theorem zerothPower_le_coefficient (Q : MarkedIdeal n X) (hd : 1≤Q.d) :
    (idealPow Q.ideal (sumExp (fun j=>Q.d-j) Q.d 0)).Le (coeffMarkedAlong Q).ideal := by
  intro x g hg
  have hZero : (idealPow (derivMarkedAlong Q 0).ideal
      (sumExp (fun j=>(derivMarkedAlong Q j).d) Q.d 0)).mem x g := by
    simpa only [derivMarkedAlong_zero,derivMarkedAlong_d] using hg
  change IsInSpanAt (n:=n) (fun s=>∃i,i<Q.d ∧
    (idealPow (derivMarkedAlong Q i).ideal
      (sumExp (fun j=>(derivMarkedAlong Q j).d) Q.d i)).mem x s) x g
  exact InvertibleIdealQuotient.isInSpanAt_self ⟨0,hd,hZero⟩ (holomorphicAt_of_mem_idealPow hg)

private theorem zeroth_exp_pos (Q : MarkedIdeal n X) :
    1≤sumExp (fun j=>Q.d-j) Q.d 0 := by
  apply one_le_sumExp
  intro j hj
  omega

/-- Off a closed trace the native exponent is the literal zero default. -/
private theorem off_trace_zero {N H : Set X} {I : GermIdeal n X} {x : X}
    (hTrace : IsClosed (N∩H)) (hx : x∉N∩H) : divExpAlong n N I H x=0 := by
  have hNone : ¬∃q,¬IsDivNearAlong n N I H (q+1) x :=
    fun ⟨q,hq⟩=>hq (isDivNearAlong_of_notMem hTrace hx (q+1))
  simp only [divExpAlong,dif_neg hNone]

/-- A native finite source-zero exponent forces coefficient-zero at every
original boundary position. The actual residual consumer below derives the premise. -/
theorem coefficient_zero_of_source_zero {k : ℕ} (Q : MarkedIdeal n X)
    (hQ : IsInvDomain k Q) (i : Fin Q.E.length) (x : X)
    (hZero : divExpAlong n Q.N Q.ideal (Q.E.get i) x=0) :
    divExpAlong n (coeffMarkedAlong Q).N (coeffMarkedAlong Q).ideal (Q.E.get i) x=0 := by
  let e:=sumExp (fun j=>Q.d-j) Q.d 0
  have hN:=hQ.isWellFormed.isClosedSubmanifold_N
  have hI:=hQ.isWellFormed.isCoherent
  have hC:=isCoherent_coeffMarkedAlong hI hN
  by_cases hx : x∈Q.N∩Q.E.get i
  · obtain ⟨j,hReg⟩:=hN.2 x hx.1
    obtain ⟨r,hr⟩:=exists_isLocalRetraction hReg
    have hP : divExpAlong n Q.N (idealPow Q.ideal e) (Q.E.get i) x=0 := by
      rw [divExpAlong_idealPow hN hI (zeroth_exp_pos Q),hZero,Nat.mul_zero]
    have hNot := not_isDivNearAlong_divExpAlong_succ hr hx.2
      (isNonzeroAlongAt_idealPow hI (hQ.isNonzeroAlongAt x hx.1) e)
      (hol (isCoherent_idealPow hI e))
    rw [hP,zero_add] at hNot
    by_contra hNonzero
    have hLe : 1≤divExpAlong n (coeffMarkedAlong Q).N
        (coeffMarkedAlong Q).ideal (Q.E.get i) x := Nat.one_le_iff_ne_zero.mpr hNonzero
    have hFirst := (isDivNearAlong_divExpAlong (H:=Q.E.get i) (hol hC) x).mono hLe
    apply hNot
    filter_upwards [hFirst] with z hz hzN hzH
    exact ⟨hzN,fun g hg=>(hz hzN hzH).2 g (zerothPower_le_coefficient Q hQ.one_le_d z g hg)⟩
  · exact off_trace_zero (hN.1.inter (hQ.isWellFormed.isSNCDivisor.1 _ (List.get_mem _ _))) hx

/-- The original residual, constructed on the SAME proper carrier/full E. -/
def residualMarked (M : MarkedIdeal n X) : MarkedIdeal n X :=
  ⟨M.N,M.E,nonmonomialPartAlong n M.N M.ideal M.E,M.d⟩

/-- Its native domain is derived from the actual residual construction. -/
theorem residualMarked_isInvDomain (hn : 0<n) {k : ℕ} (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) : IsInvDomain k (residualMarked M) := by
  have hN:=hM.isWellFormed.isClosedSubmanifold_N
  have hE:=hM.isWellFormed.isSNCDivisor
  have hT:=hM.isWellFormed.isTransverse
  have hI:=hM.isWellFormed.isCoherent
  refine ⟨⟨hN,isCoherent_nonmonomialPartAlong hn hN hE hT hI hM.isNonzeroAlongAt,hE,hT⟩,
    hM.dimLE,hM.one_le_d,?_⟩
  intro x hx
  obtain ⟨g,hg,hFreq⟩:=hM.isNonzeroAlongAt x hx
  exact ⟨g,le_nonmonomialPartAlong_self hI x g hg,hFreq⟩

private theorem boundary_zero_of_nondivisor {N : Set X} {E : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E) (hT : IsTransverse n N E)
    {J : GermIdeal n X} (hJ : J.IsCoherent)
    (hnd : ∀y∈N,∀i : Fin E.length,y∈E.get i→∃g,J.mem y g ∧
      ¬IsInSpanOnAt (n:=n) N ((vanishingIdeal (n:=n) (E.get i)).mem y) y g)
    (i : Fin E.length) (x : X) : divExpAlong n N J (E.get i) x=0 := by
  by_cases hx : x∈N∩E.get i
  · obtain ⟨g,hg,hNot⟩:=hnd x hx.1 i hx.2
    by_contra hNonzero
    have hLe : 1≤divExpAlong n N J (E.get i) x:=Nat.one_le_iff_ne_zero.mpr hNonzero
    have hFirst := (isDivNearAlong_divExpAlong (H:=E.get i) (hol hJ) x).mono hLe
    apply hNot
    apply (MemberTraceIdealAlong.isInSpanOnAt_vanishingIdeal_iff_mem hE hT hx.1 i (hol hJ _ _ hg)).mpr
    refine ⟨hol hJ _ _ hg,?_⟩
    filter_upwards [HadamardBridge.eventually_mem_of_isCoherent hJ hg,hFirst] with z hzMem hzDiv hzTrace
    exact (vanishesToOrderOn_one_iff hzTrace.1 (hol hJ _ _ hzMem)).mp
      ((hzDiv hzTrace.1 hzTrace.2).2 g hzMem)
  · exact off_trace_zero (hN.1.inter (hE.1 _ (List.get_mem _ _))) hx

/-- EVERY original residual exponent is produced as zero from the actual
nondivisor witness, with native off-trace/default cases retained. -/
theorem residual_boundary_zero (hn : 0<n) {k : ℕ} (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (i : Fin M.E.length) (x : X) :
    divExpAlong n (residualMarked M).N (residualMarked M).ideal (M.E.get i) x=0 := by
  have hN:=hM.isWellFormed.isClosedSubmanifold_N
  have hE:=hM.isWellFormed.isSNCDivisor
  have hT:=hM.isWellFormed.isTransverse
  have hI:=hM.isWellFormed.isCoherent
  exact boundary_zero_of_nondivisor hN hE hT
    (isCoherent_nonmonomialPartAlong hn hN hE hT hI hM.isNonzeroAlongAt)
    (fun _ hy _ hyi=>exists_mem_nonmonomialPartAlong_not hn hN hE hT hI hM.isNonzeroAlongAt hy hyi) i x

/-- The actual coefficient's native domain; nonzero germs enter through
the WHOLE zeroth summand, without a supplied coefficient-domain packet. -/
theorem coefficient_isInvDomain {k : ℕ} (Q : MarkedIdeal n X) (hQ : IsInvDomain k Q) :
    IsInvDomain k (coeffMarkedAlong Q) where
  isWellFormed := {
    isClosedSubmanifold_N:=hQ.isWellFormed.isClosedSubmanifold_N
    isCoherent:=isCoherent_coeffMarkedAlong hQ.isWellFormed.isCoherent hQ.isWellFormed.isClosedSubmanifold_N
    isSNCDivisor:=hQ.isWellFormed.isSNCDivisor
    isTransverse:=hQ.isWellFormed.isTransverse }
  dimLE:=hQ.dimLE
  one_le_d:=by
    change 1≤(Finset.range Q.d).prod (fun j=>(derivMarkedAlong Q j).d)
    have hPos : 0<(Finset.range Q.d).prod (fun j=>(derivMarkedAlong Q j).d) := by
      apply Finset.prod_pos
      intro j hj
      rw [derivMarkedAlong_d]
      have hlt:=Finset.mem_range.mp hj
      omega
    omega
  isNonzeroAlongAt:=by
    intro x hx
    obtain ⟨g,hg,hFreq⟩:=isNonzeroAlongAt_idealPow hQ.isWellFormed.isCoherent
      (hQ.isNonzeroAlongAt x hx) (sumExp (fun j=>Q.d-j) Q.d 0)
    exact ⟨g,zerothPower_le_coefficient Q hQ.one_le_d x g hg,hFreq⟩

/-- An ordinary native source supplies the actual residual and coefficient
domains and ALL original boundary exponents. No exponent equality is an input. -/
theorem residual_coefficient_initial_boundary_data (hn : 0<n) {k : ℕ}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) :
    let R:=residualMarked M
    let B:=coeffMarkedAlong R
    let e:=sumExp (fun j=>M.d-j) M.d 0
    IsInvDomain k R ∧ IsInvDomain k B ∧
      R.N=M.N ∧ R.E=M.E ∧ R.d=M.d ∧ B.N=M.N ∧ B.E=M.E ∧ B.d=M.d*e ∧
      ∀i : Fin M.E.length,∀x,
        divExpAlong n R.N R.ideal (M.E.get i) x=0 ∧
        divExpAlong n B.N B.ideal (M.E.get i) x=0 ∧
        divExpAlong n B.N B.ideal (M.E.get i) x=
          e*divExpAlong n R.N R.ideal (M.E.get i) x := by
  let R:=residualMarked M
  let e:=sumExp (fun j=>M.d-j) M.d 0
  have hR:=residualMarked_isInvDomain hn M hM
  have hMark : (coeffMarkedAlong R).d=M.d*e := by
    have h:=mul_sumExp (fun j=>(derivMarkedAlong R j).d) (show 0<R.d from hR.one_le_d)
    simpa only [coeffMarkedAlong,msum,derivMarkedAlong_d,R,residualMarked,e,Nat.sub_zero] using h.symm
  refine ⟨hR,coefficient_isInvDomain R hR,rfl,rfl,rfl,rfl,rfl,hMark,?_⟩
  intro i x
  have hZero:=residual_boundary_zero hn M hM i x
  have hCoeff : divExpAlong n (coeffMarkedAlong (residualMarked M)).N
      (coeffMarkedAlong (residualMarked M)).ideal (M.E.get i) x=0 :=
    coefficient_zero_of_source_zero R hR i x hZero
  exact ⟨hZero,hCoeff,by rw [hCoeff,hZero,Nat.mul_zero]⟩

end
end Hironaka.HironakaActualInitialNonmonomialCoefficientBoundary
