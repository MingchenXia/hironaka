import Hironaka.Resolution.HironakaActualOriginalInitialCommonMaskExponents
import Hironaka.Resolution.HironakaActualOldDivisorExponentTransport
import Hironaka.Resolution.HironakaActualLocalProductHistory
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualOriginalLowerOldExponents.Generic
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HomogenizedGlueingTower ResolutionInvariantSpec DivisorExponentAlong BlowupStrictSubmanifold InvDomainTowerAlong
  HironakaActualLocalProductHistory HironakaActualOldDivisorExponentTransport
variable {n k : ℕ} {X Y : CMfd.{0} n}
-- Elementary literal list dictionary; all empty slots retained.
private theorem oldBoundaryAlong_eq (E : List (Set X)) :
    {Y : CMfd.{0} n} → (T : BlowupTower X Y) → oldBoundaryAlong E T=E.map (strictAlong T)
  | _,.refl => by simp [oldBoundaryAlong,strictAlong]
  | _,.step T C π hπ => by
    rw [oldBoundaryAlong,oldBoundaryAlong_eq E T,List.map_map]
    rfl

private theorem strict_old_closed (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (i : Fin M.E.length) : {Y : CMfd.{0} n} → (T : BlowupTower X Y) → IsClosed (strictAlong T (M.E.get i))
  | _,.refl => hM.isWellFormed.isSNCDivisor.1 _ (List.get_mem _ _)
  | _,.step _ _ _ _ => isClosed_closure

private theorem old_slot (M : MarkedIdeal n X) (T : BlowupTower X Y) (i : Fin M.E.length) :
    ∃ j : Fin (geoTransformAlong M T).E.length,j.val=i.val ∧
      (geoTransformAlong M T).E.get j=strictAlong T (M.E.get i) := by
  have hD := (source_boundary_dictionary M T).1
  rw [oldBoundaryAlong_eq] at hD
  have hLt : i.val<(geoTransformAlong M T).E.length := by
    rw [hD,List.length_append,List.length_map]
    omega
  let j : Fin (geoTransformAlong M T).E.length := ⟨i.val,hLt⟩
  refine ⟨j,rfl,?_⟩
  simp only [List.get_eq_getElem]
  simp [hD,j,i.isLt]

-- Only the public365 theorem is used at an actual proper strict trace.
private theorem old_trace_transport (M : MarkedIdeal n X) (hM : IsInvDomain k M) :
    {Y : CMfd.{0} n} → (T : BlowupTower X Y) → IsGeoTestTower M T →
    ∀ (i : Fin M.E.length) (z : Y),z∈(geoTransformAlong M T).N→z∈strictAlong T (M.E.get i)→
      divExpAlong n (geoTransformAlong M T).N (geoTransformAlong M T).ideal (strictAlong T (M.E.get i)) z =
        divExpAlong n M.N M.ideal (M.E.get i) (T.proj z)
  | _,.refl,_hT,i,z,_hzN,_hzH => rfl
  | _,.step T C π hπ,hT,i,z,hzN,hzH => by
    obtain ⟨j,_hj,hGet⟩ := old_slot M T i
    have hCurrent := isInvDomain_geoTransformAlong hM T hT.1
    have hzCurrentN : π z∈(geoTransformAlong M T).N :=
      geoStrictTransform_subset_preimage hπ.contMDiff.continuous hCurrent.isWellFormed.isClosedSubmanifold_N.1 hzN
    have hzCurrentH : π z∈strictAlong T (M.E.get i) :=
      geoStrictTransform_subset_preimage hπ.contMDiff.continuous (strict_old_closed M hM i T) hzH
    have hStep := original_history_old_exponent M hM T hT.1 hT.2 hπ j hzN
      (by rw [hGet];exact hzH)
    rw [hGet] at hStep
    exact hStep.trans (old_trace_transport M hM T hT.1 i (π z) hzCurrentN hzCurrentH)

theorem initial_old_strict_trace_exponents
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T) :
    ∀ (i : Fin M.E.length),
      (∀ z : Y,z∈(geoTransformAlong M T).N→z∈strictAlong T (M.E.get i)→
        divExpAlong n (geoTransformAlong M T).N (geoTransformAlong M T).ideal
          (strictAlong T (M.E.get i)) z=divExpAlong n M.N M.ideal (M.E.get i) (T.proj z)) ∧
      (∀ z : Y,z∉(geoTransformAlong M T).N∩strictAlong T (M.E.get i)→
        (∀ e,IsDivNearAlong n (geoTransformAlong M T).N (geoTransformAlong M T).ideal
          (strictAlong T (M.E.get i)) e z) ∧
        divExpAlong n (geoTransformAlong M T).N (geoTransformAlong M T).ideal
          (strictAlong T (M.E.get i)) z=0) := by
  intro i
  refine ⟨old_trace_transport M hM T hT i,?_⟩
  intro z hz
  have hCurrent := isInvDomain_geoTransformAlong hM T hT
  have hClosed := hCurrent.isWellFormed.isClosedSubmanifold_N.1.inter (strict_old_closed M hM i T)
  have hNear : ∀ᶠy in 𝓝 z,y∉(geoTransformAlong M T).N∩strictAlong T (M.E.get i) :=
    hClosed.isOpen_compl.mem_nhds hz
  have hAll (e : ℕ) : IsDivNearAlong n (geoTransformAlong M T).N (geoTransformAlong M T).ideal
      (strictAlong T (M.E.get i)) e z := hNear.mono fun _ hy hyN hyH => (hy ⟨hyN,hyH⟩).elim
  have hNo : ¬∃e,¬IsDivNearAlong n (geoTransformAlong M T).N (geoTransformAlong M T).ideal
      (strictAlong T (M.E.get i)) (e+1) z := by
    rintro ⟨e,he⟩;exact he (hAll (e+1))
  exact ⟨hAll,by simp only [divExpAlong,dif_neg hNo]⟩

private theorem paired_old (A B : MarkedIdeal n X) (hA : IsInvDomain k A) (hB : IsInvDomain k B)
    (hE : A.E=B.E)
    (hInitial : ∀ (D : Set X) (x : X),B.d*divExpAlong n A.N A.ideal D x=A.d*divExpAlong n B.N B.ideal D x)
    (T : BlowupTower X Y) (hTA : IsGeoTestTower A T) (hTB : IsGeoTestTower B T)
    (hN : (geoTransformAlong A T).N=(geoTransformAlong B T).N) :
    let AR := geoTransformAlong A T
    let BR := geoTransformAlong B T
    (∀ (i : Fin A.E.length) (z : Y),BR.d*divExpAlong n AR.N AR.ideal (strictAlong T (A.E.get i)) z=
      AR.d*divExpAlong n BR.N BR.ideal (strictAlong T (A.E.get i)) z) ∧
    (∀ (i : Fin A.E.length) (z : Y),z∈AR.N→z∈strictAlong T (A.E.get i)→
      divExpAlong n AR.N AR.ideal (strictAlong T (A.E.get i)) z=divExpAlong n A.N A.ideal (A.E.get i) (T.proj z) ∧
      divExpAlong n BR.N BR.ideal (strictAlong T (A.E.get i)) z=divExpAlong n B.N B.ideal (A.E.get i) (T.proj z)) ∧
    (∀ (i : Fin A.E.length) (z : Y),z∉AR.N∩strictAlong T (A.E.get i)→
      (∀e,IsDivNearAlong n AR.N AR.ideal (strictAlong T (A.E.get i)) e z) ∧
      (∀e,IsDivNearAlong n BR.N BR.ideal (strictAlong T (A.E.get i)) e z) ∧
      divExpAlong n AR.N AR.ideal (strictAlong T (A.E.get i)) z=0 ∧
      divExpAlong n BR.N BR.ideal (strictAlong T (A.E.get i)) z=0) := by
  let AR := geoTransformAlong A T
  let BR := geoTransformAlong B T
  have hOn : ∀ (i : Fin A.E.length) (z : Y),z∈AR.N→z∈strictAlong T (A.E.get i)→
      divExpAlong n AR.N AR.ideal (strictAlong T (A.E.get i)) z=divExpAlong n A.N A.ideal (A.E.get i) (T.proj z) ∧
      divExpAlong n BR.N BR.ideal (strictAlong T (A.E.get i)) z=divExpAlong n B.N B.ideal (A.E.get i) (T.proj z) := by
    intro i z hzN hzH
    let j : Fin B.E.length := ⟨i.val,by rw [←hE];exact i.isLt⟩
    have hGet : A.E.get i=B.E.get j := by simpa only [List.get_eq_getElem] using getElem_congr hE rfl i.isLt
    have hBZ := (initial_old_strict_trace_exponents B hB T hTB j).1 z (hN ▸ hzN) (by rw [←hGet];exact hzH)
    rw [←hGet] at hBZ
    exact ⟨(initial_old_strict_trace_exponents A hA T hTA i).1 z hzN hzH,hBZ⟩
  have hOff : ∀ (i : Fin A.E.length) (z : Y),z∉AR.N∩strictAlong T (A.E.get i)→
      (∀e,IsDivNearAlong n AR.N AR.ideal (strictAlong T (A.E.get i)) e z) ∧
      (∀e,IsDivNearAlong n BR.N BR.ideal (strictAlong T (A.E.get i)) e z) ∧
      divExpAlong n AR.N AR.ideal (strictAlong T (A.E.get i)) z=0 ∧
      divExpAlong n BR.N BR.ideal (strictAlong T (A.E.get i)) z=0 := by
    intro i z hz
    let j : Fin B.E.length := ⟨i.val,by rw [←hE];exact i.isLt⟩
    have hGet : A.E.get i=B.E.get j := by simpa only [List.get_eq_getElem] using getElem_congr hE rfl i.isLt
    obtain ⟨hAllA,hZeroA⟩ := (initial_old_strict_trace_exponents A hA T hTA i).2 z hz
    have hzB : z∉BR.N∩strictAlong T (B.E.get j) := by rw [←hGet,←hN];exact hz
    obtain ⟨hAllB,hZeroB⟩ := (initial_old_strict_trace_exponents B hB T hTB j).2 z hzB
    rw [←hGet] at hAllB hZeroB
    exact ⟨hAllA,hAllB,hZeroA,hZeroB⟩
  refine ⟨?_,hOn,hOff⟩
  intro i z
  by_cases hz : z∈AR.N∩strictAlong T (A.E.get i)
  · obtain ⟨hAZ,hBZ⟩ := hOn i z hz.1 hz.2
    rw [hAZ,hBZ,d_geoTransformAlong,d_geoTransformAlong]
    exact hInitial (A.E.get i) (T.proj z)
  · obtain ⟨_hAllA,_hAllB,hZeroA,hZeroB⟩ := hOff i z hz
    rw [hZeroA,hZeroB,Nat.mul_zero,Nat.mul_zero]

end Hironaka.HironakaActualOriginalLowerOldExponents.Generic

namespace Hironaka.HironakaActualOriginalLowerOldExponents
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan IdealWeightPowers GermIdealOrder GermIdealPullbackCalculus IdealOrderArithmetic
  RestrictedIdealWeight RestrictedIdealExtension RestrictLeCalculus
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong
  MarkedIdealOperationsAlong.MarkedIdeal MarkedIdealEquivalence.MarkedIdeal
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower HomogenizedGlueing MarkedIdealBiholomorphism
  HomogenizedIdealAlong HomogenizedIdealAlongTower DerivativeIdealAlong DerivativeIdealAlongCoherent
  CoefficientIdeal CoefficientIdealRestriction TangentDirectionAlong
  ResolutionInvariantSpec InvDomainTowerAlong MarkedIdealRestrictOpen
  HironakaActualPowerBoundaryExponents HironakaActualOriginalPowerTransform
  HironakaActualTrueMarkCoefficientHistorySandwich
  HironakaActualOriginalHistoricalBarWeightedThreshold
  HironakaActualOriginalCoefficientHistoryAlong HironakaActualOriginalTrueMarkMaskCompanions
  HironakaActualOriginalCommonMaskRawOrder
  StepOneValue StepOneValueMasked StepOneLowerDomain ContactStageKept
  CoefficientIdealAlongRestrictionFull HironakaEmbeddedAnalytic
variable {n : ℕ} {X Y : CMfd.{u} n}

theorem original_lower_local_initial_old_exponents {A : CMfd.{0} n}
    (hn : 0<n) (Q : MarkedIdeal n A) {k : ℕ} (hQ : IsInvDomain k Q)
    (hN : Q.N=univ) (hE : Q.E=[]) (hMax : IsMaximalOrderAlong Q.N Q.ideal Q.d)
    (Z : Set A) (hZ : IsComplexAnalyticSubset (n:=n) Z)
    (hSing : Q.cosupp⊆singularSet (n:=n) Z) (a : A) (ha : a∈Q.cosupp) :
    ∃hm : a∈maskB Q (.refl : BlowupTower A A) a,
      let V:=maskB Q (.refl : BlowupTower A A) a
      let L : MarkedIdeal n (CMfd.of (n:=n) V):=lowerMarkedB Q (.refl : BlowupTower A A) a
      let x : V:=⟨a,hm⟩
      let μ:=NonmonomialOrderLocal.nmOrd L x
      let e:=sumExp (fun j=>L.d-j) L.d 0
      let U:=NonmonomialOrderTail.ordMask L μ
      let P : MarkedIdeal n (CMfd.of (n:=n) U):=MarkedIdeal.pullback (Subtype.val : U→V) L
      let B : MarkedIdeal n (CMfd.of (n:=n) U):=MarkedIdeal.pullback (Subtype.val : U→V) (coeffMarkedAlong L)
      let J:=CompanionRebase.companionOf n P μ
      let K:=CompanionRebase.companionOf n B (e*μ)
      ∃_hxU : x∈U,
        IsInvDomain (k-1) J ∧ IsInvDomain (k-1) K ∧ J.E=[] ∧ K.E=[] ∧ J.d=μ ∧ K.d=e*μ ∧
        ∀{Y : CMfd.{0} n}(H : BlowupTower (CMfd.of (n:=n) U) Y),IsGeoTestTower J H→
          IsGeoTestTower K H ∧
          ∀y∈(geoTransformAlong (barMarked K) H).cosupp,
            y∉CodimOneSupportAlong.codimOnePartAlong (geoTransformAlong (barMarked K) H).N
              (geoTransformAlong (barMarked K) H).ideal (geoTransformAlong (barMarked K) H).d→
            y∈maskB K H y ∧
            let O:=maskB K H y
            let LJ:=contactMarkedKept J (tangentChoice K (H.proj y)).2 H O
            let LK:=contactMarkedKept K (tangentChoice K (H.proj y)).2 H O
            IsInvDomain ((k-1)-1) LJ ∧ IsInvDomain ((k-1)-1) LK ∧
            LK=lowerMarkedB K H y ∧ LJ.N=LK.N ∧ LJ.E=LK.E ∧
            LJ.d=(Finset.range ((Finset.range μ).prod (fun j=>μ-j))).prod
              (fun j=>(Finset.range μ).prod (fun j=>μ-j)-j) ∧
            LK.d=(Finset.range ((Finset.range (e*μ)).prod (fun j=>e*μ-j))).prod
              (fun j=>(Finset.range (e*μ)).prod (fun j=>e*μ-j)-j) ∧
            LJ.E.length=H.length ∧ LK.E.length=H.length ∧
            (∀ (D : Set (CMfd.of (n:=n) O)) (z : O),
              LK.d*DivisorExponentAlong.divExpAlong n LJ.N LJ.ideal D z =
                LJ.d*DivisorExponentAlong.divExpAlong n LK.N LK.ideal D z) ∧
            (∀ (z : O) (i : ℕ),
              LK.d*MonomialCaseAlong.expDataAlong n LJ.N LJ.ideal LJ.E z i =
                LJ.d*MonomialCaseAlong.expDataAlong n LK.N LK.ideal LK.E z i) ∧
            ∀{Y' : CMfd.{0} n}(R : BlowupTower (CMfd.of (n:=n) O) Y'),
              (IsGeoTestTower LJ R↔IsGeoTestTower LK R) ∧
              (IsGeoTestTower LJ R→
                (geoTransformAlong LJ R).cosupp=(geoTransformAlong LK R).cosupp ∧
                (geoTransformAlong LJ R).N=(geoTransformAlong LK R).N ∧
                (geoTransformAlong LJ R).E=(geoTransformAlong LK R).E ∧
                (geoTransformAlong LJ R).d=LJ.d ∧ (geoTransformAlong LK R).d=LK.d ∧
                (geoTransformAlong LJ R).E.length=H.length+R.length ∧
                (geoTransformAlong LK R).E.length=H.length+R.length ∧
                let JR:=geoTransformAlong LJ R
                let KR:=geoTransformAlong LK R
                IsInvDomain ((k-1)-1) JR ∧ IsInvDomain ((k-1)-1) KR ∧
                (∀ (i : Fin LJ.E.length) (z : Y'),
                  KR.d*DivisorExponentAlong.divExpAlong n JR.N JR.ideal (strictAlong R (LJ.E.get i)) z =
                    JR.d*DivisorExponentAlong.divExpAlong n KR.N KR.ideal (strictAlong R (LJ.E.get i)) z) ∧
                (∀ (i : Fin LJ.E.length) (z : Y'),z∈JR.N→z∈strictAlong R (LJ.E.get i)→
                  DivisorExponentAlong.divExpAlong n JR.N JR.ideal (strictAlong R (LJ.E.get i)) z =
                    DivisorExponentAlong.divExpAlong n LJ.N LJ.ideal (LJ.E.get i) (R.proj z) ∧
                  DivisorExponentAlong.divExpAlong n KR.N KR.ideal (strictAlong R (LJ.E.get i)) z =
                    DivisorExponentAlong.divExpAlong n LK.N LK.ideal (LJ.E.get i) (R.proj z)) ∧
                (∀ (i : Fin LJ.E.length) (z : Y'),z∉JR.N∩strictAlong R (LJ.E.get i)→
                  (∀ e,DivisorExponentAlong.IsDivNearAlong n JR.N JR.ideal (strictAlong R (LJ.E.get i)) e z) ∧
                  (∀ e,DivisorExponentAlong.IsDivNearAlong n KR.N KR.ideal (strictAlong R (LJ.E.get i)) e z) ∧
                  DivisorExponentAlong.divExpAlong n JR.N JR.ideal (strictAlong R (LJ.E.get i)) z=0 ∧
                  DivisorExponentAlong.divExpAlong n KR.N KR.ideal (strictAlong R (LJ.E.get i)) z=0) ∧
                ∀ z : Y', z∈JR.cosupp →
                  HironakaActualProjectedNormalizedOrderDetection.OriginalFiniteOrderOutput JR z ∧
                  HironakaActualProjectedNormalizedOrderDetection.OriginalFiniteOrderOutput KR z ∧
                  KR.d*HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder JR.N JR.ideal z =
                    JR.d*HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder KR.N KR.ideal z ∧
                  ∀ p q : ℕ, 0<q → q≤p →
                    (((p*JR.d : ℕ) : ℕ∞) ≤ (q : ℕ∞)*GermIdealOrder.order n JR.N JR.ideal z ↔
                     ((p*KR.d : ℕ) : ℕ∞) ≤ (q : ℕ∞)*GermIdealOrder.order n KR.N KR.ideal z)) := by
  obtain ⟨hm,hxU,hJ,hK,hJE,hKE,hJd,hKd,hCommon⟩ :=
    HironakaActualOriginalInitialCommonMaskExponents.original_lower_initial_common_mask_exponents
      hn Q hQ hN hE hMax Z hZ hSing a ha
  refine ⟨hm,hxU,hJ,hK,hJE,hKE,hJd,hKd,?_⟩
  intro Y H hHJ
  obtain ⟨hHK,hStage⟩ := hCommon H hHJ
  refine ⟨hHK,?_⟩
  intro y hy hOut
  obtain ⟨hyO,hLJ,hLK,hOwn,hLN,hLE,hLJd,hLKd,hLJLen,hLKLen,hExp,hData,hLocal⟩ := hStage y hy hOut
  refine ⟨hyO,hLJ,hLK,hOwn,hLN,hLE,hLJd,hLKd,hLJLen,hLKLen,hExp,hData,?_⟩
  intro Y' R
  obtain ⟨hTest,hRecord⟩ := hLocal R
  refine ⟨hTest,?_⟩
  intro hRJ
  obtain ⟨hCos,hNcur,hEcur,hDJ,hDK,hClockJ,hClockK,hJR,hKR,hPoint⟩ := hRecord hRJ
  have hOld := Generic.paired_old _ _ hLJ hLK hLE hExp R hRJ (hTest.mp hRJ) hNcur
  exact ⟨hCos,hNcur,hEcur,hDJ,hDK,hClockJ,hClockK,hJR,hKR,hOld.1,hOld.2.1,hOld.2.2,hPoint⟩

end
end Hironaka.HironakaActualOriginalLowerOldExponents
