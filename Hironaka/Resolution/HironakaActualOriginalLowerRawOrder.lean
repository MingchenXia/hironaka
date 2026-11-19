import Hironaka.Resolution.HironakaActualOriginalLowerChronologicalExponents
import Hironaka.Resolution.HironakaActualCoefficientNonmonomialHistoryOrder
import Hironaka.Resolution.HironakaActualOriginalLowerNormalizedHighCuts
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaActualOriginalLowerRawOrder.Generic
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec DivisorExponentAlong MonomialCaseAlong MonomialCase MonomialInvariant
  MonomialPartAlong NonmonomialOrderLocal GermIdealOrder HironakaSharpOriginalProductTraceOrder
variable {n kA kB : ℕ} {X : CMfd.{0} n}
theorem finite_whole_factor_raw_comparison
    (hn : 0<n) (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : A.N=B.N) (hE : A.E=B.E) (hCos : A.cosupp=B.cosupp)
    (hTotal : ∀ x∈A.cosupp,B.d*ordinaryTraceOrder A.N A.ideal x=A.d*ordinaryTraceOrder B.N B.ideal x)
    (hExp : ∀ (x : X) (i : ℕ),B.d*expDataAlong n A.N A.ideal A.E x i=A.d*expDataAlong n B.N B.ideal B.E x i) :
    (∀ x∈A.cosupp,
      let sA := ∑i∈memberIdx A.E x,expDataAlong n A.N A.ideal A.E x i
      let sB := ∑i∈memberIdx B.E x,expDataAlong n B.N B.ideal B.E x i
      x∈cosupport n A.N A.ideal (sA+nmOrd A x) ∧
      x∉cosupport n A.N A.ideal (sA+nmOrd A x+1) ∧
      x∈cosupport n B.N B.ideal (sB+nmOrd B x) ∧
      x∉cosupport n B.N B.ideal (sB+nmOrd B x+1) ∧
      ordinaryTraceOrder A.N A.ideal x=sA+nmOrd A x ∧
      ordinaryTraceOrder B.N B.ideal x=sB+nmOrd B x ∧
      GermIdealOrder.order n A.N A.ideal x=((sA+nmOrd A x : ℕ) : ℕ∞) ∧
      GermIdealOrder.order n B.N B.ideal x=((sB+nmOrd B x : ℕ) : ℕ∞) ∧
      B.d*sA=A.d*sB ∧ B.d*nmOrd A x=A.d*nmOrd B x) ∧
    (∀ x∉A.N,nmOrd A x=0 ∧ nmOrd B x=0) := by
  refine ⟨?_,?_⟩
  · intro x hx
    have hxB : x∈B.cosupp := hCos ▸ hx
    obtain ⟨hGoodA,hBadA,hNatA,hOrderA⟩ :=
      HironakaActualCoefficientNonmonomialHistoryOrder.whole_factor_order hn A hA.isWellFormed hA.isNonzeroAlongAt x hx.1
    obtain ⟨hGoodB,hBadB,hNatB,hOrderB⟩ :=
      HironakaActualCoefficientNonmonomialHistoryOrder.whole_factor_order hn B hB.isWellFormed hB.isNonzeroAlongAt x hxB.1
    let sA := ∑i∈memberIdx A.E x,expDataAlong n A.N A.ideal A.E x i
    let sB := ∑i∈memberIdx B.E x,expDataAlong n B.N B.ideal B.E x i
    have hSum : B.d*sA=A.d*sB := by
      dsimp only [sA,sB]
      rw [Finset.mul_sum,Finset.mul_sum]
      have hIdx : memberIdx A.E x=memberIdx B.E x := by rw [hE]
      rw [←hIdx]
      exact Finset.sum_congr rfl fun i _ => hExp x i
    have hRaw : B.d*nmOrd A x=A.d*nmOrd B x := by
      have hh := hTotal x hx
      rw [hNatA,hNatB,Nat.mul_add,Nat.mul_add,hSum] at hh
      exact Nat.add_left_cancel hh
    exact ⟨hGoodA,hBadA,hGoodB,hBadB,hNatA,hNatB,hOrderA,hOrderB,hSum,hRaw⟩
  · intro x hx
    have hxB : x∉B.N := by rwa [←hN]
    have hZeroA : nmOrd A x≤0 := nmOrd_le_of_notMem (fun h => hx (ordGe_subset_N A 1 h))
    have hZeroB : nmOrd B x≤0 := nmOrd_le_of_notMem (fun h => hxB (ordGe_subset_N B 1 h))
    exact ⟨Nat.eq_zero_of_le_zero hZeroA,Nat.eq_zero_of_le_zero hZeroB⟩

end Hironaka.HironakaActualOriginalLowerRawOrder.Generic

namespace Hironaka.HironakaActualOriginalLowerRawOrder
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

/-- The raw-order upgrade of one tested local record: from the chronological exponent record of
two native domain records with common carrier and boundary to the same record with the literal
exponent sums, the whole-factor order identities and the normalized raw orders appended. -/
private theorem raw_record {W Y' : CMfd.{0} n} (hn : 0<n) (LJ LK : MarkedIdeal n W) (kk hl : ℕ)
    (R : BlowupTower W Y')
    (hRecord : (geoTransformAlong LJ R).cosupp=(geoTransformAlong LK R).cosupp ∧
    (geoTransformAlong LJ R).N=(geoTransformAlong LK R).N ∧
    (geoTransformAlong LJ R).E=(geoTransformAlong LK R).E ∧
    (geoTransformAlong LJ R).d=LJ.d ∧ (geoTransformAlong LK R).d=LK.d ∧
    (geoTransformAlong LJ R).E.length=hl+R.length ∧
    (geoTransformAlong LK R).E.length=hl+R.length ∧
    let JR:=geoTransformAlong LJ R
    let KR:=geoTransformAlong LK R
    IsInvDomain kk JR ∧ IsInvDomain kk KR ∧
    JR.E=LJ.E.map (strictAlong R) ++ HironakaActualLocalProductHistory.bornBoundaryAlong R ∧
    KR.E=LK.E.map (strictAlong R) ++ HironakaActualLocalProductHistory.bornBoundaryAlong R ∧
    (HironakaActualLocalProductHistory.bornBoundaryAlong R).length=R.length ∧
    (∀ (z : Y') (i : ℕ),KR.d*MonomialCaseAlong.expDataAlong n JR.N JR.ideal JR.E z i =
      JR.d*MonomialCaseAlong.expDataAlong n KR.N KR.ideal KR.E z i) ∧
    (∀ (i : Fin JR.E.length) (z : Y'),
      (z∈JR.N∩JR.E.get i→
        (∃e,¬DivisorExponentAlong.IsDivNearAlong n JR.N JR.ideal (JR.E.get i) (e+1) z) ∧
        (∃e,¬DivisorExponentAlong.IsDivNearAlong n KR.N KR.ideal (JR.E.get i) (e+1) z) ∧
        (∀e,DivisorExponentAlong.IsDivNearAlong n JR.N JR.ideal (JR.E.get i) e z ↔ e≤DivisorExponentAlong.divExpAlong n JR.N JR.ideal (JR.E.get i) z) ∧
        (∀e,DivisorExponentAlong.IsDivNearAlong n KR.N KR.ideal (JR.E.get i) e z ↔ e≤DivisorExponentAlong.divExpAlong n KR.N KR.ideal (JR.E.get i) z)) ∧
      (z∉JR.N∩JR.E.get i→
        (∀e,DivisorExponentAlong.IsDivNearAlong n JR.N JR.ideal (JR.E.get i) e z) ∧
        (∀e,DivisorExponentAlong.IsDivNearAlong n KR.N KR.ideal (JR.E.get i) e z) ∧
        DivisorExponentAlong.divExpAlong n JR.N JR.ideal (JR.E.get i) z=0 ∧
        DivisorExponentAlong.divExpAlong n KR.N KR.ideal (JR.E.get i) z=0)) ∧
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
         ((p*KR.d : ℕ) : ℕ∞) ≤ (q : ℕ∞)*GermIdealOrder.order n KR.N KR.ideal z)) :
    (geoTransformAlong LJ R).cosupp=(geoTransformAlong LK R).cosupp ∧
    (geoTransformAlong LJ R).N=(geoTransformAlong LK R).N ∧
    (geoTransformAlong LJ R).E=(geoTransformAlong LK R).E ∧
    (geoTransformAlong LJ R).d=LJ.d ∧ (geoTransformAlong LK R).d=LK.d ∧
    (geoTransformAlong LJ R).E.length=hl+R.length ∧
    (geoTransformAlong LK R).E.length=hl+R.length ∧
    let JR:=geoTransformAlong LJ R
    let KR:=geoTransformAlong LK R
    IsInvDomain kk JR ∧ IsInvDomain kk KR ∧
    JR.E=LJ.E.map (strictAlong R) ++ HironakaActualLocalProductHistory.bornBoundaryAlong R ∧
    KR.E=LK.E.map (strictAlong R) ++ HironakaActualLocalProductHistory.bornBoundaryAlong R ∧
    (HironakaActualLocalProductHistory.bornBoundaryAlong R).length=R.length ∧
    (∀ (z : Y') (i : ℕ),KR.d*MonomialCaseAlong.expDataAlong n JR.N JR.ideal JR.E z i =
      JR.d*MonomialCaseAlong.expDataAlong n KR.N KR.ideal KR.E z i) ∧
    (∀ (i : Fin JR.E.length) (z : Y'),
      (z∈JR.N∩JR.E.get i→
        (∃e,¬DivisorExponentAlong.IsDivNearAlong n JR.N JR.ideal (JR.E.get i) (e+1) z) ∧
        (∃e,¬DivisorExponentAlong.IsDivNearAlong n KR.N KR.ideal (JR.E.get i) (e+1) z) ∧
        (∀e,DivisorExponentAlong.IsDivNearAlong n JR.N JR.ideal (JR.E.get i) e z ↔ e≤DivisorExponentAlong.divExpAlong n JR.N JR.ideal (JR.E.get i) z) ∧
        (∀e,DivisorExponentAlong.IsDivNearAlong n KR.N KR.ideal (JR.E.get i) e z ↔ e≤DivisorExponentAlong.divExpAlong n KR.N KR.ideal (JR.E.get i) z)) ∧
      (z∉JR.N∩JR.E.get i→
        (∀e,DivisorExponentAlong.IsDivNearAlong n JR.N JR.ideal (JR.E.get i) e z) ∧
        (∀e,DivisorExponentAlong.IsDivNearAlong n KR.N KR.ideal (JR.E.get i) e z) ∧
        DivisorExponentAlong.divExpAlong n JR.N JR.ideal (JR.E.get i) z=0 ∧
        DivisorExponentAlong.divExpAlong n KR.N KR.ideal (JR.E.get i) z=0)) ∧
    (∀ z : Y',z∉JR.N→NonmonomialOrderLocal.nmOrd JR z=0 ∧ NonmonomialOrderLocal.nmOrd KR z=0) ∧
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
      (∀ p q : ℕ, 0<q → q≤p →
        (((p*JR.d : ℕ) : ℕ∞) ≤ (q : ℕ∞)*GermIdealOrder.order n JR.N JR.ideal z ↔
         ((p*KR.d : ℕ) : ℕ∞) ≤ (q : ℕ∞)*GermIdealOrder.order n KR.N KR.ideal z)) ∧
      let sJ := ∑i∈MonomialCase.memberIdx JR.E z,MonomialCaseAlong.expDataAlong n JR.N JR.ideal JR.E z i
      let sK := ∑i∈MonomialCase.memberIdx KR.E z,MonomialCaseAlong.expDataAlong n KR.N KR.ideal KR.E z i
      HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder JR.N JR.ideal z=sJ+NonmonomialOrderLocal.nmOrd JR z ∧
      HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder KR.N KR.ideal z=sK+NonmonomialOrderLocal.nmOrd KR z ∧
      GermIdealOrder.order n JR.N JR.ideal z=((sJ+NonmonomialOrderLocal.nmOrd JR z : ℕ) : ℕ∞) ∧
      GermIdealOrder.order n KR.N KR.ideal z=((sK+NonmonomialOrderLocal.nmOrd KR z : ℕ) : ℕ∞) ∧
      KR.d*sJ=JR.d*sK ∧
      KR.d*NonmonomialOrderLocal.nmOrd JR z=JR.d*NonmonomialOrderLocal.nmOrd KR z := by
  obtain ⟨hCos,hNcur,hEcur,hDJ,hDK,hClockJ,hClockK,hJR,hKR,hWholeJ,hWholeK,hBornLen,hAllExp,hTrace,
    hOldScale,hOldOn,hOldOff,hPoint⟩ := hRecord
  have hRaw := Generic.finite_whole_factor_raw_comparison hn _ _ hJR hKR hNcur hEcur hCos
    (fun z hz => (hPoint z hz).2.2.1) hAllExp
  refine ⟨hCos,hNcur,hEcur,hDJ,hDK,hClockJ,hClockK,hJR,hKR,hWholeJ,hWholeK,hBornLen,hAllExp,hTrace,
    hRaw.2,hOldScale,hOldOn,hOldOff,?_⟩
  intro z hz
  obtain ⟨hFinJ,hFinK,hCross,hCuts⟩ := hPoint z hz
  obtain ⟨_hGoodJ,_hBadJ,_hGoodK,_hBadK,hNatJ,hNatK,hOrderJ,hOrderK,hSum,hRawZ⟩ := hRaw.1 z hz
  exact ⟨hFinJ,hFinK,hCross,hCuts,hNatJ,hNatK,hOrderJ,hOrderK,hSum,hRawZ⟩

theorem original_lower_local_raw_order {A : CMfd.{0} n}
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
                JR.E=LJ.E.map (strictAlong R) ++ HironakaActualLocalProductHistory.bornBoundaryAlong R ∧
                KR.E=LK.E.map (strictAlong R) ++ HironakaActualLocalProductHistory.bornBoundaryAlong R ∧
                (HironakaActualLocalProductHistory.bornBoundaryAlong R).length=R.length ∧
                (∀ (z : Y') (i : ℕ),KR.d*MonomialCaseAlong.expDataAlong n JR.N JR.ideal JR.E z i =
                  JR.d*MonomialCaseAlong.expDataAlong n KR.N KR.ideal KR.E z i) ∧
                (∀ (i : Fin JR.E.length) (z : Y'),
                  (z∈JR.N∩JR.E.get i→
                    (∃e,¬DivisorExponentAlong.IsDivNearAlong n JR.N JR.ideal (JR.E.get i) (e+1) z) ∧
                    (∃e,¬DivisorExponentAlong.IsDivNearAlong n KR.N KR.ideal (JR.E.get i) (e+1) z) ∧
                    (∀e,DivisorExponentAlong.IsDivNearAlong n JR.N JR.ideal (JR.E.get i) e z ↔ e≤DivisorExponentAlong.divExpAlong n JR.N JR.ideal (JR.E.get i) z) ∧
                    (∀e,DivisorExponentAlong.IsDivNearAlong n KR.N KR.ideal (JR.E.get i) e z ↔ e≤DivisorExponentAlong.divExpAlong n KR.N KR.ideal (JR.E.get i) z)) ∧
                  (z∉JR.N∩JR.E.get i→
                    (∀e,DivisorExponentAlong.IsDivNearAlong n JR.N JR.ideal (JR.E.get i) e z) ∧
                    (∀e,DivisorExponentAlong.IsDivNearAlong n KR.N KR.ideal (JR.E.get i) e z) ∧
                    DivisorExponentAlong.divExpAlong n JR.N JR.ideal (JR.E.get i) z=0 ∧
                    DivisorExponentAlong.divExpAlong n KR.N KR.ideal (JR.E.get i) z=0)) ∧
                (∀ z : Y',z∉JR.N→NonmonomialOrderLocal.nmOrd JR z=0 ∧ NonmonomialOrderLocal.nmOrd KR z=0) ∧
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
                  (∀ p q : ℕ, 0<q → q≤p →
                    (((p*JR.d : ℕ) : ℕ∞) ≤ (q : ℕ∞)*GermIdealOrder.order n JR.N JR.ideal z ↔
                     ((p*KR.d : ℕ) : ℕ∞) ≤ (q : ℕ∞)*GermIdealOrder.order n KR.N KR.ideal z)) ∧
                  let sJ := ∑i∈MonomialCase.memberIdx JR.E z,MonomialCaseAlong.expDataAlong n JR.N JR.ideal JR.E z i
                  let sK := ∑i∈MonomialCase.memberIdx KR.E z,MonomialCaseAlong.expDataAlong n KR.N KR.ideal KR.E z i
                  HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder JR.N JR.ideal z=sJ+NonmonomialOrderLocal.nmOrd JR z ∧
                  HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder KR.N KR.ideal z=sK+NonmonomialOrderLocal.nmOrd KR z ∧
                  GermIdealOrder.order n JR.N JR.ideal z=((sJ+NonmonomialOrderLocal.nmOrd JR z : ℕ) : ℕ∞) ∧
                  GermIdealOrder.order n KR.N KR.ideal z=((sK+NonmonomialOrderLocal.nmOrd KR z : ℕ) : ℕ∞) ∧
                  KR.d*sJ=JR.d*sK ∧
                  KR.d*NonmonomialOrderLocal.nmOrd JR z=JR.d*NonmonomialOrderLocal.nmOrd KR z) := by
  obtain ⟨hm,hxU,hJ,hK,hJE,hKE,hJd,hKd,hCommon⟩ :=
    HironakaActualOriginalLowerChronologicalExponents.original_lower_local_chronological_exponents
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
  exact ⟨hTest,fun hRJ => raw_record hn _ _ _ _ R (hRecord hRJ)⟩

end
end Hironaka.HironakaActualOriginalLowerRawOrder
