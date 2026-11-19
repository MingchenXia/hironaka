import Hironaka.Resolution.HironakaActualProjectedNormalizedOrderDetection
import Hironaka.Resolution.HironakaActualOriginalLowerHeadProjectionTests
import Hironaka.Resolution.HironakaActualLocalProductHistory

/-! ORIGINAL head records and arbitrary future LOCAL controlled tests.
Blueprint FIRST. Original coefficient/hom transforms remain on the left;
current coefficient/hom records are auxiliary comparison bounds only. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualOriginalLowerNormalizedHighCuts
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

/-- Positive finite cross products preserve all rational cut inequalities. -/
theorem finite_cross_product_cuts (a b u v : ℕ) (ha : 0<a) (hb : 0<b)
    (h : b*u=a*v) (p q : ℕ) : p*a≤q*u ↔ p*b≤q*v := by
  constructor
  · intro hcut
    have hs := Nat.mul_le_mul_left b hcut
    have hq := congrArg (fun t : ℕ => q*t) h
    have he : b*(q*u)=a*(q*v) := by nlinarith only [hq]
    rw [he] at hs
    have hs' : a*(p*b)≤a*(q*v) := by simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hs
    exact Nat.le_of_mul_le_mul_left hs' ha
  · intro hcut
    have hs := Nat.mul_le_mul_left a hcut
    have hq := congrArg (fun t : ℕ => q*t) h
    have he : a*(q*v)=b*(q*u) := by nlinarith only [hq]
    rw [he] at hs
    have hs' : b*(p*a)≤b*(q*u) := by simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hs
    exact Nat.le_of_mul_le_mul_left hs' hb

theorem original_lower_local_normalized_high_cuts {A : CMfd.{0} n}
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
                ∀ z : Y', z∈JR.cosupp →
                  HironakaActualProjectedNormalizedOrderDetection.OriginalFiniteOrderOutput JR z ∧
                  HironakaActualProjectedNormalizedOrderDetection.OriginalFiniteOrderOutput KR z ∧
                  KR.d*HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder JR.N JR.ideal z =
                    JR.d*HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder KR.N KR.ideal z ∧
                  ∀ p q : ℕ, 0<q → q≤p →
                    (((p*JR.d : ℕ) : ℕ∞) ≤ (q : ℕ∞)*GermIdealOrder.order n JR.N JR.ideal z ↔
                     ((p*KR.d : ℕ) : ℕ∞) ≤ (q : ℕ∞)*GermIdealOrder.order n KR.N KR.ideal z)) := by
  obtain ⟨hm,hxU,hJ,hK,hJE,hKE,hJd,hKd,hCommon⟩ :=
    HironakaActualOriginalLowerHeadProjectionTests.original_lower_head_projection_tests
      hn Q hQ hN hE hMax Z hZ hSing a ha
  refine ⟨hm,hxU,hJ,hK,hJE,hKE,hJd,hKd,?_⟩
  intro Y H hHJ
  obtain ⟨hHK,hStage⟩ := hCommon H hHJ
  refine ⟨hHK,?_⟩
  intro y hy hOut
  obtain ⟨hyO,hLJ,hLK,hOwn,hLN,hLE,hLJd,hLKd,hLJLen,hLKLen,hProjected,hLocal⟩ := hStage y hy hOut
  refine ⟨hyO,hLJ,hLK,hOwn,hLN,hLE,hLJd,hLKd,hLJLen,hLKLen,?_⟩
  intro Y' R
  obtain ⟨hTest,hRecord⟩ := hLocal R
  refine ⟨hTest,?_⟩
  intro hRJ
  have hRK := hTest.mp hRJ
  obtain ⟨hCos,hNcur,hEcur,hDJ,hDK,hClockJ,hClockK⟩ := hRecord hRJ
  have hJR := isInvDomain_geoTransformAlong hLJ R hRJ
  have hKR := isInvDomain_geoTransformAlong hLK R hRK
  have hCurrent := HironakaActualLocalProductHistory.current_projected_wEquiv _ _
    hLJ.isWellFormed hLK.isWellFormed hProjected R hRJ hRK
  refine ⟨hCos,hNcur,hEcur,hDJ,hDK,hClockJ,hClockK,hJR,hKR,?_⟩
  intro z hz
  obtain ⟨hFinJ,hFinK,hCross⟩ :=
    HironakaActualProjectedNormalizedOrderDetection.normalized_ordinary_order_of_projected_wEquiv
      _ _ hJR hKR z hz (hCos ▸ hz) hNcur.symm hEcur.symm hCurrent
  refine ⟨hFinJ,hFinK,hCross,?_⟩
  intro p q _hq _hpq
  rw [hFinJ.2.1,hFinK.2.1]
  have hNat := finite_cross_product_cuts _ _ _ _
    (by have := hJR.one_le_d; omega) (by have := hKR.one_le_d; omega) hCross p q
  exact_mod_cast hNat

end
end Hironaka.HironakaActualOriginalLowerNormalizedHighCuts
