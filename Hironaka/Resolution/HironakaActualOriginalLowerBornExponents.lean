import Hironaka.Resolution.HironakaActualOriginalLowerNextCentreExponents
import Hironaka.Resolution.HironakaActualLocalBornExponent
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualOriginalLowerBornExponents.Generic
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences Hironaka.RegularLocusDense
  BlowupStrictSubmanifold
  RelativePrincipalizationSpan BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec DivisorExponentAlong GermIdealOrder InvDomainTowerAlong
  HironakaActualLocalBornExponent
variable {n kA kB : ℕ} {X Y : CMfd.{0} n}
theorem next_born_exponent_comparison
    (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : A.N=B.N) (hE : A.E=B.E) (hCos : A.cosupp=B.cosupp)
    (hCuts : ∀ x∈A.cosupp,∀ p q : ℕ,0<q→q≤p→
      ((((p*A.d : ℕ) : ℕ∞)≤(q : ℕ∞)*GermIdealOrder.order n A.N A.ideal x) ↔
       (((p*B.d : ℕ) : ℕ∞)≤(q : ℕ∞)*GermIdealOrder.order n B.N B.ideal x)))
    (C : Set X) (hC : A.IsAdmissibleCentre C)
    (π : Y→X) (hπ : IsBlowupAlong n C π) :
    let A' := A.geoTransform C π
    let B' := B.geoTransform C π
    let D := π ⁻¹' C
    IsInvDomain kA A' ∧ IsInvDomain kB B' ∧ A'.N=B'.N ∧ A'.E=B'.E ∧
      A'.d=A.d ∧ B'.d=B.d ∧
      A'.E=A.E.map (geoStrictTransform π C) ++ [D] ∧
      B'.E=B.E.map (geoStrictTransform π C) ++ [D] ∧
      (∀ z : Y,B.d*divExpAlong n A'.N A'.ideal D z=A.d*divExpAlong n B'.N B'.ideal D z) ∧
      (∀ z : Y,z∈A'.N→π z∈C→
        A.d≤divExpAlong n A.N A.ideal C (π z) ∧
        B.d≤divExpAlong n B.N B.ideal C (π z) ∧
        divExpAlong n A'.N A'.ideal D z=divExpAlong n A.N A.ideal C (π z)-A.d ∧
        divExpAlong n B'.N B'.ideal D z=divExpAlong n B.N B.ideal C (π z)-B.d ∧
        (∃ e,¬IsDivNearAlong n A'.N A'.ideal D (e+1) z) ∧
        (∃ e,¬IsDivNearAlong n B'.N B'.ideal D (e+1) z) ∧
        (∀ e,IsDivNearAlong n A'.N A'.ideal D e z ↔ e≤divExpAlong n A'.N A'.ideal D z) ∧
        (∀ e,IsDivNearAlong n B'.N B'.ideal D e z ↔ e≤divExpAlong n B'.N B'.ideal D z)) ∧
      (∀ z : Y,z∉A'.N∩D→
        (∀ e,IsDivNearAlong n A'.N A'.ideal D e z) ∧
        (∀ e,IsDivNearAlong n B'.N B'.ideal D e z) ∧
        divExpAlong n A'.N A'.ideal D z=0 ∧ divExpAlong n B'.N B'.ideal D z=0) := by
  obtain ⟨hCB,hCentre,_hCentreOn,_hCentreOff⟩ :=
    HironakaActualOriginalLowerNextCentreExponents.Generic.next_centre_exponent_comparison
      A B hA hB hN hE hCos hCuts C hC
  let A' := A.geoTransform C π
  let B' := B.geoTransform C π
  let D := π ⁻¹' C
  have hTA : IsGeoTestTower A (BlowupTower.step .refl C π hπ) := ⟨trivial,hC⟩
  have hTB : IsGeoTestTower B (BlowupTower.step .refl C π hπ) := ⟨trivial,hCB⟩
  have hNextA := isInvDomain_geoTransformAlong hA _ hTA
  have hNextB := isInvDomain_geoTransformAlong hB _ hTB
  change IsInvDomain kA A' at hNextA
  change IsInvDomain kB B' at hNextB
  have hNextN : A'.N=B'.N := congrArg (geoStrictTransform π C) hN
  have hNextE : A'.E=B'.E := by
    change A.E.map (geoStrictTransform π C) ++ [D] = B.E.map (geoStrictTransform π C) ++ [D]
    rw [hE]
  have holA : ∀x g,A'.ideal.mem x g→HolomorphicAt n g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hNextA.isWellFormed.isCoherent hg
  have holB : ∀x g,B'.ideal.mem x g→HolomorphicAt n g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hNextB.isWellFormed.isCoherent hg
  have hOn : ∀z : Y,z∈A'.N→π z∈C→
      A.d≤divExpAlong n A.N A.ideal C (π z) ∧
      B.d≤divExpAlong n B.N B.ideal C (π z) ∧
      divExpAlong n A'.N A'.ideal D z=divExpAlong n A.N A.ideal C (π z)-A.d ∧
      divExpAlong n B'.N B'.ideal D z=divExpAlong n B.N B.ideal C (π z)-B.d ∧
      (∃e,¬IsDivNearAlong n A'.N A'.ideal D (e+1) z) ∧
      (∃e,¬IsDivNearAlong n B'.N B'.ideal D (e+1) z) ∧
      (∀e,IsDivNearAlong n A'.N A'.ideal D e z ↔ e≤divExpAlong n A'.N A'.ideal D z) ∧
      (∀e,IsDivNearAlong n B'.N B'.ideal D e z ↔ e≤divExpAlong n B'.N B'.ideal D z) := by
    intro z hzN hzC
    have hzBN : z∈B'.N := hNextN ▸ hzN
    have hBirthA := original_history_born_exponent A hA (.refl : BlowupTower X X) trivial hC hπ hzN hzC
    have hBirthB := original_history_born_exponent B hB (.refl : BlowupTower X X) trivial hCB hπ hzBN hzC
    obtain ⟨dA,hdA⟩ := hNextA.isWellFormed.isClosedSubmanifold_N.2 z hzN
    obtain ⟨rA,hrA⟩ := exists_isLocalRetraction hdA
    obtain ⟨dB,hdB⟩ := hNextB.isWellFormed.isClosedSubmanifold_N.2 z hzBN
    obtain ⟨rB,hrB⟩ := exists_isLocalRetraction hdB
    have hnA := hNextA.isNonzeroAlongAt z hzN
    have hnB := hNextB.isNonzeroAlongAt z hzBN
    exact ⟨hBirthA.1,hBirthB.1,hBirthA.2,hBirthB.2,
      exists_not_isDivNearAlong hrA hzC hnA holA,exists_not_isDivNearAlong hrB hzC hnB holB,
      fun e => isDivNearAlong_iff_le_divExpAlong hrA hzC hnA holA,
      fun e => isDivNearAlong_iff_le_divExpAlong hrB hzC hnB holB⟩
  have hOff : ∀z : Y,z∉A'.N∩D→
      (∀e,IsDivNearAlong n A'.N A'.ideal D e z) ∧
      (∀e,IsDivNearAlong n B'.N B'.ideal D e z) ∧
      divExpAlong n A'.N A'.ideal D z=0 ∧ divExpAlong n B'.N B'.ideal D z=0 := by
    intro z hz
    have hClosed : IsClosed (A'.N∩D) := hNextA.isWellFormed.isClosedSubmanifold_N.1.inter
      (hC.1.1.preimage hπ.contMDiff.continuous)
    have hNear : ∀ᶠy in 𝓝 z,y∉A'.N∩D := hClosed.isOpen_compl.mem_nhds hz
    have hNearB : ∀ᶠy in 𝓝 z,y∉B'.N∩D := by simpa only [hNextN] using hNear
    have hAllA (e : ℕ) : IsDivNearAlong n A'.N A'.ideal D e z :=
      hNear.mono fun _ hy hyN hyD => (hy ⟨hyN,hyD⟩).elim
    have hAllB (e : ℕ) : IsDivNearAlong n B'.N B'.ideal D e z :=
      hNearB.mono fun _ hy hyN hyD => (hy ⟨hyN,hyD⟩).elim
    have hNoA : ¬∃e,¬IsDivNearAlong n A'.N A'.ideal D (e+1) z := by
      rintro ⟨e,he⟩;exact he (hAllA (e+1))
    have hNoB : ¬∃e,¬IsDivNearAlong n B'.N B'.ideal D (e+1) z := by
      rintro ⟨e,he⟩;exact he (hAllB (e+1))
    exact ⟨hAllA,hAllB,by simp only [divExpAlong,dif_neg hNoA],by simp only [divExpAlong,dif_neg hNoB]⟩
  refine ⟨hNextA,hNextB,hNextN,hNextE,rfl,rfl,rfl,rfl,?_,hOn,hOff⟩
  intro z
  by_cases hz : z∈A'.N∩D
  · obtain ⟨hLowerA,hLowerB,hBornA,hBornB,_hFA,_hFB,_hAllA,_hAllB⟩ := hOn z hz.1 hz.2
    have hCross := hCentre (π z)
    have hAddA : divExpAlong n A.N A.ideal C (π z) = A.d+divExpAlong n A'.N A'.ideal D z := by omega
    have hAddB : divExpAlong n B.N B.ideal C (π z) = B.d+divExpAlong n B'.N B'.ideal D z := by omega
    rw [hAddA,hAddB,Nat.mul_add,Nat.mul_add] at hCross
    have hSame : B.d*A.d=A.d*B.d := Nat.mul_comm _ _
    rw [hSame] at hCross
    exact Nat.add_left_cancel hCross
  · obtain ⟨_hAllA,_hAllB,hZeroA,hZeroB⟩ := hOff z hz
    rw [hZeroA,hZeroB,Nat.mul_zero,Nat.mul_zero]

end Hironaka.HironakaActualOriginalLowerBornExponents.Generic

namespace Hironaka.HironakaActualOriginalLowerBornExponents
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences Hironaka.RegularLocusDense
  BlowupStrictSubmanifold
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
open DivisorExponentAlong
variable {n : ℕ} {X Y : CMfd.{u} n}

theorem original_lower_local_born_exponents {A : CMfd.{0} n}
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
                (∀ z : Y', z∈JR.cosupp →
                  HironakaActualProjectedNormalizedOrderDetection.OriginalFiniteOrderOutput JR z ∧
                  HironakaActualProjectedNormalizedOrderDetection.OriginalFiniteOrderOutput KR z ∧
                  KR.d*HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder JR.N JR.ideal z =
                    JR.d*HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder KR.N KR.ideal z ∧
                  ∀ p q : ℕ, 0<q → q≤p →
                    (((p*JR.d : ℕ) : ℕ∞) ≤ (q : ℕ∞)*GermIdealOrder.order n JR.N JR.ideal z ↔
                     ((p*KR.d : ℕ) : ℕ∞) ≤ (q : ℕ∞)*GermIdealOrder.order n KR.N KR.ideal z)) ∧
                ∀ (C : Set Y'), JR.IsAdmissibleCentre C →
                  KR.IsAdmissibleCentre C ∧
                  (∀ x : Y',KR.d*divExpAlong n JR.N JR.ideal C x=JR.d*divExpAlong n KR.N KR.ideal C x) ∧
                  (∀ x∈C,
                  JR.d≤divExpAlong n JR.N JR.ideal C x ∧ KR.d≤divExpAlong n KR.N KR.ideal C x ∧
                  (∃ r,¬IsDivNearAlong n JR.N JR.ideal C (r+1) x) ∧
                  (∃ r,¬IsDivNearAlong n KR.N KR.ideal C (r+1) x) ∧
                  (∀ e,IsDivNearAlong n JR.N JR.ideal C e x ↔ e≤divExpAlong n JR.N JR.ideal C x) ∧
                  (∀ e,IsDivNearAlong n KR.N KR.ideal C e x ↔ e≤divExpAlong n KR.N KR.ideal C x)) ∧
                  (∀ x∉C,
                  (∀ e,IsDivNearAlong n JR.N JR.ideal C e x) ∧
                  (∀ e,IsDivNearAlong n KR.N KR.ideal C e x) ∧
                  divExpAlong n JR.N JR.ideal C x=0 ∧ divExpAlong n KR.N KR.ideal C x=0) ∧
                  ∀ {Z' : CMfd.{0} n} (π : Z'→Y') (_hπ : IsBlowupAlong n C π),
                    let JNext := JR.geoTransform C π
                    let KNext := KR.geoTransform C π
                    let D := π ⁻¹' C
                    IsInvDomain ((k-1)-1) JNext ∧ IsInvDomain ((k-1)-1) KNext ∧ JNext.N=KNext.N ∧ JNext.E=KNext.E ∧
                    JNext.d=JR.d ∧ KNext.d=KR.d ∧
                    JNext.E=JR.E.map (geoStrictTransform π C) ++ [D] ∧
                    KNext.E=KR.E.map (geoStrictTransform π C) ++ [D] ∧
                    (∀ z : Z',KR.d*divExpAlong n JNext.N JNext.ideal D z=JR.d*divExpAlong n KNext.N KNext.ideal D z) ∧
                    (∀ z : Z',z∈JNext.N→π z∈C→
                    JR.d≤divExpAlong n JR.N JR.ideal C (π z) ∧
                    KR.d≤divExpAlong n KR.N KR.ideal C (π z) ∧
                    divExpAlong n JNext.N JNext.ideal D z=divExpAlong n JR.N JR.ideal C (π z)-JR.d ∧
                    divExpAlong n KNext.N KNext.ideal D z=divExpAlong n KR.N KR.ideal C (π z)-KR.d ∧
                    (∃ e,¬IsDivNearAlong n JNext.N JNext.ideal D (e+1) z) ∧
                    (∃ e,¬IsDivNearAlong n KNext.N KNext.ideal D (e+1) z) ∧
                    (∀ e,IsDivNearAlong n JNext.N JNext.ideal D e z ↔ e≤divExpAlong n JNext.N JNext.ideal D z) ∧
                    (∀ e,IsDivNearAlong n KNext.N KNext.ideal D e z ↔ e≤divExpAlong n KNext.N KNext.ideal D z)) ∧
                    (∀ z : Z',z∉JNext.N∩D→
                    (∀ e,IsDivNearAlong n JNext.N JNext.ideal D e z) ∧
                    (∀ e,IsDivNearAlong n KNext.N KNext.ideal D e z) ∧
                    divExpAlong n JNext.N JNext.ideal D z=0 ∧ divExpAlong n KNext.N KNext.ideal D z=0)) := by
  obtain ⟨hm,hxU,hJ,hK,hJE,hKE,hJd,hKd,hCommon⟩ :=
    HironakaActualOriginalLowerNextCentreExponents.original_lower_local_next_centre_exponents
      hn Q hQ hN hE hMax Z hZ hSing a ha
  refine ⟨hm,hxU,hJ,hK,hJE,hKE,hJd,hKd,?_⟩
  intro Y H hHJ
  obtain ⟨hHK,hStage⟩ := hCommon H hHJ
  refine ⟨hHK,?_⟩
  intro y hy hOut
  obtain ⟨hyO,hLJ,hLK,hOwn,hLN,hLE,hLJd,hLKd,hLJLen,hLKLen,hLocal⟩ := hStage y hy hOut
  refine ⟨hyO,hLJ,hLK,hOwn,hLN,hLE,hLJd,hLKd,hLJLen,hLKLen,?_⟩
  intro Y' R
  obtain ⟨hTest,hRecord⟩ := hLocal R
  refine ⟨hTest,?_⟩
  intro hRJ
  obtain ⟨hCos,hNcur,hEcur,hDJ,hDK,hClockJ,hClockK,hJR,hKR,hPoint,hCentres⟩ := hRecord hRJ
  refine ⟨hCos,hNcur,hEcur,hDJ,hDK,hClockJ,hClockK,hJR,hKR,hPoint,?_⟩
  intro C hC
  obtain ⟨hCB,hCentre,hOn,hOff⟩ := hCentres C hC
  refine ⟨hCB,hCentre,hOn,hOff,?_⟩
  intro Z' π hπ
  exact Generic.next_born_exponent_comparison _ _ hJR hKR hNcur hEcur hCos
    (fun z hz => (hPoint z hz).2.2.2) C hC π hπ

end
end Hironaka.HironakaActualOriginalLowerBornExponents
