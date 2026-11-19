import Hironaka.Resolution.HironakaActualOriginalLowerNormalizedHighCuts
import Hironaka.Invariant.DivisorExponentAlong
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualOriginalLowerNextCentreExponents.Generic
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers RelativePrincipalizationSpan MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  DivisorExponentAlong GermIdealOrder IdealWeightPowers InvDomainTowerAlong
variable {n kA kB : ℕ} {X : CMfd.{u} n}
-- Provenance: accepted279 bounded_failure_point; exact native ENat successor argument.
private theorem bounded_failure_point (N : Set X) (I : GermIdeal n X)
    (hI : ∀x f,I.mem x f→HolomorphicAt n f x) (C : Set X) (x : X) (r : ℕ)
    (hNot : ¬IsDivNearAlong n N I C (r+1) x)
    {P : X→Prop} (hNear : ∀ᶠ y in 𝓝 x,P y) :
    ∃y,y∈N ∧ y∈C ∧ GermIdealOrder.order n N I y≤(r : ℕ∞) ∧ P y := by
  unfold IsDivNearAlong at hNot
  rw [Filter.not_eventually] at hNot
  have hFreq : ∃ᶠ y in 𝓝 x,y∈N ∧ y∈C ∧ y∉cosupport n N I (r+1) :=
    hNot.mono fun y hy => by
      obtain ⟨hyN,hy⟩ := Classical.not_imp.mp hy
      obtain ⟨hyC,hyCos⟩ := Classical.not_imp.mp hy
      exact ⟨hyN,hyC,hyCos⟩
  obtain ⟨y,⟨hyN,hyC,hyCos⟩,hyP⟩ := (hFreq.and_eventually hNear).exists
  have hNotOrder : ¬((r+1 : ℕ) : ℕ∞)≤GermIdealOrder.order n N I y :=
    fun h => hyCos ⟨hyN,(le_order_iff (hI y)).mp h⟩
  have hBound : GermIdealOrder.order n N I y≤(r : ℕ∞) :=
    ENat.lt_natCast_add_one_iff.mp (lt_of_not_ge (by
      simpa only [Nat.cast_add,Nat.cast_one] using hNotOrder))
  exact ⟨y,hyN,hyC,hBound,hyP⟩

-- Localized accepted279 positive_cross_le: cuts are required ONLY at witness y∈C.
private theorem centre_cross_le (A B : MarkedIdeal n X)
    (hA : A.ideal.IsCoherent) (hB : B.ideal.IsCoherent)
    (hN : A.N=B.N) (C : Set X) (x : X) (ha : 0<A.d)
    (hCuts : ∀y∈C,∀ p q : ℕ,0<q→q≤p→
      ((((p*A.d : ℕ) : ℕ∞)≤(q : ℕ∞)*GermIdealOrder.order n A.N A.ideal y) ↔
       (((p*B.d : ℕ) : ℕ∞)≤(q : ℕ∞)*GermIdealOrder.order n B.N B.ideal y)))
    (hLower : A.d≤divExpAlong n A.N A.ideal C x)
    (hNot : ¬IsDivNearAlong n B.N B.ideal C (divExpAlong n B.N B.ideal C x+1) x) :
    B.d*divExpAlong n A.N A.ideal C x≤A.d*divExpAlong n B.N B.ideal C x := by
  let rA := divExpAlong n A.N A.ideal C x
  let rB := divExpAlong n B.N B.ideal C x
  have holA : ∀y f,A.ideal.mem y f→HolomorphicAt n f y :=
    fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hA hf
  have holB : ∀y f,B.ideal.mem y f→HolomorphicAt n f y :=
    fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hB hf
  have hDiv := isDivNearAlong_divExpAlong (N:=A.N) (H:=C) holA x
  obtain ⟨y,hyN,hyC,hBbound,hyDiv⟩ := bounded_failure_point B.N B.ideal holB C x rB hNot hDiv
  have hyNA : y∈A.N := by rw [hN];exact hyN
  have hAord : (rA : ℕ∞)≤GermIdealOrder.order n A.N A.ideal y :=
    (le_order_iff (holA y)).mpr (hyDiv hyNA hyC).2
  have hScaled : ((rA*A.d : ℕ) : ℕ∞)≤(A.d : ℕ∞)*GermIdealOrder.order n A.N A.ideal y := by
    rw [Nat.cast_mul]
    calc
      (rA : ℕ∞)*(A.d : ℕ∞) = (A.d : ℕ∞)*(rA : ℕ∞) := mul_comm _ _
      _ ≤ (A.d : ℕ∞)*GermIdealOrder.order n A.N A.ideal y := by gcongr
  have hPeer := (hCuts y hyC rA A.d ha hLower).mp hScaled
  have hUpper : (A.d : ℕ∞)*GermIdealOrder.order n B.N B.ideal y≤((A.d*rB : ℕ) : ℕ∞) := by
    rw [Nat.cast_mul]
    gcongr
  have hNat := hPeer.trans hUpper
  have hh : rA*B.d≤A.d*rB := by exact_mod_cast hNat
  simpa only [Nat.mul_comm] using hh

-- Internal mathematical producer only: current domains/cuts are DERIVED by full ordinary consumer.
theorem next_centre_exponent_comparison
    (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : A.N=B.N) (hE : A.E=B.E) (hCos : A.cosupp=B.cosupp)
    (hCuts : ∀ x∈A.cosupp,∀ p q : ℕ,0<q→q≤p→
      ((((p*A.d : ℕ) : ℕ∞)≤(q : ℕ∞)*GermIdealOrder.order n A.N A.ideal x) ↔
       (((p*B.d : ℕ) : ℕ∞)≤(q : ℕ∞)*GermIdealOrder.order n B.N B.ideal x)))
    (C : Set X) (hC : A.IsAdmissibleCentre C) :
    B.IsAdmissibleCentre C ∧
    (∀ x : X,B.d*divExpAlong n A.N A.ideal C x=A.d*divExpAlong n B.N B.ideal C x) ∧
    (∀ x∈C,
      A.d≤divExpAlong n A.N A.ideal C x ∧ B.d≤divExpAlong n B.N B.ideal C x ∧
      (∃ r,¬IsDivNearAlong n A.N A.ideal C (r+1) x) ∧
      (∃ r,¬IsDivNearAlong n B.N B.ideal C (r+1) x) ∧
      (∀ e,IsDivNearAlong n A.N A.ideal C e x ↔ e≤divExpAlong n A.N A.ideal C x) ∧
      (∀ e,IsDivNearAlong n B.N B.ideal C e x ↔ e≤divExpAlong n B.N B.ideal C x)) ∧
    (∀ x∉C,
      (∀ e,IsDivNearAlong n A.N A.ideal C e x) ∧
      (∀ e,IsDivNearAlong n B.N B.ideal C e x) ∧
      divExpAlong n A.N A.ideal C x=0 ∧ divExpAlong n B.N B.ideal C x=0) := by
  have hCB : B.IsAdmissibleCentre C := ⟨hC.1,fun x hx => hCos ▸ hC.2.1 hx,by rw [←hE];exact hC.2.2⟩
  have holA : ∀x g,A.ideal.mem x g→HolomorphicAt n g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hA.isWellFormed.isCoherent hg
  have holB : ∀x g,B.ideal.mem x g→HolomorphicAt n g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hB.isWellFormed.isCoherent hg
  have hOn : ∀x∈C,
      A.d≤divExpAlong n A.N A.ideal C x ∧ B.d≤divExpAlong n B.N B.ideal C x ∧
      (∃r,¬IsDivNearAlong n A.N A.ideal C (r+1) x) ∧
      (∃r,¬IsDivNearAlong n B.N B.ideal C (r+1) x) ∧
      (∀e,IsDivNearAlong n A.N A.ideal C e x ↔ e≤divExpAlong n A.N A.ideal C x) ∧
      (∀e,IsDivNearAlong n B.N B.ideal C e x ↔ e≤divExpAlong n B.N B.ideal C x) := by
    intro x hx
    obtain ⟨dA,hdA⟩ := hA.isWellFormed.isClosedSubmanifold_N.2 x (hC.subset_N hx)
    obtain ⟨rA,hrA⟩ := exists_isLocalRetraction hdA
    obtain ⟨dB,hdB⟩ := hB.isWellFormed.isClosedSubmanifold_N.2 x (hCB.subset_N hx)
    obtain ⟨rB,hrB⟩ := exists_isLocalRetraction hdB
    have hnA := hA.isNonzeroAlongAt x (hC.subset_N hx)
    have hnB := hB.isNonzeroAlongAt x (hCB.subset_N hx)
    have hAllA (e : ℕ) := isDivNearAlong_iff_le_divExpAlong hrA hx hnA holA (e:=e)
    have hAllB (e : ℕ) := isDivNearAlong_iff_le_divExpAlong hrB hx hnB holB (e:=e)
    have hdA : IsDivNearAlong n A.N A.ideal C A.d x :=
      Filter.Eventually.of_forall fun y _hyN hyC => hC.2.1 hyC
    have hdB : IsDivNearAlong n B.N B.ideal C B.d x :=
      Filter.Eventually.of_forall fun y _hyN hyC => hCB.2.1 hyC
    exact ⟨(hAllA A.d).mp hdA,(hAllB B.d).mp hdB,
      exists_not_isDivNearAlong hrA hx hnA holA,exists_not_isDivNearAlong hrB hx hnB holB,hAllA,hAllB⟩
  have hOff : ∀x∉C,
      (∀e,IsDivNearAlong n A.N A.ideal C e x) ∧
      (∀e,IsDivNearAlong n B.N B.ideal C e x) ∧
      divExpAlong n A.N A.ideal C x=0 ∧ divExpAlong n B.N B.ideal C x=0 := by
    intro x hx
    have hNear : ∀ᶠ y in 𝓝 x,y∉C := hC.1.1.isOpen_compl.mem_nhds hx
    have hAllA (e : ℕ) : IsDivNearAlong n A.N A.ideal C e x :=
      hNear.mono fun _ hy _hyN hyC => (hy hyC).elim
    have hAllB (e : ℕ) : IsDivNearAlong n B.N B.ideal C e x :=
      hNear.mono fun _ hy _hyN hyC => (hy hyC).elim
    have hNoA : ¬∃r,¬IsDivNearAlong n A.N A.ideal C (r+1) x := by
      rintro ⟨r,hr⟩;exact hr (hAllA (r+1))
    have hNoB : ¬∃r,¬IsDivNearAlong n B.N B.ideal C (r+1) x := by
      rintro ⟨r,hr⟩;exact hr (hAllB (r+1))
    exact ⟨hAllA,hAllB,by simp only [divExpAlong,dif_neg hNoA],by simp only [divExpAlong,dif_neg hNoB]⟩
  refine ⟨hCB,?_,hOn,hOff⟩
  intro x
  by_cases hx : x∈C
  · obtain ⟨hLowerA,hLowerB,_hFinA,_hFinB,hAllA,hAllB⟩ := hOn x hx
    have hNotA : ¬IsDivNearAlong n A.N A.ideal C (divExpAlong n A.N A.ideal C x+1) x := by
      intro h;have := (hAllA _).mp h;omega
    have hNotB : ¬IsDivNearAlong n B.N B.ideal C (divExpAlong n B.N B.ideal C x+1) x := by
      intro h;have := (hAllB _).mp h;omega
    apply Nat.le_antisymm
    · exact centre_cross_le A B hA.isWellFormed.isCoherent hB.isWellFormed.isCoherent hN C x
        (by have := hA.one_le_d;omega)
        (fun y hy => hCuts y (hC.2.1 hy)) hLowerA hNotB
    · exact centre_cross_le B A hB.isWellFormed.isCoherent hA.isWellFormed.isCoherent hN.symm C x
        (by have := hB.one_le_d;omega)
        (fun y hy p q hq hpq => (hCuts y (hC.2.1 hy) p q hq hpq).symm) hLowerB hNotA
  · obtain ⟨_hAllA,_hAllB,hZeroA,hZeroB⟩ := hOff x hx
    rw [hZeroA,hZeroB,Nat.mul_zero,Nat.mul_zero]

end Hironaka.HironakaActualOriginalLowerNextCentreExponents.Generic

namespace Hironaka.HironakaActualOriginalLowerNextCentreExponents
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
open DivisorExponentAlong
variable {n : ℕ} {X Y : CMfd.{u} n}

theorem original_lower_local_next_centre_exponents {A : CMfd.{0} n}
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
                  divExpAlong n JR.N JR.ideal C x=0 ∧ divExpAlong n KR.N KR.ideal C x=0)) := by
  obtain ⟨hm,hxU,hJ,hK,hJE,hKE,hJd,hKd,hCommon⟩ :=
    HironakaActualOriginalLowerNormalizedHighCuts.original_lower_local_normalized_high_cuts
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
  obtain ⟨hCos,hNcur,hEcur,hDJ,hDK,hClockJ,hClockK,hJR,hKR,hPoint⟩ := hRecord hRJ
  refine ⟨hCos,hNcur,hEcur,hDJ,hDK,hClockJ,hClockK,hJR,hKR,hPoint,?_⟩
  intro C hC
  exact HironakaActualOriginalLowerNextCentreExponents.Generic.next_centre_exponent_comparison _ _ hJR hKR
    hNcur hEcur hCos (fun z hz => (hPoint z hz).2.2.2) C hC

end
end Hironaka.HironakaActualOriginalLowerNextCentreExponents
