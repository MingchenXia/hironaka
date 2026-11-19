import Hironaka.Resolution.HironakaActualOriginalLowerBornExponents
import Hironaka.Resolution.HironakaActualOriginalLowerOldExponents
import Hironaka.Resolution.HironakaActualOriginalLowerHeadProjectionTests
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualOriginalLowerChronologicalExponents.Generic
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower
  RelativePrincipalizationSpan MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec DivisorExponentAlong MonomialCaseAlong
  InvDomainTowerAlong HironakaActualOldDivisorExponentTransport BlowupSNCTransform
  MarkedIdealEquivalence.MarkedIdeal HironakaActualProjectionTestRecord HironakaActualLocalProductHistory
variable {n kA kB : ℕ} {X Y : CMfd.{0} n}
private theorem same_N (A B : MarkedIdeal n X) (hN : A.N=B.N) (T : BlowupTower X Y) :
    (geoTransformAlong A T).N=(geoTransformAlong B T).N := by
  rw [N_geoTransformAlong,N_geoTransformAlong,hN]

private theorem projected_cuts (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : A.N=B.N) (hE : A.E=B.E) (hP : WEquiv (projectionTest A) (projectionTest B)) :
    A.cosupp=B.cosupp ∧ ∀x∈A.cosupp,∀p q : ℕ,0<q→q≤p→
      ((((p*A.d : ℕ) : ℕ∞)≤(q : ℕ∞)*GermIdealOrder.order n A.N A.ideal x) ↔
       (((p*B.d : ℕ) : ℕ∞)≤(q : ℕ∞)*GermIdealOrder.order n B.N B.ideal x)) := by
  obtain ⟨_,_,_,_,_,_,_,hCA⟩ := projection_test_dictionary A hA
  obtain ⟨_,_,_,_,_,_,_,hCB⟩ := projection_test_dictionary B hB
  have hh := hP.cosupp_eq
  rw [hCA,hCB] at hh
  have hCos : A.cosupp=B.cosupp := by
    ext x
    exact Iff.of_eq (congrArg (fun S : Set (projectionAmbient X) => (x,0)∈S) hh)
  refine ⟨hCos,?_⟩
  intro x hx p q _hq _hpq
  obtain ⟨hFinA,hFinB,hCross⟩ :=
    HironakaActualProjectedNormalizedOrderDetection.normalized_ordinary_order_of_projected_wEquiv
      A B hA hB x hx (hCos ▸ hx) hN.symm hE.symm hP
  rw [hFinA.2.1,hFinB.2.1]
  have hNat := HironakaActualOriginalLowerNormalizedHighCuts.finite_cross_product_cuts _ _ _ _
    (by have := hA.one_le_d;omega) (by have := hB.one_le_d;omega) hCross p q
  exact_mod_cast hNat

private theorem off_trace (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (_hB : IsInvDomain kB B)
    (hN : A.N=B.N) (D : Set X) (hD : IsClosed D) (x : X) (hx : x∉A.N∩D) :
    (∀e,IsDivNearAlong n A.N A.ideal D e x) ∧ (∀e,IsDivNearAlong n B.N B.ideal D e x) ∧
      divExpAlong n A.N A.ideal D x=0 ∧ divExpAlong n B.N B.ideal D x=0 := by
  have hNear : ∀ᶠy in 𝓝 x,y∉A.N∩D :=
    (hA.isWellFormed.isClosedSubmanifold_N.1.inter hD).isOpen_compl.mem_nhds hx
  have hNearB : ∀ᶠy in 𝓝 x,y∉B.N∩D := by simpa only [hN] using hNear
  have hAllA (e : ℕ) : IsDivNearAlong n A.N A.ideal D e x :=
    hNear.mono fun _ hy hyN hyD => (hy ⟨hyN,hyD⟩).elim
  have hAllB (e : ℕ) : IsDivNearAlong n B.N B.ideal D e x :=
    hNearB.mono fun _ hy hyN hyD => (hy ⟨hyN,hyD⟩).elim
  have hNoA : ¬∃e,¬IsDivNearAlong n A.N A.ideal D (e+1) x := by rintro ⟨e,he⟩;exact he (hAllA _)
  have hNoB : ¬∃e,¬IsDivNearAlong n B.N B.ideal D (e+1) x := by rintro ⟨e,he⟩;exact he (hAllB _)
  exact ⟨hAllA,hAllB,by simp only [divExpAlong,dif_neg hNoA],by simp only [divExpAlong,dif_neg hNoB]⟩

-- Public365 only on actual proper strict traces; no individual equality off trace.
private theorem old_step (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : A.N=B.N) (hE : A.E=B.E)
    (hExp : ∀x i,B.d*expDataAlong n A.N A.ideal A.E x i=A.d*expDataAlong n B.N B.ideal B.E x i)
    (C : Set X) (hC : A.IsAdmissibleCentre C) (hCB : B.IsAdmissibleCentre C)
    (π : Y→X) (hπ : IsBlowupAlong n C π) (i : Fin A.E.length) (z : Y) :
    B.d*divExpAlong n (A.geoTransform C π).N (A.geoTransform C π).ideal (geoStrictTransform π C (A.E.get i)) z =
      A.d*divExpAlong n (B.geoTransform C π).N (B.geoTransform C π).ideal (geoStrictTransform π C (A.E.get i)) z := by
  let A' := A.geoTransform C π
  let B' := B.geoTransform C π
  let D := geoStrictTransform π C (A.E.get i)
  have hNA : IsInvDomain kA A' := isInvDomain_geoTransformAlong hA (.step .refl C π hπ) ⟨trivial,hC⟩
  have hNB : IsInvDomain kB B' := isInvDomain_geoTransformAlong hB (.step .refl C π hπ) ⟨trivial,hCB⟩
  have hNN : A'.N=B'.N := congrArg (geoStrictTransform π C) hN
  let j : Fin B.E.length := ⟨i.val,by rw [←hE];exact i.isLt⟩
  have hGet : A.E.get i=B.E.get j := by simpa only [List.get_eq_getElem] using getElem_congr hE rfl i.isLt
  by_cases hz : z∈A'.N∩D
  · have hSA := original_history_old_exponent A hA (.refl : BlowupTower X X) trivial hC hπ i hz.1 hz.2
    have hSB := original_history_old_exponent B hB (.refl : BlowupTower X X) trivial hCB hπ j
      (hNN ▸ hz.1) (by change z∈geoStrictTransform π C (B.E.get j);rw [←hGet];exact hz.2)
    change divExpAlong n A'.N A'.ideal (geoStrictTransform π C (A.E.get i)) z =
      divExpAlong n A.N A.ideal (A.E.get i) (π z) at hSA
    change divExpAlong n B'.N B'.ideal (geoStrictTransform π C (B.E.get j)) z =
      divExpAlong n B.N B.ideal (B.E.get j) (π z) at hSB
    rw [←hGet] at hSB
    rw [hSA,hSB]
    have hh := hExp (π z) i.val
    have hiB : i.val<B.E.length := by rw [←hE];exact i.isLt
    simpa only [expDataAlong,dif_pos i.isLt,dif_pos hiB,Fin.eta,hGet] using hh
  · obtain ⟨_hAllA,_hAllB,hZeroA,hZeroB⟩ := off_trace A' B' hNA hNB hNN D isClosed_closure z hz
    rw [hZeroA,hZeroB,Nat.mul_zero,Nat.mul_zero]

private theorem all_exp (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : A.N=B.N) (hE : A.E=B.E) (hP : WEquiv (projectionTest A) (projectionTest B))
    (hInitial : ∀ (i : Fin A.E.length) (x : X),B.d*divExpAlong n A.N A.ideal (A.E.get i) x=
      A.d*divExpAlong n B.N B.ideal (A.E.get i) x) :
    {Y : CMfd.{0} n} → (T : BlowupTower X Y) → IsGeoTestTower A T → IsGeoTestTower B T →
      ∀z i,(geoTransformAlong B T).d*expDataAlong n (geoTransformAlong A T).N (geoTransformAlong A T).ideal
        (geoTransformAlong A T).E z i = (geoTransformAlong A T).d*expDataAlong n
          (geoTransformAlong B T).N (geoTransformAlong B T).ideal (geoTransformAlong B T).E z i
  | _,.refl,_hTA,_hTB,z,i => by
    change B.d*expDataAlong n A.N A.ideal A.E z i=A.d*expDataAlong n B.N B.ideal B.E z i
    by_cases hi : i<A.E.length
    · have hiB : i<B.E.length := by rw [←hE];exact hi
      have hGet : A.E.get ⟨i,hi⟩=B.E.get ⟨i,hiB⟩ := by simpa only [List.get_eq_getElem] using getElem_congr hE rfl hi
      simpa only [expDataAlong,dif_pos hi,dif_pos hiB,hGet] using hInitial ⟨i,hi⟩ z
    · have hiB : ¬i<B.E.length := by rw [←hE];exact hi
      simp only [expDataAlong,dif_neg hi,dif_neg hiB,Nat.mul_zero]
  | _,.step T C π hπ,hTA,hTB,z,i => by
    let A0 := geoTransformAlong A T
    let B0 := geoTransformAlong B T
    have hA0 := isInvDomain_geoTransformAlong hA T hTA.1
    have hB0 := isInvDomain_geoTransformAlong hB T hTB.1
    have hN0 := same_N A B hN T
    have hE0 := E_geoTransformAlong_eq hE T
    have hP0 := HironakaActualLocalProductHistory.current_projected_wEquiv A B
      hA.isWellFormed hB.isWellFormed hP T hTA.1 hTB.1
    obtain ⟨hCos,hCuts⟩ := projected_cuts A0 B0 hA0 hB0 hN0 hE0 hP0
    obtain ⟨_hNextA,_hNextB,_hNextN,_hNextE,_hdA,_hdB,_hEA,_hEB,hBorn,_hOn,_hOff⟩ :=
      HironakaActualOriginalLowerBornExponents.Generic.next_born_exponent_comparison
        A0 B0 hA0 hB0 hN0 hE0 hCos hCuts C hTA.2 π hπ
    have ih := all_exp A B hA hB hN hE hP hInitial T hTA.1 hTB.1
    change B0.d*expDataAlong n (A0.geoTransform C π).N (A0.geoTransform C π).ideal
      (A0.geoTransform C π).E z i = A0.d*expDataAlong n (B0.geoTransform C π).N
        (B0.geoTransform C π).ideal (B0.geoTransform C π).E z i
    have hLen : A0.E.length=B0.E.length := congrArg List.length hE0
    by_cases hi : i<A0.E.length
    · have hiB : i<B0.E.length := by rw [←hLen];exact hi
      have hiA' : i<(A0.geoTransform C π).E.length := by change i<(A0.E.map _ ++ [_]).length;simp;omega
      have hiB' : i<(B0.geoTransform C π).E.length := by change i<(B0.E.map _ ++ [_]).length;simp;omega
      have hGetA : (A0.geoTransform C π).E.get ⟨i,hiA'⟩=geoStrictTransform π C (A0.E.get ⟨i,hi⟩) := by
        change (A0.E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).get ⟨i,hiA'⟩ = _
        simpa only [dif_pos hi] using get_map_append_singleton A0.E (geoStrictTransform π C) (π ⁻¹' C) ⟨i,hiA'⟩
      have hGetB : (B0.geoTransform C π).E.get ⟨i,hiB'⟩=geoStrictTransform π C (A0.E.get ⟨i,hi⟩) := by
        change (B0.E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).get ⟨i,hiB'⟩ = _
        have hh := get_map_append_singleton B0.E (geoStrictTransform π C) (π ⁻¹' C) ⟨i,hiB'⟩
        have hGet : A0.E.get ⟨i,hi⟩=B0.E.get ⟨i,hiB⟩ := by simpa only [List.get_eq_getElem] using getElem_congr hE0 rfl hi
        simpa only [dif_pos hiB,←hGet] using hh
      simp only [expDataAlong,dif_pos hiA',dif_pos hiB',hGetA,hGetB]
      exact old_step A0 B0 hA0 hB0 hN0 hE0 ih C hTA.2 hTB.2 π hπ ⟨i,hi⟩ z
    · by_cases he : i=A0.E.length
      · subst i
        have hA' : A0.E.length<(A0.geoTransform C π).E.length := by change _<(A0.E.map _ ++ [_]).length;simp
        have hB' : A0.E.length<(B0.geoTransform C π).E.length := by change _<(B0.E.map _ ++ [_]).length;simp [hLen]
        have hGA : (A0.geoTransform C π).E.get ⟨A0.E.length,hA'⟩=π ⁻¹' C := by
          change (A0.E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).get ⟨A0.E.length,hA'⟩ = _
          simpa only [dif_neg (Nat.lt_irrefl _)] using get_map_append_singleton A0.E (geoStrictTransform π C) (π ⁻¹' C) ⟨A0.E.length,hA'⟩
        have hGB : (B0.geoTransform C π).E.get ⟨A0.E.length,hB'⟩=π ⁻¹' C := by
          change (B0.E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).get ⟨A0.E.length,hB'⟩ = _
          have hh := get_map_append_singleton B0.E (geoStrictTransform π C) (π ⁻¹' C) ⟨A0.E.length,hB'⟩
          simpa only [hLen,dif_neg (Nat.lt_irrefl _)] using hh
        simpa only [expDataAlong,dif_pos hA',dif_pos hB',hGA,hGB] using hBorn z
      · have hiA' : ¬i<(A0.geoTransform C π).E.length := by change ¬i<(A0.E.map _ ++ [_]).length;simp;omega
        have hiB' : ¬i<(B0.geoTransform C π).E.length := by change ¬i<(B0.E.map _ ++ [_]).length;simp;omega
        simp only [expDataAlong,dif_neg hiA',dif_neg hiB',Nat.mul_zero]

private theorem oldBoundaryAlong_eq (E : List (Set X)) :
    {Y : CMfd.{0} n} → (T : BlowupTower X Y) → oldBoundaryAlong E T=E.map (strictAlong T)
  | _,.refl => by simp [oldBoundaryAlong,strictAlong]
  | _,.step T C π hπ => by rw [oldBoundaryAlong,oldBoundaryAlong_eq E T,List.map_map];rfl

theorem all_chronological_boundary_exponents
    (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : A.N=B.N) (hE : A.E=B.E)
    (hProjected : WEquiv (projectionTest A) (projectionTest B))
    (hInitial : ∀ (i : Fin A.E.length) (x : X),
      B.d*divExpAlong n A.N A.ideal (A.E.get i) x=A.d*divExpAlong n B.N B.ideal (A.E.get i) x)
    (T : BlowupTower X Y) (hTA : IsGeoTestTower A T) (hTB : IsGeoTestTower B T) :
    let AR := geoTransformAlong A T
    let BR := geoTransformAlong B T
    IsInvDomain kA AR ∧ IsInvDomain kB BR ∧ AR.N=BR.N ∧ AR.E=BR.E ∧
      AR.d=A.d ∧ BR.d=B.d ∧ AR.E.length=A.E.length+T.length ∧ BR.E.length=B.E.length+T.length ∧
      AR.E=A.E.map (strictAlong T) ++ bornBoundaryAlong T ∧
      BR.E=B.E.map (strictAlong T) ++ bornBoundaryAlong T ∧
      (bornBoundaryAlong T).length=T.length ∧
      (∀ (z : Y) (i : ℕ),BR.d*expDataAlong n AR.N AR.ideal AR.E z i =
        AR.d*expDataAlong n BR.N BR.ideal BR.E z i) ∧
      (∀ (i : Fin AR.E.length) (z : Y),
        (z∈AR.N∩AR.E.get i →
          (∃e,¬IsDivNearAlong n AR.N AR.ideal (AR.E.get i) (e+1) z) ∧
          (∃e,¬IsDivNearAlong n BR.N BR.ideal (AR.E.get i) (e+1) z) ∧
          (∀e,IsDivNearAlong n AR.N AR.ideal (AR.E.get i) e z ↔ e≤divExpAlong n AR.N AR.ideal (AR.E.get i) z) ∧
          (∀e,IsDivNearAlong n BR.N BR.ideal (AR.E.get i) e z ↔ e≤divExpAlong n BR.N BR.ideal (AR.E.get i) z)) ∧
        (z∉AR.N∩AR.E.get i →
          (∀e,IsDivNearAlong n AR.N AR.ideal (AR.E.get i) e z) ∧
          (∀e,IsDivNearAlong n BR.N BR.ideal (AR.E.get i) e z) ∧
          divExpAlong n AR.N AR.ideal (AR.E.get i) z=0 ∧
          divExpAlong n BR.N BR.ideal (AR.E.get i) z=0)) := by
  have hAR := isInvDomain_geoTransformAlong hA T hTA
  have hBR := isInvDomain_geoTransformAlong hB T hTB
  have hNR := same_N A B hN T
  have hER := E_geoTransformAlong_eq hE T
  obtain ⟨hDA,_hOldLen,hBornLen⟩ := source_boundary_dictionary A T
  obtain ⟨hDB,_hOldLenB,_hBornLenB⟩ := source_boundary_dictionary B T
  rw [oldBoundaryAlong_eq] at hDA hDB
  refine ⟨hAR,hBR,hNR,hER,d_geoTransformAlong A T,d_geoTransformAlong B T,
    length_E_geoTransformAlong A T,length_E_geoTransformAlong B T,hDA,hDB,hBornLen,
    all_exp A B hA hB hN hE hProjected hInitial T hTA hTB,?_⟩
  intro i z
  let AR := geoTransformAlong A T
  let BR := geoTransformAlong B T
  let D := AR.E.get i
  refine ⟨?_,?_⟩
  · intro hz
    have hzB : z∈BR.N := hNR ▸ hz.1
    obtain ⟨dA,hdA⟩ := hAR.isWellFormed.isClosedSubmanifold_N.2 z hz.1
    obtain ⟨rA,hrA⟩ := exists_isLocalRetraction hdA
    obtain ⟨dB,hdB⟩ := hBR.isWellFormed.isClosedSubmanifold_N.2 z hzB
    obtain ⟨rB,hrB⟩ := exists_isLocalRetraction hdB
    have holA : ∀x g,AR.ideal.mem x g→HolomorphicAt n g x := fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hAR.isWellFormed.isCoherent hg
    have holB : ∀x g,BR.ideal.mem x g→HolomorphicAt n g x := fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hBR.isWellFormed.isCoherent hg
    have hnA := hAR.isNonzeroAlongAt z hz.1
    have hnB := hBR.isNonzeroAlongAt z hzB
    exact ⟨exists_not_isDivNearAlong hrA hz.2 hnA holA,exists_not_isDivNearAlong hrB hz.2 hnB holB,
      fun e => isDivNearAlong_iff_le_divExpAlong hrA hz.2 hnA holA,
      fun e => isDivNearAlong_iff_le_divExpAlong hrB hz.2 hnB holB⟩
  · intro hz
    exact off_trace AR BR hAR hBR hNR D (hAR.isWellFormed.isSNCDivisor.1 _ (List.get_mem _ _)) z hz

end Hironaka.HironakaActualOriginalLowerChronologicalExponents.Generic

namespace Hironaka.HironakaActualOriginalLowerChronologicalExponents
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

theorem original_lower_local_chronological_exponents {A : CMfd.{0} n}
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
    HironakaActualOriginalLowerOldExponents.original_lower_local_initial_old_exponents
      hn Q hQ hN hE hMax Z hZ hSing a ha
  obtain ⟨_hmP,_hxP,_hJP,_hKP,_hJEP,_hKEP,_hJdP,_hKdP,hProj⟩ :=
    HironakaActualOriginalLowerHeadProjectionTests.original_lower_head_projection_tests
      hn Q hQ hN hE hMax Z hZ hSing a ha
  refine ⟨hm,hxU,hJ,hK,hJE,hKE,hJd,hKd,?_⟩
  intro Y H hHJ
  obtain ⟨hHK,hStage⟩ := hCommon H hHJ
  obtain ⟨_hHKP,hStageP⟩ := hProj H hHJ
  refine ⟨hHK,?_⟩
  intro y hy hOut
  obtain ⟨hyO,hLJ,hLK,hOwn,hLN,hLE,hLJd,hLKd,hLJLen,hLKLen,hExp,hData,hLocal⟩ := hStage y hy hOut
  obtain ⟨_hyOP,_hLJP,_hLKP,_hOwnP,_hLNP,_hLEP,_hLJdP,_hLKdP,_hLJLenP,_hLKLenP,hProjected,_hLocalP⟩ := hStageP y hy hOut
  refine ⟨hyO,hLJ,hLK,hOwn,hLN,hLE,hLJd,hLKd,hLJLen,hLKLen,hExp,hData,?_⟩
  intro Y' R
  obtain ⟨hTest,hRecord⟩ := hLocal R
  refine ⟨hTest,?_⟩
  intro hRJ
  obtain ⟨hCos,hNcur,hEcur,hDJ,hDK,hClockJ,hClockK,hJR,hKR,hOldScale,hOldOn,hOldOff,hPoint⟩ := hRecord hRJ
  obtain ⟨_hJR,_hKR,_hNcur,_hEcur,_hDJ,_hDK,_hClockJ,_hClockK,hWholeJ,hWholeK,hBornLen,hAllExp,hTrace⟩ :=
    Generic.all_chronological_boundary_exponents _ _ hLJ hLK hLN hLE hProjected
      (fun i x => hExp _ x) R hRJ (hTest.mp hRJ)
  exact ⟨hCos,hNcur,hEcur,hDJ,hDK,hClockJ,hClockK,hJR,hKR,hWholeJ,hWholeK,hBornLen,hAllExp,hTrace,
    hOldScale,hOldOn,hOldOff,hPoint⟩

end
end Hironaka.HironakaActualOriginalLowerChronologicalExponents
