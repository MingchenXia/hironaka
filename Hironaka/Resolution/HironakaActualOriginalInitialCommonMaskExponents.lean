import Hironaka.Resolution.HironakaActualProjectedNormalizedOrderDetection
import Hironaka.Resolution.HironakaActualOriginalLowerHeadProjectionTests
import Hironaka.Resolution.HironakaActualOriginalLowerNormalizedHighCuts
import Hironaka.Resolution.HironakaActualOriginalContactBoundaryExponentScaling
import Hironaka.Resolution.HironakaActualOriginalCommonMaskRawOrder

/-! ORIGINAL head records and arbitrary future LOCAL controlled tests.
Blueprint FIRST. Original coefficient/hom transforms remain on the left;
current coefficient/hom records are auxiliary comparison bounds only. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualOriginalInitialCommonMaskExponents
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
open HironakaActualOriginalStrictContactWeightedOrder HironakaActualOriginalOwnContactRawOrder
  TransformOffCentre HomogenizedIdealAlong MonomialCaseAlong
variable {n : ℕ} {X Y : CMfd.{u} n}

-- Elementary open transport only; the full exponent engine is the public mother.
private theorem exponent_open (M : MarkedIdeal n X) (hM : M.ideal.IsCoherent)
    (U : Opens X) (p : U) (D : Set X) :
    DivisorExponentAlong.divExpAlong n (MarkedIdeal.pullback (Subtype.val : U→X) M).N
      (MarkedIdeal.pullback (Subtype.val : U→X) M).ideal ((Subtype.val : U→X) ⁻¹' D) p =
        DivisorExponentAlong.divExpAlong n M.N M.ideal D p.val := by
  exact MonomialInvariantFunctorialAlong.divExpAlong_pullback (φ := (Subtype.val : U→X))
    (fun e => MarkedIdealRestrictOpen.cosupp_pullback_val (⟨M.N,[],M.ideal,e⟩ : MarkedIdeal n X)
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hM hg) U)
    (map_nhds_subtype_coe_eq_nhds p.property (U.isOpen.mem_nhds p.property)) D

-- Provenance: accepted418 projected_cosupp, short public-mother composition only.
private theorem projected_cosupp (K : MarkedIdeal n X) {k : ℕ} (hK : IsInvDomain k K)
    (T : BlowupTower X Y) (hTK : IsGeoTestTower K T) (y : Y)
    (hy : y∈(geoTransformAlong (barMarked K) T).cosupp) : T.proj y∈K.cosupp := by
  have hh := StepOneLowerDomain.proj_mem_cosupp_of_mem_cosupp (𝔪:=barMarked K)
    hK.isWellFormed.isClosedSubmanifold_N
    (isWellFormed_barMarked K hK.isWellFormed).isCoherent T
    ((original_bar_weighted_history K hK T hTK).2.2.1) hy
  rw [cosupp_barMarked K hK.isWellFormed hK.one_le_d] at hh
  exact hh

theorem original_lower_initial_common_mask_exponents {A : CMfd.{0} n}
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
                ∀ z : Y', z∈JR.cosupp →
                  HironakaActualProjectedNormalizedOrderDetection.OriginalFiniteOrderOutput JR z ∧
                  HironakaActualProjectedNormalizedOrderDetection.OriginalFiniteOrderOutput KR z ∧
                  KR.d*HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder JR.N JR.ideal z =
                    JR.d*HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder KR.N KR.ideal z ∧
                  ∀ p q : ℕ, 0<q → q≤p →
                    (((p*JR.d : ℕ) : ℕ∞) ≤ (q : ℕ∞)*GermIdealOrder.order n JR.N JR.ideal z ↔
                     ((p*KR.d : ℕ) : ℕ∞) ≤ (q : ℕ∞)*GermIdealOrder.order n KR.N KR.ideal z)) := by
  obtain ⟨hm,hxU,hJ,hK,hJE,hKE,hJd,hKd,hCommon⟩ :=
    HironakaActualOriginalLowerNormalizedHighCuts.original_lower_local_normalized_high_cuts
      hn Q hQ hN hE hMax Z hZ hSing a ha
  obtain ⟨_hmE,_hxE,_hJE,_hKE,_hJdE,_hKdE,_hzJ,_hzK,hExponents⟩ :=
    HironakaActualOriginalContactBoundaryExponentScaling.original_lower_contact_boundary_exponent_scaling
      hn Q hQ hN hE hMax Z hZ hSing a ha
  refine ⟨hm,hxU,hJ,hK,hJE,hKE,hJd,hKd,?_⟩
  intro Y H hHJ
  obtain ⟨hHK,hStage⟩ := hCommon H hHJ
  refine ⟨hHK,?_⟩
  intro y hy hOut
  obtain ⟨hyO,hLJ,hLK,hOwn,hLN,hLE,hLJd,hLKd,hLJLen,hLKLen,hLocal⟩ := hStage y hy hOut
  let V := maskB Q (.refl : BlowupTower A A) a
  let L : MarkedIdeal n (CMfd.of (n:=n) V) := lowerMarkedB Q (.refl : BlowupTower A A) a
  let x : V := ⟨a,hm⟩
  let μ := NonmonomialOrderLocal.nmOrd L x
  let e := sumExp (fun j=>L.d-j) L.d 0
  let U := NonmonomialOrderTail.ordMask L μ
  let P : MarkedIdeal n (CMfd.of (n:=n) U) := MarkedIdeal.pullback (Subtype.val : U→V) L
  let B : MarkedIdeal n (CMfd.of (n:=n) U) := MarkedIdeal.pullback (Subtype.val : U→V) (coeffMarkedAlong L)
  let J := CompanionRebase.companionOf n P μ
  let K := CompanionRebase.companionOf n B (e*μ)
  change IsInvDomain (k-1) J at hJ
  change IsInvDomain (k-1) K at hK
  have hz := projected_cosupp K hK H hHK y hy
  obtain ⟨hOpen,hWide⟩ := hExponents (H.proj y) hz
  obtain ⟨_hHK,_hNW,_hEW,_hdJW,_hdKW,_hLenJW,_hLenKW,hExp⟩ := hWide H hHJ
  let W : Opens (CMfd.of (n:=n) U) := ⟨(tangentChoice K (H.proj y)).1,hOpen⟩
  let Wide := openPreimage H W
  let O := maskB K H y
  let w := (tangentChoice K (H.proj y)).2
  let GJ := withN (coeffMarkedAlong (geoTransformAlong (barMarked J) H))
    (strictAlong H (J.N∩{z | w z=0}))
  let GK := withN (coeffMarkedAlong (geoTransformAlong (barMarked K) H))
    (strictAlong H (K.N∩{z | w z=0}))
  have hCoherentJ : GJ.ideal.IsCoherent := by
    have hh := (original_bar_weighted_history J hJ H hHJ).2.1
    exact isCoherent_coeffMarkedAlong hh.isWellFormed.isCoherent hh.isWellFormed.isClosedSubmanifold_N
  have hCoherentK : GK.ideal.IsCoherent := by
    have hh := (original_bar_weighted_history K hK H hHK).2.1
    exact isCoherent_coeffMarkedAlong hh.isWellFormed.isCoherent hh.isWellFormed.isClosedSubmanifold_N
  have hOZ : O≤Wide := fun z hz => (interior_subset hz).1
  let LJ := contactMarkedKept J w H O
  let LK := contactMarkedKept K w H O
  have hAll : ∀ (D : Set (CMfd.of (n:=n) O)) (z : O),
      LK.d*DivisorExponentAlong.divExpAlong n LJ.N LJ.ideal D z =
        LJ.d*DivisorExponentAlong.divExpAlong n LK.N LK.ideal D z := by
    intro D z
    let S : Set Y := (Subtype.val : O→Y) '' D
    let zw : Wide := ⟨z.val,hOZ z.property⟩
    have hh := hExp ((Subtype.val : Wide→Y) ⁻¹' S) zw
    change GK.d*DivisorExponentAlong.divExpAlong n
      (MarkedIdeal.pullback (Subtype.val : Wide→Y) GJ).N
      (MarkedIdeal.pullback (Subtype.val : Wide→Y) GJ).ideal _ zw =
      GJ.d*DivisorExponentAlong.divExpAlong n
      (MarkedIdeal.pullback (Subtype.val : Wide→Y) GK).N
      (MarkedIdeal.pullback (Subtype.val : Wide→Y) GK).ideal _ zw at hh
    rw [exponent_open GJ hCoherentJ Wide zw S,exponent_open GK hCoherentK Wide zw S] at hh
    have hD : (Subtype.val : O→Y) ⁻¹' S = D := Set.preimage_image_eq _ Subtype.val_injective
    rw [←hD,exponent_open GJ hCoherentJ O z S,exponent_open GK hCoherentK O z S]
    exact hh
  refine ⟨hyO,hLJ,hLK,hOwn,hLN,hLE,hLJd,hLKd,hLJLen,hLKLen,hAll,?_,hLocal⟩
  change ∀ (z : O) (i : ℕ), LK.d*MonomialCaseAlong.expDataAlong n LJ.N LJ.ideal LJ.E z i =
    LJ.d*MonomialCaseAlong.expDataAlong n LK.N LK.ideal LK.E z i
  intro z i
  by_cases hi : i<LJ.E.length
  · have hiK : i<LK.E.length := by rw [←hLE];exact hi
    have hGet : LJ.E.get ⟨i,hi⟩ = LK.E.get ⟨i,hiK⟩ := by
      simpa only [List.get_eq_getElem] using getElem_congr hLE rfl hi
    simpa only [MonomialCaseAlong.expDataAlong,dif_pos hi,dif_pos hiK,hGet] using hAll (LJ.E.get ⟨i,hi⟩) z
  · have hiK : ¬i<LK.E.length := by rw [←hLE];exact hi
    simp only [MonomialCaseAlong.expDataAlong,dif_neg hi,dif_neg hiK,Nat.mul_zero]

end
end Hironaka.HironakaActualOriginalInitialCommonMaskExponents
