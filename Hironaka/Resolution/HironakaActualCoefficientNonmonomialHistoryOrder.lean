import Hironaka.Resolution.HironakaActualOldDivisorExponentTransport
import Hironaka.Invariant.MonomialCaseAlong

/-! Whole actual proper-carrier factor/order arithmetic, and raw order of the
ORIGINAL coefficient history. Blueprint FIRST. No ambient power equality of
saturated along-parts; no current coefficient reset or full suffix/CAN claim. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualCoefficientNonmonomialHistoryOrder
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan InvertibleIdealQuotient GermIdealOrder IdealWeightPowers
  DivisorExponentAlong MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal MonomialPartAlong
  MonomialPart MonomialCase MonomialCaseAlong MonomialInvariant BoundaryCount
  BlowupFlatCoordinates GiraudAlong OrderTaylor SimultaneousNormalCrossings
  CompanionReductionAlong NonmonomialOrderLocal NonmonomialOrderRegime StepOneRegime
  ResolutionInvariantSpec InvDomainTowerAlong HomogenizedIdealAlong HomogenizedIdealAlongTower
  CoefficientIdeal HironakaSharpOriginalProductTraceOrder
  HironakaActualOldDivisorExponentTransport HironakaActualOriginalCoefficientHistoryAlong

variable {n : ℕ} {X Y : CMfd.{0} n}

private theorem hol {I : GermIdeal n X} (hI : I.IsCoherent) :
    ∀x f,I.mem x f→HolomorphicAt n f x :=
  fun _ _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem hI hf

private theorem monomial_sharp (hn : 0<n) (S : MarkedIdeal n X) (hS : S.IsWellFormed)
    (hne : ∀y∈S.N,IsNonzeroAlongAt S.N S.ideal y) (x : X) (hx : x∈S.N) :
    let s:=∑i∈memberIdx S.E x,expDataAlong n S.N S.ideal S.E x i
    x∈cosupport n S.N (monomialPartAlong n S.N S.ideal S.E) s ∧
      x∉cosupport n S.N (monomialPartAlong n S.N S.ideal S.E) (s+1) := by
  obtain ⟨kC,kN,Φ,σ,hΦsrc,hσk,hσinj,hflat⟩:=
    SimultaneousNormalCrossings.isAdaptedAt_of_hasNormalCrossings hn subset_rfl
      hS.isSNCDivisor hS.isTransverse hS.isTransverse.hasNormalCrossings hx
  have hNflat : ∀{z : X},z∈(chartAt (ComplexModel n) x).source→
      chartAt (ComplexModel n) x z∈Φ.source→
      (z∈S.N↔Φ.toFun (chartAt (ComplexModel n) x z)∈complexCoordinatePlane n kN):=
    fun hz1 hz2=>(hflat hz1 hz2).2.1
  have hA : ∀i,x∈S.E.get i→∀{z : X},z∈(chartAt (ComplexModel n) x).source→
      chartAt (ComplexModel n) x z∈Φ.source→
      (z∈S.E.get i↔Φ.toFun (chartAt (ComplexModel n) x z) (σ i)=0):=
    fun i hi _ hz1 hz2=>(hflat hz1 hz2).2.2 i hi
  let T : Finset (Fin S.E.length):=Finset.univ.filter fun i=>x∈S.E.get i
  let a : Fin S.E.length→ℕ:=fun i=>divExpAlong n S.N S.ideal (S.E.get i) x
  let m : X→ℂ:=fun z=>∏i∈T,flatCoord Φ (σ i) z^a i
  have hxD : x∈flatDomain Φ:=mem_flatDomain_self Φ
  have hSum : (∑i∈memberIdx S.E x,expDataAlong n S.N S.ideal S.E x i)=∑i∈T,a i := by
    rw [memberIdx,Finset.sum_map]
    refine Finset.sum_congr rfl fun i _=>?_
    simp only [Fin.valEmbedding_apply,expDataAlong,dif_pos i.2,Fin.eta]
    rfl
  change (x∈cosupport n S.N (monomialPartAlong n S.N S.ideal S.E)
      (∑i∈memberIdx S.E x,expDataAlong n S.N S.ideal S.E x i)) ∧ _
  rw [hSum]
  have hZero : ∀i∈T,flatCoord Φ (σ i) x=0:=fun i hi=>
    (hA i (Finset.mem_filter.mp hi).2 hxD.1 hxD.2).mp (Finset.mem_filter.mp hi).2
  obtain ⟨hMem,hNot⟩:=MonomialCase.prod_flatCoord_pow_order Φ σ a hxD T hZero
  have hGen:=(monomialPartAlong_mem_iff hΦsrc hNflat hA hn hS.isClosedSubmanifold_N
    hS.isSNCDivisor hS.isTransverse hS.isCoherent hne hx hσk hσinj).self_of_nhds
  have hR : IsLocalRetraction n S.N (flatRetract Φ kN) x:=
    isLocalRetraction_flatRetract hΦsrc hNflat hxD hx
  have hMR : m∘flatRetract Φ kN=ᶠ[𝓝 x] m := by
    have h:=(eventually_all_finset T).mpr fun i hi=>
      eventually_flatMap_flatRetract hΦsrc hNflat hxD hx (hσk i (Finset.mem_filter.mp hi).2)
    filter_upwards [h] with z hz
    simp only [Function.comp,m]
    exact Finset.prod_congr rfl fun i hi=>by
      rw [show flatCoord Φ (σ i) (flatRetract Φ kN z)=
        flatMap Φ (flatRetract Φ kN z) (σ i) from rfl,(hz i hi).2]
      rfl
  have hOrd (q : ℕ) : VanishesToOrderOn n S.N x q m↔(idealPow (pointIdeal n x) q).mem x m:=
    hR.vanishesToOrderOn_iff.trans
      ⟨fun h=>mem_idealPow_congr h hMR,fun h=>mem_idealPow_congr h hMR.symm⟩
  have hMh : HolomorphicAt n m x:=holomorphicAt_generator T a hxD
  have hMM : (monomialPartAlong n S.N S.ideal S.E).mem x m:=
    (hGen m).mpr ⟨hMh,isInSpanOnAt_eq_iff.mpr ⟨fun _=>1,holomorphicAt_const 1,
      Eventually.of_forall fun z _=>(one_mul (m z)).symm⟩⟩
  refine ⟨⟨hx,fun g hg=>?_⟩,fun hHigh=>hNot ((hOrd _).mp (hHigh.2 m hMM))⟩
  obtain ⟨_hg,hgm⟩:=(hGen g).mp hg
  obtain ⟨c,hc,hgc⟩:=isInSpanOnAt_eq_iff.mp hgm
  exact ⟨fun z=>c z*m z,mul_mem_idealPow hc hMem,hgc⟩

private theorem order_from_sharp (N : Set X) (I : GermIdeal n X) (hI : I.IsCoherent)
    (x : X) (q : ℕ) (hGood : x∈cosupport n N I q) (hBad : x∉cosupport n N I (q+1)) :
    GermIdealOrder.order n N I x=(q : ℕ∞) := by
  apply le_antisymm
  · apply ENat.lt_natCast_add_one_iff.mp
    apply lt_of_not_ge
    intro h
    apply hBad
    exact ⟨hGood.1,(le_order_iff (hol hI x)).mp (by simpa only [Nat.cast_add,Nat.cast_one] using h)⟩
  · exact (le_order_iff (hol hI x)).mpr hGood.2

/-- The genuine WHOLE restricted factorization gives sharp total order
s+raw nmOrd. Both Nat ordinaryTraceOrder and ENat order are derived. -/
theorem whole_factor_order (hn : 0<n) (S : MarkedIdeal n X) (hS : S.IsWellFormed)
    (hne : ∀y∈S.N,IsNonzeroAlongAt S.N S.ideal y) (x : X) (hx : x∈S.N) :
    let s:=∑i∈memberIdx S.E x,expDataAlong n S.N S.ideal S.E x i
    let μ:=nmOrd S x
    x∈cosupport n S.N S.ideal (s+μ) ∧ x∉cosupport n S.N S.ideal (s+μ+1) ∧
      ordinaryTraceOrder S.N S.ideal x=s+μ ∧
      GermIdealOrder.order n S.N S.ideal x=((s+μ : ℕ) : ℕ∞) := by
  let s:=∑i∈memberIdx S.E x,expDataAlong n S.N S.ideal S.E x i
  let μ:=nmOrd S x
  obtain ⟨hM,hMNot⟩:=monomial_sharp hn S hS hne x hx
  have hMu : x∈cosupport n S.N (nonmonomialPartAlong n S.N S.ideal S.E) μ := by
    change x∈ordGe S μ
    exact (mem_ordGe_iff hS hne hx μ).mpr le_rfl
  have hMuNot : x∉cosupport n S.N (nonmonomialPartAlong n S.N S.ideal S.E) (μ+1) := by
    change x∉ordGe S (μ+1)
    intro h
    exact Nat.not_succ_le_self μ ((mem_ordGe_iff hS hne hx (μ+1)).mp h)
  have hForward:=MonomialPartAlong.restrictLe_mul_along hn hS.isClosedSubmanifold_N
    hS.isSNCDivisor hS.isTransverse hS.isCoherent hne
  have hReverse:=MonomialPartAlong.restrictLe_mul_along' (E:=S.E)
    hS.isClosedSubmanifold_N hS.isCoherent
  have hProduct:=IdealOrderArithmetic.inter_cosupport_subset_cosupport_mul s μ ⟨hM,hMu⟩
  have hGood : x∈cosupport n S.N S.ideal (s+μ):=
    cosupport_subset_of_restrictLe hForward (s+μ) hProduct
  have hBad : x∉cosupport n S.N S.ideal (s+μ+1) := by
    intro hHigh
    have hProdHigh:=cosupport_subset_of_restrictLe hReverse (s+μ+1) hHigh
    have hNM:=CompanionReductionAlong.mem_cosupport_of_mem_cosupport_mul_along
      (𝔟:=monomialPartAlong n S.N S.ideal S.E) (𝔠:=nonmonomialPartAlong n S.N S.ideal S.E)
      hS.isClosedSubmanifold_N.2 (fun _ _ hg=>hg.1) (fun _ _ hg=>hg.1)
      (show s≤s+μ+1 by omega) hProdHigh hMNot
    apply hMuNot
    have hSub : s+μ+1-s=μ+1:=by omega
    simpa only [hSub] using hNM
  have hNat : ordinaryTraceOrder S.N S.ideal x=s+μ := by
    apply Nat.le_antisymm
    · by_contra h
      apply hBad
      exact (ordinaryTraceOrder_cosupport_iff hS.isClosedSubmanifold_N hS.isCoherent hne hx (s+μ+1)).mpr
        (by omega)
    · exact (ordinaryTraceOrder_cosupport_iff hS.isClosedSubmanifold_N hS.isCoherent hne hx (s+μ)).mp hGood
  exact ⟨hGood,hBad,hNat,order_from_sharp S.N S.ideal hS.isCoherent x (s+μ) hGood hBad⟩

private theorem positive_dimension (S : MarkedIdeal n X) {k : ℕ} (hS : IsInvDomain k S)
    (x : X) (hx : x∈S.cosupp) : 0<n := by
  by_contra hn
  have hn0 : n=0:=by omega
  have h0 : IsInvDomain 0 S := {
    isWellFormed:=hS.isWellFormed
    dimLE:=by
      intro y hy
      obtain ⟨r,hr⟩:=hS.isWellFormed.isClosedSubmanifold_N.2 y hy
      have hrn:=hr.1
      exact ⟨r,by omega,hr⟩
    one_le_d:=hS.one_le_d
    isNonzeroAlongAt:=hS.isNonzeroAlongAt }
  rw [cosupp_eq_empty_of_dimLE_zero h0] at hx
  exact hx

/-- Literal RAW nonmonomial order of the ORIGINAL coefficient history,
derived only on the actual ORIGINAL current cosupport. -/
theorem original_coefficient_nonmonomial_order (Q : MarkedIdeal n X) {k : ℕ}
    (hQ : IsInvDomain k Q) (hEmpty : Q.E=[]) (T : BlowupTower X Y) (hT : IsGeoTestTower Q T)
    (y : Y) (hy : y∈(geoTransformAlong Q T).cosupp) :
    let e:=sumExp (fun j=>Q.d-j) Q.d 0
    nmOrd (geoTransformAlong (coeffMarkedAlong Q) T) y=e*nmOrd (geoTransformAlong Q T) y := by
  let e:=sumExp (fun j=>Q.d-j) Q.d 0
  let A:=geoTransformAlong Q T
  let B:=geoTransformAlong (coeffMarkedAlong Q) T
  have hA:=isInvDomain_geoTransformAlong hQ T hT
  obtain ⟨hB,hNB,hBE,_hLenA,_hLenB,hExps⟩:=original_coefficient_all_boundary_exponents Q hQ hEmpty T hT
  have hyN : y∈A.N:=hy.1
  have hyB : y∈B.N:=hNB.symm ▸ hyN
  have hn:=positive_dimension A hA y hy
  obtain ⟨_hGoodA,_hBadA,_hNatA,hOrderA⟩:=whole_factor_order hn A hA.isWellFormed hA.isNonzeroAlongAt y hyN
  obtain ⟨_hGoodB,_hBadB,_hNatB,hOrderB⟩:=whole_factor_order hn B hB.isWellFormed hB.isNonzeroAlongAt y hyB
  rw [hNB,hBE] at hOrderB
  let sA:=∑i∈memberIdx A.E y,expDataAlong n A.N A.ideal A.E y i
  let sB:=∑i∈memberIdx A.E y,expDataAlong n A.N B.ideal A.E y i
  have hExp (i : ℕ) : expDataAlong n A.N B.ideal A.E y i=e*expDataAlong n A.N A.ideal A.E y i := by
    by_cases hi : i<A.E.length
    · simpa only [expDataAlong,dif_pos hi] using hExps ⟨i,hi⟩ y hyN
    · simp only [expDataAlong,dif_neg hi,Nat.mul_zero]
  have hSum : sB=e*sA := by
    change (∑i∈memberIdx A.E y,expDataAlong n A.N B.ideal A.E y i)=
      e*(∑i∈memberIdx A.E y,expDataAlong n A.N A.ideal A.E y i)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _=>hExp i
  change GermIdealOrder.order n A.N A.ideal y=((sA+nmOrd A y : ℕ) : ℕ∞) at hOrderA
  change GermIdealOrder.order n A.N B.ideal y=((sB+nmOrd B y : ℕ) : ℕ∞) at hOrderB
  have hOrd:=original_coefficient_history_order_along Q hQ.isWellFormed.isClosedSubmanifold_N
    hQ.isWellFormed.isCoherent hQ.one_le_d T hT y hy
  change GermIdealOrder.order n A.N B.ideal y=(e : ℕ∞)*GermIdealOrder.order n A.N A.ideal y at hOrd
  rw [hOrderA,hOrderB] at hOrd
  have hNat : sB+nmOrd B y=e*(sA+nmOrd A y):=by exact_mod_cast hOrd
  rw [hSum,Nat.mul_add] at hNat
  exact Nat.add_left_cancel hNat

private theorem coefficient_regime (Q : MarkedIdeal n X) {k : ℕ}
    (hQ : IsInvDomain k Q) (hEmpty : Q.E=[]) (μ : ℕ)
    {Y : CMfd.{0} n} (T : BlowupTower X Y) (hT : IsGeoTestTower Q T) (y : Y) :
    let e:=sumExp (fun j=>Q.d-j) Q.d 0
    OrdRegime (coeffMarkedAlong Q) (e*μ) T y↔OrdRegime Q μ T y := by
  let e:=sumExp (fun j=>Q.d-j) Q.d 0
  have hd:=hQ.one_le_d
  have he : 1≤e:=one_le_sumExp (fun j hj=>by omega) 0
  have he0 : e≠0:=by omega
  have hCos:=(coeffAlong_tower Q hQ.isWellFormed.isClosedSubmanifold_N
    hQ.isWellFormed.isCoherent hQ.one_le_d T).2 hT
  constructor
  · rintro ⟨hyB,hValue⟩
    have hyA : y∈(geoTransformAlong Q T).cosupp:=hCos ▸ hyB
    have hRaw:=original_coefficient_nonmonomial_order Q hQ hEmpty T hT y hyA
    have hMul : e*nmOrd (geoTransformAlong Q T) y=e*μ:=hRaw.symm.trans hValue
    exact ⟨hyA,mul_left_cancel₀ he0 hMul⟩
  · rintro ⟨hyA,hValue⟩
    refine ⟨hCos.symm ▸ hyA,?_⟩
    have hRaw:=original_coefficient_nonmonomial_order Q hQ hEmpty T hT y hyA
    rw [hRaw,hValue]

private theorem coefficient_runs (Q : MarkedIdeal n X) {k : ℕ}
    (hQ : IsInvDomain k Q) (hEmpty : Q.E=[]) (μ : ℕ) :
    {Y : CMfd.{0} n}→(T : BlowupTower X Y)→IsGeoTestTower Q T→∀y : Y,
      regimeRun (OrdRegime (coeffMarkedAlong Q) (sumExp (fun j=>Q.d-j) Q.d 0*μ)) T y=
        regimeRun (OrdRegime Q μ) T y
  | _,.refl,_hT,_y=>rfl
  | _,.step T C π hπ,hT,y=>by
    rw [regimeRun_step,regimeRun_step]
    have hIff:=coefficient_regime Q hQ hEmpty μ T hT.1 (π y)
    by_cases h : OrdRegime Q μ T (π y)
    · rw [if_pos (hIff.mpr h),if_pos h,coefficient_runs Q hQ hEmpty μ T hT.1 (π y)]
    · rw [if_neg (fun hB=>h (hIff.mp hB)),if_neg h]

/-- Actual ORIGINAL raw-order regimes and native trailing runs coincide on
the SAME given test, including empty steps; no future suffix is assumed. -/
theorem original_coefficient_order_runs (Q : MarkedIdeal n X) {k : ℕ}
    (hQ : IsInvDomain k Q) (hEmpty : Q.E=[]) (μ : ℕ)
    (T : BlowupTower X Y) (hT : IsGeoTestTower Q T) (y : Y) :
    let e:=sumExp (fun j=>Q.d-j) Q.d 0
    (OrdRegime (coeffMarkedAlong Q) (e*μ) T y↔OrdRegime Q μ T y) ∧
      regimeRun (OrdRegime (coeffMarkedAlong Q) (e*μ)) T y=regimeRun (OrdRegime Q μ) T y :=
  ⟨coefficient_regime Q hQ hEmpty μ T hT y,coefficient_runs Q hQ hEmpty μ T hT y⟩

end
end Hironaka.HironakaActualCoefficientNonmonomialHistoryOrder
