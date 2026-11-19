import Hironaka.Resolution.HironakaActualCoefficientNonmonomialHistoryOrder
import Hironaka.Resolution.HironakaActualInitialNonmonomialCoefficientBoundary

/-! SAME original lower mask and actual normalized companion TEST histories.
The genuine mu>=literal d is derived from the original lower construction.
No coefficient reset, global raw scaling, alternate window or CAN conclusion.
Blueprint FIRST: hironaka-actual-original-true-mark-mask-companions.tex. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualOriginalTrueMarkMaskCompanions
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan GermIdealOrder IdealWeightPowers DivisorExponentAlong
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal MarkedIdealEquivalence.MarkedIdeal
  MarkedIdealRestrictOpen MarkedIdealBiholomorphism BlowupExceptionalDivisor BlowupStrictSubmanifold
  HomogenizedIdealAlong HomogenizedIdealAlongTower CoefficientIdeal
  CompanionReductionAlong CompanionRebase CompanionOpen InvDomainCompanion InvDomainTowerAlong
  NonmonomialOrderLocal NonmonomialOrderTail NonmonomialOrderRegime StepOneRegime
  ResolutionInvariantSpec StepOneValue StepOneValueMasked GeneralValue HironakaEmbeddedAnalytic
  MonomialCase MonomialCaseAlong
  HironakaActualOriginalCoefficientHistoryAlong HironakaActualOldDivisorExponentTransport
  HironakaActualCoefficientNonmonomialHistoryOrder HironakaActualInitialNonmonomialCoefficientBoundary

variable {n : ℕ} {X Y : CMfd.{0} n}

private theorem coefficient_mark (Q : MarkedIdeal n X) {k : ℕ} (hQ : IsInvDomain k Q) :
    (coeffMarkedAlong Q).d=Q.d*sumExp (fun j=>Q.d-j) Q.d 0 := by
  change (Finset.range Q.d).prod (fun j=>(derivMarkedAlong Q j).d)=_
  simpa only [derivMarkedAlong_d,Nat.sub_zero] using
    (mul_sumExp (fun j=>Q.d-j) (show 0<Q.d from hQ.one_le_d) (i:=0)).symm

private theorem high_subset_cosupp (hn : 0<n) (S : MarkedIdeal n X)
    (hS : S.IsWellFormed) (hne : ∀y∈S.N,IsNonzeroAlongAt S.N S.ideal y)
    (r : ℕ) (hdr : S.d≤r) : ordGe S r⊆S.cosupp := by
  intro y hy
  have hRaw : r≤nmOrd S y:=(mem_ordGe_iff hS hne hy.1 r).mp hy
  obtain ⟨hGood,_hBad,_hNat,_hOrder⟩:=whole_factor_order hn S hS hne y hy.1
  let s:=∑i∈memberIdx S.E y,expDataAlong n S.N S.ideal S.E y i
  change y∈cosupport n S.N S.ideal (s+nmOrd S y) at hGood
  exact cosupport_anti (by omega : S.d≤s+nmOrd S y) hGood

private theorem coefficient_high_set (hn : 0<n) (Q : MarkedIdeal n X) {k : ℕ}
    (hQ : IsInvDomain k Q) (hEmpty : Q.E=[]) (μ : ℕ) (hμ : Q.d≤μ) :
    let e:=sumExp (fun j=>Q.d-j) Q.d 0
    ordGe (coeffMarkedAlong Q) (e*μ+1)=ordGe Q (μ+1) := by
  let e:=sumExp (fun j=>Q.d-j) Q.d 0
  have hd:=hQ.one_le_d
  have he : 1≤e:=one_le_sumExp (fun j hj=>by omega) 0
  have hC:=coefficient_isInvDomain Q hQ
  have hCos : (coeffMarkedAlong Q).cosupp=Q.cosupp:=
    (coeffAlong_tower Q hQ.isWellFormed.isClosedSubmanifold_N hQ.isWellFormed.isCoherent
      hQ.one_le_d (.refl : BlowupTower X X)).2 trivial
  have hMarkC : (coeffMarkedAlong Q).d≤e*μ+1 := by
    rw [coefficient_mark Q hQ]
    calc
      Q.d*e=e*Q.d:=Nat.mul_comm _ _
      _≤e*μ:=Nat.mul_le_mul_left e hμ
      _≤e*μ+1:=Nat.le_succ _
  ext y
  constructor
  · intro hy
    have hyC:=high_subset_cosupp hn (coeffMarkedAlong Q) hC.isWellFormed
      hC.isNonzeroAlongAt (e*μ+1) hMarkC hy
    have hyQ : y∈Q.cosupp:=hCos ▸ hyC
    have hRaw:=original_coefficient_nonmonomial_order Q hQ hEmpty
      (.refl : BlowupTower X X) trivial y hyQ
    change nmOrd (coeffMarkedAlong Q) y=e*nmOrd Q y at hRaw
    have hValue:=(mem_ordGe_iff hC.isWellFormed hC.isNonzeroAlongAt hy.1 (e*μ+1)).mp hy
    rw [hRaw] at hValue
    apply (mem_ordGe_iff hQ.isWellFormed hQ.isNonzeroAlongAt hyQ.1 (μ+1)).mpr
    by_contra h
    have hLe:=Nat.mul_le_mul_left e (show nmOrd Q y≤μ by omega)
    omega
  · intro hy
    have hyQ:=high_subset_cosupp hn Q hQ.isWellFormed hQ.isNonzeroAlongAt
      (μ+1) (by omega) hy
    have hRaw:=original_coefficient_nonmonomial_order Q hQ hEmpty
      (.refl : BlowupTower X X) trivial y hyQ
    change nmOrd (coeffMarkedAlong Q) y=e*nmOrd Q y at hRaw
    have hValue:=(mem_ordGe_iff hQ.isWellFormed hQ.isNonzeroAlongAt hy.1 (μ+1)).mp hy
    apply (mem_ordGe_iff hC.isWellFormed hC.isNonzeroAlongAt hy.1 (e*μ+1)).mpr
    rw [hRaw]
    calc
      e*μ+1≤e*μ+e:=Nat.add_le_add_left he _
      _=e*(μ+1):=by ring
      _≤e*nmOrd Q y:=Nat.mul_le_mul_left e hValue

private theorem coefficient_mask (hn : 0<n) (Q : MarkedIdeal n X) {k : ℕ}
    (hQ : IsInvDomain k Q) (hEmpty : Q.E=[]) (μ : ℕ) (hμ : Q.d≤μ) :
    ordMask Q μ=ordMask (coeffMarkedAlong Q) (sumExp (fun j=>Q.d-j) Q.d 0*μ) := by
  apply Opens.ext
  change (closure (ordGe Q (μ+1)))ᶜ=
    (closure (ordGe (coeffMarkedAlong Q) (sumExp (fun j=>Q.d-j) Q.d 0*μ+1)))ᶜ
  rw [coefficient_high_set hn Q hQ hEmpty μ hμ]

private theorem scaled_cut (Q : MarkedIdeal n X) {k : ℕ}
    (hQ : IsInvDomain k Q) (hEmpty : Q.E=[]) (μ : ℕ)
    (T : BlowupTower X Y) (hT : IsGeoTestTower Q T) :
    let e:=sumExp (fun j=>Q.d-j) Q.d 0
    let A:=geoTransformAlong Q T
    let B:=geoTransformAlong (coeffMarkedAlong Q) T
    ordGe B (e*μ)∩B.cosupp=ordGe A μ∩A.cosupp := by
  let e:=sumExp (fun j=>Q.d-j) Q.d 0
  let A:=geoTransformAlong Q T
  let B:=geoTransformAlong (coeffMarkedAlong Q) T
  have hd:=hQ.one_le_d
  have he : 1≤e:=one_le_sumExp (fun j hj=>by omega) 0
  have hA:=isInvDomain_geoTransformAlong hQ T hT
  obtain ⟨hB,_hNB,_hBE,_hLenA,_hLenB,_hExps⟩:=
    original_coefficient_all_boundary_exponents Q hQ hEmpty T hT
  have hCos:=(coeffAlong_tower Q hQ.isWellFormed.isClosedSubmanifold_N
    hQ.isWellFormed.isCoherent hQ.one_le_d T).2 hT
  ext y
  constructor
  · rintro ⟨hyB,hyBCos⟩
    have hyA : y∈A.cosupp:=hCos ▸ hyBCos
    refine ⟨?_,hyA⟩
    have hRaw:=original_coefficient_nonmonomial_order Q hQ hEmpty T hT y hyA
    have hValue:=(mem_ordGe_iff hB.isWellFormed hB.isNonzeroAlongAt hyB.1 (e*μ)).mp hyB
    change e*μ≤nmOrd B y at hValue
    change nmOrd B y=e*nmOrd A y at hRaw
    rw [hRaw] at hValue
    apply (mem_ordGe_iff hA.isWellFormed hA.isNonzeroAlongAt hyA.1 μ).mpr
    by_contra h
    change ¬μ≤nmOrd A y at h
    have hLT : nmOrd A y<μ:=by omega
    have hProd:=Nat.mul_lt_mul_of_pos_left hLT (show 0<e from he)
    omega
  · rintro ⟨hyA,hyACos⟩
    have hyB : y∈B.cosupp:=hCos.symm ▸ hyACos
    refine ⟨?_,hyB⟩
    have hRaw:=original_coefficient_nonmonomial_order Q hQ hEmpty T hT y hyACos
    have hValue:=(mem_ordGe_iff hA.isWellFormed hA.isNonzeroAlongAt hyA.1 μ).mp hyA
    apply (mem_ordGe_iff hB.isWellFormed hB.isNonzeroAlongAt hyB.1 (e*μ)).mpr
    change nmOrd B y=e*nmOrd A y at hRaw
    rw [hRaw]
    exact Nat.mul_le_mul_left e hValue

private theorem companions_wEquiv (hn : 0<n) (Q : MarkedIdeal n X) {k : ℕ}
    (hQ : IsInvDomain k Q) (hEmpty : Q.E=[]) (μ : ℕ) (hμ : 1≤μ)
    (hBound : ∀y∈Q.cosupp,y∉ordGe Q (μ+1))
    (hCBound : ∀y∈(coeffMarkedAlong Q).cosupp,
      y∉ordGe (coeffMarkedAlong Q) (sumExp (fun j=>Q.d-j) Q.d 0*μ+1)) :
    WEquiv (companionOf n Q μ)
      (companionOf n (coeffMarkedAlong Q) (sumExp (fun j=>Q.d-j) Q.d 0*μ)) := by
  let e:=sumExp (fun j=>Q.d-j) Q.d 0
  let J:=companionOf n Q μ
  let K:=companionOf n (coeffMarkedAlong Q) (e*μ)
  have hd:=hQ.one_le_d
  have he : 1≤e:=one_le_sumExp (fun j hj=>by omega) 0
  have heμ : 1≤e*μ:=Nat.mul_pos he hμ
  have hC:=coefficient_isInvDomain Q hQ
  have hE : J.E=K.E:=by
    simp only [J,K,companionAlong_E]
    rfl
  have hCuts {Y : CMfd.{0} n}(T : BlowupTower X Y)
      (hJT : IsGeoTestTower J T)(hKT : IsGeoTestTower K T) :
      (geoTransformAlong J T).cosupp=(geoTransformAlong K T).cosupp := by
    have hQT:=(companionOf_tower_facts hn hQ hμ hBound T hJT).1
    rw [cosupp_companionOf_geoTransformAlong hn hQ hμ hBound T hJT,
      cosupp_companionOf_geoTransformAlong hn hC heμ hCBound T hKT]
    exact (scaled_cut Q hQ hEmpty μ T hQT).symm
  have hTests : ∀{Y : CMfd.{0} n}(T : BlowupTower X Y),IsGeoTestTower J T↔IsGeoTestTower K T := by
    intro Y T
    induction T with
    | refl=>exact Iff.rfl
    | step T C π hπ ih=>
      change (IsGeoTestTower J T ∧ (geoTransformAlong J T).IsAdmissibleCentre C)↔
        (IsGeoTestTower K T ∧ (geoTransformAlong K T).IsAdmissibleCentre C)
      constructor
      · rintro ⟨hJT,hCJ⟩
        have hKT:=ih.mp hJT
        refine ⟨hKT,?_⟩
        have hCos:=hCuts T hJT hKT
        have hET:=E_geoTransformAlong_eq hE T
        simpa only [IsAdmissibleCentre,←hCos,←hET] using hCJ
      · rintro ⟨hKT,hCK⟩
        have hJT:=ih.mpr hKT
        refine ⟨hJT,?_⟩
        have hCos:=hCuts T hJT hKT
        have hET:=E_geoTransformAlong_eq hE T
        simpa only [IsAdmissibleCentre,hCos,hET] using hCK
  exact ⟨hE,fun T=>⟨hTests T,fun hJT=>hCuts T hJT ((hTests T).mp hJT)⟩⟩

private theorem same_carrier {P Q : MarkedIdeal n X} (hN : P.N=Q.N) :
    {Y : CMfd.{0} n}→(T : BlowupTower X Y)→(geoTransformAlong P T).N=(geoTransformAlong Q T).N
  | _,.refl=>hN
  | _,.step T C π _hπ=>congrArg (geoStrictTransform π C) (same_carrier hN T)

private theorem companion_mask_heq (Q : MarkedIdeal n X) (μ : ℕ) (U : Opens X)
    (hU : U=ordMask Q μ) :
    HEq (companionOf n (M:=CMfd.of (n:=n) U)
      (MarkedIdeal.pullback (Subtype.val : U→X) Q) μ)
      (compAt Q μ (.refl : BlowupTower X X)) := by
  cases hU
  rfl

/-- The literal original lower record supplies its own genuine true mu and
EXACT global coefficient mask; no generic lower order bound is assumed. -/
theorem original_lower_true_mark_mask (hn : 0<n) (Q : MarkedIdeal n X)
    {k : ℕ}(hQ : IsInvDomain k Q) (hN : Q.N=univ) (hE : Q.E=[])
    (hMax : IsMaximalOrderAlong Q.N Q.ideal Q.d)
    (W : Set X)(hW : IsComplexAnalyticSubset (n:=n) W)
    (hSing : Q.cosupp⊆singularSet (n:=n) W)(a : X)(ha : a∈Q.cosupp) :
    ∃hm : a∈maskB Q (.refl : BlowupTower X X) a,
      let L : MarkedIdeal n (CMfd.of (n:=n) (maskB Q (.refl : BlowupTower X X) a)):=
        lowerMarkedB Q (.refl : BlowupTower X X) a
      let x : maskB Q (.refl : BlowupTower X X) a:=⟨a,hm⟩
      let μ:=nmOrd L x
      let e:=sumExp (fun j=>L.d-j) L.d 0
      IsInvDomain (k-1) L ∧ L.E=[] ∧ x∈L.cosupp ∧ L.d≤μ ∧
        ordMask L μ=ordMask (coeffMarkedAlong L) (e*μ) := by
  obtain ⟨hm,hL,hEmpty,_hMark,hx,hμ,_hOrd,_hCoeff,_hHistories⟩:=
    original_lower_coefficient_history_along hn Q hQ hN hE hMax W hW hSing a ha
  exact ⟨hm,hL,hEmpty,hx,hμ,coefficient_mask hn _ hL hEmpty _ hμ⟩

/-- SAME native original mask, literal marks mu/e*mu, all actual normalized
companion tests/current cuts and every original raw-order trailing clock. -/
theorem original_lower_true_mark_companions (hn : 0<n) (Q : MarkedIdeal n X)
    {k : ℕ}(hQ : IsInvDomain k Q) (hN : Q.N=univ) (hE : Q.E=[])
    (hMax : IsMaximalOrderAlong Q.N Q.ideal Q.d)
    (W : Set X)(hW : IsComplexAnalyticSubset (n:=n) W)
    (hSing : Q.cosupp⊆singularSet (n:=n) W)(a : X)(ha : a∈Q.cosupp) :
    ∃hm : a∈maskB Q (.refl : BlowupTower X X) a,
      let V:=maskB Q (.refl : BlowupTower X X) a
      let L : MarkedIdeal n (CMfd.of (n:=n) V):=lowerMarkedB Q (.refl : BlowupTower X X) a
      let x : V:=⟨a,hm⟩
      let μ:=nmOrd L x
      let e:=sumExp (fun j=>L.d-j) L.d 0
      let U:=ordMask L μ
      let P : MarkedIdeal n (CMfd.of (n:=n) U):=MarkedIdeal.pullback (Subtype.val : U→V) L
      let B : MarkedIdeal n (CMfd.of (n:=n) U):=MarkedIdeal.pullback (Subtype.val : U→V) (coeffMarkedAlong L)
      let J:=companionOf n P μ
      let K:=companionOf n B (e*μ)
      x∈U ∧ U=ordMask (coeffMarkedAlong L) (e*μ) ∧ B=coeffMarkedAlong P ∧
      IsInvDomain (k-1) J ∧ IsInvDomain (k-1) K ∧
      IsMaximalOrderAlong J.N J.ideal J.d ∧ IsMaximalOrderAlong K.N K.ideal K.d ∧
      J.N=P.N ∧ K.N=P.N ∧ J.E=[] ∧ K.E=[] ∧ J.d=μ ∧ K.d=e*μ ∧
      HEq J (compAt L μ (.refl : BlowupTower (CMfd.of (n:=n) V) (CMfd.of (n:=n) V))) ∧
      HEq K (compAt (coeffMarkedAlong L) (e*μ)
        (.refl : BlowupTower (CMfd.of (n:=n) V) (CMfd.of (n:=n) V))) ∧
      WEquiv J K ∧
      ∀{Y : CMfd.{0} n}(T : BlowupTower (CMfd.of (n:=n) U) Y),IsGeoTestTower J T →
        IsGeoTestTower P T ∧ IsGeoTestTower B T ∧
        (geoTransformAlong J T).N=(geoTransformAlong K T).N ∧
        (geoTransformAlong J T).E=(geoTransformAlong K T).E ∧
        (geoTransformAlong J T).E.length=T.length ∧ (geoTransformAlong K T).E.length=T.length ∧
        (geoTransformAlong J T).cosupp=ordGe (geoTransformAlong P T) μ∩(geoTransformAlong P T).cosupp ∧
        (geoTransformAlong K T).cosupp=ordGe (geoTransformAlong B T) (e*μ)∩(geoTransformAlong B T).cosupp ∧
        ∀y : Y,(OrdRegime B (e*μ) T y↔OrdRegime P μ T y) ∧
          regimeRun (OrdRegime B (e*μ)) T y=regimeRun (OrdRegime P μ) T y := by
  obtain ⟨hm,hL,hEmpty,hx,hμ,hMask⟩:=
    original_lower_true_mark_mask hn Q hQ hN hE hMax W hW hSing a ha
  let V:=maskB Q (.refl : BlowupTower X X) a
  let L : MarkedIdeal n (CMfd.of (n:=n) V):=lowerMarkedB Q (.refl : BlowupTower X X) a
  let x : V:=⟨a,hm⟩
  let μ:=nmOrd L x
  let e:=sumExp (fun j=>L.d-j) L.d 0
  let U:=ordMask L μ
  let P : MarkedIdeal n (CMfd.of (n:=n) U):=MarkedIdeal.pullback (Subtype.val : U→V) L
  let B : MarkedIdeal n (CMfd.of (n:=n) U):=MarkedIdeal.pullback (Subtype.val : U→V) (coeffMarkedAlong L)
  let J:=companionOf n P μ
  let K:=companionOf n B (e*μ)
  change IsInvDomain (k-1) L at hL
  change L.E=[] at hEmpty
  change x∈L.cosupp at hx
  change L.d≤μ at hμ
  change U=ordMask (coeffMarkedAlong L) (e*μ) at hMask
  have hPos : 1≤μ:=hL.one_le_d.trans hμ
  have hd:=hL.one_le_d
  have he : 1≤e:=one_le_sumExp (fun j hj=>by omega) 0
  have heμ : 1≤e*μ:=Nat.mul_pos he hPos
  have hxU : x∈U:=(mem_ordMask_iff hn hL.isWellFormed hL.isNonzeroAlongAt μ x).mpr (by
    intro h
    have hBad:=(mem_ordGe_iff hL.isWellFormed hL.isNonzeroAlongAt hx.1 (μ+1)).mp h
    change μ+1≤μ at hBad
    omega)
  have hP : IsInvDomain (k-1) P:=isInvDomain_pullback_val U hL
  have hCL:=coefficient_isInvDomain L hL
  have hB : IsInvDomain (k-1) B:=isInvDomain_pullback_val U hCL
  have hNatural : B=coeffMarkedAlong P:=pullback_val_coeffMarkedAlong U L
    hL.isWellFormed.isCoherent hL.isWellFormed.isClosedSubmanifold_N hL.one_le_d
  have hPE : P.E=[]:=by
    change L.E.map ((Subtype.val : U→V) ⁻¹' ·)=[]
    rw [hEmpty,List.map_nil]
  have hBE : B.E=[]:=by
    change L.E.map ((Subtype.val : U→V) ⁻¹' ·)=[]
    rw [hEmpty,List.map_nil]
  have hBoundP : ∀z∈P.cosupp,z∉ordGe P (μ+1):=
    bound_pullback_val hn hL.isWellFormed hL.isNonzeroAlongAt U
      (fun _ _ hz=>notMem_ordGe_of_mem_ordMask hz)
  have hBoundB : ∀z∈B.cosupp,z∉ordGe B (e*μ+1):=
    bound_pullback_val hn hCL.isWellFormed hCL.isNonzeroAlongAt U
      (fun z _ hz=>notMem_ordGe_of_mem_ordMask (show z∈ordMask (coeffMarkedAlong L) (e*μ) from hMask ▸ hz))
  have hBoundC : ∀z∈(coeffMarkedAlong P).cosupp,z∉ordGe (coeffMarkedAlong P) (e*μ+1):=by
    rw [←hNatural]
    exact hBoundB
  have hJ : IsInvDomain (k-1) J:=isInvDomain_companionAlong hn hP hPos
  have hK : IsInvDomain (k-1) K:=isInvDomain_companionAlong hn hB heμ
  have hJN : J.N=P.N:=companionAlong_N _ _ _ _ _ _
  have hKN : K.N=P.N:=companionAlong_N _ _ _ _ _ _
  have hJE : J.E=[]:=by simpa only [J,companionAlong_E] using hPE
  have hKE : K.E=[]:=by simpa only [K,companionAlong_E] using hBE
  have hJMax : IsMaximalOrderAlong J.N J.ideal J.d:=by
    rw [hJN]
    exact isMaximalOrderAlong_companionOf hn hP.isWellFormed hP.isNonzeroAlongAt hBoundP
  have hKMax : IsMaximalOrderAlong K.N K.ideal K.d:=by
    rw [show K.N=B.N from companionAlong_N _ _ _ _ _ _]
    exact isMaximalOrderAlong_companionOf hn hB.isWellFormed hB.isNonzeroAlongAt hBoundB
  have hMarkB : B.d=L.d*e:=coefficient_mark L hL
  have hBMu : B.d≤e*μ:=by
    rw [hMarkB,Nat.mul_comm L.d e]
    exact Nat.mul_le_mul_left e hμ
  have hJd : J.d=μ:=by
    rw [companionAlong_d,if_neg (Nat.not_lt.mpr (show P.d≤μ from hμ))]
  have hKd : K.d=e*μ:=by
    rw [companionAlong_d,if_neg (Nat.not_lt.mpr hBMu)]
  have hWeak : WEquiv J K:=by
    change WEquiv (companionOf n P μ) (companionOf n B (e*μ))
    rw [hNatural]
    exact companions_wEquiv hn P hP hPE μ hPos hBoundP hBoundC
  refine ⟨hm,hxU,hMask,hNatural,hJ,hK,hJMax,hKMax,hJN,hKN,hJE,hKE,hJd,hKd,
    ?_,?_,hWeak,?_⟩
  · rfl
  · exact companion_mask_heq (coeffMarkedAlong L) (e*μ) U hMask
  · intro Y T hJT
    have hKT:=(hWeak.2 T).1.mp hJT
    have hPT:=(companionOf_tower_facts hn hP hPos hBoundP T hJT).1
    have hBT:=(companionOf_tower_facts hn hB heμ hBoundB T hKT).1
    refine ⟨hPT,hBT,same_carrier (hJN.trans hKN.symm) T,E_geoTransformAlong_eq hWeak.1 T,
      ?_,?_,cosupp_companionOf_geoTransformAlong hn hP hPos hBoundP T hJT,
      cosupp_companionOf_geoTransformAlong hn hB heμ hBoundB T hKT,?_⟩
    · rw [length_E_geoTransformAlong,hJE,List.length_nil,Nat.zero_add]
    · rw [length_E_geoTransformAlong,hKE,List.length_nil,Nat.zero_add]
    · intro y
      change (OrdRegime B (e*μ) T y↔OrdRegime P μ T y) ∧
        regimeRun (OrdRegime B (e*μ)) T y=regimeRun (OrdRegime P μ) T y
      rw [hNatural]
      exact original_coefficient_order_runs P hP hPE μ T hPT y

end
end Hironaka.HironakaActualOriginalTrueMarkMaskCompanions
