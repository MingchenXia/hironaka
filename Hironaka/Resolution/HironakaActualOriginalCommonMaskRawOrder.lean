import Hironaka.Resolution.HironakaActualOriginalContactBoundaryExponentScaling
import Hironaka.Resolution.HironakaMonomialBlowup
import Hironaka.Invariant.ContactStageInvDomain

/-! Actual native common K-mask kept lower domains, then finite WHOLE factor/raw
cancellation. Blueprint FIRST. All cuts/exponents/domains are derived in the
ordinary original-source endpoint. No future local lower history or CAN packet. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff BigOperators
namespace Hironaka.HironakaActualOriginalCommonMaskRawOrder
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan GermIdealOrder DivisorExponentAlong
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal MarkedIdealOperationsTransform
  MarkedIdealEquivalence.MarkedIdeal HomogenizedGlueingTower HomogenizedIdealAlong
  HomogenizedIdealAlongTower ContactStageKept ContactStageInvDomain
  CoefficientIdeal CoefficientIdealRestriction ContactIndependenceAlong
  GermIdealPullbackCalculus BlowupTowers BlowupTowerTransforms
  ResolutionInvariantSpec StepOneValue StepOneValueMasked StepOneLowerDomain
  TangentDirectionAlong CodimOneSupportAlong NonmonomialOrderLocal NonmonomialOrderTail
  CompanionRebase CompanionReductionAlong CompanionOpen MonomialPartAlong MonomialInvariant MonomialCase MonomialCaseAlong
  HironakaEmbeddedAnalytic HironakaActualOriginalTrueMarkMaskCompanions
  HironakaActualTrueMarkCommonContact HironakaActualOriginalStrictContactWeightedOrder
  HironakaActualOriginalHistoricalBarWeightedThreshold HironakaActualCoefficientNonmonomialHistoryOrder
  HironakaActualOriginalContactBoundaryExponentScaling HironakaMonomialBlowup

variable {n : ℕ} {X Y : CMfd.{0} n}

private theorem hol {Z : CMfd.{0} n} {I : GermIdeal n Z} (hI : I.IsCoherent) :
    ∀x f,I.mem x f→HolomorphicAt n f x := fun _ _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem hI hf

private theorem bar_test (M : MarkedIdeal n X) {k : ℕ} (hM : IsInvDomain k M)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T) : IsGeoTestTower (barMarked M) T :=
  ((coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d).2 T).1.mpr hT

private theorem bar_geometry (J K : MarkedIdeal n X) {k : ℕ}
    (hJ : IsInvDomain k J) (hK : IsInvDomain k K) (hN : J.N=K.N) (hWeak : WEquiv J K)
    (T : BlowupTower X Y) (hTJ : IsGeoTestTower J T) :
    IsGeoTestTower K T ∧
    (geoTransformAlong (barMarked J) T).N=(geoTransformAlong (barMarked K) T).N ∧
    (geoTransformAlong (barMarked J) T).cosupp=(geoTransformAlong (barMarked K) T).cosupp ∧
    codimOnePartAlong (geoTransformAlong (barMarked J) T).N
      (geoTransformAlong (barMarked J) T).ideal (geoTransformAlong (barMarked J) T).d=
    codimOnePartAlong (geoTransformAlong (barMarked K) T).N
      (geoTransformAlong (barMarked K) T).ideal (geoTransformAlong (barMarked K) T).d := by
  have hTK:=(hWeak.2 T).1.mp hTJ
  have hNJ : (geoTransformAlong (barMarked J) T).N=(geoTransformAlong (barMarked K) T).N:=by
    rw [N_geoTransformAlong,N_geoTransformAlong]
    change strictAlong T J.N=strictAlong T K.N
    rw [hN]
  have hCos : (geoTransformAlong (barMarked J) T).cosupp=(geoTransformAlong (barMarked K) T).cosupp:=by
    calc
      _=(geoTransformAlong J T).cosupp:=
        ((coeff_homAlong_wEquiv J hJ.isWellFormed.isClosedSubmanifold_N
          hJ.isWellFormed.isCoherent hJ.one_le_d).2 T).2 (bar_test J hJ T hTJ)
      _=(geoTransformAlong K T).cosupp:=(hWeak.2 T).2 hTJ
      _=_:=((coeff_homAlong_wEquiv K hK.isWellFormed.isClosedSubmanifold_N
          hK.isWellFormed.isCoherent hK.one_le_d).2 T).2 (bar_test K hK T hTK) |>.symm
  refine ⟨hTK,hNJ,hCos,?_⟩
  unfold codimOnePartAlong
  change {z | ∃s,RegularAtDim (n:=n) (geoTransformAlong (barMarked J) T).N z (s+1) ∧
    RegularAtDim (n:=n) (geoTransformAlong (barMarked J) T).cosupp z s}=_
  rw [hNJ,hCos]
  rfl

private theorem common_mask_domains (J K : MarkedIdeal n X) {k : ℕ}
    (hJ : IsInvDomain k J) (hK : IsInvDomain k K) (hN : J.N=K.N)
    (hJE : J.E=[]) (hKE : K.E=[]) (hWeak : WEquiv J K)
    (hMaxK : IsMaximalOrderAlong K.N K.ideal K.d)
    (T : BlowupTower X Y) (hTJ : IsGeoTestTower J T) (y₀ : Y)
    (hy : y₀∈(geoTransformAlong (barMarked K) T).cosupp)
    (hZ : y₀∉codimOnePartAlong (geoTransformAlong (barMarked K) T).N
      (geoTransformAlong (barMarked K) T).ideal (geoTransformAlong (barMarked K) T).d)
    (huJ : IsTangentDirectionAlong J.N J.ideal J.d (tangentChoice K (T.proj y₀)).1
      (tangentChoice K (T.proj y₀)).2) :
    y₀∈maskB K T y₀ ∧
    IsInvDomain (k-1) (contactMarkedKept J (tangentChoice K (T.proj y₀)).2 T (maskB K T y₀)) ∧
    IsInvDomain (k-1) (contactMarkedKept K (tangentChoice K (T.proj y₀)).2 T (maskB K T y₀)) := by
  obtain ⟨hTK,_hNT,_hCos,hZeq⟩:=bar_geometry J K hJ hK hN hWeak T hTJ
  have hBTJ:=bar_test J hJ T hTJ
  have hBTK:=bar_test K hK T hTK
  obtain ⟨_hyU,huK⟩:=tangentChoice_spec K
    (exists_tangent_of_mem_cosupp K hK.isWellFormed hK.one_le_d hMaxK T hBTK hy)
  have hLevel : level K T y₀=0:=by
    simp only [level,origMembers,hKE,List.length_nil,List.take_zero]
    rfl
  have hyW:=mem_maskB K hK.isWellFormed hK.one_le_d hMaxK T hBTK hy hLevel hZ
  let U : TopologicalSpace.Opens X:=⟨(tangentChoice K (T.proj y₀)).1,huK.isOpen⟩
  have hWU : (maskB K T y₀ : Set Y)⊆openPreimage T U:=fun z hz=>(interior_subset hz).1
  have hAvoidK : ∀z∈maskB K T y₀,z∈strictAlong T (K.N∩{x | (tangentChoice K (T.proj y₀)).2 x=0})→
      z∉codimOnePartAlong (geoTransformAlong (barMarked K) T).N
        (geoTransformAlong (barMarked K) T).ideal (geoTransformAlong (barMarked K) T).d:=
    fun z hz _=>(interior_subset hz).2.2
  have hAvoidJ : ∀z∈maskB K T y₀,z∈strictAlong T (J.N∩{x | (tangentChoice K (T.proj y₀)).2 x=0})→
      z∉codimOnePartAlong (geoTransformAlong (barMarked J) T).N
        (geoTransformAlong (barMarked J) T).ideal (geoTransformAlong (barMarked J) T).d:=by
    intro z hz _
    rw [hZeq]
    exact (interior_subset hz).2.2
  have hOldJ : ∀H∈(geoTransformAlong (barMarked J) T).E.take J.E.length,
      ∀z∈maskB K T y₀,z∈strictAlong T (J.N∩{x | (tangentChoice K (T.proj y₀)).2 x=0})→z∉H:=by
    simp only [hJE,List.length_nil,List.take_zero,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  have hOldK : ∀H∈(geoTransformAlong (barMarked K) T).E.take K.E.length,
      ∀z∈maskB K T y₀,z∈strictAlong T (K.N∩{x | (tangentChoice K (T.proj y₀)).2 x=0})→z∉H:=by
    simp only [hKE,List.length_nil,List.take_zero,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  exact ⟨hyW,
    isInvDomain_stage_coeffHomAlong_of_le J hJ.isWellFormed hJ.one_le_d hJ.dimLE U huJ
      T hBTJ (maskB K T y₀) hWU hAvoidJ hOldJ,
    isInvDomain_stage_coeffHomAlong_of_le K hK.isWellFormed hK.one_le_d hK.dimLE U huK
      T hBTK (maskB K T y₀) hWU hAvoidK hOldK⟩

/- Exact all-threshold order naturality, including infinity; zero new geometric engine. -/
private theorem order_open_val (A : MarkedIdeal n Y) (hA : A.ideal.IsCoherent)
    (O : TopologicalSpace.Opens Y) (p : O) (hp : p.val∈A.N) :
    GermIdealOrder.order n (MarkedIdeal.pullback (Subtype.val : O→Y) A).N
      (MarkedIdeal.pullback (Subtype.val : O→Y) A).ideal p=
      GermIdealOrder.order n A.N A.ideal p.val := by
  have hC : (GermIdeal.pullback (m:=n) (Subtype.val : O→Y) A.ideal).IsCoherent:=
    isCoherent_pullback contMDiff_subtype_val hA
  apply ENat.eq_of_forall_natCast_le_iff
  intro q
  change (q : ℕ∞)≤GermIdealOrder.order n ((Subtype.val : O→Y) ⁻¹' A.N)
    (GermIdeal.pullback (m:=n) (Subtype.val : O→Y) A.ideal) p ↔ _
  rw [le_order_iff (hol (Z:=CMfd.of (n:=n) O) hC p),le_order_iff (hol hA p.val)]
  have hcos:=cosupp_pullback_val (⟨A.N,A.E,A.ideal,q⟩ : MarkedIdeal n Y) (hol hA) O
  constructor
  · intro h
    have hh : p∈(MarkedIdeal.pullback (Subtype.val : O→Y) (⟨A.N,A.E,A.ideal,q⟩ : MarkedIdeal n Y)).cosupp:=⟨hp,h⟩
    rw [hcos] at hh
    exact hh.2
  · intro h
    have hh : p∈(Subtype.val : O→Y) ⁻¹' (⟨A.N,A.E,A.ideal,q⟩ : MarkedIdeal n Y).cosupp:=⟨hp,h⟩
    rw [←hcos] at hh
    exact hh.2

private theorem finite_raw_compare (hn : 0<n) (A B : MarkedIdeal n X) {k : ℕ}
    (hA : IsInvDomain k A) (hB : IsInvDomain k B) (hN : A.N=B.N) (hE : A.E=B.E)
    (hCuts : ∀x∈A.N,∀a b : ℕ,0<b→b≤a→
      ((((A.d*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n A.N A.ideal x) ↔
       (((B.d*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n B.N B.ideal x)))
    (hExp : ∀(x : X)(i : ℕ),B.d*expDataAlong n A.N A.ideal A.E x i=
      A.d*expDataAlong n B.N B.ideal B.E x i) :
    A.cosupp=B.cosupp ∧ ∀x∈A.cosupp,B.d*nmOrd A x=A.d*nmOrd B x := by
  have hCos : A.cosupp=B.cosupp:=by
    ext x
    constructor
    · intro hx
      have hh:=(hCuts x hx.1 1 1 (by omega) le_rfl).mp
        (by simpa only [Nat.mul_one,Nat.cast_one,one_mul] using (le_order_iff (hol hA.isWellFormed.isCoherent x)).mpr hx.2)
      exact ⟨hN ▸ hx.1,(le_order_iff (hol hB.isWellFormed.isCoherent x)).mp
        (by simpa only [Nat.mul_one,Nat.cast_one,one_mul] using hh)⟩
    · intro hx
      have hxA : x∈A.N:=by rw [hN];exact hx.1
      have hh:=(hCuts x hxA 1 1 (by omega) le_rfl).mpr
        (by simpa only [Nat.mul_one,Nat.cast_one,one_mul] using (le_order_iff (hol hB.isWellFormed.isCoherent x)).mpr hx.2)
      exact ⟨hxA,(le_order_iff (hol hA.isWellFormed.isCoherent x)).mp
        (by simpa only [Nat.mul_one,Nat.cast_one,one_mul] using hh)⟩
  refine ⟨hCos,?_⟩
  intro x hxA
  have hxB : x∈B.cosupp:=hCos ▸ hxA
  let sA:=∑i∈memberIdx A.E x,expDataAlong n A.N A.ideal A.E x i
  let sB:=∑i∈memberIdx B.E x,expDataAlong n B.N B.ideal B.E x i
  have hOA:=(whole_factor_order hn A hA.isWellFormed hA.isNonzeroAlongAt x hxA.1).2.2.2
  have hOB:=(whole_factor_order hn B hB.isWellFormed hB.isNonzeroAlongAt x hxB.1).2.2.2
  change GermIdealOrder.order n A.N A.ideal x=((sA+nmOrd A x : ℕ) : ℕ∞) at hOA
  change GermIdealOrder.order n B.N B.ideal x=((sB+nmOrd B x : ℕ) : ℕ∞) at hOB
  have hLowA : A.d≤sA+nmOrd A x:=by
    have hh:=(le_order_iff (hol hA.isWellFormed.isCoherent x)).mpr hxA.2
    rw [hOA] at hh
    exact_mod_cast hh
  have hLowB : B.d≤sB+nmOrd B x:=by
    have hh:=(le_order_iff (hol hB.isWellFormed.isCoherent x)).mpr hxB.2
    rw [hOB] at hh
    exact_mod_cast hh
  have hAB : B.d*(sA+nmOrd A x)≤A.d*(sB+nmOrd B x):=by
    have hh:=(hCuts x hxA.1 (sA+nmOrd A x) A.d hA.one_le_d hLowA).mp
      (by rw [hOA];simp only [Nat.cast_mul];exact le_rfl)
    rw [hOB] at hh
    exact_mod_cast hh
  have hBA : A.d*(sB+nmOrd B x)≤B.d*(sA+nmOrd A x):=by
    have hh:=(hCuts x hxA.1 (sB+nmOrd B x) B.d hB.one_le_d hLowB).mpr
      (by rw [hOB];simp only [Nat.cast_mul];exact le_rfl)
    rw [hOA] at hh
    exact_mod_cast hh
  have hSum : B.d*sA=A.d*sB:=by
    dsimp only [sA,sB]
    rw [Finset.mul_sum,Finset.mul_sum]
    have hIdx : memberIdx A.E x=memberIdx B.E x:=by rw [hE]
    rw [←hIdx]
    exact Finset.sum_congr rfl fun i _=>hExp x i
  have hTotal:=Nat.le_antisymm hAB hBA
  rw [Nat.mul_add,Nat.mul_add,hSum] at hTotal
  exact Nat.add_left_cancel hTotal

/- Both opens pull back the SAME whole ambient records; no C(current) reset. -/
private theorem raw_on_smaller_open (hn : 0<n) (A B : MarkedIdeal n Y)
    (hA : A.ideal.IsCoherent) (hB : B.ideal.IsCoherent) (hN : A.N=B.N) (hE : A.E=B.E)
    (Z O : TopologicalSpace.Opens Y) (hOZ : O≤Z) {k : ℕ}
    (hAO : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : O→Y) A))
    (hBO : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : O→Y) B))
    (hCuts : ∀x : Z,x.val∈A.N→∀a b : ℕ,0<b→b≤a→
      ((((A.d*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n
        (MarkedIdeal.pullback (Subtype.val : Z→Y) A).N (MarkedIdeal.pullback (Subtype.val : Z→Y) A).ideal x) ↔
       (((B.d*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n
        (MarkedIdeal.pullback (Subtype.val : Z→Y) B).N (MarkedIdeal.pullback (Subtype.val : Z→Y) B).ideal x)))
    (hExp : ∀(H : Set Z)(x : Z),B.d*divExpAlong n
        (MarkedIdeal.pullback (Subtype.val : Z→Y) A).N (MarkedIdeal.pullback (Subtype.val : Z→Y) A).ideal H x=
      A.d*divExpAlong n (MarkedIdeal.pullback (Subtype.val : Z→Y) B).N
        (MarkedIdeal.pullback (Subtype.val : Z→Y) B).ideal H x) :
    let AO:=MarkedIdeal.pullback (Subtype.val : O→Y) A
    let BO:=MarkedIdeal.pullback (Subtype.val : O→Y) B
    AO.cosupp=BO.cosupp ∧ ∀x∈AO.cosupp,BO.d*nmOrd (M:=CMfd.of (n:=n) O) AO x=AO.d*nmOrd (M:=CMfd.of (n:=n) O) BO x := by
  let AO:=MarkedIdeal.pullback (Subtype.val : O→Y) A
  let BO:=MarkedIdeal.pullback (Subtype.val : O→Y) B
  have hNO : AO.N=BO.N:=by change (Subtype.val : O→Y) ⁻¹' A.N=(Subtype.val : O→Y) ⁻¹' B.N;rw [hN]
  have hEO : AO.E=BO.E:=by change A.E.map _=B.E.map _;rw [hE]
  have hCutsO : ∀x∈AO.N,∀a b : ℕ,0<b→b≤a→
      ((((AO.d*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n AO.N AO.ideal x) ↔
       (((BO.d*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n BO.N BO.ideal x)):=by
    intro x hx a b hb hba
    let z : Z:=⟨x.val,hOZ x.2⟩
    have hxB : x.val∈B.N:=by rw [←hN];exact hx
    have hh:=hCuts z hx a b hb hba
    rw [order_open_val A hA Z z hx,order_open_val B hB Z z hxB] at hh
    rw [order_open_val A hA O x hx,order_open_val B hB O x hxB]
    exact hh
  have hExpO : ∀(x : O)(i : ℕ),BO.d*expDataAlong n AO.N AO.ideal AO.E x i=
      AO.d*expDataAlong n BO.N BO.ideal BO.E x i:=by
    intro x i
    by_cases hi : i<A.E.length
    · have hiB : i<B.E.length:=by rw [←hE];exact hi
      have hiAO : i<AO.E.length:=by simpa only [AO,MarkedIdeal.pullback,List.length_map] using hi
      have hiBO : i<BO.E.length:=by simpa only [BO,MarkedIdeal.pullback,List.length_map] using hiB
      let z : Z:=⟨x.val,hOZ x.2⟩
      have hiAZ : i<(MarkedIdeal.pullback (Subtype.val : Z→Y) A).E.length:=by simpa only [MarkedIdeal.pullback,List.length_map] using hi
      have hiBZ : i<(MarkedIdeal.pullback (Subtype.val : Z→Y) B).E.length:=by simpa only [MarkedIdeal.pullback,List.length_map] using hiB
      have hBase : A.E.get ⟨i,hi⟩=B.E.get ⟨i,hiB⟩:=by
        simpa only [List.get_eq_getElem] using getElem_congr hE rfl hi
      have hGet : (MarkedIdeal.pullback (Subtype.val : Z→Y) A).E.get ⟨i,hiAZ⟩=
          (MarkedIdeal.pullback (Subtype.val : Z→Y) B).E.get ⟨i,hiBZ⟩:=by
        calc
          _=(Subtype.val : Z→Y) ⁻¹' A.E.get ⟨i,hi⟩:=by simp [MarkedIdeal.pullback]
          _=(Subtype.val : Z→Y) ⁻¹' B.E.get ⟨i,hiB⟩:=congrArg ((Subtype.val : Z→Y) ⁻¹' ·) hBase
          _=_:=by simp [MarkedIdeal.pullback]
      have hh:=hExp ((MarkedIdeal.pullback (Subtype.val : Z→Y) A).E.get ⟨i,hiAZ⟩) z
      have hExpAZ:=divExpAlong_pullback_val_get A hA Z z hiAZ hi
      have hExpBZ:=divExpAlong_pullback_val_get B hB Z z hiBZ hiB
      rw [←hGet] at hExpBZ
      rw [hExpAZ,hExpBZ] at hh
      simp only [expDataAlong,dif_pos hiAO,dif_pos hiBO]
      rw [divExpAlong_pullback_val_get A hA O x hiAO hi,
        divExpAlong_pullback_val_get B hB O x hiBO hiB]
      exact hh
    · have hiB : ¬i<B.E.length:=by rw [←hE];exact hi
      have hiAO : ¬i<AO.E.length:=by simpa only [AO,MarkedIdeal.pullback,List.length_map] using hi
      have hiBO : ¬i<BO.E.length:=by simpa only [BO,MarkedIdeal.pullback,List.length_map] using hiB
      simp only [expDataAlong,dif_neg hiAO,dif_neg hiBO,Nat.mul_zero]
  exact finite_raw_compare (X:=CMfd.of (n:=n) O) hn AO BO hAO hBO hNO hEO hCutsO hExpO

private theorem projected_cosupp (K : MarkedIdeal n X) {k : ℕ} (hK : IsInvDomain k K)
    (T : BlowupTower X Y) (hTK : IsGeoTestTower K T) (y₀ : Y)
    (hy : y₀∈(geoTransformAlong (barMarked K) T).cosupp) : T.proj y₀∈K.cosupp := by
  have hh:=proj_mem_cosupp_of_mem_cosupp (𝔪:=barMarked K) hK.isWellFormed.isClosedSubmanifold_N
    (isWellFormed_barMarked K hK.isWellFormed).isCoherent T (bar_test K hK T hTK) hy
  rw [cosupp_barMarked K hK.isWellFormed hK.one_le_d] at hh
  exact hh

private theorem paired_mask_stage (hn : 0<n) (J K : MarkedIdeal n X) {k : ℕ}
    (hJ : IsInvDomain k J) (hK : IsInvDomain k K) (hNK : J.N=K.N)
    (hJE : J.E=[]) (hKE : K.E=[]) (hWeak : WEquiv J K)
    (hMaxK : IsMaximalOrderAlong K.N K.ideal K.d)
    (T : BlowupTower X Y) (hTJ : IsGeoTestTower J T) (y₀ : Y)
    (hy : y₀∈(geoTransformAlong (barMarked K) T).cosupp)
    (hZ : y₀∉codimOnePartAlong (geoTransformAlong (barMarked K) T).N
      (geoTransformAlong (barMarked K) T).ideal (geoTransformAlong (barMarked K) T).d)
    (huJ : IsTangentDirectionAlong J.N J.ideal J.d (tangentChoice K (T.proj y₀)).1
      (tangentChoice K (T.proj y₀)).2)
    (hOpen : IsOpen (tangentChoice K (T.proj y₀)).1)
    (hCuts : let Z:=openPreimage T ⟨(tangentChoice K (T.proj y₀)).1,hOpen⟩
      let RJ:=contactMarkedKept J (tangentChoice K (T.proj y₀)).2 T Z
      let RK:=contactMarkedKept K (tangentChoice K (T.proj y₀)).2 T Z
      ∀z : Z,z.val∈strictAlong T (K.N∩{y | (tangentChoice K (T.proj y₀)).2 y=0})→
        ∀a b : ℕ,0<b→b≤a→
          ((((RJ.d*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n RJ.N RJ.ideal z) ↔
           (((RK.d*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n RK.N RK.ideal z)))
    (hExp : let Z:=openPreimage T ⟨(tangentChoice K (T.proj y₀)).1,hOpen⟩
      let RJ:=contactMarkedKept J (tangentChoice K (T.proj y₀)).2 T Z
      let RK:=contactMarkedKept K (tangentChoice K (T.proj y₀)).2 T Z
      ∀(H : Set Z)(z : Z),RK.d*divExpAlong n RJ.N RJ.ideal H z=RJ.d*divExpAlong n RK.N RK.ideal H z) :
    y₀∈maskB K T y₀ ∧
    let O:=maskB K T y₀
    let RJ:=contactMarkedKept J (tangentChoice K (T.proj y₀)).2 T O
    let RK:=contactMarkedKept K (tangentChoice K (T.proj y₀)).2 T O
    IsInvDomain (k-1) RJ ∧ IsInvDomain (k-1) RK ∧ RJ.N=RK.N ∧ RJ.E=RK.E ∧
    RJ.cosupp=RK.cosupp ∧ ∀z∈RJ.cosupp,
      RK.d*nmOrd (M:=CMfd.of (n:=n) O) RJ z=RJ.d*nmOrd (M:=CMfd.of (n:=n) O) RK z := by
  have hTK:=(hWeak.2 T).1.mp hTJ
  obtain ⟨hyO,hDomainJ,hDomainK⟩:=common_mask_domains J K hJ hK hNK hJE hKE hWeak hMaxK T hTJ y₀ hy hZ huJ
  let U₀ : TopologicalSpace.Opens X:=⟨(tangentChoice K (T.proj y₀)).1,hOpen⟩
  let Z:=openPreimage T U₀
  let O:=maskB K T y₀
  let w:=(tangentChoice K (T.proj y₀)).2
  let GJ:=withN (coeffMarkedAlong (geoTransformAlong (barMarked J) T)) (strictAlong T (J.N∩{z | w z=0}))
  let GK:=withN (coeffMarkedAlong (geoTransformAlong (barMarked K) T)) (strictAlong T (K.N∩{z | w z=0}))
  have hOZ : O≤Z:=fun z hz=>(interior_subset hz).1
  have hNG : GJ.N=GK.N:=by
    change strictAlong T (J.N∩{z | w z=0})=strictAlong T (K.N∩{z | w z=0})
    rw [hNK]
  have hEG : GJ.E=GK.E:=by
    change (geoTransformAlong (barMarked J) T).E=(geoTransformAlong (barMarked K) T).E
    exact E_geoTransformAlong_eq (𝔪:=barMarked J) (𝔫:=barMarked K)
      (show (barMarked J).E=(barMarked K).E from hWeak.1) T
  have hCoherentJ : GJ.ideal.IsCoherent:=by
    have hh:=(original_bar_weighted_history J hJ T hTJ).2.1
    exact isCoherent_coeffMarkedAlong hh.isWellFormed.isCoherent hh.isWellFormed.isClosedSubmanifold_N
  have hCoherentK : GK.ideal.IsCoherent:=by
    have hh:=(original_bar_weighted_history K hK T hTK).2.1
    exact isCoherent_coeffMarkedAlong hh.isWellFormed.isCoherent hh.isWellFormed.isClosedSubmanifold_N
  have hCutsG : ∀z : Z,z.val∈GJ.N→∀a b : ℕ,0<b→b≤a→
      ((((GJ.d*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n
        (MarkedIdeal.pullback (Subtype.val : Z→Y) GJ).N (MarkedIdeal.pullback (Subtype.val : Z→Y) GJ).ideal z) ↔
       (((GK.d*a : ℕ) : ℕ∞)≤(b : ℕ∞)*GermIdealOrder.order n
        (MarkedIdeal.pullback (Subtype.val : Z→Y) GK).N (MarkedIdeal.pullback (Subtype.val : Z→Y) GK).ideal z)):=by
    intro z hz a b hb hba
    have hzK : z.val∈GK.N:=by rw [←hNG];exact hz
    exact hCuts z hzK a b hb hba
  have hRaw:=raw_on_smaller_open hn GJ GK hCoherentJ hCoherentK hNG hEG Z O hOZ
    hDomainJ hDomainK hCutsG hExp
  refine ⟨hyO,hDomainJ,hDomainK,?_,?_,hRaw.1,hRaw.2⟩
  · change (Subtype.val : O→Y) ⁻¹' GJ.N=(Subtype.val : O→Y) ⁻¹' GK.N
    rw [hNG]
  · change GJ.E.map ((Subtype.val : O→Y) ⁻¹' ·)=GK.E.map ((Subtype.val : O→Y) ⁻¹' ·)
    rw [hEG]

/-- Exact ordinary ORIGINAL inputs derive both actual kept lower domains on the
literal native K-mask before finite WHOLE-factor/raw cancellation. -/
theorem original_lower_common_mask_raw_order {A : CMfd.{0} n}
    (hn : 0<n) (Q : MarkedIdeal n A) {k : ℕ} (hQ : IsInvDomain k Q)
    (hN : Q.N=univ) (hE : Q.E=[]) (hMax : IsMaximalOrderAlong Q.N Q.ideal Q.d)
    (W : Set A) (hW : IsComplexAnalyticSubset (n:=n) W)
    (hSing : Q.cosupp⊆singularSet (n:=n) W) (a : A) (ha : a∈Q.cosupp) :
    ∃hm : a∈maskB Q (.refl : BlowupTower A A) a,
      let V:=maskB Q (.refl : BlowupTower A A) a
      let L : MarkedIdeal n (CMfd.of (n:=n) V):=StepOneValueMasked.lowerMarkedB Q (.refl : BlowupTower A A) a
      let x : V:=⟨a,hm⟩
      let μ:=nmOrd L x
      let e:=sumExp (fun j=>L.d-j) L.d 0
      let U:=ordMask L μ
      let P : MarkedIdeal n (CMfd.of (n:=n) U):=MarkedIdeal.pullback (Subtype.val : U→V) L
      let B : MarkedIdeal n (CMfd.of (n:=n) U):=MarkedIdeal.pullback (Subtype.val : U→V) (coeffMarkedAlong L)
      let J:=companionOf n P μ
      let K:=companionOf n B (e*μ)
      ∃hxU : x∈U,
        IsInvDomain (k-1) J ∧ IsInvDomain (k-1) K ∧ J.E=[] ∧ K.E=[] ∧ J.d=μ ∧ K.d=e*μ ∧
        (⟨x,hxU⟩ : U)∈J.cosupp ∧ (⟨x,hxU⟩ : U)∈K.cosupp ∧
        ∀{Y : CMfd.{0} n}(T : BlowupTower (CMfd.of (n:=n) U) Y),IsGeoTestTower J T→
          IsGeoTestTower K T ∧
          ∀y₀∈(geoTransformAlong (barMarked K) T).cosupp,
            y₀∉codimOnePartAlong (geoTransformAlong (barMarked K) T).N
              (geoTransformAlong (barMarked K) T).ideal (geoTransformAlong (barMarked K) T).d→
            y₀∈maskB K T y₀ ∧
            let O:=maskB K T y₀
            let RJ:=contactMarkedKept J (tangentChoice K (T.proj y₀)).2 T O
            let RK:=contactMarkedKept K (tangentChoice K (T.proj y₀)).2 T O
            RK=StepOneValueMasked.lowerMarkedB K T y₀ ∧
            IsInvDomain ((k-1)-1) RJ ∧ IsInvDomain ((k-1)-1) RK ∧ RJ.N=RK.N ∧ RJ.E=RK.E ∧
            RJ.d=(Finset.range ((Finset.range μ).prod (fun j=>μ-j))).prod
              (fun j=>(Finset.range μ).prod (fun j=>μ-j)-j) ∧
            RK.d=(Finset.range ((Finset.range (e*μ)).prod (fun j=>e*μ-j))).prod
              (fun j=>(Finset.range (e*μ)).prod (fun j=>e*μ-j)-j) ∧
            RJ.E.length=T.length ∧ RK.E.length=T.length ∧ RJ.cosupp=RK.cosupp ∧
            ∀z∈RJ.cosupp,RK.d*nmOrd (M:=CMfd.of (n:=n) O) RJ z=RJ.d*nmOrd (M:=CMfd.of (n:=n) O) RK z := by
  obtain ⟨hm,hxU,_hMask,_hNatural,hJ,hK,_hMaxJ,hMaxK,hJN,hKN,hJE,hKE,hJd,hKd,
    _hCompJ,_hCompK,hWeak,_hUpper⟩:=
    original_lower_true_mark_companions hn Q hQ hN hE hMax W hW hSing a ha
  obtain ⟨_hmC,_hxUC,_hJC,_hKC,_hNC,_hJdC,_hKdC,hzJ,hzK,_hTangent,hContacts⟩:=
    original_lower_selected_common_contact hn Q hQ hN hE hMax W hW hSing a ha
  obtain ⟨_hmT,_hxUT,_hJT,_hKT,_hJdT,_hKdT,_hzJT,_hzKT,hThresholds⟩:=
    original_lower_common_contact_history_thresholds hn Q hQ hN hE hMax W hW hSing a ha
  obtain ⟨_hmE,_hxUE,_hJE,_hKE,_hJdE,_hKdE,_hzJE,_hzKE,hExponents⟩:=
    original_lower_contact_boundary_exponent_scaling hn Q hQ hN hE hMax W hW hSing a ha
  let V:=maskB Q (.refl : BlowupTower A A) a
  let L : MarkedIdeal n (CMfd.of (n:=n) V):=StepOneValueMasked.lowerMarkedB Q (.refl : BlowupTower A A) a
  let x : V:=⟨a,hm⟩
  let μ:=nmOrd L x
  let e:=sumExp (fun j=>L.d-j) L.d 0
  let U:=ordMask L μ
  let P : MarkedIdeal n (CMfd.of (n:=n) U):=MarkedIdeal.pullback (Subtype.val : U→V) L
  let B : MarkedIdeal n (CMfd.of (n:=n) U):=MarkedIdeal.pullback (Subtype.val : U→V) (coeffMarkedAlong L)
  let J:=companionOf n P μ
  let K:=companionOf n B (e*μ)
  change IsInvDomain (k-1) J at hJ
  change IsInvDomain (k-1) K at hK
  change J.N=P.N at hJN
  change K.N=P.N at hKN
  have hNK : J.N=K.N:=hJN.trans hKN.symm
  refine ⟨hm,hxU,hJ,hK,hJE,hKE,hJd,hKd,hzJ,hzK,?_⟩
  intro Y T hTJ
  have hTK:=(hWeak.2 T).1.mp hTJ
  refine ⟨hTK,?_⟩
  intro y₀ hy hZ
  have hz₀:=projected_cosupp K hK T hTK y₀ hy
  obtain ⟨_hzU₀,huK,huJ,_hZeroJ,_hZeroK⟩:=hContacts (T.proj y₀) hz₀
  obtain ⟨hOpen,hWideCuts⟩:=hThresholds (T.proj y₀) hz₀
  obtain ⟨_hOpenE,hWideExp⟩:=hExponents (T.proj y₀) hz₀
  obtain ⟨_hTKC,_hNWide,_hEWide,hdJ,hdK,hLenJ,hLenK,hCuts⟩:=hWideCuts T hTJ
  obtain ⟨_hTKE,_hNExp,_hEExp,_hdJE,_hdKE,_hLenJE,_hLenKE,hExp⟩:=hWideExp T hTJ
  obtain ⟨hyO,hDomainJ,hDomainK,hNR,hER,hCos,hRaw⟩:=
    paired_mask_stage hn J K hJ hK hNK hJE hKE hWeak hMaxK T hTJ y₀ hy hZ huJ hOpen hCuts hExp
  refine ⟨hyO,rfl,hDomainJ,hDomainK,hNR,hER,hdJ,hdK,?_,?_,hCos,hRaw⟩
  · simpa only [contactMarkedKept,MarkedIdeal.pullback,withN,List.length_map] using hLenJ
  · simpa only [contactMarkedKept,MarkedIdeal.pullback,withN,List.length_map] using hLenK

end
end Hironaka.HironakaActualOriginalCommonMaskRawOrder
