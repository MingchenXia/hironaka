import Hironaka.Resolution.HironakaActualNativeInvariantDomain
import Hironaka.Resolution.HironakaActualNativeSectionBoundaryParts
import Hironaka.Resolution.HironakaSmoothSubmersionCanonicalValueDimensionShift

/-! Original general-step companion records, order masks and the exact
monomial ambient-dimension shift on actual native embeddings/histories. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNativeCompanionHistories
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  ResolutionInvariantSpec InvDomainTowerAlong NormalCrossings SubmanifoldChartedSpace
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionRegularity
  HironakaActualNativeSectionOrderHistory HironakaActualNativeSectionBoundaryParts
  HironakaActualNativeInvariantDomain HironakaActualRawRecordPullbacks
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionRelativeRestriction
  HironakaSmoothSubmersionCanonicalValueDimensionShift HironakaActualNonregularCoefficientNaturality
  RelativePrincipalizationSpan GermIdealPullbackCalculus GermIdealOrder
  MonomialPartAlong NonmonomialOrderLocal NonmonomialOrderTail CompanionRebase CompanionReductionAlong
  MonomialCaseAlong MonomialCase MonomialInvariant DivisorExponentAlong IdealWeightPowers

private theorem supported_image {n : ℕ} {X : CMfd.{0} n} {W : Set X}
    (M : MarkedIdeal n X) (hMN : M.N⊆W) :
    (Subtype.val : W→X) '' ((Subtype.val : W→X) ⁻¹' M.N)=M.N := by
  ext x
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact hp
  · intro hx
    exact ⟨⟨x,hMN hx⟩,hx,rfl⟩

/-- The ENTIRE original companion record on an arbitrary actual regular
native embedding, with original domain and actual support as source data. -/
theorem nativePullback_companionOf {n k r : ℕ} {X : CMfd.{0} n} {W : Set X}
    (hn : 0<n) (hk : k≤n) (hW : ∀x∈W,RegularAtDim (n:=n) W x k)
    (M : MarkedIdeal n X) (hM : IsInvDomain r M) (hMN : M.N⊆W)
    (hTrans : IsTransverse n W M.E) (o : ℕ) :
    nativePullback hk W hW (companionOf n M o)=companionOf k (nativePullback hk W hW M) o := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  have hwf:=hM.isWellFormed
  have hhol : ∀x g,M.ideal.mem x g → HolomorphicAt n g x:=
    fun _ _ ht=>GermIdeal.IsCoherent.holomorphicAt_mem hwf.isCoherent ht
  have hMon:=pullback_native_monomialPartAlong hk hW ((Subtype.val : W→X) ⁻¹' M.N)
    M.E hwf.isSNCDivisor hTrans M.ideal hhol
  have hNon:=pullback_native_nonmonomialPartAlong hk hW ((Subtype.val : W→X) ⁻¹' M.N)
    M.E hwf.isSNCDivisor hTrans M.ideal hhol
  rw [supported_image M hMN] at hMon hNon
  have hmon:=isCoherent_monomialPartAlong hn hwf.isClosedSubmanifold_N
    hwf.isSNCDivisor hwf.isTransverse hwf.isCoherent hM.isNonzeroAlongAt
  have hnon:=isCoherent_nonmonomialPartAlong hn hwf.isClosedSubmanifold_N
    hwf.isSNCDivisor hwf.isTransverse hwf.isCoherent hM.isNonzeroAlongAt
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · simp only [nativePullback,markedPullback,companionOf,companionAlong_N]
  · simp only [nativePullback,markedPullback,companionOf,companionAlong_E]
  · dsimp only [nativePullback,markedPullback,companionOf]
    rw [companionAlong_ideal,companionAlong_ideal]
    split_ifs
    · rw [pullback_sumIdeal_dimensions (contMDiff_val hk hW)
        (isCoherent_idealPow hnon _) (isCoherent_idealPow hmon _),
        pullback_idealPow (contMDiff_val hk hW) (fun ht=>GermIdeal.IsCoherent.holomorphicAt_mem hnon ht),
        pullback_idealPow (contMDiff_val hk hW) (fun ht=>GermIdeal.IsCoherent.holomorphicAt_mem hmon ht),hNon,hMon]
    · exact hNon
  · dsimp only [nativePullback,markedPullback,companionOf]
    rw [companionAlong_d,companionAlong_d]

/-- ORIGINAL order-mask membership is derived from both genuine domains and
whole nonmonomial/cosupport dictionaries, not an immersion-interior rule. -/
theorem ordMask_native_iff {n k r : ℕ} {X : CMfd.{0} n} {W : Set X}
    (hn : 0<n) (hkpos : 0<k) (hk : k≤n) (hW : ∀x∈W,RegularAtDim (n:=n) W x k)
    (M : MarkedIdeal n X) (hM : IsInvDomain r M) (hMN : M.N⊆W)
    (hTrans : IsTransverse n W M.E) (o : ℕ) (p : nativeManifold hk W hW) :
    p.val∈ordMask M o ↔ p∈ordMask (nativePullback hk W hW M) o := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  have hK:=isInvDomain_nativePullback hn hk hW M hM hMN hTrans
  rw [mem_ordMask_iff hn hM.isWellFormed hM.isNonzeroAlongAt,
    mem_ordMask_iff hkpos hK.isWellFormed hK.isNonzeroAlongAt]
  apply not_congr
  change p∈(Subtype.val : W→X) ⁻¹' cosupport n M.N
    (nonmonomialPartAlong n M.N M.ideal M.E) (o+1) ↔ _
  have hNon:=pullback_native_nonmonomialPartAlong hk hW ((Subtype.val : W→X) ⁻¹' M.N)
    M.E hM.isWellFormed.isSNCDivisor hTrans M.ideal
    (fun _ _ ht=>GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent ht)
  have hCos:=HironakaActualNativeSectionOrder.cosupport_native_preimage hk hW
    ((Subtype.val : W→X) ⁻¹' M.N) (nonmonomialPartAlong n M.N M.ideal M.E) (fun _ _ ht=>ht.1) (o+1)
  rw [supported_image M hMN] at hNon hCos
  rw [hCos,hNon]
  rfl

/-- Every original indexed exponent is retained on an actual supported
native embedding, including out-of-range zero entries. -/
theorem expDataAlong_nativePullback {n k : ℕ} {X : CMfd.{0} n} {W : Set X}
    (hk : k≤n) (hW : ∀x∈W,RegularAtDim (n:=n) W x k)
    (M : MarkedIdeal n X) (hMN : M.N⊆W)
    (hhol : ∀x g,M.ideal.mem x g → HolomorphicAt n g x) (p : nativeManifold hk W hW) :
    expDataAlong n M.N M.ideal M.E p.val=
      expDataAlong k (nativePullback hk W hW M).N (nativePullback hk W hW M).ideal
        (nativePullback hk W hW M).E p := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  funext i
  unfold expDataAlong
  by_cases hi : i<M.E.length
  · have hi' : i<(nativePullback hk W hW M).E.length:=by simpa only [nativePullback,markedPullback,List.length_map] using hi
    rw [dif_pos hi,dif_pos hi']
    have hGet : (nativePullback hk W hW M).E.get ⟨i,hi'⟩=(Subtype.val : W→X) ⁻¹' M.E.get ⟨i,hi⟩:=by
      simp only [nativePullback,markedPullback,List.get_eq_getElem,List.getElem_map]
    rw [hGet]
    have ht:=divExpAlong_native_eq hk hW ((Subtype.val : W→X) ⁻¹' M.N) (M.E.get ⟨i,hi⟩) M.ideal hhol p
    rw [supported_image M hMN] at ht
    exact ht
  · have hi' : ¬i<(nativePullback hk W hW M).E.length:=by simpa only [nativePullback,markedPullback,List.length_map] using hi
    rw [dif_neg hi,dif_neg hi']

/-- The genuine original monomial value has the REQUIRED ambient shift;
native SNC supplies the incident-cardinality bound, retaining k=0. -/
theorem gammaAlong_native_dimension_shift {n k : ℕ} {X : CMfd.{0} n} {W : Set X}
    (hn : 0<n) (hk : k≤n) (hW : ∀x∈W,RegularAtDim (n:=n) W x k)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hMN : M.N⊆W)
    (hTrans : IsTransverse n W M.E) (p : nativeManifold hk W hW) :
    gammaAlong n M.N M.ideal M.E M.d p.val=
      dimensionValue (n-k) (gammaAlong k (nativePullback hk W hW M).N
        (nativePullback hk W hW M).ideal (nativePullback hk W hW M).E (nativePullback hk W hW M).d p) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  have hNativeSNC:=isSNCDivisor_native_preimage hn hk hW hM.isSNCDivisor hTrans
  have hExp:=expDataAlong_nativePullback hk hW M hMN
    (fun _ _ ht=>GermIdeal.IsCoherent.holomorphicAt_mem hM.isCoherent ht) p
  have hIdx : memberIdx M.E p.val=memberIdx (nativePullback hk W hW M).E p:=
    (MonomialInvariantFunctorial.memberIdx_map_preimage M.E p).symm
  unfold gammaAlong
  rw [hIdx,hExp]
  simpa only [nativePullback,markedPullback,Nat.add_sub_of_le hk] using
    inv_dimension_shift k (n-k) _ _ M.d (card_memberIdx_le _ hNativeSNC p)

/-- On the SAME given geometry Lift, ANY original TEST supplies all current
domains internally. Whole companion, original masks and shifted monomial
values retain every old and born historical position, without native CAN. -/
theorem Lift.original_current_companion_masks {n k r : ℕ} {X : CMfd.{0} n}
    {hk : k≤n} {W : Set X} {hWc : IsClosed W} {hW : ∀x∈W,RegularAtDim (n:=n) W x k}
    (hn : 0<n) (hkpos : 0<k) (M : MarkedIdeal n X) (hM : IsInvDomain r M)
    (hMN : M.N⊆W) (hTrans : IsTransverse n W M.E)
    {Y : CMfd.{0} n} {T : BlowupTower X Y} {V : Set Y} {hVc : IsClosed V}
    {hV : ∀y∈V,RegularAtDim (n:=n) V y k}
    {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}
    (h : Lift hk W hWc hW M.E T V hVc hV Q) (hT : IsGeoTestTower M T) :
    let MT:=geoTransformAlong M T
    let KQ:=geoTransformAlong (nativePullback hk W hW M) Q
    (∀o,nativePullback hk V hV (companionOf n MT o)=companionOf k KQ o) ∧
      (∀o (p : nativeManifold hk V hV),p.val∈ordMask MT o ↔ p∈ordMask KQ o) ∧
      (∀p : nativeManifold hk V hV,gammaAlong n MT.N MT.ideal MT.E MT.d p.val=
        dimensionValue (n-k) (gammaAlong k KQ.N KQ.ideal KQ.E KQ.d p)) := by
  let := chartedSpace hk hV
  have := isComplexManifold_chartedSpace hk hV
  have hMT:=isInvDomain_geoTransformAlong hM T hT
  have hSupport:=HironakaActualNativeSectionOrderHistory.Lift.current_carrier_subset h M hMN
  obtain ⟨_hCurrentSNC,hCurrentTrans⟩:=h.geometry hn hM.isWellFormed.isSNCDivisor hTrans
  have hEN : (geoTransformAlong M T).E=boundary M.E T:=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪:=M) (𝔫:=(⟨univ,M.E,IdealWeightPowers.unitIdeal n X,1⟩ : MarkedIdeal n X)) rfl T
  rw [←hEN] at hCurrentTrans
  have hRecord:=h.whole_records hn hM.isWellFormed.isSNCDivisor hTrans M rfl hMN
    (fun _ _ ht=>GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent ht)
  constructor
  · intro o
    rw [hRecord]
    exact nativePullback_companionOf hn hk hV (geoTransformAlong M T) hMT hSupport hCurrentTrans o
  constructor
  · intro o p
    rw [hRecord]
    exact ordMask_native_iff hn hkpos hk hV (geoTransformAlong M T) hMT hSupport hCurrentTrans o p
  · intro p
    rw [hRecord]
    exact gammaAlong_native_dimension_shift hn hk hV (geoTransformAlong M T) hMT.isWellFormed hSupport hCurrentTrans p

end
end Hironaka.HironakaActualNativeCompanionHistories
