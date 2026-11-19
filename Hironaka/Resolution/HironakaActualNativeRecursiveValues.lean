import Hironaka.Resolution.HironakaActualNativeOriginalLowerTailEmbedding
import Hironaka.Resolution.HironakaActualNativeCompanionHistories
import Hironaka.Resolution.HironakaActualNativeZeroDimensionalHistory
import Hironaka.Resolution.HironakaActualNativeSectionOriginalCuts

/-! Actual tight-carrier offset recursion on the SAME native history.
Native canonicality is proved from shorter actual prefixes, never supplied
as the desired output comparison. Full adjoining-normal recoding is separate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNativeRecursiveValues
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  ResolutionInvariantSpec ResolutionInvariantExt InvDomainTowerAlong NormalCrossings NormalCrossingsInvariance NormalCrossingsComparison
  SubmanifoldChartedSpace MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionRegularity
  HironakaActualNativeSectionOrderHistory HironakaActualNativeSectionOriginalCuts
  HironakaActualNativeSectionNormalCrossings HironakaActualNativeInvariantDomain
  HironakaActualNativeHistoryExistence HironakaActualNativeZeroDimensionalHistory
  HironakaActualNativePositiveHistories HironakaActualNativeOriginalLowerTailEmbedding
  HironakaActualNativeCompanionHistories HironakaDisjointNativeOpenLift HironakaDisjointNativeReferenceWindow
  HironakaActualRawRecordPullbacks HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionOrderedChoiceImageTrace
  HironakaSmoothSubmersionCanonicalValueDimensionShift CanonicalCentres
  HomogenizedIdealAlong HomogenizedIdealAlongTower HomogenizedGlueingTower
  StepOneValue StepOneValueMasked StepOneRegime StepOneLowerDomain
  NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail GeneralValue
  MonomialCaseAlong MonomialCase RelativePrincipalizationSpan GermIdealPullbackCalculus
  InvDomainMemberRestriction InvDomainRebase HironakaActualNativeLowerEmbedding HironakaActualNativeLowerTailFrames
  BlowupTowerIsomorphism BlowupTowerIsoTail BlowupTowerSplitIso StepOneTangentChange

/-- Actual supported regular-image reflection supplies the ORIGINAL tight
carrier bound; a loose ambient bound is never arithmetically reduced. -/
theorem isInvDomain_native_support_bound {n k r : ℕ} {X : CMfd.{0} n} {W : Set X}
    (hk : k≤n) (hW : ∀x∈W,RegularAtDim (n:=n) W x k)
    (M : MarkedIdeal n X) (hM : IsInvDomain r M) (hMN : M.N⊆W) : IsInvDomain k M := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  let A : Set W:=(Subtype.val : W→X) ⁻¹' M.N
  have hImage : (Subtype.val : W→X) '' A=M.N:=by
    ext x
    constructor
    · rintro ⟨p,hp,rfl⟩;exact hp
    · intro hx;exact ⟨⟨x,hMN hx⟩,hx,rfl⟩
  refine ⟨hM.isWellFormed,?_,hM.one_le_d,hM.isNonzeroAlongAt⟩
  intro x hx
  obtain ⟨j,_hjr,hj⟩:=hM.dimLE x hx
  let p : W:=⟨x,hMN hx⟩
  have hReg:=regularAtDim_native_image_iff hk hW A p j
  rw [hImage] at hReg
  have hjNative : RegularAtDim (n:=k) A p j:=hReg.mp hj
  exact ⟨j,hjNative.1,hj⟩

private theorem domain_mono {n q p : ℕ} {X : CMfd.{0} n} {M : MarkedIdeal n X}
    (hM : IsInvDomain q M) (hqp : q≤p) : IsInvDomain p M := by
  refine ⟨hM.isWellFormed,?_,hM.one_le_d,hM.isNonzeroAlongAt⟩
  intro x hx
  obtain ⟨j,hj,hReg⟩:=hM.dimLE x hx
  exact ⟨j,hj.trans hqp,hReg⟩

private theorem zero_offset_history {n k : ℕ} {X : CMfd.{0} n}
    {hk : k≤n} {W : Set X} {hWc : IsClosed W} {hW : ∀x∈W,RegularAtDim (n:=n) W x k}
    (hn : 0<n) (hkpos : 0<k) (M : MarkedIdeal n X) (hM : IsInvDomain 0 M)
    {Y : CMfd.{0} n} {T : BlowupTower X Y} {V : Set Y} {hVc : IsClosed V}
    {hV : ∀y∈V,RegularAtDim (n:=n) V y k}
    {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}
    (h : Lift hk W hWc hW M.E T V hVc hV Q) (hT : IsGeoTestTower M T) :
    IsCanonical (nativePullback hk W hW M) ((invFamily hkpos 0).inv (nativePullback hk W hW M)) Q ∧
      ∀z : nativeManifold hk V hV,z.val∈(geoTransformAlong M T).cosupp →
        (invFamily hn ((n-k)+0)).inv M T z.val=
          familyDimensionMap (n-k) 0 ((invFamily hkpos 0).inv (nativePullback hk W hW M) Q z) := by
  have hReg : ∀x∈M.N,RegularAtDim (n:=n) M.N x 0:=by
    intro x hx
    obtain ⟨j,hj,hReg⟩:=hM.dimLE x hx
    have hj0 : j=0:=Nat.eq_zero_of_le_zero hj
    exact hj0 ▸ hReg
  have hEmpty:=(original_zero_support_test_resolution hReg M hM subset_rfl T hT).1
  have hNativeEmpty:=(HironakaActualNativeZeroDimensionalHistory.Lift.isEmptyTower_iff h).mp hEmpty
  refine ⟨isCanonical_of_isEmptyTower _ _ Q hNativeEmpty,?_⟩
  intro z hz
  rw [cosupp_geoTransformAlong_eq_empty_of_dimLE_zero hM T hT] at hz
  exact False.elim hz

private theorem monomial_family_value {n k q : ℕ} {X : CMfd.{0} n}
    {hk : k≤n} {W : Set X} {hWc : IsClosed W} {hW : ∀x∈W,RegularAtDim (n:=n) W x k}
    (hn : 0<n) (hkpos : 0<k) (M : MarkedIdeal n X) (hM : IsInvDomain (q+1) M)
    (hMN : M.N⊆W) (hTrans : IsTransverse n W M.E)
    {Y : CMfd.{0} n} {T : BlowupTower X Y} {V : Set Y} {hVc : IsClosed V}
    {hV : ∀y∈V,RegularAtDim (n:=n) V y k}
    {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}
    (h : Lift hk W hWc hW M.E T V hVc hV Q) (hT : IsGeoTestTower M T)
    (z : nativeManifold hk V hV) (hzero : nmOrd (geoTransformAlong M T) z.val=0) :
    (invFamily hn ((n-k)+(q+1))).inv M T z.val=
      familyDimensionMap (n-k) (q+1) ((invFamily hkpos (q+1)).inv (nativePullback hk W hW M) Q z) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  let := chartedSpace hk hV
  have := isComplexManifold_chartedSpace hk hV
  have hOrd:=HironakaActualNativeSectionOrderHistory.Lift.current_nmOrd h hn hM.isWellFormed.isSNCDivisor hTrans
    M rfl hMN (fun _ _ ht=>GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent ht) z
  have hNativeZero : nmOrd (geoTransformAlong (nativePullback hk W hW M) Q) z=0:=hOrd.symm.trans hzero
  have hGamma:=(HironakaActualNativeCompanionHistories.Lift.original_current_companion_masks
    hn hkpos M hM hMN hTrans h hT).2.2 z
  change genInv (fun {A} L {B} S y=>Seq.StepOneValueMasked.stepOneInvM (X:=A)
      (invFamily hn ((n-k)+q)) L (Y:=B) S y) M T z.val=
    generalDimensionMap (n-k) (stepDimensionMap (familyDimensionMap (n-k) q))
      (genInv (fun {A} L {B} S y=>Seq.StepOneValueMasked.stepOneInvM (X:=A)
        (invFamily hkpos q) L (Y:=B) S y) (nativePullback hk W hW M) Q z)
  rw [genInv_of_nmOrd_eq_zero _ _ T hzero,genInv_of_nmOrd_eq_zero _ _ Q hNativeZero]
  simp only [generalDimensionMap,ofLex_toLex,Sum.map_inl]
  exact congrArg (fun a=>toLex (0,toLex (Sum.inl a))) hGamma

private theorem double_restrict_original_value {k q : ℕ} {Λ : Type} [LinearOrder Λ]
    (I : ResolutionInvariantSeq.ResolutionInvariant.{0,0} k q Λ) {X Y : CMfd.{0} k}
    (L : MarkedIdeal k X) (hL : L.ideal.IsCoherent) (T : BlowupTower X Y)
    (A D : Opens X) (hA : IsInvDomain q (MarkedIdeal.pullback (Subtype.val : A→X) L))
    (hCan : IsCanonical (MarkedIdeal.pullback (Subtype.val : A→X) L)
      (I.inv (MarkedIdeal.pullback (Subtype.val : A→X) L)) (restrict A T))
    (O : Opens D) (g : O→A)
    (hg : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k) ∞ g)
    (hgval : ∀w,(g w).val=w.val.val)
    (z : openPreimage (restrict D T) O) (a : openPreimage T A) (ha : a.val=z.val.val)
    (hz : a∈(geoTransformAlong (MarkedIdeal.pullback (Subtype.val : A→X) L) (restrict A T)).cosupp) :
    IsCanonical (MarkedIdeal.pullback g (MarkedIdeal.pullback (Subtype.val : A→X) L))
      (I.inv (MarkedIdeal.pullback g (MarkedIdeal.pullback (Subtype.val : A→X) L))) (restrict O (restrict D T)) ∧
      I.inv (MarkedIdeal.pullback g (MarkedIdeal.pullback (Subtype.val : A→X) L)) (restrict O (restrict D T)) z=
        I.inv (MarkedIdeal.pullback (Subtype.val : A→X) L) (restrict A T) a := by
  let C : Opens X:=⟨(Subtype.val : D→X) '' (O : Set D),D.isOpen.isOpenMap_subtype_val _ O.isOpen⟩
  have hOC : ∀w : D,w∈O ↔ w.val∈C:=by
    intro w
    constructor
    · intro hw;exact ⟨w,hw,rfl⟩
    · rintro ⟨v,hv,hvw⟩;exact (Subtype.ext hvw : v=w) ▸ hv
  have hCD : C≤D:=by rintro _ ⟨w,_hw,rfl⟩;exact w.property
  have hCA : C≤A:=by
    rintro _ ⟨w,hw,rfl⟩
    exact (hgval ⟨w,hw⟩) ▸ (g ⟨w,hw⟩).property
  let Ξ:=MaxLocusLocal.nestedDiffeo (n:=k) D O C hOC hCD
  have hEnd : ∀w : openPreimage T D,w∈openPreimage (restrict D T) O ↔ w.val∈openPreimage T C:=by
    intro w
    change (restrict D T).proj w∈O ↔ T.proj w.val∈C
    rw [hOC,proj_restrict]
  let τ:=MaxLocusLocal.nestedDiffeo (n:=k) (openPreimage T D) (openPreimage (restrict D T) O)
    (openPreimage T C) hEnd (MaxLocusLocal.openPreimage_mono T hCD)
  have hFlat : BlowupTowerIsomorphism.IsTowerIso Ξ (restrict O (restrict D T)) (restrict C T) τ:=by
    have hO : O=MaxLocusLocal.nestedOpens D C:=by
      apply Opens.ext
      ext w
      exact hOC w
    clear_value C
    subst O
    exact MaxLocusLocal.isTowerIso_restrict_nestedOpens hCD T
  obtain ⟨hCdom,hCcan,hCval⟩:=Seq.MaxLocusLocal.restrict_nestedOpens I hL hCA hA T hCan
  let LC:=MarkedIdeal.pullback (Subtype.val : C→X) L
  have hMap : (Subtype.val : A→X) ∘ g=(Subtype.val : C→X) ∘ Ξ:=funext hgval
  have hWhole : MarkedIdeal.pullback Ξ LC=MarkedIdeal.pullback g (MarkedIdeal.pullback (Subtype.val : A→X) L):=by
    have h1:=whole_markedPullback_comp contMDiff_subtype_val hg L hL
    have h2:=whole_markedPullback_comp contMDiff_subtype_val Ξ.contMDiff L hL
    have h3:=congrArg (fun f : O→X=>markedPullback (m:=k) f L) hMap.symm
    exact h2.symm.trans (h3.trans h1)
  have hNcan:=Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso I hCdom Ξ hFlat hCcan
  rw [hWhole] at hNcan
  have hHol : ∀x f,L.ideal.mem x f → HolomorphicAt k f x:=fun _ _ ht=>GermIdeal.IsCoherent.holomorphicAt_mem hL ht
  have hCurrentHol:=holomorphic_geoTransformAlong L hHol T
  have hzRaw : a.val∈(geoTransformAlong L T).cosupp:=by
    rw [geoTransformAlong_restrict_of_hhol L hHol A T,cosupp_pullback_val _ hCurrentHol (openPreimage T A)] at hz
    exact hz
  have hzC : τ z∈(geoTransformAlong LC (restrict C T)).cosupp:=by
    change τ z∈(geoTransformAlong (MarkedIdeal.pullback (Subtype.val : C→X) L) (restrict C T)).cosupp
    rw [geoTransformAlong_restrict_of_hhol L hHol C T,cosupp_pullback_val _ hCurrentHol (openPreimage T C)]
    change z.val.val∈(geoTransformAlong L T).cosupp
    exact ha ▸ hzRaw
  have hIsoValue:=I.isInvValue.towerIso Ξ LC hCdom (restrict O (restrict D T)) (restrict C T) τ hFlat hCcan z hzC
  rw [hWhole] at hIsoValue
  refine ⟨hNcan,hIsoValue.trans ((hCval (τ z) hzC).trans ?_)⟩
  apply congrArg (I.inv (MarkedIdeal.pullback (Subtype.val : A→X) L) (restrict A T))
  exact Subtype.ext ha.symm

private def NativeFamilyTransport (q : ℕ) : Prop :=
  ∀{n k : ℕ}{X : CMfd.{0} n}(hn : 0<n)(hkpos : 0<k)(hk : k≤n)
    (W : Set X)(hWc : IsClosed W)(hW : ∀x∈W,RegularAtDim (n:=n) W x k)
    (M : MarkedIdeal n X),IsInvDomain q M → M.N⊆W → IsTransverse n W M.E →
    ∀{Y : CMfd.{0} n}{T : BlowupTower X Y}{V : Set Y}{hVc : IsClosed V}
      {hV : ∀y∈V,RegularAtDim (n:=n) V y k}
      {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)},
      Lift hk W hWc hW M.E T V hVc hV Q →
      IsCanonical M ((invFamily hn ((n-k)+q)).inv M) T →
      IsCanonical (nativePullback hk W hW M) ((invFamily hkpos q).inv (nativePullback hk W hW M)) Q ∧
        ∀z : nativeManifold hk V hV,z.val∈(geoTransformAlong M T).cosupp →
          (invFamily hn ((n-k)+q)).inv M T z.val=
            familyDimensionMap (n-k) q ((invFamily hkpos q).inv (nativePullback hk W hW M) Q z)

private theorem zero_lower_value_of_induction {n k q : ℕ} {X : CMfd.{0} n}
    (hIH : NativeFamilyTransport q) (hn : 0<n) (hkpos : 0<k) (hk : k≤n)
    (W : Set X) (hWc : IsClosed W) (hW : ∀x∈W,RegularAtDim (n:=n) W x k)
    (M : MarkedIdeal n X) (hM : IsInvDomain (q+1) M) (hMN : M.N⊆W)
    (hTrans : IsTransverse n W M.E) (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (a0 : nativeManifold hk W hW) (ha0 : a0.val∈M.cosupp)
    {Y Z : CMfd.{0} n}{T : BlowupTower X Y}{S : BlowupTower Y Z}
    {V : Set Y}{hVc : IsClosed V}{hV : ∀y∈V,RegularAtDim (n:=n) V y k}
    {V' : Set Z}{hV'c : IsClosed V'}{hV' : ∀z∈V',RegularAtDim (n:=n) V' z k}
    {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}
    {R : BlowupTower (nativeManifold hk V hV) (nativeManifold hk V' hV')}
    (hHead : Lift hk W hWc hW M.E T V hVc hV Q)
    (hTail : Lift hk V hVc hV (boundary M.E T) S V' hV'c hV' R)
    (hUpper : IsGeoTestTower (barMarked M) (T.append S))
    (z : nativeManifold hk V' hV') (hzq : Q.proj (R.proj z)=a0)
    (hz : z.val∈(geoTransformAlong (barMarked M) (T.append S)).cosupp)
    (hl : level M T (R.proj z).val=0)
    (hZ : (R.proj z).val∉CodimOneSupportAlong.codimOnePartAlong (geoTransformAlong (barMarked M) T).N
      (geoTransformAlong (barMarked M) T).ideal (geoTransformAlong (barMarked M) T).d)
    (a : openPreimage S (maskB M T (R.proj z).val)) (ha : a.val=z.val)
    (b : openPreimage R (maskB (nativePullback hk W hW M) Q (R.proj z))) (hb : b.val=z)
    (hDom : IsInvDomain ((n-k)+q) (lowerMarkedB M T (R.proj z).val))
    (hCan : IsCanonical (lowerMarkedB M T (R.proj z).val)
      ((invFamily hn ((n-k)+q)).inv (lowerMarkedB M T (R.proj z).val))
        (restrict (maskB M T (R.proj z).val) S))
    (hCos : a∈(geoTransformAlong (lowerMarkedB M T (R.proj z).val)
      (restrict (maskB M T (R.proj z).val) S)).cosupp)
    (hNativeDom : IsInvDomain q (lowerMarkedB (nativePullback hk W hW M) Q (R.proj z)))
    (hNativeCan : IsCanonical (lowerMarkedB (nativePullback hk W hW M) Q (R.proj z))
      ((invFamily hkpos q).inv (lowerMarkedB (nativePullback hk W hW M) Q (R.proj z)))
        (restrict (maskB (nativePullback hk W hW M) Q (R.proj z)) R))
    (hNativeCos : b∈(geoTransformAlong (lowerMarkedB (nativePullback hk W hW M) Q (R.proj z))
      (restrict (maskB (nativePullback hk W hW M) Q (R.proj z)) R)).cosupp) :
    (invFamily hn ((n-k)+q)).inv (lowerMarkedB M T (R.proj z).val)
        (restrict (maskB M T (R.proj z).val) S) a=
      familyDimensionMap (n-k) q ((invFamily hkpos q).inv (lowerMarkedB (nativePullback hk W hW M) Q (R.proj z))
        (restrict (maskB (nativePullback hk W hW M) Q (R.proj z)) R) b) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  let := chartedSpace hk hV
  have := isComplexManifold_chartedSpace hk hV
  let := chartedSpace hk hV'
  have := isComplexManifold_chartedSpace hk hV'
  let K:=nativePullback hk W hW M
  let p:=R.proj z
  let AM:=maskB M T p.val
  let KM:=maskB K Q p
  let AU:=HironakaDisjointNativeContactReference.contactHead M (StepOneValue.tangentChoice M (T.proj p.val)).2 T
  let KV:=HironakaDisjointNativeContactReference.contactHead K (StepOneValue.tangentChoice K (Q.proj p)).2 Q
  obtain ⟨G,_hqd,_hqc,hAll⟩:=exists_original_zero_tail_domain_frame hn hk W hWc hW M hM hMN hTrans hmax a0 ha0
  obtain ⟨Φ,χ,_hGlue,_hχ,pG,_hpG,_hFixP,O,_hpO,f,g,_hf,hg,_hfval,hgval,_hRaw,zO,hzO,
    B,hBA,_hpB,Ψ,_hΨ,hLBN,hLBT,hLB,hJ,_hN0Dom,hWhole,hSc,hS,P,ν,hActual,hFrame,_hPoint,hNuZ,
    _hN0Test,_hJPTest,hLBTest,_F,_hF,_hFz,_hRecords⟩:=hAll hHead hTail hUpper z hzq hz hl hZ
  let := chartedSpace hk (openSection_regular hV B)
  have := isComplexManifold_chartedSpace hk (openSection_regular hV B)
  let := chartedSpace hk hS
  have := isComplexManifold_chartedSpace hk hS
  let L:=lowerMarkedB M T p.val
  let LB:=markedPullback (m:=n) (fun y : B=>⟨y.val,hBA y.property⟩ : B→AM) L
  let J:=nativePullback hk (openSection V B) (openSection_regular hV B) LB
  let N0:=MarkedIdeal.pullback g (lowerMarkedB K Q p)
  have hT:=(isGeoTestTower_append_iff (barMarked M) T S).mp hUpper |>.1
  have hAU : AU.ideal.IsCoherent:=ContactStageKept.isCoherent_restrictedCoeff M hM.isWellFormed.isCoherent
    hM.isWellFormed.isClosedSubmanifold_N _ T hT
  have hInc : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (fun y : B=>⟨y.val,hBA y.property⟩ : B→AM):=
    (ContMDiff.subtypeVal_comp_iff AM _).mp contMDiff_subtype_val
  have hLBRecord : LB=MarkedIdeal.pullback (Subtype.val : B→Y) AU:=
    (whole_markedPullback_comp contMDiff_subtype_val hInc AU hAU).symm
  obtain ⟨_hLBCoarse,hLBCan,hLBValue⟩:=Seq.MaxLocusLocal.restrict_nestedOpens (invFamily hn ((n-k)+q))
    hAU hBA hDom S hCan
  rw [←hLBRecord] at hLBCan hLBValue
  have hAUHol : ∀y t,AU.ideal.mem y t → HolomorphicAt n t y:=fun _ _ ht=>GermIdeal.IsCoherent.holomorphicAt_mem hAU ht
  have hCurrentHol:=holomorphic_geoTransformAlong AU hAUHol S
  have hCosRaw : a.val∈(geoTransformAlong AU S).cosupp:=by
    have hCos : a∈(geoTransformAlong (MarkedIdeal.pullback (Subtype.val : AM→Y) AU) (restrict AM S)).cosupp:=hCos
    rw [geoTransformAlong_restrict_of_hhol AU hAUHol AM S,
      cosupp_pullback_val _ hCurrentHol (openPreimage S AM)] at hCos
    exact hCos
  have hCosLB : (ν zO).val∈(geoTransformAlong LB (restrict B S)).cosupp:=by
    rw [hLBRecord,geoTransformAlong_restrict_of_hhol AU hAUHol B S,
      cosupp_pullback_val _ hCurrentHol (openPreimage S B)]
    change (ν zO).val.val∈(geoTransformAlong AU S).cosupp
    rw [hNuZ,←ha]
    exact hCosRaw
  obtain ⟨hNativePCan,hValue⟩:=hIH hn hkpos hk (openSection V B) (hVc.preimage continuous_subtype_val)
    (openSection_regular hV B) LB hLB hLBN hLBT hActual hLBCan
  have hVal:=hValue (ν zO) hCosLB
  have hSourceValue : (invFamily hn ((n-k)+q)).inv LB (restrict B S) (ν zO).val=
      (invFamily hn ((n-k)+q)).inv L (restrict AM S) a:=by
    have hv:=hLBValue (ν zO).val hCosLB
    apply hv.trans
    apply congrArg ((invFamily hn ((n-k)+q)).inv L (restrict AM S))
    exact Subtype.ext (hNuZ.trans ha.symm)
  have hNative:=actual_split_native_original_test hHead hTail hn hM.isWellFormed.isSNCDivisor hTrans
    M rfl hMN hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent hM.one_le_d hmax hUpper
  obtain ⟨hKN,hKI,_hKmax,_hKcos⟩:=HironakaActualNativeSectionContactChoices.native_source_geometry
    hk hW M hMN hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent hmax
  have hBar:=(coeff_homAlong_wEquiv K hKN hKI hM.one_le_d).2 (Q.append R) |>.1.mpr hNative
  have hQ:=(isGeoTestTower_append_iff (barMarked K) Q R).mp hBar |>.1
  have hKV : KV.ideal.IsCoherent:=ContactStageKept.isCoherent_restrictedCoeff K hKI hKN _ Q hQ
  have hOwn:=double_restrict_original_value (invFamily hkpos q) KV hKV R KM (openPreimage Q G.dom)
    hNativeDom hNativeCan O g hg hgval zO b (hb.trans hzO.symm) hNativeCos
  have hJPCos : ν zO∈(geoTransformAlong J P).cosupp:=by
    rw [HironakaActualNativeSectionOrderHistory.Lift.current_cosupport hActual hn hLB.isWellFormed.isSNCDivisor
      hLBT LB rfl hLBN (fun _ _ ht=>GermIdeal.IsCoherent.holomorphicAt_mem hLB.isWellFormed.isCoherent ht)]
    exact hCosLB
  have hViaFrame:=(invFamily hkpos q).isInvValue.towerIso Ψ J hJ
    (restrict O (restrict (openPreimage Q G.dom) R)) P ν hFrame hNativePCan zO hJPCos
  rw [hWhole] at hViaFrame
  have hNativeValue : (invFamily hkpos q).inv J P (ν zO)=
      (invFamily hkpos q).inv (lowerMarkedB K Q p) (restrict KM R) b:=hViaFrame.symm.trans hOwn.2
  exact hSourceValue.symm.trans (hVal.trans (congrArg (familyDimensionMap (n-k) q) hNativeValue))

private theorem positive_lower_value_of_induction {n k q : ℕ} {X : CMfd.{0} n}
    (hIH : NativeFamilyTransport q) (hn : 0<n) (hkpos : 0<k) (hk : k≤n)
    (W : Set X) (hWc : IsClosed W) (hW : ∀x∈W,RegularAtDim (n:=n) W x k)
    (M : MarkedIdeal n X) (hM : IsInvDomain (q+1) M) (hMN : M.N⊆W)
    (hTrans : IsTransverse n W M.E) (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    {Y Z : CMfd.{0} n}{T : BlowupTower X Y}{S : BlowupTower Y Z}
    {V : Set Y}{hVc : IsClosed V}{hV : ∀y∈V,RegularAtDim (n:=n) V y k}
    {V' : Set Z}{hV'c : IsClosed V'}{hV' : ∀z∈V',RegularAtDim (n:=n) V' z k}
    {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}
    {R : BlowupTower (nativeManifold hk V hV) (nativeManifold hk V' hV')}
    (hHead : Lift hk W hWc hW M.E T V hVc hV Q)
    (hTail : Lift hk V hVc hV (boundary M.E T) S V' hV'c hV' R)
    (hUpper : IsGeoTestTower (barMarked M) (T.append S))
    (s : ℕ) (z : nativeManifold hk V' hV')
    (hz : z.val∈(geoTransformAlong (barMarked M) (T.append S)).cosupp)
    (hl : level M T (R.proj z).val=s+1) (hns : ¬IsSpecial M T (R.proj z).val)
    (a : openPreimage S (maskA M T (R.proj z).val)) (ha : a.val=z.val)
    (b : openPreimage R (maskA (nativePullback hk W hW M) Q (R.proj z))) (hb : b.val=z)
    (hDom : IsInvDomain ((n-k)+q) (lowerMarkedM M (s+1) T (R.proj z).val))
    (hCan : IsCanonical (lowerMarkedM M (s+1) T (R.proj z).val)
      ((invFamily hn ((n-k)+q)).inv (lowerMarkedM M (s+1) T (R.proj z).val))
        (restrict (maskA M T (R.proj z).val) S))
    (hCos : a∈(geoTransformAlong (lowerMarkedM M (s+1) T (R.proj z).val)
      (restrict (maskA M T (R.proj z).val) S)).cosupp)
    (hNativeDom : IsInvDomain q (lowerMarkedM (nativePullback hk W hW M) (s+1) Q (R.proj z)))
    (hNativeCan : IsCanonical (lowerMarkedM (nativePullback hk W hW M) (s+1) Q (R.proj z))
      ((invFamily hkpos q).inv (lowerMarkedM (nativePullback hk W hW M) (s+1) Q (R.proj z)))
        (restrict (maskA (nativePullback hk W hW M) Q (R.proj z)) R))
    (hNativeCos : b∈(geoTransformAlong (lowerMarkedM (nativePullback hk W hW M) (s+1) Q (R.proj z))
      (restrict (maskA (nativePullback hk W hW M) Q (R.proj z)) R)).cosupp) :
    (invFamily hn ((n-k)+q)).inv (lowerMarkedM M (s+1) T (R.proj z).val)
        (restrict (maskA M T (R.proj z).val) S) a=
      familyDimensionMap (n-k) q ((invFamily hkpos q).inv (lowerMarkedM (nativePullback hk W hW M) (s+1) Q (R.proj z))
        (restrict (maskA (nativePullback hk W hW M) Q (R.proj z)) R) b) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  let := chartedSpace hk hV
  have := isComplexManifold_chartedSpace hk hV
  let := chartedSpace hk hV'
  have := isComplexManifold_chartedSpace hk hV'
  let K:=nativePullback hk W hW M
  let p:=R.proj z
  let AM:=maskA M T p.val
  let KM:=maskA K Q p
  let MT:=geoTransformAlong (barMarked M) T
  let LA:=memberRestrict MT (membersThrough MT.E (origMembers M T) p.val)
  let KB:=memberRestrict (geoTransformAlong (barMarked K) Q)
    (membersThrough (geoTransformAlong (barMarked K) Q).E (origMembers K Q) p)
  let L:=lowerMarkedM M (s+1) T p.val
  have ⟨hT,hSUpper⟩:=(isGeoTestTower_append_iff (barMarked M) T S).mp hUpper
  have hMTWF:=MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong (isWellFormed_barMarked M hM.isWellFormed) T hT
  have hLAWF : LA.IsWellFormed:=isWellFormed_memberRestrict hn hMTWF _
  have hLA : LA.ideal.IsCoherent:=hLAWF.isCoherent
  have hzS : z.val∈(geoTransformAlong MT S).cosupp:=by rw [←geoTransformAlong_append];exact hz
  have hpCos : p.val∈MT.cosupp:=by
    have ht:=proj_mem_cosupp_of_mem_cosupp hMTWF.isClosedSubmanifold_N hMTWF.isCoherent S hSUpper hzS
    rw [hTail.square z] at ht
    exact ht
  have hFineLower:=StepOneValueMasked.mem_lowerMask_and_isInvDomain_M M hM.isWellFormed hM.one_le_d hn hmax
    hM.dimLE T hT hpCos (show stepRegime M (s+1) T p.val from ⟨hl,hns⟩)
  have hL : IsInvDomain q L:=by simpa only [Nat.add_sub_cancel] using hFineLower.2
  have hEN : MT.E=boundary M.E T:=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪:=barMarked M) (𝔫:=(⟨univ,M.E,IdealWeightPowers.unitIdeal n X,1⟩ : MarkedIdeal n X)) rfl T
  have hSub : LA.E.Sublist MT.E:=by rw [memberRestrict_membersThrough_E];exact List.filter_sublist
  have hSmall:=HironakaActualNativeSectionPositiveLowerRecords.Lift.forget_boundary hTail
    (E':=LA.E) (by rw [←hEN];exact hSub)
  have hLAN : LA.N⊆V:=fun _ ht=>HironakaActualNativeSectionOrderHistory.Lift.current_carrier_subset hHead (barMarked M) hMN ht.1
  have hLN : L.N⊆openSection V AM:=fun _ ht=>hLAN ht
  obtain ⟨_hCurrentSNC,hCurrentTrans⟩:=hHead.geometry hn hM.isWellFormed.isSNCDivisor hTrans
  rw [←hEN] at hCurrentTrans
  have hLATrans : IsTransverse n V LA.E:=isTransverse_of_forall_mem hCurrentTrans hSub.subset
  have hLTrans : IsTransverse n (openSection V AM) L.E:=isTransverse_preimage (pullsBackCoordinates_val AM) hLATrans
  let σ:=positiveMaskSection M hM.isWellFormed hMN hTrans hHead hn p
  have hσ:=positiveMaskSection_contMDiff M hM.isWellFormed hMN hTrans hHead hn p
  have hRecord:=original_positive_lower_record M hM.isWellFormed hMN hTrans hHead hn s p
  let O : Opens KM:=⊤
  let Φ:=Diffeomorph.refl 𝓘(ℂ,ComplexModel k) (CMfd.of (n:=k) KM) ∞
  let χ:=Diffeomorph.refl 𝓘(ℂ,ComplexModel k) (CMfd.of (n:=k) (openPreimage R KM)) ∞
  let f : O→AM:=σ ∘ (Subtype.val : O→KM)
  let g : O→KM:=Subtype.val
  have hg : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k) ∞ g:=contMDiff_subtype_val
  have hRaw : markedPullback (m:=k) f L=MarkedIdeal.pullback g (lowerMarkedM K (s+1) Q p):=by
    have ht:=whole_markedPullback_comp hσ hg L hL.isWellFormed.isCoherent
    have he:=congrArg (fun A : MarkedIdeal k (CMfd.of (n:=k) KM)=>MarkedIdeal.pullback g A) hRecord
    exact ht.trans he
  have hOA : ∀w : O,(Φ w.val).val.val∈AM:=fun w=>(f w).property
  obtain ⟨B,hBA,hTrace,_hBc,Ψ,hΨ,hLBN,hLBT,hLB,hJ,hWhole,_hChanged⟩:=exists_native_window_domain hn hk V hVc hV
    KM KM Φ O AM hOA L hL hLN hLTrans
  have hMap : (fun w : O=>⟨(Φ w.val).val.val,hOA w⟩ : O→AM)=f:=rfl
  rw [hMap,hRaw] at hWhole
  have hFlat:=BlowupTowerIsomorphism.IsTowerIso.refl_self (restrict KM R)
  obtain ⟨hSc,hS,P,ν,hActual,hFrame,hPoint⟩:=exists_actual_changed_tail_frame hSmall KM KM Φ χ hFlat O B hTrace Ψ hΨ
  let := chartedSpace hk (openSection_regular hV B)
  have := isComplexManifold_chartedSpace hk (openSection_regular hV B)
  let := chartedSpace hk hS
  have := isComplexManifold_chartedSpace hk hS
  let LB:=markedPullback (m:=n) (fun y : B=>⟨y.val,hBA y.property⟩ : B→AM) L
  let J:=nativePullback hk (openSection V B) (openSection_regular hV B) LB
  let zO : openPreimage (restrict KM R) O:=⟨b,by trivial⟩
  have hNuZ : (ν zO).val.val=z.val:=by
    have ht:=hPoint zO
    exact ht.trans (congrArg Subtype.val hb)
  have hLBE : LB.E=LA.E.map ((Subtype.val : B→Y) ⁻¹' ·):=by
    change (LA.E.map ((Subtype.val : AM→Y) ⁻¹' ·)).map
      ((fun y : B=>⟨y.val,hBA y.property⟩ : B→AM) ⁻¹' ·)=_
    rw [List.map_map]
    rfl
  have hActual : Lift hk (openSection V B) (hVc.preimage continuous_subtype_val) (openSection_regular hV B)
      LB.E (restrict B S) (openSection V' (openPreimage S B)) hSc hS P:=hLBE.symm ▸ hActual
  have hInc : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (fun y : B=>⟨y.val,hBA y.property⟩ : B→AM):=
    (ContMDiff.subtypeVal_comp_iff AM _).mp contMDiff_subtype_val
  have hLBRecord : LB=MarkedIdeal.pullback (Subtype.val : B→Y) LA:=
    (whole_markedPullback_comp contMDiff_subtype_val hInc LA hLA).symm
  obtain ⟨_hLBCoarse,hLBCan,hLBValue⟩:=Seq.MaxLocusLocal.restrict_nestedOpens (invFamily hn ((n-k)+q))
    hLA hBA hDom S hCan
  rw [←hLBRecord] at hLBCan hLBValue
  have hLAHol : ∀y t,LA.ideal.mem y t → HolomorphicAt n t y:=fun _ _ ht=>GermIdeal.IsCoherent.holomorphicAt_mem hLA ht
  have hCurrentHol:=holomorphic_geoTransformAlong LA hLAHol S
  have hCosRaw : a.val∈(geoTransformAlong LA S).cosupp:=by
    have hCos : a∈(geoTransformAlong (MarkedIdeal.pullback (Subtype.val : AM→Y) LA) (restrict AM S)).cosupp:=hCos
    rw [geoTransformAlong_restrict_of_hhol LA hLAHol AM S,
      cosupp_pullback_val _ hCurrentHol (openPreimage S AM)] at hCos
    exact hCos
  have hCosLB : (ν zO).val∈(geoTransformAlong LB (restrict B S)).cosupp:=by
    rw [hLBRecord,geoTransformAlong_restrict_of_hhol LA hLAHol B S,
      cosupp_pullback_val _ hCurrentHol (openPreimage S B)]
    change (ν zO).val.val∈(geoTransformAlong LA S).cosupp
    rw [hNuZ,←ha]
    exact hCosRaw
  obtain ⟨hNativePCan,hValue⟩:=hIH hn hkpos hk (openSection V B) (hVc.preimage continuous_subtype_val)
    (openSection_regular hV B) LB hLB hLBN hLBT hActual hLBCan
  have hVal:=hValue (ν zO) hCosLB
  have hSourceValue : (invFamily hn ((n-k)+q)).inv LB (restrict B S) (ν zO).val=
      (invFamily hn ((n-k)+q)).inv L (restrict AM S) a:=by
    have hv:=hLBValue (ν zO).val hCosLB
    apply hv.trans
    apply congrArg ((invFamily hn ((n-k)+q)).inv L (restrict AM S))
    exact Subtype.ext (hNuZ.trans ha.symm)
  have hNative:=actual_split_native_original_test hHead hTail hn hM.isWellFormed.isSNCDivisor hTrans
    M rfl hMN hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent hM.one_le_d hmax hUpper
  have hKDom:=isInvDomain_nativePullback hn hk hW M hM hMN hTrans
  obtain ⟨hKN,hKI,_hKmax,_hKcos⟩:=HironakaActualNativeSectionContactChoices.native_source_geometry
    hk hW M hMN hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent hmax
  have hBar:=(coeff_homAlong_wEquiv K hKN hKI hM.one_le_d).2 (Q.append R) |>.1.mpr hNative
  have hQ:=(isGeoTestTower_append_iff (barMarked K) Q R).mp hBar |>.1
  have hKQWF:=MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong (isWellFormed_barMarked K hKDom.isWellFormed) Q hQ
  have hKB : KB.ideal.IsCoherent:=(isWellFormed_memberRestrict hkpos hKQWF _).isCoherent
  have hOwn:=double_restrict_original_value (invFamily hkpos q) KB hKB R KM KM hNativeDom hNativeCan
    O g hg (fun _=>rfl) zO b rfl hNativeCos
  have hJPCos : ν zO∈(geoTransformAlong J P).cosupp:=by
    rw [HironakaActualNativeSectionOrderHistory.Lift.current_cosupport hActual hn hLB.isWellFormed.isSNCDivisor
      hLBT LB rfl hLBN (fun _ _ ht=>GermIdeal.IsCoherent.holomorphicAt_mem hLB.isWellFormed.isCoherent ht)]
    exact hCosLB
  have hViaFrame:=(invFamily hkpos q).isInvValue.towerIso Ψ J hJ
    (restrict O (restrict KM R)) P ν hFrame hNativePCan zO hJPCos
  rw [hWhole] at hViaFrame
  have hNativeValue : (invFamily hkpos q).inv J P (ν zO)=
      (invFamily hkpos q).inv (lowerMarkedM K (s+1) Q p) (restrict KM R) b:=hViaFrame.symm.trans hOwn.2
  exact hSourceValue.symm.trans (hVal.trans (congrArg (familyDimensionMap (n-k) q) hNativeValue))

private theorem lower_value_recast {k d : ℕ} {Λ : Type} [LinearOrder Λ]
    (I : ResolutionInvariantSeq.ResolutionInvariant.{0,0} k d Λ) {X D D' F : CMfd.{0} k}
    (M : MarkedIdeal k X) (s : ℕ) (e : D=D') (Q : BlowupTower X D) (R : BlowupTower D F) (z : F) :
    Seq.StepOneValueMasked.lowerValueL I M (lowerMarkedM M) s (recastTarget e Q) (recastSource e R) z=
      Seq.StepOneValueMasked.lowerValueL I M (lowerMarkedM M) s Q R z := by
  cases e
  rfl

private theorem lower_data_recast {k d : ℕ} {Λ : Type} [LinearOrder Λ]
    (I : ResolutionInvariantSeq.ResolutionInvariant.{0,0} k d Λ) {X D D' F : CMfd.{0} k}
    (M : MarkedIdeal k X) (s : ℕ) (e : D=D') (Q : BlowupTower X D) (R : BlowupTower D F) (z : F)
    (h : Seq.StepOneValueMasked.LowerDataL I M (lowerMarkedM M) s Q R z) :
    Seq.StepOneValueMasked.LowerDataL I M (lowerMarkedM M) s (recastTarget e Q) (recastSource e R) z := by
  cases e
  exact h

private theorem lower_data_projection {k d : ℕ} {Λ : Type} [LinearOrder Λ]
    (I : ResolutionInvariantSeq.ResolutionInvariant.{0,0} k d Λ) {X D F : CMfd.{0} k}
    (M : MarkedIdeal k X) (s : ℕ) (T : BlowupTower X D) (S : BlowupTower D F)
    (z : F) (p : D) (he : S.proj z=p)
    (h : Seq.StepOneValueMasked.LowerDataL I M (lowerMarkedM M) s T S z) :
    ∃hp : p∈lowerMask M s T p,
      IsInvDomain d (lowerMarkedM M s T p) ∧
      IsCanonical (lowerMarkedM M s T p) (I.inv (lowerMarkedM M s T p)) (restrict (lowerMask M s T p) S) ∧
      (⟨z,he.symm ▸ hp⟩ : openPreimage S (lowerMask M s T p))∈
        (geoTransformAlong (lowerMarkedM M s T p) (restrict (lowerMask M s T p) S)).cosupp := by
  cases he
  exact h

private theorem lower_value_projection {k d : ℕ} {Λ : Type} [LinearOrder Λ]
    (I : ResolutionInvariantSeq.ResolutionInvariant.{0,0} k d Λ) {X D F : CMfd.{0} k}
    (M : MarkedIdeal k X) (s : ℕ) (T : BlowupTower X D) (S : BlowupTower D F)
    (z : F) (p : D) (he : S.proj z=p) (hp : p∈lowerMask M s T p) :
    Seq.StepOneValueMasked.lowerValueL I M (lowerMarkedM M) s T S z=
      ((I.inv (lowerMarkedM M s T p) (restrict (lowerMask M s T p) S)
        (⟨z,he.symm ▸ hp⟩ : openPreimage S (lowerMask M s T p)) : Λ) : WithTop Λ) := by
  cases he
  exact Seq.StepOneValueMasked.lowerValueL_eq_of_mem I M (lowerMarkedM M) hp

private theorem step_value_of_current_native_canonical {n k q : ℕ} {X : CMfd.{0} n}
    (hIH : NativeFamilyTransport q) (hn : 0<n) (hkpos : 0<k) (hk : k≤n)
    (W : Set X) (hWc : IsClosed W) (hW : ∀x∈W,RegularAtDim (n:=n) W x k)
    (M : MarkedIdeal n X) (hM : IsInvDomain (q+1) M) (hMN : M.N⊆W)
    (hTrans : IsTransverse n W M.E) (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    {Y : CMfd.{0} n}{T : BlowupTower X Y}{V : Set Y}{hVc : IsClosed V}
    {hV : ∀y∈V,RegularAtDim (n:=n) V y k}
    {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}
    (h : Lift hk W hWc hW M.E T V hVc hV Q)
    (hCan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn ((n-k)+q)) M) T)
    (hNativeCan : IsCanonical (nativePullback hk W hW M)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily hkpos q) (nativePullback hk W hW M)) Q)
    (z : nativeManifold hk V hV) (hz : z.val∈(geoTransformAlong M T).cosupp) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn ((n-k)+q)) M T z.val=
      stepDimensionMap (familyDimensionMap (n-k) q)
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hkpos q) (nativePullback hk W hW M) Q z) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  let := chartedSpace hk hV
  have := isComplexManifold_chartedSpace hk hV
  let K:=nativePullback hk W hW M
  have hCoarse : IsInvDomain (((n-k)+q)+1) M:=domain_mono hM (by omega)
  have hKDom : IsInvDomain (q+1) K:=isInvDomain_nativePullback hn hk hW M hM hMN hTrans
  obtain ⟨_hKN,_hKI,hKmax,_hKcos⟩:=HironakaActualNativeSectionContactChoices.native_source_geometry
    hk hW M hMN hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent hmax
  obtain ⟨hTBar,hTOrig,hTCos⟩:=Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (invFamily hn ((n-k)+q)) M hCoarse hmax hn T hCan
  obtain ⟨hQBar,_hQOrig,hQCos⟩:=Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (invFamily hkpos q) K hKDom hKmax hkpos Q hNativeCan
  have hCanBar:=(Seq.StepOneBridge.isCanonical_iff (invFamily hn ((n-k)+q)) M hCoarse hmax hn T).mp hCan
  have hNativeCanBar:=(Seq.StepOneBridge.isCanonical_iff (invFamily hkpos q) K hKDom hKmax hkpos Q).mp hNativeCan
  have hzBar : z.val∈(geoTransformAlong (barMarked M) T).cosupp:=hTCos.symm ▸ hz
  have hQDict:=HironakaActualNativeSectionOrderHistory.Lift.current_cosupport h hn hM.isWellFormed.isSNCDivisor hTrans
    M rfl hMN (fun _ _ ht=>GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent ht)
  have hzK : z∈(geoTransformAlong K Q).cosupp:=by rw [hQDict];exact hz
  have hzKBar : z∈(geoTransformAlong (barMarked K) Q).cosupp:=hQCos.symm ▸ hzK
  obtain ⟨_hRec,_hOrig,hLS,_hReg,hRuns⟩:=original_step_one_chronology M hM.isWellFormed hMN hTrans h hn
  by_cases hsp : IsSpecial M T z.val
  · have hspK : IsSpecial K Q z:=(hLS z).2.mp hsp
    unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_pos hsp,if_pos hspK,(hLS z).1]
    simp only [stepDimensionMap,ofLex_toLex,WithTop.map_top]
  have hnsK : ¬IsSpecial K Q z:=fun ht=>hsp ((hLS z).2.mpr ht)
  let m:=level M T z.val
  let r:=regimeRun (stepRegime M m) T z.val
  have hLevelK : level K Q z=m:=(hLS z).1.symm
  have hRunK : regimeRun (stepRegime K (level K Q z)) Q z=r:=by
    rw [hLevelK]
    exact (hRuns m z).symm
  have hD:=Seq.StepOneCanonicalTail.hasLowerDataL_of_isCanonical M (k:=((n-k)+q)+1)
    (invFamily hn ((n-k)+q)) hM.isWellFormed hM.one_le_d hn hmax hCoarse.dimLE T hTBar hCanBar z.val hzBar hsp
  have hDK:=Seq.StepOneCanonicalTail.hasLowerDataL_of_isCanonical K (k:=q+1)
    (invFamily hkpos q) hKDom.isWellFormed hKDom.one_le_d hkpos hKmax hKDom.dimLE Q hQBar hNativeCanBar z hzKBar hnsK
  rw [hRunK,hLevelK] at hDK
  have hHeadReg:=StepOneValueMasked.stepRegime_and_mem_cosupp_head M hM.isWellFormed T hTBar hzBar hsp |>.1
  obtain ⟨A,hAc,hA,e,hHead,hTail⟩:=HironakaActualNativeSectionOriginalCuts.Lift.original_head_tails h r
  let := chartedSpace hk hA
  have := isComplexManifold_chartedSpace hk hA
  let T0:=head T r
  let S0:=tail T r
  let Q0:=recastTarget e (head Q r)
  let R0:=recastSource e (tail Q r)
  let p:=R0.proj z
  have hSquare : S0.proj z.val=p.val:=hTail.square z
  have hD : Seq.StepOneValueMasked.LowerDataL (invFamily hn ((n-k)+q)) M (lowerMarkedM M) m T0 S0 z.val:=hD
  have hDK : Seq.StepOneValueMasked.LowerDataL (invFamily hkpos q) K (lowerMarkedM K) m (head Q r) (tail Q r) z:=hDK
  have hDK0:=lower_data_recast (invFamily hkpos q) K m e (head Q r) (tail Q r) z hDK
  have hHeadReg : stepRegime M m T0 (S0.proj z.val):=hHeadReg
  have hD:=lower_data_projection (invFamily hn ((n-k)+q)) M m T0 S0 z.val p.val hSquare hD
  unfold Seq.StepOneValueMasked.LowerDataL at hDK0
  rw [hSquare] at hHeadReg
  have hUpper : IsGeoTestTower (barMarked M) (T0.append S0):=by
    simpa only [T0,S0,head_append_tail] using hTBar
  have hzUpper : z.val∈(geoTransformAlong (barMarked M) (T0.append S0)).cosupp:=by
    simpa only [T0,S0,head_append_tail] using hzBar
  have hOrigUpper : IsGeoTestTower M (T0.append S0):=by
    simpa only [T0,S0,head_append_tail] using hTOrig
  have hzOrigUpper : z.val∈(geoTransformAlong M (T0.append S0)).cosupp:=by
    simpa only [T0,S0,head_append_tail] using hz
  let a0:=Q0.proj p
  have ha0 : a0.val∈M.cosupp:=by
    have ht:=proj_mem_cosupp_of_mem_cosupp hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent
      (T0.append S0) hOrigUpper hzOrigUpper
    have he : (T0.append S0).proj z.val=a0.val:=by
      rw [BlowupTower.proj_append]
      change T0.proj (S0.proj z.val)=a0.val
      rw [hSquare,hHead.square p]
    rw [he] at ht
    exact ht
  have hLower : Seq.StepOneValueMasked.lowerValueL (invFamily hn ((n-k)+q)) M (lowerMarkedM M) m T0 S0 z.val=
      WithTop.map (familyDimensionMap (n-k) q)
        (Seq.StepOneValueMasked.lowerValueL (invFamily hkpos q) K (lowerMarkedM K) m Q0 R0 z) := by
    cases hm : m with
    | zero =>
      rw [hm] at hD hDK0 hHeadReg
      obtain ⟨hpA,hDom,hCanLow,hCosLow⟩:=hD
      obtain ⟨hpK,hNativeDom,hNativeCanLow,hNativeCos⟩:=hDK0
      let a : openPreimage S0 (maskB M T0 p.val):=⟨z.val,hSquare.symm ▸ hpA⟩
      let b : openPreimage R0 (maskB K Q0 p):=⟨z,hpK⟩
      have hAvoid : p.val∉CodimOneSupportAlong.codimOnePartAlong (geoTransformAlong (barMarked M) T0).N
          (geoTransformAlong (barMarked M) T0).ideal (geoTransformAlong (barMarked M) T0).d:=(interior_subset hpA).2.2
      have hv:=zero_lower_value_of_induction hIH hn hkpos hk W hWc hW M hM hMN hTrans hmax a0 ha0
        hHead hTail hUpper z rfl hzUpper hHeadReg.1 hAvoid a rfl b rfl hDom hCanLow hCosLow
        hNativeDom hNativeCanLow hNativeCos
      rw [lower_value_projection (invFamily hn ((n-k)+q)) M 0 T0 S0 z.val p.val hSquare hpA,
        Seq.StepOneValueMasked.lowerValueL_eq_of_mem (invFamily hkpos q) K (lowerMarkedM K) hpK]
      simp only [WithTop.map_coe]
      exact congrArg (fun v : ValTy ((n-k)+q)=>(v : WithTop (ValTy ((n-k)+q)))) hv
    | succ s =>
      rw [hm] at hD hDK0 hHeadReg
      obtain ⟨hpA,hDom,hCanLow,hCosLow⟩:=hD
      obtain ⟨hpK,hNativeDom,hNativeCanLow,hNativeCos⟩:=hDK0
      let a : openPreimage S0 (maskA M T0 p.val):=⟨z.val,hSquare.symm ▸ hpA⟩
      let b : openPreimage R0 (maskA K Q0 p):=⟨z,hpK⟩
      have hv:=positive_lower_value_of_induction hIH hn hkpos hk W hWc hW M hM hMN hTrans hmax
        hHead hTail hUpper s z hzUpper hHeadReg.1 hHeadReg.2 a rfl b rfl hDom hCanLow hCosLow
        hNativeDom hNativeCanLow hNativeCos
      rw [lower_value_projection (invFamily hn ((n-k)+q)) M (s+1) T0 S0 z.val p.val hSquare hpA,
        Seq.StepOneValueMasked.lowerValueL_eq_of_mem (invFamily hkpos q) K (lowerMarkedM K) hpK]
      simp only [WithTop.map_coe]
      exact congrArg (fun v : ValTy ((n-k)+q)=>(v : WithTop (ValTy ((n-k)+q)))) hv
  unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
  rw [if_neg hsp,if_neg hnsK,hRunK,hLevelK]
  change toLex (m,Seq.StepOneValueMasked.lowerValueL (invFamily hn ((n-k)+q)) M (lowerMarkedM M) m T0 S0 z.val)=_
  rw [←lower_value_recast (invFamily hkpos q) K m e (head Q r) (tail Q r) z,hLower]
  simp only [stepDimensionMap,ofLex_toLex]
  rfl

private theorem trace_centre_of_values {A B Λ Γ : Type} [LinearOrder Λ] [LinearOrder Γ]
    (ι : B→A) (hι : Function.Injective ι) (S : Set A) (S' : Set B) (hS : S'=ι ⁻¹' S)
    (f : A→Λ) (g : B→Γ) (δ : Γ→Λ) (hδ : StrictMono δ)
    (hv : ∀z,ι z∈S → f (ι z)=δ (g z)) (D : Set B)
    (hC : ι '' D=∅ ∨ ι '' D=ResolutionDriver.maxLocus f S) :
    D=∅ ∨ D=ResolutionDriver.maxLocus g S' := by
  rcases hC with hC|hC
  · exact Or.inl (image_eq_empty.mp hC)
  have ht:=MaxLocusLocal.preimage_maxLocus_eq_or ι hδ
    (show S'⊆ι ⁻¹' S by rw [hS]) (fun z hz=>hv z (by change z∈ι ⁻¹' S;rw [←hS];exact hz))
    (fun z hz hbad=>False.elim (hbad (by rw [hS];exact hz)))
  rw [←hC,preimage_image_eq D hι] at ht
  exact ht

private theorem step_family_of_induction {n k q : ℕ} {X : CMfd.{0} n}
    (hIH : NativeFamilyTransport q) (hn : 0<n) (hkpos : 0<k) (hk : k≤n)
    (W : Set X) (hWc : IsClosed W) (hW : ∀x∈W,RegularAtDim (n:=n) W x k)
    (M : MarkedIdeal n X) (hM : IsInvDomain (q+1) M) (hMN : M.N⊆W)
    (hTrans : IsTransverse n W M.E) (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    {Y : CMfd.{0} n}{T : BlowupTower X Y}{V : Set Y}{hVc : IsClosed V}
    {hV : ∀y∈V,RegularAtDim (n:=n) V y k}
    {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}
    (h : Lift hk W hWc hW M.E T V hVc hV Q)
    (hCan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn ((n-k)+q)) M) T) :
    IsCanonical (nativePullback hk W hW M)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily hkpos q) (nativePullback hk W hW M)) Q ∧
      ∀z : nativeManifold hk V hV,z.val∈(geoTransformAlong M T).cosupp →
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn ((n-k)+q)) M T z.val=
          stepDimensionMap (familyDimensionMap (n-k) q)
            (Seq.StepOneValueMasked.stepOneInvM (invFamily hkpos q) (nativePullback hk W hW M) Q z) := by
  induction h with
  | refl =>
    refine ⟨trivial,fun z hz=>?_⟩
    exact step_value_of_current_native_canonical hIH hn hkpos hk W hWc hW M hM hMN hTrans hmax
      Lift.refl hCan trivial z hz
  | @step Y Z T V hVc hV Q h D hD hint π hπ hNC ih =>
    let := chartedSpace hk hV
    have := isComplexManifold_chartedSpace hk hV
    obtain ⟨hPrefix,hC⟩:=hCan
    obtain ⟨hNativePrefix,hValues⟩:=ih hPrefix
    have hCos:=HironakaActualNativeSectionOrderHistory.Lift.current_cosupport h hn hM.isWellFormed.isSNCDivisor hTrans
      M rfl hMN (fun _ _ ht=>GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent ht)
    have hNativeCentre:=trace_centre_of_values (Subtype.val : V→Y) Subtype.val_injective
      (geoTransformAlong M T).cosupp (geoTransformAlong (nativePullback hk W hW M) Q).cosupp hCos
      (Seq.StepOneValueMasked.stepOneInvM (invFamily hn ((n-k)+q)) M T)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily hkpos q) (nativePullback hk W hW M) Q)
      (stepDimensionMap (familyDimensionMap (n-k) q))
      (strictMono_stepDimensionMap (strictMono_familyDimensionMap (n-k) q)) hValues D hC
    have hCurrent : IsCanonical (nativePullback hk W hW M)
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hkpos q) (nativePullback hk W hW M))
        (.step Q D (nativeProjection hk hVc hV D π hπ) (nativeProjection_genuine hk hVc hV D hD hint π hπ)):=
      ⟨hNativePrefix,hNativeCentre⟩
    refine ⟨hCurrent,fun z hz=>?_⟩
    exact step_value_of_current_native_canonical hIH hn hkpos hk W hWc hW M hM hMN hTrans hmax
      (Lift.step h D hD hint π hπ hNC) ⟨hPrefix,hC⟩ hCurrent z hz

private theorem actual_open_mask_frame {n k : ℕ} {X : CMfd.{0} n}
    {hk : k≤n} {W : Set X} {hWc : IsClosed W} {hW : ∀x∈W,RegularAtDim (n:=n) W x k}
    {E : List (Set X)} {Y : CMfd.{0} n} {T : BlowupTower X Y}
    {V : Set Y} {hVc : IsClosed V} {hV : ∀y∈V,RegularAtDim (n:=n) V y k}
    {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}
    (h : Lift hk W hWc hW E T V hVc hV Q) (A : Opens X) (B : Opens (nativeManifold hk W hW))
    (hMatch : ∀p : nativeManifold hk W hW,p∈nativeWindow hk W hW A ↔ p∈B) :
    ∃(hSc : IsClosed (openSection V (openPreimage T A)))
      (hS : ∀y∈openSection V (openPreimage T A),RegularAtDim (n:=n) (openSection V (openPreimage T A)) y k)
      (P : BlowupTower (nativeManifold hk (openSection W A) (openSection_regular hW A))
        (nativeManifold hk (openSection V (openPreimage T A)) hS))
      (Φ : nativeManifold hk (openSection W A) (openSection_regular hW A) ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯
        CMfd.of (n:=k) B)
      (χ : nativeManifold hk (openSection V (openPreimage T A)) hS ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯
        CMfd.of (n:=k) (openPreimage Q B)),
      Lift hk (openSection W A) (hWc.preimage continuous_subtype_val) (openSection_regular hW A)
        (E.map ((Subtype.val : A→X) ⁻¹' ·)) (restrict A T) (openSection V (openPreimage T A)) hSc hS P ∧
      IsTowerIso Φ P (restrict B Q) χ ∧
      (∀y,(Φ y).val.val=y.val.val) ∧ (∀z,(χ z).val.val=z.val.val) ∧
      ∀(L : MarkedIdeal n X),L.ideal.IsCoherent →
        MarkedIdeal.pullback Φ (MarkedIdeal.pullback (Subtype.val : B→nativeManifold hk W hW) (nativePullback hk W hW L))=
          nativePullback hk (openSection W A) (openSection_regular hW A) (MarkedIdeal.pullback (Subtype.val : A→X) L) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  let := chartedSpace hk hV
  have := isComplexManifold_chartedSpace hk hV
  let NW:=nativeWindow hk W hW A
  let α:=diffeoOpens (Diffeomorph.refl 𝓘(ℂ,ComplexModel k) (nativeManifold hk W hW) ∞) NW B hMatch
  have hEnd:=isTowerIso_mem_openPreimage_iff (IsTowerIso.refl_self Q) hMatch
  let β:=diffeoOpens (Diffeomorph.refl 𝓘(ℂ,ComplexModel k) (nativeManifold hk V hV) ∞)
    (openPreimage Q NW) (openPreimage Q B) hEnd
  have hMaskIso : IsTowerIso α (restrict NW Q) (restrict B Q) β:=
    isTowerIso_restrictOpens hMatch (IsTowerIso.refl_self Q) hEnd
  obtain ⟨hSc,hS,P,hActual,hFrame⟩:=exists_open_lift h A
  let := chartedSpace hk (openSection_regular hW A)
  have := isComplexManifold_chartedSpace hk (openSection_regular hW A)
  let := chartedSpace hk hS
  have := isComplexManifold_chartedSpace hk hS
  let Φ:=(windowEquiv hk W hW hWc A).trans α
  let χ:=(endpointEquiv h A).trans β
  refine ⟨hSc,hS,P,Φ,χ,hActual,hFrame.trans hMaskIso,fun _=>rfl,?_,?_⟩
  · intro z
    exact endpointEquiv_val_native h A z
  intro L hL
  let J:=nativePullback hk W hW L
  have hJ : J.ideal.IsCoherent:=isCoherent_pullback (contMDiff_val hk hW) hL
  have hJB : (MarkedIdeal.pullback (Subtype.val : B→nativeManifold hk W hW) J).ideal.IsCoherent:=
    isCoherent_pullback contMDiff_subtype_val hJ
  have hAlpha : MarkedIdeal.pullback α (MarkedIdeal.pullback (Subtype.val : B→nativeManifold hk W hW) J)=
      MarkedIdeal.pullback (Subtype.val : NW→nativeManifold hk W hW) J:=
    (whole_markedPullback_comp contMDiff_subtype_val α.contMDiff J hJ).symm
  have hComp:=whole_markedPullback_comp α.contMDiff (windowEquiv hk W hW hWc A).contMDiff
    (MarkedIdeal.pullback (Subtype.val : B→nativeManifold hk W hW) J) hJB
  have hInner:=congrArg (fun L : MarkedIdeal k (CMfd.of (n:=k) NW)=>MarkedIdeal.pullback (windowEquiv hk W hW hWc A) L) hAlpha
  have hInitial:=HironakaDisjointRecursiveNativeHistory.native_open_initial_record hk W hWc hW A L hL
  exact hComp.trans (hInner.trans hInitial.symm)

private theorem companion_step_value_of_induction {n k q : ℕ} {X : CMfd.{0} n}
    (hIH : NativeFamilyTransport q) (hn : 0<n) (hkpos : 0<k) (hk : k≤n)
    (W : Set X) (hWc : IsClosed W) (hW : ∀x∈W,RegularAtDim (n:=n) W x k)
    (M : MarkedIdeal n X) (hM : IsInvDomain (q+1) M) (hMN : M.N⊆W) (hTrans : IsTransverse n W M.E)
    {Y Z : CMfd.{0} n}{T : BlowupTower X Y}{S : BlowupTower Y Z}
    {V : Set Y}{hVc : IsClosed V}{hV : ∀y∈V,RegularAtDim (n:=n) V y k}
    {V' : Set Z}{hV'c : IsClosed V'}{hV' : ∀z∈V',RegularAtDim (n:=n) V' z k}
    {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}
    {R : BlowupTower (nativeManifold hk V hV) (nativeManifold hk V' hV')}
    (hHead : Lift hk W hWc hW M.E T V hVc hV Q)
    (hTail : Lift hk V hVc hV (boundary M.E T) S V' hV'c hV' R)
    (hUpper : IsGeoTestTower M (T.append S)) (o : ℕ) (ho : 1≤o)
    (z : nativeManifold hk V' hV')
    (a : openPreimage S (ordMask (geoTransformAlong M T) o)) (ha : a.val=z.val)
    (b : openPreimage R (ordMask (geoTransformAlong (nativePullback hk W hW M) Q) o)) (hb : b.val=z)
    (hMax : IsMaximalOrderAlong (compAt M o T).N (compAt M o T).ideal (compAt M o T).d)
    (hCan : IsCanonical (compAt M o T) (Seq.StepOneValueMasked.stepOneInvM (invFamily hn ((n-k)+q)) (compAt M o T))
      (restrict (ordMask (geoTransformAlong M T) o) S))
    (hCos : a∈(geoTransformAlong (compAt M o T) (restrict (ordMask (geoTransformAlong M T) o) S)).cosupp)
    (hNativeDom : IsInvDomain (q+1) (compAt (nativePullback hk W hW M) o Q))
    (hNativeMax : IsMaximalOrderAlong (compAt (nativePullback hk W hW M) o Q).N
      (compAt (nativePullback hk W hW M) o Q).ideal (compAt (nativePullback hk W hW M) o Q).d)
    (hNativeCan : IsCanonical (compAt (nativePullback hk W hW M) o Q)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily hkpos q) (compAt (nativePullback hk W hW M) o Q))
        (restrict (ordMask (geoTransformAlong (nativePullback hk W hW M) Q) o) R))
    (hNativeCos : b∈(geoTransformAlong (compAt (nativePullback hk W hW M) o Q)
      (restrict (ordMask (geoTransformAlong (nativePullback hk W hW M) Q) o) R)).cosupp) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn ((n-k)+q)) (compAt M o T)
        (restrict (ordMask (geoTransformAlong M T) o) S) a=
      stepDimensionMap (familyDimensionMap (n-k) q)
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hkpos q) (compAt (nativePullback hk W hW M) o Q)
          (restrict (ordMask (geoTransformAlong (nativePullback hk W hW M) Q) o) R) b) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  let := chartedSpace hk hV
  have := isComplexManifold_chartedSpace hk hV
  let := chartedSpace hk hV'
  have := isComplexManifold_chartedSpace hk hV'
  let K:=nativePullback hk W hW M
  let MT:=geoTransformAlong M T
  let KQ:=geoTransformAlong K Q
  let AM:=ordMask MT o
  let KM:=ordMask KQ o
  let L0:=CompanionRebase.companionOf n MT o
  let L:=compAt M o T
  let LK:=compAt K o Q
  have hT:=(isGeoTestTower_append_iff M T S).mp hUpper |>.1
  have hMT:=isInvDomain_geoTransformAlong hM T hT
  have hL0 : IsInvDomain (q+1) L0:=InvDomainCompanion.isInvDomain_companionAlong hn hMT ho
  have hEN : MT.E=boundary M.E T:=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪:=M) (𝔫:=(⟨univ,M.E,IdealWeightPowers.unitIdeal n X,1⟩ : MarkedIdeal n X)) rfl T
  obtain ⟨_hCurrentSNC,hCurrentTrans⟩:=hHead.geometry hn hM.isWellFormed.isSNCDivisor hTrans
  rw [←hEN] at hCurrentTrans
  have hSupport:=HironakaActualNativeSectionOrderHistory.Lift.current_carrier_subset hHead M hMN
  have hRec:=hHead.whole_records hn hM.isWellFormed.isSNCDivisor hTrans M rfl hMN
    (fun _ _ ht=>GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent ht)
  have hRec : KQ=nativePullback hk V hV MT:=hRec
  have hSourceRecord : MarkedIdeal.pullback (Subtype.val : AM→Y) L0=L:=
    CompanionRebase.pullback_val_companionOf hn hMT.isWellFormed hMT.isNonzeroAlongAt AM o
  have hLFine : IsInvDomain (q+1) L:=by
    rw [←hSourceRecord]
    exact isInvDomain_pullback_val AM hL0
  have hL0N : L0.N⊆V:=by
    simpa only [L0,CompanionRebase.companionOf,CompanionReductionAlong.companionAlong_N] using hSupport
  have hLN : L.N⊆openSection V AM:=by rw [←hSourceRecord];exact fun _ ht=>hL0N ht
  have hLE : L.E=(boundary M.E T).map ((Subtype.val : AM→Y) ⁻¹' ·):=by
    rw [←hSourceRecord]
    simpa only [L0,MarkedIdeal.pullback,CompanionRebase.companionOf,CompanionReductionAlong.companionAlong_E] using
      congrArg (fun E=>E.map ((Subtype.val : AM→Y) ⁻¹' ·)) hEN
  have hLTrans : IsTransverse n (openSection V AM) L.E:=by
    have ht:=isTransverse_preimage (pullsBackCoordinates_val AM) hCurrentTrans
    rw [hEN,←hLE] at ht
    exact ht
  have hKQ : IsInvDomain (q+1) KQ:=by
    rw [hRec]
    exact isInvDomain_nativePullback hn hk hV MT hMT hSupport hCurrentTrans
  have hNativeRaw:=nativePullback_companionOf hn hk hV MT hMT hSupport hCurrentTrans o
  rw [←hRec] at hNativeRaw
  have hNativeRecord : MarkedIdeal.pullback (Subtype.val : KM→nativeManifold hk V hV)
      (nativePullback hk V hV L0)=LK:=by
    rw [hNativeRaw]
    exact CompanionRebase.pullback_val_companionOf hkpos hKQ.isWellFormed hKQ.isNonzeroAlongAt KM o
  have hMatch : ∀p : nativeManifold hk V hV,p∈nativeWindow hk V hV AM ↔ p∈KM:=by
    intro p
    have ht:=ordMask_native_iff hn hkpos hk hV MT hMT hSupport hCurrentTrans o p
    rw [←hRec] at ht
    exact ht
  obtain ⟨hSc,hS,P,Φ,χ,hActual,hFrame,_hBasePoint,hEndPoint,hInitial⟩:=actual_open_mask_frame hTail AM KM hMatch
  let := chartedSpace hk (openSection_regular hV AM)
  have := isComplexManifold_chartedSpace hk (openSection_regular hV AM)
  let := chartedSpace hk hS
  have := isComplexManifold_chartedSpace hk hS
  let J:=nativePullback hk (openSection V AM) (openSection_regular hV AM) L
  have hActual : Lift hk (openSection V AM) (hVc.preimage continuous_subtype_val) (openSection_regular hV AM)
      L.E (restrict AM S) (openSection V' (openPreimage S AM)) hSc hS P:=hLE.symm ▸ hActual
  have hWhole : MarkedIdeal.pullback Φ LK=J:=by
    have ht:=hInitial L0 hL0.isWellFormed.isCoherent
    rw [hSourceRecord,hNativeRecord] at ht
    exact ht
  obtain ⟨_hNativePCan,hValues⟩:=step_family_of_induction hIH hn hkpos hk (openSection V AM)
    (hVc.preimage continuous_subtype_val) (openSection_regular hV AM) L hLFine hLN hLTrans hMax hActual hCan
  let y:=χ.symm b
  have hPoint : y.val=a:=by
    apply Subtype.ext
    have ht:=hEndPoint y
    rw [χ.apply_symm_apply] at ht
    exact ht.symm.trans ((congrArg Subtype.val hb).trans ha.symm)
  have hVal:=hValues y (hPoint.symm ▸ hCos)
  have hViaFrame:=(StepOneSeq.isMaxOrderValue_stepOneInvM (k:=q+1) (invFamily hkpos q) hkpos).towerIso
    Φ LK hNativeDom hNativeMax P (restrict KM R) χ hFrame hNativeCan y (by rw [χ.apply_symm_apply];exact hNativeCos)
  rw [hWhole,χ.apply_symm_apply] at hViaFrame
  have hSourceVal : Seq.StepOneValueMasked.stepOneInvM (invFamily hn ((n-k)+q)) L (restrict AM S) a=
      stepDimensionMap (familyDimensionMap (n-k) q) (Seq.StepOneValueMasked.stepOneInvM (invFamily hkpos q) J P y):=by
    rw [←hPoint]
    exact hVal
  exact hSourceVal.trans (congrArg (stepDimensionMap (familyDimensionMap (n-k) q)) hViaFrame)

private theorem gen_data_recast {k d : ℕ} {Λ : Type} [LinearOrder Λ]
    (Fv : ∀{X : CMfd.{0} k},MarkedIdeal k X → ∀{Y : CMfd.{0} k},BlowupTower X Y → Y → Λ)
    {X D D' F : CMfd.{0} k} (M : MarkedIdeal k X) (o : ℕ) (e : D=D')
    (Q : BlowupTower X D) (R : BlowupTower D F) (z : F)
    (h : GenLowerData Fv d M o Q R z) : GenLowerData Fv d M o (recastTarget e Q) (recastSource e R) z := by
  cases e
  exact h

private theorem gen_value_recast {k : ℕ} {Λ : Type} [LinearOrder Λ]
    (Fv : ∀{X : CMfd.{0} k},MarkedIdeal k X → ∀{Y : CMfd.{0} k},BlowupTower X Y → Y → Λ)
    {X D D' F : CMfd.{0} k} (M : MarkedIdeal k X) (o : ℕ) (e : D=D')
    (Q : BlowupTower X D) (R : BlowupTower D F) (z : F) :
    genLowerValue Fv M o (recastTarget e Q) (recastSource e R) z=genLowerValue Fv M o Q R z := by
  cases e
  rfl

private theorem family_value_of_current_native_canonical {n k q : ℕ} {X : CMfd.{0} n}
    (hIH : NativeFamilyTransport q) (hn : 0<n) (hkpos : 0<k) (hk : k≤n)
    (W : Set X) (hWc : IsClosed W) (hW : ∀x∈W,RegularAtDim (n:=n) W x k)
    (M : MarkedIdeal n X) (hM : IsInvDomain (q+1) M) (hMN : M.N⊆W) (hTrans : IsTransverse n W M.E)
    {Y : CMfd.{0} n}{T : BlowupTower X Y}{V : Set Y}{hVc : IsClosed V}
    {hV : ∀y∈V,RegularAtDim (n:=n) V y k}
    {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}
    (h : Lift hk W hWc hW M.E T V hVc hV Q)
    (hCan : IsCanonical M ((invFamily hn ((n-k)+(q+1))).inv M) T)
    (hNativeCan : IsCanonical (nativePullback hk W hW M) ((invFamily hkpos (q+1)).inv (nativePullback hk W hW M)) Q)
    (z : nativeManifold hk V hV) (hz : z.val∈(geoTransformAlong M T).cosupp) :
    (invFamily hn ((n-k)+(q+1))).inv M T z.val=
      familyDimensionMap (n-k) (q+1) ((invFamily hkpos (q+1)).inv (nativePullback hk W hW M) Q z) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  let := chartedSpace hk hV
  have := isComplexManifold_chartedSpace hk hV
  let K:=nativePullback hk W hW M
  have hCoarse : IsInvDomain (((n-k)+q)+1) M:=domain_mono hM (by omega)
  have hKDom : IsInvDomain (q+1) K:=isInvDomain_nativePullback hn hk hW M hM hMN hTrans
  have hT:=ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (invFamily hn ((n-k)+(q+1))).isInvValue hCoarse T hCan
  have hQ:=ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (invFamily hkpos (q+1)).isInvValue hKDom Q hNativeCan
  have hCos:=HironakaActualNativeSectionOrderHistory.Lift.current_cosupport h hn hM.isWellFormed.isSNCDivisor hTrans
    M rfl hMN (fun _ _ ht=>GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent ht)
  have hzK : z∈(geoTransformAlong K Q).cosupp:=by rw [hCos];exact hz
  have hOrder:=HironakaActualNativeSectionOrderHistory.Lift.current_nmOrd h hn hM.isWellFormed.isSNCDivisor hTrans
    M rfl hMN (fun _ _ ht=>GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent ht) z
  by_cases hZero : nmOrd (geoTransformAlong M T) z.val=0
  · exact monomial_family_value hn hkpos M hM hMN hTrans h hT z hZero
  let o:=nmOrd (geoTransformAlong M T) z.val
  have ho : 0<o:=Nat.pos_of_ne_zero hZero
  have hOrderK : nmOrd (geoTransformAlong K Q) z=o:=hOrder.symm
  let r:=regimeRun (OrdRegime M o) T z.val
  have hRunK : regimeRun (OrdRegime K o) Q z=r:=
    (HironakaActualNativeSectionOrderHistory.Lift.original_order_regime_run h hn hM.isWellFormed.isSNCDivisor hTrans
      M rfl hMN (fun _ _ ht=>GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent ht) o z).symm
  let Fs : ∀{A : CMfd.{0} n},MarkedIdeal n A → ∀{B : CMfd.{0} n},BlowupTower A B → B → ℕ ×ₗ WithTop (ValTy ((n-k)+q)):=
    fun {A} L {B} S y=>Seq.StepOneValueMasked.stepOneInvM (X:=A) (invFamily hn ((n-k)+q)) L (Y:=B) S y
  let Fn : ∀{A : CMfd.{0} k},MarkedIdeal k A → ∀{B : CMfd.{0} k},BlowupTower A B → B → ℕ ×ₗ WithTop (ValTy q):=
    fun {A} L {B} S y=>Seq.StepOneValueMasked.stepOneInvM (X:=A) (invFamily hkpos q) L (Y:=B) S y
  have hD:=GeneralCanonicalTail.hasGenLowerData_of_isCanonical Fs
    (StepOneSeq.isMaxOrderValue_stepOneInvM (k:=((n-k)+q)+1) (invFamily hn ((n-k)+q)) hn)
    hn hCoarse T hT hCan z.val hz o rfl ho
  have hDK:=GeneralCanonicalTail.hasGenLowerData_of_isCanonical Fn
    (StepOneSeq.isMaxOrderValue_stepOneInvM (k:=q+1) (invFamily hkpos q) hkpos)
    hkpos hKDom Q hQ hNativeCan z hzK o hOrderK ho
  rw [hRunK] at hDK
  obtain ⟨A,hAc,hA,e,hHead,hTail⟩:=HironakaActualNativeSectionOriginalCuts.Lift.original_head_tails h r
  let := chartedSpace hk hA
  have := isComplexManifold_chartedSpace hk hA
  let T0:=head T r
  let S0:=tail T r
  let Q0:=recastTarget e (head Q r)
  let R0:=recastSource e (tail Q r)
  have hD : GenLowerData Fs (((n-k)+q)+1) M o T0 S0 z.val:=hD
  have hDK : GenLowerData Fn (q+1) K o (head Q r) (tail Q r) z:=hDK
  have hDK0:=gen_data_recast Fn K o e (head Q r) (tail Q r) z hDK
  obtain ⟨hpA,_hDom,hMax,hCanLow,hCosLow⟩:=hD
  obtain ⟨hpK,hNativeDom,hNativeMax,hNativeCanLow,hNativeCos⟩:=hDK0
  let a : openPreimage S0 (ordMask (geoTransformAlong M T0) o):=⟨z.val,hpA⟩
  let b : openPreimage R0 (ordMask (geoTransformAlong K Q0) o):=⟨z,hpK⟩
  have hUpper : IsGeoTestTower M (T0.append S0):=by simpa only [T0,S0,head_append_tail] using hT
  have hComp:=companion_step_value_of_induction hIH hn hkpos hk W hWc hW M hM hMN hTrans hHead hTail
    hUpper o ho z a rfl b rfl hMax hCanLow hCosLow hNativeDom hNativeMax hNativeCanLow hNativeCos
  have hLower : genLowerValue Fs M o T0 S0 z.val=
      WithTop.map (stepDimensionMap (familyDimensionMap (n-k) q))
        (genLowerValue Fn K o (head Q r) (tail Q r) z):=by
    rw [←gen_value_recast Fn K o e (head Q r) (tail Q r) z,
      genLowerValue_eq_of_mem Fs M hpA,genLowerValue_eq_of_mem Fn K hpK]
    simp only [WithTop.map_coe]
    exact congrArg (fun v : ℕ ×ₗ WithTop (ValTy ((n-k)+q))=>(v : WithTop (ℕ ×ₗ WithTop (ValTy ((n-k)+q))))) hComp
  change genInv Fs M T z.val=generalDimensionMap (n-k) (stepDimensionMap (familyDimensionMap (n-k) q)) (genInv Fn K Q z)
  unfold generalDimensionMap genInv genSecond
  rw [show nmOrd (geoTransformAlong M T) z.val=o from rfl,hOrderK,if_neg (ne_of_gt ho),hRunK]
  simp only [if_neg (ne_of_gt ho),ofLex_toLex,Sum.map_inr]
  rw [hLower]

private theorem family_of_induction {n k q : ℕ} {X : CMfd.{0} n}
    (hIH : NativeFamilyTransport q) (hn : 0<n) (hkpos : 0<k) (hk : k≤n)
    (W : Set X) (hWc : IsClosed W) (hW : ∀x∈W,RegularAtDim (n:=n) W x k)
    (M : MarkedIdeal n X) (hM : IsInvDomain (q+1) M) (hMN : M.N⊆W) (hTrans : IsTransverse n W M.E)
    {Y : CMfd.{0} n}{T : BlowupTower X Y}{V : Set Y}{hVc : IsClosed V}
    {hV : ∀y∈V,RegularAtDim (n:=n) V y k}
    {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}
    (h : Lift hk W hWc hW M.E T V hVc hV Q)
    (hCan : IsCanonical M ((invFamily hn ((n-k)+(q+1))).inv M) T) :
    IsCanonical (nativePullback hk W hW M) ((invFamily hkpos (q+1)).inv (nativePullback hk W hW M)) Q ∧
      ∀z : nativeManifold hk V hV,z.val∈(geoTransformAlong M T).cosupp →
        (invFamily hn ((n-k)+(q+1))).inv M T z.val=
          familyDimensionMap (n-k) (q+1) ((invFamily hkpos (q+1)).inv (nativePullback hk W hW M) Q z) := by
  induction h with
  | refl =>
    refine ⟨trivial,fun z hz=>?_⟩
    exact family_value_of_current_native_canonical hIH hn hkpos hk W hWc hW M hM hMN hTrans
      Lift.refl hCan trivial z hz
  | @step Y Z T V hVc hV Q h D hD hint π hπ hNC ih =>
    let := chartedSpace hk hV
    have := isComplexManifold_chartedSpace hk hV
    obtain ⟨hPrefix,hC⟩:=hCan
    obtain ⟨hNativePrefix,hValues⟩:=ih hPrefix
    have hCos:=HironakaActualNativeSectionOrderHistory.Lift.current_cosupport h hn hM.isWellFormed.isSNCDivisor hTrans
      M rfl hMN (fun _ _ ht=>GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent ht)
    have hNativeCentre:=trace_centre_of_values (Subtype.val : V→Y) Subtype.val_injective
      (geoTransformAlong M T).cosupp (geoTransformAlong (nativePullback hk W hW M) Q).cosupp hCos
      ((invFamily hn ((n-k)+(q+1))).inv M T)
      ((invFamily hkpos (q+1)).inv (nativePullback hk W hW M) Q)
      (familyDimensionMap (n-k) (q+1)) (strictMono_familyDimensionMap (n-k) (q+1)) hValues D hC
    have hCurrent : IsCanonical (nativePullback hk W hW M)
        ((invFamily hkpos (q+1)).inv (nativePullback hk W hW M))
        (.step Q D (nativeProjection hk hVc hV D π hπ) (nativeProjection_genuine hk hVc hV D hD hint π hπ)):=
      ⟨hNativePrefix,hNativeCentre⟩
    refine ⟨hCurrent,fun z hz=>?_⟩
    exact family_value_of_current_native_canonical hIH hn hkpos hk W hWc hW M hM hMN hTrans
      (Lift.step h D hD hint π hπ hNC) ⟨hPrefix,hC⟩ hCurrent z hz

private theorem family_transport_all : ∀q : ℕ,NativeFamilyTransport q := by
  intro q
  induction q with
  | zero =>
    intro n k X hn hkpos hk W hWc hW M hM hMN hTrans Y T V hVc hV Q h hCan
    have hCoarse : IsInvDomain ((n-k)+0) M:=domain_mono hM (Nat.zero_le _)
    have hT:=ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
      (invFamily hn ((n-k)+0)).isInvValue hCoarse T hCan
    exact zero_offset_history hn hkpos M hM h hT
  | succ q ih =>
    intro n k X hn hkpos hk W hWc hW M hM hMN hTrans Y T V hVc hV Q h hCan
    exact family_of_induction ih hn hkpos hk W hWc hW M hM hMN hTrans h hCan

/-- ENTIRE original offset-bound recursive values and native canonical centres
on the SAME actual Lift. Tight source bound q is maintained internally through
all lower histories; native CAN, native domain and comparisons are outputs. -/
theorem Lift.original_recursive_values {n k q : ℕ} {X : CMfd.{0} n}
    {hk : k≤n} {W : Set X} {hWc : IsClosed W} {hW : ∀x∈W,RegularAtDim (n:=n) W x k}
    (hn : 0<n) (hkpos : 0<k) (M : MarkedIdeal n X) (hM : IsInvDomain q M)
    (hMN : M.N⊆W) (hTrans : IsTransverse n W M.E)
    {Y : CMfd.{0} n}{T : BlowupTower X Y}{V : Set Y}{hVc : IsClosed V}
    {hV : ∀y∈V,RegularAtDim (n:=n) V y k}
    {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}
    (h : Lift hk W hWc hW M.E T V hVc hV Q)
    (hCan : IsCanonical M ((invFamily hn ((n-k)+q)).inv M) T) :
    IsCanonical (nativePullback hk W hW M) ((invFamily hkpos q).inv (nativePullback hk W hW M)) Q ∧
      ∀z : nativeManifold hk V hV,z.val∈(geoTransformAlong M T).cosupp →
        (invFamily hn ((n-k)+q)).inv M T z.val=
          familyDimensionMap (n-k) q ((invFamily hkpos q).inv (nativePullback hk W hW M) Q z) :=
  family_transport_all q hn hkpos hk W hWc hW M hM hMN hTrans h hCan

/-- For a supported maximal-order record, the original Step One value
and canonical history transport on the actual lift at the offset bound.
The comparison covers both nonspecial lower branches and the special value. -/
theorem Lift.original_step_one_offset_values {n k q : ℕ} {X : CMfd.{0} n}
    {hk : k ≤ n} {W : Set X} {hWc : IsClosed W}
    {hW : ∀ x ∈ W, RegularAtDim (n := n) W x k}
    (hn : 0 < n) (hkpos : 0 < k) (M : MarkedIdeal n X) (hM : IsInvDomain (q + 1) M)
    (hMN : M.N ⊆ W) (hTrans : IsTransverse n W M.E)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    {Y : CMfd.{0} n} {T : BlowupTower X Y} {V : Set Y} {hVc : IsClosed V}
    {hV : ∀ y ∈ V, RegularAtDim (n := n) V y k}
    {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}
    (h : Lift hk W hWc hW M.E T V hVc hV Q)
    (hCan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily hn ((n - k) + q)) M) T) :
    let B := nativePullback hk W hW M
    IsCanonical B (Seq.StepOneValueMasked.stepOneInvM (invFamily hkpos q) B) Q ∧
      ∀ z : nativeManifold hk V hV, z.val ∈ (geoTransformAlong M T).cosupp →
        Seq.StepOneValueMasked.stepOneInvM (invFamily hn ((n - k) + q)) M T z.val =
          stepDimensionMap (familyDimensionMap (n - k) q)
            (Seq.StepOneValueMasked.stepOneInvM (invFamily hkpos q) B Q z) :=
  step_family_of_induction (family_transport_all q) hn hkpos hk W hWc hW M hM hMN hTrans hmax h hCan

/-- ORIGINAL default canonical history produces its genuine SAME native
canonical history, retaining k=0, all prescribed centres/projections and
the resolved endpoint. No native Lift/TEST/domain/CAN certificate is supplied. -/
theorem exists_original_native_canonical_history {n k : ℕ} {X : CMfd.{0} n}
    (hn : 0<n) (hk : k≤n) (W : Set X) (hWc : IsClosed W)
    (hW : ∀x∈W,RegularAtDim (n:=n) W x k)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (hMN : M.N⊆W) (hTrans : IsTransverse n W M.E)
    {Y : CMfd.{0} n} (T : BlowupTower X Y) (hCan : IsCanonical M ((invFamily hn n).inv M) T) :
    ∃(V : Set Y)(hVc : IsClosed V)(hV : ∀y∈V,RegularAtDim (n:=n) V y k)
      (Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)),
      Lift hk W hWc hW M.E T V hVc hV Q ∧ Q.length=T.length ∧
      IsInvDomain k (nativePullback hk W hW M) ∧
      IsCanonical (nativePullback hk W hW M) ((canonicalInvariant k).inv (nativePullback hk W hW M)) Q ∧
      IsGeoTestTower (nativePullback hk W hW M) Q ∧
      (∀hkpos : 0<k,∀z : nativeManifold hk V hV,z.val∈(geoTransformAlong M T).cosupp →
        (invFamily hn ((n-k)+k)).inv M T z.val=
          familyDimensionMap (n-k) k ((invFamily hkpos k).inv (nativePullback hk W hW M) Q z)) ∧
      (IsGeoResolution M T → IsGeoResolution (nativePullback hk W hW M) Q) := by
  have hFine:=isInvDomain_native_support_bound hk hW M hM hMN
  have hT:=ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical (invFamily hn n).isInvValue hM T hCan
  have hCanOffset : IsCanonical M ((invFamily hn ((n-k)+k)).inv M) T:=by
    exact Eq.mpr (congrArg (fun p=>IsCanonical M ((invFamily hn p).inv M) T) (Nat.sub_add_cancel hk)) hCan
  obtain ⟨V,hVc,hV,Q,hLift,hNativeTest⟩:=exists_native_history_of_original_test hn hk W hWc hW M hFine hMN hTrans T hT
  have hNativeDomain:=isInvDomain_nativePullback hn hk hW M hFine hMN hTrans
  have hNativeCanonical : IsCanonical (nativePullback hk W hW M) ((canonicalInvariant k).inv (nativePullback hk W hW M)) Q:=by
    cases k with
    | zero =>
      have hEmpty:=(original_zero_support_test_resolution hW M hM hMN T hT).1
      have hNativeEmpty:=(HironakaActualNativeZeroDimensionalHistory.Lift.isEmptyTower_iff hLift).mp hEmpty
      exact isCanonical_of_isEmptyTower _ _ Q hNativeEmpty
    | succ j =>
      have hRec:=Lift.original_recursive_values hn (Nat.succ_pos j) M hFine hMN hTrans hLift hCanOffset
      exact hRec.1
  refine ⟨V,hVc,hV,Q,hLift,hLift.length,hNativeDomain,hNativeCanonical,hNativeTest,?_,?_⟩
  · intro hkpos
    exact (Lift.original_recursive_values hn hkpos M hFine hMN hTrans hLift hCanOffset).2
  intro hResolved
  refine ⟨hNativeTest,?_⟩
  rw [HironakaActualNativeSectionOrderHistory.Lift.current_cosupport hLift hn hM.isWellFormed.isSNCDivisor hTrans
    M rfl hMN (fun _ _ ht=>GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent ht),hResolved.2,preimage_empty]

end
end Hironaka.HironakaActualNativeRecursiveValues
