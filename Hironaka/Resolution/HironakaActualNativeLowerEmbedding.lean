import Hironaka.Resolution.HironakaActualNativePositiveHistories
import Hironaka.Resolution.HironakaActualNativeSectionZeroHeadRecords
import Hironaka.Resolution.HironakaDisjointNativeOpenLift

/-! Actual closed regular native presentations and invariant domains for
ORIGINAL changed lower-head windows; actual native atlases are constructed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNativeLowerEmbedding
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  ResolutionInvariantSpec InvDomainTowerAlong NormalCrossings NormalCrossingsInvariance
  SubmanifoldChartedSpace SubmanifoldCodRestrict MarkedIdealBiholomorphism
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionRegularity
  HironakaActualNativeSectionOrderHistory HironakaActualNativeSectionNormalCrossings
  HironakaActualNativeInvariantDomain HironakaDisjointNativeOpenLift
  HironakaActualNativeSectionZeroHeadRecords HironakaActualNativeSectionContactChoices
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionOrderedChoiceImageTrace
  HomogenizedIdealAlong HomogenizedIdealAlongTower HomogenizedGlueingAlong HomogenizedGlueingAlongTower HomogenizedGlueingLiftAlong
  HomogenizedGlueingTower MemberInterTowerAlong StepOneValue StepOneValueMasked StepOneLowerDomain
  RelativePrincipalizationSpan GermIdealPullbackCalculus

/-- Construct an ACTUAL closed regular ambient presentation of the ENTIRE
changed native window, inside the prescribed ambient open, with the genuine
native atlas biholomorphism. No closed-image/coordinate certificate is supplied. -/
theorem exists_native_window_atlas {n k : ℕ} {X : CMfd.{0} n}
    (hk : k≤n) (W : Set X) (hWc : IsClosed W)
    (hW : ∀x∈W,RegularAtDim (n:=n) W x k)
    (U U' : Opens (nativeManifold hk W hW))
    (Φ : CMfd.of (n:=k) U ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯ CMfd.of (n:=k) U')
    (O : Opens U) (A : Opens X) (hOA : ∀w : O,(Φ w.val).val.val∈A) :
    ∃B : Opens X,B≤A ∧
      (Subtype.val : W→X) ⁻¹' (B : Set X)=
        (Subtype.val : U'→nativeManifold hk W hW) '' (Φ '' (O : Set U)) ∧
      IsClosed (openSection W B) ∧
      ∃Ψ : CMfd.of (n:=k) O ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯
          nativeManifold hk (openSection W B) (openSection_regular hW B),
        ∀w,(Ψ w).val.val=(Φ w.val).val.val := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  let S : Set (nativeManifold hk W hW):=(Subtype.val : U'→nativeManifold hk W hW) '' (Φ '' (O : Set U))
  have hSO : IsOpen S:=U'.isOpen.isOpenMap_subtype_val _ (Φ.toHomeomorph.isOpenMap _ O.isOpen)
  have hSA : S⊆(Subtype.val : W→X) ⁻¹' (A : Set X):=by
    rintro p ⟨z,⟨w,hw,rfl⟩,rfl⟩
    exact hOA ⟨w,hw⟩
  obtain ⟨B0,hB0,hTrace0⟩:=(Topology.IsInducing.subtypeVal.isOpen_iff).mp hSO
  let B : Opens X:=⟨B0∩(A : Set X),hB0.inter A.isOpen⟩
  have hTrace : (Subtype.val : W→X) ⁻¹' (B : Set X)=S:=by
    ext p
    have hp : p.val∈B0 ↔ p∈S:=Iff.of_eq (congrArg (fun Z : Set W=>p∈Z) hTrace0)
    exact ⟨fun h=>hp.mp h.1,fun h=>⟨hp.mpr h,hSA h⟩⟩
  let := chartedSpace hk (openSection_regular hW B)
  have := isComplexManifold_chartedSpace hk (openSection_regular hW B)
  let toNative : O→nativeManifold hk (openSection W B) (openSection_regular hW B):=fun w=>
    ⟨⟨(Φ w.val).val.val,by
      have hs : (Φ w.val).val∈S:=⟨Φ w.val,⟨w.val,w.property,rfl⟩,rfl⟩
      exact (show (Φ w.val).val∈(Subtype.val : W→X) ⁻¹' (B : Set X) from hTrace.symm ▸ hs)⟩,
      (Φ w.val).val.property⟩
  let base : nativeManifold hk (openSection W B) (openSection_regular hW B)→nativeManifold hk W hW:=
    fun y=>⟨y.val.val,y.property⟩
  have hBaseS (y : nativeManifold hk (openSection W B) (openSection_regular hW B)) : base y∈S:=by
    rw [←hTrace]
    exact y.val.property
  have hBaseCod (y : nativeManifold hk (openSection W B) (openSection_regular hW B)) : base y∈U':=by
    obtain ⟨z,_hz,hz⟩:=hBaseS y
    exact hz ▸ z.property
  let codPoint : nativeManifold hk (openSection W B) (openSection_regular hW B)→U':=
    fun y=>⟨base y,hBaseCod y⟩
  have hInverseO (y : nativeManifold hk (openSection W B) (openSection_regular hW B)) :
      Φ.symm (codPoint y)∈O:=by
    obtain ⟨z,⟨w,hw,hwz⟩,hzbase⟩:=hBaseS y
    have hzcod : z=codPoint y:=Subtype.ext hzbase
    rw [←hzcod,←hwz,Φ.symm_apply_apply]
    exact hw
  let fromNative : nativeManifold hk (openSection W B) (openSection_regular hW B)→O:=
    fun y=>⟨Φ.symm (codPoint y),hInverseO y⟩
  have hCodTo (w : O) : codPoint (toNative w)=Φ w.val:=by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  let Ψ : CMfd.of (n:=k) O ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯
      nativeManifold hk (openSection W B) (openSection_regular hW B):=by
    refine ⟨⟨toNative,fromNative,?_,?_⟩,?_,?_⟩
    · intro w
      apply Subtype.ext
      change Φ.symm (codPoint (toNative w))=w.val
      rw [hCodTo,Φ.symm_apply_apply]
    · intro y
      apply Subtype.ext
      apply Subtype.ext
      change (Φ (Φ.symm (codPoint y))).val.val=y.val.val
      rw [Φ.apply_symm_apply]
    · have hAmbient : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel n) ∞
          (fun w : O=>(toNative w).val):=by
        apply (ContMDiff.subtypeVal_comp_iff B _).mp
        exact (contMDiff_val hk hW).comp
          (contMDiff_subtype_val.comp (Φ.contMDiff.comp contMDiff_subtype_val))
      exact contMDiff_codRestrict hk (openSection_regular hW B) hAmbient
        (fun w=>(Φ w.val).val.property)
    · have hBaseCont : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k) ∞ base:=
        contMDiff_codRestrict hk hW
          (contMDiff_subtype_val.comp (contMDiff_val hk (openSection_regular hW B))) (fun y=>y.property)
      have hCodCont : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k) ∞ codPoint:=
        (ContMDiff.subtypeVal_comp_iff U' codPoint).mp hBaseCont
      apply (ContMDiff.subtypeVal_comp_iff O fromNative).mp
      exact Φ.symm.contMDiff.comp hCodCont
  exact ⟨B,inter_subset_right,hTrace,hWc.preimage continuous_subtype_val,Ψ,fun _=>rfl⟩

private theorem isInvDomain_open_inclusion {n r : ℕ} {X : CMfd.{0} n}
    (A B : Opens X) (hBA : B≤A) (L : MarkedIdeal n (CMfd.of (n:=n) A))
    (hL : IsInvDomain r L) :
    IsInvDomain r (markedPullback (m:=n) (fun y : B=>⟨y.val,hBA y.property⟩ : B→A) L) := by
  let Ξ:=MaxLocusLocal.nestedOpensDiffeo (n:=n) hBA
  have hD:=isInvDomain_pullback Ξ.symm (isInvDomain_pullback_val (MaxLocusLocal.nestedOpens A B) hL)
  have hEq : MarkedIdeal.pullback Ξ.symm
      (MarkedIdeal.pullback (Subtype.val : MaxLocusLocal.nestedOpens A B→A) L)=
      markedPullback (m:=n) (fun y : B=>⟨y.val,hBA y.property⟩ : B→A) L:=
    (whole_markedPullback_comp contMDiff_subtype_val Ξ.symm.contMDiff L hL.isWellFormed.isCoherent).symm
  exact hEq ▸ hD

private theorem coordinates_open_inclusion {n : ℕ} {X : CMfd.{0} n}
    (A B : Opens X) (hBA : B≤A) :
    PullsBackCoordinates n (fun y : B=>⟨y.val,hBA y.property⟩ : B→A) := by
  let Ξ:=MaxLocusLocal.nestedOpensDiffeo (n:=n) hBA
  intro ι F S y hF
  exact MarkedIdealTowerTransport.pullsBackCoordinates Ξ.symm _ S y
    (pullsBackCoordinates_val (MaxLocusLocal.nestedOpens A B) F S (Ξ.symm y) hF)

/-- The ACTUAL changed window obtains a genuine closed regular native source,
its full original ambient/native domains, and whole pullback dictionary. -/
theorem exists_native_window_domain {n k r : ℕ} {X : CMfd.{0} n}
    (hn : 0<n) (hk : k≤n) (W : Set X) (hWc : IsClosed W)
    (hW : ∀x∈W,RegularAtDim (n:=n) W x k)
    (U U' : Opens (nativeManifold hk W hW))
    (Φ : CMfd.of (n:=k) U ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯ CMfd.of (n:=k) U')
    (O : Opens U) (A : Opens X) (hOA : ∀w : O,(Φ w.val).val.val∈A)
    (L : MarkedIdeal n (CMfd.of (n:=n) A)) (hL : IsInvDomain r L)
    (hLN : L.N⊆openSection W A) (hTrans : IsTransverse n (openSection W A) L.E) :
    ∃(B : Opens X)(hBA : B≤A),
      (Subtype.val : W→X) ⁻¹' (B : Set X)=
        (Subtype.val : U'→nativeManifold hk W hW) '' (Φ '' (O : Set U)) ∧
      IsClosed (openSection W B) ∧
      ∃Ψ : CMfd.of (n:=k) O ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯
          nativeManifold hk (openSection W B) (openSection_regular hW B),
        (∀w,(Ψ w).val.val=(Φ w.val).val.val) ∧
        let LB:=markedPullback (m:=n) (fun y : B=>⟨y.val,hBA y.property⟩ : B→A) L
        let J:=nativePullback hk (openSection W B) (openSection_regular hW B) LB
        LB.N⊆openSection W B ∧ IsTransverse n (openSection W B) LB.E ∧
        IsInvDomain r LB ∧ IsInvDomain r J ∧
        MarkedIdeal.pullback Ψ J=markedPullback (m:=k) (fun w : O=>⟨(Φ w.val).val.val,hOA w⟩ : O→A) L ∧
        IsInvDomain r (markedPullback (m:=k) (fun w : O=>⟨(Φ w.val).val.val,hOA w⟩ : O→A) L) := by
  obtain ⟨B,hBA,hTrace,hBc,Ψ,hΨ⟩:=exists_native_window_atlas hk W hWc hW U U' Φ O A hOA
  let := chartedSpace hk (openSection_regular hW B)
  have := isComplexManifold_chartedSpace hk (openSection_regular hW B)
  let fB : B→A:=fun y=>⟨y.val,hBA y.property⟩
  let LB:=markedPullback (m:=n) fB L
  let J:=nativePullback hk (openSection W B) (openSection_regular hW B) LB
  let f : O→A:=fun w=>⟨(Φ w.val).val.val,hOA w⟩
  have hLB : IsInvDomain r LB:=isInvDomain_open_inclusion A B hBA L hL
  have hLBN : LB.N⊆openSection W B:=fun _ hy=>hLN hy
  have hLBT : IsTransverse n (openSection W B) LB.E:=
    isTransverse_preimage (coordinates_open_inclusion A B hBA) hTrans
  have hJ : IsInvDomain r J:=isInvDomain_nativePullback hn hk (openSection_regular hW B) LB hLB hLBN hLBT
  have hfB : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ fB:=
    (ContMDiff.subtypeVal_comp_iff A fB).mp contMDiff_subtype_val
  have hFun : fB ∘ ((Subtype.val : openSection W B→B) ∘ Ψ)=f:=by
    funext w
    apply Subtype.ext
    exact hΨ w
  have hWhole : MarkedIdeal.pullback Ψ J=markedPullback (m:=k) f L:=by
    change markedPullback (m:=k) Ψ
      (markedPullback (m:=k) (Subtype.val : openSection W B→B) (markedPullback (m:=n) fB L))=_
    rw [←whole_markedPullback_comp (contMDiff_val hk (openSection_regular hW B)) Ψ.contMDiff LB hLB.isWellFormed.isCoherent,
      ←whole_markedPullback_comp hfB ((contMDiff_val hk (openSection_regular hW B)).comp Ψ.contMDiff) L hL.isWellFormed.isCoherent]
    rw [hFun]
  refine ⟨B,hBA,hTrace,hBc,Ψ,hΨ,hLBN,hLBT,hLB,hJ,hWhole,?_⟩
  rw [←hWhole]
  exact isInvDomain_pullback Ψ hJ

/-- ONE source contact change gives an actual closed regular lower embedding
and its ORIGINAL ambient/native domains BEFORE ALL actual matched head TESTs.
Lower domain, native TEST and desired record equality are internally produced. -/
theorem exists_original_zero_head_domain_embedding {n k r : ℕ} {X : CMfd.{0} n}
    (hn : 0<n) (hk : k≤n) (W : Set X) (hWc : IsClosed W)
    (hW : ∀x∈W,RegularAtDim (n:=n) W x k)
    (M : MarkedIdeal n X) (hM : IsInvDomain (r+1) M) (hMN : M.N⊆W)
    (hTrans : IsTransverse n W M.E) (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (q : nativeManifold hk W hW) (hq : q.val∈M.cosupp) :
    let K:=nativePullback hk W hW M
    let u:=(tangentChoice M q.val).2 ∘ (Subtype.val : W→X)
    let v:=(tangentChoice K q).2
    ∃G : GlueingDataAlong K.N K.ideal K.d u v,q∈G.dom ∧ q∈G.cod ∧
      ∀{Y : CMfd.{0} n}{T : BlowupTower X Y}{V : Set Y}{hVc : IsClosed V}
        {hV : ∀y∈V,RegularAtDim (n:=n) V y k}
        {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)},
        Lift hk W hWc hW M.E T V hVc hV Q → IsGeoTestTower (barMarked M) T →
        ∀(p : nativeManifold hk V hV),Q.proj p=q →
          p.val∈(geoTransformAlong (barMarked M) T).cosupp → level M T p.val=0 →
          p.val∉CodimOneSupportAlong.codimOnePartAlong (geoTransformAlong (barMarked M) T).N
            (geoTransformAlong (barMarked M) T).ideal (geoTransformAlong (barMarked M) T).d →
          ∃Φ,IsGlueingLiftAlong G Q Φ ∧
            ∃pG : openPreimage Q G.dom,pG.val=p ∧ (Φ pG).val=p ∧
              ∃O : Opens (openPreimage Q G.dom),pG∈O ∧
                ∃(f : O→maskB M T p.val)(g : O→maskB K Q p),
                  (∀w,(f w).val=(Φ w.val).val.val) ∧ (∀w,(g w).val=w.val.val) ∧
                  markedPullback (m:=k) f (lowerMarkedB M T p.val)=MarkedIdeal.pullback g (lowerMarkedB K Q p) ∧
                  ∃(B : Opens Y)(hBA : B≤maskB M T p.val),p.val∈B ∧ IsClosed (openSection V B) ∧
                    ∃Ψ : CMfd.of (n:=k) O ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯
                        nativeManifold hk (openSection V B) (openSection_regular hV B),
                      (∀w,(Ψ w).val.val=(f w).val) ∧
                      let LB:=markedPullback (m:=n)
                        (fun y : B=>⟨y.val,hBA y.property⟩ : B→maskB M T p.val) (lowerMarkedB M T p.val)
                      let J:=nativePullback hk (openSection V B) (openSection_regular hV B) LB
                      LB.N⊆openSection V B ∧ IsTransverse n (openSection V B) LB.E ∧
                      IsInvDomain r LB ∧ IsInvDomain r J ∧
                      MarkedIdeal.pullback Ψ J=MarkedIdeal.pullback g (lowerMarkedB K Q p) ∧
                      IsInvDomain r (MarkedIdeal.pullback g (lowerMarkedB K Q p)) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  let K:=nativePullback hk W hW M
  obtain ⟨_B0,_hqB,_hBU,_hBu,G,hqd,hqc,_hGD,_hGC,hAll⟩:=
    exists_original_zero_head_comparison hn hk W hWc hW M hM.isWellFormed hMN hTrans
      hM.one_le_d hmax q hq
  refine ⟨G,hqd,hqc,?_⟩
  intro Y T V hVc hV Q hLift hT p hpq hp hl hZ
  let := chartedSpace hk hV
  have := isComplexManifold_chartedSpace hk hV
  have hEq:=coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent hM.one_le_d
  have hOriginalTest : IsGeoTestTower M T:=(hEq.2 T).1.mp hT
  have hNativeTest:=HironakaActualNativeSectionNormalCrossings.Lift.native_test hLift hn
    hM.isWellFormed.isSNCDivisor hTrans M rfl hMN
    (fun _ _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg) hOriginalTest
  obtain ⟨Φ,hΦ,pG,hPG,hFix,O,hpO,f,g,_hf,_hg,hfval,hgval,hRaw⟩:=hAll hLift hT hNativeTest p hpq hp hl hZ
  let AM:=maskB M T p.val
  let L:=lowerMarkedB M T p.val
  have hNotSpecial : ¬IsSpecial M T p.val:=by
    rintro (hzero|hpos)
    · exact hZ hzero.2
    · have hposLevel:=hpos.1
      omega
  have hRegime : stepRegime M 0 T p.val:=⟨hl,hNotSpecial⟩
  have hLower:=StepOneValueMasked.mem_lowerMask_and_isInvDomain_M M hM.isWellFormed hM.one_le_d
    hn hmax hM.dimLE T hT hp hRegime
  have hL : IsInvDomain r L:=by
    simpa only [lowerMask,lowerMarkedM,Nat.add_sub_cancel] using hLower.2
  have hLN : L.N⊆openSection V AM:=by
    intro y hy
    change y.val∈strictAlong T (M.N∩{x | (tangentChoice M (T.proj p.val)).2 x=0}) at hy
    have hStrict : y.val∈strictAlong T M.N:=MemberInterTowerAlong.strictAlong_mono T inter_subset_left hy
    have hyCurrent : y.val∈(geoTransformAlong (barMarked M) T).N:=by
      rw [N_geoTransformAlong]
      exact hStrict
    exact HironakaActualNativeSectionOrderHistory.Lift.current_carrier_subset hLift (barMarked M) hMN hyCurrent
  obtain ⟨_hCurrentE,hCurrentTrans⟩:=hLift.geometry hn hM.isWellFormed.isSNCDivisor hTrans
  have hCurrentE : (geoTransformAlong (barMarked M) T).E=boundary M.E T:=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪:=barMarked M) (𝔫:=⟨univ,M.E,IdealWeightPowers.unitIdeal n X,1⟩) rfl T
  rw [←hCurrentE] at hCurrentTrans
  have hLTrans : IsTransverse n (openSection V AM) L.E:=
    isTransverse_preimage (pullsBackCoordinates_val AM) hCurrentTrans
  have hOA : ∀w : O,(Φ w.val).val.val∈AM:=by
    intro w
    rw [←hfval w]
    exact (f w).property
  obtain ⟨B,hBA,hTrace,hBc,Ψ,hΨ,hLBN,hLBT,hLB,hJ,hWhole,hChanged⟩:=exists_native_window_domain hn hk V hVc hV
    (openPreimage Q G.dom) (openPreimage Q G.cod) Φ O AM hOA L hL hLN hLTrans
  have hMapEq : (fun w : O=>⟨(Φ w.val).val.val,hOA w⟩ : O→AM)=f:=by
    funext w
    apply Subtype.ext
    exact (hfval w).symm
  rw [hMapEq,hRaw] at hWhole hChanged
  have hpB : p.val∈B:=by
    have hS : p∈(Subtype.val : V→Y) ⁻¹' (B : Set Y):=by
      rw [hTrace]
      exact ⟨Φ pG,⟨pG,hpO,rfl⟩,hFix⟩
    exact hS
  refine ⟨Φ,hΦ,pG,hPG,hFix,O,hpO,f,g,hfval,hgval,hRaw,B,hBA,hpB,hBc,Ψ,?_,hLBN,hLBT,hLB,hJ,hWhole,hChanged⟩
  intro w
  exact (hΨ w).trans (hfval w).symm

end
end Hironaka.HironakaActualNativeLowerEmbedding
