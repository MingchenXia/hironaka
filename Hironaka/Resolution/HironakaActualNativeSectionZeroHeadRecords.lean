import Hironaka.Resolution.HironakaActualZeroContactWholeRecords
import Hironaka.Resolution.HironakaDisjointNativeContactReference

/-! The original ambient and native zero-head records on an explicitly produced
smaller current native window, with one source glueing before all actual tests. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNativeSectionZeroHeadRecords
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  SubmanifoldChartedSpace NormalCrossings GermIdealOrder GermIdealPullbackCalculus
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen HomogenizedGlueingTower
  HomogenizedGlueingAlongTower HomogenizedGlueingLiftAlong HomogenizedIdealAlong
  HomogenizedIdealAlongTower
  StepOneValue StepOneValueMasked StepOneLowerDomain ContactStageKept CoefficientIdealRestriction
  CodimOneSupportAlong TangentDirectionAlong
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionOrderHistory
  HironakaActualNativeSectionRegularity HironakaActualNativeSectionCoefficientRecords
  HironakaActualNativeSectionContactChoices HironakaActualZeroContactWholeRecords
  HironakaDisjointNativeContactReference HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionOrderedChoiceImageTrace HironakaActualRawRecordPullbacks
  HironakaStepOneZeroContactRemainderExtension HironakaStepOneZeroContactRemainderGlueing

/-- ONE source glueing compares ENTIRE ORIGINAL zero lower records on an
explicit genuine smaller native window containing the SAME current point.
The literal two original masks and every ordered old/born slot are retained. -/
theorem exists_original_zero_head_comparison {n k : ℕ} {X : CMfd.{0} n}
    (hn : 0<n) (hk : k≤n) (W : Set X) (hWc : IsClosed W)
    (hW : ∀x∈W,RegularAtDim (n:=n) W x k)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hNW : M.N⊆W)
    (hTrans : IsTransverse n W M.E) (hd : 1≤M.d)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (q : nativeManifold hk W hW) (hq : q.val∈M.cosupp) :
    let K:=nativePullback hk W hW M
    let u:=(tangentChoice M q.val).2 ∘ (Subtype.val : W→X)
    let v:=(tangentChoice K q).2
    ∃B : Opens (nativeManifold hk W hW),q∈B ∧
      (B : Set (nativeManifold hk W hW))⊆(Subtype.val : W→X) ⁻¹' (tangentChoice M q.val).1 ∧
      IsTangentDirectionAlong K.N K.ideal K.d B u ∧
      ∃G : GlueingDataAlong K.N K.ideal K.d u v,
        q∈G.dom ∧ q∈G.cod ∧
        (G.dom : Set (nativeManifold hk W hW))⊆B∩(tangentChoice K q).1 ∧
        (G.cod : Set (nativeManifold hk W hW))⊆B∩(tangentChoice K q).1 ∧
        ∀{Y : CMfd.{0} n}{T : BlowupTower X Y}{V : Set Y}{hVc : IsClosed V}
          {hV : ∀y∈V,RegularAtDim (n:=n) V y k}
          {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)},
          Lift hk W hWc hW M.E T V hVc hV Q →
          IsGeoTestTower (barMarked M) T → IsGeoTestTower K Q →
          ∀(p : nativeManifold hk V hV),Q.proj p=q →
            p.val∈(geoTransformAlong (barMarked M) T).cosupp → level M T p.val=0 →
            p.val∉codimOnePartAlong (geoTransformAlong (barMarked M) T).N
              (geoTransformAlong (barMarked M) T).ideal (geoTransformAlong (barMarked M) T).d →
            ∃Φ,IsGlueingLiftAlong G Q Φ ∧
              ∃pG : openPreimage Q G.dom,pG.val=p ∧ (Φ pG).val=p ∧
                ∃O : Opens (openPreimage Q G.dom),pG∈O ∧
                  ∃(f : O→maskB M T p.val)(g : O→maskB K Q p),
                    ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel n) ∞ f ∧
                    ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k) ∞ g ∧
                    (∀z,(f z).val=(Φ z.val).val.val) ∧
                    (∀z,(g z).val=z.val.val) ∧
                    markedPullback (m:=k) f (lowerMarkedB M T p.val)=
                      MarkedIdeal.pullback g (lowerMarkedB K Q p) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  let K:=nativePullback hk W hW M
  let ua:=(tangentChoice M q.val).2
  let u:=ua ∘ (Subtype.val : W→X)
  let v:=(tangentChoice K q).2
  have hN:=hM.isClosedSubmanifold_N
  have hI:=hM.isCoherent
  have hE:=hM.isSNCDivisor
  have hhol : ∀x a,M.ideal.mem x a → HolomorphicAt n a x:=
    fun _ _ ha=>RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI ha
  obtain ⟨hKN,hKI,_hKmax,_hKcos⟩:=native_source_geometry hk hW M hNW hN hI hmax
  obtain ⟨U,hUE,hqU,hu,B,hqB,hBU,hBu,L,hLE,hqL,hLv,G,hqd,hqc,hGD,hGC,hAll⟩:=
    exists_native_selected_contact_glueing hk hW M hNW hN hI hd hmax q hq
  refine ⟨B,hqB,?_,hBu,G,hqd,hqc,?_,?_,?_⟩
  · simpa only [hUE] using hBU
  · simpa only [hLE] using hGD
  · simpa only [hLE] using hGC
  intro Y T V hVc hV Q h hT hQ p hpq hp hl hZ
  let := chartedSpace hk hV
  have := isComplexManifold_chartedSpace hk hV
  have hbase : T.proj p.val=q.val:=(h.square p).trans (congrArg Subtype.val hpq)
  have hBar:=nativePullback_barMarked hk hW M hNW hhol
  have hRec:=h.whole_records hn hE hTrans (barMarked M) rfl hNW (fun _ _ ha=>ha.1)
  rw [hBar] at hRec
  have hCos:=HironakaActualNativeSectionOrderHistory.Lift.current_cosupport h hn hE hTrans
    (barMarked M) rfl hNW (fun _ _ ha=>ha.1)
  rw [hBar] at hCos
  have hZpre:=HironakaActualNativeSectionRegularity.Lift.current_codimOnePart h hn hE hTrans
    (barMarked M) rfl hNW (fun _ _ ha=>ha.1)
  rw [hBar] at hZpre
  have hOrig : (origMembers M T).map ((Subtype.val : V→Y) ⁻¹' ·)=origMembers K Q:=by
    have he:=congrArg (fun A : MarkedIdeal k (nativeManifold hk V hV)=>A.E) hRec
    have hlen : K.E.length=M.E.length:=List.length_map _
    change (geoTransformAlong (barMarked K) Q).E=
      (geoTransformAlong (barMarked M) T).E.map ((Subtype.val : V→Y) ⁻¹' ·) at he
    unfold origMembers
    rw [he,hlen,←List.map_take]
  have hNativeZ (z : nativeManifold hk V hV)
      (hz : z.val∉codimOnePartAlong (geoTransformAlong (barMarked M) T).N
        (geoTransformAlong (barMarked M) T).ideal (geoTransformAlong (barMarked M) T).d) :
      z∉codimOnePartAlong (geoTransformAlong (barMarked K) Q).N
        (geoTransformAlong (barMarked K) Q).ideal (geoTransformAlong (barMarked K) Q).d:=by
    intro hbad
    apply hz
    change z∈(Subtype.val : V→Y) ⁻¹'
      codimOnePartAlong (geoTransformAlong (barMarked M) T).N
        (geoTransformAlong (barMarked M) T).ideal (geoTransformAlong (barMarked M) T).d
    rw [hZpre]
    exact hbad
  have hNativeOld (z : nativeManifold hk V hV) (hz : ∀H∈origMembers M T,z.val∉H) :
      ∀H∈origMembers K Q,z∉H:=by
    intro H hH
    rw [←hOrig] at hH
    obtain ⟨H₀,hH₀,rfl⟩:=List.mem_map.mp hH
    exact hz H₀ hH₀
  have hpA : p.val∈maskB M T p.val:=mem_maskB M hM hd hmax T hT hp hl hZ
  let AM:=maskB M T p.val
  let KM:=maskB K Q p
  let Atrace : Opens (nativeManifold hk V hV):=
    ⟨(Subtype.val : V→Y) ⁻¹' (AM : Set Y),AM.isOpen.preimage continuous_subtype_val⟩
  let P:=Atrace⊓openPreimage Q L
  have hPK : (P : Set (nativeManifold hk V hV))⊆(KM : Set (nativeManifold hk V hV)):=by
    apply interior_maximal ?_ P.isOpen
    intro z hz
    have ha:=interior_subset hz.1
    refine ⟨?_,hNativeOld z ha.2.1,hNativeZ z ha.2.2⟩
    rw [hpq,←hLE]
    exact hz.2
  have hpK : p∈KM:=hPK ⟨hpA,by change Q.proj p∈L;rw [hpq];exact hqL⟩
  have heq:=coeff_homAlong_wEquiv K hKN hKI hd
  have hQB : IsGeoTestTower (barMarked K) Q:=(heq.2 Q).1.mpr hQ
  have hpKC : p∈(geoTransformAlong K Q).cosupp:=by
    rw [←(heq.2 Q).2 hQB,hCos]
    exact hp
  obtain ⟨Φ,hLift,hRem,hFix⟩:=hAll Q hQ
  let DG:=openPreimage Q G.dom
  let DC:=openPreimage Q G.cod
  have hpDG : p∈DG:=by change Q.proj p∈G.dom;rw [hpq];exact hqd
  let pG : DG:=⟨p,hpDG⟩
  have hFixp : (Φ pG).val=p:=hFix pG hpKC
  let O : Opens DG:=⟨(Subtype.val : DG→nativeManifold hk V hV) ⁻¹' (KM : Set _) ∩
    (fun z : DG=>(Φ z).val.val) ⁻¹' (AM : Set Y),
    (KM.isOpen.preimage continuous_subtype_val).inter
      (AM.isOpen.preimage (continuous_subtype_val.comp
        (continuous_subtype_val.comp Φ.contMDiff.continuous)))⟩
  have hpO : pG∈O:=⟨hpK,by change (Φ pG).val.val∈AM;rw [hFixp];exact hpA⟩
  let f : O→AM:=fun z=>⟨(Φ z.val).val.val,z.property.2⟩
  let g : O→KM:=fun z=>⟨z.val.val,z.property.1⟩
  have hf : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel n) ∞ f:=by
    apply (ContMDiff.subtypeVal_comp_iff AM f).mp
    exact (contMDiff_val hk hV).comp
      (contMDiff_subtype_val.comp (Φ.contMDiff.comp contMDiff_subtype_val))
  have hg : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k) ∞ g:=by
    apply (ContMDiff.subtypeVal_comp_iff KM g).mp
    change ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k) ∞ (fun z : O=>z.val.val)
    exact contMDiff_subtype_val.comp contMDiff_subtype_val
  refine ⟨Φ,hLift,pG,rfl,hFixp,O,hpO,f,g,hf,hg,fun _=>rfl,fun _=>rfl,?_⟩
  let OU:=Atrace⊓DC
  let OV:=KM⊓DG
  have hOU : OU≤DC:=fun _ hz=>hz.2
  have hOV : OV≤DG:=fun _ hz=>hz.2
  have huC : IsTangentDirectionAlong K.N K.ideal K.d G.cod u:=
    ⟨G.cod.isOpen,fun x hx=>hBu.mem x (hGC hx).1,
      fun x hx hz=>hBu.multiplicity_one x (hGC hx).1 hz⟩
  have hvD : IsTangentDirectionAlong K.N K.ideal K.d G.dom v:=
    ⟨G.dom.isOpen,fun x hx=>hLv.mem x (hGD hx).2,
      fun x hx hz=>hLv.multiplicity_one x (hGD hx).2 hz⟩
  have hRU:=contact_remainder_eq_on_zero_window K hKN hKI hd G.cod u huC Q hQB OU hOU
    (fun z hz=>hNativeZ z (interior_subset hz.1).2.2)
    (fun H hH z hz=>hNativeOld z (interior_subset hz.1).2.1 H hH)
  have hRV:=contact_remainder_eq_on_zero_window K hKN hKI hd G.dom v hvD Q hQB OV hOV
    (fun z hz=>(interior_subset hz.1).2.2)
    (fun H hH z hz=>(interior_subset hz.1).2.1 H hH)
  let r : O→OU:=fun z=>⟨(Φ z.val).val,⟨z.property.2,(Φ z.val).property⟩⟩
  let s : O→OV:=fun z=>⟨z.val.val,⟨z.property.1,z.val.property⟩⟩
  have hr : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k) ∞ r:=by
    apply (ContMDiff.subtypeVal_comp_iff OU r).mp
    change ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k) ∞ (fun z : O=>(Φ z.val).val)
    exact contMDiff_subtype_val.comp (Φ.contMDiff.comp contMDiff_subtype_val)
  have hs : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k) ∞ s:=by
    apply (ContMDiff.subtypeVal_comp_iff OV s).mp
    change ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k) ∞ (fun z : O=>z.val.val)
    exact contMDiff_subtype_val.comp contMDiff_subtype_val
  let AU:=contactHead M ua T
  let KU:=contactHead K u Q
  let KV:=contactHead K v Q
  have hAU : AU.ideal.IsCoherent:=isCoherent_restrictedCoeff M hI hN ua T hT
  have hKU : KU.ideal.IsCoherent:=isCoherent_restrictedCoeff K hKI hKN u Q hQB
  have hKV : KV.ideal.IsCoherent:=isCoherent_restrictedCoeff K hKI hKN v Q hQB
  let RU:=contactRemainderMarked (contactMarkedKept K u Q DC) K.E.length
  let RV:=contactRemainderMarked (contactMarkedKept K v Q DG) K.E.length
  have hRUc : RU.ideal.IsCoherent:=isCoherent_pullback contMDiff_subtype_val hKU
  have hRVc : RV.ideal.IsCoherent:=isCoherent_pullback contMDiff_subtype_val hKV
  let a:=windowInclusion DC OU hOU
  let b:=windowInclusion DG OV hOV
  have ha:=windowInclusion_contMDiff DC OU hOU
  have hb:=windowInclusion_contMDiff DG OV hOV
  have hWhole : markedPullback (m:=k) (fun z : O=>(Φ z.val).val) KU=
      markedPullback (m:=k) (fun z : O=>z.val.val) KV:=by
    calc
      _=markedPullback (m:=k) r (contactMarkedKept K u Q OU):=
        whole_markedPullback_comp contMDiff_subtype_val hr KU hKU
      _=markedPullback (m:=k) r (MarkedIdeal.pullback a RU):=congrArg
        (fun A=>markedPullback (m:=k) r A) hRU.symm
      _=markedPullback (m:=k) (a∘r) RU:=
        (whole_markedPullback_comp ha hr RU hRUc).symm
      _=markedPullback (m:=k) (Φ∘(Subtype.val : O→DG)) RU:=rfl
      _=markedPullback (m:=k) (Subtype.val : O→DG) (MarkedIdeal.pullback Φ RU):=
        whole_markedPullback_comp Φ.contMDiff contMDiff_subtype_val RU hRUc
      _=markedPullback (m:=k) (Subtype.val : O→DG) RV:=congrArg
        (fun A=>markedPullback (m:=k) (Subtype.val : O→DG) A) hRem
      _=markedPullback (m:=k) (b∘s) RV:=rfl
      _=markedPullback (m:=k) s (MarkedIdeal.pullback b RV):=
        whole_markedPullback_comp hb hs RV hRVc
      _=markedPullback (m:=k) s (contactMarkedKept K v Q OV):=congrArg
        (fun A=>markedPullback (m:=k) s A) hRV
      _=markedPullback (m:=k) (fun z : O=>z.val.val) KV:=
        (whole_markedPullback_comp contMDiff_subtype_val hs KV hKV).symm
  have hNative:=native_contact_head h hn hE hTrans M rfl hNW hhol ua
  have hAM : lowerMarkedB M T p.val=MarkedIdeal.pullback (Subtype.val : AM→Y) AU:=by
    simp only [lowerMarkedB,hbase]
    rfl
  have hKM : lowerMarkedB K Q p=MarkedIdeal.pullback
      (Subtype.val : KM→nativeManifold hk V hV) KV:=by
    simp only [lowerMarkedB,hpq]
    rfl
  rw [hAM,hKM]
  calc
    _=markedPullback (m:=k) ((Subtype.val : AM→Y)∘f) AU:=
      (whole_markedPullback_comp contMDiff_subtype_val hf AU hAU).symm
    _=markedPullback (m:=k) (fun z : O=>(Φ z.val).val) (nativePullback hk V hV AU):=
      whole_markedPullback_comp (contMDiff_val hk hV)
        (contMDiff_subtype_val.comp (Φ.contMDiff.comp contMDiff_subtype_val)) AU hAU
    _=markedPullback (m:=k) (fun z : O=>(Φ z.val).val) KU:=by rw [hNative]
    _=markedPullback (m:=k) (fun z : O=>z.val.val) KV:=hWhole
    _=MarkedIdeal.pullback g (MarkedIdeal.pullback
        (Subtype.val : KM→nativeManifold hk V hV) KV):=
      whole_markedPullback_comp contMDiff_subtype_val hg KV hKV

end
end Hironaka.HironakaActualNativeSectionZeroHeadRecords
