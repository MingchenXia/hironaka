import Hironaka.Resolution.HironakaActualNativeSectionZeroTailSubwindows
import Hironaka.Resolution.HironakaStepOneZeroContactRemainderTailGlueing

/-! Whole ORIGINAL independently selected zero-contact records along SAME
actual native and ambient restricted tails. One genuine source glueing is
chosen before every actual split test; only original initial slots are padded. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNativeSectionZeroWholeTails
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  SubmanifoldChartedSpace NormalCrossings NormalCrossingsComparison
  GermIdealOrder GermIdealPullbackCalculus HomogenizedGlueingTower HomogenizedIdealAlong
  HomogenizedIdealAlongTower HomogenizedGlueingAlongTower HomogenizedGlueingLiftAlong
  StepOneValue StepOneValueMasked StepOneLowerDomain StepOneRegime
  TangentDirectionAlong ContactStageKept ContactStageInvDomain CoefficientIdealRestriction
  MaximalOrderStepOneB CodimOneSupportAlong StepOneTangentChange
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionOrderHistory
  HironakaActualNativeSectionRegularity HironakaActualNativeSectionCoefficientRecords
  HironakaActualNativeSectionPositiveLowerRecords HironakaActualNativeSectionContactChoices
  HironakaActualNativeSectionZeroTailSubwindows HironakaActualNativeSectionZeroHeadRecords
  HironakaDisjointNativeContactReference
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionOrderedChoiceImageTrace
  HironakaActualRawRecordPullbacks HironakaStepOneZeroContactRemainderTailGlueing

private theorem contactHead_drop_initial {n : ℕ} {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (u : X→ℂ) (T : BlowupTower X Y) :
    contactHead ({M with E:=[]} : MarkedIdeal n X) u T=
      ({contactHead M u T with E:=(contactHead M u T).E.drop M.E.length} : MarkedIdeal n Y) := by
  change withN (coeffMarkedAlong (geoTransformAlong (stepOneMarked M.N M.ideal M.d) T))
    (strictAlong T (M.N∩{x | u x=0}))=_
  rw [geoTransformAlong_coeffHom_dropE M T]
  rfl

private theorem lowerMarkedB_eq_empty_pad {n : ℕ} {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (T : BlowupTower X Y) (p : Y) :
    let A:=contactMarkedKept ({M with E:=[]} : MarkedIdeal n X)
      (tangentChoice M (T.proj p)).2 T (maskB M T p)
    lowerMarkedB M T p=({A with E:=List.replicate M.E.length ∅ ++ A.E} : MarkedIdeal n (maskB M T p)) := by
  exact pullback_val_restrictedCoeffHom_eq M T (tangentChoice M (T.proj p)).2 (maskB M T p)
    (fun H hH y hy=>(interior_subset hy).2.1 H hH)

/-- The SAME ambient selected function, the independent native choice and
ONE genuine compatible joint-tail glueing BEFORE ALL ORIGINAL native tests.
No native well-formedness or canonicality is supplied. -/
theorem exists_native_selected_joint_tail {n k : ℕ} {X : CMfd.{0} n} {W : Set X}
    (hk : k≤n) (hW : ∀x∈W,RegularAtDim (n:=n) W x k)
    (M : MarkedIdeal n X) (hNW : M.N⊆W)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    (hd : 1≤M.d) (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (q : nativeManifold hk W hW) (hq : q.val∈M.cosupp) :
    let K:=nativePullback hk W hW M
    let u:=(tangentChoice M q.val).2 ∘ (Subtype.val : W→X)
    let v:=(tangentChoice K q).2
    ∃(U : Opens X),(U : Set X)=(tangentChoice M q.val).1 ∧ q.val∈U ∧
      IsTangentDirectionAlong M.N M.ideal M.d U (tangentChoice M q.val).2 ∧
      ∃(B L : Opens (nativeManifold hk W hW)),q∈B ∧ q∈L ∧
        (B : Set (nativeManifold hk W hW))⊆(Subtype.val : W→X) ⁻¹' (U : Set X) ∧
        (L : Set (nativeManifold hk W hW))=(tangentChoice K q).1 ∧
        IsTangentDirectionAlong K.N K.ideal K.d B u ∧
        IsTangentDirectionAlong K.N K.ideal K.d L v ∧
        ∃G : GlueingDataAlong K.N K.ideal K.d u v,
          q∈G.dom ∧ q∈G.cod ∧ (G.dom : Set (nativeManifold hk W hW))⊆B∩L ∧
            (G.cod : Set (nativeManifold hk W hW))⊆B∩L ∧
          ∀{D F : CMfd.{0} k}(P : BlowupTower (nativeManifold hk W hW) D)(R : BlowupTower D F),
            IsGeoTestTower K (P.append R) →
            ∃Φ χ,IsGlueingLiftAlong G P Φ ∧
              IsTowerIso Φ (restrict (openPreimage P G.dom) R) (restrict (openPreimage P G.cod) R) χ ∧
              let A:=contactMarkedKept ({K with E:=[]} : MarkedIdeal k (nativeManifold hk W hW))
                u P (openPreimage P G.cod)
              let B0:=contactMarkedKept ({K with E:=[]} : MarkedIdeal k (nativeManifold hk W hW))
                v P (openPreimage P G.dom)
              MarkedIdeal.pullback Φ A=B0 ∧
              ∃(_hAN : IsClosedSubmanifold k A.N)(_hAI : A.ideal.IsCoherent),
                IsGeoTestTower A (restrict (openPreimage P G.cod) R) ∧
                ∀z : openPreimage R (openPreimage P G.dom),
                  z.val∈(geoTransformAlong K (P.append R)).cosupp → (χ z).val=z.val := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  let K:=nativePullback hk W hW M
  obtain ⟨hKN,hKI,_hKmax,hKcos⟩:=native_source_geometry hk hW M hNW hN hI hmax
  have hqK : q∈K.cosupp:=by rw [hKcos];exact hq
  obtain ⟨U,hUE,hqU,hu,B,hqB,hBU,hBu,L,hLE,hqL,hLv⟩:=
    exists_native_selected_contact_pair hk hW M hNW hN hI hd hmax q hq
  obtain ⟨G,hqd,hqc,hGD,hGC,hAll⟩:=exists_contact_remainder_tail_glueing K hKN hKI hd q hqK
    B L hBu hqB hLv hqL
  have he:=coeff_homAlong_wEquiv K hKN hKI hd
  refine ⟨U,hUE,hqU,hu,B,L,hqB,hqL,hBU,hLE,hBu,hLv,G,hqd,hqc,hGD,hGC,?_⟩
  intro D F P R hPR
  have hBar : IsGeoTestTower (barMarked K) (P.append R):=(he.2 _).1.mpr hPR
  have hEmpty:=isGeoTestTower_stepOneMarked_of_coeffHom K (P.append R) hBar
  obtain ⟨Φ,χ,hLift,hχ,hModel,hAN,hAI,_hdA,hAT,hRest⟩:=hAll P R hEmpty
  refine ⟨Φ,χ,hLift,hχ,hModel,hAN,hAI,hAT,fun z hz=>?_⟩
  apply hRest.2.2.2.2.2 z
  rw [cosupp_geoTransformAlong_stepOneMarked K (P.append R),(he.2 _).2 hBar]
  exact hz

/-- ONE genuine source glueing gives ENTIRE ORIGINAL independent-choice zero
lower records on SAME actual restricted tails, with genuine lower TESTs.
All original, born-before-cut and born-after-cut positions are retained. -/
theorem exists_original_zero_tail_comparison {n k : ℕ} {X : CMfd.{0} n}
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
        ∀{Y Z : CMfd.{0} n}{T : BlowupTower X Y}{S : BlowupTower Y Z}
          {V : Set Y}{hVc : IsClosed V}{hV : ∀y∈V,RegularAtDim (n:=n) V y k}
          {V' : Set Z}{hV'c : IsClosed V'}{hV' : ∀z∈V',RegularAtDim (n:=n) V' z k}
          {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}
          {R : BlowupTower (nativeManifold hk V hV) (nativeManifold hk V' hV')},
          Lift hk W hWc hW M.E T V hVc hV Q →
          Lift hk V hVc hV (boundary M.E T) S V' hV'c hV' R →
          IsGeoTestTower (barMarked M) (T.append S) → IsGeoTestTower K (Q.append R) →
          ∀z : nativeManifold hk V' hV',Q.proj (R.proj z)=q →
            z.val∈(geoTransformAlong (barMarked M) (T.append S)).cosupp →
            level M T (R.proj z).val=0 →
            (R.proj z).val∉codimOnePartAlong (geoTransformAlong (barMarked M) T).N
              (geoTransformAlong (barMarked M) T).ideal (geoTransformAlong (barMarked M) T).d →
            ∃Φ χ,IsGlueingLiftAlong G Q Φ ∧
              IsTowerIso Φ (restrict (openPreimage Q G.dom) R) (restrict (openPreimage Q G.cod) R) χ ∧
              let p:=R.proj z
              let AM:=maskB M T p.val
              let KM:=maskB K Q p
              let DG:=openPreimage Q G.dom
              let P:=restrict DG R
              ∃pG : DG,pG.val=p ∧ (Φ pG).val=p ∧
                ∃O : Opens DG,pG∈O ∧
                  ∃(f : O→AM)(g : O→KM),
                    ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel n) ∞ f ∧
                    ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k) ∞ g ∧
                    (∀w,(f w).val=(Φ w.val).val.val) ∧ (∀w,(g w).val=w.val.val) ∧
                    ∃zO : openPreimage P O,zO.val.val=z ∧
                      ∃F : openPreimage P O → openPreimage S AM,
                        ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel n) ∞ F ∧
                        (∀w,(F w).val=(χ w.val).val.val) ∧ (F zO).val=z.val ∧
                        IsGeoTestTower (MarkedIdeal.pullback g (lowerMarkedB K Q p)) (restrict O P) ∧
                        IsGeoTestTower (lowerMarkedB M T p.val) (restrict AM S) ∧
                        geoTransformAlong (MarkedIdeal.pullback g (lowerMarkedB K Q p)) (restrict O P)=
                          markedPullback (m:=k) F (geoTransformAlong (lowerMarkedB M T p.val) (restrict AM S)) := by
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
  obtain ⟨_Ba,_hqa,_hBa,_huBa,_Ga,_hqad,_hqac,_hGad,_hGac,hHeadAll⟩:=
    exists_original_zero_head_comparison hn hk W hWc hW M hM hNW hTrans hd hmax q hq
  obtain ⟨U,hUE,_hqU,hu,B,L,hqB,_hqL,hBU,hLE,hBu,_hLv,G,hqd,hqc,hGD,hGC,hAll⟩:=
    exists_native_selected_joint_tail hk hW M hNW hN hI hd hmax q hq
  refine ⟨B,hqB,?_,hBu,G,hqd,hqc,?_,?_,?_⟩
  · simpa only [hUE] using hBU
  · simpa only [hLE] using hGD
  · simpa only [hLE] using hGC
  intro Y Z T S V hVc hV V' hV'c hV' Q R h hTail hUpper hNative z hzq hz hl hZ
  let := chartedSpace hk hV
  have := isComplexManifold_chartedSpace hk hV
  let := chartedSpace hk hV'
  have := isComplexManifold_chartedSpace hk hV'
  let p:=R.proj z
  let AM:=maskB M T p.val
  let KM:=maskB K Q p
  have hpq : Q.proj p=q:=hzq
  have hbase : T.proj p.val=q.val:=(h.square p).trans (congrArg Subtype.val hpq)
  obtain ⟨hT,hS⟩:=(isGeoTestTower_append_iff (barMarked M) T S).mp hUpper
  have hQ:=(isGeoTestTower_append_iff K Q R).mp hNative |>.1
  have hBarI:=isCoherent_barMarked M hN hI
  obtain ⟨hMTN,hMTI⟩:=isClosedSubmanifold_N_and_isCoherent_geoTransformAlong (𝔪:=barMarked M) hN hBarI T hT
  have hzS : z.val∈(geoTransformAlong (geoTransformAlong (barMarked M) T) S).cosupp:=by
    rw [←geoTransformAlong_append]
    exact hz
  have hpAcos : p.val∈(geoTransformAlong (barMarked M) T).cosupp:=by
    have hpS:=proj_mem_cosupp_of_mem_cosupp hMTN hMTI S hS hzS
    rw [hTail.square z] at hpS
    exact hpS
  have hpAM : p.val∈AM:=mem_maskB M hM hd hmax T hT hpAcos hl hZ
  obtain ⟨_Φa,_hLa,pa,hpa,_hFpa,Oa,hpOa,_fa,ga,_hfa,_hga,_hfaval,hgaval,_hHeadEq⟩:=
    hHeadAll h hT hQ p hpq hpAcos hl hZ
  have hpKM : p∈KM:=by
    have hg:=(ga ⟨pa,hpOa⟩).property
    rw [hgaval,hpa] at hg
    exact hg
  have hBar:=nativePullback_barMarked hk hW M hNW hhol
  have hRec:=h.whole_records hn hE hTrans (barMarked M) rfl hNW (fun _ _ ha=>ha.1)
  rw [hBar] at hRec
  obtain ⟨hEC,hTC⟩:=h.geometry hn hE hTrans
  have hEN : (geoTransformAlong (barMarked M) T).E=boundary M.E T:=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪:=barMarked M) (𝔫:=(⟨univ,M.E,IdealWeightPowers.unitIdeal n X,1⟩ : MarkedIdeal n X)) rfl T
  have hTailCos:=HironakaActualNativeSectionOrderHistory.Lift.current_cosupport hTail hn hEC hTC
    (geoTransformAlong (barMarked M) T) hEN
    (HironakaActualNativeSectionOrderHistory.Lift.current_carrier_subset h (barMarked M) hNW)
    (holomorphic_geoTransformAlong (barMarked M) (fun _ _ ha=>ha.1) T)
  rw [←hRec] at hTailCos
  have hEndCos : (geoTransformAlong (barMarked K) (Q.append R)).cosupp=
      (Subtype.val : V'→Z) ⁻¹' (geoTransformAlong (barMarked M) (T.append S)).cosupp:=by
    simpa only [geoTransformAlong_append] using hTailCos
  have he:=coeff_homAlong_wEquiv K hKN hKI hd
  have hNativeBar : IsGeoTestTower (barMarked K) (Q.append R):=(he.2 _).1.mpr hNative
  have hzK : z∈(geoTransformAlong K (Q.append R)).cosupp:=by
    rw [←(he.2 _).2 hNativeBar,hEndCos]
    exact hz
  obtain ⟨Φ,χ,hLift,hχ,hModel,hAN,hAI,hAT,hFix⟩:=hAll Q R hNative
  let DG:=openPreimage Q G.dom
  let DC:=openPreimage Q G.cod
  let P:=restrict DG R
  let PC:=restrict DC R
  let K0 : MarkedIdeal k (nativeManifold hk W hW):={K with E:=[]}
  let A0:=contactMarkedKept K0 u Q DC
  let B0:=contactMarkedKept K0 v Q DG
  have hModel : MarkedIdeal.pullback Φ A0=B0:=hModel
  have hAN : IsClosedSubmanifold k A0.N:=hAN
  have hAI : A0.ideal.IsCoherent:=hAI
  have hAT : IsGeoTestTower A0 PC:=hAT
  have hpDG : p∈DG:=by change Q.proj p∈G.dom;rw [hpq];exact hqd
  let pG : DG:=⟨p,hpDG⟩
  let zG : openPreimage R DG:=⟨z,hpDG⟩
  have hFixz : (χ zG).val=z:=hFix zG hzK
  have hpProj : P.proj zG=pG:=Subtype.ext (proj_restrict DG R zG)
  have hFixp : (Φ pG).val=p:=by
    have hc:=congrArg Subtype.val (hχ.proj_comm zG)
    rw [hpProj,proj_restrict DC R (χ zG),hFixz] at hc
    exact hc
  let O : Opens DG:=⟨(Subtype.val : DG→nativeManifold hk V hV) ⁻¹' (KM : Set _) ∩
    (fun w : DG=>(Φ w).val.val) ⁻¹' (AM : Set Y),
    (KM.isOpen.preimage continuous_subtype_val).inter
      (AM.isOpen.preimage (continuous_subtype_val.comp
        (continuous_subtype_val.comp Φ.contMDiff.continuous)))⟩
  have hpO : pG∈O:=⟨hpKM,by change (Φ pG).val.val∈AM;rw [hFixp];exact hpAM⟩
  let f : O→AM:=fun w=>⟨(Φ w.val).val.val,w.property.2⟩
  let g : O→KM:=fun w=>⟨w.val.val,w.property.1⟩
  have hf : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel n) ∞ f:=by
    apply (ContMDiff.subtypeVal_comp_iff AM f).mp
    exact (contMDiff_val hk hV).comp
      (contMDiff_subtype_val.comp (Φ.contMDiff.comp contMDiff_subtype_val))
  have hg : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k) ∞ g:=by
    apply (ContMDiff.subtypeVal_comp_iff KM g).mp
    change ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k) ∞ (fun w : O=>w.val.val)
    exact contMDiff_subtype_val.comp contMDiff_subtype_val
  let zO : openPreimage P O:=⟨zG,by change P.proj zG∈O;rw [hpProj];exact hpO⟩
  let F : openPreimage P O → openPreimage S AM:=fun w=>⟨(χ w.val).val.val,by
    change S.proj (χ w.val).val.val∈AM
    rw [hTail.square (χ w.val).val]
    have hc:=congrArg Subtype.val (hχ.proj_comm w.val)
    rw [proj_restrict DC R (χ w.val)] at hc
    rw [←hc]
    exact w.property.2⟩
  have hF : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel n) ∞ F:=by
    apply (ContMDiff.subtypeVal_comp_iff (openPreimage S AM) F).mp
    exact (contMDiff_val hk hV').comp
      (contMDiff_subtype_val.comp (χ.contMDiff.comp contMDiff_subtype_val))
  have hFz : (F zO).val=z.val:=congrArg Subtype.val hFixz
  refine ⟨Φ,χ,hLift,hχ,pG,rfl,hFixp,O,hpO,f,g,hf,hg,fun _=>rfl,fun _=>rfl,zO,rfl,F,hF,
    fun _=>rfl,hFz,?_,?_,?_⟩
  · have hBN : IsClosedSubmanifold k B0.N:=by
      rw [←hModel]
      exact (MarkedIdealTowerTransport.isClosedSubmanifold_preimage_iff Φ).mpr hAN
    have hBI : B0.ideal.IsCoherent:=by rw [←hModel];exact isCoherent_pullback Φ.contMDiff hAI
    have hBT : IsGeoTestTower B0 P:=by
      rw [←hModel]
      exact (IsTowerIso.isGeoTestTower_iff Φ hAN hAI hχ).mpr hAT
    have hTest:=isGeoTestTower_restrict O hBN hBI P hBT
    have hQB0 : IsGeoTestTower (barMarked K0) Q:=
      (isGeoTestTower_append_iff (stepOneMarked K.N K.ideal K.d) Q R).mp
        (isGeoTestTower_stepOneMarked_of_coeffHom K (Q.append R) hNativeBar) |>.1
    let KV0:=contactHead K0 v Q
    have hKV0 : KV0.ideal.IsCoherent:=isCoherent_restrictedCoeff K0 hKI hKN v Q hQB0
    have hComp : MarkedIdeal.pullback g (contactMarkedKept K0 v Q KM)=
        MarkedIdeal.pullback (Subtype.val : O→DG) B0:=by
      have h1:=marked_pullback_comp_hhol
        (J:=KV0) (fun _ _ ha=>RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hKV0 ha)
        contMDiff_subtype_val hg (d:=fun w : O=>w.val.val) (fun _=>rfl)
      have h2:=marked_pullback_comp_hhol
        (J:=KV0) (fun _ _ ha=>RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hKV0 ha)
        contMDiff_subtype_val contMDiff_subtype_val (d:=fun w : O=>w.val.val) (fun _=>rfl)
      exact h1.trans h2.symm
    have hPad:=lowerMarkedB_eq_empty_pad K Q p
    rw [hpq] at hPad
    rw [hPad,pullback_replicate_empty,hComp]
    exact empty_pad_isGeoTestTower _ K.E.length _ hTest
  · let M0 : MarkedIdeal n X:={M with E:=[]}
    have hStep : IsGeoTestTower (barMarked M0) (T.append S):=
      isGeoTestTower_stepOneMarked_of_coeffHom M (T.append S) hUpper
    have hAMU : (AM : Set Y)⊆openPreimage T U:=by
      intro y hy
      have hyU:=(interior_subset hy).1
      rw [hbase,←hUE] at hyU
      exact hyU
    have hEmptyTest:=(ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le
      M0 hN hI hd U hu T S hStep AM hAMU).1
    have hPad:=lowerMarkedB_eq_empty_pad M T p.val
    rw [hbase] at hPad
    rw [hPad]
    exact empty_pad_isGeoTestTower _ M.E.length _ hEmptyTest
  · let M0 : MarkedIdeal n X:={M with E:=[]}
    let AU:=contactHead M ua T
    let AU0:=contactHead M0 ua T
    let KU0:=contactHead K0 u Q
    let KV0:=contactHead K0 v Q
    have hLen : K.E.length=M.E.length:=List.length_map _
    have hFullE : AU.E=boundary M.E T:=hEN
    have hDropAU : AU0=({AU with E:=AU.E.drop M.E.length} : MarkedIdeal n Y):=
      contactHead_drop_initial M ua T
    have hSub : AU0.E.Sublist AU.E:=by
      rw [hDropAU]
      exact List.drop_sublist _ _
    have hSmall:=HironakaActualNativeSectionPositiveLowerRecords.Lift.forget_boundary hTail
      (E':=AU0.E) (by rw [←hFullE];exact hSub)
    have hAU_N : AU0.N⊆V:=by
      let L0 : MarkedIdeal n X:=⟨M.N∩{x | ua x=0},M.E,IdealWeightPowers.unitIdeal n X,1⟩
      have hs:=HironakaActualNativeSectionOrderHistory.Lift.current_carrier_subset h L0 (fun _ hx=>hNW hx.1)
      rw [N_geoTransformAlong] at hs
      exact hs
    have hAU_H : ∀y a,AU0.ideal.mem y a → HolomorphicAt n a y:=fun _ _ ha=>ha.1
    have hNativeFull:=native_contact_head h hn hE hTrans M rfl hNW hhol ua
    have hDict : nativePullback hk V hV AU0=KU0:=by
      change nativePullback hk V hV (contactHead ({M with E:=[]} : MarkedIdeal n X) ua T)=
        contactHead ({K with E:=[]} : MarkedIdeal k (nativeManifold hk W hW)) u Q
      rw [contactHead_drop_initial M ua T,contactHead_drop_initial K u Q,←hNativeFull]
      apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
      · rfl
      · change (AU.E.drop M.E.length).map ((Subtype.val : V→Y) ⁻¹' ·)=
          (AU.E.map ((Subtype.val : V→Y) ⁻¹' ·)).drop K.E.length
        rw [List.map_drop,hLen]
      · rfl
      · rfl
    rw [←hFullE] at hEC hTC
    have hRecords:=hSmall.whole_records hn (isSNCDivisor_of_sublist hEC hSub)
      (isTransverse_of_forall_mem hTC hSub.subset) AU0 rfl hAU_N hAU_H
    rw [hDict] at hRecords
    have hBI : B0.ideal.IsCoherent:=by rw [←hModel];exact isCoherent_pullback Φ.contMDiff hAI
    have hTowerEq:=IsTowerIso.geoTransformAlong_eq Φ hAN hAI hχ hAT
    rw [hModel] at hTowerEq
    have hARestr : geoTransformAlong A0 PC=MarkedIdeal.pullback
        (Subtype.val : openPreimage R DC→nativeManifold hk V' hV') (geoTransformAlong KU0 R):=
      geoTransformAlong_restrict_of_hhol KU0 (fun _ _ ha=>ha.1) DC R
    have hEmpty : geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O→DG) B0) (restrict O P)=
        markedPullback (m:=k) F
          (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : AM→Y) AU0) (restrict AM S)):=by
      rw [geoTransformAlong_restrict_of_hhol B0
        (fun _ _ ha=>RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hBI ha) O P,
        hTowerEq,hARestr,
        hRecords,geoTransformAlong_restrict_of_hhol AU0 hAU_H AM S]
      have hCur:=holomorphic_geoTransformAlong AU0 hAU_H S
      apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
      · rfl
      · simp only [nativePullback,MarkedIdeal.pullback,markedPullback,List.map_map,Function.comp_def]
        rfl
      · change GermIdeal.pullback (m:=k) (Subtype.val : openPreimage P O→ openPreimage R DG)
          (GermIdeal.pullback (m:=k) χ
            (GermIdeal.pullback (m:=k) (Subtype.val : openPreimage R DC→nativeManifold hk V' hV')
              (GermIdeal.pullback (m:=k) (Subtype.val : V'→Z) (geoTransformAlong AU0 S).ideal)))=
          GermIdeal.pullback (m:=k) F
            (GermIdeal.pullback (m:=n) (Subtype.val : openPreimage S AM→Z) (geoTransformAlong AU0 S).ideal)
        rw [←whole_pullback_comp (contMDiff_val hk hV') contMDiff_subtype_val _ hCur,
          ←whole_pullback_comp ((contMDiff_val hk hV').comp contMDiff_subtype_val) χ.contMDiff _ hCur,
          ←whole_pullback_comp
            (((contMDiff_val hk hV').comp contMDiff_subtype_val).comp χ.contMDiff)
            contMDiff_subtype_val _ hCur,
          ←whole_pullback_comp contMDiff_subtype_val hF _ hCur]
        rfl
      · rfl
    have hQB0 : IsGeoTestTower (barMarked K0) Q:=
      (isGeoTestTower_append_iff (stepOneMarked K.N K.ideal K.d) Q R).mp
        (isGeoTestTower_stepOneMarked_of_coeffHom K (Q.append R) hNativeBar) |>.1
    have hKV0 : KV0.ideal.IsCoherent:=isCoherent_restrictedCoeff K0 hKI hKN v Q hQB0
    have hComp : MarkedIdeal.pullback g (contactMarkedKept K0 v Q KM)=
        MarkedIdeal.pullback (Subtype.val : O→DG) B0:=by
      have h1:=marked_pullback_comp_hhol
        (J:=KV0) (fun _ _ ha=>RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hKV0 ha)
        contMDiff_subtype_val hg (d:=fun w : O=>w.val.val) (fun _=>rfl)
      have h2:=marked_pullback_comp_hhol
        (J:=KV0) (fun _ _ ha=>RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hKV0 ha)
        contMDiff_subtype_val contMDiff_subtype_val (d:=fun w : O=>w.val.val) (fun _=>rfl)
      exact h1.trans h2.symm
    have hKPad:=lowerMarkedB_eq_empty_pad K Q p
    rw [hpq] at hKPad
    have hAPad:=lowerMarkedB_eq_empty_pad M T p.val
    rw [hbase] at hAPad
    rw [hKPad,pullback_replicate_empty,hComp,empty_pad_geoTransformAlong,
      hAPad,empty_pad_geoTransformAlong]
    apply (congrArg (fun A : MarkedIdeal k (openPreimage P O)=>
      ({A with E:=List.replicate K.E.length ∅ ++ A.E} : MarkedIdeal k (openPreimage P O))) hEmpty).trans
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · rfl
    · change List.replicate K.E.length ∅ ++
          (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : AM→Y) AU0) (restrict AM S)).E.map (F ⁻¹' ·)=
        (List.replicate M.E.length ∅ ++
          (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : AM→Y) AU0) (restrict AM S)).E).map (F ⁻¹' ·)
      simp only [List.map_append,List.map_replicate,preimage_empty,hLen]
    · rfl
    · rfl

end
end Hironaka.HironakaActualNativeSectionZeroWholeTails
