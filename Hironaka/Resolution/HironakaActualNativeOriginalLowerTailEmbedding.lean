import Hironaka.Resolution.HironakaActualNativeLowerTailFrames

/-! Original zero lower tails obtain actual closed regular native Lift frames
from ONE stronger joint contact datum. Full HEAD laws are produced from its
actual empty-initial model, retaining every born-before-cut position. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNativeOriginalLowerTailEmbedding
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism BlowupTowerIsoTail BlowupTowerSplitIso
  ResolutionInvariantSpec InvDomainTowerAlong NormalCrossings NormalCrossingsInvariance
  SubmanifoldChartedSpace SubmanifoldCodRestrict MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionRegularity
  HironakaActualNativeSectionOrderHistory HironakaActualNativeSectionNormalCrossings
  HironakaActualNativeInvariantDomain HironakaDisjointNativeOpenLift HironakaDisjointNativeReferenceWindow
  HironakaActualNativeSectionZeroWholeTails HironakaActualNativeSectionContactChoices
  HironakaActualNativeLowerEmbedding HironakaDisjointRecursiveNativeHistory HironakaActualNativeLowerTailFrames
  HironakaActualNativePositiveHistories HironakaActualNativeSectionPositiveLowerRecords HironakaActualNativeSectionCoefficientRecords
  HironakaDisjointNativeContactReference HironakaActualRawRecordPullbacks
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionOrderedChoiceImageTrace
  HomogenizedIdealAlong HomogenizedIdealAlongTower HomogenizedGlueingAlong HomogenizedGlueingAlongTower
  HomogenizedGlueingLiftAlong HomogenizedGlueingTower MemberInterTowerAlong
  StepOneValue StepOneValueMasked StepOneLowerDomain StepOneTangentChange StepOneRegime
  ContactStageKept ContactStageInvDomain CoefficientIdealRestriction TangentDirectionAlong MaximalOrderStepOneB
  HironakaStepOneZeroContactRemainderTailGlueing RelativePrincipalizationSpan GermIdealPullbackCalculus

private theorem pullback_initial_empty_pad {n k : ℕ} {X : CMfd.{0} n} {Y : CMfd.{0} k}
    (f : Y→X) (L : MarkedIdeal n X) (j : ℕ) :
    markedPullback (m:=k) f ({L with E:=List.replicate j ∅ ++ L.E} : MarkedIdeal n X)=
      ({markedPullback (m:=k) f L with E:=List.replicate j ∅ ++ (markedPullback (m:=k) f L).E} : MarkedIdeal k Y) := by
  unfold markedPullback
  simp only [List.map_append,List.map_replicate,preimage_empty]

private theorem lowerMarkedB_initial_pad {n : ℕ} {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (T : BlowupTower X Y) (p : Y) :
    let A:=contactMarkedKept ({M with E:=[]} : MarkedIdeal n X)
      (tangentChoice M (T.proj p)).2 T (maskB M T p)
    lowerMarkedB M T p=({A with E:=List.replicate M.E.length ∅ ++ A.E} : MarkedIdeal n (maskB M T p)) := by
  exact pullback_val_restrictedCoeffHom_eq M T (tangentChoice M (T.proj p)).2 (maskB M T p)
    (fun H hH y hy=>(interior_subset hy).2.1 H hH)

private theorem whole_zero_head_of_empty_model {n k : ℕ} {X : CMfd.{0} n}
    {hk : k≤n} {W : Set X} {hWc : IsClosed W} {hW : ∀x∈W,RegularAtDim (n:=n) W x k}
    (hn : 0<n) (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hMN : M.N⊆W)
    {Y : CMfd.{0} n} {T : BlowupTower X Y} {V : Set Y} {hVc : IsClosed V}
    {hV : ∀y∈V,RegularAtDim (n:=n) V y k}
    {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}
    (h : Lift hk W hWc hW M.E T V hVc hV Q) (hT : IsGeoTestTower (barMarked M) T)
    (q : nativeManifold hk W hW) (p : nativeManifold hk V hV) (hpq : Q.proj p=q) :
    let K:=nativePullback hk W hW M
    let u:=(tangentChoice M q.val).2 ∘ (Subtype.val : W→X)
    let v:=(tangentChoice K q).2
    ∀(G : GlueingDataAlong K.N K.ideal K.d u v)
      (Φ : CMfd.of (n:=k) (openPreimage Q G.dom) ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯
        CMfd.of (n:=k) (openPreimage Q G.cod)),
      MarkedIdeal.pullback Φ
          (contactMarkedKept ({K with E:=[]} : MarkedIdeal k (nativeManifold hk W hW)) u Q (openPreimage Q G.cod))=
        contactMarkedKept ({K with E:=[]} : MarkedIdeal k (nativeManifold hk W hW)) v Q (openPreimage Q G.dom) →
      ∀(O : Opens (openPreimage Q G.dom))(f : O→maskB M T p.val)(g : O→maskB K Q p),
        ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel n) ∞ f →
        ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k) ∞ g →
        (∀w,(f w).val=(Φ w.val).val.val) → (∀w,(g w).val=w.val.val) →
        markedPullback (m:=k) f (lowerMarkedB M T p.val)=MarkedIdeal.pullback g (lowerMarkedB K Q p) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  let := chartedSpace hk hV
  have := isComplexManifold_chartedSpace hk hV
  let K:=nativePullback hk W hW M
  let ua:=(tangentChoice M q.val).2
  let u:=ua ∘ (Subtype.val : W→X)
  let v:=(tangentChoice K q).2
  dsimp only
  intro G Φ hModel O f g hf hg hfval hgval
  let M0 : MarkedIdeal n X:={M with E:=[]}
  let K0 : MarkedIdeal k (nativeManifold hk W hW):={K with E:=[]}
  let DG:=openPreimage Q G.dom
  let DC:=openPreimage Q G.cod
  let AM:=maskB M T p.val
  let KM:=maskB K Q p
  let AU:=contactHead M0 ua T
  let KU:=contactHead K0 u Q
  let KV:=contactHead K0 v Q
  let A0:=contactMarkedKept K0 u Q DC
  let B0:=contactMarkedKept K0 v Q DG
  have hBase : T.proj p.val=q.val:=(h.square p).trans (congrArg Subtype.val hpq)
  have hEmpty:=HironakaActualNativeSectionPositiveLowerRecords.Lift.forget_boundary h (E':=[]) (List.nil_sublist _)
  have hWSub : IsClosedSubmanifold n W:=⟨hWc,fun x hx=>⟨k,hW x hx⟩⟩
  have hK0 : nativePullback hk W hW M0=K0:=rfl
  have hDict : nativePullback hk V hV AU=KU:=by
    have ht:=native_contact_head hEmpty hn isSNCDivisor_nil (isTransverse_nil_of_isClosedSubmanifold hWSub)
      M0 rfl hMN (fun _ _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hM.isCoherent hg) ua
    rw [hK0] at ht
    exact ht
  have hTM0 : IsGeoTestTower (barMarked M0) T:=isGeoTestTower_stepOneMarked_of_coeffHom M T hT
  have hAU : AU.ideal.IsCoherent:=isCoherent_restrictedCoeff M0 hM.isCoherent hM.isClosedSubmanifold_N ua T hTM0
  have hKU : KU.ideal.IsCoherent:=by
    rw [←hDict]
    exact isCoherent_pullback (contMDiff_val hk hV) hAU
  have hA0 : A0.ideal.IsCoherent:=isCoherent_pullback contMDiff_subtype_val hKU
  let δ : O→nativeManifold hk V hV:=fun w=>(Φ w.val).val
  have hδ : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k) ∞ δ:=
    contMDiff_subtype_val.comp (Φ.contMDiff.comp contMDiff_subtype_val)
  have hMap : (Subtype.val : AM→Y) ∘ f=(Subtype.val : V→Y) ∘ δ:=funext hfval
  have hPullComp : markedPullback (m:=k) δ KU=MarkedIdeal.pullback (Subtype.val : O→DG) B0:=by
    have h1:=whole_markedPullback_comp (f:=(Subtype.val : DC→nativeManifold hk V hV))
      (g:=Φ ∘ (Subtype.val : O→DG)) contMDiff_subtype_val (Φ.contMDiff.comp contMDiff_subtype_val) KU hKU
    have h2:=whole_markedPullback_comp (g:=(Subtype.val : O→DG)) Φ.contMDiff contMDiff_subtype_val A0 hA0
    have h3:=congrArg (fun L : MarkedIdeal k (CMfd.of (n:=k) DG)=>MarkedIdeal.pullback (Subtype.val : O→DG) L) hModel
    exact h1.trans (h2.trans h3)
  have hEmptyCompare : markedPullback (m:=k) f (contactMarkedKept M0 ua T AM)=
      MarkedIdeal.pullback (Subtype.val : O→DG) B0:=by
    have h1:=(whole_markedPullback_comp contMDiff_subtype_val hf AU hAU).symm
    have h2:=congrArg (fun b : O→Y=>markedPullback (m:=k) b AU) hMap
    have h3:=whole_markedPullback_comp (contMDiff_val hk hV) hδ AU hAU
    have h4:=congrArg (fun L : MarkedIdeal k (nativeManifold hk V hV)=>markedPullback (m:=k) δ L) hDict
    exact h1.trans (h2.trans (h3.trans (h4.trans hPullComp)))
  have hNativeCompare : MarkedIdeal.pullback g (contactMarkedKept K0 v Q KM)=
      MarkedIdeal.pullback (Subtype.val : O→DG) B0:=by
    have h1:=marked_pullback_comp_hhol (J:=KV) (fun _ _ ha=>ha.1)
      contMDiff_subtype_val hg (d:=fun w : O=>w.val.val) hgval
    have h2:=marked_pullback_comp_hhol (J:=KV) (fun _ _ ha=>ha.1)
      contMDiff_subtype_val contMDiff_subtype_val (d:=fun w : O=>w.val.val) (fun _=>rfl)
    exact h1.trans h2.symm
  have hAPad:=lowerMarkedB_initial_pad M T p.val
  rw [hBase] at hAPad
  have hKPad:=lowerMarkedB_initial_pad K Q p
  rw [hpq] at hKPad
  have hLen : K.E.length=M.E.length:=List.length_map _
  let PA:=markedPullback (m:=k) f (contactMarkedKept M0 ua T AM)
  let PB:=MarkedIdeal.pullback g (contactMarkedKept K0 v Q KM)
  let pad (j : ℕ) (L : MarkedIdeal k (CMfd.of (n:=k) O)) : MarkedIdeal k (CMfd.of (n:=k) O):=
    {L with E:=List.replicate j ∅ ++ L.E}
  have hPadA : markedPullback (m:=k) f (lowerMarkedB M T p.val)=pad M.E.length PA:=by
    have h1:=congrArg (fun L : MarkedIdeal n (CMfd.of (n:=n) AM)=>markedPullback (m:=k) f L) hAPad
    exact h1.trans (pullback_initial_empty_pad (X:=CMfd.of (n:=n) AM) (Y:=CMfd.of (n:=k) O)
      f (contactMarkedKept M0 ua T AM) M.E.length)
  have hPadK : MarkedIdeal.pullback g (lowerMarkedB K Q p)=pad K.E.length PB:=by
    have h1:=congrArg (fun L : MarkedIdeal k (CMfd.of (n:=k) KM)=>MarkedIdeal.pullback g L) hKPad
    exact h1.trans (pullback_initial_empty_pad (X:=CMfd.of (n:=k) KM) (Y:=CMfd.of (n:=k) O)
      g (contactMarkedKept K0 v Q KM) K.E.length)
  have hEq : PA=PB:=hEmptyCompare.trans hNativeCompare.symm
  have hPadEq:=congrArg (pad M.E.length) hEq
  have hLenEq:=congrArg (fun j=>pad j PB) hLen
  exact hPadA.trans (hPadEq.trans (hLenEq.symm.trans hPadK.symm))

private theorem native_zero_lower_test_of_empty_model {k : ℕ} {X D F : CMfd.{0} k}
    (K : MarkedIdeal k X) (Q : BlowupTower X D) (R : BlowupTower D F)
    (q : X) (p : D) (hpq : Q.proj p=q)
    {u : X→ℂ} (G : GlueingDataAlong K.N K.ideal K.d u (tangentChoice K q).2)
    (Φ : CMfd.of (n:=k) (openPreimage Q G.dom) ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯
      CMfd.of (n:=k) (openPreimage Q G.cod))
    (χ : CMfd.of (n:=k) (openPreimage R (openPreimage Q G.dom)) ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯
      CMfd.of (n:=k) (openPreimage R (openPreimage Q G.cod)))
    (hχ : IsTowerIso Φ (restrict (openPreimage Q G.dom) R) (restrict (openPreimage Q G.cod) R) χ) :
    let K0 : MarkedIdeal k X:={K with E:=[]}
    let A0:=contactMarkedKept K0 u Q (openPreimage Q G.cod)
    let B0:=contactMarkedKept K0 (tangentChoice K q).2 Q (openPreimage Q G.dom)
    MarkedIdeal.pullback Φ A0=B0 →
    IsClosedSubmanifold k A0.N → A0.ideal.IsCoherent →
    IsGeoTestTower A0 (restrict (openPreimage Q G.cod) R) →
    ∀(O : Opens (openPreimage Q G.dom))(g : O→maskB K Q p),
      ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k) ∞ g →
      (∀w,(g w).val=w.val.val) →
      IsGeoTestTower (MarkedIdeal.pullback g (lowerMarkedB K Q p))
        (restrict O (restrict (openPreimage Q G.dom) R)) := by
  let K0 : MarkedIdeal k X:={K with E:=[]}
  let v:=(tangentChoice K q).2
  let DG:=openPreimage Q G.dom
  let DC:=openPreimage Q G.cod
  let A0:=contactMarkedKept K0 u Q DC
  let B0:=contactMarkedKept K0 v Q DG
  dsimp only
  intro hModel hAN hAI hAT O g hg hgval
  have hModel : MarkedIdeal.pullback Φ A0=B0:=hModel
  have hAN : IsClosedSubmanifold k A0.N:=hAN
  have hAI : A0.ideal.IsCoherent:=hAI
  have hAT : IsGeoTestTower A0 (restrict DC R):=hAT
  have hBN : IsClosedSubmanifold k B0.N:=by
    rw [←hModel]
    exact (MarkedIdealTowerTransport.isClosedSubmanifold_preimage_iff Φ).mpr hAN
  have hBI : B0.ideal.IsCoherent:=by
    rw [←hModel]
    exact isCoherent_pullback Φ.contMDiff hAI
  have hBT : IsGeoTestTower B0 (restrict DG R):=by
    rw [←hModel]
    exact (IsTowerIso.isGeoTestTower_iff Φ hAN hAI hχ).mpr hAT
  have hRestricted:=isGeoTestTower_restrict O hBN hBI (restrict DG R) hBT
  let KV:=contactHead K0 v Q
  have hComp : MarkedIdeal.pullback g (contactMarkedKept K0 v Q (maskB K Q p))=
      MarkedIdeal.pullback (Subtype.val : O→DG) B0:=by
    have h1:=marked_pullback_comp_hhol (J:=KV) (fun _ _ ha=>ha.1)
      contMDiff_subtype_val hg (d:=fun w : O=>w.val.val) hgval
    have h2:=marked_pullback_comp_hhol (J:=KV) (fun _ _ ha=>ha.1)
      contMDiff_subtype_val contMDiff_subtype_val (d:=fun w : O=>w.val.val) (fun _=>rfl)
    exact h1.trans h2.symm
  have hPad:=lowerMarkedB_initial_pad K Q p
  rw [hpq] at hPad
  have hFullEq : MarkedIdeal.pullback g (lowerMarkedB K Q p)=
      ({MarkedIdeal.pullback (Subtype.val : O→DG) B0 with E:=List.replicate K.E.length ∅ ++
        (MarkedIdeal.pullback (Subtype.val : O→DG) B0).E} : MarkedIdeal k (CMfd.of (n:=k) O)):=by
    have h1:=congrArg (fun L : MarkedIdeal k (CMfd.of (n:=k) (maskB K Q p))=>MarkedIdeal.pullback g L) hPad
    have h2:=pullback_initial_empty_pad (X:=CMfd.of (n:=k) (maskB K Q p)) (Y:=CMfd.of (n:=k) O)
      g (contactMarkedKept K0 v Q (maskB K Q p)) K.E.length
    have h3:=congrArg (fun L : MarkedIdeal k (CMfd.of (n:=k) O)=>
      ({L with E:=List.replicate K.E.length ∅ ++ L.E} : MarkedIdeal k (CMfd.of (n:=k) O))) hComp
    exact h1.trans (h2.trans h3)
  have hPadded:=empty_pad_isGeoTestTower (MarkedIdeal.pullback (Subtype.val : O→DG) B0)
    K.E.length (restrict O (restrict DG R)) hRestricted
  exact hFullEq.symm ▸ hPadded

/-- ONE genuine joint contact datum supplies the ORIGINAL zero lower domain
and actual same-tail native frame. Both lower TESTs and the ENTIRE controlled
record dictionary are produced, with the actual endpoint retained. -/
theorem exists_original_zero_tail_domain_frame {n k r : ℕ} {X : CMfd.{0} n}
    (hn : 0<n) (hk : k≤n) (W : Set X) (hWc : IsClosed W)
    (hW : ∀x∈W,RegularAtDim (n:=n) W x k)
    (M : MarkedIdeal n X) (hM : IsInvDomain (r+1) M) (hMN : M.N⊆W)
    (hTrans : IsTransverse n W M.E) (hmax : IsMaximalOrderAlong M.N M.ideal M.d)
    (q : nativeManifold hk W hW) (hq : q.val∈M.cosupp) :
    let K:=nativePullback hk W hW M
    let u:=(tangentChoice M q.val).2 ∘ (Subtype.val : W→X)
    let v:=(tangentChoice K q).2
    ∃G : GlueingDataAlong K.N K.ideal K.d u v,q∈G.dom ∧ q∈G.cod ∧
      ∀{Y Z : CMfd.{0} n}{T : BlowupTower X Y}{S : BlowupTower Y Z}
        {V : Set Y}{hVc : IsClosed V}{hV : ∀y∈V,RegularAtDim (n:=n) V y k}
        {V' : Set Z}{hV'c : IsClosed V'}{hV' : ∀z∈V',RegularAtDim (n:=n) V' z k}
        {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}
        {R : BlowupTower (nativeManifold hk V hV) (nativeManifold hk V' hV')},
        Lift hk W hWc hW M.E T V hVc hV Q →
        Lift hk V hVc hV (boundary M.E T) S V' hV'c hV' R →
        IsGeoTestTower (barMarked M) (T.append S) →
        ∀z : nativeManifold hk V' hV',Q.proj (R.proj z)=q →
          z.val∈(geoTransformAlong (barMarked M) (T.append S)).cosupp →
          level M T (R.proj z).val=0 →
          (R.proj z).val∉CodimOneSupportAlong.codimOnePartAlong (geoTransformAlong (barMarked M) T).N
            (geoTransformAlong (barMarked M) T).ideal (geoTransformAlong (barMarked M) T).d →
          ∃Φ χ,IsGlueingLiftAlong G Q Φ ∧
            IsTowerIso Φ (restrict (openPreimage Q G.dom) R) (restrict (openPreimage Q G.cod) R) χ ∧
            let p:=R.proj z
            let AM:=maskB M T p.val
            let KM:=maskB K Q p
            let DG:=openPreimage Q G.dom
            let QR:=restrict DG R
            ∃pG : DG,pG.val=p ∧ (Φ pG).val=p ∧
              ∃O : Opens DG,pG∈O ∧
                ∃(f : O→AM)(g : O→KM),
                  ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel n) ∞ f ∧
                  ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k) ∞ g ∧
                  (∀w,(f w).val=(Φ w.val).val.val) ∧ (∀w,(g w).val=w.val.val) ∧
                  markedPullback (m:=k) f (lowerMarkedB M T p.val)=MarkedIdeal.pullback g (lowerMarkedB K Q p) ∧
                  ∃zO : openPreimage QR O,zO.val.val=z ∧
                    ∃(B : Opens Y)(hBA : B≤AM),p.val∈B ∧
                      ∃Ψ : CMfd.of (n:=k) O ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯
                          nativeManifold hk (openSection V B) (openSection_regular hV B),
                        (∀w,(Ψ w).val.val=(f w).val) ∧
                        let LB:=markedPullback (m:=n) (fun y : B=>⟨y.val,hBA y.property⟩ : B→AM) (lowerMarkedB M T p.val)
                        let J:=nativePullback hk (openSection V B) (openSection_regular hV B) LB
                        let N0:=MarkedIdeal.pullback g (lowerMarkedB K Q p)
                        LB.N⊆openSection V B ∧ IsTransverse n (openSection V B) LB.E ∧
                        IsInvDomain r LB ∧ IsInvDomain r J ∧ IsInvDomain r N0 ∧
                        MarkedIdeal.pullback Ψ J=N0 ∧
                        ∃(hSc : IsClosed (openSection V' (openPreimage S B)))
                          (hS : ∀y∈openSection V' (openPreimage S B),RegularAtDim (n:=n) (openSection V' (openPreimage S B)) y k)
                          (P : BlowupTower (nativeManifold hk (openSection V B) (openSection_regular hV B))
                            (nativeManifold hk (openSection V' (openPreimage S B)) hS))
                          (ν : CMfd.of (n:=k) (openPreimage QR O) ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯
                            nativeManifold hk (openSection V' (openPreimage S B)) hS),
                          Lift hk (openSection V B) (hVc.preimage continuous_subtype_val) (openSection_regular hV B)
                            LB.E (restrict B S) (openSection V' (openPreimage S B)) hSc hS P ∧
                          IsTowerIso Ψ (restrict O QR) P ν ∧
                          (∀w,(ν w).val.val=(χ w.val).val.val) ∧ (ν zO).val.val=z.val ∧
                          IsGeoTestTower N0 (restrict O QR) ∧ IsGeoTestTower J P ∧ IsGeoTestTower LB (restrict B S) ∧
                          ∃F : openPreimage QR O → openPreimage S B,
                            ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel n) ∞ F ∧
                            (F zO).val=z.val ∧
                            geoTransformAlong N0 (restrict O QR)=markedPullback (m:=k) F (geoTransformAlong LB (restrict B S)) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  let K:=nativePullback hk W hW M
  let u:=(tangentChoice M q.val).2 ∘ (Subtype.val : W→X)
  let v:=(tangentChoice K q).2
  have hN:=hM.isWellFormed.isClosedSubmanifold_N
  have hI:=hM.isWellFormed.isCoherent
  have hE:=hM.isWellFormed.isSNCDivisor
  have hd:=hM.one_le_d
  have hK : IsInvDomain (r+1) K:=isInvDomain_nativePullback hn hk hW M hM hMN hTrans
  obtain ⟨hKN,hKI,hKmax,_hKcos⟩:=native_source_geometry hk hW M hMN hN hI hmax
  obtain ⟨_U,_hUE,_hqU,_hu,_B,_L,_hqB,_hqL,_hBU,_hLE,_hBu,_hLv,G,hqd,hqc,_hGD,_hGC,hAll⟩:=
    exists_native_selected_joint_tail hk hW M hMN hN hI hd hmax q hq
  refine ⟨G,hqd,hqc,?_⟩
  intro Y Z T S V hVc hV V' hV'c hV' Q R hHead hTail hUpper z hzq hz hl hZ
  let := chartedSpace hk hV
  have := isComplexManifold_chartedSpace hk hV
  let := chartedSpace hk hV'
  have := isComplexManifold_chartedSpace hk hV'
  let p:=R.proj z
  let AM:=maskB M T p.val
  let KM:=maskB K Q p
  have hpq : Q.proj p=q:=hzq
  have hNative : IsGeoTestTower K (Q.append R):=actual_split_native_original_test hHead hTail hn hE hTrans
    M rfl hMN hN hI hd hmax hUpper
  obtain ⟨hT,hSUpper⟩:=(isGeoTestTower_append_iff (barMarked M) T S).mp hUpper
  have hBarI:=isCoherent_barMarked M hN hI
  obtain ⟨hMTN,hMTI⟩:=isClosedSubmanifold_N_and_isCoherent_geoTransformAlong (𝔪:=barMarked M) hN hBarI T hT
  have hzS : z.val∈(geoTransformAlong (geoTransformAlong (barMarked M) T) S).cosupp:=by
    rw [←geoTransformAlong_append]
    exact hz
  have hpAcos : p.val∈(geoTransformAlong (barMarked M) T).cosupp:=by
    have ht:=proj_mem_cosupp_of_mem_cosupp hMTN hMTI S hSUpper hzS
    rw [hTail.square z] at ht
    exact ht
  have hpAM : p.val∈AM:=mem_maskB M hM.isWellFormed hd hmax T hT hpAcos hl hZ
  have hNotSpecial : ¬IsSpecial M T p.val:=by
    rintro (hzero|hpos)
    · exact hZ hzero.2
    · have ht:=hpos.1
      have hlp : level M T p.val=0:=hl
      omega
  obtain ⟨hRec,_hOrig,hLS,_hReg,_hRun⟩:=original_step_one_chronology M hM.isWellFormed hMN hTrans hHead hn
  have he:=coeff_homAlong_wEquiv K hKN hKI hd
  have hNativeBar : IsGeoTestTower (barMarked K) (Q.append R):=(he.2 _).1.mpr hNative
  have hQBar:=(isGeoTestTower_append_iff (barMarked K) Q R).mp hNativeBar |>.1
  have hpKcos : p∈(geoTransformAlong (barMarked K) Q).cosupp:=by
    rw [hRec]
    rw [cosupp_nativePullback hk V hV (geoTransformAlong (barMarked M) T)
      (HironakaActualNativeSectionOrderHistory.Lift.current_carrier_subset hHead (barMarked M) hMN)
      (holomorphic_geoTransformAlong (barMarked M) (fun _ _ ha=>ha.1) T)]
    exact hpAcos
  have hLevelK : level K Q p=0:=(hLS p).1.symm.trans hl
  have hNotSpecialK : ¬IsSpecial K Q p:=fun ht=>hNotSpecial ((hLS p).2.mpr ht)
  have hZK : p∉CodimOneSupportAlong.codimOnePartAlong (geoTransformAlong (barMarked K) Q).N
      (geoTransformAlong (barMarked K) Q).ideal (geoTransformAlong (barMarked K) Q).d:=by
    intro ht
    exact hNotSpecialK (Or.inl ⟨hLevelK,ht⟩)
  have hpKM : p∈KM:=mem_maskB K hK.isWellFormed hd hKmax Q hQBar hpKcos hLevelK hZK
  obtain ⟨hEC,hTC⟩:=hHead.geometry hn hE hTrans
  have hEN : (geoTransformAlong (barMarked M) T).E=boundary M.E T:=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪:=barMarked M) (𝔫:=(⟨univ,M.E,IdealWeightPowers.unitIdeal n X,1⟩ : MarkedIdeal n X)) rfl T
  have hTailCos:=HironakaActualNativeSectionOrderHistory.Lift.current_cosupport hTail hn hEC hTC
    (geoTransformAlong (barMarked M) T) hEN
    (HironakaActualNativeSectionOrderHistory.Lift.current_carrier_subset hHead (barMarked M) hMN)
    (holomorphic_geoTransformAlong (barMarked M) (fun _ _ ha=>ha.1) T)
  rw [←hRec] at hTailCos
  have hEndCos : (geoTransformAlong (barMarked K) (Q.append R)).cosupp=
      (Subtype.val : V'→Z) ⁻¹' (geoTransformAlong (barMarked M) (T.append S)).cosupp:=by
    simpa only [geoTransformAlong_append] using hTailCos
  have hzK : z∈(geoTransformAlong K (Q.append R)).cosupp:=by
    rw [←(he.2 _).2 hNativeBar,hEndCos]
    exact hz
  obtain ⟨Φ,χ,hGlue,hχ,hModel,hAN,hAI,hAT,hFix⟩:=hAll Q R hNative
  let DG:=openPreimage Q G.dom
  let DC:=openPreimage Q G.cod
  let QR:=restrict DG R
  have hpDG : p∈DG:=by change Q.proj p∈G.dom;rw [hpq];exact hqd
  let pG : DG:=⟨p,hpDG⟩
  let zG : openPreimage R DG:=⟨z,hpDG⟩
  have hFixz : (χ zG).val=z:=hFix zG hzK
  have hpProj : QR.proj zG=pG:=Subtype.ext (proj_restrict DG R zG)
  have hFixp : (Φ pG).val=p:=by
    have ht:=congrArg Subtype.val (hχ.proj_comm zG)
    rw [hpProj,proj_restrict DC R (χ zG),hFixz] at ht
    exact ht
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
  let zO : openPreimage QR O:=⟨zG,by change QR.proj zG∈O;rw [hpProj];exact hpO⟩
  have hRaw:=whole_zero_head_of_empty_model hn M hM.isWellFormed hMN hHead hT q p hpq
    G Φ hModel O f g hf hg (fun _=>rfl) (fun _=>rfl)
  have hN0Test:=native_zero_lower_test_of_empty_model K Q R q p hpq G Φ χ hχ hModel hAN hAI hAT O g hg (fun _=>rfl)
  let L:=lowerMarkedB M T p.val
  have hRegime : stepRegime M 0 T p.val:=⟨hl,hNotSpecial⟩
  have hLower:=StepOneValueMasked.mem_lowerMask_and_isInvDomain_M M hM.isWellFormed hd hn hmax hM.dimLE T hT hpAcos hRegime
  have hL : IsInvDomain r L:=by
    simpa only [lowerMask,lowerMarkedM,Nat.add_sub_cancel] using hLower.2
  have hLN : L.N⊆openSection V AM:=by
    intro y hy
    change y.val∈strictAlong T (M.N∩{x | (tangentChoice M (T.proj p.val)).2 x=0}) at hy
    have hs:=MemberInterTowerAlong.strictAlong_mono T inter_subset_left hy
    have hc : y.val∈(geoTransformAlong (barMarked M) T).N:=by rw [N_geoTransformAlong];exact hs
    exact HironakaActualNativeSectionOrderHistory.Lift.current_carrier_subset hHead (barMarked M) hMN hc
  have hLTrans : IsTransverse n (openSection V AM) L.E:=by
    rw [←hEN] at hTC
    exact isTransverse_preimage (pullsBackCoordinates_val AM) hTC
  have hOA : ∀w : O,(Φ w.val).val.val∈AM:=fun w=>w.property.2
  obtain ⟨B,hBA,hTrace,hBc,Ψ,hΨ,hLBN,hLBT,hLB,hJ,hWhole,hChanged⟩:=exists_native_window_domain hn hk V hVc hV
    DG DC Φ O AM hOA L hL hLN hLTrans
  have hMapEq : (fun w : O=>⟨(Φ w.val).val.val,hOA w⟩ : O→AM)=f:=rfl
  rw [hMapEq,hRaw] at hWhole hChanged
  have hpB : p.val∈B:=by
    have ht : p∈(Subtype.val : V→Y) ⁻¹' (B : Set Y):=by
      rw [hTrace]
      exact ⟨Φ pG,⟨pG,hpO,rfl⟩,hFixp⟩
    exact ht
  let LB:=markedPullback (m:=n) (fun y : B=>⟨y.val,hBA y.property⟩ : B→AM) L
  let J:=nativePullback hk (openSection V B) (openSection_regular hV B) LB
  let N0:=MarkedIdeal.pullback g (lowerMarkedB K Q p)
  obtain ⟨hSc,hS,P,ν,hActual,hFrame,hPoint⟩:=exists_actual_changed_tail_frame hTail DG DC Φ χ hχ O B hTrace Ψ hΨ
  let := chartedSpace hk (openSection_regular hV B)
  have := isComplexManifold_chartedSpace hk (openSection_regular hV B)
  let := chartedSpace hk hS
  have := isComplexManifold_chartedSpace hk hS
  have hLBE : LB.E=(boundary M.E T).map ((Subtype.val : B→Y) ⁻¹' ·):=by
    change ((geoTransformAlong (barMarked M) T).E.map ((Subtype.val : AM→Y) ⁻¹' ·)).map
      ((fun y : B=>⟨y.val,hBA y.property⟩ : B→AM) ⁻¹' ·)=_
    rw [hEN,List.map_map]
    rfl
  have hActual : Lift hk (openSection V B) (hVc.preimage continuous_subtype_val) (openSection_regular hV B)
      LB.E (restrict B S) (openSection V' (openPreimage S B)) hSc hS P:=hLBE.symm ▸ hActual
  have hJTest : IsGeoTestTower J P:=by
    apply (IsTowerIso.isGeoTestTower_iff Ψ hJ.isWellFormed.isClosedSubmanifold_N hJ.isWellFormed.isCoherent hFrame).mp
    rw [hWhole]
    exact hN0Test
  have hLBTest : IsGeoTestTower LB (restrict B S):=ambient_test_of_native_test hActual hn
    hLB.isWellFormed.isSNCDivisor hLBT LB rfl hLBN
    (fun _ _ ht=>GermIdeal.IsCoherent.holomorphicAt_mem hLB.isWellFormed.isCoherent ht) hJTest
  have hNuZ : (ν zO).val.val=z.val:=(hPoint zO).trans (congrArg Subtype.val hFixz)
  let F : openPreimage QR O → openPreimage S B:=fun w=>(ν w).val
  have hF : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel n) ∞ F:=
    (contMDiff_val hk hS).comp ν.contMDiff
  have hRecords:=hActual.whole_records hn hLB.isWellFormed.isSNCDivisor hLBT LB rfl hLBN
    (fun _ _ ht=>GermIdeal.IsCoherent.holomorphicAt_mem hLB.isWellFormed.isCoherent ht)
  have hTowerEq:=IsTowerIso.geoTransformAlong_eq Ψ hJ.isWellFormed.isClosedSubmanifold_N hJ.isWellFormed.isCoherent hFrame hJTest
  rw [hWhole,hRecords] at hTowerEq
  have hCurrentI : (geoTransformAlong LB (restrict B S)).ideal.IsCoherent:=
    (isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hLB.isWellFormed.isClosedSubmanifold_N hLB.isWellFormed.isCoherent (restrict B S) hLBTest).2
  have hComp:=whole_markedPullback_comp (contMDiff_val hk hS) ν.contMDiff
    (geoTransformAlong LB (restrict B S)) hCurrentI
  have hFinal : geoTransformAlong N0 (restrict O QR)=markedPullback (m:=k) F (geoTransformAlong LB (restrict B S)):=
    hTowerEq.trans hComp.symm
  refine ⟨Φ,χ,hGlue,hχ,pG,rfl,hFixp,O,hpO,f,g,hf,hg,fun _=>rfl,fun _=>rfl,hRaw,zO,rfl,
    B,hBA,hpB,Ψ,?_,hLBN,hLBT,hLB,hJ,hChanged,hWhole,hSc,hS,P,ν,hActual,hFrame,hPoint,hNuZ,
    hN0Test,hJTest,hLBTest,F,hF,hNuZ,hFinal⟩
  intro w
  exact (hΨ w).trans (rfl : (f w).val=(Φ w.val).val.val).symm

end
end Hironaka.HironakaActualNativeOriginalLowerTailEmbedding
