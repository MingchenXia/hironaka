import Hironaka.Resolution.HironakaActualOriginalCommonMaskRawOrder
import Hironaka.Invariant.StepOneTangentChange
import Hironaka.Resolution.HironakaActualRawOrderLocality

/-! Actual OWN contact masks at the two ORIGINAL true marks. Blueprint FIRST.
Same-input whole gluing and native raw locality consume the common-mask factor
producer; no future original LOWER-tail/raw/value comparison is asserted. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff BigOperators
namespace Hironaka.HironakaActualOriginalOwnContactRawOrder
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan GermIdealOrder DivisorExponentAlong
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal MarkedIdealOperationsTransform
  MarkedIdealEquivalence.MarkedIdeal HomogenizedGlueingTower HomogenizedIdealAlong
  HomogenizedIdealAlongTower ContactStageKept ContactStageInvDomain
  CoefficientIdeal CoefficientIdealRestriction ContactIndependenceAlong
  GermIdealPullbackCalculus BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  ResolutionInvariantSpec StepOneValue StepOneValueMasked StepOneLowerDomain StepOneCompare StepOneRegime
  TangentDirectionAlong CodimOneSupportAlong NonmonomialOrderLocal NonmonomialOrderTail
  CompanionRebase CompanionReductionAlong CompanionOpen HomogenizedIdeal
  HironakaEmbeddedAnalytic HironakaActualOriginalTrueMarkMaskCompanions HironakaActualTrueMarkCommonContact
  HironakaActualOriginalCommonMaskRawOrder HironakaActualOriginalHistoricalBarWeightedThreshold

variable {n : ℕ} {X Y : CMfd.{0} n}

private theorem hol {Z : CMfd.{0} n} {I : GermIdeal n Z} (hI : I.IsCoherent) :
    ∀x f,I.mem x f→HolomorphicAt n f x := fun _ _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem hI hf

private theorem span_closed {Z : CMfd.{0} n} {I : GermIdeal n Z} (hI : I.IsCoherent) :
    ∀x f,IsInSpanAt (n:=n) (I.mem x) x f→I.mem x f :=
  fun _ _ hf=>HomogenizedIdeal.mem_of_isInSpanAt hI hf

private theorem bar_test (M : MarkedIdeal n X) {k : ℕ} (hM : IsInvDomain k M)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T) : IsGeoTestTower (barMarked M) T :=
  ((coeff_homAlong_wEquiv M hM.isWellFormed.isClosedSubmanifold_N
    hM.isWellFormed.isCoherent hM.one_le_d).2 T).1.mpr hT

/- Repeats the held carrier/cosupport composition with ZERO engine credit. -/
private theorem bar_codim_eq (J K : MarkedIdeal n X) {k : ℕ}
    (hJ : IsInvDomain k J) (hK : IsInvDomain k K) (hN : J.N=K.N) (hWeak : WEquiv J K)
    (T : BlowupTower X Y) (hTJ : IsGeoTestTower J T) :
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
  refine ⟨hCos,?_⟩
  unfold codimOnePartAlong
  change {z | ∃s,RegularAtDim (n:=n) (geoTransformAlong (barMarked J) T).N z (s+1) ∧
    RegularAtDim (n:=n) (geoTransformAlong (barMarked J) T).cosupp z s}=_
  rw [hNJ,hCos]
  rfl

private theorem level_zero (M : MarkedIdeal n X) (hE : M.E=[])
    (T : BlowupTower X Y) (y : Y) : level M T y=0 := by
  simp only [level,origMembers,hE,List.length_nil,List.take_zero]
  rfl

private theorem zero_regime_iff (M : MarkedIdeal n X) (hE : M.E=[])
    (T : BlowupTower X Y) (y : Y) : stepRegime M 0 T y ↔
    y∉codimOnePartAlong (geoTransformAlong (barMarked M) T).N
      (geoTransformAlong (barMarked M) T).ideal (geoTransformAlong (barMarked M) T).d := by
  simp only [stepRegime,IsSpecial,level_zero M hE T y]
  simp

private theorem step_regime_eq (J K : MarkedIdeal n X) {k : ℕ}
    (hJ : IsInvDomain k J) (hK : IsInvDomain k K) (hN : J.N=K.N)
    (hJE : J.E=[]) (hKE : K.E=[]) (hWeak : WEquiv J K)
    (T : BlowupTower X Y) (hTJ : IsGeoTestTower J T) (y : Y) :
    stepRegime J 0 T y ↔ stepRegime K 0 T y := by
  rw [zero_regime_iff J hJE,zero_regime_iff K hKE,(bar_codim_eq J K hJ hK hN hWeak T hTJ).2]

private theorem step_runs (J K : MarkedIdeal n X) {k : ℕ}
    (hJ : IsInvDomain k J) (hK : IsInvDomain k K) (hN : J.N=K.N)
    (hJE : J.E=[]) (hKE : K.E=[]) (hWeak : WEquiv J K) :
    ∀{Y : CMfd.{0} n}(T : BlowupTower X Y),IsGeoTestTower J T→∀y : Y,
      regimeRun (stepRegime J 0) T y=regimeRun (stepRegime K 0) T y
  | _,.refl,_,_=>rfl
  | _,.step T C π hπ,hT,y=>by
    by_cases hR : stepRegime J 0 T (π y)
    · rw [regimeRun_step_of _ T C π hπ hR,
        regimeRun_step_of _ T C π hπ ((step_regime_eq J K hJ hK hN hJE hKE hWeak T hT.1 (π y)).mp hR),
        step_runs J K hJ hK hN hJE hKE hWeak T hT.1]
    · rw [regimeRun_step_of_not _ T C π hπ hR,
        regimeRun_step_of_not _ T C π hπ (fun h=>hR ((step_regime_eq J K hJ hK hN hJE hKE hWeak T hT.1 (π y)).mpr h))]

private def contactAmbient (J : MarkedIdeal n X) (w : X→ℂ) (T : BlowupTower X Y) : MarkedIdeal n Y :=
  withN (coeffMarkedAlong (geoTransformAlong (barMarked J) T)) (strictAlong T (J.N∩{x | w x=0}))

private theorem contact_coherent (J : MarkedIdeal n X) {k : ℕ} (hJ : IsInvDomain k J)
    (T : BlowupTower X Y) (hT : IsGeoTestTower J T) (w : X→ℂ) :
    (contactAmbient J w T).ideal.IsCoherent := by
  have hh:=(original_bar_weighted_history J hJ T hT).2.1
  exact isCoherent_coeffMarkedAlong hh.isWellFormed.isCoherent hh.isWellFormed.isClosedSubmanifold_N

private theorem raw_open (A : MarkedIdeal n Y) (hA : A.ideal.IsCoherent)
    (O : TopologicalSpace.Opens Y) (z : O) :
    nmOrd (M:=CMfd.of (n:=n) O) (MarkedIdeal.pullback (Subtype.val : O→Y) A) z=nmOrd A z.val :=
  HironakaActualRawOrderLocality.nmOrd_pullback_of_local (X:=Y) (Y:=CMfd.of (n:=n) O)
    contMDiff_subtype_val
    (fun p=>⟨DerivativeIdealAlongEtale.openInv O p,DerivativeIdealAlongEtale.isLocalInverseAt_val O p⟩)
    A (hol hA) (span_closed hA) z

private theorem kept_eq_contact (J : MarkedIdeal n X) (hE : J.E=[])
    (T : BlowupTower X Y) (w : X→ℂ) (O : TopologicalSpace.Opens Y) :
    contactMarkedKept J w T O=MaximalOrderStepOneB.contactMarked J.N J.ideal J.d w T O := by
  have hMask : ∀H∈(geoTransformAlong (coeffMarkedAlong (homMarkedAlong J)) T).E.take J.E.length,
      ∀y∈O,y∉H:=by simp only [hE,List.length_nil,List.take_zero,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  have h:=StepOneTangentChange.pullback_val_restrictedCoeffHom_eq J T w O hMask
  simpa only [hE,List.length_nil,List.replicate_zero,List.nil_append] using h

private theorem own_point (J : MarkedIdeal n X) {k : ℕ} (hJ : IsInvDomain k J)
    (hMax : IsMaximalOrderAlong J.N J.ideal J.d) (T : BlowupTower X Y)
    (hT : IsGeoTestTower J T) (y : Y) (hy : y∈(geoTransformAlong (barMarked J) T).cosupp)
    (hW : y∈maskB J T y) :
    (⟨y,hW⟩ : maskB J T y)∈(StepOneValueMasked.lowerMarkedB J T y).cosupp := by
  have h:= (isGeoTestTower_cosupp_lowerMarkedB J hJ.isWellFormed hJ.one_le_d hMax
    T (.refl : BlowupTower Y Y) (bar_test J hJ T hT) hy).2
  have hp : (⟨y,hW⟩ : openPreimage (.refl : BlowupTower Y Y) (maskB J T y))∈
      (geoTransformAlong (StepOneValueMasked.lowerMarkedB J T y)
        (restrict (maskB J T y) (.refl : BlowupTower Y Y))).cosupp:=by
    rw [h]
    exact hy
  exact hp

/- Generic SAME-input gluing consumes actual masks; ZERO repeated engine credit. -/
private theorem own_shared_glue (hn : 0<n) (J : MarkedIdeal n X) {k : ℕ}
    (hJ : IsInvDomain k J) (hMax : IsMaximalOrderAlong J.N J.ideal J.d) (hE : J.E=[])
    (T : BlowupTower X Y) (hT : IsGeoTestTower J T) (y : Y)
    (hy : y∈(geoTransformAlong (barMarked J) T).cosupp)
    (hZ : y∉codimOnePartAlong (geoTransformAlong (barMarked J) T).N
      (geoTransformAlong (barMarked J) T).ideal (geoTransformAlong (barMarked J) T).d)
    (U₂ : TopologicalSpace.Opens X) (v : X→ℂ)
    (hv : IsTangentDirectionAlong J.N J.ideal J.d U₂ v) (hxU₂ : T.proj y∈U₂)
    (O : TopologicalSpace.Opens Y) (_hOU₂ : (O:Set Y)⊆T.proj ⁻¹' (U₂:Set X)) (hyO : y∈O) :
    ∃hyOwn : y∈maskB J T y,
      IsInvDomain (k-1) (StepOneValueMasked.lowerMarkedB J T y) ∧
      (⟨y,hyOwn⟩ : maskB J T y)∈(StepOneValueMasked.lowerMarkedB J T y).cosupp ∧
      nmOrd (M:=CMfd.of (n:=n) (maskB J T y)) (StepOneValueMasked.lowerMarkedB J T y) ⟨y,hyOwn⟩=
        nmOrd (M:=CMfd.of (n:=n) O) (contactMarkedKept J v T O) ⟨y,hyO⟩ ∧
      ∃(Vu Vv : TopologicalSpace.Opens Y)(_hyu : y∈Vu)(hyv : y∈Vv)
        (ψ : CMfd.of (n:=n) Vv ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n:=n) Vu),
        Vu≤maskB J T y ∧ Vv≤O ∧ (ψ ⟨y,hyv⟩).val=y ∧
        MarkedIdeal.pullback ψ (contactMarkedKept J (tangentChoice J (T.proj y)).2 T Vu)=
          contactMarkedKept J v T Vv := by
  have hBarT:=bar_test J hJ T hT
  have hReg : stepRegime J 0 T y:=(zero_regime_iff J hE T y).mpr hZ
  obtain ⟨hyOwn,hOwnD⟩:=mem_lowerMask_and_isInvDomain_M J hJ.isWellFormed hJ.one_le_d hn hMax
    hJ.dimLE T hBarT hy hReg
  have hOwnPoint:=own_point J hJ hMax T hT y hy hyOwn
  obtain ⟨hxU₁,hu⟩:=tangentChoice_spec J
    (exists_tangent_of_mem_cosupp J hJ.isWellFormed hJ.one_le_d hMax T hBarT hy)
  have hx : T.proj y∈J.cosupp:=by
    have hh:=proj_mem_cosupp_of_mem_cosupp (𝔪:=barMarked J) hJ.isWellFormed.isClosedSubmanifold_N
      (isWellFormed_barMarked J hJ.isWellFormed).isCoherent T hBarT hy
    rw [cosupp_barMarked J hJ.isWellFormed hJ.one_le_d] at hh
    exact hh
  obtain ⟨G,hxG,hGlue⟩:=StepOneTangentChange.exists_tail_iso_opens hJ.isWellFormed.isCoherent
    hJ.isWellFormed.isClosedSubmanifold_N hJ.one_le_d hx hu hxU₁ hv hxU₂
  have hStepTest:=StepOneRegime.isGeoTestTower_stepOneMarked_of_coeffHom J T hBarT
  have hyStep : y∈(geoTransformAlong (MaximalOrderStepOneB.stepOneMarked J.N J.ideal J.d) T).cosupp:=by
    rw [StepOneRegime.cosupp_geoTransformAlong_stepOneMarked]
    exact hy
  obtain ⟨Vu,Vv,hyu,hyv,ψ,ξ,hVu,hVv,hIso,hFix,hRec⟩:=
    hGlue T (.refl : BlowupTower Y Y) hStepTest (maskB J T y) O y hyOwn hyO hxG hyStep
  have hψFix : (ψ ⟨y,hyv⟩).val=y:=by
    have hh:=hIso.proj_comm ⟨y,hyv⟩
    change ψ ⟨y,hyv⟩=ξ ⟨y,hyv⟩ at hh
    exact congrArg Subtype.val (hh.trans hFix)
  have hRecKept : MarkedIdeal.pullback ψ
      (contactMarkedKept J (tangentChoice J (T.proj y)).2 T Vu)=contactMarkedKept J v T Vv:=by
    rw [kept_eq_contact J hE,kept_eq_contact J hE]
    exact hRec
  let A:=contactAmbient J (tangentChoice J (T.proj y)).2 T
  let B:=contactAmbient J v T
  have hAI : A.ideal.IsCoherent:=contact_coherent J hJ T hT _
  have hBI : B.ideal.IsCoherent:=contact_coherent J hJ T hT _
  have hAB : MarkedIdeal.pullback (Subtype.val : Vv→Y) B=
      MarkedIdeal.pullback ψ (MarkedIdeal.pullback (Subtype.val : Vu→Y) A):=hRecKept.symm
  have hRaw:=(HironakaActualRawOrderLocality.order_and_cosupp_from_records B A
    (hol hBI) (span_closed hBI) (hol hAI) (span_closed hAI) Vv Vu ψ hAB ⟨y,hyv⟩).1
  rw [hψFix] at hRaw
  refine ⟨hyOwn,hOwnD,hOwnPoint,?_,Vu,Vv,hyu,hyv,ψ,hVu,hVv,hψFix,hRecKept⟩
  have hOwnRaw:=raw_open A hAI (maskB J T y) ⟨y,hyOwn⟩
  have hSharedRaw:=raw_open B hBI O ⟨y,hyO⟩
  exact hOwnRaw.trans (hRaw.symm.trans hSharedRaw.symm)

/- Resets elaboration of the same ordinary-data stage composition. -/
private theorem pair_raw_stage (hn : 0<n) (J K : MarkedIdeal n X) {k : ℕ}
    (hJ : IsInvDomain k J) (hK : IsInvDomain k K)
    (hMaxJ : IsMaximalOrderAlong J.N J.ideal J.d) (hMaxK : IsMaximalOrderAlong K.N K.ideal K.d)
    (hJE : J.E=[]) (hNK : J.N=K.N) (hWeak : WEquiv J K)
    (hContact : ∀z∈K.cosupp,z∈(tangentChoice K z).1 ∧
      IsTangentDirectionAlong J.N J.ideal J.d (tangentChoice K z).1 (tangentChoice K z).2)
    (T : BlowupTower X Y) (hTJ : IsGeoTestTower J T) (y : Y)
    (hyK : y∈(geoTransformAlong (barMarked K) T).cosupp)
    (hZK : y∉codimOnePartAlong (geoTransformAlong (barMarked K) T).N
      (geoTransformAlong (barMarked K) T).ideal (geoTransformAlong (barMarked K) T).d)
    (hyWK : y∈maskB K T y)
    (hLowerCos : (contactMarkedKept J (tangentChoice K (T.proj y)).2 T (maskB K T y)).cosupp=
      (StepOneValueMasked.lowerMarkedB K T y).cosupp)
    (hRaw : let S:=contactMarkedKept J (tangentChoice K (T.proj y)).2 T (maskB K T y)
      ∀z∈S.cosupp,(StepOneValueMasked.lowerMarkedB K T y).d*nmOrd (M:=CMfd.of (n:=n) (maskB K T y)) S z=
        S.d*nmOrd (M:=CMfd.of (n:=n) (maskB K T y)) (StepOneValueMasked.lowerMarkedB K T y) z) :
    ∃hyWJ : y∈maskB J T y,
      IsInvDomain (k-1) (StepOneValueMasked.lowerMarkedB J T y) ∧
      (⟨y,hyWJ⟩ : maskB J T y)∈(StepOneValueMasked.lowerMarkedB J T y).cosupp ∧
      (⟨y,hyWK⟩ : maskB K T y)∈(StepOneValueMasked.lowerMarkedB K T y).cosupp ∧
      (StepOneValueMasked.lowerMarkedB K T y).d*
        nmOrd (M:=CMfd.of (n:=n) (maskB J T y)) (StepOneValueMasked.lowerMarkedB J T y) ⟨y,hyWJ⟩=
      (StepOneValueMasked.lowerMarkedB J T y).d*
        nmOrd (M:=CMfd.of (n:=n) (maskB K T y)) (StepOneValueMasked.lowerMarkedB K T y) ⟨y,hyWK⟩ ∧
      ∃(Vu Vv : TopologicalSpace.Opens Y)(_hyu : y∈Vu)(hyv : y∈Vv)
        (ψ : CMfd.of (n:=n) Vv ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n:=n) Vu),
        Vu≤maskB J T y ∧ Vv≤maskB K T y ∧ (ψ ⟨y,hyv⟩).val=y ∧
        MarkedIdeal.pullback ψ (contactMarkedKept J (tangentChoice J (T.proj y)).2 T Vu)=
          contactMarkedKept J (tangentChoice K (T.proj y)).2 T Vv := by
  have hTK:=(hWeak.2 T).1.mp hTJ
  obtain ⟨hCos,hZeq⟩:=bar_codim_eq J K hJ hK hNK hWeak T hTJ
  have hyJ : y∈(geoTransformAlong (barMarked J) T).cosupp:=by rw [hCos];exact hyK
  have hZJ : y∉codimOnePartAlong (geoTransformAlong (barMarked J) T).N
      (geoTransformAlong (barMarked J) T).ideal (geoTransformAlong (barMarked J) T).d:=by
    rw [hZeq];exact hZK
  have hKPoint:=own_point K hK hMaxK T hTK y hyK hyWK
  have hSharedPoint : (⟨y,hyWK⟩ : maskB K T y)∈
      (contactMarkedKept J (tangentChoice K (T.proj y)).2 T (maskB K T y)).cosupp:=by
    rw [hLowerCos]
    exact hKPoint
  have hCross:=hRaw ⟨y,hyWK⟩ hSharedPoint
  have hxK : T.proj y∈K.cosupp:=by
    have hh:=proj_mem_cosupp_of_mem_cosupp (𝔪:=barMarked K) hK.isWellFormed.isClosedSubmanifold_N
      (isWellFormed_barMarked K hK.isWellFormed).isCoherent T (bar_test K hK T hTK) hyK
    rw [cosupp_barMarked K hK.isWellFormed hK.one_le_d] at hh
    exact hh
  obtain ⟨hxU₂,huJ⟩:=hContact (T.proj y) hxK
  let U₂ : TopologicalSpace.Opens X:=⟨(tangentChoice K (T.proj y)).1,huJ.isOpen⟩
  obtain ⟨hyWJ,hJOwnDomain,hJPoint,hOwnRaw,hLocal⟩:=own_shared_glue hn J hJ hMaxJ hJE T hTJ y hyJ hZJ
    U₂ (tangentChoice K (T.proj y)).2 huJ hxU₂ (maskB K T y) (fun z hz=>(interior_subset hz).1) hyWK
  refine ⟨hyWJ,hJOwnDomain,hJPoint,hKPoint,?_,hLocal⟩
  rw [hOwnRaw]
  exact hCross

/-- Ordinary ORIGINAL inputs derive the actual OWN masks and WHOLE local gluing,
then compare their native raw orders; original UPPER zero-regime clocks agree. -/
theorem original_lower_own_contact_raw_order {A : CMfd.{0} n}
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
          (∀y : Y,(stepRegime J 0 T y ↔ stepRegime K 0 T y) ∧
            regimeRun (stepRegime J 0) T y=regimeRun (stepRegime K 0) T y) ∧
          ∀y∈(geoTransformAlong (barMarked K) T).cosupp,
            y∉codimOnePartAlong (geoTransformAlong (barMarked K) T).N
              (geoTransformAlong (barMarked K) T).ideal (geoTransformAlong (barMarked K) T).d→
            ∃hyJ : y∈maskB J T y,∃hyK : y∈maskB K T y,
              let AJ:=StepOneValueMasked.lowerMarkedB J T y
              let AK:=StepOneValueMasked.lowerMarkedB K T y
              IsInvDomain ((k-1)-1) AJ ∧ IsInvDomain ((k-1)-1) AK ∧
              (⟨y,hyJ⟩ : maskB J T y)∈AJ.cosupp ∧ (⟨y,hyK⟩ : maskB K T y)∈AK.cosupp ∧
              AJ.d=(Finset.range ((Finset.range μ).prod (fun j=>μ-j))).prod
                (fun j=>(Finset.range μ).prod (fun j=>μ-j)-j) ∧
              AK.d=(Finset.range ((Finset.range (e*μ)).prod (fun j=>e*μ-j))).prod
                (fun j=>(Finset.range (e*μ)).prod (fun j=>e*μ-j)-j) ∧
              AJ.E.length=T.length ∧ AK.E.length=T.length ∧
              AK.d*nmOrd (M:=CMfd.of (n:=n) (maskB J T y)) AJ ⟨y,hyJ⟩=
                AJ.d*nmOrd (M:=CMfd.of (n:=n) (maskB K T y)) AK ⟨y,hyK⟩ ∧
              ∃(Vu Vv : TopologicalSpace.Opens Y)(_hyu : y∈Vu)(hyv : y∈Vv)
                (ψ : CMfd.of (n:=n) Vv ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n:=n) Vu),
                Vu≤maskB J T y ∧ Vv≤maskB K T y ∧ (ψ ⟨y,hyv⟩).val=y ∧
                MarkedIdeal.pullback ψ (contactMarkedKept J (tangentChoice J (T.proj y)).2 T Vu)=
                  contactMarkedKept J (tangentChoice K (T.proj y)).2 T Vv := by
  obtain ⟨hm,hxU,_hMask,_hNatural,hJ,hK,hMaxJ,hMaxK,hJN,hKN,hJE,hKE,hJd,hKd,
    _hCompJ,_hCompK,hWeak,_hUpper⟩:=
    original_lower_true_mark_companions hn Q hQ hN hE hMax W hW hSing a ha
  obtain ⟨_hmC,_hxUC,_hJC,_hKC,_hNC,_hJdC,_hKdC,hzJ,hzK,_hTangent,hContacts⟩:=
    original_lower_selected_common_contact hn Q hQ hN hE hMax W hW hSing a ha
  obtain ⟨_hmM,_hxUM,_hJM,_hKM,_hJEM,_hKEM,_hJdM,_hKdM,_hzJM,_hzKM,hMasks⟩:=
    original_lower_common_mask_raw_order hn Q hQ hN hE hMax W hW hSing a ha
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
  refine ⟨hTK,fun y=>⟨step_regime_eq J K hJ hK hNK hJE hKE hWeak T hTJ y,
    step_runs J K hJ hK hNK hJE hKE hWeak T hTJ y⟩,?_⟩
  intro y hyK hZK
  obtain ⟨hyWK,_hRKOwn,_hSharedDomain,hKOwnDomain,_hNR,_hER,hdJ,hdK,hLenJ,hLenK,hLowerCos,hRaw⟩:=
    (hMasks T hTJ).2 y hyK hZK
  have hContacts' : ∀z∈K.cosupp,z∈(tangentChoice K z).1 ∧
      IsTangentDirectionAlong J.N J.ideal J.d (tangentChoice K z).1 (tangentChoice K z).2:=by
    intro z hz
    exact ⟨(hContacts z hz).1,(hContacts z hz).2.2.1⟩
  obtain ⟨hyWJ,hJOwnDomain,hJPoint,hKPoint,hOwnCross,hLocal⟩:=
    pair_raw_stage hn J K hJ hK hMaxJ hMaxK hJE hNK hWeak hContacts' T hTJ y hyK hZK hyWK hLowerCos hRaw
  refine ⟨hyWJ,hyWK,hJOwnDomain,hKOwnDomain,hJPoint,hKPoint,hdJ,hdK,?_,?_,hOwnCross,hLocal⟩
  · simpa only [StepOneValueMasked.lowerMarkedB,contactMarkedKept,MarkedIdeal.pullback,withN,List.length_map] using hLenJ
  · exact hLenK

end
end Hironaka.HironakaActualOriginalOwnContactRawOrder
