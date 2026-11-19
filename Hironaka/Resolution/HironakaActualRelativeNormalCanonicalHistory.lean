import Hironaka.Resolution.HironakaActualRelativeNormalGeometry
import Hironaka.Resolution.HironakaOriginalFamilyDepthStability

/-! Actual original relative-open normal canonical histories, without extending
the original coherent ideal to the whole coordinate space. Source-first
blueprint: hironaka-actual-relative-normal-canonical-history-20261102.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualRelativeNormalCanonicalHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdealTowerTransport
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  ResolutionInvariantSpec InvDomainTowerAlong CanonicalCentres NormalCrossings
  HironakaActualOpenZeroSectionDifferentials HironakaRelativeNormalIdeal
  HironakaActualCentreJointJets HironakaActualIntrinsicStableAmbientIso
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionOrderHistory
  HironakaActualNativeHistoryExistence HironakaActualNativeInvariantDomain
  HironakaOriginalFamilyDepthStability HironakaActualSectionBoundaryDimension
  HironakaActualMarkOneFixedContactHistory HironakaActualRelativeNormalGeometry
  HironakaDisjointCoherentNormalRecoding
  HironakaActualZeroCoordinateContactSeed
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionOrderedChoiceImageTrace
  SubmanifoldChartedSpace SubmanifoldCodRestrict RelativePrincipalizationSpan

private abbrev baseModel {n : ℕ} (U : Opens (ComplexModel n)) : CMfd n:=CMfd.of (n:=n) U
private abbrev ambientModel {n : ℕ} (U : Opens (ComplexModel n)) : CMfd (n+1):=
  CMfd.of (n:=n+1) (productOpen U)
private abbrev wholeOpenModel {n : ℕ} (U : Opens (ComplexModel n)) : CMfd (n+1):=
  CMfd.of (n:=n+1) (⊤ : Opens (productOpen U))

def normalPlane {n : ℕ} (U : Opens (ComplexModel n)) : Set (wholeOpenModel U):=
  (Subtype.val : (⊤ : Opens (productOpen U))→productOpen U) ⁻¹'
    HironakaActualNativeSectionInitialBar.zeroPlane U

theorem normalPlane_regular {n : ℕ} (U : Opens (ComplexModel n)) :
    ∀z∈normalPlane U,RegularAtDim (n:=n+1) (normalPlane U) z n:=by
  intro z hz
  exact AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr
    (HironakaActualNativeSectionInitialBar.zeroPlane_regular U z.val hz)

private theorem normalPlane_closed {n : ℕ} (U : Opens (ComplexModel n)) : IsClosed (normalPlane U):=by
  have h : IsClosed {z : (⊤ : Opens (productOpen U)) | actualJointNormalProjection n 1 z.val.val=0}:=
    isClosed_eq ((actualJointNormalProjection n 1).continuous.comp
      ((continuous_subtype_val : Continuous (Subtype.val : productOpen U→ComplexModel (n+1))).comp
        (continuous_subtype_val : Continuous (Subtype.val : (⊤ : Opens (productOpen U))→productOpen U)))) continuous_const
  have he : normalPlane U={z : (⊤ : Opens (productOpen U)) | actualJointNormalProjection n 1 z.val.val=0}:=by
    ext z
    change (projection U z.val∈univ ∧ actualJointNormalProjection n 1 z.val.val=0) ↔
      actualJointNormalProjection n 1 z.val.val=0
    simp only [mem_univ,true_and]
  exact he.symm ▸ h

private theorem projection_section {n : ℕ} (U : Opens (ComplexModel n)) (x : U) :
    projection U (zeroSection U x)=x:=by
  apply Subtype.ext
  exact tangentProjection_tangentInclusion n 1 x.val

def normalBaseEquiv {n : ℕ} (U : Opens (ComplexModel n)) :
    baseModel U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      nativeManifold (Nat.le_succ n) (normalPlane U) (normalPlane_regular U):=by
  let :=chartedSpace (Nat.le_succ n) (normalPlane_regular U)
  have :=isComplexManifold_chartedSpace (Nat.le_succ n) (normalPlane_regular U)
  let s : U→(⊤ : Opens (productOpen U)):=fun x=>⟨zeroSection U x,trivial⟩
  have hs : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (n+1)) ∞ s:=
    BlowupRestrictOpen.contMDiff_opens_mk (V:=⊤) (f:=zeroSection U) (zeroSection_contMDiff U) (fun _=>trivial)
  have hZero (x : U) : s x∈normalPlane U:=by
    refine ⟨mem_univ _,?_⟩
    change actualJointNormalProjection n 1 (tangentInclusion n 1 x.val)=0
    simp
  refine ⟨⟨(fun x=>⟨s x,hZero x⟩),(fun z=>projection U z.val.val),?_,?_⟩,?_,?_⟩
  · exact projection_section U
  · intro z
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change tangentInclusion n 1 (tangentProjection n 1 z.val.val.val)=z.val.val.val
    have hq : actualJointNormalProjection n 1 z.val.val.val=0:=z.property.2
    simpa only [HironakaActualIntrinsicStableAmbientIso.join,hq,map_zero,add_zero] using
      (join_projections (n:=n) (m:=1) z.val.val.val)
  · exact contMDiff_codRestrict (Nat.le_succ n) (normalPlane_regular U) hs hZero
  · exact (projection_contMDiff U).comp
      (contMDiff_subtype_val.comp (contMDiff_val (Nat.le_succ n) (normalPlane_regular U)))

private theorem normalBaseEquiv_val {n : ℕ} (U : Opens (ComplexModel n)) (x : U) :
    ((normalBaseEquiv U) x).val.val=zeroSection U x:=rfl

def relativeNormalContact {n : ℕ} {U : Opens (ComplexModel n)} (I : GermIdeal n U) :
    MarkedIdeal (n+1) (wholeOpenModel U):=
  fixedContact (relativeNormalMarked I) (relativeNormalCoordinate U)

private theorem normal_contact_support {n : ℕ} {U : Opens (ComplexModel n)} {I : GermIdeal n U}
    (hI : I.IsCoherent) : (relativeNormalContact I).N⊆normalPlane U:=by
  intro z hz
  have hRecord:=fixed_contact_record (relativeNormalMarked I) (relativeNormalIdeal_isCoherent hI) rfl rfl rfl
    (relativeNormalCoordinate U)
  change z∈(fixedContact (relativeNormalMarked I) (relativeNormalCoordinate U)).N at hz
  rw [hRecord] at hz
  have hz0 : relativeNormalCoordinate U z.val=0:=hz
  refine ⟨mem_univ _,?_⟩
  ext i
  have hi : i=0:=Fin.eq_zero i
  subst i
  simpa [relativeNormalCoordinate,addedCoordinate,HironakaActualGraphFunctionalIdeal.graphFunction,zeroFunction] using hz0

private theorem normal_contact_boundary {n : ℕ} {U : Opens (ComplexModel n)} {I : GermIdeal n U}
    (hI : I.IsCoherent) : (relativeNormalContact I).E=[]:=by
  change (fixedContact (relativeNormalMarked I) (relativeNormalCoordinate U)).E=[]
  rw [fixed_contact_record (relativeNormalMarked I) (relativeNormalIdeal_isCoherent hI) rfl rfl rfl]
  rfl

private theorem normal_contact_transverse {n : ℕ} {U : Opens (ComplexModel n)} {I : GermIdeal n U}
    (hI : I.IsCoherent) : IsTransverse (n+1) (normalPlane U) (relativeNormalContact I).E:=by
  rw [normal_contact_boundary hI]
  exact isTransverse_nil_of_isClosedSubmanifold
    ⟨normalPlane_closed U,fun z hz=>⟨n,normalPlane_regular U z hz⟩⟩

/-- The ENTIRE actual original relative contact record is exactly the original
base record under the genuine zero-section/native-plane biholomorphism. -/
theorem normal_contact_native_record {n : ℕ} {U : Opens (ComplexModel n)}
    {I : GermIdeal n U} (hI : I.IsCoherent) :
    MarkedIdeal.pullback (normalBaseEquiv U)
      (nativePullback (Nat.le_succ n) (normalPlane U) (normalPlane_regular U) (relativeNormalContact I))=
      relativeBaseMarked I:=by
  let :=chartedSpace (Nat.le_succ n) (normalPlane_regular U)
  have :=isComplexManifold_chartedSpace (Nat.le_succ n) (normalPlane_regular U)
  let K : MarkedIdeal (n+1) (ambientModel U):=⟨{z | relativeNormalCoordinate U z=0},[],relativeNormalIdeal I,1⟩
  have hK : K.ideal.IsCoherent:=relativeNormalIdeal_isCoherent hI
  have hRecord:=fixed_contact_record (relativeNormalMarked I) hK rfl rfl rfl (relativeNormalCoordinate U)
  change relativeNormalContact I=MarkedIdeal.pullback
    (Subtype.val : (⊤ : Opens (productOpen U))→productOpen U) K at hRecord
  have h1:=whole_markedPullback_comp
    (f:=(Subtype.val : (⊤ : Opens (productOpen U))→productOpen U))
    (g:=(Subtype.val : nativeManifold (Nat.le_succ n) (normalPlane U) (normalPlane_regular U)→(⊤ : Opens (productOpen U))))
    contMDiff_subtype_val (contMDiff_val (Nat.le_succ n) (normalPlane_regular U)) K hK
  have hInner : nativePullback (Nat.le_succ n) (normalPlane U) (normalPlane_regular U) (relativeNormalContact I)=
      markedPullback (m:=n)
        (fun z : nativeManifold (Nat.le_succ n) (normalPlane U) (normalPlane_regular U)=>z.val.val) K:=
    (congrArg (fun A : MarkedIdeal (n+1) (wholeOpenModel U)=>
      nativePullback (Nat.le_succ n) (normalPlane U) (normalPlane_regular U) A) hRecord).trans h1.symm
  have h2:=whole_markedPullback_comp
    (f:=fun z : nativeManifold (Nat.le_succ n) (normalPlane U) (normalPlane_regular U)=>z.val.val)
    (g:=normalBaseEquiv U)
    (contMDiff_subtype_val.comp (contMDiff_val (Nat.le_succ n) (normalPlane_regular U)))
    (normalBaseEquiv U).contMDiff K hK
  have hSection : markedPullback (m:=n) (zeroSection U) K=relativeBaseMarked I:=by
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · ext x
      change relativeNormalCoordinate U (zeroSection U x)=0 ↔ x∈univ
      simp [relativeNormalCoordinate,addedCoordinate,HironakaActualGraphFunctionalIdeal.graphFunction,
        zeroFunction,zeroSection]
    · rfl
    · exact section_pullback_relativeNormalIdeal hI
    · rfl
  exact (congrArg (MarkedIdeal.pullback (normalBaseEquiv U)) hInner).trans (h2.symm.trans hSection)

private theorem normal_history_data {n q : ℕ} {U : Opens (ComplexModel n)} {I : GermIdeal n U}
    (hM : IsInvDomain q (relativeBaseMarked I)) {Y : CMfd.{0} (n+1)}
    (T : BlowupTower (ambientModel U) Y)
    (hCan : IsCanonical (relativeNormalMarked I)
      ((invFamily (Nat.succ_pos n) (q+1)).inv (relativeNormalMarked I)) T) :
    IsInvDomain q (relativeNormalContact I) ∧
    IsCanonical (relativeNormalContact I) ((invFamily (Nat.succ_pos n) q).inv (relativeNormalContact I)) (restrict ⊤ T) ∧
    (∀y∈(geoTransformAlong (relativeNormalMarked I) T).cosupp,
      (invFamily (Nat.succ_pos n) (q+1)).inv (relativeNormalMarked I) T y=
        initialEmbedding q ((invFamily (Nat.succ_pos n) q).inv (relativeNormalContact I) (restrict ⊤ T) ⟨y,mem_univ _⟩)) ∧
    (geoTransformAlong (relativeNormalContact I) (restrict ⊤ T)).cosupp=
      (Subtype.val : openPreimage T (⊤ : Opens (productOpen U))→Y) ⁻¹'
        (geoTransformAlong (relativeNormalMarked I) T).cosupp ∧
    (geoTransformAlong (relativeNormalContact I) (restrict ⊤ T)).E=
      (geoTransformAlong (relativeNormalMarked I) T).E.map
        ((Subtype.val : openPreimage T (⊤ : Opens (productOpen U))→Y) ⁻¹' ·):=by
  obtain ⟨hJ,hmax,hZ,hu⟩:=relative_normal_original_geometry hM
  obtain ⟨hDom,_hStepCan,hKCan,_hStepVal,hFullVal,hCos,hE,_hLen,_hMax⟩:=
    fixed_contact_canonical_history (relativeNormalMarked I) hJ rfl rfl rfl hmax hZ
      (relativeNormalCoordinate U) hu T hCan
  exact ⟨hDom,hKCan,hFullVal,hCos,hE⟩

private theorem exists_normal_native_history {n q : ℕ} {U : Opens (ComplexModel n)} (hn : 0<n)
    {I : GermIdeal n U} (hM : IsInvDomain q (relativeBaseMarked I))
    {Y : CMfd.{0} (n+1)} (T : BlowupTower (ambientModel U) Y)
    (hCan : IsCanonical (relativeNormalMarked I)
      ((invFamily (Nat.succ_pos n) (q+1)).inv (relativeNormalMarked I)) T) :
    ∃(V : Set (openPreimage T (⊤ : Opens (productOpen U))))
      (hVc : IsClosed V)(hV : ∀z∈V,RegularAtDim (n:=n+1) V z n)
      (Q : BlowupTower (nativeManifold (Nat.le_succ n) (normalPlane U) (normalPlane_regular U))
        (nativeManifold (Y:=CMfd.of (n:=n+1) (openPreimage T (⊤ : Opens (productOpen U)))) (Nat.le_succ n) V hV)),
      Lift (Nat.le_succ n) (normalPlane U) (normalPlane_closed U) (normalPlane_regular U)
        (relativeNormalContact I).E (restrict ⊤ T) V hVc hV Q ∧
      IsInvDomain q (nativePullback (Nat.le_succ n) (normalPlane U) (normalPlane_regular U) (relativeNormalContact I)) ∧
      IsCanonical (nativePullback (Nat.le_succ n) (normalPlane U) (normalPlane_regular U) (relativeNormalContact I))
        ((invFamily hn q).inv (nativePullback (Nat.le_succ n) (normalPlane U) (normalPlane_regular U) (relativeNormalContact I))) Q ∧
      ∀z : nativeManifold (Y:=CMfd.of (n:=n+1) (openPreimage T (⊤ : Opens (productOpen U)))) (Nat.le_succ n) V hV,
        z.val.val∈(geoTransformAlong (relativeNormalMarked I) T).cosupp →
        (invFamily (Nat.succ_pos n) q).inv (relativeNormalContact I) (restrict ⊤ T) z.val=
          sameIndexMap 1 q ((invFamily hn q).inv
            (nativePullback (Nat.le_succ n) (normalPlane U) (normalPlane_regular U) (relativeNormalContact I)) Q z) := by
  obtain ⟨hDom,hContactCan,_hFullValues,hContactCos,_hContactE⟩:=normal_history_data hM T hCan
  have hTest:=Seq.ResolutionInvariantExt.isGeoTestTower_of_isCanonical
    (invFamily (Nat.succ_pos n) q) hDom (restrict ⊤ T) hContactCan
  obtain ⟨V,hVc,hV,Q,hLift,_hNativeTest⟩:=exists_native_history_of_original_test (Nat.succ_pos n)
    (Nat.le_succ n) (normalPlane U) (normalPlane_closed U) (normalPlane_regular U)
    (relativeNormalContact I) hDom (normal_contact_support hM.isWellFormed.isCoherent) (normal_contact_transverse hM.isWellFormed.isCoherent) (restrict ⊤ T) hTest
  have hNativeDom:=isInvDomain_nativePullback (Nat.succ_pos n) (Nat.le_succ n) (normalPlane_regular U)
    (relativeNormalContact I) hDom (normal_contact_support hM.isWellFormed.isCoherent) (normal_contact_transverse hM.isWellFormed.isCoherent)
  obtain ⟨hNativeCan,hValues⟩:=HironakaOriginalFamilyDepthStability.Lift.original_same_bound_values
    (Nat.succ_pos n) hn (relativeNormalContact I) hDom (normal_contact_support hM.isWellFormed.isCoherent) (normal_contact_transverse hM.isWellFormed.isCoherent) hLift hContactCan
  refine ⟨V,hVc,hV,Q,hLift,hNativeDom,hNativeCan,?_⟩
  intro z hz
  have hCos:=hContactCos
  have hzContact : z.val∈(geoTransformAlong (relativeNormalContact I) (restrict ⊤ T)).cosupp:=by
    rw [hCos]
    exact hz
  simpa using hValues z hzContact

private theorem maxLocus_image_of_values {A B α β : Type} [LinearOrder α] [LinearOrder β]
    (f : A→α) (g : B→β) (s : Set A) (t : Set B) (j : B→A) (F : β→α)
    (hF : StrictMono F) (hImage : j '' t=s) (hValues : ∀z∈t,f (j z)=F (g z)) :
    ResolutionDriver.maxLocus f s=j '' ResolutionDriver.maxLocus g t:=by
  ext a
  constructor
  · rintro ⟨ha,hmax⟩
    obtain ⟨b,hb,rfl⟩:=hImage.symm ▸ ha
    refine ⟨b,⟨hb,?_⟩,rfl⟩
    intro c hc
    apply hF.le_iff_le.mp
    rw [←hValues c hc,←hValues b hb]
    exact hmax (j c) (hImage ▸ mem_image_of_mem j hc)
  · rintro ⟨b,⟨hb,hmax⟩,rfl⟩
    refine ⟨hImage ▸ mem_image_of_mem j hb,?_⟩
    intro a ha
    obtain ⟨c,hc,rfl⟩:=hImage.symm ▸ ha
    rw [hValues c hc,hValues b hb]
    exact hF.monotone (hmax c hc)

/-- A full-carrier ORIGINAL RELATIVE normal extension with ORIGINAL empty boundary
internally produces its SAME actual native/base canonical history and map.
Every old/born boundary slot and every chronological empty step is retained. -/
theorem exists_original_relative_normal_base_history {n q : ℕ} {U : Opens (ComplexModel n)} (hn : 0<n)
    {I : GermIdeal n U} (hM : IsInvDomain q (relativeBaseMarked I))
    {Y : CMfd.{0} (n+1)} (T : BlowupTower (ambientModel U) Y)
    (hCan : IsCanonical (relativeNormalMarked I)
      ((invFamily (Nat.succ_pos n) (q+1)).inv (relativeNormalMarked I)) T) :
    ∃(V : Set (openPreimage T (⊤ : Opens (productOpen U))))
      (hVc : IsClosed V)(hV : ∀z∈V,RegularAtDim (n:=n+1) V z n)
      (Q : BlowupTower (nativeManifold (Nat.le_succ n) (normalPlane U) (normalPlane_regular U))
        (nativeManifold (Y:=CMfd.of (n:=n+1) (openPreimage T (⊤ : Opens (productOpen U)))) (Nat.le_succ n) V hV)),
      Lift (Nat.le_succ n) (normalPlane U) (normalPlane_closed U) (normalPlane_regular U)
        (relativeNormalContact I).E (restrict ⊤ T) V hVc hV Q ∧
      let H:=transport (normalBaseEquiv U) Q
      let j : H.target→Y:=fun z=>(H.back z).val.val
      IsCanonical (relativeBaseMarked I) ((invFamily hn q).inv (relativeBaseMarked I)) H.tower ∧
      IsGeoTestTower (relativeBaseMarked I) H.tower ∧ H.tower.length=T.length ∧
      (∀z,T.proj (j z)=zeroSection U (H.tower.proj z)) ∧
      (geoTransformAlong (relativeBaseMarked I) H.tower).E=
        (geoTransformAlong (relativeNormalMarked I) T).E.map (j ⁻¹' ·) ∧
      (geoTransformAlong (relativeBaseMarked I) H.tower).cosupp=
        j ⁻¹' (geoTransformAlong (relativeNormalMarked I) T).cosupp ∧
      j '' (geoTransformAlong (relativeBaseMarked I) H.tower).cosupp=
        (geoTransformAlong (relativeNormalMarked I) T).cosupp ∧
      (∀z∈(geoTransformAlong (relativeBaseMarked I) H.tower).cosupp,
        (invFamily (Nat.succ_pos n) (q+1)).inv (relativeNormalMarked I) T (j z)=
          initialEmbedding q (sameIndexMap 1 q ((invFamily hn q).inv (relativeBaseMarked I) H.tower z))) ∧
      ResolutionDriver.maxLocus ((invFamily (Nat.succ_pos n) (q+1)).inv (relativeNormalMarked I) T)
        (geoTransformAlong (relativeNormalMarked I) T).cosupp=
        j '' ResolutionDriver.maxLocus ((invFamily hn q).inv (relativeBaseMarked I) H.tower)
          (geoTransformAlong (relativeBaseMarked I) H.tower).cosupp ∧
      (IsGeoResolution (relativeNormalMarked I) T ↔ IsGeoResolution (relativeBaseMarked I) H.tower) := by
  obtain ⟨V,hVc,hV,Q,hLift,hNativeDom,hNativeCan,hContactValues⟩:=exists_normal_native_history hn hM T hCan
  let NEnd : CMfd n:=nativeManifold
    (Y:=CMfd.of (n:=n+1) (openPreimage T (⊤ : Opens (productOpen U)))) (Nat.le_succ n) V hV
  let B:=nativePullback (Nat.le_succ n) (normalPlane U) (normalPlane_regular U) (relativeNormalContact I)
  let H:=transport (normalBaseEquiv U) Q
  let j : H.target→Y:=fun z=>(H.back z).val.val
  have hData:=normal_history_data hM T hCan
  have hDom:=hData.1
  have hTrans:=normal_contact_transverse hM.isWellFormed.isCoherent
  have hE:=hDom.isWellFormed.isSNCDivisor
  have hhol : ∀z g,(relativeNormalContact I).ideal.mem z g → HolomorphicAt (n+1) g z:=
    fun _ _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hDom.isWellFormed.isCoherent hg
  have hInitial : MarkedIdeal.pullback (normalBaseEquiv U) B=relativeBaseMarked I:=
    normal_contact_native_record hM.isWellFormed.isCoherent
  have hIso:=transport_isTowerIso (normalBaseEquiv U) Q
  have hNativeTest:=Seq.ResolutionInvariantExt.isGeoTestTower_of_isCanonical (invFamily hn q) hNativeDom Q hNativeCan
  have hBaseCan : IsCanonical (relativeBaseMarked I) ((invFamily hn q).inv (relativeBaseMarked I)) H.tower:=by
    have h:=Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso (invFamily hn q) hNativeDom
      (normalBaseEquiv U) hIso hNativeCan
    change IsCanonical (MarkedIdeal.pullback (normalBaseEquiv U) B)
      ((invFamily hn q).inv (MarkedIdeal.pullback (normalBaseEquiv U) B)) H.tower at h
    simpa only [hInitial] using h
  have hBaseTest:=Seq.ResolutionInvariantExt.isGeoTestTower_of_isCanonical (invFamily hn q) hM H.tower hBaseCan
  have hSourceTest:=Seq.ResolutionInvariantExt.isGeoTestTower_of_isCanonical
    (invFamily (Nat.succ_pos n) (q+1)) (relative_normal_original_geometry hM).1 T hCan
  have hWholeBase : geoTransformAlong (relativeBaseMarked I) H.tower=
      MarkedIdeal.pullback H.back (geoTransformAlong B Q):=by
    have h:=BlowupTowerIsomorphism.IsTowerIso.geoTransformAlong_eq (normalBaseEquiv U)
      hNativeDom.isWellFormed.isClosedSubmanifold_N hNativeDom.isWellFormed.isCoherent hIso hNativeTest
    exact (congrArg (fun K : MarkedIdeal n (baseModel U)=>geoTransformAlong K H.tower) hInitial).symm.trans h
  have hNativeRecord:=hLift.whole_records (Nat.succ_pos n) hE hTrans (relativeNormalContact I)
    rfl (normal_contact_support hM.isWellFormed.isCoherent) hhol
  have hNativeCos:=HironakaActualNativeSectionOrderHistory.Lift.current_cosupport hLift (Nat.succ_pos n) hE hTrans (relativeNormalContact I)
    rfl (normal_contact_support hM.isWellFormed.isCoherent) hhol
  have hContactCos:=hData.2.2.2.1
  have hContactE:=hData.2.2.2.2
  have hBaseCos : (geoTransformAlong (relativeBaseMarked I) H.tower).cosupp=
      H.back ⁻¹' (geoTransformAlong B Q).cosupp:=by
    have h:=BlowupTowerIsomorphism.IsTowerIso.cosupp_geoTransformAlong (normalBaseEquiv U)
      hNativeDom.isWellFormed.isClosedSubmanifold_N hNativeDom.isWellFormed.isCoherent hIso hNativeTest
    exact (congrArg (fun K : MarkedIdeal n (baseModel U)=>(geoTransformAlong K H.tower).cosupp) hInitial).symm.trans h
  have hCos : (geoTransformAlong (relativeBaseMarked I) H.tower).cosupp=
      j ⁻¹' (geoTransformAlong (relativeNormalMarked I) T).cosupp:=by
    rw [hBaseCos,hNativeCos,hContactCos]
    rfl
  have hBoundary : (geoTransformAlong (relativeBaseMarked I) H.tower).E=
      (geoTransformAlong (relativeNormalMarked I) T).E.map (j ⁻¹' ·):=by
    have h1:=congrArg (fun K : MarkedIdeal n H.target=>K.E) hWholeBase
    change (geoTransformAlong (relativeBaseMarked I) H.tower).E=(geoTransformAlong B Q).E.map (H.back ⁻¹' ·) at h1
    have h2:=congrArg (fun K : MarkedIdeal n NEnd=>K.E) hNativeRecord
    change (geoTransformAlong B Q).E=(geoTransformAlong (relativeNormalContact I) (restrict ⊤ T)).E.map
      ((Subtype.val : V → openPreimage T (⊤ : Opens (productOpen U))) ⁻¹' ·) at h2
    rw [h2,hContactE] at h1
    simpa only [List.map_map,Function.comp_def,preimage_preimage] using h1
  have hImage : j '' (geoTransformAlong (relativeBaseMarked I) H.tower).cosupp=
      (geoTransformAlong (relativeNormalMarked I) T).cosupp:=by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact (Set.ext_iff.mp hCos z).mp hz
    · intro hy
      let yTop : openPreimage T (⊤ : Opens (productOpen U)):=⟨y,mem_univ _⟩
      have hyContact : yTop∈(geoTransformAlong (relativeNormalContact I) (restrict ⊤ T)).cosupp:=by
        rw [hContactCos]
        exact hy
      have hyV : yTop∈V:=HironakaActualNativeSectionOrderHistory.Lift.current_carrier_subset hLift (relativeNormalContact I) (normal_contact_support hM.isWellFormed.isCoherent)
        ((geoTransformAlong (relativeNormalContact I) (restrict ⊤ T)).cosupp_subset_N hyContact)
      let w : NEnd:=⟨yTop,hyV⟩
      let z:=H.back.symm w
      have hjz : j z=y:=by
        change (H.back (H.back.symm w)).val.val=y
        rw [H.back.apply_symm_apply]
      refine ⟨z,?_,hjz⟩
      rw [hCos]
      change j z∈(geoTransformAlong (relativeNormalMarked I) T).cosupp
      exact hjz.symm ▸ hy
  have hValues : ∀z∈(geoTransformAlong (relativeBaseMarked I) H.tower).cosupp,
      (invFamily (Nat.succ_pos n) (q+1)).inv (relativeNormalMarked I) T (j z)=
        initialEmbedding q (sameIndexMap 1 q ((invFamily hn q).inv (relativeBaseMarked I) H.tower z)):=by
    intro z hz
    have hzFull : j z∈(geoTransformAlong (relativeNormalMarked I) T).cosupp:=(Set.ext_iff.mp hCos z).mp hz
    have hzNative : H.back z∈(geoTransformAlong B Q).cosupp:=(Set.ext_iff.mp hBaseCos z).mp hz
    have hBaseValue:= (invFamily hn q).isInvValue.towerIso (normalBaseEquiv U) B hNativeDom
      H.tower Q H.back hIso hNativeCan z hzNative
    have hBaseValue' : (invFamily hn q).inv (relativeBaseMarked I) H.tower z=(invFamily hn q).inv B Q (H.back z):=by
      simpa only [hInitial] using hBaseValue
    have hUpper:=hData.2.2.1 (j z) hzFull
    change (invFamily (Nat.succ_pos n) (q+1)).inv (relativeNormalMarked I) T (j z)=
      initialEmbedding q ((invFamily (Nat.succ_pos n) q).inv (relativeNormalContact I) (restrict ⊤ T) (H.back z).val) at hUpper
    exact hUpper.trans (congrArg (fun v=>initialEmbedding q v)
      ((hContactValues (H.back z) hzFull).trans (congrArg (sameIndexMap 1 q) hBaseValue'.symm)))
  have hSquare : ∀z,T.proj (j z)=zeroSection U (H.tower.proj z):=by
    intro z
    have h1:=congrArg (fun x : wholeOpenModel U=>x.val) (hLift.square (H.back z))
    have h2:=congrArg (fun x : nativeManifold (Nat.le_succ n) (normalPlane U) (normalPlane_regular U)=>x.val.val)
      (hIso.proj_comm z)
    change zeroSection U (H.tower.proj z)=(Q.proj (H.back z)).val.val at h2
    have h1' : T.proj (j z)=(Q.proj (H.back z)).val.val:=by
      simpa only [proj_restrict] using h1
    exact h1'.trans h2.symm
  have hMaximum:=maxLocus_image_of_values
    ((invFamily (Nat.succ_pos n) (q+1)).inv (relativeNormalMarked I) T)
    ((invFamily hn q).inv (relativeBaseMarked I) H.tower)
    (geoTransformAlong (relativeNormalMarked I) T).cosupp (geoTransformAlong (relativeBaseMarked I) H.tower).cosupp
    j (fun v=>initialEmbedding q (sameIndexMap 1 q v))
    ((initialEmbedding q).strictMono.comp (strictMono_sameIndexMap 1 q)) hImage hValues
  have hResolution : IsGeoResolution (relativeNormalMarked I) T ↔ IsGeoResolution (relativeBaseMarked I) H.tower:=by
    constructor
    · intro h
      refine ⟨hBaseTest,?_⟩
      rw [hCos,h.2,preimage_empty]
    · intro h
      refine ⟨hSourceTest,?_⟩
      rw [←hImage,h.2,image_empty]
  exact ⟨V,hVc,hV,Q,hLift,hBaseCan,hBaseTest,
    hIso.length_eq.trans (hLift.length.trans (length_restrict ⊤ T)),hSquare,hBoundary,hCos,hImage,hValues,hMaximum,hResolution⟩

end
end Hironaka.HironakaActualRelativeNormalCanonicalHistory
