import Hironaka.Resolution.HironakaG1ProperNormalPhaseNative
import Hironaka.Resolution.HironakaActualOpenSectionRepresentative
import Hironaka.Resolution.HironakaActualNativeSectionNormalCrossings
import Hironaka.Resolution.HironakaActualSectionInitialValues

/-! Literal ORIGINAL input/test histories from ordinary upper normal TESTs.
WHOLE supported M0 transforms are retained; cylindrical current ideals are
never equated to them. Blueprint FIRST: hironaka-g1-proper-normal-original-test.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1ProperNormalOriginalTest
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealOperationsAlong.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealTowerTransport
  BlowupTowerIsomorphism ResolutionInvariantSpec HomogenizedIdealAlong StepOneValue
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact
  HironakaG1ProperCarrierNormalLocalClass HironakaG1ProperNormalPhaseNative
  HironakaG1ChosenCommonContactClassData HironakaG8LocalHistory
  HironakaG8LocalContactStage
  HironakaActualOpenSectionRepresentative HironakaActualOpenZeroSectionDifferentials
  HironakaActualWeightedNormalAmbientDerivatives HironakaActualNativeSectionInitialBar
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionOrderHistory
  HironakaActualNativeInvariantDomain HironakaActualNativeSectionNormalCrossings
  HironakaSmoothSubmersionOrderedChoiceImageTrace HironakaActualCentreJointJets
  HironakaRelativeNormalIdeal HironakaActualSectionBoundaryGeometry
  GermIdealPullbackCalculus RelativePrincipalizationSpan InvertibleIdealQuotient
  RestrictLeCalculus DerivativeIdeal NormalCrossings GermIdealOrder

/-- True section support, retaining the WHOLE original padding ideal, E and d. -/
def supportedNormalMarked {n : ℕ} {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U) :
    MarkedIdeal (n+1) (productOpen U) :=
  ⟨liftedCarrier Q.N,(properNormalMarked Q).E,(properNormalMarked Q).ideal,Q.d⟩

private theorem projection_section {n : ℕ} (U : Opens (ComplexModel n)) (x : U) :
    projection U (zeroSection U x)=x := by
  apply Subtype.ext
  exact tangentProjection_tangentInclusion n 1 x.val

private theorem padding_trace {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) :
    GermIdeal.pullback (m := n) (zeroSection U) (properNormalMarked Q).ideal=Q.ideal := by
  simpa only [properNormalMarked,iterDerivIdeal_zero] using
    entire_ambient_derivative_trace (U := U) hQ.isWellFormed.isCoherent
      (d := Q.d) (j := 0) (lt_of_lt_of_le Nat.zero_lt_one hQ.one_le_d)

private theorem projection_trace {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) :
    GermIdeal.pullback (m := n) (zeroSection U)
      (GermIdeal.pullback (m := n+1) (projection U) Q.ideal)=Q.ideal := by
  have he : projection U ∘ zeroSection U=id:=funext (projection_section U)
  rw [←coherent_pullback_comp (projection_contMDiff U) (zeroSection_contMDiff U)
    Q.ideal hQ.isWellFormed.isCoherent,he,BlowupControlledTransform.pullback_id hQ.isWellFormed.isCoherent]

/-- Actual trace/retraction produces both restricted inclusions and genuine
supported domain/class internally. No lower/current whole ideal is assumed. -/
theorem supported_normal_data {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) :
    RestrictEquiv (supportedNormalMarked Q) (sectionMarked Q) ∧
      IsInvDomain k (supportedNormalMarked Q) ∧
      LocWPEquiv (X := CMfd.of (n := n+1) (productOpen U)) (properNormalMarked Q) (supportedNormalMarked Q) := by
  let M:=supportedNormalMarked Q
  let S:=sectionMarked Q
  have hP:=properNormalMarked_isInvDomain Q hQ
  have hS : IsInvDomain k S:=section_projected_domain k Q.N Q.E Q.ideal Q.d hQ
  have hMI:=hP.isWellFormed.isCoherent
  have hSI:=isCoherent_pullback (projection_contMDiff U) hQ.isWellFormed.isCoherent
  have hA:=restrictEquiv_actual_open_section U Q.N M.E Q.d M.ideal
    (fun _ _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem hMI hf)
  have hB:=restrictEquiv_actual_open_section U Q.N M.E Q.d S.ideal
    (fun _ _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem hSI hf)
  have hr : GermIdeal.pullback (m := n+1) (zeroSection U∘projection U) M.ideal=
      GermIdeal.pullback (m := n+1) (zeroSection U∘projection U) S.ideal := by
    rw [coherent_pullback_comp (zeroSection_contMDiff U) (projection_contMDiff U) M.ideal hMI,
      coherent_pullback_comp (zeroSection_contMDiff U) (projection_contMDiff U) S.ideal hSI]
    change GermIdeal.pullback (m := n+1) (projection U)
        (GermIdeal.pullback (m := n) (zeroSection U) (properNormalMarked Q).ideal)=
      GermIdeal.pullback (m := n+1) (projection U)
        (GermIdeal.pullback (m := n) (zeroSection U) (GermIdeal.pullback (m := n+1) (projection U) Q.ideal))
    rw [padding_trace Q hQ,projection_trace Q hQ]
  have hRE : RestrictEquiv M S:=⟨rfl,rfl,rfl,
    RestrictLeCalculus.RestrictLe.trans hA.le (by rw [hr];exact hB.ge),
    RestrictLeCalculus.RestrictLe.trans hB.le (by rw [←hr];exact hA.ge)⟩
  have hLS : LocWPEquiv (X := CMfd.of (n := n+1) (productOpen U)) M S :=
    locEquiv_of_restrictEquiv_closed (κ := Kinds.wp) rfl hRE
      hS.isWellFormed.isClosedSubmanifold_N hMI hSI
  have hM : IsInvDomain k M:=isInvDomain_of_sameCarrier_cosupp
    (X := CMfd.of (n := n+1) (productOpen U)) M S hS hMI hQ.one_le_d rfl rfl hLS.cosupp_eq_base
  exact ⟨hRE,hM,(properNormalMarked_locWPEquiv_section Q hQ).trans hLS.symm⟩

/-- The ENTIRE initial native supported record is literal ORIGINAL Q,
with its original true mark and every ordered boundary occurrence. -/
theorem native_supported_input_record {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) :
    MarkedIdeal.pullback (nativeZeroSectionEquiv U)
      (nativePullback (Y := CMfd.of (n := n+1) (productOpen U))
        (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) (supportedNormalMarked Q))=Q := by
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ n) (zeroPlane_regular U)
  have := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ n) (zeroPlane_regular U)
  have hM:=(supported_normal_data Q hQ).2.1
  have hTrace : HironakaSmoothSubmersionCoefficientIdeals.markedPullback (m := n)
      (zeroSection U) (supportedNormalMarked Q)=Q := by
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · ext x
      change (projection U (zeroSection U x)∈Q.N ∧
        actualJointNormalProjection n 1 (tangentInclusion n 1 x.val)=0) ↔ x∈Q.N
      rw [projection_section]
      simp
    · change (Q.E.map (projection U ⁻¹' ·)).map (zeroSection U ⁻¹' ·)=Q.E
      rw [List.map_map]
      change Q.E.map (fun H : Set U=>zeroSection U ⁻¹' (projection U ⁻¹' H))=Q.E
      have he : (fun H : Set U=>zeroSection U ⁻¹' (projection U ⁻¹' H))=id := by
        funext H
        ext x
        change projection U (zeroSection U x)∈H ↔ x∈H
        rw [projection_section]
      rw [he,List.map_id]
    · exact padding_trace Q hQ
    · rfl
  exact (whole_markedPullback_comp (SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ n) (zeroPlane_regular U))
    (nativeZeroSectionEquiv U).contMDiff (supportedNormalMarked Q) hM.isWellFormed.isCoherent).symm.trans hTrace

/-- The supported whole padding record has exactly the original order on
its carrier. In particular, source maximal order transfers with the true mark. -/
theorem supported_normal_maximal_order {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    (hMax : IsMaximalOrderAlong Q.N Q.ideal Q.d) :
    let M := supportedNormalMarked Q
    IsMaximalOrderAlong M.N M.ideal M.d := by
  let M := supportedNormalMarked Q
  have hM := (supported_normal_data Q hQ).2.1
  have hHol : ∀ x g, M.ideal.mem x g → HolomorphicAt (n + 1) g x := fun _ _ hg =>
    GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg
  change IsMaximalOrderAlong M.N M.ideal M.d
  intro x hx
  change x ∈ cosupport (n + 1) (liftedCarrier Q.N) M.ideal (Q.d + 1) at hx
  rw [HironakaActualSectionInitialValues.source_cosupport_eq_lifted Q.N M.ideal hHol,
    show GermIdeal.pullback (m := n) (zeroSection U) M.ideal = Q.ideal from padding_trace Q hQ] at hx
  exact hMax (projection U x) hx.1

private theorem plane_closed {n : ℕ} (U : Opens (ComplexModel n)) : IsClosed (zeroPlane U) :=
  (liftedCarrier_closed_submanifold
    (HomogenizedGlueingTower.isClosedSubmanifold_univ (n := n) (M := U))).1

/-- Literal ORIGINAL Q input and TEST/history/scalar factory. Whole current
identities concern M0, never the distinct cylindrical ambient P ideal. -/
theorem exists_literal_original_native_test_history {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n+1)} (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (hT : IsGeoTestTower (properNormalMarked Q) T) :
    ∃(C : Set Y)(hCc : IsClosed C)(hC : ∀y∈C,RegularAtDim (n := n+1) C y n)
      (N : BlowupTower (nativeManifold (Y := CMfd.of (n := n+1) (productOpen U))
          (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U))
        (nativeManifold (Y := Y) (Nat.le_succ n) C hC)),
      Lift (Nat.le_succ n) (zeroPlane U) (plane_closed U) (zeroPlane_regular U)
        (supportedNormalMarked Q).E T C hCc hC N ∧
      IsGeoTestTower (nativePullback (Y := CMfd.of (n := n+1) (productOpen U))
        (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) (supportedNormalMarked Q)) N ∧
      geoTransformAlong (nativePullback (Y := CMfd.of (n := n+1) (productOpen U))
          (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) (supportedNormalMarked Q)) N=
        nativePullback (Y := Y) (Nat.le_succ n) C hC (geoTransformAlong (supportedNormalMarked Q) T) ∧
      let H:=transport (nativeZeroSectionEquiv U) N
      let j : H.target → Y:=fun z=>(H.back z).val
      H.tower.length=T.length ∧ IsGeoTestTower Q H.tower ∧
        (∀z,T.proj (j z)=zeroSection U (H.tower.proj z)) ∧
        (geoTransformAlong Q H.tower).E=(geoTransformAlong (properNormalMarked Q) T).E.map (j ⁻¹' ·) ∧
        (geoTransformAlong Q H.tower).cosupp=j ⁻¹' (geoTransformAlong (properNormalMarked Q) T).cosupp ∧
        j '' (geoTransformAlong Q H.tower).cosupp=(geoTransformAlong (properNormalMarked Q) T).cosupp ∧
        (IsGeoResolution (properNormalMarked Q) T ↔ IsGeoResolution Q H.tower) := by
  let M:=supportedNormalMarked Q
  obtain ⟨_hRE,hM,hPM⟩:=supported_normal_data Q hQ
  have hMT:=(hPM.wEquiv.2 T).1.mp hT
  have hCosPM:=(hPM.wEquiv.2 T).2 hT
  have hSupport : M.N⊆zeroPlane U:=fun _ hz=>⟨mem_univ _,hz.2⟩
  have hTrans : IsTransverse (n+1) (zeroPlane U) M.E := by
    change IsTransverse (n+1) (liftedCarrier (univ : Set U)) (Q.E.map (projection U ⁻¹' ·))
    exact isTransverse_liftedCarrier (univ : Set U) Q.E
      (SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hQ.isWellFormed.isSNCDivisor)
  obtain ⟨C,hCc,hC,N,hLift,_hOldNativeTest,_hLen,_hSquare,_hTrans,_hWhole,_hOldInput⟩:=
    exists_upper_native_test_history Q hQ T hT
  have hhol : ∀x f,M.ideal.mem x f→HolomorphicAt (n+1) f x:=
    fun _ _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hf
  have hNativeTest:=HironakaActualNativeSectionNormalCrossings.Lift.native_test hLift
    (Nat.succ_pos n) hM.isWellFormed.isSNCDivisor hTrans M rfl hSupport hhol hMT
  let NB:=nativePullback (Y := CMfd.of (n := n+1) (productOpen U))
    (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) M
  have hNB : IsInvDomain k NB:=isInvDomain_nativePullback
    (X := CMfd.of (n := n+1) (productOpen U)) (W := zeroPlane U)
    (Nat.succ_pos n) (Nat.le_succ n) (zeroPlane_regular U) M hM hSupport hTrans
  have hNativeWhole:=hLift.whole_records (Nat.succ_pos n) hM.isWellFormed.isSNCDivisor hTrans M rfl hSupport hhol
  let H:=transport (nativeZeroSectionEquiv U) N
  let j : H.target → Y:=fun z=>(H.back z).val
  have hIso:=transport_isTowerIso (nativeZeroSectionEquiv U) N
  have hInput : MarkedIdeal.pullback (nativeZeroSectionEquiv U) NB=Q:=native_supported_input_record Q hQ
  have hBaseTest : IsGeoTestTower Q H.tower := by
    have h := (BlowupTowerIsomorphism.IsTowerIso.isGeoTestTower_iff (nativeZeroSectionEquiv U)
      hNB.isWellFormed.isClosedSubmanifold_N hNB.isWellFormed.isCoherent hIso).mpr hNativeTest
    simpa only [hInput] using h
  have hBaseWhole : geoTransformAlong Q H.tower=MarkedIdeal.pullback H.back (geoTransformAlong NB N) := by
    have h:=BlowupTowerIsomorphism.IsTowerIso.geoTransformAlong_eq (nativeZeroSectionEquiv U)
      hNB.isWellFormed.isClosedSubmanifold_N hNB.isWellFormed.isCoherent hIso hNativeTest
    simpa only [hInput] using h
  have hNativeCos:=HironakaActualNativeSectionOrderHistory.Lift.current_cosupport hLift
    (Nat.succ_pos n) hM.isWellFormed.isSNCDivisor hTrans M rfl hSupport hhol
  have hCurrentNB:=InvDomainTowerAlong.isInvDomain_geoTransformAlong hNB N hNativeTest
  have hBaseCos : (geoTransformAlong Q H.tower).cosupp=H.back ⁻¹' (geoTransformAlong NB N).cosupp := by
    rw [hBaseWhole,cosupp_pullback_eq hCurrentNB.isWellFormed.isCoherent]
  have hCos : (geoTransformAlong Q H.tower).cosupp=j ⁻¹' (geoTransformAlong (properNormalMarked Q) T).cosupp := by
    rw [hBaseCos,hNativeCos,←hCosPM]
    rfl
  have hPE : (geoTransformAlong (properNormalMarked Q) T).E=(geoTransformAlong M T).E:=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪 := properNormalMarked Q) (𝔫 := M) rfl T
  have hBoundary : (geoTransformAlong Q H.tower).E=(geoTransformAlong (properNormalMarked Q) T).E.map (j ⁻¹' ·) := by
    have h1:=congrArg (fun A : MarkedIdeal n H.target=>A.E) hBaseWhole
    have h2:=congrArg (fun A : MarkedIdeal n (nativeManifold (Y := Y) (Nat.le_succ n) C hC)=>A.E) hNativeWhole
    change (geoTransformAlong Q H.tower).E=(geoTransformAlong NB N).E.map (H.back ⁻¹' ·) at h1
    change (geoTransformAlong NB N).E=(geoTransformAlong M T).E.map ((Subtype.val : C → Y) ⁻¹' ·) at h2
    rw [h2,←hPE] at h1
    simpa only [j,List.map_map,Function.comp_def,preimage_preimage] using h1
  have hCurrentSupport : (geoTransformAlong M T).N⊆C:=
    HironakaActualNativeSectionOrderHistory.Lift.current_carrier_subset
      (X := CMfd.of (n := n+1) (productOpen U)) (Y := Y) hLift M hSupport
  have hImage : j '' (geoTransformAlong Q H.tower).cosupp=(geoTransformAlong (properNormalMarked Q) T).cosupp := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact (Set.ext_iff.mp hCos z).mp hz
    · intro hy
      have hyM : y∈(geoTransformAlong M T).cosupp:=hCosPM ▸ hy
      let p : nativeManifold (Y := Y) (Nat.le_succ n) C hC:=⟨y,hCurrentSupport hyM.1⟩
      let z : H.target:=H.back.symm p
      have hj : j z=y:=by simp only [j,z,H.back.apply_symm_apply,p]
      refine ⟨z,?_,hj⟩
      rw [hCos]
      change j z∈(geoTransformAlong (properNormalMarked Q) T).cosupp
      rwa [hj]
  have hResolved : IsGeoResolution (properNormalMarked Q) T ↔ IsGeoResolution Q H.tower := by
    constructor
    · intro h
      exact ⟨hBaseTest,by rw [hCos,h.2,preimage_empty]⟩
    · intro h
      exact ⟨hT,by rw [←hImage,h.2,image_empty]⟩
  refine ⟨C,hCc,hC,N,hLift,hNativeTest,hNativeWhole,?_,hBaseTest,?_,hBoundary,hCos,hImage,hResolved⟩
  · exact (length_transport (nativeZeroSectionEquiv U) N).trans hLift.length
  · intro z
    exact (hLift.square (H.back z)).trans
      (congrArg Subtype.val (proj_transport (nativeZeroSectionEquiv U) N z)).symm

end
end Hironaka.HironakaG1ProperNormalOriginalTest
