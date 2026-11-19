import Hironaka.Resolution.HironakaActualWeightedNormalHomogenizedDerivatives
import Hironaka.Invariant.CompanionRebase
import Hironaka.MarkedIdeal.GermIdealTotalTransform

/-! Actual native companions of the literal weighted normal padding.
The original vertical normal fibre derives every pulled-boundary exponent
zero. Whole actual companions/bar records are compared; no padded CAN or
raw marked-driver invariant equality is asserted. Blueprint FIRST:
`hironaka-actual-normal-padding-native-companion.tex`. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNormalPaddingNativeCompanion
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaActualWeightedNormalHomogenizedDerivatives HironakaActualWeightedNormalAmbientDerivatives
  HironakaActualWeightedNormalPadding HironakaActualRelativeNormalGeometry
  HironakaActualOpenZeroSectionDifferentials HironakaActualIntrinsicStableAmbientIso
  HironakaActualCentreJointJets HironakaRelativeNormalIdeal HironakaActualZeroCoordinateContactSeed
  HironakaActualCoherentWeightedCoefficientMarked GermIdealPullbackCalculus
  RelativePrincipalizationSpan RestrictedIdealExtension RestrictedIdealQuotient
  InvertibleIdealQuotient IdealWeightPowers GermIdealOrder DivisorExponent DivisorExponentAlong
  MonomialPartAlong CompanionRebase CompanionReductionAlong MarkedIdeals MarkedIdeals.MarkedIdeal
  HomogenizedIdealAlong CoefficientIdealRestriction HomogenizedGlueing DerivativeIdeal
  HironakaSmoothSubmersionOrderedChoiceImageTrace HironakaSmoothSubmersionRelativeGeometry
  HironakaSmoothSubmersionCoefficientIdeals HironakaActualSectionBoundaryGeometry
  ResolutionInvariantSpec BlowupTowers StepOneValue

variable {n : ℕ} {U : Opens (ComplexModel n)}

private theorem padding_coherent {I : GermIdeal n U} (hI : I.IsCoherent) (d : ℕ) :
    (normalPaddingIdeal I d).IsCoherent :=
  isCoherent_sumIdeal (isCoherent_pullback (projection_contMDiff U) hI)
    (isCoherent_finiteFunctionIdeal _ (fun _=>(normalCoordinate_mdifferentiable U).pow d))

private def vertical (z : productOpen U) (v : ComplexModel 1) : productOpen U :=
  ⟨join (projection U z).val v,by
    change tangentProjection n 1 (join (projection U z).val v)∈U
    rw [first_join]
    exact (projection U z).property⟩

private theorem vertical_continuous (z : productOpen U) : Continuous (vertical z) := by
  apply Continuous.subtype_mk
  change Continuous (fun v : ComplexModel 1=>
    tangentInclusion n 1 (projection U z).val+actualJointNormalInclusion n 1 v)
  exact continuous_const.add (actualJointNormalInclusion n 1).continuous

private theorem projection_vertical (z : productOpen U) (v : ComplexModel 1) :
    projection U (vertical z v)=projection U z := by
  apply Subtype.ext
  exact first_join _ _

private theorem vertical_center (z : productOpen U) :
    vertical z (actualJointNormalProjection n 1 z.val)=z := by
  apply Subtype.ext
  exact join_projections z.val

private theorem normal_vertical (z : productOpen U) (v : ComplexModel 1) :
    relativeNormalCoordinate U (vertical z v)=v 0 := by
  change actualJointNormalProjection n 1 (join (projection U z).val v) 0-0=v 0
  rw [second_join,sub_zero]

private theorem normal_power_member {I : GermIdeal n U} (d : ℕ) (z : productOpen U) :
    (normalPaddingIdeal I d).mem z (fun w=>relativeNormalCoordinate U w^d) :=
  le_sumIdeal_right (isCoherent_finiteFunctionIdeal _
    (fun _=>(normalCoordinate_mdifferentiable U).pow d)) z _
      (isInSpanAt_self ⟨(),rfl⟩
        (Eventually.of_forall fun w=>(normalCoordinate_mdifferentiable U).pow d w))

/-- Actual vertical normal fibres force the SAME native exponent zero along
EVERY closed pulled boundary, for EVERY product point. No monomial premise. -/
theorem normal_padding_divExpAlong_eq_zero {I : GermIdeal n U}
    (hI : I.IsCoherent) (d : ℕ) (H : Set U) (hH : IsClosed H) (z : productOpen U) :
    divExpAlong (n+1) univ (normalPaddingIdeal I d) (projection U ⁻¹' H) z=0 := by
  rw [divExpAlong_univ]
  have hJ := padding_coherent hI d
  have hHol : ∀w f,(normalPaddingIdeal I d).mem w f→HolomorphicAt (n+1) f w :=
    fun _ _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem hJ hf
  by_cases hz : z∈projection U ⁻¹' H
  · have hNot : ¬IsDivNear (n+1) (normalPaddingIdeal I d) (projection U ⁻¹' H) 1 z := by
      intro hDiv
      let v₀ := actualJointNormalProjection n 1 z.val
      have ht : Tendsto (vertical z) (𝓝 v₀) (𝓝 z) := by
        simpa only [v₀,vertical_center] using (vertical_continuous z).tendsto v₀
      have hZero : ∀ᶠv in 𝓝 v₀,(v 0)^d=0 := by
        filter_upwards [ht.eventually hDiv] with v hv
        have hvH : vertical z v∈projection U ⁻¹' H := by
          change projection U (vertical z v)∈H
          rw [projection_vertical]
          exact hz
        have hPow := (vanishesToOrderOn_one_iff (mem_univ (vertical z v))
          (Eventually.of_forall fun w=>(normalCoordinate_mdifferentiable U).pow d w)).mp
            ((hv hvH).2 _ (normal_power_member d (vertical z v)))
        change relativeNormalCoordinate U (vertical z v)^d=0 at hPow
        simpa only [normal_vertical] using hPow
      have hNonzero : ∃ᶠv in 𝓝 v₀,v≠(0 : ComplexModel 1) := by
        simpa only [mem_compl_iff,mem_singleton_iff] using
          (mem_closure_iff_frequently.mp (dense_compl_singleton (0 : ComplexModel 1) v₀))
      obtain ⟨v,hv,hvZero⟩ := (hNonzero.and_eventually hZero).exists
      have hv0 : v 0≠0 := by
        intro h
        apply hv
        ext i
        have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
        simpa only [hi,WithLp.ofLp_zero,Pi.zero_apply] using h
      exact pow_ne_zero d hv0 hvZero
    by_contra hne
    exact hNot ((isDivNear_divExp hHol z).mono (Nat.one_le_iff_ne_zero.mpr hne))
  · have hClosed := hH.preimage (projection_contMDiff U).continuous
    have hNone : ¬∃e,¬IsDivNear (n+1) (normalPaddingIdeal I d) (projection U ⁻¹' H) (e+1) z := by
      rintro ⟨e,he⟩
      exact he (isDivNear_of_notMem hClosed hz (e+1))
    simp only [divExp,dif_neg hNone]

/-- Literal normal padding of an ORIGINAL whole record, with every source
boundary position and original mark retained. -/
def normalMarked (Q : MarkedIdeal n U) : MarkedIdeal (n+1) (productOpen U) :=
  ⟨univ,Q.E.map (projection U ⁻¹' ·),normalPaddingIdeal Q.ideal Q.d,Q.d⟩

/-- The genuine ORIGINAL source domain internally supplies the actual padded domain. -/
theorem normalMarked_original_domain (Q : MarkedIdeal n U)
    (hQ : IsInvDomain n Q) (hN : Q.N=univ) :
    IsInvDomain (n+1) (normalMarked Q) := by
  have hD := isInvDomain_markedPullback_submersion (X:=CMfd.of (n:=n) U)
    (Y:=CMfd.of (n:=n+1) (productOpen U)) (projection_isSubmersion (U:=U)) Q hQ
  have he : n+((n+1)-n)=n+1 := by omega
  rw [he] at hD
  have hDN : (HironakaSmoothSubmersionCoefficientIdeals.markedPullback (m:=n+1) (projection U) Q).N=univ := by
    change projection U ⁻¹' Q.N=univ
    rw [hN,preimage_univ]
  have hReg : IsClosedSubmanifold (n+1) (univ : Set (productOpen U)) := by
    simpa only [hDN] using hD.isWellFormed.isClosedSubmanifold_N
  have hTrans : NormalCrossings.IsTransverse (n+1) (univ : Set (productOpen U))
      (Q.E.map (projection U ⁻¹' ·)) := by
    have hT := hD.isWellFormed.isTransverse
    change NormalCrossings.IsTransverse (n+1) (projection U ⁻¹' Q.N)
      (Q.E.map (projection U ⁻¹' ·)) at hT
    rw [hN,preimage_univ] at hT
    exact hT
  have hDim : DimLE (n+1) (univ : Set (productOpen U)) (n+1) := by
    simpa only [hDN] using hD.dimLE
  refine ⟨⟨hReg,padding_coherent hQ.isWellFormed.isCoherent Q.d,
    hD.isWellFormed.isSNCDivisor,hTrans⟩,hDim,hD.one_le_d,?_⟩
  intro z _hz
  have hzD : z∈(HironakaSmoothSubmersionCoefficientIdeals.markedPullback (m:=n+1) (projection U) Q).N := by
    rw [hDN]
    exact mem_univ z
  obtain ⟨f,hf,hfreq⟩ := hD.isNonzeroAlongAt z hzD
  refine ⟨f,le_sumIdeal_left
    (isCoherent_pullback (projection_contMDiff U) hQ.isWellFormed.isCoherent) z f hf,?_⟩
  simpa only [normalMarked,hDN] using hfreq

/-- ALL actual pulled boundary positions have unit monomial part; therefore
the actual native companion is the ENTIRE original padded record. -/
theorem normalMarked_companion_eq (Q : MarkedIdeal n U) (hQ : IsInvDomain n Q) :
    companionOf (n+1) (M:=CMfd.of (n:=n+1) (productOpen U)) (normalMarked Q) Q.d=
      normalMarked Q := by
  let J := normalMarked Q
  have hJI := padding_coherent hQ.isWellFormed.isCoherent Q.d
  have hOne (z : productOpen U) :
      (monomialPartAlong (n+1) univ J.ideal J.E).mem z (fun _=>1) := by
    refine ⟨holomorphicAt_const 1,fun i _ _=>?_⟩
    have hi : J.E.get i∈Q.E.map (projection U ⁻¹' ·) := List.get_mem J.E i
    obtain ⟨H,hHE,hH⟩ := List.mem_map.mp hi
    rw [← hH]
    change IsInSpanOnAt (n:=n+1) univ
      ((idealPow (vanishingIdeal (n:=n+1) (projection U ⁻¹' H))
        (divExpAlong (n+1) univ (normalPaddingIdeal Q.ideal Q.d) (projection U ⁻¹' H) z)).mem z) z (fun _=>1)
    rw [normal_padding_divExpAlong_eq_zero hQ.isWellFormed.isCoherent Q.d H
      (hQ.isWellFormed.isSNCDivisor.1 H hHE) z,idealPow_zero]
    exact IsInSpanAt.restrict (isInSpanAt_self (holomorphicAt_const 1) (holomorphicAt_const 1))
  have hNonmono : nonmonomialPartAlong (n+1) univ J.ideal J.E=J.ideal := by
    ext z g
    constructor
    · intro hg
      have h := hg.2 (fun _=>1) (hOne z)
      obtain ⟨k,s,a,hs,ha,heq⟩ := h.2
      apply GermIdealTotalTransform.mem_of_isInSpanAt_mem hJI
      refine ⟨hg.1,k,s,a,hs,ha,?_⟩
      filter_upwards [heq] with y hy
      simpa only [one_mul] using hy (mem_univ y)
    · intro hg
      exact ⟨GermIdeal.IsCoherent.holomorphicAt_mem hJI hg,
        fun a ha=>restrictOn_mul_left ha.1 (le_restrictOn hJI z g hg)⟩
  change companionAlong (X:=CMfd.of (n:=n+1) (productOpen U)) univ J.E (nonmonomialPartAlong (n+1) univ J.ideal J.E)
    (monomialPartAlong (n+1) univ J.ideal J.E) Q.d Q.d=J
  simp only [companionAlong,lt_self_iff_false,if_false,hNonmono]
  rfl

private theorem section_projection (x : U) : projection U (zeroSection U x)=x := by
  apply Subtype.ext
  exact tangentProjection_tangentInclusion n 1 x.val

private theorem section_boundary (E : List (Set U)) :
    (E.map (projection U ⁻¹' ·)).map (zeroSection U ⁻¹' ·)=E := by
  rw [List.map_map]
  change E.map (fun H : Set U=>zeroSection U ⁻¹' (projection U ⁻¹' H))=E
  have h : (fun H : Set U=>zeroSection U ⁻¹' (projection U ⁻¹' H))=id := by
    funext H
    ext x
    change projection U (zeroSection U x)∈H ↔ x∈H
    rw [section_projection]
  rw [h,List.map_id]

/-- The entire zero-section record of the ACTUAL native padded companion is
the SAME original source record, without a target comparison premise. -/
theorem normalMarked_companion_zero_section_record (Q : MarkedIdeal n U)
    (hQ : IsInvDomain n Q) (hN : Q.N=univ) :
    markedPullback (m:=n) (zeroSection U)
      (companionOf (n+1) (M:=CMfd.of (n:=n+1) (productOpen U)) (normalMarked Q) Q.d)=Q := by
  rw [normalMarked_companion_eq Q hQ]
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ (section_boundary Q.E) ?_ rfl
  · change zeroSection U ⁻¹' univ=Q.N
    rw [preimage_univ,hN]
  · change GermIdeal.pullback (m:=n) (zeroSection U) (normalPaddingIdeal Q.ideal Q.d)=Q.ideal
    have hd : 0<Q.d := lt_of_lt_of_le Nat.zero_lt_one hQ.one_le_d
    have hTrace := entire_ambient_derivative_trace (U:=U) hQ.isWellFormed.isCoherent
      (d:=Q.d) (j:=0) hd
    simpa only [iterDerivIdeal_zero] using hTrace

/-- The ACTUAL native companion's full bar recoding has exactly the SAME
source full bar record, retaining every boundary and the true product mark.
This is not an equality of raw marked-driver values or canonical histories. -/
theorem normalMarked_companion_bar_zero_section_record (Q : MarkedIdeal n U)
    (hQ : IsInvDomain n Q) (hN : Q.N=univ) :
    markedPullback (m:=n) (zeroSection U)
      (barMarked (X:=CMfd.of (n:=n+1) (productOpen U)) (companionOf (n+1) (M:=CMfd.of (n:=n+1) (productOpen U)) (normalMarked Q) Q.d))=
        barMarked (X:=CMfd.of (n:=n) U) Q := by
  rw [normalMarked_companion_eq Q hQ]
  have hI := hQ.isWellFormed.isCoherent
  have hJ := padding_coherent hI Q.d
  have hHI := HomogenizedGlueing.isCoherent_homogenizedIdeal hI Q.d
  have hHJ := HomogenizedGlueing.isCoherent_homogenizedIdeal hJ Q.d
  change markedPullback (m:=n) (zeroSection U)
    (coeffMarkedAlong (homMarkedAlong (normalMarked Q)))=coeffMarkedAlong (homMarkedAlong Q)
  rw [homMarkedAlong_eq_homMarked rfl (fun _ _ h=>GermIdeal.IsCoherent.holomorphicAt_mem hJ h),
    homMarkedAlong_eq_homMarked hN (fun _ _ h=>GermIdeal.IsCoherent.holomorphicAt_mem hI h),
    coeffMarkedAlong_eq_coeffMarked rfl (fun _ _ h=>GermIdeal.IsCoherent.holomorphicAt_mem hHJ h),
    coeffMarkedAlong_eq_coeffMarked (𝔪:=HomogenizedEquivalence.homMarked Q) hN
      (fun _ _ h=>GermIdeal.IsCoherent.holomorphicAt_mem hHI h)]
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ (section_boundary Q.E)
    (normal_padding_coefficient_homogenized_trace hI Q.d) rfl
  change zeroSection U ⁻¹' univ=Q.N
  rw [preimage_univ,hN]

end
end Hironaka.HironakaActualNormalPaddingNativeCompanion
