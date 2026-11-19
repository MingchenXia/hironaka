import Hironaka.Resolution.HironakaActualAdaptedContactDerivation
import Hironaka.Resolution.HironakaActualWeightedNormalHomogenizedDerivatives
import Hironaka.Resolution.HironakaHolomorphicJetRankLoci
import Hironaka.Invariant.CompanionReduction

/-! Every genuine ambient derivative of the ORIGINAL bar has its entire
original zero-section trace, via actual source contact/Euler recovery.
Blueprint: hironaka-actual-weighted-normal-bar-derivatives-20261102.tex. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaActualWeightedNormalBarDerivatives
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
  DerivativeIdeal IdealOrderArithmetic IdealWeightPowers RelativePrincipalizationSpan
  GermIdealPullbackCalculus InvertibleIdealQuotient HomogenizedGlueing HomogenizedEquivalence
  CoefficientIdeal MaximalContact GermIdealOrder HironakaSmoothSubmersionGermIdealColon
  HironakaActualAdaptedContactDerivation HironakaActualHomogenizedTangentStability
  HironakaActualEulerContactPowerRecovery HironakaActualWeightedNormalHomogenizedDerivatives
  HironakaActualWeightedNormalAmbientDerivatives HironakaActualOpenZeroSectionDifferentials
  HironakaActualRelativeNormalGeometry HironakaActualWeightedNormalPadding
  HironakaActualCoherentWeightedCoefficientMarked HironakaRelativeNormalIdeal RestrictedIdealExtension
  HironakaActualWeightedHSNormalInput HironakaActualOriginalInitialHSPhase
  HironakaActualHistoricalHSMarkedDomain HironakaActualGeometricCurrentNeighborhoodHS
  HironakaActualRelativeNormalJetDivision HironakaActualNormalZeroAnalyticSaturation
  HironakaActualFormalInitialDiagram HironakaRelativeNormalMonomialBasis
  HironakaActualCoefficientPresentationCentrePower MarkedIdeals
  HironakaActualWeightedCoefficientCompression HironakaActualWeightedHSNormalRecodingInput
  DerivativeIdealAlong HomogenizedIdealAlong HironakaSmoothSubmersionCoefficientIdeals

section Ambient
variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- The literal ORIGINAL C(H(I,d),d), with every coefficient exponent. -/
def barIdeal (I : GermIdeal n X) (d : ℕ) : GermIdeal n X:=
  finSumIdeal (fun i=>idealPow (iterDerivIdeal (HomogenizedIdeal.homogenizedIdeal I d) i)
    (sumExp (fun j=>d-j) d i)) d

private theorem bar_coherent {I : GermIdeal n X} (hI : I.IsCoherent) (d : ℕ) :
    (barIdeal I d).IsCoherent:=isCoherent_finSumIdeal
  (fun i=>isCoherent_idealPow (isCoherent_iterDerivIdeal (isCoherent_homogenizedIdeal hI d) i) _) d

/-- A TRUE original tangent function internally supplies a true power in the
ORIGINAL bar, via its actual last homogenization and first coefficient terms. -/
theorem tangent_function_power_mem_bar {I : GermIdeal n X} (hI : I.IsCoherent)
    {d : ℕ} (hd : 0<d) {x : X} {u : X→ℂ} (hu : (iterDerivIdeal I (d-1)).mem x u) :
    (barIdeal I d).mem x (fun y=>u y^(d*sumExp (fun j=>d-j) d 0)):=by
  let T:=iterDerivIdeal I (d-1)
  have hT : T.IsCoherent:=isCoherent_iterDerivIdeal hI (d-1)
  have huh : HolomorphicAt n u x:=GermIdeal.IsCoherent.holomorphicAt_mem hT hu
  have hUPow : ((iterDerivIdeal I (d-1)).mul (idealPow T (d-1))).mem x (fun y=>u y^d):=by
    have hMul:=HomogenizedIdeal.mul_mem_mul hu (HomogenizedIdeal.pow_mem_idealPow hu huh (d-1))
      (huh.mul (CompanionReduction.holomorphicAt_pow_of huh (d-1)))
    convert hMul using 1
    funext y
    calc
      u y^d=u y^((d-1)+1):=by congr 1;omega
      _=u y*u y^(d-1):=by rw [pow_succ];ring
  have hH : (HomogenizedIdeal.homogenizedIdeal I d).mem x (fun y=>u y^d):=
    isInSpanAt_self ⟨d-1,by omega,hUPow⟩ (CompanionReduction.holomorphicAt_pow_of huh d)
  change IsInSpanAt (n:=n)
    (fun f=>∃i,i<d ∧ (idealPow (iterDerivIdeal (HomogenizedIdeal.homogenizedIdeal I d) i)
      (sumExp (fun j=>d-j) d i)).mem x f) x _
  have hFirst : (idealPow (iterDerivIdeal (HomogenizedIdeal.homogenizedIdeal I d) 0)
      (sumExp (fun j=>d-j) d 0)).mem x (fun y=>u y^(d*sumExp (fun j=>d-j) d 0)):=by
    simpa only [iterDerivIdeal_zero,←pow_mul] using
      HomogenizedIdeal.pow_mem_idealPow hH (CompanionReduction.holomorphicAt_pow_of huh d)
        (sumExp (fun j=>d-j) d 0)
  exact isInSpanAt_self ⟨0,hd,hFirst⟩ (CompanionReduction.holomorphicAt_pow_of huh _)

end Ambient

section Normal
variable {n : ℕ} {U : Opens (ComplexModel n)} {I : GermIdeal n U}

private theorem projection_section (x : U) : projection U (zeroSection U x)=x:=by
  apply Subtype.ext
  exact tangentProjection_tangentInclusion n 1 x.val

private theorem padding_coherent (hI : I.IsCoherent) (d : ℕ) :
    (normalPaddingIdeal I d).IsCoherent:=
  isCoherent_sumIdeal (isCoherent_pullback (projection_contMDiff U) hI)
    (isCoherent_finiteFunctionIdeal _ (fun _=>(normalCoordinate_mdifferentiable U).pow d))

private theorem projection_tangent_member (hI : I.IsCoherent) (d : ℕ)
    (x : U) (u : U→ℂ) (hu : (iterDerivIdeal I (d-1)).mem x u) :
    (iterDerivIdeal (normalPaddingIdeal I d) (d-1)).mem (zeroSection U x) (u ∘ projection U):=by
  have hT:=isCoherent_iterDerivIdeal hI (d-1)
  have huP : (iterDerivIdeal I (d-1)).mem (projection U (zeroSection U x)) u:=by
    rw [projection_section]
    exact hu
  have hcomp : HolomorphicAt (n+1) (u ∘ projection U) (zeroSection U x):=
    (GermIdeal.IsCoherent.holomorphicAt_mem hT huP).comp_contMDiff
      (Eventually.of_forall fun _=>(projection_contMDiff U).contMDiffAt)
  have hPB : (GermIdeal.pullback (m:=n+1) (projection U) (iterDerivIdeal I (d-1))).mem
      (zeroSection U x) (u ∘ projection U):=
    GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨u,huP,rfl⟩ hcomp)
  have hProj:=HironakaSmoothSubmersionDerivativeEquality.iterDerivIdeal_pullback_eq
    (fun y=>(HironakaActualSectionBoundaryGeometry.projection_isSubmersion (U:=U)).isSubmersionAt y)
    (fun y=>(projection_contMDiff U).mdifferentiable (by simp) y)
    (fun _ _ h=>GermIdeal.IsCoherent.holomorphicAt_mem hI h) (d-1)
  have hPI:=isCoherent_pullback (projection_contMDiff U) hI
  have hLe : (GermIdeal.pullback (m:=n+1) (projection U) I).Le (normalPaddingIdeal I d):=
    le_sumIdeal_left hPI
  exact iterDerivIdeal_mono hLe (d-1) _ _ (by rwa [hProj])

private theorem upper_bar_product_trace (hI : I.IsCoherent) {d : ℕ} (hd : 0<d)
    (j : ℕ) (x : U) (u : U→ℂ) (hu : (iterDerivIdeal I (d-1)).mem x u)
    (F : productOpen U→ℂ)
    (hF : (iterDerivIdeal (barIdeal (normalPaddingIdeal I d) d) j).mem (zeroSection U x) F) :
    (barIdeal I d).mem x (fun y=>u y^j*F (zeroSection U y)):=by
  let J:=normalPaddingIdeal I d
  have hJ : J.IsCoherent:=padding_coherent hI d
  have hBJ:=bar_coherent hJ d
  have hTJ:=isCoherent_iterDerivIdeal hJ (d-1)
  have huUpper:=projection_tangent_member hI d x u hu
  have huUpperHol:=GermIdeal.IsCoherent.holomorphicAt_mem hTJ huUpper
  have hFHol:=GermIdeal.IsCoherent.holomorphicAt_mem (isCoherent_iterDerivIdeal hBJ j) hF
  have hAbsorb:=iterDeriv_tangent_absorption hBJ hTJ
    (coefficient_homogenized_tangent_stability hJ hd) j
  have hMul : ((iterDerivIdeal (barIdeal J d) j).mul
      (idealPow (iterDerivIdeal J (d-1)) j)).mem (zeroSection U x)
        (fun z=>F z*(u (projection U z))^j):=
    HomogenizedIdeal.mul_mem_mul hF (HomogenizedIdeal.pow_mem_idealPow huUpper huUpperHol j)
      (hFHol.mul (CompanionReduction.holomorphicAt_pow_of huUpperHol j))
  have hUpper:=hAbsorb (zeroSection U x) _ hMul
  have hUpperHol:=GermIdeal.IsCoherent.holomorphicAt_mem hBJ hUpper
  have hPB : (GermIdeal.pullback (m:=n) (zeroSection U) (barIdeal J d)).mem x
      ((fun z=>F z*(u (projection U z))^j) ∘ zeroSection U):=
    GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨_,hUpper,rfl⟩
      (hUpperHol.comp_contMDiff (Eventually.of_forall fun _=>(zeroSection_contMDiff U).contMDiffAt)))
  have hTrace : GermIdeal.pullback (m:=n) (zeroSection U) (barIdeal J d)=barIdeal I d:=
    normal_padding_coefficient_homogenized_trace hI d
  rw [hTrace] at hPB
  convert hPB using 1
  funext y
  simp only [Function.comp_apply,projection_section]
  ring

/-- EVERY actual upper ambient bar derivative has its actual original lower
derivative trace. Actual source maximal order produces contact where needed;
outside its cosupport the ORIGINAL tangent/bar are genuinely unit. -/
theorem normal_bar_derivative_member (hI : I.IsCoherent) {d : ℕ} (hd : 0<d)
    (hMax : IsMaximalOrder I d) (j : ℕ) (x : U) (F : productOpen U→ℂ)
    (hF : (iterDerivIdeal (barIdeal (normalPaddingIdeal I d) d) j).mem (zeroSection U x) F) :
    (iterDerivIdeal (barIdeal I d) j).mem x (F ∘ zeroSection U):=by
  have hBar:=bar_coherent hI d
  have hDBar:=isCoherent_iterDerivIdeal hBar j
  have hUpperBar:=bar_coherent (padding_coherent hI d) d
  have hFHol:=GermIdeal.IsCoherent.holomorphicAt_mem (isCoherent_iterDerivIdeal hUpperBar j) hF
  have hF0 : HolomorphicAt n (F ∘ zeroSection U) x:=
    hFHol.comp_contMDiff (Eventually.of_forall fun _=>(zeroSection_contMDiff U).contMDiffAt)
  have hHolI : ∀y f,I.mem y f→HolomorphicAt n f y:=
    fun _ _ h=>GermIdeal.IsCoherent.holomorphicAt_mem hI h
  have hT:=isCoherent_iterDerivIdeal hI (d-1)
  by_cases hx : x∈cosupport n univ I d
  · obtain ⟨V,u,hxV,hu⟩:=exists_isTangentDirection hI hHolI (show 1≤d by omega) hMax hx
    let Φ:=HironakaHolomorphicJetRankLoci.translationEquiv (chartAt (ComplexModel n) x x)
    have h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0:=sub_self _
    obtain ⟨hUh,hRec⟩:=actual_contact_adapted_power_recovery I hI d (show 1≤d by omega)
      V u hu x hxV hx Φ h0
    have huT:=hu.mem x hxV
    have hProduct:=upper_bar_product_trace hI hd j x u huT F hF
    have hProductHol:=GermIdeal.IsCoherent.holomorphicAt_mem hBar hProduct
    have hGermProduct : (adaptedGerm x Φ h0 u hUh)^j*adaptedGerm x Φ h0 (F ∘ zeroSection U) hF0∈
        adaptedIdeal (barIdeal I d) x Φ h0:=by
      have huFlat:=(holomorphic_adapted_iff x Φ h0 u).mpr hUh
      have hF0Flat:=(holomorphic_adapted_iff x Φ h0 (F ∘ zeroSection U)).mpr hF0
      have hEq : adaptedGerm x Φ h0 (fun y=>u y^j*F (zeroSection U y)) hProductHol=
          (adaptedGerm x Φ h0 u hUh)^j*adaptedGerm x Φ h0 (F ∘ zeroSection U) hF0:=by
        have hm:=HolGerm.mk_mul
          (fun z=>u ((chartAt (ComplexModel n) x).symm (Φ.invFun z))^j)
          (fun z=>F (zeroSection U ((chartAt (ComplexModel n) x).symm (Φ.invFun z))))
          (eventually_differentiableAt_pow huFlat j) hF0Flat
        rw [HolGerm.mk_pow] at hm
        exact hm
      rw [←hEq]
      exact Ideal.subset_span ⟨_,hProductHol,hProduct,rfl⟩
    have hRecovered:=hRec (barIdeal I d) (iterDerivIdeal I (d-1)) hBar hT
      (coefficient_homogenized_tangent_stability hI hd) huT
      (d*sumExp (fun k=>d-k) d 0) (tangent_function_power_mem_bar hI hd huT) j
      (adaptedGerm x Φ h0 (F ∘ zeroSection U) hF0) hGermProduct
    exact (mem_adaptedIdeal_iff _ hDBar x Φ h0 _ hF0).mp hRecovered
  · have hxT : x∉(iterDerivIdeal I (d-1)).zeroLocus:=by
      rw [←OrderTaylor.cosupport_succ_eq_zeroLocus_iterDerivIdeal hHolI (d-1),
        show (d-1)+1=d by omega]
      exact hx
    obtain ⟨g,hg,hgx⟩:=CompanionReduction.exists_mem_ne_zero_of_notMem_zeroLocus hxT
    have hUnitT:=CompanionReduction.one_mem_of_apply_ne_zero hT hg hgx
    have hUnitBar : (barIdeal I d).mem x (fun _=>1):=by
      simpa only [one_pow] using tangent_function_power_mem_bar hI hd hUnitT
    have hUnitD:=le_iterDerivIdeal
      (fun _ _ h=>GermIdeal.IsCoherent.holomorphicAt_mem hBar h) j x _ hUnitBar
    apply HomogenizedIdeal.mem_of_isInSpanAt hDBar
    exact isInSpanAt_of_eq_mul hUnitD hF0 hF0 (Eventually.of_forall fun _=>by simp)

/-- ENTIRE actual ambient bar derivatives have the ORIGINAL zero-section
trace at EVERY order, with genuine source maximal order only. -/
theorem normal_bar_entire_derivative_trace (hI : I.IsCoherent) {d : ℕ} (hd : 0<d)
    (hMax : IsMaximalOrder I d) (j : ℕ) :
    GermIdeal.pullback (m:=n) (zeroSection U)
      (iterDerivIdeal (barIdeal (normalPaddingIdeal I d) d) j)=iterDerivIdeal (barIdeal I d) j:=by
  have hBJ:=bar_coherent (padding_coherent hI d) d
  have hBI:=bar_coherent hI d
  have hDBI:=isCoherent_iterDerivIdeal hBI j
  have hUpper : (GermIdeal.pullback (m:=n) (zeroSection U)
      (iterDerivIdeal (barIdeal (normalPaddingIdeal I d) d) j)).Le
        (iterDerivIdeal (barIdeal I d) j):=by
    intro x g hg
    apply HomogenizedIdeal.mem_of_isInSpanAt hDBI
    refine IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hg)
    rintro _ ⟨F,hF,rfl⟩
    have hMember:=normal_bar_derivative_member hI hd hMax j x F hF
    exact isInSpanAt_self hMember (GermIdeal.IsCoherent.holomorphicAt_mem hDBI hMember)
  have hLower:=HironakaSmoothPullbackDerivatives.iterDerivIdeal_pullback_le
    (fun y=>(zeroSection_contMDiff U).mdifferentiable (by simp) y)
    (fun _ _ h=>GermIdeal.IsCoherent.holomorphicAt_mem hBJ h) j
  have hTrace : GermIdeal.pullback (m:=n) (zeroSection U)
      (barIdeal (normalPaddingIdeal I d) d)=barIdeal I d:=
    normal_padding_coefficient_homogenized_trace hI d
  rw [hTrace] at hLower
  exact GermIdeal.ext (funext fun x=>funext fun g=>propext ⟨hUpper x g,hLower x g⟩)

/-- The further ORIGINAL coefficient of the bar has its ENTIRE original
trace, for every actual next mark (in particular the literal bar product mark). -/
theorem normal_further_coefficient_bar_trace (hI : I.IsCoherent) {d : ℕ} (hd : 0<d)
    (hMax : IsMaximalOrder I d) (m : ℕ) :
    GermIdeal.pullback (m:=n) (zeroSection U)
      (finSumIdeal (fun j=>idealPow (iterDerivIdeal (barIdeal (normalPaddingIdeal I d) d) j)
        (sumExp (fun k=>m-k) m j)) m)=
      finSumIdeal (fun j=>idealPow (iterDerivIdeal (barIdeal I d) j)
        (sumExp (fun k=>m-k) m j)) m:=by
  have hBJ:=bar_coherent (padding_coherent hI d) d
  rw [HironakaSmoothSubmersionCoefficientIdeals.pullback_finSumIdeal (zeroSection_contMDiff U)
    _ m (fun j _=>isCoherent_idealPow (isCoherent_iterDerivIdeal hBJ j) _)]
  apply finSumIdeal_congr
  intro j _hj
  rw [HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow (zeroSection_contMDiff U)
    (isCoherent_iterDerivIdeal hBJ j),normal_bar_entire_derivative_trace hI hd hMax j]

end Normal

section InitialPhase
variable {n : ℕ} {A : GermIdeal n (ComplexModel n)} {I : Ideal (HolGerm (ComplexModel n))}
  {G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)} {R : ℕ→ℕ}

private theorem presentation_functions_mdifferentiable
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R) (i) :
    MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ)
      (fun z : presentationOpen PHS=>PHS.representatives i z.val):=by
  intro z
  have h:=holomorphicAt_of_mdifferentiableOn PHS.isOpen_neighborhood
    (mdifferentiableOn_iff_differentiableOn.mpr (PHS.holomorphicOn i)) z.property
  exact (h.comp_contMDiff (Eventually.of_forall fun _=>
    (contMDiff_subtype_val (U:=presentationOpen PHS)).contMDiffAt)).mdifferentiableAt

/-- The literal phase retains the ENTIRE further ORIGINAL coefficient-bar
marked record, with exact full E and both successive product markings. -/
theorem phase_normal_further_bar_marked_record
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    (hw : ∀i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
      0<normalExponentDegree i.val)
    {M : Type u} (η : presentationOpen PHS→M) (E : List (Set M))
    (hMax : IsMaximalOrder (initialWeightedRecord PHS η E).ideal
      (initialWeightedRecord PHS η E).d) :
    markedPullback (m:=n) (zeroSection (presentationOpen PHS))
      (coeffMarkedAlong (coeffMarkedAlong (homMarkedAlong (phaseNormalMarked PHS η E))))=
      coeffMarkedAlong (coeffMarkedAlong (homMarkedAlong (initialWeightedRecord PHS η E))):=by
  let Q:=initialWeightedRecord PHS η E
  let J:=phaseNormalMarked PHS η E
  have hQ : Q.ideal.IsCoherent:=
    isCoherent_weightedFunctionIdeal _ _ (presentation_functions_mdifferentiable PHS)
  have hJ : J.ideal.IsCoherent:=padding_coherent hQ Q.d
  have hHQ:=isCoherent_homogenizedIdeal hQ Q.d
  have hHJ:=isCoherent_homogenizedIdeal hJ Q.d
  have hBQ:=bar_coherent hQ Q.d
  have hBJ:=bar_coherent hJ Q.d
  have hd : 0<Q.d:=weightedCommonMark_pos _ hw
  rw [homMarkedAlong_eq_homMarked (𝔪:=J) rfl (fun _ _ h=>GermIdeal.IsCoherent.holomorphicAt_mem hJ h),
    homMarkedAlong_eq_homMarked (𝔪:=Q) rfl (fun _ _ h=>GermIdeal.IsCoherent.holomorphicAt_mem hQ h),
    coeffMarkedAlong_eq_coeffMarked (𝔪:=homMarked J) rfl
      (fun _ _ h=>GermIdeal.IsCoherent.holomorphicAt_mem hHJ h),
    coeffMarkedAlong_eq_coeffMarked (𝔪:=homMarked Q) rfl
      (fun _ _ h=>GermIdeal.IsCoherent.holomorphicAt_mem hHQ h),
    coeffMarkedAlong_eq_coeffMarked (𝔪:=coeffMarked (homMarked J)) rfl
      (fun _ _ h=>GermIdeal.IsCoherent.holomorphicAt_mem hBJ h),
    coeffMarkedAlong_eq_coeffMarked (𝔪:=coeffMarked (homMarked Q)) rfl
      (fun _ _ h=>GermIdeal.IsCoherent.holomorphicAt_mem hBQ h)]
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_
    (normal_further_coefficient_bar_trace hQ hd hMax _) rfl
  change (markedPullback (m:=n) (zeroSection (presentationOpen PHS)) J).E=Q.E
  exact congrArg (fun K : MarkedIdeal n (presentationOpen PHS)=>K.E)
    (phase_normal_zero_section_record PHS hw η E)

end InitialPhase

end
end Hironaka.HironakaActualWeightedNormalBarDerivatives
