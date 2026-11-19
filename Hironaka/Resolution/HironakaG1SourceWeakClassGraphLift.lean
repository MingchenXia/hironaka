import Hironaka.Resolution.HironakaG1SeparateCarrierMemberCut
import Hironaka.Resolution.HironakaG1NormalSelectorGraph
import Hironaka.Resolution.HironakaG1ProperNormalOriginalTest
import Hironaka.Resolution.HironakaG11PresLineStable
import Hironaka.Resolution.HironakaG1ProperCarrierNormalLocalClass
import Hironaka.Resolution.HironakaG8LocalTransport

/-! Lifting the source weak test class to actual section-supported records. -/
set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1SourceWeakClassGraphLift

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan GermIdealPullbackCalculus MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism BlowupTowers ResolutionInvariantSpec
  HironakaActualProjectionTestRecord HironakaActualOpenZeroSectionDifferentials
  HironakaActualIntrinsicStableAmbientIso HironakaActualCentreJointJets HironakaRelativeNormalIdeal
  HironakaG8LocalStable HironakaG8LocalHistory HironakaG8LocalTransport HironakaG8ClassStepPerm
  HironakaG1SeparateCarrierMemberCut HironakaG8MemberLocalRelation HomogenizedIdealAlong
  HironakaActualNativeSectionInitialBar HironakaG1ProperCarrierNormalLocalClass
  MarkedIdealOperationsAlong.MarkedIdeal CoefficientIdealRestriction
  HironakaActualSectionBoundaryGeometry HironakaActualSectionMemberRestriction
  HironakaActualOpenSectionRepresentative HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionOrderedChoiceImageTrace
  DerivativeIdealAlong DerivativeIdealAlongCoherent IdealWeightPowers CoefficientIdeal HomogenizedGlueing
  HironakaG8LocalContactStage HironakaG8CoefficientBoundaryLocal RestrictLeCalculus
  HironakaG8ClassStepCut HironakaG1ProperCarrierNormalDerivativeTrace

open scoped ProductComplexManifold

variable {n k l : ℕ} {U : Opens (ComplexModel n)}

private abbrev base (U : Opens (ComplexModel n)) := CMfd.of (n := n) U
private abbrev ambient (U : Opens (ComplexModel n)) := CMfd.of (n := n + 1) (productOpen U)

private def splitLine (U : Opens (ComplexModel n)) (z : productOpen U) :
    projectionAmbient (base U) :=
  (projection U z, actualJointNormalProjection n 1 z.val)

private def joinLine (U : Opens (ComplexModel n)) (p : projectionAmbient (base U)) : productOpen U :=
  ⟨join p.1.val p.2, by
    change tangentProjection n 1 (join _ _) ∈ U
    rw [first_join]
    exact p.1.property⟩

/-- The actual open normal chart is the model for the ordinary line
projection test, with its real horizontal divisor. -/
def projectionLineDiffeo (U : Opens (ComplexModel n)) :
    productOpen U ≃ₘ⟮𝓘(ℂ, ComplexModel (n + 1)), 𝓘(ℂ, ComplexModel (n + 1))⟯ projectionAmbient (base U) where
  toEquiv := ⟨splitLine U, joinLine U,
    fun z => Subtype.ext (join_projections z.val),
    fun p => Prod.ext (Subtype.ext (first_join _ _)) (second_join _ _)⟩
  contMDiff_toFun := ProductComplexManifold.contMDiff_prodMk (n := n) (m := 1)
    (projection_contMDiff U) ((actualJointNormalProjection n 1).contMDiff.comp contMDiff_subtype_val)
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff (productOpen U) _).mp
    exact ((tangentInclusion n 1).contMDiff.comp
      (contMDiff_subtype_val.comp (ProductComplexManifold.contMDiff_fst (n := n) (m := 1)))).add
        ((actualJointNormalInclusion n 1).contMDiff.comp
          (ProductComplexManifold.contMDiff_snd (n := n) (m := 1)))

private def cylinder (P : MarkedIdeal n U) : MarkedIdeal (n + 1) (ambient U) :=
  ⟨projection U ⁻¹' P.N, P.E.map (projection U ⁻¹' ·),
    GermIdeal.pullback (m := n + 1) (projection U) P.ideal, P.d⟩

private theorem projectionTest_pullback_line (P : MarkedIdeal n U) (hI : P.ideal.IsCoherent) :
    MarkedIdeal.pullback (M := projectionAmbient (base U)) (M' := ambient U)
      (projectionLineDiffeo U) (projectionTest (X := base U) P) =
      { cylinder P with E := (cylinder P).E ++ [zeroPlane U] } := by
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · rfl
  · change ((P.E.map ((Prod.fst : projectionAmbient (base U) → U) ⁻¹' ·)) ++
      [horizontal (base U)]).map (projectionLineDiffeo U ⁻¹' ·) =
      P.E.map (projection U ⁻¹' ·) ++ [zeroPlane U]
    have hZ : projectionLineDiffeo U ⁻¹' horizontal (base U) = zeroPlane U := by
      ext z
      change actualJointNormalProjection n 1 z.val = 0 ↔ projection U z ∈ Set.univ ∧
        actualJointNormalProjection n 1 z.val = 0
      simp
    rw [List.map_append, List.map_map, List.map_singleton, hZ]
    rfl
  · have hp := ProductComplexManifold.contMDiff_fst (n := n) (m := 1)
      (X := U) (Y := ComplexModel 1)
    change GermIdeal.pullback (m := n + 1) (projectionLineDiffeo U)
      (GermIdeal.pullback (m := n + 1) Prod.fst P.ideal) =
      GermIdeal.pullback (m := n + 1) (projection U) P.ideal
    exact (HironakaSmoothSubmersionOrderedChoiceImageTrace.coherent_pullback_comp
      hp (projectionLineDiffeo U).contMDiff P.ideal hI).symm
  · rfl

private theorem cylinder_wellFormed (P : MarkedIdeal n U) (hP : IsInvDomain k P) :
    ({ cylinder P with E := (cylinder P).E ++ [zeroPlane U] } :
      MarkedIdeal (n + 1) (ambient U)).IsWellFormed := by
  rw [← projectionTest_pullback_line P hP.isWellFormed.isCoherent]
  exact MarkedIdealTowerTransport.IsWellFormed.pullback
    (Φ := projectionLineDiffeo U) (projection_test_isInvDomain (X := base U) P hP).isWellFormed

private theorem cylinder_local (P Q : MarkedIdeal n U) (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (h : LocWPEquiv (X := base U) P Q) :
    LocWPEquiv (X := ambient U)
      { cylinder P with E := (cylinder P).E ++ [zeroPlane U] }
      { cylinder Q with E := (cylinder Q).E ++ [zeroPlane U] } := by
  have h0 := (isLocStable_locEquiv Kinds.wp).projection rfl h
  have h1 := LocEquiv.pullback_diffeo (κ := Kinds.wp) (X' := ambient U) rfl (projectionLineDiffeo U)
    (projection_test_isInvDomain (X := base U) P hP).isWellFormed.isCoherent
    (projection_test_isInvDomain (X := base U) Q hQ).isWellFormed.isCoherent h0
  rw [projectionTest_pullback_line P hP.isWellFormed.isCoherent,
    projectionTest_pullback_line Q hQ.isWellFormed.isCoherent] at h1
  exact h1


private def sectionCut (P : MarkedIdeal n U) : MarkedIdeal (n + 1) (ambient U) :=
  withN (coeffMarkedAlong (cylinder P)) (liftedCarrier P.N)

private theorem cylinder_cut_relation (P : MarkedIdeal n U) (hP : IsInvDomain k P) :
    MemberRel (Y := ambient U) (cylinder P) (sectionCut P) (fun i => derivMarkedAlong (cylinder P) i)
      ((cylinder P).N ∩ {x | ∀ H ∈ [zeroPlane U], x ∈ H}) := by
  have hW := cylinder_wellFormed P hP
  have hSet : (cylinder P).N ∩ {x | ∀ H ∈ [zeroPlane U], x ∈ H} = liftedCarrier P.N := by
    ext x
    simp [cylinder, zeroPlane, liftedCarrier]
  rw [hSet]
  exact memberRel_base (X := ambient U) (cylinder P) hW.isClosedSubmanifold_N hW.isCoherent hP.one_le_d
    (liftedCarrier_closed_submanifold hP.isWellFormed.isClosedSubmanifold_N) (fun _ hx => hx.1)

private theorem cut_local (P Q : MarkedIdeal n U) (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (h : LocWPEquiv (X := base U) P Q) :
    LocWPEquiv (X := ambient U) (sectionCut P) (sectionCut Q) := by
  let F := [zeroPlane U]
  have hE : (cylinder P).E = (cylinder Q).E :=
    congrArg (List.map (projection U ⁻¹' ·)) h.E_eq.symm
  have hPerm : (F ++ (cylinder P).E).Perm ((cylinder P).E ++ F) := List.perm_append_comm
  have hCut := locEquiv_perm (κ := Kinds.wp) rfl (cylinder_local P Q hP hQ h) hPerm
  have hP' := cylinder_wellFormed P hP
  have hQ' := cylinder_wellFormed Q hQ
  have hPW : ({ cylinder P with E := F ++ (cylinder P).E } :
      MarkedIdeal (n + 1) (ambient U)).IsWellFormed :=
    ⟨hP'.isClosedSubmanifold_N, hP'.isCoherent,
      HironakaG3SNCListPermutation.isSNCDivisor_of_perm hP'.isSNCDivisor hPerm,
      NormalCrossingsComparison.isTransverse_of_forall_mem hP'.isTransverse hPerm.subset⟩
  have hQW : ({ cylinder Q with E := F ++ (cylinder P).E } :
      MarkedIdeal (n + 1) (ambient U)).IsWellFormed := by
    rw [hE]
    have hPermQ : (F ++ (cylinder Q).E).Perm ((cylinder Q).E ++ F) := List.perm_append_comm
    exact ⟨hQ'.isClosedSubmanifold_N, hQ'.isCoherent,
      HironakaG3SNCListPermutation.isSNCDivisor_of_perm hQ'.isSNCDivisor hPermQ,
      NormalCrossingsComparison.isTransverse_of_forall_mem hQ'.isTransverse hPermQ.subset⟩
  apply LocEquiv.of_isLocStable (isLocStable_separateMemberCut Kinds.wp) rfl
  exact ⟨cylinder P, cylinder Q, F, fun i => derivMarkedAlong (cylinder P) i,
    fun i => derivMarkedAlong (cylinder Q) i, hE, hCut, hPW, hQW,
    cylinder_cut_relation P hP, cylinder_cut_relation Q hQ⟩


private theorem projection_section_ideal {I : GermIdeal n U} (hI : I.IsCoherent) :
    GermIdeal.pullback (m := n) (zeroSection U)
      (GermIdeal.pullback (m := n + 1) (projection U) I) = I := by
  have hId : projection U ∘ zeroSection U = id :=
    funext (fun x => Subtype.ext (tangentProjection_tangentInclusion n 1 x.val))
  rw [← coherent_pullback_comp (projection_contMDiff U) (zeroSection_contMDiff U) I hI,
    hId, BlowupControlledTransform.pullback_id hI]

private theorem cylinder_coeff_ideal (P : MarkedIdeal n U) (hP : IsInvDomain k P) :
    (coeffMarkedAlong (cylinder P)).ideal =
      GermIdeal.pullback (m := n + 1) (projection U) (coeffMarkedAlong P).ideal := by
  let I := P.ideal
  have hI := hP.isWellFormed.isCoherent
  have hN := hP.isWellFormed.isClosedSubmanifold_N
  change (finSumIdeal (fun i => idealPow (iterDerivIdealAlong (projection U ⁻¹' P.N)
      (GermIdeal.pullback (m := n + 1) (projection U) I) i) (sumExp (fun j => P.d - j) P.d i)) P.d) =
    GermIdeal.pullback (m := n + 1) (projection U)
      (finSumIdeal (fun i => idealPow (iterDerivIdealAlong P.N I i)
        (sumExp (fun j => P.d - j) P.d i)) P.d)
  rw [pullback_finSumIdeal (projection_contMDiff U) _ P.d
    (fun i _ => isCoherent_idealPow (isCoherent_iterDerivIdealAlong hI hN i) _)]
  apply finSumIdeal_congr
  intro i _
  rw [HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow (projection_contMDiff U)
    (isCoherent_iterDerivIdealAlong hI hN i),
    HironakaSmoothSubmersionRelativeDifferentialIdeals.pullback_iterDerivIdealAlong
      (X := base U) (Y := ambient U) (projection_isSubmersion (U := U)) I hI P.N hN i]

private theorem sectionCut_local_sectionMarked (P : MarkedIdeal n U) (hP : IsInvDomain k P) :
    LocWPEquiv (X := ambient U) (sectionCut P) (sectionMarked P) := by
  let S := sectionMarked P
  let A := sectionCut P
  let B := coeffMarkedAlong S
  have hS : IsInvDomain k S := section_projected_domain k P.N P.E P.ideal P.d hP
  have hAI : A.ideal.IsCoherent := isCoherent_coeffMarkedAlong
    (cylinder_wellFormed P hP).isCoherent (cylinder_wellFormed P hP).isClosedSubmanifold_N
  have hBI : B.ideal.IsCoherent := isCoherent_coeffMarkedAlong
    hS.isWellFormed.isCoherent hS.isWellFormed.isClosedSubmanifold_N
  have hCoeff := isCoherent_coeffMarkedAlong hP.isWellFormed.isCoherent hP.isWellFormed.isClosedSubmanifold_N
  have hTraceA : GermIdeal.pullback (m := n) (zeroSection U) A.ideal = (coeffMarkedAlong P).ideal := by
    change GermIdeal.pullback (m := n) (zeroSection U) (coeffMarkedAlong (cylinder P)).ideal = _
    rw [cylinder_coeff_ideal P hP, projection_section_ideal hCoeff]
  have hTraceB : GermIdeal.pullback (m := n) (zeroSection U) B.ideal = (coeffMarkedAlong P).ideal := by
    have hTrace := markedPullback_section_coeffMarkedAlong P.N hP.isWellFormed.isClosedSubmanifold_N P.E
      (GermIdeal.pullback (m := n + 1) (projection U) P.ideal)
      (isCoherent_pullback (projection_contMDiff U) hP.isWellFormed.isCoherent) P.d
    rw [projection_section_ideal hP.isWellFormed.isCoherent] at hTrace
    exact congrArg (fun M : MarkedIdeal n U => M.ideal) hTrace
  have hRetEq : GermIdeal.pullback (m := n + 1) (zeroSection U ∘ projection U) A.ideal =
      GermIdeal.pullback (m := n + 1) (zeroSection U ∘ projection U) B.ideal := by
    rw [coherent_pullback_comp (zeroSection_contMDiff U) (projection_contMDiff U) A.ideal hAI,
      coherent_pullback_comp (zeroSection_contMDiff U) (projection_contMDiff U) B.ideal hBI,
      hTraceA, hTraceB]
  have hA := restrictEquiv_actual_open_section U P.N A.E A.d A.ideal (hol_of_isCoherent hAI)
  have hB := restrictEquiv_actual_open_section U P.N B.E B.d B.ideal (hol_of_isCoherent hBI)
  have hLe := hA.le
  have hGe := hB.le
  rw [hRetEq] at hLe
  rw [← hRetEq] at hGe
  have hEquiv : RestrictEquiv A B := by
    exact ⟨rfl, rfl, rfl, RestrictLe.trans hLe hB.ge, RestrictLe.trans hGe hA.ge⟩
  exact (locEquiv_of_restrictEquiv_closed (κ := Kinds.wp) rfl hEquiv
    hS.isWellFormed.isClosedSubmanifold_N hAI hBI).trans
    (coefficient_local_any_boundary (X := ambient U) S hS).symm

/-- Arbitrary native marks and separate proper carriers may be given on the
source. The supported zero-section records inherit the full weak test class. -/
theorem locWPEquiv_sectionMarked_of_source (P Q : MarkedIdeal n U)
    (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (h : LocWPEquiv (X := base U) P Q) :
    LocWPEquiv (X := ambient U) (sectionMarked P) (sectionMarked Q) :=
  (sectionCut_local_sectionMarked P hP).symm.trans
    ((cut_local P Q hP hQ h).trans (sectionCut_local_sectionMarked Q hQ))

/-- The actual whole normal padding keeps the original source weak test
class, with arbitrary additional ordered ambient boundary slots. -/
theorem locWPEquiv_properNormalMarked_of_source (P Q : MarkedIdeal n U)
    (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (h : LocWPEquiv (X := base U) P Q) (F : List (Set (productOpen U))) :
    LocWPEquiv (X := ambient U)
      { properNormalMarked P with E := F ++ (properNormalMarked P).E }
      { properNormalMarked Q with E := F ++ (properNormalMarked Q).E } := by
  have hNative := (properNormalMarked_locWPEquiv_section P hP).trans
    ((locWPEquiv_sectionMarked_of_source P Q hP hQ h).trans
      (properNormalMarked_locWPEquiv_section Q hQ).symm)
  have hE := hNative.E_eq
  exact hE ▸ locEquiv_addE (κ := Kinds.wp) rfl hNative F


open HironakaG1NormalSelectorGraph HironakaG1ProperNormalOriginalTest
  HironakaActualCoherentWeightedCoefficientMarked HironakaActualPowerBoundaryExponents
  HironakaActualWeightedNormalAmbientDerivatives HironakaActualRelativeNormalGeometry
  RestrictedIdealExtension

private theorem selectorMarked_isCoherent {f : U → ComplexModel 1}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ f)
    (P : MarkedIdeal n U) (hP : P.ideal.IsCoherent) (F : List (Set (productOpen U))) :
    (selectorMarked f P F).ideal.IsCoherent := by
  have hcd : ContMDiff 𝓘(ℂ, ComplexModel (n + 1)) 𝓘(ℂ, ℂ) ∞
      (fun z : productOpen U => (actualJointNormalProjection n 1 z.val - f (projection U z)) 0) :=
    (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1)).contMDiff.comp
      (((actualJointNormalProjection n 1).contMDiff.comp contMDiff_subtype_val).sub
        (hf.comp (projection_contMDiff U)))
  exact isCoherent_sumIdeal (isCoherent_pullback (projection_contMDiff U) hP)
    (isCoherent_finiteFunctionIdeal _ (fun _ => (hcd.mdifferentiable (by simp)).pow P.d))

private theorem pullback_selectorMarked {f g : U → ComplexModel 1}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ g)
    (P : MarkedIdeal n U) (hP : P.ideal.IsCoherent) (F : List (Set (productOpen U))) :
    MarkedIdeal.pullback (M := ambient U) (M' := ambient U) (graphShift f g)
      (selectorMarked g P F) = selectorMarked f P (F.map (graphShift f g ⁻¹' ·)) := by
  have h := pullback_power_selectorMarked hf hg P hP F 1
  have hOne (M : MarkedIdeal (n + 1) (ambient U)) (hM : M.ideal.IsCoherent) :
      powerMarked (X := ambient U) M 1 = M :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl
      (FactorizationFromResolution.idealPow_one_of_isCoherent hM) (Nat.mul_one _)
  rw [hOne _ (selectorMarked_isCoherent hg P hP F),
    hOne _ (selectorMarked_isCoherent hf P hP _)] at h
  exact h

private theorem selectorMarked_zero_eq_supported (P : MarkedIdeal n U) :
    selectorMarked (0 : U → ComplexModel 1) P [] = supportedNormalMarked P := by
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
  change sumIdeal (GermIdeal.pullback (m := n + 1) (projection U) P.ideal)
    (finiteFunctionIdeal (fun _ : Unit => fun z : productOpen U =>
      (actualJointNormalProjection n 1 z.val - (0 : ComplexModel 1)) 0 ^ P.d)) =
    (properNormalMarked P).ideal
  have hCoord (z : productOpen U) :
      relativeNormalCoordinate U z = actualJointNormalProjection n 1 z.val 0 := by
    simp [relativeNormalCoordinate,
      HironakaActualZeroCoordinateContactSeed.addedCoordinate,
      HironakaActualGraphFunctionalIdeal.graphFunction,
      HironakaActualZeroCoordinateContactSeed.zeroFunction]
  change _ = sumIdeal (GermIdeal.pullback (m := n + 1) (projection U) P.ideal)
    (finiteFunctionIdeal (fun _ : Unit => fun z => relativeNormalCoordinate U z ^ P.d))
  simp only [sub_zero, hCoord]

/-- The supported graph records in two different actual selector charts
inherit the source weak class after the real graph shift. The comparison
transports each additional ordered ambient boundary member. -/
theorem locWPEquiv_selectorMarked_of_source (P Q : MarkedIdeal n U)
    (hP : IsInvDomain k P) (hQ : IsInvDomain l Q) (h : LocWPEquiv (X := base U) P Q)
    {f g : U → ComplexModel 1}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ g)
    (F : List (Set (productOpen U))) :
    LocWPEquiv (X := ambient U) (selectorMarked f P (F.map (graphShift f g ⁻¹' ·)))
      (MarkedIdeal.pullback (M := ambient U) (M' := ambient U) (graphShift f g) (selectorMarked g Q F)) := by
  have hSDP := supported_normal_data P hP
  have hSDQ := supported_normal_data Q hQ
  have hZero : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞
      (0 : U → ComplexModel 1) := contMDiff_const
  have hZL : LocWPEquiv (X := ambient U) (supportedNormalMarked P) (supportedNormalMarked Q) :=
    hSDP.2.2.symm.trans ((locWPEquiv_properNormalMarked_of_source P Q hP hQ h []).trans hSDQ.2.2)
  rw [← selectorMarked_zero_eq_supported P, ← selectorMarked_zero_eq_supported Q] at hZL
  have hfL := LocEquiv.pullback_diffeo (κ := Kinds.wp) (X' := ambient U) rfl
    (graphShiftEquiv f 0 hf hZero)
    (selectorMarked_isCoherent hZero P hP.isWellFormed.isCoherent [])
    (selectorMarked_isCoherent hZero Q hQ.isWellFormed.isCoherent []) hZL
  change LocWPEquiv (X := ambient U)
    (MarkedIdeal.pullback (M := ambient U) (M' := ambient U) (graphShift f 0) (selectorMarked 0 P []))
    (MarkedIdeal.pullback (M := ambient U) (M' := ambient U) (graphShift f 0) (selectorMarked 0 Q [])) at hfL
  rw [pullback_selectorMarked hf hZero P hP.isWellFormed.isCoherent [],
    pullback_selectorMarked hf hZero Q hQ.isWellFormed.isCoherent []] at hfL
  rw [pullback_selectorMarked hf hg Q hQ.isWellFormed.isCoherent F]
  let F' := F.map (graphShift f g ⁻¹' ·)
  have hF := locEquiv_addE (κ := Kinds.wp) rfl hfL F'
  have hRight : ({ selectorMarked f Q [] with E := F' ++ (selectorMarked f P []).E } :
      MarkedIdeal (n + 1) (ambient U)) = selectorMarked f Q F' := by
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · rfl
    · change F' ++ P.E.map (projection U ⁻¹' ·) = F' ++ Q.E.map (projection U ⁻¹' ·)
      rw [h.E_eq]
    · rfl
    · rfl
  change LocWPEquiv (X := ambient U) (selectorMarked f P F')
    { selectorMarked f Q [] with E := F' ++ (selectorMarked f P []).E } at hF
  rwa [hRight] at hF

/-- Independent native Hilbert–Samuel presentations over the same intrinsic
cut inherit the full graph-supported test comparison from the actual
source weak class, without requiring equality of compressed ideals. -/
theorem locWPEquiv_selectorMarked_of_native (P Q : MarkedIdeal n U)
    (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    {W : Set U} {H : ℕ → ℕ}
    (hPN : HironakaG11PresLineState.NativeHSState (X := base U) P W H)
    (hQN : HironakaG11PresLineState.NativeHSState (X := base U) Q W H)
    (hE : Q.E = P.E)
    {f g : U → ComplexModel 1}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ g)
    (F : List (Set (productOpen U))) :
    LocWPEquiv (X := ambient U) (selectorMarked f P (F.map (graphShift f g ⁻¹' ·)))
      (MarkedIdeal.pullback (M := ambient U) (M' := ambient U) (graphShift f g) (selectorMarked g Q F)) :=
  locWPEquiv_selectorMarked_of_source P Q hP hQ
    (HironakaG11PresLineStable.locWPEquiv_native hPN hQN hE) hf hg F

end
end Hironaka.HironakaG1SourceWeakClassGraphLift
