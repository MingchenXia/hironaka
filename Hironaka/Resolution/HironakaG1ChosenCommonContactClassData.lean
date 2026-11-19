import Hironaka.Resolution.HironakaG8OriginalRecursiveLocal
import Hironaka.Resolution.HironakaG1CoefficientCarrierClassData
import Hironaka.Resolution.HironakaStepOneMemberLowerExtension
import Hironaka.Resolution.HironakaG8PowerLowerMarks

/-! Ordinary original arbitrary-boundary sources give the actual chosen
common-contact lower domain and normalized exponents. The second source's
existing contact is retained, including its entire double-product mark.
Blueprint FIRST: hironaka-g1-chosen-common-contact-class-data.tex. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1ChosenCommonContactClassData
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealEquivalence.MarkedIdeal ResolutionInvariantSpec
  GermIdealOrder DivisorExponentAlong HironakaG8LocalHistory
  HironakaStepOneMemberLowerExtension HironakaG8OriginalRecursiveLocal
  HironakaG8HomStable HironakaG1CoeffBarLocal InvDomainTowerAlong
  HomogenizedIdealAlong HomogenizedIdealAlongTower ContactStageKept ContactStageInvDomain
  CoefficientIdealRestriction ContactIndependenceAlong
  HironakaActualOriginalHistoricalBarWeightedThreshold HironakaActualCoefficientDivisorExponentGap
  HironakaG8GapNormalizedExponent HironakaG8PowerLowerMarks
  StepOneValue StepOneValueMasked StepOneLowerDomain

/-- Whole coherence and positive native mark, together with equality of
the actual carrier, ordered boundary and true cosupport, transfer the
complete native domain. Nonzero along the carrier is derived internally. -/
theorem isInvDomain_of_sameCarrier_cosupp {n k : ℕ} {X : CMfd.{0} n}
    (A B : MarkedIdeal n X) (hB : IsInvDomain k B)
    (hI : A.ideal.IsCoherent) (hd : 1 ≤ A.d)
    (hN : A.N = B.N) (hE : A.E = B.E) (hCos : A.cosupp = B.cosupp) :
    IsInvDomain k A := by
  refine ⟨⟨?_, hI, ?_, ?_⟩, ?_, hd, ?_⟩
  · rw [hN]
    exact hB.isWellFormed.isClosedSubmanifold_N
  · rw [hE]
    exact hB.isWellFormed.isSNCDivisor
  · rw [hN, hE]
    exact hB.isWellFormed.isTransverse
  · rw [hN]
    exact hB.dimLE
  · intro x hx
    apply isNonzeroAlongAt_of_thin_cosupport (d := A.d) hI
    · intro O hO hSub
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro p ⟨hpO, hpN⟩
      have hpB : p ∈ B.N := hN ▸ hpN
      obtain ⟨g, hg, hFreq⟩ := hB.isNonzeroAlongAt p hpB
      have hMem := HomogenizedGlueing.eventually_mem hB.isWellFormed.isCoherent hg
      obtain ⟨z, ⟨hzN, hzNe⟩, hzMem, hzO⟩ :=
        (hFreq.and_eventually (hMem.and (hO.mem_nhds hpO))).exists
      have hzA : z ∈ A.N := hN.symm ▸ hzN
      have hzCos : z ∈ B.cosupp := hCos ▸ hSub ⟨hzO, hzA⟩
      exact hzNe ((vanishesToOrderOn_one_iff hzN
        (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
          hB.isWellFormed.isCoherent hzMem)).mp
        ((hzCos.2 g hzMem).mono hB.one_le_d))
    · exact hx

/-- At the actual second-source zero mask, ordinary original source data
derive BOTH full kept-contact domains, true native marks, entire historical
boundaries, local relation and normalized boundary exponents. -/
theorem chosen_common_contact_class_data {n kJ kK : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (J K : MarkedIdeal n X)
    (hJ : IsInvDomain kJ J) (hK : IsInvDomain kK K)
    (hN : J.N = K.N) (hLocal : LocWPEquiv J K)
    (hMaxK : IsMaximalOrderAlong K.N K.ideal K.d)
    (T : BlowupTower X Y) (hT : IsGeoTestTower J T)
    (y : Y) (hy : y ∈ (geoTransformAlong (barMarked K) T).cosupp)
    (hLevel : level K T y = 0)
    (hOut : y ∉ CodimOneSupportAlong.codimOnePartAlong (geoTransformAlong (barMarked K) T).N
      (geoTransformAlong (barMarked K) T).ideal (geoTransformAlong (barMarked K) T).d) :
    ∃ _hyO : y ∈ maskB K T y,
      let O := maskB K T y
      let w := (tangentChoice K (T.proj y)).2
      let A := contactMarkedKept J w T O
      let B := contactMarkedKept K w T O
      B = lowerMarkedB K T y ∧
      IsInvDomain (kK-1) A ∧ IsInvDomain (kK-1) B ∧
      A.N = B.N ∧ A.E = B.E ∧ LocWPEquiv (X := CMfd.of (n := n) O) A B ∧
      A.d = coefficientMark (coefficientMark J.d) ∧
      B.d = coefficientMark (coefficientMark K.d) ∧
      A.E = (geoTransformAlong J T).E.map ((Subtype.val : O → Y) ⁻¹' ·) ∧
      B.E = (geoTransformAlong K T).E.map ((Subtype.val : O → Y) ⁻¹' ·) ∧
      A.E.length = J.E.length + T.length ∧ B.E.length = K.E.length + T.length ∧
      (∀ H ∈ A.E, ∀ x ∈ A.cosupp, x ∈ H →
        B.d * divExpAlong n A.N A.ideal H x = A.d * divExpAlong n B.N B.ideal H x) := by
  have hTK : IsGeoTestTower K T := (hLocal.wEquiv.2 T).1.mp hT
  have hBarK : IsGeoTestTower (barMarked K) T :=
    (((bar_local_any_boundary K hK).wEquiv).2 T).1.mp hTK
  have hyO := StepOneLowerDomain.mem_maskB K hK.isWellFormed hK.one_le_d hMaxK T hBarK hy hLevel hOut
  let O := maskB K T y
  let w := (tangentChoice K (T.proj y)).2
  let A := contactMarkedKept J w T O
  let B := contactMarkedKept K w T O
  obtain ⟨_hyU, hw⟩ := tangentChoice_spec K
    (exists_tangent_of_mem_cosupp K hK.isWellFormed hK.one_le_d hMaxK T hBarK hy)
  let U : Opens X := ⟨(tangentChoice K (T.proj y)).1, hw.isOpen⟩
  have hB : IsInvDomain (kK-1) B :=
    isInvDomain_stage_coeffHomAlong_of_le K hK.isWellFormed hK.one_le_d hK.dimLE U hw T hBarK O
      (fun _ hz => (interior_subset hz).1)
      (fun _ hz _ => (interior_subset hz).2.2)
      (fun H hH _ hz _ => (interior_subset hz).2.1 H hH)
  have hABN : A.N = B.N := by
    change (Subtype.val : O → Y) ⁻¹' HomogenizedGlueingTower.strictAlong T (J.N ∩ {x | w x = 0}) =
      (Subtype.val : O → Y) ⁻¹' HomogenizedGlueingTower.strictAlong T (K.N ∩ {x | w x = 0})
    rw [hN]
  have hAN : IsClosedSubmanifold n A.N := hABN.symm ▸ hB.isWellFormed.isClosedSubmanifold_N
  have hAB : LocWPEquiv (X := CMfd.of (n := n) O) A B :=
    contact_lower_locally_equivalent J K hJ hK hN hLocal T hT hTK O w hAN
  have hAJBar := (original_bar_weighted_history J hJ T hT).2.1
  have hAI : A.ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val
      (isCoherent_coeffMarkedAlong hAJBar.isWellFormed.isCoherent hAJBar.isWellFormed.isClosedSubmanifold_N)
  have hAd : 1 ≤ A.d := one_le_coeffMarkedAlong_d (geoTransformAlong (barMarked J) T)
  have hA : IsInvDomain (kK-1) A :=
    isInvDomain_of_sameCarrier_cosupp (X := CMfd.of (n := n) O)
      A B hB hAI hAd hABN hAB.wEquiv.1 hAB.cosupp_eq_base
  have hGapA := original_contact_divisor_exponent_gap J hJ T hT w O
  have hGapB := original_contact_divisor_exponent_gap K hK T hTK w O
  refine ⟨hyO, rfl, hA, hB, hABN, hAB.wEquiv.1, hAB, ?_, ?_, hGapA.2.1,
    hGapB.2.1, hGapA.2.2.1, hGapB.2.2.1, ?_⟩
  · exact hGapA.1
  · exact hGapB.1
  · change ∀ H ∈ A.E, ∀ x ∈ A.cosupp, x ∈ H →
      B.d * divExpAlong n A.N A.ideal H x = A.d * divExpAlong n B.N B.ideal H x
    intro H hH x hx hxH
    obtain ⟨i, hi⟩ := List.get_of_mem hH
    have hHB : H ∈ B.E := hAB.wEquiv.1 ▸ hH
    obtain ⟨j, hj⟩ := List.get_of_mem hHB
    have hGa : divExpAlong n A.N A.ideal (A.E.get i) x = 0 ∨
        A.d ≤ divExpAlong n A.N A.ideal (A.E.get i) x := by
      simpa only [hi] using hGapA.2.2.2 H x
    have hGb : divExpAlong n B.N B.ideal (B.E.get j) x = 0 ∨
        B.d ≤ divExpAlong n B.N B.ideal (B.E.get j) x := by
      simpa only [hj] using hGapB.2.2.2 H x
    have hExp := normalized_exponent_of_numeric_gap (X := CMfd.of (n := n) O) hn A B hA hB hABN hAB i j
      (hi.trans hj.symm) (A.cosupp_subset_N hx) (hi.symm ▸ hxH) hGa hGb
    simpa only [hi, hj] using hExp

end
end Hironaka.HironakaG1ChosenCommonContactClassData
