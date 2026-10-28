import TranscendentalNakamaye.Pending.HironakaDisjointCoherentNormalRecoding
import TranscendentalNakamaye.Pending.SNCGlobalPrimeComponents
import TranscendentalNakamaye.Pending.DimensionMonotone
import TranscendentalNakamaye.Pending.CodimOnePartTowerAlong

/-! The genuine first full ambient normal history, with born boundary retained.
The blueprint `hironaka-disjoint-first-step-historical-anchor.tex` precedes code.
The lower endpoint is the actual original literal normal contact history.
No nonempty thin cross-ambient historical comparison is asserted. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace TranscendentalNakamaye.Pending.HironakaDisjointFirstStepHistoricalAnchor
noncomputable section
open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  MarkedIdealOperationsAlong.MarkedIdeal BlowupTowers BlowupTowerTransforms
  HironakaDisjointCoherentNormalRecoding HironakaActualZeroCoordinateContactSeed
  HironakaRelativeNormalIdeal HironakaActualCentreJointJets HironakaActualIntrinsicStableAmbientIso
  GermIdealOrder RelativePrincipalizationSpan GermIdealPullbackCalculus
  InvertibleIdealQuotient IdealWeightPowers DivisorExponentAlong
  HomogenizedIdealAlong StepOneValue StepOneRegime StepOneLowerDomain
  HironakaSharpOriginalProductTraceOrder RestrictedIdealExtension InvDomainRebase
  CanonicalCentres ContactStageKept GeneralValue NonmonomialOrderTail MonomialPartAlong
  CompanionReductionAlong CoefficientIdeal HomogenizedGlueing DerivativeIdeal TangentDirectionAlong GermIdealTotalTransform
  CodimOneSupportAlong NormalCrossings NonmonomialOrderLocal BlowupTowerSplit
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

private abbrev model (n : ℕ) : CMfd n := CMfd.of (n := n) (ComplexModel n)
variable {n : ℕ}

/-- Every actual boundary exponent through the point is zero when the full
maximal-order-one ideal has no codimension-one cosupport part. -/
theorem one_mem_monomial_of_empty_codimOne {Y : CMfd (n+1)}
    (A : MarkedIdeal (n+1) Y) (hA : A.IsWellFormed) (hN : A.N=univ) (hd : A.d=1)
    (hmax : IsMaximalOrderAlong A.N A.ideal A.d)
    (hZ : codimOnePartAlong A.N A.ideal A.d=∅) (y : Y) :
    (monomialPartAlong (n+1) A.N A.ideal A.E).mem y (fun _ => 1) := by
  have hmax' : IsMaximalOrderAlong univ A.ideal 1 := by simpa only [hN,hd] using hmax
  have hZ' : codimOnePartAlong univ A.ideal 1=∅ := by simpa only [hN,hd] using hZ
  have hhol : ∀ z g,A.ideal.mem z g → HolomorphicAt (n+1) g z :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hA.isCoherent hg
  refine ⟨holomorphicAt_const 1,?_⟩
  intro i _hyN hyi
  have he : divExpAlong (n+1) A.N A.ideal (A.E.get i) y=0 := by
    by_contra hne
    have hpos : 1≤divExpAlong (n+1) A.N A.ideal (A.E.get i) y := by omega
    have hP := (isDivNearAlong_divExpAlong (N := A.N) (H := A.E.get i) hhol y).mono hpos
    have hP' : ∀ᶠ z in 𝓝 y,z∈A.E.get i → z∈cosupport (n+1) univ A.ideal 1 := by
      simpa only [IsDivNearAlong,hN,mem_univ,true_implies] using hP
    let V : Set Y := interior {z | z∈A.E.get i → z∈cosupport (n+1) univ A.ideal 1}
    have hyV : y∈V := mem_interior_iff_mem_nhds.mpr hP'
    have hreg := SNCGlobalPrimeComponents.regularAtDim_member hA.isSNCDivisor i hyi
    have hregV : RegularAtDim (n := n+1) (A.E.get i ∩ V) y n :=
      RegularPointDimension.regularAtDim_of_inter_eq isOpen_interior hyV
        (by rw [inter_assoc,inter_self]) hreg
    have hsub : A.E.get i ∩ V ⊆ cosupport (n+1) univ A.ideal 1 :=
      fun z hz => interior_subset hz.2 hz.1
    have hdim := DimensionMonotone.locDimGE_of_regularAtDim_subset
      (isComplexAnalyticSubset_cosupport_along hA.isCoherent
        HomogenizedGlueingTower.isClosedSubmanifold_univ (by rfl)) hsub hregV
    have hz := (mem_codimOnePartAlong_iff hA.isCoherent
      HomogenizedGlueingTower.isClosedSubmanifold_univ (by rfl) hmax').mpr
        ⟨n,AnalyticIrreducibleComponents.regularAtDim_univ y,hdim⟩
    rw [hZ'] at hz
    exact hz
  rw [he]
  exact IsInSpanAt.restrict (isInSpanAt_self
    (show (idealPow (vanishingIdeal (n := n+1) (A.E.get i)) 0).mem y (fun _ => 1) from holomorphicAt_const 1)
    (holomorphicAt_const 1))

private theorem stabilized_maximal_order {I : GermIdeal n (ComplexModel n)} (hI : I.IsCoherent) :
    IsMaximalOrderAlong (stabilizedMarked I).N (stabilizedMarked I).ideal (stabilizedMarked I).d := by
  intro z hz
  have hp : z∈ordMask (M := model (n+1)) (stabilizedMarked I) 1 := by
    rw [stabilized_initial_orderMask hI]
    trivial
  have hnot := notMem_ordGe_of_mem_ordMask hp
  change z∉ordGe (ordinaryTraceMarked (X := model (n+1)) univ (stabilizedIdeal I)) 2 at hnot
  rw [ordGe_ordinaryTraceMarked_eq_cosupport (X := model (n+1)) univ (stabilizedIdeal I) (stabilizedIdeal_isCoherent hI) 2] at hnot
  exact hnot hz

/-- Original members remain empty, even though the transformed boundary is born. -/
theorem original_members_nil (I : GermIdeal n (ComplexModel n)) {Y : CMfd (n+1)}
    (T : BlowupTower (model (n+1)) Y) : origMembers (stabilizedMarked I) T=[] := by
  exact List.take_zero

theorem original_level_zero (I : GermIdeal n (ComplexModel n)) {Y : CMfd (n+1)}
    (T : BlowupTower (model (n+1)) Y) (y : Y) : level (stabilizedMarked I) T y=0 := by
  change BoundaryCount.boundaryCount (origMembers (stabilizedMarked I) T) y=0
  rw [original_members_nil]
  rfl

private theorem section_image (A : Set (ComplexModel n)) :
    tangentInclusion n 1 '' A=zeroCarrier A := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    change tangentProjection n 1 (tangentInclusion n 1 x)∈A ∧ actualJointNormalProjection n 1 (tangentInclusion n 1 x)=0
    exact ⟨by simpa only [tangentProjection_tangentInclusion] using hx,by simp⟩
  · rintro ⟨hx,hz⟩
    refine ⟨tangentProjection n 1 z,hx,?_⟩
    change actualJointNormalProjection n 1 z=0 at hz
    simpa only [HironakaActualIntrinsicStableAmbientIso.join,hz,map_zero,add_zero] using
      (join_projections (n := n) (m := 1) z)

/-- The actual canonical base first centre induces an actual canonical upper step. -/
theorem firstStep_upper_isCanonical {q : ℕ} (hn : 0<n) {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) (C : Set (ComplexModel n))
    (hC : C=∅ ∨ C=ResolutionDriver.maxLocus ((invFamily hn q).inv (X := model n) (baseMarked I) .refl)
      (baseMarked I).cosupp)
    {Y : CMfd (n+1)} (π : Y → ComplexModel (n+1))
    (hπ : IsBlowupAlong (n+1) (tangentInclusion n 1 '' C) π) :
    IsCanonical (X := model (n+1)) (stabilizedMarked I) ((invFamily (Nat.succ_pos n) (q+1)).inv (stabilizedMarked I))
      (.step (X := model (n+1)) .refl (tangentInclusion n 1 '' C) π hπ) := by
  refine ⟨trivial,?_⟩
  rcases hC with hC | hC
  · left
    simp only [hC,image_empty]
  · right
    change tangentInclusion n 1 '' C=ResolutionDriver.maxLocus
      ((invFamily (Nat.succ_pos n) (q+1)).inv (X := model (n+1)) (stabilizedMarked I) .refl)
      (stabilizedMarked I).cosupp
    rw [stabilized_initial_maximum_locus hn hM,hC,section_image]

/-- The first transformed record retains the whole born boundary at index zero. -/
theorem firstStep_current_boundary (I : GermIdeal n (ComplexModel n))
    (C : Set (ComplexModel n)) {Y : CMfd (n+1)} (π : Y → ComplexModel (n+1))
    (hπ : IsBlowupAlong (n+1) (tangentInclusion n 1 '' C) π) :
    (geoTransformAlong (X := model (n+1)) (stabilizedMarked I) (.step (X := model (n+1)) .refl (tangentInclusion n 1 '' C) π hπ)).E=
      [π ⁻¹' (tangentInclusion n 1 '' C)] := rfl

private theorem bar_test {q : ℕ} {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) {Y : CMfd (n+1)}
    (T : BlowupTower (model (n+1)) Y) (hT : IsGeoTestTower (stabilizedMarked I) T) :
    IsGeoTestTower (barMarked (stabilizedMarked I)) T := by
  have hd := stabilized_isInvDomain hM
  exact ((HomogenizedIdealAlongTower.coeff_homAlong_wEquiv (X := model (n+1))
    (stabilizedMarked I) hd.isWellFormed.isClosedSubmanifold_N hd.isWellFormed.isCoherent hd.one_le_d).2 T).1.mpr hT

private theorem initial_codimOne_empty {q : ℕ} {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) :
    codimOnePartAlong (stabilizedMarked I).N (stabilizedMarked I).ideal (stabilizedMarked I).d=∅ := by
  have hd := stabilized_isInvDomain hM
  have hbar : codimOnePartAlong (barMarked (X := model (n+1)) (stabilizedMarked I)).N
      (barMarked (X := model (n+1)) (stabilizedMarked I)).ideal
      (barMarked (X := model (n+1)) (stabilizedMarked I)).d=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact stabilized_not_special hM z (Or.inl ⟨rfl,hz⟩)
  have hw := HomogenizedIdealAlongTower.coeff_homAlong_wEquiv (X := model (n+1))
    (stabilizedMarked I) hd.isWellFormed.isClosedSubmanifold_N hd.isWellFormed.isCoherent hd.one_le_d
  have he := CodimOnePartCanonical.codimOnePartAlong_geoTransformAlong_of_wEquiv
    (X := model (n+1)) (𝔪 := barMarked (stabilizedMarked I)) hw rfl .refl trivial
  exact he.symm.trans hbar

private theorem current_codimOne_empty {q : ℕ} {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) {Y : CMfd (n+1)}
    (T : BlowupTower (model (n+1)) Y) (hT : IsGeoTestTower (stabilizedMarked I) T) :
    codimOnePartAlong (geoTransformAlong (stabilizedMarked I) T).N
      (geoTransformAlong (stabilizedMarked I) T).ideal (geoTransformAlong (stabilizedMarked I) T).d=∅ := by
  have hd := stabilized_isInvDomain hM
  exact CodimOnePartTowerAlong.codimOnePartAlong_geoTransformAlong_eq_empty (stabilizedMarked I)
    hd.isWellFormed hd.one_le_d (stabilized_maximal_order (I := I) hM.isWellFormed.isCoherent)
    (initial_codimOne_empty hM) T hT

private theorem current_not_special {q : ℕ} {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) {Y : CMfd (n+1)}
    (T : BlowupTower (model (n+1)) Y) (hT : IsGeoTestTower (stabilizedMarked I) T) (y : Y) :
    ¬ IsSpecial (stabilizedMarked I) T y := by
  have hd := stabilized_isInvDomain hM
  have hw := HomogenizedIdealAlongTower.coeff_homAlong_wEquiv (X := model (n+1))
    (stabilizedMarked I) hd.isWellFormed.isClosedSubmanifold_N hd.isWellFormed.isCoherent hd.one_le_d
  have he := CodimOnePartCanonical.codimOnePartAlong_geoTransformAlong_of_wEquiv
    (X := model (n+1)) (𝔪 := barMarked (stabilizedMarked I)) hw rfl T (bar_test hM T hT)
  rw [current_codimOne_empty hM T hT] at he
  rintro (⟨_,hz⟩ | ⟨hpos,_⟩)
  · rw [he] at hz
    exact hz
  · rw [original_level_zero] at hpos
    omega

private theorem mem_of_spanOn_univ {Y : CMfd (n+1)} {A : GermIdeal (n+1) Y}
    (hA : A.IsCoherent) {y : Y} {g : Y → ℂ} (hg : HolomorphicAt (n+1) g y)
    (hs : IsInSpanOnAt (n := n+1) univ (A.mem y) y g) : A.mem y g := by
  obtain ⟨N,s,a,hs,ha,heq⟩ := hs
  exact mem_of_isInSpanAt_mem hA ⟨hg,N,s,a,hs,ha,heq.mono fun z hz => hz (mem_univ z)⟩

private theorem current_order_positive {q : ℕ} {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) {Y : CMfd (n+1)}
    (T : BlowupTower (model (n+1)) Y) (hT : IsGeoTestTower (stabilizedMarked I) T)
    {y : Y} (hy : y∈(geoTransformAlong (stabilizedMarked I) T).cosupp) :
    1≤nmOrd (geoTransformAlong (stabilizedMarked I) T) y := by
  have hd := stabilized_isInvDomain hM
  have hA := InvDomainTowerAlong.isInvDomain_geoTransformAlong hd T hT
  have hN : (geoTransformAlong (stabilizedMarked I) T).N=univ :=
    (pullback_eq_mul_geoTransformAlong (𝔪 := stabilizedMarked I) rfl hd.isWellFormed.isCoherent T hT).1
  have hmax := isMaximalOrderAlong_geoTransformAlong hd.isWellFormed.isClosedSubmanifold_N
    hd.isWellFormed.isCoherent (stabilized_maximal_order (I := I) hM.isWellFormed.isCoherent) T hT
  have hOne := one_mem_monomial_of_empty_codimOne (geoTransformAlong (stabilizedMarked I) T)
    hA.isWellFormed hN (d_geoTransformAlong (stabilizedMarked I) T) hmax (current_codimOne_empty hM T hT) y
  apply (mem_ordGe_iff hA.isWellFormed hA.isNonzeroAlongAt hy.1 1).mp
  refine ⟨hy.1,?_⟩
  intro g hg
  have hprod := hg.2 (fun _ => 1) hOne
  have hs : IsInSpanOnAt (n := n+1) univ
      ((geoTransformAlong (stabilizedMarked I) T).ideal.mem y) y g := by
    simpa only [hN,one_mul,mul_one] using hprod.2
  have hmem := mem_of_spanOn_univ hA.isWellFormed.isCoherent hg.1 hs
  simpa only [d_geoTransformAlong,stabilizedMarked] using hy.2 g hmem

section FirstStep
variable {q : ℕ} (hn : 0<n) {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) (C : Set (ComplexModel n))
    (hC : C=∅ ∨ C=ResolutionDriver.maxLocus ((invFamily hn q).inv (X := model n) (baseMarked I) .refl)
      (baseMarked I).cosupp)
    {Y : CMfd (n+1)} (π : Y → ComplexModel (n+1))
    (hπ : IsBlowupAlong (n+1) (tangentInclusion n 1 '' C) π)
include hn hM hC

private theorem first_test :
    IsGeoTestTower (X := model (n+1)) (stabilizedMarked I) (.step (X := model (n+1)) .refl (tangentInclusion n 1 '' C) π hπ) :=
  (invFamily (Nat.succ_pos n) (q+1)).isInvValue.isGeoTestTower_of_isCanonical
    (stabilized_isInvDomain hM) _ (firstStep_upper_isCanonical hn hM C hC π hπ)

/-- Nonmonomial order stays exactly one on the actual full ambient cosupport. -/
theorem firstStep_nmOrd_eq_one {y : Y}
    (hy : y∈(geoTransformAlong (X := model (n+1)) (stabilizedMarked I)
      (.step (X := model (n+1)) .refl (tangentInclusion n 1 '' C) π hπ)).cosupp) :
    nmOrd (geoTransformAlong (X := model (n+1)) (stabilizedMarked I)
      (.step (X := model (n+1)) .refl (tangentInclusion n 1 '' C) π hπ)) y=1 := by
  have hd := stabilized_isInvDomain hM
  have ht := first_test hn hM C hC π hπ
  have hc := firstStep_upper_isCanonical hn hM C hC π hπ
  have hf : NonmonomialOrderCanonical.OrdMonotone (X := model (n+1)) (stabilizedMarked I)
      ((invFamily (Nat.succ_pos n) (q+1)).inv (X := model (n+1)) (stabilizedMarked I)) :=
    ordMonotone_genInv _ _
  obtain ⟨hp,hbound⟩ := NonmonomialOrderCanonical.nmOrd_step_le_of_canonical
    (X := model (n+1)) (Nat.succ_pos n) hd hf .refl (tangentInclusion n 1 '' C) π hπ ht hc.2 hy
  have hp1 := stabilized_order_one hM hp
  exact Nat.le_antisymm (hbound.trans_eq hp1) (current_order_positive hM _ ht hy)

/-- The special branch cannot appear along this original full ambient run. -/
theorem firstStep_not_special (y : Y) :
    ¬ IsSpecial (X := model (n+1)) (stabilizedMarked I)
      (.step (X := model (n+1)) .refl (tangentInclusion n 1 '' C) π hπ) y :=
  current_not_special hM _ (first_test hn hM C hC π hπ) y

/-- The actual order clock retains the real one-step tail. -/
theorem firstStep_order_run {y : Y}
    (hy : y∈(geoTransformAlong (X := model (n+1)) (stabilizedMarked I)
      (.step (X := model (n+1)) .refl (tangentInclusion n 1 '' C) π hπ)).cosupp) :
    regimeRun (NonmonomialOrderRegime.OrdRegime (X := model (n+1)) (stabilizedMarked I) 1)
      (.step (X := model (n+1)) .refl (tangentInclusion n 1 '' C) π hπ) y=1 := by
  have hd := stabilized_isInvDomain hM
  have hp := proj_mem_cosupp_of_mem_cosupp hd.isWellFormed.isClosedSubmanifold_N
    hd.isWellFormed.isCoherent _ (first_test hn hM C hC π hπ) hy
  exact regimeRun_step_of (X := model (n+1)) _ .refl (tangentInclusion n 1 '' C) π hπ
    (show NonmonomialOrderRegime.OrdRegime (X := model (n+1)) (stabilizedMarked I) 1 .refl (π y) from
      ⟨hp,stabilized_order_one hM hp⟩)

omit hn hC in
/-- The Step One clock is the real one-step original run, with level zero. -/
theorem firstStep_step_run (y : Y) :
    regimeRun (stepRegime (X := model (n+1)) (stabilizedMarked I) 0)
      (.step (X := model (n+1)) .refl (tangentInclusion n 1 '' C) π hπ) y=1 := by
  exact regimeRun_step_of (X := model (n+1)) _ .refl (tangentInclusion n 1 '' C) π hπ
    (show stepRegime (X := model (n+1)) (stabilizedMarked I) 0 .refl (π y) from
      ⟨rfl,stabilized_not_special hM (π y)⟩)

end FirstStep

/-- Literal original normal contact, with its complete actual history boundary. -/
def normalContact (I : GermIdeal n (ComplexModel n)) :
    MarkedIdeal (n+1) (CMfd.of (n := n+1) (⊤ : Opens (ComplexModel (n+1)))) :=
  contactMarkedKept (X := model (n+1)) (stabilizedMarked I) (addedCoordinate n) .refl ⊤

private theorem normal_tangent : IsTangentDirectionAlong
    (univ : Set (ComplexModel (n+1))) (vanishingIdeal (n := n+1) (zeroPlane n)) 1 univ
    (addedCoordinate n) := by
  have he : zeroCarrier (univ : Set (ComplexModel n))=zeroPlane n := by
    ext z
    change (tangentProjection n 1 z∈(univ : Set (ComplexModel n)) ∧
      actualJointNormalProjection n 1 z=0) ↔ actualJointNormalProjection n 1 z=0
    simp only [mem_univ,true_and]
  simpa only [zeroIdeal,he] using zero_coordinate_tangent (univ : Set (ComplexModel n))

private theorem stabilized_tangent {I : GermIdeal n (ComplexModel n)} :
    IsTangentDirectionAlong (univ : Set (ComplexModel (n+1))) (stabilizedIdeal I) 1 univ
      (addedCoordinate n) := by
  have hnormal : (vanishingIdeal (n := n+1) (zeroPlane n)).IsCoherent := by
    apply CartanIrreducible.cartanCoherence
    exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
      (actualJointNormalProjection n 1).contMDiff
      (FibreDimensionLowerBound.isComplexAnalyticSubset_singleton (0 : ComplexModel 1))
  refine ⟨isOpen_univ,?_,normal_tangent.multiplicity_one⟩
  intro x hx
  exact le_sumIdeal_right hnormal x _ (normal_tangent.mem x hx)

private theorem normalContact_domain {q : ℕ} {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) : IsInvDomain q (normalContact I) := by
  have hd := stabilized_isInvDomain hM
  have h := ContactStageInvDomain.isInvDomain_stage_coeffHomAlong_of_le (X := model (n+1))
    (k := q+1) (stabilizedMarked I) hd.isWellFormed hd.one_le_d hd.dimLE
    ⊤ (stabilized_tangent (I := I)) .refl trivial ⊤ (subset_univ _)
    (by intro y _ _ hz; exact stabilized_not_special hM y (Or.inl ⟨rfl,hz⟩))
    (by intro H hH; cases hH)
  exact h

private theorem normalContact_cosupport {q : ℕ} {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) {Y : CMfd (n+1)}
    (T : BlowupTower (model (n+1)) Y) (hT : IsGeoTestTower (stabilizedMarked I) T) :
    (geoTransformAlong (normalContact I) (restrict ⊤ T)).cosupp=
      (Subtype.val : openPreimage T (⊤ : Opens (ComplexModel (n+1))) → Y) ⁻¹'
        (geoTransformAlong (stabilizedMarked I) T).cosupp := by
  have hd := stabilized_isInvDomain hM
  have hw := HomogenizedIdealAlongTower.coeff_homAlong_wEquiv (X := model (n+1))
    (stabilizedMarked I) hd.isWellFormed.isClosedSubmanifold_N hd.isWellFormed.isCoherent hd.one_le_d
  have hbar := bar_test hM T hT
  have h := ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le (X := model (n+1))
    (stabilizedMarked I) hd.isWellFormed.isClosedSubmanifold_N hd.isWellFormed.isCoherent hd.one_le_d
    ⊤ (stabilized_tangent (I := I)) .refl T (by simpa only [BlowupTower.refl_append] using hbar) ⊤ (subset_univ _)
  exact h.2.trans (congrArg (fun A : Set Y =>
    (Subtype.val : openPreimage T (⊤ : Opens (ComplexModel (n+1))) → Y) ⁻¹' A) (by simpa only [BlowupTower.refl_append] using ((hw.2 T).2 hbar)))

private theorem original_section_cosupport {I : GermIdeal n (ComplexModel n)}
    (hI : I.IsCoherent) {x : ComplexModel n} (hx : x∈(baseMarked I).cosupp) :
    tangentInclusion n 1 x∈(stabilizedMarked I).cosupp := by
  rw [stabilized_cosupport hI]
  exact ⟨by simpa only [tangentProjection_tangentInclusion] using hx,by simp [zeroFunction]⟩

private theorem normalContact_initial_value {q : ℕ} (hn : 0<n) {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) (x : ComplexModel n) (hx : x∈(baseMarked I).cosupp) :
    (invFamily (Nat.succ_pos n) q).inv (normalContact I) .refl
      ⟨tangentInclusion n 1 x,mem_univ _⟩ =
      (invFamily hn q).inv (X := model n) (baseMarked I) .refl x := by
  let J := (stabilizedMarked I : MarkedIdeal (n+1) (model (n+1)))
  let R := invFamily (Nat.succ_pos n) q
  have hd := stabilized_isInvDomain hM
  have hp := original_section_cosupport hM.isWellFormed.isCoherent hx
  have hbarp : tangentInclusion n 1 x∈(barMarked (X := model (n+1)) J).cosupp := by
    rw [cosupp_barMarked (X := model (n+1)) J hd.isWellFormed hd.one_le_d]
    exact hp
  have hD := Seq.StepOneCanonicalTail.lowerDataL_refl (X := model (n+1)) J (k := q+1) R
    hd.isWellFormed hd.one_le_d (Nat.succ_pos n) (stabilized_maximal_order (I := I) hM.isWellFormed.isCoherent)
    hd.dimLE .refl trivial hbarp ⟨rfl,stabilized_not_special hM _⟩
  have hAnchor := Seq.ContactLowerValue.lowerValueL_zero_eq (X := model (n+1)) R J hd.isWellFormed
    hd.one_le_d .refl .refl trivial (stabilized_tangent (I := I)) ⊤ (subset_univ _)
    (by intro H hH; cases hH) (normalContact_domain hM) trivial (mem_univ _) hbarp hD
  have hv := stabilized_stepOne_initial_value hn hM x hx
  simp only [Seq.StepOneValueMasked.stepOneInvM,Seq.StepOneValueMasked.stepOneInvL,
    stabilized_not_special hM _,if_false] at hv
  have hSecond := congrArg (fun v : ℕ ×ₗ WithTop (ValTy q) => (ofLex v).2) hv
  change Seq.StepOneValueMasked.lowerValueL (X := model (n+1)) R J
    (StepOneValueMasked.lowerMarkedM (X := model (n+1)) J) 0 .refl .refl (tangentInclusion n 1 x) =
      (((invFamily hn q).inv (X := model n) (baseMarked I) .refl x) : WithTop (ValTy q)) at hSecond
  exact WithTop.coe_injective (hAnchor.symm.trans hSecond)

private theorem contact_initial_cosupp_iff {q : ℕ} {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) (p : (⊤ : Opens (ComplexModel (n+1)))) :
    p∈(normalContact I).cosupp ↔ p.val∈(stabilizedMarked I).cosupp := by
  exact Set.ext_iff.mp (normalContact_cosupport hM .refl trivial) p

private theorem contact_initial_full_value {q : ℕ} (hn : 0<n) {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) (p : (⊤ : Opens (ComplexModel (n+1))))
    (hp : p∈(normalContact I).cosupp) :
    (invFamily (Nat.succ_pos n) (q+1)).inv (X := model (n+1)) (stabilizedMarked I) .refl p.val=
      initialEmbedding q ((invFamily (Nat.succ_pos n) q).inv (normalContact I) .refl p) := by
  have hpJ := (contact_initial_cosupp_iff hM p).mp hp
  have hpPlane := hpJ
  rw [stabilized_cosupport (I := I) hM.isWellFormed.isCoherent] at hpPlane
  let x := tangentProjection n 1 p.val
  have he : tangentInclusion n 1 x=p.val := by
    have h0 : actualJointNormalProjection n 1 p.val=0 := hpPlane.2
    simpa only [HironakaActualIntrinsicStableAmbientIso.join,h0,map_zero,add_zero] using
      (join_projections (n := n) (m := 1) p.val)
  have hpEq : (⟨tangentInclusion n 1 x,mem_univ _⟩ : (⊤ : Opens (ComplexModel (n+1))))=p := Subtype.ext he
  have hLower := normalContact_initial_value hn hM x hpPlane.1
  have hUpper := stabilized_initial_value hn hM x hpPlane.1
  exact (congrArg (fun z => (invFamily (Nat.succ_pos n) (q+1)).inv
      (X := model (n+1)) (stabilizedMarked I) .refl z) he).symm.trans
    (hUpper.trans (congrArg (initialEmbedding q)
      (hLower.symm.trans (congrArg (fun z => (invFamily (Nat.succ_pos n) q).inv (normalContact I) .refl z) hpEq))))

private theorem contact_initial_maximum {q : ℕ} (hn : 0<n) {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) :
    ResolutionDriver.maxLocus ((invFamily (Nat.succ_pos n) q).inv (normalContact I) .refl)
      (normalContact I).cosupp =
      (Subtype.val : (⊤ : Opens (ComplexModel (n+1))) → ComplexModel (n+1)) ⁻¹'
        ResolutionDriver.maxLocus ((invFamily (Nat.succ_pos n) (q+1)).inv (X := model (n+1))
          (stabilizedMarked I) .refl) (stabilizedMarked I).cosupp := by
  ext p
  constructor
  · rintro ⟨hp,hmax⟩
    refine ⟨(contact_initial_cosupp_iff hM p).mp hp,?_⟩
    intro z hz
    let r : (⊤ : Opens (ComplexModel (n+1))) := ⟨z,mem_univ _⟩
    have hr : r∈(normalContact I).cosupp := (contact_initial_cosupp_iff hM r).mpr hz
    have hvp := contact_initial_full_value hn hM p hp
    have hvr := contact_initial_full_value hn hM r hr
    exact hvr ▸ (hvp ▸ (initialEmbedding q).monotone (hmax r hr))
  · rintro ⟨hp,hmax⟩
    have hpK := (contact_initial_cosupp_iff hM p).mpr hp
    refine ⟨hpK,?_⟩
    intro z hz
    have h := hmax z.val ((contact_initial_cosupp_iff hM z).mp hz)
    have hvp := contact_initial_full_value hn hM p hpK
    have hvz := contact_initial_full_value hn hM z hz
    exact (initialEmbedding q).le_iff_le.mp (hvz ▸ (hvp ▸ h))

section FirstContact
variable {q : ℕ} (hn : 0<n) {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) (C : Set (ComplexModel n))
    (hC : C=∅ ∨ C=ResolutionDriver.maxLocus ((invFamily hn q).inv (X := model n) (baseMarked I) .refl)
      (baseMarked I).cosupp)
    {Y : CMfd (n+1)} (π : Y → ComplexModel (n+1))
    (hπ : IsBlowupAlong (n+1) (tangentInclusion n 1 '' C) π)
include hn hM hC

/-- The literal original normal contact has its own genuine canonical first tail. -/
theorem firstStep_contact_isCanonical :
    IsInvDomain q (normalContact I) ∧
      IsCanonical (normalContact I) ((invFamily (Nat.succ_pos n) q).inv (normalContact I))
        (restrict ⊤ (.step (X := model (n+1)) .refl (tangentInclusion n 1 '' C) π hπ)) := by
  refine ⟨normalContact_domain hM,trivial,?_⟩
  change (Subtype.val : (⊤ : Opens (ComplexModel (n+1))) → ComplexModel (n+1)) ⁻¹'
      (tangentInclusion n 1 '' C)=∅ ∨
    (Subtype.val : (⊤ : Opens (ComplexModel (n+1))) → ComplexModel (n+1)) ⁻¹'
      (tangentInclusion n 1 '' C)=ResolutionDriver.maxLocus
        ((invFamily (Nat.succ_pos n) q).inv (normalContact I) .refl) (normalContact I).cosupp
  rcases (firstStep_upper_isCanonical hn hM C hC π hπ).2 with hEmpty | hMax
  · left
    rw [hEmpty,preimage_empty]
  · right
    exact (congrArg (fun A : Set (ComplexModel (n+1)) =>
      (Subtype.val : (⊤ : Opens (ComplexModel (n+1))) → ComplexModel (n+1)) ⁻¹' A) hMax).trans
      (contact_initial_maximum hn hM).symm

/-- Complete transformed cosupport dictionary along the actual born-boundary tail. -/
theorem firstStep_contact_cosupport :
    (geoTransformAlong (normalContact I)
      (restrict ⊤ (.step (X := model (n+1)) .refl (tangentInclusion n 1 '' C) π hπ))).cosupp=
      (Subtype.val : openPreimage (.step (X := model (n+1)) .refl (tangentInclusion n 1 '' C) π hπ)
        (⊤ : Opens (ComplexModel (n+1))) → Y) ⁻¹'
        (geoTransformAlong (X := model (n+1)) (stabilizedMarked I)
          (.step (X := model (n+1)) .refl (tangentInclusion n 1 '' C) π hπ)).cosupp :=
  normalContact_cosupport hM _ (first_test hn hM C hC π hπ)

end FirstContact

private theorem initial_stepOne_value_at {q : ℕ} (hn : 0<n) {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) (z : ComplexModel (n+1))
    (hz : z∈(stabilizedMarked I).cosupp) :
    Seq.StepOneValueMasked.stepOneInvM (X := model (n+1)) (invFamily (Nat.succ_pos n) q)
      (stabilizedMarked I) .refl z =
      toLex (0,(((invFamily hn q).inv (X := model n) (baseMarked I) .refl
        (tangentProjection n 1 z)) : WithTop (ValTy q))) := by
  have hp := hz
  rw [stabilized_cosupport (I := I) hM.isWellFormed.isCoherent] at hp
  have he : tangentInclusion n 1 (tangentProjection n 1 z)=z := by
    have h0 : actualJointNormalProjection n 1 z=0 := hp.2
    simpa only [HironakaActualIntrinsicStableAmbientIso.join,h0,map_zero,add_zero] using
      (join_projections (n := n) (m := 1) z)
  exact (congrArg (fun p => Seq.StepOneValueMasked.stepOneInvM (X := model (n+1))
      (invFamily (Nat.succ_pos n) q) (stabilizedMarked I) .refl p) he).symm.trans
    (stabilized_stepOne_initial_value hn hM (tangentProjection n 1 z) hp.1)

private theorem initial_stepOne_maximum {q : ℕ} (hn : 0<n) {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) :
    ResolutionDriver.maxLocus
      (Seq.StepOneValueMasked.stepOneInvM (X := model (n+1)) (invFamily (Nat.succ_pos n) q)
        (stabilizedMarked I) .refl) (stabilizedMarked I).cosupp =
      zeroCarrier (ResolutionDriver.maxLocus ((invFamily hn q).inv (X := model n) (baseMarked I) .refl)
        (baseMarked I).cosupp) := by
  ext z
  constructor
  · rintro ⟨hz,hmax⟩
    have hz' := hz
    rw [stabilized_cosupport (I := I) hM.isWellFormed.isCoherent] at hz'
    refine ⟨⟨hz'.1,?_⟩,hz'.2⟩
    intro y hy
    have hyJ := original_section_cosupport hM.isWellFormed.isCoherent hy
    have h := hmax (tangentInclusion n 1 y) hyJ
    have hvy := stabilized_stepOne_initial_value hn hM y hy
    have hvz := initial_stepOne_value_at hn hM z hz
    have h' := hvy ▸ (hvz ▸ h)
    exact WithTop.coe_le_coe.mp ((Prod.Lex.toLex_le_toLex.mp h').resolve_left (Nat.lt_irrefl 0)).2
  · rintro ⟨⟨hz,hmax⟩,hplane⟩
    have hzJ : z∈(stabilizedMarked I).cosupp := by
      rw [stabilized_cosupport (I := I) hM.isWellFormed.isCoherent]
      exact ⟨hz,hplane⟩
    refine ⟨hzJ,?_⟩
    intro y hy
    have hy' := hy
    rw [stabilized_cosupport (I := I) hM.isWellFormed.isCoherent] at hy'
    have hvy := initial_stepOne_value_at hn hM y hy
    have hvz := initial_stepOne_value_at hn hM z hzJ
    rw [hvy,hvz]
    exact Prod.Lex.toLex_le_toLex.mpr (Or.inr ⟨rfl,WithTop.coe_le_coe.mpr (hmax _ hy'.1)⟩)

section FirstAnchor
variable {q : ℕ} (hn : 0<n) {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) (C : Set (ComplexModel n))
    (hC : C=∅ ∨ C=ResolutionDriver.maxLocus ((invFamily hn q).inv (X := model n) (baseMarked I) .refl)
      (baseMarked I).cosupp)
    {Y : CMfd (n+1)} (π : Y → ComplexModel (n+1))
    (hπ : IsBlowupAlong (n+1) (tangentInclusion n 1 '' C) π)
include hn hM hC

private theorem first_stepOne_canonical :
    IsCanonical (X := model (n+1)) (stabilizedMarked I)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) (stabilizedMarked I))
      (.step (X := model (n+1)) .refl (tangentInclusion n 1 '' C) π hπ) := by
  refine ⟨trivial,?_⟩
  change tangentInclusion n 1 '' C=∅ ∨ tangentInclusion n 1 '' C=ResolutionDriver.maxLocus
    (Seq.StepOneValueMasked.stepOneInvM (X := model (n+1)) (invFamily (Nat.succ_pos n) q)
      (stabilizedMarked I) .refl) (stabilizedMarked I).cosupp
  rcases hC with hEmpty | hMax
  · left
    rw [hEmpty,image_empty]
  · right
    rw [initial_stepOne_maximum hn hM,hMax,section_image]

/-- The selected original Step One value is the literal normal contact's real historical value. -/
theorem firstStep_stepOne_value {y : Y}
    (hy : y∈(geoTransformAlong (X := model (n+1)) (stabilizedMarked I)
      (.step (X := model (n+1)) .refl (tangentInclusion n 1 '' C) π hπ)).cosupp) :
    Seq.StepOneValueMasked.stepOneInvM (X := model (n+1)) (invFamily (Nat.succ_pos n) q)
      (stabilizedMarked I) (.step (X := model (n+1)) .refl (tangentInclusion n 1 '' C) π hπ) y =
      toLex (0,(((invFamily (Nat.succ_pos n) q).inv (normalContact I)
        (restrict ⊤ (.step (X := model (n+1)) .refl (tangentInclusion n 1 '' C) π hπ))
        ⟨y,mem_univ _⟩) : WithTop (ValTy q))) := by
  let J := (stabilizedMarked I : MarkedIdeal (n+1) (model (n+1)))
  let R := invFamily (Nat.succ_pos n) q
  let S : BlowupTower (model (n+1)) Y := .step .refl (tangentInclusion n 1 '' C) π hπ
  have hd := stabilized_isInvDomain hM
  have hmax := stabilized_maximal_order (I := I) hM.isWellFormed.isCoherent
  have ht := first_test hn hM C hC π hπ
  have hbar := bar_test hM S ht
  have hcan := first_stepOne_canonical hn hM C hC π hπ
  have hbarcan := (Seq.StepOneBridge.isCanonical_iff (X := model (n+1)) (k := q+1)
    R J hd hmax (Nat.succ_pos n) S).mp hcan
  have hnsp : ¬ IsSpecial (X := model (n+1)) J S y := firstStep_not_special hn hM C hC π hπ y
  have hw := HomogenizedIdealAlongTower.coeff_homAlong_wEquiv (X := model (n+1))
    J hd.isWellFormed.isClosedSubmanifold_N hd.isWellFormed.isCoherent hd.one_le_d
  have hp : y∈(geoTransformAlong (barMarked (X := model (n+1)) J) S).cosupp :=
    ((hw.2 S).2 hbar).symm ▸ hy
  have hD := Seq.StepOneCanonicalTail.hasLowerDataL_of_isCanonical (X := model (n+1)) J (k := q+1) R
    hd.isWellFormed hd.one_le_d (Nat.succ_pos n) hmax hd.dimLE S hbar hbarcan y hp hnsp
  have hRun := firstStep_step_run (I := I) hM C π hπ y
  have hLevel := original_level_zero I S y
  change Seq.StepOneValueMasked.LowerDataL (X := model (n+1)) R J (StepOneValueMasked.lowerMarkedM (X := model (n+1)) J)
    (level (X := model (n+1)) J S y) (head S (regimeRun (stepRegime (X := model (n+1)) J (level (X := model (n+1)) J S y)) S y))
      (tail S (regimeRun (stepRegime (X := model (n+1)) J (level (X := model (n+1)) J S y)) S y)) y at hD
  rw [hLevel,hRun] at hD
  have hContact := firstStep_contact_isCanonical hn hM C hC π hπ
  have hAnchor := Seq.ContactLowerValue.lowerValueL_zero_eq (X := model (n+1)) R J hd.isWellFormed
    hd.one_le_d .refl S (by simpa only [BlowupTower.refl_append] using hbar)
    (stabilized_tangent (I := I)) ⊤ (subset_univ _) (by intro H hH; cases hH)
    hContact.1 hContact.2 (mem_univ _) (by simpa only [BlowupTower.refl_append] using hp) hD
  have hValue : Seq.StepOneValueMasked.stepOneInvM (X := model (n+1)) R J S y=
      toLex (0,Seq.StepOneValueMasked.lowerValueL (X := model (n+1)) R J
        (StepOneValueMasked.lowerMarkedM (X := model (n+1)) J) 0 .refl S y) := by
    simp only [Seq.StepOneValueMasked.stepOneInvM,Seq.StepOneValueMasked.stepOneInvL,if_neg hnsp]
    rw [hLevel,hRun]
    rfl
  exact hValue.trans (congrArg (fun v : WithTop (ValTy q) => toLex (0,v)) hAnchor)

end FirstAnchor

private theorem original_companion_equiv {I : GermIdeal n (ComplexModel n)}
    (hI : I.IsCoherent) :
    RestrictEquiv (compAt (X := model (n+1)) (stabilizedMarked I) 1 .refl)
      (MarkedIdeal.pullback (Subtype.val : ordMask (M := model (n+1)) (stabilizedMarked I) 1 → ComplexModel (n+1))
        (stabilizedMarked I)) := by
  let O := ordMask (M := model (n+1)) (stabilizedMarked I) 1
  change RestrictEquiv
    (companionAlong (X := CMfd.of (n := n+1) O) ((Subtype.val : O → ComplexModel (n+1)) ⁻¹' univ) []
      (nonmonomialPartAlong (n+1) ((Subtype.val : O → ComplexModel (n+1)) ⁻¹' univ)
        (GermIdeal.pullback (m := n+1) (Subtype.val : O → ComplexModel (n+1)) (stabilizedIdeal I)) [])
      (monomialPartAlong (n+1) ((Subtype.val : O → ComplexModel (n+1)) ⁻¹' univ)
        (GermIdeal.pullback (m := n+1) (Subtype.val : O → ComplexModel (n+1)) (stabilizedIdeal I)) []) 1 1)
    (⟨(Subtype.val : O → ComplexModel (n+1)) ⁻¹' univ, [],
      GermIdeal.pullback (m := n+1) (Subtype.val : O → ComplexModel (n+1)) (stabilizedIdeal I), 1⟩ : MarkedIdeal (n+1) O)
  rw [companionAlong,if_neg (Nat.lt_irrefl 1),nonmonomialPartAlong_nil_eq_restrictOn]
  exact ⟨rfl,rfl,rfl,restrictLe_restrictOn,
    restrictLe_self_restrictOn (isCoherent_pullback contMDiff_subtype_val (stabilizedIdeal_isCoherent hI))⟩

section FullAnchor
variable {q : ℕ} (hn : 0<n) {I : GermIdeal n (ComplexModel n)}
    (hM : IsInvDomain q (baseMarked I)) (C : Set (ComplexModel n))
    (hC : C=∅ ∨ C=ResolutionDriver.maxLocus ((invFamily hn q).inv (X := model n) (baseMarked I) .refl)
      (baseMarked I).cosupp)
    {Y : CMfd (n+1)} (π : Y → ComplexModel (n+1))
    (hπ : IsBlowupAlong (n+1) (tangentInclusion n 1 '' C) π)
include hn hM hC

private theorem original_companion_historical_value {y : Y}
    (hy : y∈(geoTransformAlong (X := model (n+1)) (stabilizedMarked I)
      (.step (X := model (n+1)) .refl (tangentInclusion n 1 '' C) π hπ)).cosupp)
    (hp : π y∈ordMask (M := model (n+1)) (stabilizedMarked I) 1) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q)
      (X := CMfd.of (n := n+1) (ordMask (M := model (n+1)) (stabilizedMarked I) 1))
      (compAt (X := model (n+1)) (stabilizedMarked I) 1 .refl)
      (restrict (ordMask (M := model (n+1)) (stabilizedMarked I) 1)
        (.step (X := model (n+1)) .refl (tangentInclusion n 1 '' C) π hπ)) ⟨y,hp⟩ =
      toLex (0,(((invFamily (Nat.succ_pos n) q).inv (normalContact I)
        (restrict ⊤ (.step (X := model (n+1)) .refl (tangentInclusion n 1 '' C) π hπ))
        ⟨y,mem_univ _⟩) : WithTop (ValTy q))) := by
  have hI : I.IsCoherent := hM.isWellFormed.isCoherent
  let J := (stabilizedMarked I : MarkedIdeal (n+1) (model (n+1)))
  let R := invFamily (Nat.succ_pos n) q
  let S : BlowupTower (model (n+1)) Y := .step .refl (tangentInclusion n 1 '' C) π hπ
  let O := ordMask (M := model (n+1)) J 1
  let A : MarkedIdeal (n+1) O := compAt (X := model (n+1)) J 1 .refl
  let P := MarkedIdeal.pullback (Subtype.val : O → ComplexModel (n+1)) J
  let p : openPreimage S O := ⟨y,hp⟩
  have hd := stabilized_isInvDomain hM
  have hmax := stabilized_maximal_order hI
  have hA : IsInvDomain (q+1) A := GeneralCompare.isInvDomain_compAt
    (X := model (n+1)) (Nat.succ_pos n) (by rfl) .refl hd
  have hAM : IsMaximalOrderAlong A.N A.ideal A.d :=
    GeneralCompare.isMaximalOrderAlong_compAt (X := model (n+1)) (Nat.succ_pos n) 1 .refl hd
  have hP : IsInvDomain (q+1) P := InvDomainTowerAlong.isInvDomain_pullback_val O hd
  obtain ⟨_,_,hPM,_⟩ := StepOneRestrictOpen.hypotheses_restrict (X := model (n+1)) J O
    hd.isWellFormed hd.one_le_d hmax hd.dimLE
  have hEq : RestrictEquiv A P := original_companion_equiv hI
  have hEqPA : RestrictEquiv P A :=
    ⟨hEq.N_eq.symm,hEq.E_eq.symm,hEq.d_eq.symm,hEq.N_eq ▸ hEq.ge,hEq.N_eq ▸ hEq.le⟩
  have hF := StepOneSeq.isMaxOrderValue_stepOneInvM (k := q+1) R (Nat.succ_pos n)
  have hCanJ := first_stepOne_canonical hn hM C hC π hπ
  have hCanP := hF.isCanonical_restrict (X := model (n+1)) hd hmax O S hCanJ
  have hCanA := hF.isCanonical_of_restrictEquiv (X := CMfd.of (n := n+1) O)
    hP hPM hA hAM hEqPA (restrict O S) hCanP
  have hcsP := ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict (X := model (n+1))
    (𝔪 := J) hd.isWellFormed.isClosedSubmanifold_N hd.isWellFormed.isCoherent O S
    (first_test hn hM C hC π hπ)
  have hpP : p∈(geoTransformAlong P (restrict O S)).cosupp := hcsP.symm ▸ hy
  have hcsA := MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.cosupp_admissible_geoTransformAlong hEq
    hA.isWellFormed.isClosedSubmanifold_N.1 hA.isWellFormed.isCoherent hP.isWellFormed.isCoherent (restrict O S)
  have hpA : p∈(geoTransformAlong A (restrict O S)).cosupp := hcsA.1.symm ▸ hpP
  have hRep := hF.representative (X := CMfd.of (n := n+1) O) A P hA hAM hP hPM hEq (restrict O S) hCanA p hpA
  have hRest := hF.restrictOpen (X := model (n+1)) J hd hmax O S hCanJ p hy
  exact hRep.trans (hRest.trans (firstStep_stepOne_value hn hM C hC π hπ hy))

/-- The genuine original full ambient first history is the explicit finite
depth shift of the literal original normal contact history, born boundary kept. -/
theorem firstStep_historical_value {y : Y}
    (hy : y∈(geoTransformAlong (X := model (n+1)) (stabilizedMarked I)
      (.step (X := model (n+1)) .refl (tangentInclusion n 1 '' C) π hπ)).cosupp) :
    (invFamily (Nat.succ_pos n) (q+1)).inv (X := model (n+1)) (stabilizedMarked I)
      (.step (X := model (n+1)) .refl (tangentInclusion n 1 '' C) π hπ) y =
      initialEmbedding q ((invFamily (Nat.succ_pos n) q).inv (normalContact I)
        (restrict ⊤ (.step (X := model (n+1)) .refl (tangentInclusion n 1 '' C) π hπ)) ⟨y,mem_univ _⟩) := by
  let J := (stabilizedMarked I : MarkedIdeal (n+1) (model (n+1)))
  let R := invFamily (Nat.succ_pos n) q
  let S : BlowupTower (model (n+1)) Y := .step .refl (tangentInclusion n 1 '' C) π hπ
  let F := fun {X : CMfd (n+1)} (K : MarkedIdeal (n+1) X) {Z : CMfd (n+1)}
    (T : BlowupTower X Z) (z : Z) => Seq.StepOneValueMasked.stepOneInvM (X := X) R K (Y := Z) T z
  have hOrd := firstStep_nmOrd_eq_one hn hM C hC π hπ hy
  have hRun := firstStep_order_run hn hM C hC π hπ hy
  have hp : π y∈ordMask (M := model (n+1)) J 1 := by
    rw [stabilized_initial_orderMask (I := I) hM.isWellFormed.isCoherent]
    trivial
  have hLower := original_companion_historical_value hn hM C hC π hπ hy hp
  rw [invFamily_succ,generalStep_inv]
  change genInv (X := model (n+1)) F J S y=_
  rw [genInv_of_nmOrd_ne_zero (X := model (n+1)) F J S hOrd (by decide),hRun]
  change toLex (1,Sum.inrₗ (genLowerValue (X := model (n+1)) F J 1 .refl S y))=_
  have hGen := genLowerValue_eq_of_mem (X := model (n+1)) (T₀ := .refl) (T₁ := S)
    (y := y) F J hp
  have hCoefficient := hGen.trans
    (congrArg (fun v : ℕ ×ₗ WithTop (ValTy q) => (v : WithTop (ℕ ×ₗ WithTop (ValTy q)))) hLower)
  exact congrArg (fun v : WithTop (ℕ ×ₗ WithTop (ValTy q)) => (toLex (1,Sum.inrₗ v) : ValTy (q+1))) hCoefficient

/-- The next full ambient maximum is exactly the actual historical contact maximum. -/
theorem firstStep_historical_maximum_locus :
    ResolutionDriver.maxLocus ((invFamily (Nat.succ_pos n) (q+1)).inv (X := model (n+1))
      (stabilizedMarked I) (.step (X := model (n+1)) .refl (tangentInclusion n 1 '' C) π hπ))
      (geoTransformAlong (X := model (n+1)) (stabilizedMarked I)
        (.step (X := model (n+1)) .refl (tangentInclusion n 1 '' C) π hπ)).cosupp =
    (Subtype.val : openPreimage (.step (X := model (n+1)) .refl (tangentInclusion n 1 '' C) π hπ)
      (⊤ : Opens (ComplexModel (n+1))) → Y) ''
      ResolutionDriver.maxLocus ((invFamily (Nat.succ_pos n) q).inv (normalContact I)
        (restrict ⊤ (.step (X := model (n+1)) .refl (tangentInclusion n 1 '' C) π hπ)))
        (geoTransformAlong (normalContact I)
          (restrict ⊤ (.step (X := model (n+1)) .refl (tangentInclusion n 1 '' C) π hπ))).cosupp := by
  let S : BlowupTower (model (n+1)) Y := .step .refl (tangentInclusion n 1 '' C) π hπ
  have hcs := firstStep_contact_cosupport hn hM C hC π hπ
  ext y
  constructor
  · rintro ⟨hy,hmax⟩
    let p : openPreimage S (⊤ : Opens (ComplexModel (n+1))) := ⟨y,mem_univ _⟩
    have hp : p∈(geoTransformAlong (normalContact I) (restrict ⊤ S)).cosupp := (Set.ext_iff.mp hcs p).mpr hy
    refine ⟨p,⟨hp,?_⟩,rfl⟩
    intro z hz
    have hzJ : z.val∈(geoTransformAlong (stabilizedMarked I) S).cosupp := (Set.ext_iff.mp hcs z).mp hz
    have h := hmax z.val hzJ
    have hvz := firstStep_historical_value hn hM C hC π hπ hzJ
    have hvy := firstStep_historical_value hn hM C hC π hπ hy
    exact (initialEmbedding q).le_iff_le.mp (hvz ▸ (hvy ▸ h))
  · rintro ⟨p,⟨hp,hmax⟩,rfl⟩
    have hpJ : p.val∈(geoTransformAlong (stabilizedMarked I) S).cosupp := (Set.ext_iff.mp hcs p).mp hp
    refine ⟨hpJ,?_⟩
    intro z hz
    let r : openPreimage S (⊤ : Opens (ComplexModel (n+1))) := ⟨z,mem_univ _⟩
    have hr : r∈(geoTransformAlong (normalContact I) (restrict ⊤ S)).cosupp := (Set.ext_iff.mp hcs r).mpr hz
    have h := (initialEmbedding q).monotone (hmax r hr)
    have hvz := firstStep_historical_value hn hM C hC π hπ hz
    have hvp := firstStep_historical_value hn hM C hC π hπ hpJ
    exact hvz.symm ▸ (hvp.symm ▸ h)

end FullAnchor

/-- The contact's actual born member is the trace of the full ambient born member. -/
theorem firstStep_contact_boundary (I : GermIdeal n (ComplexModel n)) (C : Set (ComplexModel n))
    {Y : CMfd (n+1)} (π : Y → ComplexModel (n+1))
    (hπ : IsBlowupAlong (n+1) (tangentInclusion n 1 '' C) π) :
    (geoTransformAlong (normalContact I)
      (restrict ⊤ (.step (X := model (n+1)) .refl (tangentInclusion n 1 '' C) π hπ))).E=
      [(Subtype.val : openPreimage (.step (X := model (n+1)) .refl (tangentInclusion n 1 '' C) π hπ)
        (⊤ : Opens (ComplexModel (n+1))) → Y) ⁻¹' (π ⁻¹' (tangentInclusion n 1 '' C))] := rfl

end
end TranscendentalNakamaye.Pending.HironakaDisjointFirstStepHistoricalAnchor
