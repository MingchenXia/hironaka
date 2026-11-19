import Hironaka.Resolution.HironakaActualSectionCompanion

/-! Arbitrary ordered-boundary initial counts, special regimes and the whole monomial branch on the actual zero section. Positive-order all-index induction and historical recurrence remain separate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualSectionInitialBoundaryRegime
noncomputable section
open Hironaka.HolomorphicIdealSheaves MarkedIdeals
  HironakaActualOpenZeroSectionDifferentials HironakaRelativeNormalIdeal
  HironakaActualCentreJointJets HironakaActualIntrinsicStableAmbientIso
  HironakaActualSectionInitialValues HironakaActualSectionBoundaryDimension
  HironakaActualSectionCompanion BoundaryCount MemberInterLocusAlong BlowupTowers
  IdealOrderArithmetic GermIdealOrder IdealWeightPowers RelativePrincipalizationSpan
  GermIdealPullbackCalculus InvertibleIdealQuotient HadamardBridge
  HironakaSharpOriginalProductTraceOrder NonmonomialOrderLocal
  HomogenizedIdealAlong CoefficientIdealRestriction CanonicalCentres
  DerivativeIdealAlong DerivativeIdealAlongCoherent CoefficientIdeal HomogenizedGlueing
  Hironaka.BlowupSequences GiraudAlong HomogenizedEquivalence
variable {n : ℕ} {U : TopologicalSpace.Opens (ComplexModel n)}

private theorem projection_section (x : U) : projection U (zeroSection U x)=x := by
  apply Subtype.ext
  exact tangentProjection_tangentInclusion n 1 x

/-- Counts retain every original ordered member, including empty ones. -/
theorem boundaryCount_section (E : List (Set U)) (x : U) :
    boundaryCount (E.map (projection U ⁻¹' ·)) (zeroSection U x)=boundaryCount E x := by
  classical
  rw [boundaryCount_map]
  change (Finset.univ.filter (fun i : Fin E.length =>
    projection U (zeroSection U x) ∈ E.get i)).card = boundaryCount E x
  rw [projection_section]
  rfl

theorem level_section_refl (A : Set U) (E : List (Set U))
    (J : GermIdeal (n+1) (productOpen U)) (d : ℕ) (x : U) :
    StepOneValue.level (X := CMfd.of (n := n+1) (productOpen U))
      (⟨liftedCarrier A,E.map (projection U ⁻¹' ·),J,d⟩ : MarkedIdeal (n+1) (productOpen U))
      .refl (zeroSection U x)=
    StepOneValue.level (X := CMfd.of (n := n) U)
      (⟨A,E,GermIdeal.pullback (m := n) (zeroSection U) J,d⟩ : MarkedIdeal n U) .refl x := by
  change boundaryCount ((E.map (projection U ⁻¹' ·)).take (E.map (projection U ⁻¹' ·)).length)
    (zeroSection U x) = boundaryCount (E.take E.length) x
  rw [List.take_length,List.take_length]
  exact boundaryCount_section E x

/-- Entire original member-intersection locus under the literal section. -/
theorem memberInterLocus_section_iff (A S : Set U) (E : List (Set U)) (x : U) :
    zeroSection U x∈memberInterLocus (liftedCarrier A) (E.map (projection U ⁻¹' ·)) (liftedCarrier S) ↔
      x∈memberInterLocus A E S := by
  have hmem (B : Set U) (y : U) : zeroSection U y∈liftedCarrier B ↔ y∈B := by
    change (projection U (zeroSection U y)∈B ∧ _=0) ↔ y∈B
    simp only [projection_section]
    simp [zeroSection]
  rw [mem_memberInterLocus_iff,mem_memberInterLocus_iff]
  constructor
  · rintro ⟨hx,hnear⟩
    refine ⟨(hmem S x).mp hx,?_⟩
    filter_upwards [(zeroSection_contMDiff U).continuous.continuousAt.eventually hnear] with y hy hyA hyE
    apply (hmem S y).mp
    apply hy ((hmem A y).mpr hyA)
    intro K hK hxK
    obtain ⟨H,hH,rfl⟩ := List.mem_map.mp hK
    change zeroSection U x ∈ projection U ⁻¹' H at hxK
    simpa only [Set.mem_preimage,projection_section] using
      hyE H hH (by simpa only [Set.mem_preimage,projection_section] using hxK)
  · rintro ⟨hx,hnear⟩
    refine ⟨(hmem S x).mpr hx,?_⟩
    have hp : Tendsto (projection U) (𝓝 (zeroSection U x)) (𝓝 x) := by
      simpa only [projection_section] using (projection_contMDiff U).continuous.tendsto (zeroSection U x)
    filter_upwards [hp.eventually hnear] with z hz hzA hzE
    refine ⟨hz hzA.1 ?_,hzA.2⟩
    intro H hH hxH
    exact hzE (projection U ⁻¹' H) (List.mem_map.mpr ⟨H,hH,rfl⟩)
      (by simpa only [Set.mem_preimage,projection_section] using hxH)

private theorem section_homogenizedIdeal (A : Set U) (hA : IsClosedSubmanifold n A)
    (J : GermIdeal (n+1) (productOpen U)) (hJ : J.IsCoherent) (d : ℕ) :
    GermIdeal.pullback (m := n) (zeroSection U) (homogenizedIdealAlong (liftedCarrier A) J d)=
      homogenizedIdealAlong A (GermIdeal.pullback (m := n) (zeroSection U) J) d := by
  unfold homogenizedIdealAlong
  rw [HironakaActualNonregularCoefficientNaturality.pullback_homSum (zeroSection_contMDiff U)
    (fun i => iterDerivIdealAlong (liftedCarrier A) J i) (tangentIdealAlong (liftedCarrier A) J d) d
    (fun i _ {_ _} hg => holomorphicAt_of_mem_iterDerivIdealAlong
      (fun _ _ hj => GermIdeal.IsCoherent.holomorphicAt_mem hJ hj) i _ _ hg)
    (fun {_ _} hg => holomorphicAt_of_mem_iterDerivIdealAlong
      (N := liftedCarrier A) (fun _ _ hj => GermIdeal.IsCoherent.holomorphicAt_mem hJ hj) (d-1) _ _ hg)]
  exact homSum_congr (fun i _ => zero_section_iterDerivIdealAlong U hA J hJ i)
    (zero_section_iterDerivIdealAlong U hA J hJ (d-1))

private theorem section_coefficientIdeal (A : Set U) (hA : IsClosedSubmanifold n A)
    (J : GermIdeal (n+1) (productOpen U)) (hJ : J.IsCoherent) (d : ℕ) :
    GermIdeal.pullback (m := n) (zeroSection U)
      (finSumIdeal (fun i => idealPow (iterDerivIdealAlong (liftedCarrier A) J i)
        (sumExp (fun j => d-j) d i)) d)=
      finSumIdeal (fun i => idealPow (iterDerivIdealAlong A (GermIdeal.pullback (m := n) (zeroSection U) J) i)
        (sumExp (fun j => d-j) d i)) d := by
  rw [HironakaActualNonregularCoefficientNaturality.pullback_finSumIdeal (zeroSection_contMDiff U) _ _
    (fun _ _ {_ _} hg => holomorphicAt_of_mem_idealPow hg)]
  apply finSumIdeal_congr
  intro i _
  rw [HironakaActualNonregularCoefficientNaturality.pullback_idealPow (zeroSection_contMDiff U)
    (fun {_ _} hg => holomorphicAt_of_mem_iterDerivIdealAlong
      (N := liftedCarrier A) (fun _ _ hj => GermIdeal.IsCoherent.holomorphicAt_mem hJ hj) i _ _ hg),
    zero_section_iterDerivIdealAlong U hA J hJ i]


theorem bar_ideal_section (A : Set U) (hA : IsClosedSubmanifold n A)
    (E : List (Set U)) (J : GermIdeal (n+1) (productOpen U)) (hJ : J.IsCoherent) (d : ℕ) :
    GermIdeal.pullback (m := n) (zeroSection U)
      (StepOneValue.barMarked (X := CMfd.of (n := n+1) (productOpen U))
        (⟨liftedCarrier A,E.map (projection U ⁻¹' ·),J,d⟩ : MarkedIdeal (n+1) (productOpen U))).ideal=
      (StepOneValue.barMarked (X := CMfd.of (n := n) U)
        (⟨A,E,GermIdeal.pullback (m := n) (zeroSection U) J,d⟩ : MarkedIdeal n U)).ideal := by
  change GermIdeal.pullback (m := n) (zeroSection U)
      (finSumIdeal (fun i => idealPow (iterDerivIdealAlong (liftedCarrier A) (homogenizedIdealAlong (liftedCarrier A) J d) i)
        (sumExp (fun j => d-j) d i)) d)=
      finSumIdeal (fun i => idealPow (iterDerivIdealAlong A (homogenizedIdealAlong A (GermIdeal.pullback (m := n) (zeroSection U) J) d) i)
        (sumExp (fun j => d-j) d i)) d
  rw [section_coefficientIdeal A hA _ (isCoherent_homogenizedIdealAlong hJ (liftedCarrier_closed_submanifold hA) d) d,
    section_homogenizedIdeal A hA J hJ d]

theorem isSpecial_section_refl_iff (A : Set U) (hA : IsClosedSubmanifold n A)
    (E : List (Set U)) (J : GermIdeal (n+1) (productOpen U)) (hJ : J.IsCoherent) (d : ℕ) (x : U) :
    StepOneValue.IsSpecial (X := CMfd.of (n := n+1) (productOpen U))
      (⟨liftedCarrier A,E.map (projection U ⁻¹' ·),J,d⟩ : MarkedIdeal (n+1) (productOpen U)) .refl (zeroSection U x) ↔
    StepOneValue.IsSpecial (X := CMfd.of (n := n) U)
      (⟨A,E,GermIdeal.pullback (m := n) (zeroSection U) J,d⟩ : MarkedIdeal n U) .refl x := by
  let M : MarkedIdeal (n+1) (CMfd.of (n := n+1) (productOpen U)):=⟨liftedCarrier A,E.map (projection U ⁻¹' ·),J,d⟩
  let B : MarkedIdeal n (CMfd.of (n := n) U):=⟨A,E,GermIdeal.pullback (m := n) (zeroSection U) J,d⟩
  have hc : (StepOneValue.barMarked M).ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong (isCoherent_homMarkedAlong (𝔪 := M) hJ (liftedCarrier_closed_submanifold hA))
      (liftedCarrier_closed_submanifold hA)
  have hIdeal : GermIdeal.pullback (m := n) (zeroSection U) (StepOneValue.barMarked M).ideal=
      (StepOneValue.barMarked B).ideal:=bar_ideal_section A hA E J hJ d
  have hC:=section_codimOnePart_iff A (StepOneValue.barMarked M).ideal
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hc hg) x (StepOneValue.barMarked M).d
  rw [hIdeal] at hC
  have hCos : (StepOneValue.barMarked M).cosupp=liftedCarrier (StepOneValue.barMarked B).cosupp := by
    change cosupport (n+1) (liftedCarrier A) (StepOneValue.barMarked M).ideal (StepOneValue.barMarked M).d=
      liftedCarrier (cosupport n A (StepOneValue.barMarked B).ideal (StepOneValue.barMarked B).d)
    rw [source_cosupport_eq_lifted A _ (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hc hg),hIdeal]
    rfl
  have hL : zeroSection U x∈memberInterLocus (StepOneValue.barMarked M).N
      (StepOneValue.origMembers M .refl) (StepOneValue.barMarked M).cosupp ↔
      x∈memberInterLocus (StepOneValue.barMarked B).N
      (StepOneValue.origMembers B .refl) (StepOneValue.barMarked B).cosupp := by
    rw [hCos]
    change zeroSection U x ∈ memberInterLocus (liftedCarrier A)
      ((E.map (projection U ⁻¹' ·)).take (E.map (projection U ⁻¹' ·)).length)
      (liftedCarrier (StepOneValue.barMarked B).cosupp) ↔
      x ∈ memberInterLocus A (E.take E.length) (StepOneValue.barMarked B).cosupp
    rw [List.take_length,List.take_length]
    exact memberInterLocus_section_iff A (StepOneValue.barMarked B).cosupp E x
  change StepOneValue.IsSpecial M .refl (zeroSection U x) ↔StepOneValue.IsSpecial B .refl x
  unfold StepOneValue.IsSpecial
  rw [level_section_refl A E J d x]
  exact or_congr (and_congr_right fun _ => hC) (and_congr_right fun _ => hL)

theorem stepRegime_section_refl_iff (A : Set U) (hA : IsClosedSubmanifold n A)
    (E : List (Set U)) (J : GermIdeal (n+1) (productOpen U)) (hJ : J.IsCoherent) (d s : ℕ) (x : U) :
    StepOneValue.stepRegime (X := CMfd.of (n := n+1) (productOpen U))
      (⟨liftedCarrier A,E.map (projection U ⁻¹' ·),J,d⟩ : MarkedIdeal (n+1) (productOpen U)) s .refl (zeroSection U x) ↔
    StepOneValue.stepRegime (X := CMfd.of (n := n) U)
      (⟨A,E,GermIdeal.pullback (m := n) (zeroSection U) J,d⟩ : MarkedIdeal n U) s .refl x := by
  unfold StepOneValue.stepRegime
  rw [level_section_refl A E J d x,isSpecial_section_refl_iff A hA E J hJ d x]

open HironakaSmoothSubmersionCanonicalValueDimensionShift GeneralValue MonomialCaseAlong

theorem initial_family_monomial (q : ℕ) (hn : 0<n) (A : Set U) (E : List (Set U))
    (hE : NormalCrossings.IsSNCDivisor n E) (J : GermIdeal (n+1) (productOpen U))
    (hJ : ∀z g,J.mem z g → HolomorphicAt (n+1) g z) (d : ℕ) (x : U)
    (hz : nmOrd (M := CMfd.of (n := n) U)
      (⟨A,E,GermIdeal.pullback (m := n) (zeroSection U) J,d⟩ : MarkedIdeal n U) x=0) :
    (invFamily (Nat.succ_pos n) (q+1)).inv (X := CMfd.of (n := n+1) (productOpen U))
      (⟨liftedCarrier A,E.map (projection U ⁻¹' ·),J,d⟩ : MarkedIdeal (n+1) (productOpen U)) .refl (zeroSection U x)=
    sameIndexMap 1 (q+1) ((invFamily hn (q+1)).inv (X := CMfd.of (n := n) U)
      (⟨A,E,GermIdeal.pullback (m := n) (zeroSection U) J,d⟩ : MarkedIdeal n U) .refl x) := by
  have ho:=nmOrd_section_eq A E J hJ d x
  rw [hz] at ho
  rw [invFamily_succ,generalStep_inv,invFamily_succ,generalStep_inv]
  rw [genInv_of_nmOrd_eq_zero _ _ .refl ho,genInv_of_nmOrd_eq_zero _ _ .refl hz]
  simp only [MarkedIdeal.geoTransformAlong]
  rw [gammaAlong_section_dimension_shift A E hE J hJ d x]
  rfl

end
end Hironaka.HironakaActualSectionInitialBoundaryRegime
