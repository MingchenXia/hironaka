import Hironaka.Resolution.HironakaG1ProperBornDerivativeTrace

/-! The actual proper-plane mismatch occurs on the unique canonical initial point centre. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1ProperBornCanonicalMismatch

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaActualOpenZeroSectionDifferentials HironakaG1ProperBornStrictPlane
  HironakaG1ProperBornDerivativeTrace HironakaG1LaterPositiveNormalExample
  HironakaActualCoherentWeightedCoefficientMarked GermIdealOrder IdealOrderArithmetic
  CoefficientIdealRestriction HomogenizedIdealAlong ResolutionInvariantSpec InvDomainTowerAlong
  HironakaOneDimensionalCanonicalSuperlevels NormalCrossings RelativePrincipalizationSpan
  InvertibleIdealQuotient DivisorExponentAlong BlowupStrictSubmanifold HomogenizedGlueingTower

noncomputable section

private abbrev U : Opens (ComplexModel 2) := ⊤
private abbrev X := CMfd.of (n := 3) (productOpen U)
private abbrev p : X := zeroSection U ⟨0,mem_univ _⟩
private abbrev C : Set X := {p}

private theorem coord_hol (i : Fin 3) (x : X) :
    HolomorphicAt 3 (fun w : X => w.val i) x := by
  have h : ContMDiff 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ℂ) ∞
      (fun w : X => w.val i) :=
    (EuclideanSpace.proj i : ComplexModel 3 →L[ℂ] ℂ).contMDiff.comp contMDiff_subtype_val
  exact Eventually.of_forall fun w => (h.contMDiffAt (x := w)).mdifferentiableAt (by simp)

private theorem gen_hol (i : Fin 3) (x : X) : HolomorphicAt 3 (sourceGen i) x := by
  filter_upwards [coord_hol i x] with z hz
  exact hz.pow _

private theorem raw_coherent : record.ideal.IsCoherent :=
  isCoherent_finiteFunctionIdeal _ fun i x => (gen_hol i x).self_of_nhds

private theorem gen_mem (i : Fin 3) (x : X) : record.ideal.mem x (sourceGen i) :=
  isInSpanAt_self ⟨i,rfl⟩ (gen_hol i x)

private theorem p_zero : p.val = 0 := by simp [p, zeroSection]

theorem raw_source_cosupport : record.cosupp = C := by
  ext x
  constructor
  · intro hx
    apply mem_singleton_iff.mpr
    apply Subtype.ext
    rw [p_zero]
    ext i
    have h := (vanishesToOrderOn_one_iff hx.1 (gen_hol i x)).mp
      ((hx.2 _ (gen_mem i x)).mono (by decide : 1 ≤ 2))
    exact eq_zero_of_pow_eq_zero h
  · rintro rfl
    refine ⟨mem_univ _,fun g hg => IsInSpanAt.vanishesToOrderOn hg ?_⟩
    rintro _ ⟨j,rfl⟩
    have hv : VanishesToOrderOn 3 (univ : Set X) p 1 (fun w : X => w.val j) :=
      (vanishesToOrderOn_one_iff (mem_univ p) (coord_hol j p)).mpr (by rw [p_zero]; rfl)
    have h2 := hv.mul hv
    have h3 := h2.mul hv
    have h4 := h3.mul hv
    change VanishesToOrderOn 3 (univ : Set X) p 2 (sourceGen j)
    unfold sourceGen
    by_cases hj : j = 1
    · simpa [hj,pow_succ] using h4.mono (by decide : 2 ≤ (1 + 1) + 1 + 1)
    · by_cases hk : j = 2
      · simpa [hj,hk,pow_succ] using h2
      · simpa [hj,hk,pow_succ] using h3.mono (by decide : 2 ≤ (1 + 1) + 1)

private theorem proper_cosupport (M : MarkedIdeal 3 X) (hPos : 1 ≤ M.d)
    (hN : M.N = univ) (hCos : M.cosupp = C) (hGen : ∀ i x, M.ideal.mem x (sourceGen i)) :
    (withN M plane).cosupp = C := by
  ext x
  constructor
  · intro h
    apply mem_singleton_iff.mpr
    apply Subtype.ext
    rw [p_zero]
    ext i
    have hi := (vanishesToOrderOn_one_iff h.1 (gen_hol i x)).mp
      ((h.2 _ (hGen i x)).mono hPos)
    exact eq_zero_of_pow_eq_zero hi
  · intro h
    have hM : x ∈ M.cosupp := hCos.symm ▸ h
    have hp : p ∈ plane := by change p.val 2 = 0; rw [p_zero]; rfl
    refine ⟨(mem_singleton_iff.mp h).symm ▸ hp, fun g hg => (hM.2 _ hg).mono_set ?_⟩
    rw [hN]
    exact subset_univ _

theorem proper_raw_source_cosupport : (withN record plane).cosupp = C :=
  proper_cosupport record (by decide) rfl raw_source_cosupport gen_mem

private abbrev sourceCoeff := coeffMarkedAlong record

theorem proper_coefficient_source_cosupport : (withN sourceCoeff plane).cosupp = C := by
  have hCos : sourceCoeff.cosupp = record.cosupp := cosupp_coeffMarkedAlong
    isClosedSubmanifold_univ.2
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem raw_coherent hg) (by decide)
  refine proper_cosupport sourceCoeff (by decide) rfl (hCos.trans raw_source_cosupport) ?_
  intro i x
  have hWF : record.IsWellFormed := ⟨isClosedSubmanifold_univ,raw_coherent,
    isSNCDivisor_nil,SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor isSNCDivisor_nil⟩
  rw [(HironakaG1RecursiveBornOrderTwoBarExample.coefficient_mark_two record hWF rfl).2]
  exact le_sumIdeal_left' (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem raw_coherent hg)
    x _ (gen_mem i x)

private theorem canonical_singleton {Λ : Type} [LinearOrder Λ] (M : MarkedIdeal 3 X)
    (hCos : M.cosupp = C) (I : ∀ {Z : CMfd.{0} 3}, BlowupTower X Z → Z → Λ) :
    IsCanonical M I B := by
  refine ⟨trivial, Or.inr ?_⟩
  change C = ResolutionDriver.maxLocus (I (.refl : BlowupTower X X)) M.cosupp
  rw [hCos]
  ext z
  exact ⟨fun hz => ⟨hz,fun w hw => by rw [mem_singleton_iff.mp hz,mem_singleton_iff.mp hw]⟩,
    fun hz => hz.1⟩

/-- Singleton cosupport forces this exact actual point blowup for every ordered invariant. -/
theorem proper_point_canonical {Λ : Type} [LinearOrder Λ]
    (I : ∀ {Z : CMfd.{0} 3}, BlowupTower X Z → Z → Λ) :
    IsCanonical (withN record plane) I B ∧ IsCanonical (withN sourceCoeff plane) I B :=
  ⟨canonical_singleton _ proper_raw_source_cosupport I,
    canonical_singleton _ proper_coefficient_source_cosupport I⟩

/-- The canonical move and the exact inherited-versus-refreshed exponent
comparison refer to the same genuine geometric point blowup. -/
theorem canonical_proper_coefficient_mismatch {Λ : Type} [LinearOrder Λ]
    (I : ∀ {Z : CMfd.{0} 3}, BlowupTower X Z → Z → Λ) :
    let P := withN record plane
    let Q := withN sourceCoeff plane
    let A := geoTransformAlong Q B
    let R := coeffMarkedAlong (geoTransformAlong P B)
    IsCanonical P I B ∧ IsCanonical Q I B ∧
      A.E = R.E ∧ R.E = [π ⁻¹' C] ∧ q ∈ A.cosupp ∧ q ∈ R.cosupp ∧
      divExpAlong 3 A.N A.ideal (π ⁻¹' C) q = 1 ∧
      divExpAlong 3 R.N R.ideal (π ⁻¹' C) q = 0 := by
  obtain ⟨hP,hQ⟩ := proper_point_canonical I
  exact ⟨hP,hQ,proper_chronological_inherited_vs_refreshed⟩

open HironakaActualCentreJointJets HironakaRelativeNormalIdeal
  HironakaActualNativeSectionInitialBar BlowupConstruction

private theorem plane_eq_section : plane = zeroPlane U := by
  ext z
  change z.val (2 : Fin 3) = 0 ↔ (projection U z ∈ univ ∧ actualJointNormalProjection 2 1 z.val = 0)
  simp only [mem_univ,true_and]
  constructor
  · intro h
    ext i
    obtain rfl : i = 0 := Fin.eq_zero i
    rw [actualJointNormalProjection_apply]
    exact h
  · intro h
    have he := congrArg (fun v : ComplexModel 1 => v 0) h
    change actualJointNormalProjection 2 1 z.val 0 = 0 at he
    rw [actualJointNormalProjection_apply] at he
    exact he

private theorem section_project {z : X} (hz : z ∈ plane) :
    zeroSection U (projection U z) = z := by
  apply Subtype.ext
  change tangentInclusion 2 1 (tangentProjection 2 1 z.val) = z.val
  have hn : actualJointNormalProjection 2 1 z.val = 0 := ((Set.ext_iff.mp plane_eq_section z).mp hz).2
  simpa only [HironakaActualIntrinsicStableAmbientIso.join,hn,map_zero,add_zero] using
    (HironakaActualIntrinsicStableAmbientIso.join_projections (n := 2) (m := 1) z.val)

private theorem section_mem_plane (x : U) : zeroSection U x ∈ plane := by
  rw [plane_eq_section]
  refine ⟨mem_univ _,?_⟩
  change actualJointNormalProjection 2 1 (tangentInclusion 2 1 x.val) = 0
  ext i
  obtain rfl : i = 0 := Fin.eq_zero i
  rw [actualJointNormalProjection_apply]
  exact tangentInclusion_normal 2 1 x.val 0

private theorem section_first (x : U) : (zeroSection U x).val (0 : Fin 3) = x.val (0 : Fin 2) := by
  change tangentInclusion 2 1 x.val 0 = _
  exact congrArg (fun w : ComplexModel 2 => w 0) (tangentProjection_tangentInclusion 2 1 x.val)

/-- This proper mark-two source belongs to the invariant domain in carrier dimension two. -/
theorem proper_raw_source_domain : IsInvDomain 2 (withN record plane) := by
  have hReg : ∀ z ∈ plane, RegularAtDim (n := 3) plane z 2 := by
    rw [plane_eq_section]
    exact zeroPlane_regular U
  have hClosed : IsClosed plane := isClosed_singleton.preimage
    ((EuclideanSpace.proj (2 : Fin 3) : ComplexModel 3 →L[ℂ] ℂ).continuous.comp continuous_subtype_val)
  have hPlane : IsClosedSubmanifold 3 plane := ⟨hClosed,fun z hz => ⟨2,hReg z hz⟩⟩
  refine ⟨⟨hPlane,raw_coherent,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hPlane⟩,
    fun z hz => ⟨2,le_rfl,hReg z hz⟩,by decide,?_⟩
  intro z hz
  refine ⟨sourceGen 0,gen_mem 0 z,?_⟩
  have hne : ∃ᶠ x : U in 𝓝 (projection U z), x.val (0 : Fin 2) ≠ 0 := by
    by_contra! h
    have hI := U.isOpen.isOpenEmbedding_subtypeVal.isOpenMap.image_mem_nhds h
    obtain ⟨_,⟨x,hx,rfl⟩,hn⟩ := exists_coord_ne_zero_of_mem_nhds hI (0 : Fin 2)
    exact hn hx
  have hs := (zeroSection_contMDiff U).continuous.continuousAt (x := projection U z)
  change Tendsto (zeroSection U) (𝓝 (projection U z)) (𝓝 (zeroSection U (projection U z))) at hs
  rw [section_project hz] at hs
  exact hs.frequently (hne.mono fun x hx => ⟨section_mem_plane x,by
    simpa [sourceGen,section_first,show (0 : Fin 3) ≠ 1 by decide,show (0 : Fin 3) ≠ 2 by decide]
      using pow_ne_zero 3 hx⟩)


open MarkedIdealOperationsAlong.MarkedIdeal HironakaG8DomainExponents

/-- The exact refreshed compatibility premise fails on the canonical point witness. -/
theorem canonical_inherited_not_refresh_compatible :
    ¬ RestrictEquiv (geoTransformAlong (withN sourceCoeff plane) B)
      (coeffMarkedAlong (geoTransformAlong (withN record plane) B)) := by
  intro h
  obtain ⟨_,_,_,_,hA,hR⟩ := proper_chronological_inherited_vs_refreshed
  have he := divExpAlong_eq_of_restrictEquiv h (π ⁻¹' C) q
  change divExpAlong 3 ((withN sourceCoeff plane).geoTransform C π).N
      ((withN sourceCoeff plane).geoTransform C π).ideal (π ⁻¹' C) q =
    divExpAlong 3 (coeffMarkedAlong ((withN record plane).geoTransform C π)).N
      (coeffMarkedAlong ((withN record plane).geoTransform C π)).ideal (π ⁻¹' C) q at he
  exact Nat.one_ne_zero (hA.symm.trans (he.trans hR))

#print axioms canonical_inherited_not_refresh_compatible
#print axioms proper_raw_source_domain
#print axioms canonical_proper_coefficient_mismatch
#print axioms proper_point_canonical
end
end Hironaka.HironakaG1ProperBornCanonicalMismatch
