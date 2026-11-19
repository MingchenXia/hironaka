import Hironaka.Resolution.HironakaG1AdvancedHeadCountExhaustion
import Hironaka.Resolution.HironakaActualWeightedNormalPadding
import Hironaka.Resolution.HironakaG1NonemptyHeadMixedTrace

/-! # An additional off-centre source zero beside the advanced born head -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1TwoZeroBornCounts
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec ResolutionDriver CanonicalCentres StepOneValue StepOneRegime
  GermIdealOrder InvertibleIdealQuotient RelativePrincipalizationSpan DivisorExponentAlong NormalCrossings
  HironakaActualCoherentWeightedCoefficientMarked HironakaActualWeightedNormalPadding
  HironakaPrincipalizationBoundary HironakaActualOpenZeroSectionDifferentials
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact
  HironakaActualNativeSectionInitialBar HironakaG8MemberLoci HironakaG1LaterPositiveNormalExample
  HironakaG1LaterAdvancedHeadNativeExample BoundaryCount HironakaAdmissibleSequence
  HironakaG1PositiveNormalJointExample HironakaG1PositiveNormalNonspecialExample
  BlowupControlledTransform GermIdealPullbackCalculus IdealOrderArithmetic BlowupStrictSubmanifold
  BlowupMonomialCharts TransformOffCentre HironakaG1LaterMixedUpperBornTrace
  HironakaG1NonemptyHeadMixedTrace HironakaG1LaterAdvancedHeadExample HironakaG1AdvancedHeadCountExhaustion HomogenizedGlueingTower
  HironakaG1ProperCarrierNormalLocalClass HironakaActualCentreJointJets HironakaRelativeNormalIdeal

abbrev U : Opens (ComplexModel 2) := ⊤
abbrev X := CMfd.of (n := 3) (productOpen U)
def a₀ : U := ⟨0, mem_univ _⟩
def a₁ : U := ⟨EuclideanSpace.single (1 : Fin 2) (1 : ℂ), mem_univ _⟩
def p₀ : X := zeroSection U a₀
def p₁ : X := zeroSection U a₁

def generator (j : Bool) (z : ComplexModel 2) : ℂ :=
  if j then z 0 else z 1 ^ 2 * (z 1 - 1)

abbrev sourceIdeal : GermIdeal 2 (ComplexModel 2) := finiteFunctionIdeal generator

def source : MarkedIdeal 2 U :=
  ⟨univ, [{z | z.val 0 = 0}, {z | z.val 1 = 0}],
    GermIdeal.pullback (m := 2) (Subtype.val : U → ComplexModel 2) sourceIdeal, 1⟩

abbrev padded := properNormalMarked source
abbrev sectionRecord := sectionMarked source
abbrev emptyTower : BlowupTower X X := .refl

private theorem generator_hol (j : Bool) :
    MDifferentiable 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ℂ) (generator j) := by
  cases j
  · change MDifferentiable 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ℂ)
      (fun z : ComplexModel 2 => z 1 ^ 2 * (z 1 - 1))
    exact ((((EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 2)).differentiable.pow 2).mul
      ((EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 2)).differentiable.sub_const (1 : ℂ)))).mdifferentiable
  · change MDifferentiable 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ℂ)
      (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2))
    exact (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2)).mdifferentiable

private theorem sourceIdeal_nonzero (z : ComplexModel 2) :
    IsNonzeroAlongAt univ sourceIdeal z := by
  apply isNonzeroAlongAt_univ_iff_exists.mpr
  let f : ComplexModel 2 → ℂ := EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2)
  have hf : HolomorphicAt 2 f z := Eventually.of_forall fun _ =>
    (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2)).mdifferentiableAt
  refine ⟨f, isInSpanAt_self ⟨true, rfl⟩ hf, ?_⟩
  by_contra! h
  have hzero : f =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := h
  have hd := hzero.fderiv_eq (𝕜 := ℂ)
  change fderiv ℂ (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2)) z =
    fderiv ℂ (fun _ : ComplexModel 2 => (0 : ℂ)) z at hd
  rw [ContinuousLinearMap.fderiv, fderiv_const_apply] at hd
  have hbad := congrArg (fun L : ComplexModel 2 →L[ℂ] ℂ => L (PiLp.single 2 (0 : Fin 2) 1)) hd
  simp at hbad

theorem source_domain : IsInvDomain 2 source := by
  let C := CMfd.of (n := 2) (ComplexModel 2)
  let A : MarkedIdeal 2 C := ⟨univ, [], sourceIdeal, 1⟩
  have hA : IsInvDomain 2 A := isInvDomain_univ_of_isSNCDivisor
    (isCoherent_finiteFunctionIdeal generator generator_hol) sourceIdeal_nonzero isSNCDivisor_nil
  have hU := InvDomainTowerAlong.isInvDomain_pullback_val U hA
  have hOld := Q_domain
  exact isInvDomain_univ_of_isSNCDivisor hU.isWellFormed.isCoherent
    (fun z => hU.isNonzeroAlongAt z (mem_univ _)) hOld.isWellFormed.isSNCDivisor

private theorem source_generators :
    source.ideal = finiteFunctionIdeal (n := 2) (fun j => generator j ∘ (Subtype.val : U → ComplexModel 2)) :=
  finiteFunctionIdeal_pullback generator generator_hol _ contMDiff_subtype_val

theorem source_cosupport : source.cosupp = {a₀, a₁} := by
  ext z
  let g := fun j => generator j ∘ (Subtype.val : U → ComplexModel 2)
  have hHol (j : Bool) : HolomorphicAt 2 (g j) z :=
    Eventually.of_forall fun y => by
      have hv : MDifferentiable 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ComplexModel 2)
          (Subtype.val : U → ComplexModel 2) :=
        (contMDiff_subtype_val : ContMDiff 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ComplexModel 2) ∞
          (Subtype.val : U → ComplexModel 2)).mdifferentiable (by simp)
      exact (generator_hol j).mdifferentiableAt.comp y (hv y)
  change z ∈ cosupport 2 univ source.ideal 1 ↔ _
  rw [source_generators, mem_cosupport_finiteFunctionIdeal_iff _ z 1 hHol]
  constructor
  · intro h
    have h0 : z.val (0 : Fin 2) = 0 :=
      (vanishesToOrderOn_one_iff (mem_univ z) (hHol true)).mp (h true)
    have h1 : z.val (1 : Fin 2) ^ 2 * (z.val (1 : Fin 2) - 1) = 0 :=
      (vanishesToOrderOn_one_iff (mem_univ z) (hHol false)).mp (h false)
    have hz : z.val (1 : Fin 2) = 0 ∨ z.val (1 : Fin 2) = 1 := by
      rcases mul_eq_zero.mp h1 with h1 | h1
      · exact Or.inl (eq_zero_of_pow_eq_zero h1)
      · exact Or.inr (sub_eq_zero.mp h1)
    rcases hz with hz | hz
    · left
      apply Subtype.ext
      ext i
      fin_cases i <;> assumption
    · right
      apply mem_singleton_iff.mpr
      apply Subtype.ext
      ext i
      fin_cases i <;> simp [a₁, h0, hz]
  · intro hz j
    apply (vanishesToOrderOn_one_iff (mem_univ z) (hHol j)).mpr
    rcases hz with rfl | hz
    · cases j <;> simp [g, generator, a₀]
    · rw [mem_singleton_iff.mp hz]
      cases j <;> simp [g, generator, a₁]

theorem padded_source_cosupport : padded.cosupp = {p₀, p₁} := by
  rw [properNormalMarked_cosupp source source_domain, source_cosupport]
  ext z
  simp only [mem_image, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨a, rfl | rfl, rfl⟩ <;> simp [p₀, p₁]
  · rintro (rfl | rfl)
    · exact ⟨a₀, Or.inl rfl, rfl⟩
    · exact ⟨a₁, Or.inr rfl, rfl⟩

private theorem projection_of_zero (a : U) : projection U (zeroSection U a) = a := by
  apply Subtype.ext
  exact tangentProjection_tangentInclusion 2 1 a

private abbrev D (i : Fin 2) : Set X := projection U ⁻¹' {a : U | a.val i = 0}

theorem padded_initial_levels :
    level padded emptyTower p₀ = 2 ∧ level padded emptyTower p₁ = 1 := by
  have h00 : p₀ ∈ D 0 := by
    change (projection U (zeroSection U a₀)).val 0 = 0
    rw [projection_of_zero]
    rfl
  have h01 : p₀ ∈ D 1 := by
    change (projection U (zeroSection U a₀)).val 1 = 0
    rw [projection_of_zero]
    rfl
  have h10 : p₁ ∈ D 0 := by
    change (projection U (zeroSection U a₁)).val 0 = 0
    rw [projection_of_zero]
    simp [a₁]
  have h11 : p₁ ∉ D 1 := by
    change ¬ (projection U (zeroSection U a₁)).val 1 = 0
    rw [projection_of_zero]
    simp [a₁]
  change boundaryCount [D 0, D 1] p₀ = 2 ∧ boundaryCount [D 0, D 1] p₁ = 1
  classical
  have hAll : Finset.univ.filter (fun i : Fin ([D 0, D 1].length) => p₀ ∈ [D 0, D 1].get i) =
      Finset.univ := by
    ext i
    fin_cases i
    · exact iff_of_true (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h00⟩) (Finset.mem_univ _)
    · exact iff_of_true (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h01⟩) (Finset.mem_univ _)
  have hFirst : Finset.univ.filter (fun i : Fin ([D 0, D 1].length) => p₁ ∈ [D 0, D 1].get i) =
      {0} := by
    ext i
    fin_cases i
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      change p₁ ∈ D 0 ↔ (0 : Fin 2) = 0
      exact iff_of_true h10 rfl
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      change p₁ ∈ D 1 ↔ (1 : Fin 2) = 0
      exact iff_of_false h11 (by decide)
  unfold boundaryCount
  rw [hAll, hFirst]
  simp

theorem section_initial_levels :
    level sectionRecord emptyTower p₀ = 2 ∧ level sectionRecord emptyTower p₁ = 1 := by
  rw [← level_eq_of_E_eq (A := padded) (B := sectionRecord) rfl emptyTower p₀,
    ← level_eq_of_E_eq (A := padded) (B := sectionRecord) rfl emptyTower p₁]
  exact padded_initial_levels

theorem section_source_cosupport : sectionRecord.cosupp = {p₀, p₁} :=
  ((((properNormalMarked_locWPEquiv_section source source_domain).wEquiv.2 emptyTower).2 trivial).symm.trans
    padded_source_cosupport)

private theorem initial_max_of_levels {J : MarkedIdeal 3 X} {k : ℕ}
    (hCos : J.cosupp = {p₀,p₁}) (h0 : level J emptyTower p₀ = 2) (h1 : level J emptyTower p₁ = 1) :
    maxLocus (Seq.StepOneValueMasked.stepOneInvM (invFamily (by decide : 0 < 3) k) J emptyTower)
      J.cosupp = {p₀} := by
  let R := invFamily (by decide : 0 < 3) k
  let f := Seq.StepOneValueMasked.stepOneInvM R J emptyTower
  have hlt : f p₁ < f p₀ := by
    change Seq.StepOneValueMasked.stepOneInvM R J emptyTower p₁ <
      Seq.StepOneValueMasked.stepOneInvM R J emptyTower p₀
    rw [Prod.Lex.lt_iff, Seq.StepOneValueMasked.stepOneInvL_fst,
      Seq.StepOneValueMasked.stepOneInvL_fst, h0, h1]
    exact Or.inl (by decide)
  rw [hCos]
  ext x
  constructor
  · intro hx
    rcases hx.1 with h | h
    · exact h
    · have he : x = p₁ := mem_singleton_iff.mp h
      exact ((not_lt_of_ge (hx.2 p₀ (mem_insert p₀ _))) (he.symm ▸ hlt)).elim
  · intro hx
    change x = p₀ at hx
    subst x
    refine ⟨mem_insert p₀ _, fun y hy => ?_⟩
    rcases hy with h | h
    · change y = p₀ at h
      rw [h]
    · rw [mem_singleton_iff.mp h]
      exact hlt.le

/-- The existing genuine point blowup at the origin is canonical for
both modified records. The other source zero has smaller original
boundary level, so it does not enter the first centre. -/
theorem two_zero_first_blowup_common_canonical :
    IsCanonical padded (Seq.StepOneValueMasked.stepOneInvM (invFamily (by decide : 0 < 3) 2) padded) B ∧
      IsCanonical sectionRecord
        (Seq.StepOneValueMasked.stepOneInvM (invFamily (by decide : 0 < 3) 1) sectionRecord) B := by
  exact ⟨⟨trivial, Or.inr (initial_max_of_levels padded_source_cosupport
      padded_initial_levels.1 padded_initial_levels.2).symm⟩,
    ⟨trivial, Or.inr (initial_max_of_levels section_source_cosupport
      section_initial_levels.1 section_initial_levels.2).symm⟩⟩

private theorem pullback_le {n m : ℕ} {A : CMfd.{0} n} {B : CMfd.{0} m}
    {I J : GermIdeal n A} (h : I.Le J) (f : B → A) :
    (GermIdeal.pullback (m := m) f I).Le (GermIdeal.pullback (m := m) f J) := by
  intro x g hg
  exact GermIdeal.mem_pullback_iff.mpr ((GermIdeal.mem_pullback_iff.mp hg).mono
    (by rintro s ⟨a,ha,rfl⟩; exact ⟨a,h _ _ ha,rfl⟩))

private theorem source_ideal_le_original : sourceIdeal.Le coordinatePairIdeal := by
  intro x g hg
  refine IsInSpanAt.trans ?_ hg
  rintro _ ⟨j, rfl⟩
  cases j
  · have h : HolomorphicAt 2 (fun z : ComplexModel 2 => z 1 - 1) x :=
      Eventually.of_forall fun _ =>
        ((EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 2)).differentiable.sub_const (1 : ℂ)).mdifferentiable _
    have hBase : coordinatePairIdeal.mem x (coordinatePairGenerator false) :=
      isInSpanAt_self ⟨false, rfl⟩ (Eventually.of_forall fun _ =>
        ((EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 2)).mdifferentiable.pow 2).mdifferentiableAt)
    apply InvertibleIdealQuotient.IsInSpanAt.congr' (RelativePrincipalizationSpan.IsInSpanAt.mul_left h hBase)
    exact Eventually.of_forall fun z => by
      simp only [generator, Bool.false_eq_true, ↓reduceIte, coordinatePairGenerator]
      ring
  · exact isInSpanAt_self ⟨true, rfl⟩ (Eventually.of_forall fun _ =>
      (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2)).mdifferentiableAt)

private theorem padded_ideal_le_original :
    padded.ideal.Le (properNormalMarked sourceRecord).ideal := by
  have hSource : source.ideal.Le sourceRecord.ideal :=
    pullback_le (A := CMfd.of (n := 2) (ComplexModel 2)) (B := CMfd.of (n := 2) U)
      source_ideal_le_original Subtype.val
  have hSection := pullback_le (A := CMfd.of (n := 2) U) (B := X) hSource (projection U)
  intro x g hg
  exact mem_sumIdeal_iff.mpr ((mem_sumIdeal_iff.mp hg).mono (fun f h =>
    h.elim (fun h => Or.inl (hSection x f h)) Or.inr))


set_option maxHeartbeats 1200000 in
/-- The advanced-chart origin survives the very same genuine point
blowup for the new ideal. Generator inclusion suffices here because the
whole controlled transform is monotone at the unchanged mark. -/
theorem two_zero_born_survivor : q ∈ (geoTransformAlong padded B).cosupp := by
  let P := properNormalMarked sourceRecord
  have hP := properNormalMarked_isInvDomain sourceRecord sourceRecord_domain
  have hQ := properNormalMarked_isInvDomain source source_domain
  have hN : padded.N = P.N := rfl
  have hCar : (geoTransformAlong padded B).N = (geoTransformAlong P B).N := by
    change geoStrictTransform π {p₀} padded.N = geoStrictTransform π {p₀} P.N
    rw [hN]
  have hLe : (geoTransformAlong padded B).ideal.Le (geoTransformAlong P B).ideal := by
    change (padded.geoTransform {p₀} π).ideal.Le (P.geoTransform {p₀} π).ideal
    have hNew : (padded.geoTransform {p₀} π).ideal = controlledTransform hπ padded.ideal 1 :=
      geoTransform_ideal_eq_controlledTransform (𝔪 := padded) (show padded.N = univ from preimage_univ)
        hQ.isWellFormed.isCoherent hπ
    have hOld : (P.geoTransform {p₀} π).ideal = controlledTransform hπ P.ideal 1 :=
      geoTransform_ideal_eq_controlledTransform (𝔪 := P) (show P.N = univ from preimage_univ)
        hP.isWellFormed.isCoherent hπ
    rw [hNew, hOld]
    intro z f hf
    obtain ⟨hHol, hProd⟩ := mem_colon_iff.mp hf
    exact mem_colon_iff.mpr ⟨hHol, fun g hg =>
      pullback_le (A := X) (B := Y) padded_ideal_le_original π _ _ (hProd _ hg)⟩
  refine ⟨hCar.symm ▸ q_cosupp.1, fun g hg => ?_⟩
  rw [hCar]
  exact q_cosupp.2 g (hLe _ _ hg)

/-- The second survivor lies on the same middle-coordinate chart at
nonzero exceptional coordinate, over the additional source zero. -/
def offCentreAnchor : Y := yChart.invFun (EuclideanSpace.single (1 : Fin 3) (1 : ℂ))

theorem offCentreAnchor_proj : π offCentreAnchor = p₁ := by
  let b := EuclideanSpace.single (1 : Fin 3) (1 : ℂ)
  have hz : offCentreAnchor ∈ yChart.source := yChart.toPartialEquiv.map_target (chart_all b)
  have hCoord : yChart.toFun offCentreAnchor = b := yChart.toPartialEquiv.right_inv (chart_all b)
  apply Subtype.ext
  rw [chart_projection offCentreAnchor hz, hCoord]
  change monomial 0 (1 : Fin 3) b = tangentInclusion 2 1 a₁.val
  ext i
  fin_cases i <;> simp [monomial_apply, b, a₁, tangentInclusion]

private theorem p₁_ne_p₀ : p₁ ≠ p₀ := by
  intro h
  have hEq := congrArg (fun p : X => (projection U p).val (1 : Fin 2)) h
  change (projection U (zeroSection U a₁)).val 1 = (projection U (zeroSection U a₀)).val 1 at hEq
  rw [projection_of_zero, projection_of_zero] at hEq
  simp [a₀,a₁] at hEq

private theorem offCentreAnchor_off : π offCentreAnchor ∉ ({p₀} : Set X) := by
  rw [offCentreAnchor_proj, mem_singleton_iff]
  exact p₁_ne_p₀

theorem offCentreAnchor_survives : offCentreAnchor ∈ (geoTransformAlong padded B).cosupp := by
  have hP := properNormalMarked_isInvDomain source source_domain
  have hCos : π offCentreAnchor ∈ padded.cosupp := by
    rw [offCentreAnchor_proj, padded_source_cosupport]
    exact mem_insert_of_mem _ (mem_singleton _)
  exact (TransformOffCentre.mem_cosupp_geoTransform_iff padded
    hP.isWellFormed.isClosedSubmanifold_N.1
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hP.isWellFormed.isCoherent hg)
    hπ offCentreAnchor_off).mpr hCos

theorem offCentreAnchor_level : level padded B offCentreAnchor = 1 := by
  have hpD₀ : p₁ ∈ D 0 := by
    change (projection U (zeroSection U a₁)).val 0 = 0
    rw [projection_of_zero]
    simp [a₁]
  have hpD₁ : p₁ ∉ D 1 := by
    change ¬ (projection U (zeroSection U a₁)).val 1 = 0
    rw [projection_of_zero]
    simp [a₁]
  let H₀ := geoStrictTransform π {p₀} (D 0)
  let H₁ := geoStrictTransform π {p₀} (D 1)
  have h0 : offCentreAnchor ∈ H₀ := subset_closure
    (show π offCentreAnchor ∈ D 0 \ {p₀} from
      ⟨offCentreAnchor_proj.symm ▸ hpD₀, offCentreAnchor_off⟩)
  have hClosed : IsClosed (D 1) := (properNormalMarked_isInvDomain source source_domain).isWellFormed.isSNCDivisor.1
    _ (by change D 1 ∈ [D 0,D 1]; simp)
  have h1 : offCentreAnchor ∉ H₁ := fun h => hpD₁
    (offCentreAnchor_proj ▸ geoStrictTransform_subset_preimage hπ.contMDiff.continuous hClosed h)
  change boundaryCount [H₀,H₁] offCentreAnchor = 1
  classical
  have hFirst : Finset.univ.filter (fun i : Fin ([H₀,H₁].length) => offCentreAnchor ∈ [H₀,H₁].get i) =
      {0} := by
    ext i
    fin_cases i
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      change offCentreAnchor ∈ H₀ ↔ (0 : Fin 2) = 0
      exact iff_of_true h0 rfl
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      change offCentreAnchor ∈ H₁ ↔ (1 : Fin 2) = 0
      exact iff_of_false h1 (by decide)
  unfold boundaryCount
  rw [hFirst]
  rfl

theorem offCentreAnchor_has_zero_head_count :
    upperHeadNonOriginalBoundaryCount source B 0 offCentreAnchor = 0 := by
  by_cases hReg : stepRegime padded 1 emptyTower (π offCentreAnchor)
  · apply upperHeadNonOriginalBoundaryCount_eq_zero_of_full_run
    change regimeRun (stepRegime padded 1) (.step emptyTower {p₀} π hπ) offCentreAnchor = 1
    exact (regimeRun_step_of _ emptyTower {p₀} π hπ hReg).trans (by rw [regimeRun_refl])
  · have hr : regimeRun (stepRegime padded 1) B offCentreAnchor = 0 :=
      regimeRun_step_of_not _ emptyTower {p₀} π hπ hReg
    apply (upperHeadNonOriginalBoundaryCount_eq_zero_iff_off_endpoint source B offCentreAnchor).2
    let Test (j : ℕ) : Prop :=
      ∀ H ∈ (geoTransformAlong (barMarked padded) (head B j)).E, H ∉ origMembers padded (head B j) →
        offCentreAnchor ∉ strictAlong (tail B j) H
    change Test (regimeRun (stepRegime padded 1) B offCentreAnchor)
    apply (congrArg Test hr).mpr
    change ∀ H ∈ ([geoStrictTransform π {p₀} (D 0), geoStrictTransform π {p₀} (D 1),
      π ⁻¹' ({p₀} : Set X)] : List (Set Y)),
      H ∉ [geoStrictTransform π {p₀} (D 0), geoStrictTransform π {p₀} (D 1)] →
        offCentreAnchor ∉ H
    intro H hH hOld hIn
    rcases List.mem_cons.mp hH with rfl | hH
    · exact hOld (List.mem_cons_self)
    rcases List.mem_cons.mp hH with rfl | hH
    · exact hOld (List.mem_cons_of_mem _ List.mem_cons_self)
    have hEq := List.mem_singleton.mp hH
    have hf : offCentreAnchor ∈ π ⁻¹' ({p₀} : Set X) := hEq ▸ hIn
    exact offCentreAnchor_off hf

private abbrev originalTwoBoundarySource : MarkedIdeal 2 U := {source with ideal := sourceRecord.ideal}

theorem bornAnchor_level : level padded B q = 1 := by
  have h := level_eq_of_E_eq (A := padded) (B := properNormalMarked originalTwoBoundarySource) rfl B q
  exact h.trans joint_added_boundary_upper_regime_advances.2.1

set_option maxHeartbeats 500000 in
theorem bornAnchor_has_one_head_count :
    upperHeadNonOriginalBoundaryCount source B 0 q = 1 := by
  have hRun : regimeRun (stepRegime padded 1) B q = 0 := by
    apply regimeRun_step_of_not _ emptyTower {p₀} π hπ
    have hp : π q = p₀ := joint_first_point_blowup_positive_normal_contact.2.2.2.1
    rw [hp]
    intro h
    exact (by decide : (2 : ℕ) ≠ 1) (padded_initial_levels.1.symm.trans h.1)
  let H₀ := geoStrictTransform π {p₀} (D 0)
  let H₁ := geoStrictTransform π {p₀} (D 1)
  let E : Set Y := π ⁻¹' ({p₀} : Set X)
  have hqE : q ∈ E := by
    change π q ∈ ({p₀} : Set X)
    rw [show π q = p₀ from joint_first_point_blowup_positive_normal_contact.2.2.2.1]
    exact mem_singleton _
  have hq0 : q ∈ H₀ := joint_first_point_blowup_positive_normal_contact.2.2.2.2.2.1
  have hq1 : q ∉ H₁ := by
    intro h1
    have hLevel := bornAnchor_level
    change boundaryCount [H₀,H₁] q = 1 at hLevel
    classical
    have hBoth : Finset.univ.filter (fun i : Fin ([H₀,H₁].length) => q ∈ [H₀,H₁].get i) =
        Finset.univ := by
      ext i
      fin_cases i
      · exact iff_of_true (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq0⟩) (Finset.mem_univ _)
      · exact iff_of_true (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩) (Finset.mem_univ _)
    unfold boundaryCount at hLevel
    rw [hBoth] at hLevel
    simp at hLevel
  have hOff0 : offCentreAnchor ∈ H₀ := subset_closure (show π offCentreAnchor ∈ D 0 \ {p₀} from by
    refine ⟨?_, offCentreAnchor_off⟩
    rw [offCentreAnchor_proj]
    change (projection U (zeroSection U a₁)).val 0 = 0
    rw [projection_of_zero]
    simp [a₁])
  have hE0 : E ≠ H₀ := fun he => offCentreAnchor_off (show offCentreAnchor ∈ E from he.symm ▸ hOff0)
  have hE1 : E ≠ H₁ := fun he => hq1 (he ▸ hqE)
  let metric (j : ℕ) :=
    let H := head B j
    boundaryCount (((geoTransformAlong (barMarked padded) H).E.filter
      (fun D => decide (D ∉ origMembers padded H))).map (strictAlong (tail B j))) q
  change metric (regimeRun (stepRegime padded 1) B q) = 1
  apply (congrArg (fun j => metric j = 1) hRun).mpr
  change boundaryCount (([H₀,H₁,E].filter (fun H => decide (H ∉ [H₀,H₁]))).map
    (strictAlong (.refl : BlowupTower Y Y))) q = 1
  have hFiltered : [H₀,H₁,E].filter (fun H => decide (H ∉ [H₀,H₁])) = [E] := by
    simp [hE0, hE1]
  rw [hFiltered]
  change boundaryCount [E] q = 1
  classical
  unfold boundaryCount
  have hSlot : Finset.univ.filter (fun i : Fin ([E].length) => q ∈ [E].get i) = Finset.univ := by
    ext i
    fin_cases i
    exact iff_of_true (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqE⟩) (Finset.mem_univ _)
  rw [hSlot]
  rfl



/-- Two actual survivors of one common canonical positive prefix have
equal original level but unequal retained upper-head counts. -/
theorem common_canonical_prefix_has_unequal_retained_counts :
    IsCanonical padded (Seq.StepOneValueMasked.stepOneInvM (invFamily (by decide : 0 < 3) 2) padded) B ∧
    IsCanonical sectionRecord (Seq.StepOneValueMasked.stepOneInvM (invFamily (by decide : 0 < 3) 1) sectionRecord) B ∧
    q ∈ (geoTransformAlong padded B).cosupp ∧ offCentreAnchor ∈ (geoTransformAlong padded B).cosupp ∧
    level padded B q = 1 ∧ level padded B offCentreAnchor = 1 ∧
    upperHeadNonOriginalBoundaryCount source B 0 q = 1 ∧
      upperHeadNonOriginalBoundaryCount source B 0 offCentreAnchor = 0 :=
  ⟨two_zero_first_blowup_common_canonical.1, two_zero_first_blowup_common_canonical.2,
    two_zero_born_survivor, offCentreAnchor_survives, bornAnchor_level, offCentreAnchor_level,
    bornAnchor_has_one_head_count, offCentreAnchor_has_zero_head_count⟩

end
end Hironaka.HironakaG1TwoZeroBornCounts
