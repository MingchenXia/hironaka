import Hironaka.Resolution.HironakaG1TwoZeroSourceCharts

/-! # The same-Q principal divisor variant of the two-anchor example -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1CartierTwoAnchors
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec ResolutionDriver CanonicalCentres StepOneValue
  MemberInterAlong MemberInterTowerAlong RestrictedIdealExtension GermIdealOrder RelativePrincipalizationSpan BlowupControlledTransform IdealOrderArithmetic
  BlowupStrictSubmanifold TransformOffCentre GermIdealPullbackCalculus
  HironakaSmoothSubmersionOrderedChoiceImageTrace HironakaG1LaterPositiveSelectedExample
  BlowupMonomialCharts BlowupFlatCoordinates BlowupFunctionTransform
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaActualRelativeNormalGeometry InvertibleIdealQuotient DivisorExponentAlong NormalCrossings
  HironakaActualCoherentWeightedCoefficientMarked HironakaActualWeightedNormalPadding
  HironakaPrincipalizationBoundary HironakaActualOpenZeroSectionDifferentials
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact
  HironakaG1ProperCarrierNormalLocalClass HironakaRelativeNormalIdeal
  HironakaG8MemberLoci HironakaG1LaterPositiveNormalExample HironakaAdmissibleSequence
  HironakaG1TwoZeroBornCounts HironakaG1TwoZeroSourceCharts BoundaryCount
  HironakaG1LaterLiteralSectionMixedStratum HironakaG1ActualLaterSuccessorRead HironakaG1LaterPositiveBranchOrder HironakaG8PowerLowerMarks
  StepOneRegime StepOneValueMasked HironakaG1LaterMixedUpperBornTrace HironakaG1NonemptyHeadMixedTrace
  HomogenizedGlueingTower BlowupTowerSplit
  HironakaG8TransverseCarrierIdeal BlowupExistenceOriginIdeal MemberInterLocusAlong
  HironakaG1PositiveNormalNonspecialExample HomogenizedIdealAlong

def linearGenerator (_ : Unit) (z : ComplexModel 2) : ℂ := z 0

abbrev modelIdeal : GermIdeal 2 (ComplexModel 2) := finiteFunctionIdeal linearGenerator
abbrev record : MarkedIdeal 2 U := sourceWithIdeal modelIdeal
abbrev P := properNormalMarked record
abbrev S := sectionMarked record

private theorem linear_hol (j : Unit) :
    MDifferentiable 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ℂ) (linearGenerator j) :=
  (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2)).mdifferentiable

private theorem modelIdeal_nonzero (z : ComplexModel 2) :
    IsNonzeroAlongAt univ modelIdeal z := by
  apply isNonzeroAlongAt_univ_iff_exists.mpr
  let f : ComplexModel 2 → ℂ := EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2)
  have hf : HolomorphicAt 2 f z := Eventually.of_forall fun _ =>
    (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2)).mdifferentiableAt
  refine ⟨f, isInSpanAt_self ⟨(), rfl⟩ hf, ?_⟩
  by_contra! h
  have hzero : f =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := h
  have hd := hzero.fderiv_eq (𝕜 := ℂ)
  change fderiv ℂ (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2)) z =
    fderiv ℂ (fun _ : ComplexModel 2 => (0 : ℂ)) z at hd
  rw [ContinuousLinearMap.fderiv, fderiv_const_apply] at hd
  have hbad := congrArg (fun L : ComplexModel 2 →L[ℂ] ℂ => L (PiLp.single 2 (0 : Fin 2) 1)) hd
  simp at hbad

theorem record_domain : IsInvDomain 2 record := by
  let A : MarkedIdeal 2 (CMfd.of (n := 2) (ComplexModel 2)) := ⟨univ, [], modelIdeal, 1⟩
  have hA : IsInvDomain 2 A := isInvDomain_univ_of_isSNCDivisor
    (isCoherent_finiteFunctionIdeal linearGenerator linear_hol) modelIdeal_nonzero isSNCDivisor_nil
  have hU := InvDomainTowerAlong.isInvDomain_pullback_val U hA
  exact isInvDomain_univ_of_isSNCDivisor hU.isWellFormed.isCoherent
    (fun z => hU.isNonzeroAlongAt z (mem_univ _)) source_domain.isWellFormed.isSNCDivisor

theorem record_cosupport : record.cosupp = {z | z.val 0 = 0} := by
  ext z
  let g := fun j => linearGenerator j ∘ (Subtype.val : U → ComplexModel 2)
  have hVal : ContMDiff 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ComplexModel 2) ∞
      (Subtype.val : U → ComplexModel 2) := contMDiff_subtype_val
  have hG (j : Unit) : HolomorphicAt 2 (g j) z :=
    Eventually.of_forall fun w => (linear_hol j).mdifferentiableAt.comp w
      ((hVal.mdifferentiable (by simp)) w)
  change z ∈ cosupport 2 univ
    (GermIdeal.pullback (m := 2) (Subtype.val : U → ComplexModel 2) modelIdeal) 1 ↔ z.val 0 = 0
  rw [finiteFunctionIdeal_pullback linearGenerator linear_hol _ hVal,
    mem_cosupport_finiteFunctionIdeal_iff _ z 1 hG]
  constructor
  · exact fun hz => (vanishesToOrderOn_one_iff (mem_univ z) (hG ())).mp (hz ())
  · intro hz j
    exact (vanishesToOrderOn_one_iff (mem_univ z) (hG j)).mpr hz

theorem padded_cosupport : P.cosupp = zeroSection U '' {z | z.val 0 = 0} := by
  rw [properNormalMarked_cosupp record record_domain, record_cosupport]

theorem section_cosupport : S.cosupp = zeroSection U '' {z | z.val 0 = 0} :=
  ((((properNormalMarked_locWPEquiv_section record record_domain).wEquiv.2 emptyTower).2 trivial).symm).trans
    padded_cosupport

private theorem projection_zero (a : U) : projection U (zeroSection U a) = a := by
  apply Subtype.ext
  exact tangentProjection_tangentInclusion 2 1 a

private theorem level_on_divisor (a : U) (ha : a.val 0 = 0) :
    level P emptyTower (zeroSection U a) = if a.val 1 = 0 then 2 else 1 := by
  classical
  let D (i : Fin 2) : Set HironakaG1TwoZeroBornCounts.X := projection U ⁻¹' {z : U | z.val i = 0}
  let p := zeroSection U a
  have h0 : p ∈ D 0 := by
    change (projection U (zeroSection U a)).val 0 = 0
    rw [projection_zero]
    exact ha
  have h1 : p ∈ D 1 ↔ a.val 1 = 0 := by
    change ((projection U (zeroSection U a)).val 1 = 0) ↔ _
    rw [projection_zero]
  change boundaryCount [D 0,D 1] p = _
  unfold boundaryCount
  by_cases h : a.val 1 = 0
  · have he : Finset.univ.filter (fun i : Fin ([D 0,D 1].length) => p ∈ [D 0,D 1].get i) =
        Finset.univ := by
      ext i
      fin_cases i
      · exact iff_of_true (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩) (Finset.mem_univ _)
      · exact iff_of_true (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1.mpr h⟩) (Finset.mem_univ _)
    rw [he, if_pos h]
    rfl
  · have he : Finset.univ.filter (fun i : Fin ([D 0,D 1].length) => p ∈ [D 0,D 1].get i) =
        {0} := by
      ext i
      fin_cases i
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        change p ∈ D 0 ↔ (0 : Fin 2) = 0
        exact iff_of_true h0 rfl
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        change p ∈ D 1 ↔ (1 : Fin 2) = 0
        exact iff_of_false (h ∘ h1.mp) (by decide)
    rw [he, if_neg h]
    rfl

/-- The whole Cartier divisor is initial cosupport, and the unique
level-two point is the common origin. -/
theorem level_two_iff_origin {x : HironakaG1TwoZeroBornCounts.X} (hx : x ∈ P.cosupp) :
    level P emptyTower x = 2 ↔ x = p₀ := by
  obtain ⟨a, ha, rfl⟩ := padded_cosupport ▸ hx
  rw [level_on_divisor a ha]
  by_cases h : a.val 1 = 0
  · have he : a = a₀ := by
      apply Subtype.ext
      ext i
      fin_cases i
      · exact ha
      · exact h
    simp [he, p₀, a₀]
  · rw [if_neg h]
    constructor
    · intro hf
      exact ((by decide : (1 : ℕ) ≠ 2) hf).elim
    · intro e
      apply (h ?_).elim
      have eq := congrArg (fun x => (projection U x).val (1 : Fin 2)) e
      change (projection U (zeroSection U a)).val 1 = (projection U (zeroSection U a₀)).val 1 at eq
      rw [projection_zero, projection_zero] at eq
      exact eq

private theorem first_max {J : MarkedIdeal 3 HironakaG1TwoZeroBornCounts.X}
    (hCos : J.cosupp = P.cosupp) (hE : J.E = P.E) (k : ℕ) :
    maxLocus (Seq.StepOneValueMasked.stepOneInvM (invFamily (by decide : 0 < 3) k) J emptyTower)
      J.cosupp = {p₀} := by
  let f := Seq.StepOneValueMasked.stepOneInvM (invFamily (by decide : 0 < 3) k) J emptyTower
  have hp : p₀ ∈ P.cosupp := by
    rw [padded_cosupport]
    exact ⟨a₀, rfl, rfl⟩
  have hpLevel : level J emptyTower p₀ = 2 :=
    (level_eq_of_E_eq hE emptyTower p₀).trans ((level_two_iff_origin hp).mpr rfl)
  have hlt (x : HironakaG1TwoZeroBornCounts.X) (hx : x ∈ P.cosupp) (hne : x ≠ p₀) : f x < f p₀ := by
    have hc : level P emptyTower x < 2 := by
      obtain ⟨a, ha, rfl⟩ := padded_cosupport ▸ hx
      rw [level_on_divisor a ha]
      have he := fun h : a.val 1 = 0 => hne ((level_two_iff_origin hx).mp (by
        rw [level_on_divisor a ha, if_pos h]))
      rw [if_neg he]
      decide
    change Seq.StepOneValueMasked.stepOneInvM _ J emptyTower x <
      Seq.StepOneValueMasked.stepOneInvM _ J emptyTower p₀
    rw [Prod.Lex.lt_iff, Seq.StepOneValueMasked.stepOneInvL_fst,
      Seq.StepOneValueMasked.stepOneInvL_fst, hpLevel, level_eq_of_E_eq hE]
    exact Or.inl hc
  rw [hCos]
  ext x
  constructor
  · intro hx
    by_contra he
    exact (not_lt_of_ge (hx.2 p₀ hp)) (hlt x hx.1 he)
  · intro hx
    have he : x = p₀ := mem_singleton_iff.mp hx
    subst x
    refine ⟨hp, fun y hy => ?_⟩
    by_cases he : y = p₀
    · rw [he]
    · exact (hlt y hy he).le

/-- The same genuine point blowup is the first canonical step for both
literal records derived from the single principal-divisor source. -/
theorem cartier_common_first_canonical :
    IsCanonical P (Seq.StepOneValueMasked.stepOneInvM (invFamily (by decide : 0 < 3) 2) P) B ∧
    IsCanonical S (Seq.StepOneValueMasked.stepOneInvM (invFamily (by decide : 0 < 3) 1) S) B :=
  ⟨⟨trivial,Or.inr (first_max (J := P) rfl rfl 2).symm⟩,
   ⟨trivial,Or.inr (first_max (J := S) (section_cosupport.trans padded_cosupport.symm) rfl 1).symm⟩⟩

private theorem pullback_le {n m : ℕ} {A : CMfd.{0} n} {B : CMfd.{0} m}
    {I J : GermIdeal n A} (h : I.Le J) (f : B → A) :
    (GermIdeal.pullback (m := m) f I).Le (GermIdeal.pullback (m := m) f J) := by
  intro x g hg
  exact GermIdeal.mem_pullback_iff.mpr ((GermIdeal.mem_pullback_iff.mp hg).mono
    (by rintro s ⟨a,ha,rfl⟩; exact ⟨a,h _ _ ha,rfl⟩))

private theorem padded_le_two_zero : P.ideal.Le padded.ideal := by
  let X := HironakaG1TwoZeroBornCounts.X
  have hModel : modelIdeal.Le sourceIdeal := by
    intro x g hg
    exact IsInSpanAt.mono (by rintro _ ⟨⟨⟩,rfl⟩; exact ⟨true,rfl⟩) hg
  have hSource : record.ideal.Le source.ideal :=
    pullback_le (A := CMfd.of (n := 2) (ComplexModel 2)) (B := CMfd.of (n := 2) U) hModel Subtype.val
  have hSection := pullback_le (A := CMfd.of (n := 2) U) (B := X) hSource (projection U)
  intro x g hg
  exact mem_sumIdeal_iff.mpr ((mem_sumIdeal_iff.mp hg).mono (fun f h =>
    h.elim (fun h => Or.inl (hSection x f h)) Or.inr))

set_option maxHeartbeats 1100000 in
/-- The same-Q Cartier variant preserves both concrete survivors after
the common first canonical step. -/
theorem cartier_born_and_off_survive :
    q ∈ (geoTransformAlong P B).cosupp ∧ offCentreAnchor ∈ (geoTransformAlong P B).cosupp := by
  let X := HironakaG1TwoZeroBornCounts.X
  have hP := properNormalMarked_isInvDomain record record_domain
  have hQ := properNormalMarked_isInvDomain source source_domain
  have hCar : (geoTransformAlong P B).N = (geoTransformAlong padded B).N := rfl
  have hLe : (geoTransformAlong P B).ideal.Le (geoTransformAlong padded B).ideal := by
    change (P.geoTransform {p₀} π).ideal.Le (padded.geoTransform {p₀} π).ideal
    have hNew : (P.geoTransform {p₀} π).ideal = controlledTransform hπ P.ideal 1 :=
      geoTransform_ideal_eq_controlledTransform (𝔪 := P) (show P.N = univ from preimage_univ)
        hP.isWellFormed.isCoherent hπ
    have hOld : (padded.geoTransform {p₀} π).ideal = controlledTransform hπ padded.ideal 1 :=
      geoTransform_ideal_eq_controlledTransform (𝔪 := padded) (show padded.N = univ from preimage_univ)
        hQ.isWellFormed.isCoherent hπ
    rw [hNew, hOld]
    intro z f hf
    obtain ⟨hHol, hProd⟩ := mem_colon_iff.mp hf
    exact mem_colon_iff.mpr ⟨hHol, fun g hg =>
      pullback_le (A := X) (B := Y) padded_le_two_zero π _ _ (hProd _ hg)⟩
  have hOf (z : Y) (hz : z ∈ (geoTransformAlong padded B).cosupp) :
      z ∈ (geoTransformAlong P B).cosupp := ⟨hCar.symm ▸ hz.1, fun g hg => by
    rw [hCar]
    exact hz.2 g (hLe _ _ hg)⟩
  exact ⟨hOf q two_zero_born_survivor, hOf offCentreAnchor offCentreAnchor_survives⟩

private def twoGenerator (j : Bool) (x : HironakaG1TwoZeroBornCounts.X) : ℂ :=
  if j then x.val 0 else x.val 2

private theorem twoGenerator_hol (j : Bool) :
    MDifferentiable 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ℂ) (twoGenerator j) := by
  let v : HironakaG1TwoZeroBornCounts.X → ComplexModel 3 := Subtype.val
  have hv : ContMDiff 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ComplexModel 3) ∞ v := contMDiff_subtype_val
  cases j
  · exact (EuclideanSpace.proj (𝕜 := ℂ) (2 : Fin 3)).mdifferentiable.comp (hv.mdifferentiable (by simp))
  · exact (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 3)).mdifferentiable.comp (hv.mdifferentiable (by simp))

set_option maxHeartbeats 1000000 in
private theorem padded_generators : P.ideal = finiteFunctionIdeal (n := 3) twoGenerator := by
  let X := HironakaG1TwoZeroBornCounts.X
  let v : U → ComplexModel 2 := Subtype.val
  let f : X → ComplexModel 2 := v ∘ projection U
  have hv : ContMDiff 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ComplexModel 2) ∞ v := contMDiff_subtype_val
  have hf := hv.comp (projection_contMDiff U)
  have hSec : S.ideal = finiteFunctionIdeal (n := 3) (fun _ : Unit => fun x : X => x.val 0) := by
    change GermIdeal.pullback (m := 3) (projection U) (GermIdeal.pullback (m := 2) v modelIdeal) = _
    rw [← coherent_pullback_comp hv (projection_contMDiff U) modelIdeal
      (isCoherent_finiteFunctionIdeal linearGenerator linear_hol)]
    rw [finiteFunctionIdeal_pullback linearGenerator linear_hol f hf]
    rfl
  have hNormal : (fun _ : Unit => fun x : X => relativeNormalCoordinate U x ^ 1) =
      fun _ : Unit => fun x : X => x.val 2 := by
    funext j x
    simp [relativeNormalCoordinate, HironakaActualZeroCoordinateContactSeed.addedCoordinate,
      HironakaActualGraphFunctionalIdeal.graphFunction, HironakaActualZeroCoordinateContactSeed.zeroFunction]
  change sumIdeal S.ideal (finiteFunctionIdeal (n := 3)
    (fun _ : Unit => fun x : X => relativeNormalCoordinate U x ^ 1)) = _
  rw [hSec, hNormal]
  apply GermIdeal.ext
  funext x g
  apply propext
  constructor
  · intro hg
    refine IsInSpanAt.trans ?_ (mem_sumIdeal_iff.mp hg)
    rintro b (hb | hb)
    · exact hb.mono (by rintro _ ⟨j,rfl⟩; exact ⟨true,rfl⟩)
    · exact hb.mono (by rintro _ ⟨j,rfl⟩; exact ⟨false,rfl⟩)
  · intro hg
    refine mem_sumIdeal_iff.mpr (IsInSpanAt.mono ?_ hg)
    rintro _ ⟨j,rfl⟩
    cases j
    · exact Or.inr (isInSpanAt_self ⟨(),rfl⟩ (Eventually.of_forall fun y => twoGenerator_hol false y))
    · exact Or.inl (isInSpanAt_self ⟨(),rfl⟩ (Eventually.of_forall fun y => twoGenerator_hol true y))

abbrev linearLine : Set HironakaG1TwoZeroBornCounts.X :=
  {x | x.val (0 : Fin 3) = 0 ∧ x.val (2 : Fin 3) = 0}

private theorem product_top : productOpen U = ⊤ := by
  ext z
  exact iff_of_true (mem_univ _) (mem_univ _)

set_option maxHeartbeats 1400000 in
private theorem padded_ideal_is_line_vanishing :
    P.ideal = vanishingIdeal (n := 3) linearLine := by
  rw [padded_generators]
  let X := HironakaG1TwoZeroBornCounts.X
  let A : Finset (Fin 3) := {0,2}
  have hChart (x : X) : chartAt (ComplexModel 3) p₀ x = x.val := by
    rw [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq]
    rfl
  let φ : LocalHolomorphicEquivAt (n := 3) (chartAt (ComplexModel 3) p₀ p₀) :=
    { source := univ, target := univ, isOpen_source := isOpen_univ, isOpen_target := isOpen_univ
      center_mem_source := mem_univ _, toFun := id, invFun := id
      toFun_holomorphic := differentiable_id.differentiableOn
      invFun_holomorphic := differentiable_id.differentiableOn
      mapsTo_toFun := mapsTo_univ _ _, mapsTo_invFun := mapsTo_univ _ _
      left_inv := fun _ _ => rfl, right_inv := fun _ _ => rfl }
  have hφsource : φ.source = univ := rfl
  have hφ (z : ComplexModel 3) : φ.toFun z = z := rfl
  have hT (z : ComplexModel 3) : z ∈ (chartAt (ComplexModel 3) p₀).target := by
    rw [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq]
    have hz : z ∈ productOpen U := by rw [product_top]; exact mem_univ _
    exact (OpenPartialHomeomorph.refl (ComplexModel 3)).map_subtype_source
      ⟨p₀⟩ (x := ⟨z,hz⟩) (mem_univ _)
  have hFlat {x : X} : x ∈ linearLine ↔ φ.toFun (chartAt (ComplexModel 3) p₀ x) ∈ coordSubspace A := by
    rw [hφ,hChart]
    change (x.val 0 = 0 ∧ x.val 2 = 0) ↔ _
    simp [coordSubspace, A]
  apply GermIdeal.ext
  funext x g
  apply propext
  have hx : x ∈ flatDomain φ := by
    refine ⟨?_, ?_⟩
    · rw [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq]
      rw [OpenPartialHomeomorph.subtypeRestr_source]
      exact mem_univ _
    · rw [hφsource]
      exact mem_univ _
  rw [mem_vanishingIdeal_iff_coordinate_span φ (fun z _ => hT z) A linearLine
    (fun _ _ => hFlat) hx]
  have hF (i : Fin 3) (z : X) : flatCoord φ i z = z.val i := by
    unfold flatCoord
    rw [hφ,hChart]
  constructor
  · intro hg
    apply IsInSpanAt.mono _ hg
    rintro _ ⟨j,rfl⟩
    cases j
    · exact ⟨2, funext fun z => by simp [A, hF, twoGenerator]⟩
    · exact ⟨0, funext fun z => by simp [A, hF, twoGenerator]⟩
  · intro hg
    refine IsInSpanAt.trans ?_ hg
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · have he : (if (0 : Fin 3) ∈ A then flatCoord φ 0 else fun _ => (0 : ℂ)) =
          twoGenerator true := by
        rw [if_pos (by simp [A])]
        exact funext fun z => hF _ z
      change IsInSpanAt (n := 3) (· ∈ range twoGenerator) x
        (if (0 : Fin 3) ∈ A then flatCoord φ 0 else fun _ => (0 : ℂ))
      rw [he]
      exact isInSpanAt_self ⟨true,rfl⟩ (Eventually.of_forall fun z => twoGenerator_hol true z)
    · have hNot : (1 : Fin 3) ∉ A := by decide
      change IsInSpanAt (n := 3) (· ∈ range twoGenerator) x
        (if (1 : Fin 3) ∈ A then flatCoord φ 1 else fun _ => (0 : ℂ))
      rw [if_neg hNot]
      exact BlowupStrictIdeal.isInSpanAt_zero
    · have he : (if (2 : Fin 3) ∈ A then flatCoord φ 2 else fun _ => (0 : ℂ)) =
          twoGenerator false := by
        rw [if_pos (by simp [A])]
        exact funext fun z => hF _ z
      change IsInSpanAt (n := 3) (· ∈ range twoGenerator) x
        (if (2 : Fin 3) ∈ A then flatCoord φ 2 else fun _ => (0 : ℂ))
      rw [he]
      exact isInSpanAt_self ⟨false,rfl⟩ (Eventually.of_forall fun z => twoGenerator_hol false z)

private theorem section_carrier_coordinate : S.N = {x : HironakaG1TwoZeroBornCounts.X | x.val (2 : Fin 3) = 0} := by
  ext x
  constructor
  · intro hx
    exact congrArg (fun w : ComplexModel 1 => w (0 : Fin 1)) hx.2
  · intro hx
    refine ⟨mem_univ _, ?_⟩
    ext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    rw [hi]
    exact hx

private def oldZero : Finset (Fin S.E.length) := {⟨0, by decide⟩}
private def allOld : Finset (Fin S.E.length) := Finset.univ

private theorem line_eq_member : linearLine = S.N ∩ memberInter S.E oldZero := by
  rw [section_carrier_coordinate]
  ext x
  change (_ ∧ _) ↔ (_ ∧ ((∀ i ∈ oldZero, x ∈ S.E.get i)))
  have he : S.E.get (⟨0,by decide⟩ : Fin S.E.length) = {a | a.val (0 : Fin 3) = 0} := rfl
  rw [show (∀ i ∈ oldZero, x ∈ S.E.get i) ↔ x ∈ S.E.get ⟨0,by decide⟩ by simp [oldZero], he]
  exact and_comm

private theorem section_domain : IsInvDomain 2 S :=
  HironakaActualSectionBoundaryGeometry.section_projected_domain 2 record.N record.E record.ideal
    record.d record_domain

private theorem padded_test : IsGeoTestTower P B :=
  (Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (invFamily (by decide : 0 < 3) 2) P (properNormalMarked_isInvDomain record record_domain)
    (properNormalMarked_maximalOrder record record_domain.isWellFormed.isCoherent)
    (by decide) B cartier_common_first_canonical.1).2.1

private theorem section_test : IsGeoTestTower S B :=
  ((properNormalMarked_locWPEquiv_section record record_domain).wEquiv.2 B).1.mp padded_test

set_option maxHeartbeats 1200000 in
/-- The whole first padded cosupport is the actual strict transform of
the same-Q source line. -/
theorem cartier_endpoint_cosupport :
    (geoTransformAlong P B).cosupp = geoStrictTransform π {p₀} linearLine := by
  have hP := properNormalMarked_isInvDomain record record_domain
  have hL : IsClosedSubmanifold 3 linearLine := by
    rw [line_eq_member]
    exact isClosedSubmanifold_inter_memberInter (by decide) section_domain.isWellFormed.isClosedSubmanifold_N.1
      section_domain.isWellFormed.isSNCDivisor section_domain.isWellFormed.isTransverse oldZero
  have hp : ({p₀} : Set HironakaG1TwoZeroBornCounts.X) ⊆ linearLine := by
    intro x hx
    have hx' : x = p₀ := mem_singleton_iff.mp hx
    subst x
    have hp0 : p₀.val = 0 := map_zero (tangentInclusion 2 1)
    exact ⟨congrArg (fun z : ComplexModel 3 => z 0) hp0,
      congrArg (fun z : ComplexModel 3 => z 2) hp0⟩
  have hIdeal : (geoTransformAlong P B).ideal =
      vanishingIdeal (n := 3) (geoStrictTransform π {p₀} linearLine) := by
    have hC : (geoTransformAlong P B).ideal = controlledTransform hπ P.ideal 1 :=
      geoTransform_ideal_eq_controlledTransform (𝔪 := P) (show P.N = univ from preimage_univ)
        hP.isWellFormed.isCoherent hπ
    rw [hC, padded_ideal_is_line_vanishing]
    exact BlowupStrictIdeal.controlledTransform_vanishingIdeal hπ hL hp
  have hN : (geoTransformAlong P B).N = univ := by
    change geoStrictTransform π {p₀} P.N = univ
    rw [show P.N = univ from preimage_univ]
    exact geoStrictTransform_univ hπ
  change cosupport 3 (geoTransformAlong P B).N (geoTransformAlong P B).ideal 1 = _
  rw [hN, hIdeal, cosupport_one SmoothCentreLocus.holomorphicAt_of_mem_vanishingIdeal,
    univ_inter]
  exact BlowupExceptionalDivisor.zeroLocus_vanishingIdeal
    (show IsClosed (geoStrictTransform π {p₀} linearLine) from isClosed_closure)

private abbrev D (i : Fin 2) : Set HironakaG1TwoZeroBornCounts.X :=
  projection U ⁻¹' {z : U | z.val i = 0}
private abbrev H (i : Fin 2) : Set Y := geoStrictTransform π {p₀} (D i)
private abbrev V := geoStrictTransform π {p₀} S.N

private theorem centre_in_section : ({p₀} : Set HironakaG1TwoZeroBornCounts.X) ⊆ S.N :=
  fun _ hx => S.cosupp_subset_N (section_test.2.2.1 hx)

private theorem section_endpoint_cosupport :
    (geoTransformAlong S B).cosupp = V ∩ H 0 := by
  have hCos := ((properNormalMarked_locWPEquiv_section record record_domain).wEquiv.2 B).2 padded_test
  rw [← hCos, cartier_endpoint_cosupport, line_eq_member]
  have h := geoStrictTransform_inter_memberInter_eq hπ section_domain.isWellFormed.isClosedSubmanifold_N.1
    centre_in_section
    section_domain.isWellFormed.isSNCDivisor section_domain.isWellFormed.isTransverse
    section_test.2.2.2 oldZero
  change geoStrictTransform π {p₀} (S.N ∩ memberInter S.E oldZero) =
    V ∩ {z | ∀ i ∈ oldZero, z ∈ geoStrictTransform π {p₀} (S.E.get i)} at h
  rw [h]
  ext y
  simp only [mem_inter_iff, mem_ofPred_eq, oldZero, Finset.mem_singleton]
  exact and_congr_right fun _ => ⟨fun hp => hp _ rfl, fun hp i hi => hi.symm ▸ hp⟩

private theorem source_three_inter_eq_centre :
    S.N ∩ memberInter S.E allOld = {p₀} := by
  ext x
  rw [section_carrier_coordinate]
  constructor
  · rintro ⟨h2,hh⟩
    have h0 : x.val (0 : Fin 3) = 0 := hh ⟨0,by decide⟩ (Finset.mem_univ _)
    have h1 : x.val (1 : Fin 3) = 0 := hh ⟨1,by decide⟩ (Finset.mem_univ _)
    apply mem_singleton_iff.mpr
    apply Subtype.ext
    rw [show p₀.val = 0 from map_zero (tangentInclusion 2 1)]
    ext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · intro hx
    obtain rfl := mem_singleton_iff.mp hx
    have hp0 : p₀.val = 0 := map_zero (tangentInclusion 2 1)
    refine ⟨congrArg (fun z : ComplexModel 3 => z 2) hp0, fun i _ => ?_⟩
    fin_cases i
    · exact congrArg (fun z : ComplexModel 3 => z 0) hp0
    · exact congrArg (fun z : ComplexModel 3 => z 1) hp0

private theorem section_endpoint_off_second {y : Y} (hy : y ∈ (geoTransformAlong S B).cosupp) :
    y ∉ H 1 := by
  have ht := geoStrictTransform_inter_memberInter_eq hπ section_domain.isWellFormed.isClosedSubmanifold_N.1
    centre_in_section section_domain.isWellFormed.isSNCDivisor section_domain.isWellFormed.isTransverse
    section_test.2.2.2 allOld
  change geoStrictTransform π {p₀} (S.N ∩ memberInter S.E allOld) =
    V ∩ {z | ∀ i ∈ allOld, z ∈ geoStrictTransform π {p₀} (S.E.get i)} at ht
  rw [source_three_inter_eq_centre, BlowupStrictIdeal.geoStrictTransform_self] at ht
  have hy' : y ∈ V ∩ H 0 := section_endpoint_cosupport ▸ hy
  intro h1
  have hm : y ∈ geoStrictTransform π {p₀} S.N ∩ {z | ∀ i ∈ allOld, z ∈ geoStrictTransform π {p₀} (S.E.get i)} := by
    refine ⟨hy'.1, fun i _ => ?_⟩
    fin_cases i
    · exact hy'.2
    · exact h1
  exact (ht.symm ▸ hm : y ∈ (∅ : Set Y))

private theorem section_endpoint_level {y : Y} (hy : y ∈ (geoTransformAlong S B).cosupp) :
    level S B y = 1 := by
  have h0 : y ∈ H 0 := (show y ∈ V ∩ H 0 from section_endpoint_cosupport ▸ hy).2
  have h1 := section_endpoint_off_second hy
  change boundaryCount [H 0,H 1] y = 1
  classical
  have he : Finset.univ.filter (fun i : Fin ([H 0,H 1].length) => y ∈ [H 0,H 1].get i) = {0} := by
    ext i
    fin_cases i
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      change y ∈ H 0 ↔ (0 : Fin 2) = 0
      exact iff_of_true h0 rfl
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      change y ∈ H 1 ↔ (1 : Fin 2) = 0
      exact iff_of_false h1 (by decide)
  unfold boundaryCount
  rw [he]
  rfl

private theorem section_bar_eq : barMarked (X := HironakaG1TwoZeroBornCounts.X) S = S := by
  change coeffMarkedAlong (homMarkedAlong S) = S
  have hHom : homMarkedAlong (M := HironakaG1TwoZeroBornCounts.X) S = S :=
    homMarkedAlong_eq_of_mark_one (X := HironakaG1TwoZeroBornCounts.X) S rfl section_domain.isWellFormed.isCoherent
  exact (congrArg (coeffMarkedAlong (M := HironakaG1TwoZeroBornCounts.X)) hHom).trans
    (coeffMarkedAlong_eq_of_mark_one (X := HironakaG1TwoZeroBornCounts.X) S rfl section_domain.isWellFormed.isCoherent)

theorem cartier_section_endpoint_all_special {y : Y} (hy : y ∈ (geoTransformAlong S B).cosupp) :
    IsSpecial S B y := by
  have h0 : y ∈ H 0 := (show y ∈ V ∩ H 0 from section_endpoint_cosupport ▸ hy).2
  right
  refine ⟨(section_endpoint_level hy).ge, ?_⟩
  rw [section_bar_eq]
  apply mem_memberInterLocus_iff.mpr
  refine ⟨hy, Eventually.of_forall fun z hz hMembers => ?_⟩
  have hz0 : z ∈ H 0 := hMembers (H 0) (by change H 0 ∈ [H 0,H 1]; simp) h0
  exact section_endpoint_cosupport.symm ▸ (show z ∈ V ∩ H 0 from ⟨hz,hz0⟩)

private theorem section_max_of_all_special {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) {Y : CMfd.{0} (n+1)}
    (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (hLevel : ∀ y ∈ (geoTransformAlong (sectionMarked Q) T).cosupp, level (sectionMarked Q) T y = 1)
    (hSpecial : ∀ y ∈ (geoTransformAlong (sectionMarked Q) T).cosupp, IsSpecial (sectionMarked Q) T y) :
    maxLocus (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) (sectionMarked Q) T)
       (geoTransformAlong (sectionMarked Q) T).cosupp = (geoTransformAlong (sectionMarked Q) T).cosupp := by
  have hv (y : Y) (hy : y ∈ (geoTransformAlong (sectionMarked Q) T).cosupp) :=
    later_literal_section_special_read (n := n) (k := k) (s := 0) (Y := Y) Q T y
      (hLevel y hy) (hSpecial y hy)
  ext y
  constructor
  · exact fun hy => hy.1
  · intro hy
    exact ⟨hy, fun z hz => (hv z hz).le.trans (hv y hy).symm.le⟩

theorem cartier_section_maximum_eq_cosupport :
    maxLocus (Seq.StepOneValueMasked.stepOneInvM (invFamily (by decide : 0 < 3) 1) S B)
       (geoTransformAlong S B).cosupp = (geoTransformAlong S B).cosupp :=
  section_max_of_all_special (n := 2) (k := 1) (Y := Y) record B
    (fun y hy => section_endpoint_level (y := y) hy)
    (fun y hy => cartier_section_endpoint_all_special (y := y) hy)

theorem cartier_both_anchors_maximize_section :
    q ∈ maxLocus (Seq.StepOneValueMasked.stepOneInvM (invFamily (by decide : 0 < 3) 1) S B)
       (geoTransformAlong S B).cosupp ∧
    offCentreAnchor ∈ maxLocus (Seq.StepOneValueMasked.stepOneInvM (invFamily (by decide : 0 < 3) 1) S B)
       (geoTransformAlong S B).cosupp := by
  rw [cartier_section_maximum_eq_cosupport]
  have hCos : (geoTransformAlong P B).cosupp = (geoTransformAlong S B).cosupp :=
    ((properNormalMarked_locWPEquiv_section record record_domain).wEquiv.2 B).2 padded_test
  exact hCos ▸ cartier_born_and_off_survive

set_option maxHeartbeats 700000 in
theorem cartier_born_count :
    upperHeadNonOriginalBoundaryCount record B 0 q = 1 := by
  let X := HironakaG1TwoZeroBornCounts.X
  have hπq : π q = p₀ := joint_first_point_blowup_positive_normal_contact.2.2.2.1
  have hp : p₀ ∈ P.cosupp := by rw [padded_cosupport]; exact ⟨a₀,rfl,rfl⟩
  have hRun : regimeRun (stepRegime P 1) B q = 0 := by
    apply regimeRun_step_of_not _ emptyTower {p₀} π hπ
    rw [hπq]
    intro h
    exact (by decide : (2 : ℕ) ≠ 1) (((level_two_iff_origin hp).mpr rfl).symm.trans h.1)
  have offCentreAnchor_off : π offCentreAnchor ∉ ({p₀} : Set X) := by
    rw [offCentreAnchor_proj]
    intro hh
    have heq := congrArg (fun x => (projection U x).val (1 : Fin 2)) (mem_singleton_iff.mp hh)
    change (projection U (zeroSection U a₁)).val 1 = (projection U (zeroSection U a₀)).val 1 at heq
    rw [projection_zero, projection_zero] at heq
    simp [a₀,a₁] at heq
  let H₀ := geoStrictTransform π {p₀} (D 0)
  let H₁ := geoStrictTransform π {p₀} (D 1)
  let E : Set Y := π ⁻¹' ({p₀} : Set HironakaG1TwoZeroBornCounts.X)
  have hqE : q ∈ E := by
    change π q ∈ ({p₀} : Set HironakaG1TwoZeroBornCounts.X)
    rw [show π q = p₀ from joint_first_point_blowup_positive_normal_contact.2.2.2.1]
    exact mem_singleton _
  have hq0 : q ∈ H₀ := joint_first_point_blowup_positive_normal_contact.2.2.2.2.2.1
  have hq1 : q ∉ H₁ := by
    intro h1
    have hLevel : level P B q = 1 :=
      (level_eq_of_E_eq (A := P) (B := padded) rfl B q).trans bornAnchor_level
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
    rw [projection_zero]
    simp [a₁])
  have hE0 : E ≠ H₀ := fun he => offCentreAnchor_off (show offCentreAnchor ∈ E from he.symm ▸ hOff0)
  have hE1 : E ≠ H₁ := fun he => hq1 (he ▸ hqE)
  let metric (j : ℕ) :=
    let H := head B j
    boundaryCount (((geoTransformAlong (barMarked P) H).E.filter
      (fun D => decide (D ∉ origMembers P H))).map (strictAlong (tail B j))) q
  change metric (regimeRun (stepRegime P 1) B q) = 1
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


theorem cartier_off_count :
    upperHeadNonOriginalBoundaryCount record B 0 offCentreAnchor = 0 := by
  by_cases hReg : stepRegime P 1 emptyTower (π offCentreAnchor)
  · apply upperHeadNonOriginalBoundaryCount_eq_zero_of_full_run
    change regimeRun (stepRegime P 1) (.step emptyTower {p₀} π hπ) offCentreAnchor = 1
    exact (regimeRun_step_of _ emptyTower {p₀} π hπ hReg).trans (by rw [regimeRun_refl])
  · have hr : regimeRun (stepRegime P 1) B offCentreAnchor = 0 :=
      regimeRun_step_of_not _ emptyTower {p₀} π hπ hReg
    apply (upperHeadNonOriginalBoundaryCount_eq_zero_iff_off_endpoint record B offCentreAnchor).2
    let Test (j : ℕ) : Prop :=
      ∀ F ∈ (geoTransformAlong (barMarked P) (head B j)).E, F ∉ origMembers P (head B j) →
        offCentreAnchor ∉ strictAlong (tail B j) F
    change Test (regimeRun (stepRegime P 1) B offCentreAnchor)
    apply (congrArg Test hr).mpr
    change ∀ F ∈ ([H 0,H 1,π ⁻¹' ({p₀} : Set HironakaG1TwoZeroBornCounts.X)] : List (Set Y)),
      F ∉ [H 0,H 1] → offCentreAnchor ∉ F
    intro F hF hOld hIn
    rcases List.mem_cons.mp hF with rfl | hF
    · exact hOld List.mem_cons_self
    rcases List.mem_cons.mp hF with rfl | hF
    · exact hOld (List.mem_cons_of_mem _ List.mem_cons_self)
    have he := List.mem_singleton.mp hF
    have hf : offCentreAnchor ∈ π ⁻¹' ({p₀} : Set HironakaG1TwoZeroBornCounts.X) := he ▸ hIn
    have hh : π offCentreAnchor ∈ ({p₀} : Set HironakaG1TwoZeroBornCounts.X) := hf
    rw [offCentreAnchor_proj] at hh
    have heq := congrArg (fun x => (projection U x).val (1 : Fin 2)) (mem_singleton_iff.mp hh)
    change (projection U (zeroSection U a₁)).val 1 = (projection U (zeroSection U a₀)).val 1 at heq
    rw [projection_zero, projection_zero] at heq
    simp [a₀,a₁] at heq

private theorem padded_bar_eq : barMarked (X := HironakaG1TwoZeroBornCounts.X) P = P := by
  let X := HironakaG1TwoZeroBornCounts.X
  have hC := (properNormalMarked_isInvDomain record record_domain).isWellFormed.isCoherent
  have hHom : homMarkedAlong (M := X) P = P := homMarkedAlong_eq_of_mark_one (X := X) P rfl hC
  exact (congrArg (coeffMarkedAlong (M := X)) hHom).trans
    (coeffMarkedAlong_eq_of_mark_one (X := X) P rfl hC)

private theorem padded_to_section_cosupp :
    (geoTransformAlong P B).cosupp = (geoTransformAlong S B).cosupp :=
  ((properNormalMarked_locWPEquiv_section record record_domain).wEquiv.2 B).2 padded_test

set_option maxHeartbeats 1350000 in
private theorem padded_chart_nonspecial {y : Y} (hChart : y ∈ yChart.source)
    (hy : y ∈ (geoTransformAlong P B).cosupp) : ¬ IsSpecial P B y := by
  intro h
  have hyS : y ∈ (geoTransformAlong S B).cosupp := padded_to_section_cosupp ▸ hy
  have hLevel := (level_eq_of_E_eq (A := P) (B := S) rfl B y).trans (section_endpoint_level hyS)
  rcases h with hZ | ⟨_, hM⟩
  · exact (by decide : (1 : ℕ) ≠ 0) (hLevel.symm.trans hZ.1)
  rw [padded_bar_eq] at hM
  have hyVH : y ∈ V ∩ H 0 := section_endpoint_cosupport ▸ hyS
  have hNormal : V = geoStrictTransform π {p₀} {x : HironakaG1TwoZeroBornCounts.X | x.val (2 : Fin 3) = 0} :=
    congrArg (geoStrictTransform π {p₀}) section_carrier_coordinate
  have h0 : yChart.toFun y (0 : Fin 3) = 0 :=
    (strict_chart_coordinate 0 (by decide) y hChart).mp hyVH.2
  have h2 : yChart.toFun y (2 : Fin 3) = 0 :=
    (strict_chart_coordinate 2 (by decide) y hChart).mp (hNormal ▸ hyVH.1)
  let e := EuclideanSpace.single (2 : Fin 3) (1 : ℂ)
  let f (t : ℂ) := yChart.invFun (yChart.toFun y + t • e)
  have hf : Tendsto f (𝓝 0) (𝓝 y) := by
    have hC : Continuous (fun t : ℂ => yChart.toFun y + t • e) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hCt : Tendsto (fun t : ℂ => yChart.toFun y + t • e) (𝓝 0) (𝓝 (yChart.toFun y)) :=
      by simpa using hC.tendsto (0 : ℂ)
    exact (yChart.homeo.tendsto_symm hChart).comp hCt
  have hne : ∃ᶠ t : ℂ in 𝓝 0, t ≠ 0 := by
    have hF : ∃ᶠ t : ℂ in 𝓝[≠] 0, True :=
      Filter.Eventually.frequently (Filter.Eventually.of_forall fun _ => trivial)
    exact ((frequently_nhdsWithin_iff).mp hF).mono (fun _ ht => ht.2)
  obtain ⟨t, ht, hLoc⟩ :=
    (hne.and_eventually (hf.eventually (mem_memberInterLocus_iff.mp hM).2)).exists
  have htChart : f t ∈ yChart.source := yChart.toPartialEquiv.map_target (chart_all _)
  have hCoord : yChart.toFun (f t) = yChart.toFun y + t • e :=
    yChart.toPartialEquiv.right_inv (chart_all _)
  have htH : f t ∈ H 0 := (strict_chart_coordinate 0 (by decide) (f t) htChart).mpr (by
    rw [hCoord]
    simp [h0,e])
  have hN : (geoTransformAlong P B).N = univ := by
    change geoStrictTransform π {p₀} P.N = univ
    rw [show P.N = univ from preimage_univ]
    exact geoStrictTransform_univ hπ
  have htP : f t ∈ (geoTransformAlong P B).cosupp := by
    apply hLoc
    · rw [hN]
      exact mem_univ _
    · intro D hD hyD
      change D ∈ [H 0,H 1] at hD
      rcases List.mem_cons.mp hD with rfl | hD
      · exact htH
      · obtain rfl := List.mem_singleton.mp hD
        exact (section_endpoint_off_second hyS hyD).elim
  have htV : f t ∈ V := (show f t ∈ V ∩ H 0 from
    section_endpoint_cosupport ▸ (padded_to_section_cosupp ▸ htP)).1
  have h2t := (strict_chart_coordinate 2 (by decide) (f t) htChart).mp (hNormal ▸ htV)
  rw [hCoord] at h2t
  exact ht (by simpa [h2,e] using h2t)

set_option maxHeartbeats 1300000 in
private theorem off_padded_lt_born :
    Seq.StepOneValueMasked.stepOneInvM (invFamily (by decide : 0 < 3) 2) P B offCentreAnchor <
      Seq.StepOneValueMasked.stepOneInvM (invFamily (by decide : 0 < 3) 2) P B q := by
  have hCan := cartier_common_first_canonical.1
  have hChart : offCentreAnchor ∈ yChart.source := yChart.toPartialEquiv.map_target (chart_all _)
  have hRead (y : Y) (hChart : y ∈ yChart.source) (hy : y ∈ (geoTransformAlong P B).cosupp) :
      ∃ F : LaterPositiveRead record B y 1 0, F.order = 1 ∧
        (ofLex F.companion).1 = upperHeadNonOriginalBoundaryCount record B 0 y := by
    have hLevel : level P B y = 1 :=
      (level_eq_of_E_eq (A := P) (B := S) rfl B y).trans
        (section_endpoint_level (padded_to_section_cosupp ▸ hy))
    have hNS := padded_chart_nonspecial hChart hy
    have hOrder : LaterPositiveOrderAt record B y 0 1 := by
      unfold LaterPositiveOrderAt
      intro r H S p O A Z L R z hz
      have h := (original_upper_positive_lower_raw_mark (s := 0) record record_domain B hCan y hy
        hLevel hNS).2 z hz
      have hMark : L.d = 1 := by
        change (lowerMarkedM P 1 H p).d = 1
        rw [lowerMarkedM_succ_mark]
        decide
      exact h.trans hMark
    obtain ⟨F,hF⟩ := exists_laterPositiveRead record B y record_domain hCan hy hLevel hNS 1
      (by decide) hOrder
    exact ⟨F,hF,laterPositiveRead_companion_level_eq_upperHeadNonOriginal record B record_domain
      hCan y hy hLevel hNS F⟩
  obtain ⟨F,hF,hFC⟩ := hRead offCentreAnchor hChart cartier_born_and_off_survive.2
  obtain ⟨G,hG,hGC⟩ := hRead q chart_q.1 cartier_born_and_off_survive.1
  exact LaterPositiveRead.upper_lt_of_companion_level_lt F G (hF.trans hG.symm)
    ((hFC.trans cartier_off_count).symm ▸ (hGC.trans cartier_born_count).symm ▸ (by decide : (0 : ℕ) < 1))

/-- A common genuine canonical prefix of a single source record can
have distinct retained counts on two actual section maxima. Their
padded maximum locus differs, since the off-centre survivor is strictly
below the born survivor for the padded invariant. -/
theorem cartier_common_prefix_maximum_discrepancy :
    maxLocus (Seq.StepOneValueMasked.stepOneInvM (invFamily (by decide : 0 < 3) 2) P B)
       (geoTransformAlong P B).cosupp ≠
    maxLocus (Seq.StepOneValueMasked.stepOneInvM (invFamily (by decide : 0 < 3) 1) S B)
       (geoTransformAlong S B).cosupp := by
  intro h
  have hOff := h.symm ▸ cartier_both_anchors_maximize_section.2
  exact not_lt_of_ge (hOff.2 q cartier_born_and_off_survive.1) off_padded_lt_born

end
end Hironaka.HironakaG1CartierTwoAnchors
