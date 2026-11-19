import Hironaka.Resolution.HironakaG1RecursiveBornSelectedExample
import Hironaka.Resolution.HironakaNormalCrossingsActualResidual

/-! The exact residual generators at the survivor of the canonical point blowup. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1RecursiveBornResidualExample
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  BlowupConstruction BlowupFlatCoordinates BlowupMonomialCharts
  GermIdealOrder IdealOrderArithmetic OrderTaylor CompanionReduction IdealWeightPowers
  InvertibleIdealQuotient RelativePrincipalizationSpan InvDomainTowerAlong
  HironakaG1LaterPositiveNormalExample HironakaG1RecursiveBornFiniteExample
  HironakaG1RecursiveBornOrderExample HironakaNormalCrossingsActualResidual
  HironakaRelativeNormalIdeal HironakaActualOpenZeroSectionDifferentials
  HironakaActualNativeSectionInitialBar MonomialPartAlong MonomialPart
  DivisorExponentAlong DivisorExponent HironakaSNCSupportedMonomialIdeal
  GermIdealTotalTransform RestrictedIdealExtension NormalCrossings DivisorMetric HironakaG8CoeffClass BlowupSNCTransform HironakaNormalCrossingsFiniteMarkedCompletion

private abbrev U : Opens (ComplexModel 2) := ⊤
private abbrev X := CMfd.of (n := 3) (productOpen U)
private abbrev p : X := zeroSection U ⟨0, mem_univ _⟩
private abbrev F : Set Y := π ⁻¹' ({p} : Set X)
private abbrev A := geoTransformAlong record B
private abbrev coord (i : Fin 3) (z : Y) : ℂ := yChart.toFun z i
private def chart : ComplexChart 3 Y :=
  ⟨yChart.homeo, atlasHomeo_mem_atlas yChart.toPartialEquiv (Or.inl ⟨yChart, rfl⟩)⟩

private theorem born_iff {z : Y} (hz : z ∈ yChart.source) :
    z ∈ F ↔ coord 1 z = 0 := by
  have hp : p.val = 0 := map_zero (tangentInclusion 2 1)
  constructor
  · intro h
    have hi := congrArg (fun x : X => x.val (1 : Fin 3)) (mem_singleton_iff.mp h)
    change (π z).val (1 : Fin 3) = p.val (1 : Fin 3) at hi
    rw [chart_projection z hz, hp, monomial_apply] at hi
    simpa using hi
  · intro he
    apply mem_singleton_iff.mpr
    apply Subtype.ext
    rw [chart_projection z hz, hp]
    ext i
    by_cases hi : i = 1
    · subst i
      simpa [monomial_apply] using he
    · simp [monomial_apply, hi, he]

private theorem qF : q ∈ F := (born_iff chart_q.1).mpr
  (by change yChart.toFun q 1 = 0; rw [chart_q.2]; rfl)

private theorem exponent_one : divExp 3 A.ideal F q = 1 := by
  have h := stage_exceptional_exponent
  have hF : A.E.head! = F := by rw [stage_boundary]; rfl
  change divExpAlong 3 A.N A.ideal A.E.head! q = 1 at h
  rw [hF, stage_carrier, divExpAlong_univ] at h
  exact h

private theorem monomial_iff (g : Y → ℂ) :
    (monomialPart 3 A.ideal A.E).mem q g ↔ (vanishingIdeal (n := 3) F).mem q g := by
  have hA := isInvDomain_geoTransformAlong domain B test
  have hS : IsSNCDivisor 3 [F] := (show A.E = [F] from stage_boundary) ▸ hA.isWellFormed.isSNCDivisor
  have hC : (vanishingIdeal (n := 3) F).IsCoherent :=
    isCoherent_of_isInvertible (isInvertible_vanishingIdeal_snc_member hS (0 : Fin 1))
  rw [show A.E = [F] from stage_boundary]
  constructor
  · rintro ⟨_, h⟩
    have hm := h (0 : Fin [F].length) qF
    change (idealPow (vanishingIdeal (n := 3) F) (divExp 3 A.ideal F q)).mem q g at hm
    rw [exponent_one, idealPow_one_eq hC] at hm
    exact hm
  · intro hg
    refine ⟨hg.1, fun i _ => ?_⟩
    have hi : i = 0 := Fin.eq_zero i
    subst i
    change (idealPow (vanishingIdeal (n := 3) F) (divExp 3 A.ideal F q)).mem q g
    rwa [exponent_one, idealPow_one_eq hC]

private theorem vanishing_divides (g : Y → ℂ)
    (hg : (vanishingIdeal (n := 3) F).mem q g) :
    ∃ b : Y → ℂ, HolomorphicAt 3 b q ∧
      g =ᶠ[𝓝 q] fun z => coord 1 z * b z := by
  let G : ComplexModel 3 → ℂ := g ∘ yChart.invFun
  have ht := yChart.homeo.tendsto_symm (x := q) chart_q.1
  change Tendsto yChart.invFun (𝓝 (yChart.toFun q)) (𝓝 q) at ht
  rw [chart_q.2] at ht
  have hG : ∀ᶠ u in 𝓝 (0 : ComplexModel 3), DifferentiableAt ℂ G u := by
    filter_upwards [ht.eventually hg.1] with u hu
    exact mdifferentiableAt_iff_differentiableAt.mp
      (hu.comp u (mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel 3)) chart.property (chart_all u)))
  have hVan : ∀ᶠ u in 𝓝 (0 : ComplexModel 3), u (1 : Fin 3) = 0 → G u = 0 := by
    filter_upwards [ht.eventually hg.2] with u hu he
    apply hu
    have hs := yChart.toPartialEquiv.map_target (chart_all u)
    have hr : yChart.toFun (yChart.invFun u) = u := yChart.toPartialEquiv.right_inv (chart_all u)
    apply (born_iff hs).mpr
    change yChart.toFun (yChart.invFun u) (1 : Fin 3) = 0
    rw [hr]
    exact he
  obtain ⟨H, hH, hGH⟩ := CoordinatePlaneDivision.exists_eq_coord_mul hG (by rfl) hVan
  have hT := yChart.homeo.continuousAt chart_q.1
  change ContinuousAt yChart.toFun q at hT
  have hc := hT.tendsto
  rw [chart_q.2] at hc
  refine ⟨H ∘ yChart.toFun, ?_, ?_⟩
  · filter_upwards [hc.eventually hH, yChart.isOpen_source.mem_nhds chart_q.1] with z hz hs
    exact (hz.mdifferentiableAt).comp z (mdifferentiableAt_atlas (I := 𝓘(ℂ, ComplexModel 3)) chart.property hs)
  · filter_upwards [hc.eventually hGH, yChart.isOpen_source.mem_nhds chart_q.1] with z hz hs
    have hLeft : yChart.invFun (yChart.toFun z) = z := yChart.toPartialEquiv.left_inv hs
    change G (yChart.toFun z) = _ at hz
    simpa only [G, Function.comp_apply, hLeft] using hz

/-- The ambient residual before the last member restriction has generators
(a^2,y,c^2) at the survivor. -/
def residualGen (i : Fin 3) (z : Y) : ℂ :=
  if i = 1 then coord i z else coord i z ^ 2

private theorem residual_hol (i : Fin 3) : HolomorphicAt 3 (residualGen i) q := by
  unfold residualGen
  split
  · exact yChart.holomorphicAt_coord chart_q.1 i
  · simp only [pow_two]
    exact (yChart.holomorphicAt_coord chart_q.1 i).mul (yChart.holomorphicAt_coord chart_q.1 i)

private theorem coord_member : (monomialPart 3 A.ideal A.E).mem q (coord 1) := by
  apply (monomial_iff _).mpr
  refine ⟨yChart.holomorphicAt_coord chart_q.1 1, ?_⟩
  filter_upwards [yChart.isOpen_source.mem_nhds chart_q.1] with z hz hF
  exact (born_iff hz).mp hF

/-- The intrinsic residual on the whole carrier is exactly the indicated
three-generated germ ideal at the mark-one survivor. -/
theorem residual_span (g : Y → ℂ) :
    (nonmonomialPartAlong 3 A.N A.ideal A.E).mem q g ↔
      IsInSpanAt (n := 3) (fun b => ∃ i, b = residualGen i) q g := by
  have hA := isInvDomain_geoTransformAlong domain B test
  have hR : nonmonomialPartAlong 3 A.N A.ideal A.E =
      colon A.ideal (monomialPart 3 A.ideal A.E) := by
    rw [stage_carrier, nonmonomialPartAlong_univ_eq (by decide : 0 < 3)
      hA.isWellFormed.isSNCDivisor hA.isWellFormed.isCoherent, nonmonomialPart_eq_colon]
  rw [hR]
  constructor
  · intro hg
    have hm := (mem_colon_iff.mp hg).2 _ coord_member
    obtain ⟨_, k, s, b, hs, hb, he⟩ := (stage_span chart_q.1 _).mp hm
    choose i hi using hs
    let G : Y → ℂ := fun z => ∑ l, b l z * residualGen (i l) z
    have hG : HolomorphicAt 3 G q := HolomorphicAt.sum _ fun l _ => (hb l).mul (residual_hol (i l))
    have hCancel : ∀ᶠ z in 𝓝 q, exceptionalCoordinate z * g z = exceptionalCoordinate z * G z := by
      filter_upwards [he, yChart.isOpen_source.mem_nhds chart_q.1] with z hz hs
      change coord 1 z * g z = ∑ l, b l z * s l z at hz
      rw [exceptionalCoordinate_coord z hs, hz, show G z = ∑ l, b l z * residualGen (i l) z from rfl,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hi l]
      change b l z * (exceptionalCoordinate z * residualGen (i l) z) = _
      rw [exceptionalCoordinate_coord z hs]
      ring
    exact ⟨(mem_colon_iff.mp hg).1, k, (fun l => residualGen (i l)), b,
      (fun l => ⟨i l, rfl⟩), hb,
      eventuallyEq_of_mul_eventuallyEq yChart.isOpen_source exceptionalCoordinate_nontrivial chart_q.1
        (mem_colon_iff.mp hg).1 hG hCancel⟩
  · intro hg
    refine mem_colon_iff.mpr ⟨hg.1, fun a ha => ?_⟩
    obtain ⟨b, hb, he⟩ := vanishing_divides a ((monomial_iff a).mp ha)
    obtain ⟨hgh, k, s, c, hs, hc, hsum⟩ := hg
    choose i hi using hs
    apply (stage_span chart_q.1 _).mpr
    refine ⟨ha.1.mul hgh, k, (fun l => quotientGen (i l)), (fun l => b * c l),
      (fun l => ⟨i l, rfl⟩), (fun l => hb.mul (hc l)), ?_⟩
    filter_upwards [he, hsum, yChart.isOpen_source.mem_nhds chart_q.1] with z hz hzSum hs
    change a z * g z = ∑ l, (b z * c l z) * quotientGen (i l) z
    rw [hz, hzSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hi l]
    change _ = (b z * c l z) * (exceptionalCoordinate z * residualGen (i l) z)
    rw [exceptionalCoordinate_coord z hs]
    ring
open GeneralValue NonmonomialOrderTail CompanionRebase CompanionReductionAlong
  StepOneValue StepOneValueMasked MarkedIdealBiholomorphism InvDomainMemberRestriction
  InvDomainRebase HomogenizedIdealAlong CoefficientIdeal HironakaG1PositiveNormalNonspecialExample
  MonomialPartEtale MarkedIdealRestrictOpen HironakaG8LogClosureHistory GermIdealPullbackCalculus
  HironakaG1RecursiveBornSelectedExample DerivativeIdealAlongEtale

private abbrev W := ordMask (M := Y) A 1
private abbrev V := CMfd.of (n := 3) W
private abbrev J : MarkedIdeal 3 V := compAt record 1 B
private abbrev R : BlowupTower V V := .refl
private abbrev D : Set W := (Subtype.val : W → Y) ⁻¹' F
private abbrev O (z : W) := maskA J R z
private abbrev L (z : W) := lowerMarkedM J 1 R z
private abbrev NPart := nonmonomialPartAlong 3 A.N A.ideal A.E

private theorem open_span {M M' : CMfd.{0} 3} {I : GermIdeal 3 M}
    {φ : M' → M} (hφ : ContMDiff 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ComplexModel 3) ∞ φ)
    {x : M'} (f : Fin 3 → M → ℂ)
    (hf : ∀ i, HolomorphicAt 3 (f i) (φ x))
    (hs : ∀ g, I.mem (φ x) g ↔ IsInSpanAt (n := 3) (fun b => ∃ i, b = f i) (φ x) g)
    (g : M' → ℂ) :
    (GermIdeal.pullback (m := 3) φ I).mem x g ↔
      IsInSpanAt (n := 3) (fun b => ∃ i, b = f i ∘ φ) x g := by
  rw [GermIdeal.mem_pullback_iff]
  constructor
  · refine IsInSpanAt.trans ?_
    rintro _ ⟨a, ha, rfl⟩
    refine (isInSpanAt_comp' hφ ((hs a).mp ha)).mono ?_
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · intro h
    refine h.mono ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨f i, (hs _).mpr (isInSpanAt_self ⟨i, rfl⟩ (hf i)), rfl⟩

private theorem J_ideal :
    J.ideal = GermIdeal.pullback (m := 3) (Subtype.val : W → Y) NPart := by
  have hA := isInvDomain_geoTransformAlong domain B test
  have hH := hA.isWellFormed
  have hM := isCoherent_monomialPartAlong (by decide : 0 < 3) hH.isClosedSubmanifold_N
    hH.isSNCDivisor hH.isTransverse hH.isCoherent hA.isNonzeroAlongAt
  have hN := isCoherent_nonmonomialPartAlong (by decide : 0 < 3) hH.isClosedSubmanifold_N
    hH.isSNCDivisor hH.isTransverse hH.isCoherent hA.isNonzeroAlongAt
  let K : MarkedIdeal 3 V := MarkedIdeal.pullback (Subtype.val : W → Y) A
  have hK : K.d = 1 := rfl
  change (companionOf 3 (M := V) K 1).ideal = _
  rw [companionOf, companionAlong_ideal, hK, if_neg (by decide : ¬ 1 < 1)]
  exact (pullback_nonmonomialPartAlong (fun u => ⟨_, isLocalInverseAt_val (n := 3) W u⟩)
    hH.isCoherent hM hN).symm

private theorem L_ideal (z : W) (hJ : J.ideal.IsCoherent) :
    (L z).ideal = GermIdeal.pullback (m := 3) (Subtype.val : O z → W) J.ideal := by
  have hMark : J.d = 1 := by simp only [J, compAt, companionOf, companionAlong_d]; rfl
  have hBar : barMarked J = J := by
    change coeffMarkedAlong (homMarkedAlong J) = J
    rw [homMarkedAlong_eq_of_mark_one J hMark hJ, coeffMarkedAlong_eq_of_mark_one J hMark hJ]
  have hk : (coeffMarkedAlong (barMarked J)).ideal = J.ideal := by
    rw [hBar, coeffMarkedAlong_eq_of_mark_one J hMark hJ]
  change GermIdeal.pullback (m := 3) (Subtype.val : O z → W) (coeffMarkedAlong (barMarked J)).ideal = _
  rw [hk]

private theorem J_gens (hq : q ∈ W) (g : W → ℂ) :
    J.ideal.mem ⟨q, hq⟩ g ↔
      IsInSpanAt (n := 3) (fun b => ∃ i, b = residualGen i ∘ (Subtype.val : W → Y)) ⟨q, hq⟩ g := by
  rw [J_ideal]
  exact open_span (M := Y) (M' := V) (x := ⟨q, hq⟩) contMDiff_subtype_val residualGen residual_hol residual_span g

private theorem L_gens (hq : q ∈ W) (hz : (⟨q, hq⟩ : W) ∈ O ⟨q, hq⟩)
    (hJ : J.ideal.IsCoherent) (g : O ⟨q, hq⟩ → ℂ) :
    (L (⟨q, hq⟩ : W)).ideal.mem ⟨⟨q, hq⟩, hz⟩ g ↔
      IsInSpanAt (n := 3)
        (fun b => ∃ i, b = (fun u : O ⟨q, hq⟩ => residualGen i u.val.val)) ⟨⟨q, hq⟩, hz⟩ g := by
  rw [L_ideal _ hJ]
  exact open_span (M := V) (M' := CMfd.of (n := 3) (O ⟨q, hq⟩))
    (x := ⟨⟨q, hq⟩, hz⟩) contMDiff_subtype_val
    (fun i => residualGen i ∘ (Subtype.val : W → Y))
    (fun i => (residual_hol i).comp_contMDiff (f := (Subtype.val : W → Y))
      (y := ⟨q, hq⟩) (Eventually.of_forall fun _ => contMDiff_subtype_val.contMDiffAt))
    (J_gens hq) g

open ResolutionInvariantSpec CanonicalCentres HironakaG1InitialPositiveGeneralRead

set_option maxHeartbeats 700000 in
/-- On the real next mask the selected ideal is represented along its
carrier by the two squared chart coordinates (a^2,c^2). -/
theorem selected_born_trace_gens :
    ∃ (hq : q ∈ W) (hz : (⟨q, hq⟩ : W) ∈ O ⟨q, hq⟩),
      let z : W := ⟨q, hq⟩
      let x : O z := ⟨z, hz⟩
      let K := L z
      let T := BlowupTower.refl (X := CMfd.of (n := 3) (O z))
      let v := (invFamily (by decide : 0 < 3) 2).inv K T x
      K.E = [] ∧ K.d = 1 ∧ K.N = (Subtype.val : O z → W) ⁻¹' D ∧
      (invFamily (by decide : 0 < 3) 3).inv record B q =
        positiveSuccessorRead 1 (toLex (1, (v : WithTop (ValTy 2)))) ∧
      ∀ g : O z → ℂ,
        IsInSpanOnAt (n := 3) K.N (K.ideal.mem x) x g ↔
          IsInSpanOnAt (n := 3) K.N
            (fun b => b = (fun u => coord 0 u.val.val ^ 2) ∨
                      b = (fun u => coord 2 u.val.val ^ 2)) x g := by
  obtain ⟨hq, hz, hN, hE, hd, hRead⟩ := actual_selected_born_read
  obtain ⟨_, hJ, _, _, _⟩ := actual_positive_companion_level
  let z : W := ⟨q, hq⟩
  let x : O z := ⟨z, hz⟩
  let f (i : Fin 3) (u : O z) : ℂ := residualGen i u.val.val
  let G (b : O z → ℂ) : Prop := b = (fun u => coord 0 u.val.val ^ 2) ∨
                                 b = (fun u => coord 2 u.val.val ^ 2)
  have hf (i : Fin 3) : HolomorphicAt 3 (f i) x :=
    (residual_hol i).comp_contMDiff (f := fun u : O z => u.val.val) (y := x)
      (Eventually.of_forall fun _ => (contMDiff_subtype_val.comp contMDiff_subtype_val).contMDiffAt)
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  have he0 : f 0 = fun u => coord 0 u.val.val ^ 2 := by funext u; simp only [f, residualGen, h01, if_false]
  have he2 : f 2 = fun u => coord 2 u.val.val ^ 2 := by funext u; simp only [f, residualGen, h21, if_false]
  refine ⟨hq, hz, hE, hd, hN, hRead, fun g => ?_⟩
  change IsInSpanOnAt (n := 3) (L z).N ((L z).ideal.mem x) x g ↔ IsInSpanOnAt (n := 3) (L z).N G x g
  constructor
  · refine IsInSpanOnAt.trans ?_
    intro s hs
    have h := (L_gens hq hz hJ.isWellFormed.isCoherent s).mp hs
    refine IsInSpanOnAt.trans ?_ (IsInSpanAt.restrict h)
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact IsInSpanAt.restrict (isInSpanAt_self (Or.inl he0) (hf 0))
    · refine ⟨0, Fin.elim0, Fin.elim0, (fun i => i.elim0), (fun i => i.elim0), ?_⟩
      have ht : Continuous (fun u : O z => u.val.val) := continuous_subtype_val.comp continuous_subtype_val
      filter_upwards [ht.continuousAt.eventually (yChart.isOpen_source.mem_nhds chart_q.1)] with u hu huN
      have hF : u.val.val ∈ F := by
        change u ∈ (Subtype.val : O z → W) ⁻¹' D
        rw [← hN]
        exact huN
      change residualGen 1 u.val.val = _
      simp only [residualGen, if_true, Finset.univ_eq_empty, Finset.sum_empty]
      exact (born_iff hu).mp hF
    · exact IsInSpanAt.restrict (isInSpanAt_self (Or.inr he2) (hf 2))
  · refine IsInSpanOnAt.trans ?_
    intro s hs
    refine IsInSpanAt.restrict (isInSpanAt_self ?_ ?_)
    rcases hs with h | h
    · rw [h, ← he0]
      exact (L_gens hq hz hJ.isWellFormed.isCoherent _).mpr (isInSpanAt_self ⟨0, rfl⟩ (hf 0))
    · rw [h, ← he2]
      exact (L_gens hq hz hJ.isWellFormed.isCoherent _).mpr (isInSpanAt_self ⟨2, rfl⟩ (hf 2))
    · rcases hs with h | h
      · rw [h, ← he0]; exact hf 0
      · rw [h, ← he2]; exact hf 2

open MonomialPartEtale HironakaSharpOriginalProductTraceOrder NonmonomialOrderLocal

private def axis (w : ComplexModel 3) : ComplexModel 3 :=
  w (0 : Fin 3) • EuclideanSpace.single (0 : Fin 3) (1 : ℂ)

private theorem axis_chart (w : ComplexModel 3) :
    let u := yChart.invFun (axis w)
    u ∈ F ∧ coord 0 u = w (0 : Fin 3) := by
  intro u
  have hs := yChart.toPartialEquiv.map_target (chart_all (axis w))
  have he : yChart.toFun u = axis w := yChart.toPartialEquiv.right_inv (chart_all (axis w))
  refine ⟨(born_iff hs).mpr ?_, ?_⟩
  · change yChart.toFun u (1 : Fin 3) = 0
    rw [he]
    simp [axis]
  · change yChart.toFun u (0 : Fin 3) = _
    rw [he]
    simp [axis]

set_option maxHeartbeats 650000 in
private theorem axis_in_mask (hq : q ∈ W) (hz : (⟨q, hq⟩ : W) ∈ O ⟨q, hq⟩)
    (hN : (L (⟨q, hq⟩ : W)).N = (Subtype.val : O ⟨q, hq⟩ → W) ⁻¹' D) :
    let z : W := ⟨q, hq⟩
    ∃ θ : ComplexModel 3 → O z, θ 0 = ⟨z, hz⟩ ∧
      (∀ᶠ w : ComplexModel 3 in 𝓝 0,
        MDifferentiableAt 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ComplexModel 3) θ w) ∧
      ∀ᶠ w : ComplexModel 3 in 𝓝 0, θ w ∈ (L z).N ∧ coord 0 (θ w).val.val = w (0 : Fin 3) := by
  intro z
  let x : O z := ⟨z, hz⟩
  let f : ComplexModel 3 → Y := fun w => yChart.invFun (axis w)
  let ψ₁ := openInv W z
  let ψ₂ := openInv (O z) x
  have h₁ := isLocalInverseAt_val (n := 3) W z
  have h₂ := isLocalInverseAt_val (n := 3) (O z) x
  have hf₀ : f 0 = q := by
    change yChart.invFun (axis 0) = yChart.invFun 0
    simp [axis]
  have hfD (w : ComplexModel 3) :
      MDifferentiableAt 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ComplexModel 3) f w := by
    have hp : DifferentiableAt ℂ (fun u : ComplexModel 3 => u (0 : Fin 3)) w :=
      (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 3)).differentiableAt
    have hD : DifferentiableAt ℂ axis w := hp.smul (differentiableAt_const _)
    exact (mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel 3)) chart.property
      (chart_all (axis w))).comp w hD.mdifferentiableAt
  have hf : Tendsto f (𝓝 0) (𝓝 q) := hf₀ ▸ (hfD 0).continuousAt.tendsto
  have hT₁ : Tendsto ψ₁ (𝓝 q) (𝓝 z) := h₁.tendsto
  have hT₂ : Tendsto ψ₂ (𝓝 z) (𝓝 x) := h₂.tendsto
  let θ := ψ₂ ∘ ψ₁ ∘ f
  have hAt : θ 0 = x := by
    change ψ₂ (ψ₁ (f 0)) = x
    rw [hf₀, show ψ₁ q = z from h₁.left_inv.self_of_nhds]
    exact h₂.left_inv.self_of_nhds
  refine ⟨θ, hAt, ?_, ?_⟩
  · filter_upwards [hf.eventually h₁.mdiff_inv, (hT₁.comp hf).eventually h₂.mdiff_inv] with w hw₁ hw₂
    exact hw₂.comp w (hw₁.comp w (hfD w))
  · filter_upwards [hf.eventually h₁.right_inv, (hT₁.comp hf).eventually h₂.right_inv] with w hw₁ hw₂
    have hVal : (θ w).val.val = f w := by
      change (ψ₂ (ψ₁ (f w))).val.val = f w
      change (ψ₂ (ψ₁ (f w))).val = ψ₁ (f w) at hw₂
      rw [hw₂]
      exact hw₁
    refine ⟨?_, ?_⟩
    · rw [hN]
      change (θ w).val.val ∈ F
      rw [hVal]
      exact (axis_chart w).1
    · rw [hVal]
      exact (axis_chart w).2

open StepOneLowerDomain

set_option maxHeartbeats 1200000 in
/-- The next finite payload has first entry two on its exact literal mask. -/
theorem selected_born_payload_first :
    ∃ v : ValTy 2, (ofLex v).1 = 2 ∧
      (invFamily (by decide : 0 < 3) 3).inv record B q =
        positiveSuccessorRead 1 (toLex (1, (v : WithTop (ValTy 2)))) := by
  obtain ⟨hq, hz, hE, hd, hN, hRead, hSpan⟩ := selected_born_trace_gens
  obtain ⟨hq', hJ, _, hLevel, _⟩ := actual_positive_companion_level
  let z : W := ⟨q, hq⟩
  let Z := CMfd.of (n := 3) (O z)
  let x : O z := ⟨z, hz⟩
  let K := L z
  let T := BlowupTower.refl (X := Z)
  have hLevel : level J R z = 1 := hLevel
  have hK : IsInvDomain 2 K := isInvDomain_lowerMarked_succ J hJ.isWellFormed hJ.one_le_d
    (by decide : 0 < 3) R trivial hJ.dimLE (show level J R z = 0 + 1 from hLevel)
  have hxN : x ∈ K.N := by
    change x ∈ (L z).N
    rw [hN]
    exact qF
  let g (i : Fin 3) (w : O z) : ℂ := coord i w.val.val
  have gg (i : Fin 3) : HolomorphicAt 3 (g i) x :=
    (yChart.holomorphicAt_coord chart_q.1 i).comp_contMDiff
      (f := fun u : O z => u.val.val) (y := x)
      (Eventually.of_forall fun _ => (contMDiff_subtype_val.comp contMDiff_subtype_val).contMDiffAt)
  have hv (i : Fin 3) : VanishesToOrderOn 3 K.N x 1 (g i) :=
    (vanishesToOrderOn_one_iff hxN (gg i)).mpr (by change yChart.toFun q i = 0; rw [chart_q.2]; rfl)
  have h2 : x ∈ cosupport 3 K.N K.ideal 2 := by
    refine ⟨hxN, fun u hu => ?_⟩
    obtain ⟨k, a, b, ha, hb, hEq⟩ := (hSpan u).mp
      (IsInSpanAt.restrict (isInSpanAt_self hu
        (GermIdeal.IsCoherent.holomorphicAt_mem hK.isWellFormed.isCoherent hu)))
    have hvan (l : Fin k) : VanishesToOrderOn 3 K.N x 2 (a l) := by
      rcases ha l with he | he
      · rw [he]
        simpa only [pow_two] using (hv 0).mul (hv 0)
      · rw [he]
        simpa only [pow_two] using (hv 2).mul (hv 2)
    obtain ⟨c, hc, he⟩ := vanishesToOrderOn_sum_mul hb hvan
    refine ⟨c, hc, ?_⟩
    filter_upwards [hEq, he] with w hw hw' hwN
    exact (hw hwN).trans (hw' hwN)
  have h3 : x ∉ cosupport 3 K.N K.ideal 3 := by
    intro h
    let g0 : O z → ℂ := fun w => g 0 w ^ 2
    have hg : K.ideal.mem x g0 := by
      apply (L_gens hq hz hJ.isWellFormed.isCoherent _).mpr
      have hg0 : g0 = fun u : O z => residualGen 0 u.val.val := by
        funext u
        simp only [g0, g, residualGen, show (0 : Fin 3) ≠ 1 by decide, if_false]
      rw [hg0]
      refine isInSpanAt_self ⟨0, rfl⟩ ?_
      rw [← hg0]
      simpa only [g0, pow_two] using (gg 0).mul (gg 0)
    obtain ⟨θ, hAt, hDiff, hNear⟩ := axis_in_mask hq hz hN
    have hVan : VanishesToOrderOn 3 K.N (θ 0) 3 g0 := hAt.symm ▸ h.2 _ hg
    obtain ⟨b, hb, he⟩ := vanishesToOrderOn_comp (θ := θ) hDiff hVan
    have hEq : (fun w : ComplexModel 3 => w (0 : Fin 3) ^ 2) =ᶠ[𝓝 0] b := by
      filter_upwards [hNear, he] with w hw hw'
      have hvv : g0 (θ w) = b w := hw' hw.1
      change g 0 (θ w) ^ 2 = b w at hvv
      change coord 0 (θ w).val.val ^ 2 = b w at hvv
      rwa [hw.2] at hvv
    let Φ : LocalHolomorphicEquivAt (n := 3) (chartAt (ComplexModel 3) (0 : ComplexModel 3) 0) :=
      BlowupExistenceOriginIdeal.idEquivAt
    have hnot := MonomialCase.flatCoord_notMem_idealPow_two Φ 0 (mem_flatDomain_self Φ)
    have hh : HolomorphicAt 3 (fun w : ComplexModel 3 => w (0 : Fin 3)) 0 :=
      Eventually.of_forall fun _ => (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 3)).mdifferentiableAt
    exact pow_notMem_idealPow (o := 1) hh hnot 2 (mem_idealPow_congr hb hEq.symm)
  have hSame : K = ordinaryTraceMarked (X := Z) K.N K.ideal :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of (𝔪 := K) (𝔫 := ordinaryTraceMarked (X := Z) K.N K.ideal) rfl hE rfl hd
  have hCuts (i : ℕ) : ordGe (M := Z) K i = cosupport 3 K.N K.ideal i := by
    exact (congrArg (fun S : MarkedIdeal 3 Z => ordGe (M := Z) S i) hSame).trans
      (ordGe_ordinaryTraceMarked_eq_cosupport (X := Z) K.N K.ideal hK.isWellFormed.isCoherent i)
  have hLow : 2 ≤ nmOrd (M := Z) K x :=
    (mem_ordGe_iff hK.isWellFormed hK.isNonzeroAlongAt hxN 2).mp ((hCuts 2).symm ▸ h2)
  have hHigh : ¬ 3 ≤ nmOrd (M := Z) K x := fun h =>
    h3 ((hCuts 3) ▸ (mem_ordGe_iff hK.isWellFormed hK.isNonzeroAlongAt hxN 3).mpr h)
  let v := (invFamily (by decide : 0 < 3) 2).inv K T x
  have hV : (ofLex v).1 = nmOrd (M := Z) K x := by
    change (ofLex (genInv _ K T x)).1 = _
    rfl
  exact ⟨v, by omega, hRead⟩

end
end Hironaka.HironakaG1RecursiveBornResidualExample
