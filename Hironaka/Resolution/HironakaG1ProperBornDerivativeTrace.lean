import Hironaka.Resolution.HironakaG1RecursiveBornOrderTwoBarExample
import Hironaka.Resolution.HironakaG1ProperBornStrictPlane
import Hironaka.Resolution.HironakaActualWeightedNormalAmbientDerivatives

/-! The whole initial derivative trace on the actual proper tangent of the mark-two example. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1ProperBornDerivativeTrace
open Hironaka.HolomorphicIdealSheaves RelativePrincipalizationSpan
  InvertibleIdealQuotient HironakaActualWeightedNormalPadding
  HironakaActualWeightedNormalAmbientDerivatives HironakaActualOpenZeroSectionDifferentials
  HironakaActualRelativeNormalGeometry HironakaActualCoherentWeightedCoefficientMarked
  HironakaG1ProperBornStrictPlane HironakaActualZeroCoordinateContactSeed
  HironakaActualGraphFunctionalIdeal HironakaActualCentreJointJets HironakaRelativeNormalIdeal
  DerivativeIdeal DerivativeIdealAlong IdealOrderArithmetic

noncomputable section

private abbrev U : Opens (ComplexModel 2) := ⊤
private abbrev X := productOpen U

def baseGen (i : Fin 2) (x : U) : ℂ := x.val i ^ (if i = 1 then 4 else 3)

private theorem baseGen_mdifferentiable (i : Fin 2) :
    MDifferentiable 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ℂ) (baseGen i) := by
  have h : ContMDiff 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ℂ) ∞
      (fun w : U => w.val i) :=
    (EuclideanSpace.proj i : ComplexModel 2 →L[ℂ] ℂ).contMDiff.comp contMDiff_subtype_val
  exact fun z => (h.contMDiffAt (x := z)).mdifferentiableAt (by simp) |>.pow _

def baseIdeal : GermIdeal 2 U := finiteFunctionIdeal baseGen

theorem baseIdeal_coherent : baseIdeal.IsCoherent :=
  isCoherent_finiteFunctionIdeal baseGen baseGen_mdifferentiable

private theorem normal_formula (x : X) : relativeNormalCoordinate U x = x.val (2 : Fin 3) := by
  simp [relativeNormalCoordinate,addedCoordinate,graphFunction,zeroFunction]

private theorem old_gen (i : Fin 2) :
    baseGen i ∘ projection U = sourceGen (i.castAdd 1) := by
  have h (x : X) : (projection U x).val i = x.val (i.castAdd 1) := rfl
  funext x
  fin_cases i
  all_goals
    rw [Function.comp_apply]
    unfold baseGen sourceGen
    rw [h]
    rfl

private theorem normal_gen :
    (fun x : X => relativeNormalCoordinate U x ^ 2) = sourceGen 2 := by
  funext x
  simp [normal_formula,sourceGen,show (2 : Fin 3) ≠ 1 by decide]

private theorem oldHol (i : Fin 2) (x : X) :
    HolomorphicAt 3 (baseGen i ∘ projection U) x :=
  Eventually.of_forall ((baseGen_mdifferentiable i).comp ((projection_contMDiff U).mdifferentiable (by simp)))

private theorem normalHol (x : X) :
    HolomorphicAt 3 (fun x => relativeNormalCoordinate U x ^ 2) x :=
  Eventually.of_forall ((normalCoordinate_mdifferentiable U).pow 2)

/-- The original ideal is literally the normal-square padding of the two horizontal powers. -/
theorem record_eq_padding : record.ideal = normalPaddingIdeal baseIdeal 2 := by
  unfold normalPaddingIdeal baseIdeal
  rw [finiteFunctionIdeal_pullback _ baseGen_mdifferentiable _ (projection_contMDiff U)]
  apply GermIdeal.ext
  funext x g
  apply propext
  constructor
  · intro hg
    apply mem_sumIdeal_iff.mpr
    apply IsInSpanAt.mono _ hg
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · exact Or.inl (isInSpanAt_self ⟨0,old_gen 0 |>.symm⟩ (old_gen 0 ▸ oldHol 0 x))
    · exact Or.inl (isInSpanAt_self ⟨1,old_gen 1 |>.symm⟩ (old_gen 1 ▸ oldHol 1 x))
    · exact Or.inr (isInSpanAt_self ⟨(),normal_gen⟩ (normal_gen ▸ normalHol x))
  · intro hg
    refine IsInSpanAt.trans ?_ (mem_sumIdeal_iff.mp hg)
    intro u hu
    rcases hu with h | h
    · refine h.mono ?_
      rintro _ ⟨i,rfl⟩
      exact ⟨i.castAdd 1,(old_gen i).symm⟩
    · refine h.mono ?_
      rintro _ ⟨i,rfl⟩
      exact ⟨2,normal_gen.symm⟩

/-- The source entire derivative traces in degrees zero and one are the
actual lower-dimensional ideals of the horizontal generators. -/
theorem source_ambient_derivative_trace {j : ℕ} (hj : j < 2) :
    GermIdeal.pullback (m := 2) (zeroSection U) (iterDerivIdeal record.ideal j) =
      iterDerivIdeal baseIdeal j := by
  rw [record_eq_padding]
  exact entire_ambient_derivative_trace baseIdeal_coherent hj

open Hironaka.BlowupSequences BlowupTowers BlowupStrictSubmanifold
  HironakaG1LaterPositiveNormalExample HironakaActualNativeSectionInitialBar
  GermIdealOrder IdealWeightPowers GermIdealPullbackCalculus BlowupControlledTransform
  HomogenizedIdealAlong HironakaG8HomStable CoefficientIdealRestriction MarkedIdeals MarkedIdeals.MarkedIdeal
  DivisorExponentAlong OrderTaylor HadamardBridge HironakaG8GapNormalizedExponent
  HironakaActualCoefficientDivisorExponentGap

private abbrev o : U := ⟨0,mem_univ _⟩
private abbrev p : X := zeroSection U o
private abbrev C : Set X := {p}

private theorem ambient_coord_hol (i : Fin 3) (x : X) :
    HolomorphicAt 3 (fun w : X => w.val i) x := by
  have h : ContMDiff 𝓘(ℂ, ComplexModel 3) 𝓘(ℂ, ℂ) ∞
      (fun w : X => w.val i) :=
    (EuclideanSpace.proj i : ComplexModel 3 →L[ℂ] ℂ).contMDiff.comp contMDiff_subtype_val
  exact Eventually.of_forall fun w => (h.contMDiffAt (x := w)).mdifferentiableAt (by simp)

private theorem raw_coherent : record.ideal.IsCoherent :=
  isCoherent_finiteFunctionIdeal _ fun i x =>
    ((ambient_coord_hol i x).self_of_nhds).pow _

private theorem centre_mem_order_two : p ∈ cosupport 3 (univ : Set X) record.ideal 2 := by
  refine ⟨mem_univ _,fun g hg => IsInSpanAt.vanishesToOrderOn hg ?_⟩
  rintro _ ⟨j,rfl⟩
  have hv : VanishesToOrderOn 3 (univ : Set X) p 1 (fun w : X => w.val j) :=
    (vanishesToOrderOn_one_iff (mem_univ p) (ambient_coord_hol j p)).mpr (by simp [p, zeroSection])
  have h2 := hv.mul hv
  have h3 := h2.mul hv
  have h4 := h3.mul hv
  unfold sourceGen
  by_cases hj : j = 1
  · simpa [hj,pow_succ] using h4.mono (by decide : 2 ≤ (1 + 1) + 1 + 1)
  · by_cases hk : j = 2
    · simpa [hj,hk,pow_succ] using h2
    · simpa [hj,hk,pow_succ] using h3.mono (by decide : 2 ≤ (1 + 1) + 1)

private theorem le_centre_pow {I : GermIdeal 3 X} (hI : I.IsCoherent) (m : ℕ)
    (hp : p ∈ cosupport 3 (univ : Set X) I m) :
    I.Le (idealPow (vanishingIdeal (n := 3) C) m) := by
  intro x g hg
  by_cases hx : x = p
  · subst x
    exact mem_idealPow_of_vanishesToOrderOn_univ (hp.2 _ hg)
  · apply mem_idealPow_of_one_mem (I := vanishingIdeal (n := 3) C) _
      (GermIdeal.IsCoherent.holomorphicAt_mem hI hg)
    refine ⟨holomorphicAt_const 1, ?_⟩
    have hx' : x ∉ C := hx
    filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hx'] with z hZ hz
    exact (hZ hz).elim

private theorem plane_eq_zeroPlane : plane = zeroPlane U := by
  ext z
  change z.val (2 : Fin 3) = 0 ↔ (projection U z ∈ univ ∧ actualJointNormalProjection 2 1 z.val = 0)
  simp only [mem_univ,true_and]
  constructor
  · intro h
    ext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rw [actualJointNormalProjection_apply]
    exact h
  · intro h
    have he := congrArg (fun w : ComplexModel 1 => w 0) h
    change actualJointNormalProjection 2 1 z.val 0 = 0 at he
    rw [actualJointNormalProjection_apply] at he
    exact he

private theorem plane_closed : IsClosed plane :=
  isClosed_singleton.preimage
    ((EuclideanSpace.proj (2 : Fin 3) : ComplexModel 3 →L[ℂ] ℂ).continuous.comp continuous_subtype_val)

private theorem centre_subset_plane : C ⊆ plane := by
  rintro z rfl
  change p.val (2 : Fin 3) = 0
  simp [p,zeroSection]

theorem strictPlane_closedSubmanifold : IsClosedSubmanifold 3 strictPlane :=
  isClosedSubmanifold_geoStrictTransform hπ plane_closed
    (by rw [plane_eq_zeroPlane]; exact zeroPlane_regular U) centre_subset_plane

/-- The true ordered born boundary and proper carrier at the mark-two stage. -/
def supportedStage : MarkedIdeal 3 Y :=
  ⟨strictPlane, [π ⁻¹' C], controlledTransform hπ record.ideal 2, 2⟩

theorem supportedStage_coherent : supportedStage.ideal.IsCoherent :=
  isCoherent_controlledTransform hπ raw_coherent (le_centre_pow raw_coherent 2 centre_mem_order_two)

/-- Genuine coefficient refresh on the proper strict carrier preserves the
ordered born member and the surviving mark-two point, while its exponent is zero. -/
theorem proper_refreshed_born_zero :
    let R := coeffMarkedAlong supportedStage
    R.E = [π ⁻¹' C] ∧ q ∈ R.cosupp ∧ divExpAlong 3 strictPlane R.ideal (π ⁻¹' C) q = 0 := by
  intro R
  have hCos : R.cosupp = supportedStage.cosupp := cosupp_coeffMarkedAlong
    strictPlane_closedSubmanifold.2
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem supportedStage_coherent hg)
    (by decide)
  have hGap : HasCosupportGap R := by
    intro x _ hx
    change x ∈ cosupport 3 strictPlane (coeffMarkedAlong supportedStage).ideal
      (coeffMarkedAlong supportedStage).d
    rw [← coefficient_restriction_cosupport_gap supportedStage strictPlane_closedSubmanifold
      supportedStage_coherent (by decide) strictPlane (fun _ h => h)]
    exact hx
  have hR := isCoherent_coeffMarkedAlong supportedStage_coherent strictPlane_closedSubmanifold
  refine ⟨rfl,hCos.symm ▸ strictPlane_survivor,?_⟩
  by_contra h
  have hDiv := (isDivNearAlong_divExpAlong
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hR hg) q).mono
      (Nat.pos_of_ne_zero h)
  obtain ⟨z,⟨hp,hz,hn⟩,hd⟩ := (frequently_strictPlane_born_order_one.and_eventually hDiv).exists
  apply hn
  change z ∈ supportedStage.cosupp
  rw [← hCos]
  exact hGap z hz.1 (hd hz.1 (mem_singleton_iff.mpr hp))

open BlowupDerivativeIdeal BlowupStrictIdeal HironakaSmoothSubmersionCoefficientIdeals
  DerivativeIdealAlongCoherent CompanionReduction VanishingIdealCoherent
  BlowupExceptionalDivisor TangentDirectionAlong MarkedIdealOperationsTransform
  RestrictedIdealExtension HironakaG8CoeffClass DivisorExponent

private abbrev J := derivIdealAlong (univ : Set X) record.ideal
private abbrev A := vanishingIdeal (n := 3) C
private abbrev P := vanishingIdeal (n := 3) plane

private theorem plane_regular : ∀ z ∈ plane, RegularAtDim (n := 3) plane z 2 := by
  rw [plane_eq_zeroPlane]
  exact zeroPlane_regular U

private theorem P_coherent : P.IsCoherent :=
  isCoherent_vanishingIdeal ⟨plane_closed,fun z hz => ⟨2,plane_regular z hz⟩⟩

private theorem A_coherent : A.IsCoherent := isCoherent_vanishingIdeal_centre hπ

private theorem J_eq : J = derivIdeal record.ideal :=
  derivIdealAlong_univ (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem raw_coherent hg)

private theorem J_coherent : J.IsCoherent := J_eq ▸ isCoherent_derivIdeal raw_coherent

private theorem J_centre : J.Le (idealPow A 1) :=
  le_centre_pow J_coherent 1
    (cosupport_add_subset_cosupport_iterDerivIdealAlong
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem raw_coherent hg) 1 1 centre_mem_order_two)

private theorem base_at_three : o ∈ cosupport 2 (univ : Set U) baseIdeal 3 := by
  refine ⟨mem_univ _,fun g hg => IsInSpanAt.vanishesToOrderOn hg ?_⟩
  rintro _ ⟨j,rfl⟩
  have h : ContMDiff 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ℂ) ∞
      (fun w : U => w.val j) :=
    (EuclideanSpace.proj j : ComplexModel 2 →L[ℂ] ℂ).contMDiff.comp contMDiff_subtype_val
  have hh : HolomorphicAt 2 (fun w : U => w.val j) o :=
    Eventually.of_forall fun w => (h.contMDiffAt (x := w)).mdifferentiableAt (by simp)
  have hv : VanishesToOrderOn 2 (univ : Set U) o 1 (fun w : U => w.val j) :=
    (vanishesToOrderOn_one_iff (mem_univ o) hh).mpr rfl
  have h3 := (hv.mul hv).mul hv
  have h4 := h3.mul hv
  unfold baseGen
  split
  · simpa [pow_succ] using h4.mono (by decide : 3 ≤ (1 + 1) + 1 + 1)
  · simpa [pow_succ] using h3

private theorem base_deriv_at_two : o ∈ cosupport 2 (univ : Set U) (derivIdeal baseIdeal) 2 := by
  have h := cosupport_add_subset_cosupport_iterDerivIdealAlong
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem baseIdeal_coherent hg) 2 1 base_at_three
  simpa only [iterDerivIdealAlong,derivIdealAlong_univ
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem baseIdeal_coherent hg)] using h

private theorem projection_p : projection U p = o := by
  apply Subtype.ext
  exact tangentProjection_tangentInclusion 2 1 o.val

private theorem section_projection_on_plane (z : X) (hz : z ∈ plane) :
    zeroSection U (projection U z) = z := by
  apply Subtype.ext
  change tangentInclusion 2 1 (tangentProjection 2 1 z.val) = z.val
  have hn : actualJointNormalProjection 2 1 z.val = 0 := ((Set.ext_iff.mp plane_eq_zeroPlane z).mp hz).2
  simpa only [HironakaActualIntrinsicStableAmbientIso.join,hn,map_zero,add_zero] using
    (HironakaActualIntrinsicStableAmbientIso.join_projections (n := 2) (m := 1) z.val)

private theorem J_pullback : GermIdeal.pullback (m := 2) (zeroSection U) J = derivIdeal baseIdeal :=
  J_eq.symm ▸ source_ambient_derivative_trace (by decide : 1 < 2)


private theorem J_le_upper : J.Le (sumIdeal (idealPow A 2) P) := by
  intro x g hg
  have hgH := GermIdeal.IsCoherent.holomorphicAt_mem J_coherent hg
  by_cases hx : x = p
  · subst x
    let f : U → ℂ := g ∘ zeroSection U
    let a : X → ℂ := f ∘ projection U
    let b : X → ℂ := g - a
    have hf : (derivIdeal baseIdeal).mem o f := by
      rw [← J_pullback]
      exact GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨g,hg,rfl⟩
        (hgH.comp_contMDiff (Eventually.of_forall fun _ => (zeroSection_contMDiff U).contMDiffAt)))
    have hfp := mem_idealPow_of_vanishesToOrderOn_univ (base_deriv_at_two.2 _ hf)
    let B := vanishingIdeal (n := 2) ({o} : Set U)
    have hBreg : RegularAtDim (n := 2) ({o} : Set U) o 0 := by
      have he : (Subtype.val : U → ComplexModel 2) ⁻¹' ({0} : Set (ComplexModel 2)) = {o} := by
        ext x
        exact ⟨fun hx => mem_singleton_iff.mpr (Subtype.ext (mem_singleton_iff.mp hx)),
          fun hx => congrArg Subtype.val (mem_singleton_iff.mp hx)⟩
      rw [← he]
      exact (AnalyticSubsetOpens.regularAtDim_preimage_val_iff (U := U)).mpr
        BlowupExistenceOriginIdeal.regularAtDim_zero
    have hBcoh : B.IsCoherent := VanishingIdealCoherent.isCoherent_vanishingIdeal
      ⟨isClosed_singleton,fun x hx => by rw [mem_singleton_iff.mp hx]; exact ⟨0,hBreg⟩⟩
    have H := GermIdeal.mem_pullback_iff.mpr
      (isInSpanAt_self (S := fun k : X → ℂ => ∃ t, (idealPow B 2).mem (projection U p) t ∧
        k = t ∘ projection U) (x := p)
        ⟨f,projection_p.symm ▸ hfp,rfl⟩
        ((GermIdealOrder.holomorphicAt_of_mem_idealPow (projection_p.symm ▸ hfp)).comp_contMDiff
          (Eventually.of_forall fun _ => (projection_contMDiff U).contMDiffAt)))
    have hB : (GermIdeal.pullback (m := 3) (projection U) B).Le A := by
      intro y k hk
      refine ⟨(GermIdeal.mem_pullback_iff.mp hk).1,?_⟩
      by_cases hy : y = p
      · subst y
        have hk0 : k p = 0 := by
          obtain ⟨_,n,s,c,hs,_,he⟩ := GermIdeal.mem_pullback_iff.mp hk
          rw [he.self_of_nhds]
          refine Finset.sum_eq_zero fun i _ => ?_
          obtain ⟨u,hu,heq⟩ := hs i
          rw [heq]
          have hu0 := hu.2.self_of_nhds (mem_singleton_iff.mpr projection_p)
          change u (projection U p) = 0 at hu0
          simp [Function.comp_apply,hu0]
        exact Eventually.of_forall fun z hz => (mem_singleton_iff.mp hz).symm ▸ hk0
      · have hy' : y ∉ C := hy
        filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hy'] with z hZ hz
        exact (hZ hz).elim
    have ha : (idealPow A 2).mem p a := by
      rw [pullback_idealPow (projection_contMDiff U) hBcoh] at H
      exact idealPow_le_idealPow hB 2 p a H
    have haH := GermIdealOrder.holomorphicAt_of_mem_idealPow ha
    have hbH : HolomorphicAt 3 b p := by
      filter_upwards [hgH,haH] with z hgZ haZ
      exact hgZ.sub haZ
    have hb : P.mem p b := ⟨hbH,Eventually.of_forall fun z hz => by
      simp [b,a,f,Function.comp_apply,section_projection_on_plane z hz]⟩
    apply mem_sumIdeal_iff.mpr
    let S : (X → ℂ) → Prop := fun k => (idealPow A 2).mem p k ∨ P.mem p k
    have hm : IsInSpanAt (n := 3) S p (a + b) :=
      IsInSpanAt.add (isInSpanAt_self (S := S) (Or.inl ha) haH)
        (isInSpanAt_self (S := S) (Or.inr hb) hbH)
    apply DerivativeIdeal.isInSpanAt_congr hm
    exact Eventually.of_forall fun z => by simp [b,Pi.add_apply,Pi.sub_apply]
  · have hu : A.mem x (fun _ => 1) := by
      refine ⟨holomorphicAt_const 1,?_⟩
      have hx' : x ∉ C := hx
      filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hx'] with z hZ hz
      exact (hZ hz).elim
    exact le_sumIdeal_left' (fun _ _ h => GermIdealOrder.holomorphicAt_of_mem_idealPow h)
      x g (mem_idealPow_of_one_mem hu hgH 2)


open BlowupFunctionTransform BlowupFlatCoordinates

private theorem A_two_le_one : (idealPow A 2).Le (idealPow A 1) :=
  idealPow_le_of_le (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem A_coherent hg) (by decide)

private theorem P_le_centre : P.Le (idealPow A 1) := by
  intro z g hg
  have hs : A.mem z g := ⟨hg.1,hg.2.mono fun _ h hC => h (centre_subset_plane hC)⟩
  exact BlowupDerivativeIdeal.mem_idealPow_one_of_mem (fun _ _ m => m.1) hs

private theorem upper_derivative_order_one {z : Y} (hz : z ∈ yChart.source)
    (hs : z ∈ strictPlane) (hF : π z ∈ C) :
    z ∈ cosupport 3 strictPlane (controlledTransform hπ (idealPow A 2) 1) 1 := by
  let hEq := HironakaG1LaterPositiveSelectedExample.equation_on_chart
  refine ⟨hs,fun g hg => ?_⟩
  apply IsInSpanAt.vanishesToOrderOn
    ((mem_controlledTransform_iff hEq hz (isCoherent_idealPow A_coherent 2) A_two_le_one g).mp hg)
  rintro v ⟨hv,u,hu,hvEq⟩
  obtain ⟨w,hw,hwEq⟩ := exists_eq_pow_mul hEq hz hu
  have h' : (fun a => exceptionalCoordinate a ^ 1 * v a) =ᶠ[𝓝 z]
      (fun a => exceptionalCoordinate a ^ 1 * (exceptionalCoordinate a * w a)) := by
    filter_upwards [hvEq,hwEq] with a h1 h2
    rw [← h1,h2]
    ring
  have hHz : HolomorphicAt 3 exceptionalCoordinate z := hEq.holomorphicAt hz
  have hSame := eventuallyEq_of_pow_mul hEq hz (μ := 1) hv (hHz.mul hw) h'
  have hEx0 : exceptionalCoordinate z = 0 := by
    rw [exceptionalCoordinate_coord z hz]
    have hp : π z = p := mem_singleton_iff.mp hF
    have he := congrArg (fun x : X => x.val (1 : Fin 3)) hp
    rw [chart_projection z hz,BlowupMonomialCharts.monomial_apply] at he
    simpa [p,zeroSection] using he
  apply (vanishesToOrderOn_one_iff hs hv).mpr
  rw [hSame.self_of_nhds]
  change exceptionalCoordinate z * w z = 0
  rw [hEx0,zero_mul]

/-- The entire controlled source derivative has order at least one on the
actual born trace of the true proper carrier. -/
theorem controlled_source_derivative_on_born {z : Y} (hz : z ∈ yChart.source)
    (hs : z ∈ strictPlane) (hF : π z ∈ C) :
    z ∈ cosupport 3 strictPlane (controlledTransform hπ J 1) 1 := by
  have hLe := controlledTransform_le_controlledTransform hπ J_le_upper (by decide : 1 ≤ 1)
  rw [controlledTransform_sumIdeal hπ (isCoherent_idealPow A_coherent 2) P_coherent
    A_two_le_one P_le_centre,
    controlledTransform_vanishingIdeal hπ ⟨plane_closed,fun z hz => ⟨2,plane_regular z hz⟩⟩
      centre_subset_plane] at hLe
  refine ⟨hs,fun g hg => ?_⟩
  apply IsInSpanAt.vanishesToOrderOn (mem_sumIdeal_iff.mp (hLe z g hg))
  rintro s (h | h)
  · exact (upper_derivative_order_one hz hs hF).2 _ h
  · have h' : (vanishingIdeal (n := 3) strictPlane).mem z s := h
    exact (vanishesToOrderOn_one_iff hs h'.1).mpr (h'.2.self_of_nhds hs)


open HironakaG1RecursiveBornOrderTwoBarExample NormalCrossings SimultaneousNormalCrossings
  HomogenizedGlueingTower

private theorem raw_wellFormed : record.IsWellFormed :=
  ⟨isClosedSubmanifold_univ,raw_coherent,isSNCDivisor_nil,isTransverse_univ_of_isSNCDivisor isSNCDivisor_nil⟩

private abbrev sourceCoefficient := coeffMarkedAlong record

/-- The actual entire source coefficient after the actual geometric point
blowup, read on the strict transform of its tangent plane. -/
def inheritedStage : MarkedIdeal 3 Y :=
  withN (sourceCoefficient.geoTransform C π) strictPlane

theorem inheritedStage_ideal :
    inheritedStage.ideal =
      sumIdeal supportedStage.ideal (idealPow (controlledTransform hπ J 1) 2) := by
  obtain ⟨hd,hI⟩ := coefficient_mark_two record raw_wellFormed rfl
  change (sourceCoefficient.geoTransform C π).ideal = _
  rw [geoTransform_ideal_eq_controlledTransform (𝔪 := sourceCoefficient) rfl
    (isCoherent_coeffMarkedAlong raw_coherent isClosedSubmanifold_univ) hπ,hd,hI]
  have hSum := controlledTransform_sumIdeal_idealPow hπ raw_coherent J_coherent
    (le_centre_pow raw_coherent 2 centre_mem_order_two) J_centre
  have hRaw : idealPow (controlledTransform hπ record.ideal 2) 1 =
      controlledTransform hπ record.ideal 2 :=
    HironakaG8CoeffClass.idealPow_one_eq supportedStage_coherent
  rw [HironakaG8CoeffClass.idealPow_one_eq raw_coherent,hRaw] at hSum
  exact hSum

private abbrev born : Set Y := π ⁻¹' C

/-- Exact proper-carrier coefficient comparison. Both records retain the
same ordered born boundary and marked point. Inherited control has born
exponent one, while genuine proper coefficient refresh has exponent zero. -/
theorem proper_inherited_vs_refreshed :
    let R := coeffMarkedAlong supportedStage
    inheritedStage.E = R.E ∧ R.E = [born] ∧
      q ∈ inheritedStage.cosupp ∧ q ∈ R.cosupp ∧
      divExpAlong 3 strictPlane inheritedStage.ideal born q = 1 ∧
      divExpAlong 3 strictPlane R.ideal born q = 0 := by
  intro R
  obtain ⟨hRE,hRq,hR0⟩ := proper_refreshed_born_zero
  have hMark : inheritedStage.d = 2 := (coefficient_mark_two record raw_wellFormed rfl).1
  have hBoth {z : Y} (hz : z ∈ yChart.source) (hs : z ∈ strictPlane) (hb : z ∈ born)
      {k : ℕ} (hk : k ≤ 2) :
      z ∈ cosupport 3 strictPlane inheritedStage.ideal k ↔
        z ∈ cosupport 3 strictPlane supportedStage.ideal k := by
    rw [inheritedStage_ideal,cosupport_sumIdeal
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem supportedStage_coherent hg)
      (fun _ _ hg => GermIdealOrder.holomorphicAt_of_mem_idealPow hg)]
    exact and_iff_left (cosupport_anti hk (cosupport_subset_cosupport_idealPow
      (N := strictPlane) (𝔞 := controlledTransform hπ J 1) 1 2
      (controlled_source_derivative_on_born hz hs hb)))
  have hNear : IsDivNearAlong 3 strictPlane inheritedStage.ideal born 1 q := by
    have hRaw := isDivNearAlong_divExpAlong (H := born)
      (N := strictPlane) (𝔞 := supportedStage.ideal)
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem supportedStage_coherent hg) q
    change IsDivNearAlong 3 strictPlane (controlledTransform hπ record.ideal 2) born
      (divExpAlong 3 strictPlane (controlledTransform hπ record.ideal 2) born q) q at hRaw
    rw [strictPlane_born_exponent] at hRaw
    filter_upwards [hRaw,yChart.isOpen_source.mem_nhds chart_q.1] with z hRawZ hz hs hb
    exact (hBoth hz hs hb (by decide)).mpr (hRawZ hs hb)
  have hNot : ¬ IsDivNearAlong 3 strictPlane inheritedStage.ideal born 2 q := by
    intro hd
    obtain ⟨z,⟨hp,hz,hn⟩,h⟩ := (frequently_strictPlane_born_order_one.and_eventually hd).exists
    have hb : z ∈ born := mem_singleton_iff.mpr hp
    apply hn
    have hI := h hz.1 hb
    rw [inheritedStage_ideal,cosupport_sumIdeal
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem supportedStage_coherent hg)
      (fun _ _ hg => GermIdealOrder.holomorphicAt_of_mem_idealPow hg)] at hI
    exact hI.1
  have hqBorn : q ∈ born := by
    change π q ∈ C
    have hp : π q = p := by
      apply Subtype.ext
      rw [chart_projection q chart_q.1,chart_q.2]
      ext i
      simp [BlowupMonomialCharts.monomial_apply,p,zeroSection]
    exact mem_singleton_iff.mpr hp
  have hExp : divExpAlong 3 strictPlane inheritedStage.ideal born q = 1 := by
    classical
    have hex : ∃ e, ¬ IsDivNearAlong 3 strictPlane inheritedStage.ideal born (e + 1) q := ⟨1,hNot⟩
    rw [divExpAlong,dif_pos hex]
    exact le_antisymm (Nat.find_min' hex hNot) (by
      by_contra! h
      have he : Nat.find hex = 0 := by omega
      exact Nat.find_spec hex (by simpa [he] using hNear))
  refine ⟨rfl,hRE,?_,hRq,hExp,hR0⟩
  change q ∈ cosupport 3 strictPlane inheritedStage.ideal inheritedStage.d
  rw [hMark]
  exact (hBoth chart_q.1 strictPlane_survivor.1 hqBorn (by decide)).mpr strictPlane_survivor


open ContactCanonicalAlong HironakaG8DomainExponents HironakaOneDimensionalCanonicalSuperlevels
  MarkedIdealOperationsAlong.MarkedIdeal HadamardBridgeAlong

private theorem plane_closedSubmanifold : IsClosedSubmanifold 3 plane :=
  ⟨plane_closed,fun z hz => ⟨2,plane_regular z hz⟩⟩

private theorem raw_admissible : record.IsAdmissibleCentre C :=
  ⟨hπ.1,fun _z hz => (mem_singleton_iff.mp hz).symm ▸ centre_mem_order_two,
    hasNormalCrossings_singleton p isSNCDivisor_nil⟩


private theorem supported_admissible (M : MarkedIdeal 3 (CMfd.of (n := 3) X))
    (hN : M.N = univ) (h : M.IsAdmissibleCentre C) :
    (withN M plane).IsAdmissibleCentre C := by
  refine ⟨h.1,fun _z hz => ⟨centre_subset_plane hz,fun g hg => ?_⟩,h.2.2⟩
  exact ((h.2.1 hz).2 g hg).mono_set (by rw [hN]; exact subset_univ _)

private theorem supportedStage_eq :
    supportedStage = withN (record.geoTransform C π) strictPlane := by
  have hI := geoTransform_ideal_eq_controlledTransform (𝔪 := record) rfl raw_coherent hπ
  exact congrArg (fun I => (⟨strictPlane,[born],I,2⟩ : MarkedIdeal 3 Y)) hI.symm

private abbrev properRaw := (withN record plane).geoTransform C π
private abbrev properInherited := (withN sourceCoefficient plane).geoTransform C π

private theorem properRaw_restrictEquiv : RestrictEquiv properRaw supportedStage := by
  rw [supportedStage_eq]
  exact geoTransform_withN_restrictEquiv rfl raw_coherent plane_closedSubmanifold hπ
    raw_admissible (supported_admissible record rfl raw_admissible)

private theorem properInherited_restrictEquiv : RestrictEquiv properInherited inheritedStage := by
  have hc := isCoherent_coeffMarkedAlong raw_coherent raw_wellFormed.isClosedSubmanifold_N
  have hCos : sourceCoefficient.cosupp = record.cosupp := cosupp_coeffMarkedAlong
    raw_wellFormed.isClosedSubmanifold_N.2
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem raw_coherent hg) (by decide)
  have hAdm : sourceCoefficient.IsAdmissibleCentre C :=
    ⟨raw_admissible.1,hCos.symm ▸ raw_admissible.2.1,raw_admissible.2.2⟩
  exact geoTransform_withN_restrictEquiv rfl hc plane_closedSubmanifold hπ hAdm
    (supported_admissible sourceCoefficient rfl hAdm)

/-- The mismatch also holds for the literal proper-record transforms,
with restriction to the tangent performed before the geometric blowup. -/
theorem proper_chronological_inherited_vs_refreshed :
    let R := coeffMarkedAlong properRaw
    properInherited.E = R.E ∧ R.E = [born] ∧
      q ∈ properInherited.cosupp ∧ q ∈ R.cosupp ∧
      divExpAlong 3 properInherited.N properInherited.ideal born q = 1 ∧
      divExpAlong 3 R.N R.ideal born q = 0 := by
  intro R
  have hCoh := isCoherent_geoTransform_ideal_of_isAdmissibleCentre
    (𝔪 := withN record plane) plane_closedSubmanifold raw_coherent
    (supported_admissible record rfl raw_admissible) hπ
  have hR := restrictEquiv_coeffMarkedAlong properRaw_restrictEquiv
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hCoh hg)
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem supportedStage_coherent hg)
  obtain ⟨hE,hRE,hi,hr,he,h0⟩ := proper_inherited_vs_refreshed
  exact ⟨properInherited_restrictEquiv.E_eq.trans (hE.trans hR.E_eq.symm),
    hR.E_eq.trans hRE,properInherited_restrictEquiv.cosupp_eq.symm ▸ hi,
    hR.cosupp_eq.symm ▸ hr,
    (divExpAlong_eq_of_restrictEquiv properInherited_restrictEquiv born q).trans he,
    (divExpAlong_eq_of_restrictEquiv hR born q).trans h0⟩


#print axioms proper_chronological_inherited_vs_refreshed
#print axioms proper_inherited_vs_refreshed
#print axioms inheritedStage_ideal
#print axioms controlled_source_derivative_on_born
#print axioms J_le_upper
#print axioms proper_refreshed_born_zero
#print axioms strictPlane_closedSubmanifold
#print axioms record_eq_padding
#print axioms source_ambient_derivative_trace

end
end Hironaka.HironakaG1ProperBornDerivativeTrace
