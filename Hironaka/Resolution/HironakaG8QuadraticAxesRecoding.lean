import Hironaka.Resolution.HironakaG8QuadraticInitialTieCriterion
import Hironaka.Resolution.HironakaActualCoherentWeightedCoefficientMarked

/-! Coordinate axes and the full-rank quadric have the same exact
degree-two coefficient recoding. -/
set_option autoImplicit false
open Set TopologicalSpace Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8QuadraticAxesRecoding
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaActualCoherentWeightedCoefficientMarked RelativePrincipalizationSpan
  InvertibleIdealQuotient DerivativeIdeal RestrictedIdealExtension
  IdealWeightPowers IdealOrderArithmetic OrderMultiplicativity GermIdealPullbackCalculus
  HomogenizedGlueing HomogenizedIdeal FactorizationFromResolution RestrictLeCalculus

abbrev coord (i : Fin 3) (x : ComplexModel 3) : ℂ := x.ofLp i

def axesI (i : Fin 3) : Fin 3 := ![0,0,1] i
def axesJ (i : Fin 3) : Fin 3 := ![1,2,2] i
def axesFunction (i : Fin 3) (x : ComplexModel 3) : ℂ :=
  coord (axesI i) x * coord (axesJ i) x
def quadFunction (x : ComplexModel 3) : ℂ :=
  coord 0 x * coord 1 x + coord 2 x * coord 2 x

def axesIdeal : GermIdeal 3 (ComplexModel 3) := finiteFunctionIdeal axesFunction
def quadIdeal : GermIdeal 3 (ComplexModel 3) := finiteFunctionIdeal (fun _ : Fin 1 => quadFunction)
def coordinateIdeal : GermIdeal 3 (ComplexModel 3) := finiteFunctionIdeal coord

private theorem holCoord (i : Fin 3) (x : ComplexModel 3) : HolomorphicAt 3 (coord i) x :=
  Eventually.of_forall fun _ => (EuclideanSpace.proj (𝕜 := ℂ) i).differentiableAt.mdifferentiableAt

private theorem coordCoherent : coordinateIdeal.IsCoherent :=
  isCoherent_finiteFunctionIdeal _ (fun i => (EuclideanSpace.proj (𝕜 := ℂ) i).differentiable.mdifferentiable)

private theorem axesDifferentiable (i : Fin 3) : Differentiable ℂ (axesFunction i) :=
  ((EuclideanSpace.proj (𝕜 := ℂ) (axesI i)).differentiable.mul
    (EuclideanSpace.proj (𝕜 := ℂ) (axesJ i)).differentiable)

private theorem quadDifferentiable : Differentiable ℂ quadFunction :=
  (((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 3)).differentiable.mul
    (EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 3)).differentiable).add
    ((EuclideanSpace.proj (𝕜 := ℂ) (2 : Fin 3)).differentiable.mul
      (EuclideanSpace.proj (𝕜 := ℂ) (2 : Fin 3)).differentiable))

theorem axesCoherent : axesIdeal.IsCoherent :=
  isCoherent_finiteFunctionIdeal _ (fun i => (axesDifferentiable i).mdifferentiable)

theorem quadCoherent : quadIdeal.IsCoherent :=
  isCoherent_finiteFunctionIdeal _ (fun _ => quadDifferentiable.mdifferentiable)

private theorem coord_mem (i : Fin 3) (x : ComplexModel 3) : coordinateIdeal.mem x (coord i) :=
  isInSpanAt_self ⟨i,rfl⟩ (holCoord i x)

private theorem pair_mem_sq (i j : Fin 3) (x : ComplexModel 3) :
    (idealPow coordinateIdeal 2).mem x (fun y => coord i y * coord j y) := by
  rw [idealPow_succ (p := 1), idealPow_one_of_isCoherent coordCoherent]
  exact IdealOrderArithmetic.mul_mem_mul (coord_mem i x) (coord_mem j x)
    ((holCoord i x).mul (holCoord j x))

private theorem axesLe : axesIdeal.Le (idealPow coordinateIdeal 2) := by
  intro x g hg
  apply HomogenizedIdeal.mem_of_isInSpanAt (isCoherent_idealPow coordCoherent 2)
  refine hg.mono ?_
  rintro _ ⟨i,rfl⟩
  exact pair_mem_sq (axesI i) (axesJ i) x

private theorem quadLe : quadIdeal.Le (idealPow coordinateIdeal 2) := by
  intro x g hg
  have hC := isCoherent_idealPow coordCoherent 2
  apply HomogenizedIdeal.mem_of_isInSpanAt hC
  refine hg.mono ?_
  rintro _ ⟨i,rfl⟩
  apply HomogenizedIdeal.mem_of_isInSpanAt hC
  exact IsInSpanAt.add (isInSpanAt_self (pair_mem_sq 0 1 x)
    ((holCoord 0 x).mul (holCoord 1 x))) (isInSpanAt_self (pair_mem_sq 2 2 x)
    ((holCoord 2 x).mul (holCoord 2 x)))

private abbrev e := complexChartAt (n := 3) (0 : ComplexModel 3)

private theorem chartProduct (i j k : Fin 3) (x : ComplexModel 3) :
    chartDeriv e (EuclideanSpace.single k 1) (fun y => coord i y * coord j y) x =
      coord i x * (if j = k then 1 else 0) + (if i = k then 1 else 0) * coord j x := by
  have he : e.val = OpenPartialHomeomorph.refl (ComplexModel 3) := chartAt_self_eq
  unfold chartDeriv
  rw [he]
  have h := ((EuclideanSpace.proj (𝕜 := ℂ) i).hasFDerivAt (x := x)).mul
    ((EuclideanSpace.proj (𝕜 := ℂ) j).hasFDerivAt (x := x))
  have hVal := congrArg (fun g : ComplexModel 3 →L[ℂ] ℂ => g (EuclideanSpace.single k 1)) h.fderiv
  change fderiv ℂ (fun y => coord i y * coord j y) x (EuclideanSpace.single k 1) = _ at hVal
  change fderiv ℂ (fun y => coord i y * coord j y) x (EuclideanSpace.single k 1) = _
  rw [hVal]
  simp [coord,PiLp.single_apply,mul_comm]

private theorem quadDerivative (k : Fin 3) :
    chartDeriv e (EuclideanSpace.single k 1) quadFunction =
      if k = 0 then coord 1 else if k = 1 then coord 0 else fun x => 2 * coord 2 x := by
  funext x
  have he : e.val = OpenPartialHomeomorph.refl (ComplexModel 3) := chartAt_self_eq
  have h := (((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 3)).hasFDerivAt (x := x)).mul
    ((EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 3)).hasFDerivAt (x := x))).add
    (((EuclideanSpace.proj (𝕜 := ℂ) (2 : Fin 3)).hasFDerivAt (x := x)).mul
    ((EuclideanSpace.proj (𝕜 := ℂ) (2 : Fin 3)).hasFDerivAt (x := x)))
  have hVal := congrArg (fun g : ComplexModel 3 →L[ℂ] ℂ => g (EuclideanSpace.single k 1)) h.fderiv
  unfold chartDeriv
  rw [he]
  change fderiv ℂ quadFunction x (EuclideanSpace.single k 1) = _ at hVal
  change fderiv ℂ quadFunction x (EuclideanSpace.single k 1) = _
  rw [hVal]
  fin_cases k <;> simp [coord,two_mul]

private theorem axesDerivative (i k : Fin 3) :
    chartDeriv e (EuclideanSpace.single k 1) (axesFunction i) =
      if axesI i = k then coord (axesJ i)
      else if axesJ i = k then coord (axesI i) else 0 := by
  funext x
  rw [show axesFunction i = (fun y => coord (axesI i) y * coord (axesJ i) y) from rfl,
    chartProduct]
  fin_cases i <;> fin_cases k <;> simp [axesI,axesJ]


private theorem derivative_span {m : ℕ} (s : Fin m → ComplexModel 3 → ℂ)
    (hs : ∀ i, Differentiable ℂ (s i)) (x : ComplexModel 3) (g : ComplexModel 3 → ℂ) :
    (derivIdeal (finiteFunctionIdeal (n := 3) s)).mem x g ↔
      IsInSpanAt (n := 3) (· ∈ range (derivFamily e s)) x g := by
  refine derivIdeal_mem_iff_of_generators (𝔞 := finiteFunctionIdeal s) isOpen_univ
    (fun i => (hs i).mdifferentiable.mdifferentiableOn) (fun _ _ _ => Iff.rfl) e ?_ (mem_univ x) g
  have he : e.val = OpenPartialHomeomorph.refl (ComplexModel 3) := chartAt_self_eq
  rw [he]
  exact subset_rfl

private theorem coordSq_le : (idealPow coordinateIdeal 2).Le coordinateIdeal := by
  rw [idealPow_succ (p := 1),idealPow_one_of_isCoherent coordCoherent]
  exact mul_le_left coordCoherent (fun hg => GermIdeal.IsCoherent.holomorphicAt_mem coordCoherent hg)

private theorem coord_mul_mem (x : ComplexModel 3) (i : Fin 3) (c : ℂ) :
    coordinateIdeal.mem x (fun z => c * coord i z) :=
  isInSpanAt_mul_gen ⟨i,rfl⟩ (holomorphicAt_const c) (holCoord i x)

private theorem coord_zero_mem (x : ComplexModel 3) :
    coordinateIdeal.mem x 0 := by
  convert coord_mul_mem x 0 0 using 1
  funext z
  simp

private theorem finite_derivative_eq_coordinate {m : ℕ} (s : Fin m → ComplexModel 3 → ℂ)
    (hs : ∀ i, Differentiable ℂ (s i))
    (hL : (finiteFunctionIdeal s).Le (idealPow coordinateIdeal 2))
    (hDiff : ∀ i k x, coordinateIdeal.mem x (chartDeriv e (EuclideanSpace.single k 1) (s i)))
    (hSpan : ∀ i x, IsInSpanAt (n := 3) (· ∈ range (derivFamily e s)) x (coord i)) :
    derivIdeal (finiteFunctionIdeal (n := 3) s) = coordinateIdeal := by
  apply GermIdeal.ext
  funext x g
  apply propext
  rw [derivative_span s hs]
  constructor
  · intro hg
    apply HomogenizedIdeal.mem_of_isInSpanAt coordCoherent
    refine hg.mono ?_
    rintro f ⟨a,rfl⟩
    cases a with
    | inl i =>
      exact coordSq_le x _ (hL x _ (isInSpanAt_self ⟨i,rfl⟩
        (Eventually.of_forall fun y => (hs i y).mdifferentiableAt)))
    | inr ij => exact hDiff ij.1 ij.2 x
  · intro hg
    apply IsInSpanAt.trans _ hg
    rintro f ⟨i,rfl⟩
    exact hSpan i x

/-- Both exact first derivative ideals equal the full coordinate ideal. -/
theorem axes_derivative_ideal : derivIdeal axesIdeal = coordinateIdeal := by
  apply finite_derivative_eq_coordinate axesFunction axesDifferentiable axesLe
  · intro i k x
    rw [axesDerivative]
    split
    · exact coord_mem _ _
    split
    · exact coord_mem _ _
    · exact coord_zero_mem _
  · intro i x
    fin_cases i
    · apply isInSpanAt_self _ (holCoord 0 x)
      exact ⟨Sum.inr (0,1),by rw [derivFamily,axesDerivative]; rfl⟩
    · apply isInSpanAt_self _ (holCoord 1 x)
      exact ⟨Sum.inr (0,0),by rw [derivFamily,axesDerivative]; rfl⟩
    · apply isInSpanAt_self _ (holCoord 2 x)
      exact ⟨Sum.inr (1,0),by rw [derivFamily,axesDerivative]; rfl⟩

theorem quad_derivative_ideal : derivIdeal quadIdeal = coordinateIdeal := by
  apply finite_derivative_eq_coordinate (fun _ : Fin 1 => quadFunction) (fun _ => quadDifferentiable) quadLe
  · intro i k x
    rw [quadDerivative]
    split
    · exact coord_mem _ _
    split
    · exact coord_mem _ _
    · exact coord_mul_mem _ _ _
  · intro i x
    fin_cases i
    · apply isInSpanAt_self _ (holCoord 0 x)
      exact ⟨Sum.inr (0,1),by rw [derivFamily,quadDerivative]; rfl⟩
    · apply isInSpanAt_self _ (holCoord 1 x)
      exact ⟨Sum.inr (0,0),by rw [derivFamily,quadDerivative]; rfl⟩
    · have hm : (fun z => (2 : ℂ) * coord 2 z) ∈
          range (derivFamily e (fun _ : Fin 1 => quadFunction)) :=
        ⟨Sum.inr (0,2),by rw [derivFamily,quadDerivative]; rfl⟩
      refine isInSpanAt_of_eq_mul hm (holCoord 2 x) (holomorphicAt_const (1/2 : ℂ)) ?_
      exact Eventually.of_forall fun z => by
        change coord 2 z = (1/2 : ℂ) * (2 * coord 2 z)
        ring

private theorem absorb {I : GermIdeal 3 (ComplexModel 3)}
    (hI : I.Le (idealPow coordinateIdeal 2)) : sumIdeal I (idealPow coordinateIdeal 2) =
      idealPow coordinateIdeal 2 := by
  have hC := isCoherent_idealPow coordCoherent 2
  apply GermIdeal.ext
  funext x f
  apply propext
  constructor
  · intro hf
    apply HomogenizedIdeal.mem_of_isInSpanAt hC
    exact (mem_sumIdeal_iff.mp hf).mono (fun g hg => hg.elim (hI x g) id)
  · exact le_sumIdeal_right hC x f

/-- Despite different degree-two generator counts, the entire quadratic
coefficient records agree. -/
theorem axes_quad_quadratic_recoding_eq :
    sumIdeal axesIdeal (idealPow (derivIdeal axesIdeal) 2) =
      sumIdeal quadIdeal (idealPow (derivIdeal quadIdeal) 2) := by
  rw [axes_derivative_ideal,quad_derivative_ideal,absorb axesLe,absorb quadLe]


open BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec CanonicalCentres
  HironakaG8QuadraticInitialTieCriterion AnalyticIrreducibleComponents NormalCrossings
  NonmonomialOrderLocal HironakaSharpOriginalProductTraceOrder GermIdealOrder OrderTaylor

abbrev model := CMfd.of (n := 3) (ComplexModel 3)

private theorem polynomial_domain {I : GermIdeal 3 (ComplexModel 3)} (hI : I.IsCoherent)
    (f : ComplexModel 3 → ℂ) (hf : ∀ z,I.mem z f)
    (hAnal : AnalyticOnNhd ℂ f univ) {b : ComplexModel 3} (hb : f b ≠ 0) :
    IsInvDomain 3 (fullRecord (X := model) I 2) := by
  have hN := HomogenizedGlueingTower.isClosedSubmanifold_univ (n := 3) (M := ComplexModel 3)
  refine ⟨⟨hN,hI,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hN⟩,
    fun z _ => ⟨3,le_rfl,regularAtDim_univ z⟩,(show 1 ≤ 2 by decide),?_⟩
  intro z _
  refine ⟨f,hf z,?_⟩
  apply Frequently.mono (p := fun y => f y ≠ 0) _ (fun y hy => ⟨mem_univ y,hy⟩)
  by_contra hn
  have he : f =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := by
    change ∀ᶠ y in 𝓝 z, f y = 0
    simpa using hn
  exact hb (congrFun (hAnal.eq_of_eventuallyEq analyticOnNhd_const he) b)

private theorem invariant_order_two {I : GermIdeal 3 (ComplexModel 3)}
    (hI : IsInvDomain 3 (fullRecord (X := model) I 2))
    (hD : derivIdeal I = coordinateIdeal) :
    (0 : ComplexModel 3) ∈ (fullRecord (X := model) I 2).cosupp ∧
      nmOrd (fullRecord (X := model) I 1) 0 = 2 := by
  have hHol : ∀ x g,I.mem x g → HolomorphicAt 3 g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hI.isWellFormed.isCoherent hg
  have hC : (0 : ComplexModel 3) ∈ cosupport 3 univ coordinateIdeal 1 := by
    unfold coordinateIdeal
    rw [mem_cosupport_finiteFunctionIdeal_iff _ _ _ (fun _ => holCoord _ _)]
    intro i
    exact (vanishesToOrderOn_one_iff (mem_univ _) (holCoord i _)).mpr rfl
  have hC2 : (0 : ComplexModel 3) ∉ cosupport 3 univ coordinateIdeal 2 := by
    intro h
    have hDer : chartDeriv e (EuclideanSpace.single (0 : Fin 3) 1) (coord 0) = 1 := by
      funext z
      have he : e.val = OpenPartialHomeomorph.refl (ComplexModel 3) := chartAt_self_eq
      unfold chartDeriv
      rw [he]
      change fderiv ℂ (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 3)) z
        (EuclideanSpace.single (0 : Fin 3) 1) = 1
      rw [(EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 3)).hasFDerivAt.fderiv]
      simp
    have hM := chartDeriv_mem_derivIdeal (𝔞 := coordinateIdeal)
      (v := EuclideanSpace.single (0 : Fin 3) (1 : ℂ))
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem coordCoherent hg)
      (show (0 : ComplexModel 3) ∈ e.val.source by simp [e,complexChartAt,chartAt_self_eq])
      (coord_mem 0 0)
    rw [hDer] at hM
    rw [show 2 = 1+1 by decide,cosupport_succ_eq_cosupport_derivIdeal
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem coordCoherent hg) (μ := 1) le_rfl] at h
    exact one_ne_zero ((vanishesToOrderOn_one_iff (mem_univ _) (holomorphicAt_const 1)).mp (h.2 _ hM))
  have h2 : (0 : ComplexModel 3) ∈ cosupport 3 univ I 2 := by
    rw [show 2 = 1+1 by decide,cosupport_succ_eq_cosupport_derivIdeal hHol le_rfl,hD]
    exact hC
  have h3 : (0 : ComplexModel 3) ∉ cosupport 3 univ I 3 := by
    change (0 : ComplexModel 3) ∉ cosupport 3 univ I (2+1)
    rw [cosupport_succ_eq_cosupport_derivIdeal hHol (by decide : 1 ≤ 2),hD]
    exact hC2
  have hOrder (q : ℕ) : 0 ∈ cosupport 3 univ I q ↔ q ≤ nmOrd (fullRecord (X := model) I 1) 0 :=
    ordinaryTraceOrder_cosupport_iff (X := model) hI.isWellFormed.isClosedSubmanifold_N
      hI.isWellFormed.isCoherent hI.isNonzeroAlongAt (mem_univ 0) q
  have hHi : ¬ 3 ≤ nmOrd (fullRecord (X := model) I 1) 0 := fun hn => h3 ((hOrder 3).mpr hn)
  exact ⟨h2, Nat.le_antisymm (by omega) ((hOrder 2).mp h2)⟩

private theorem axis_actual_domain : IsInvDomain 3 (fullRecord (X := model) axesIdeal 2) := by
  let b : ComplexModel 3 := EuclideanSpace.single (0 : Fin 3) (1 : ℂ) + EuclideanSpace.single (1 : Fin 3) 1
  refine polynomial_domain axesCoherent (axesFunction 0)
    (fun z => isInSpanAt_self ⟨0,rfl⟩ (Eventually.of_forall fun y =>
      (axesDifferentiable 0 y).mdifferentiableAt)) (b := b) ?_ ?_
  · intro z _
    exact ((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 3)).analyticAt z).mul
      ((EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 3)).analyticAt z)
  · change coord 0 b * coord 1 b ≠ 0
    simp [b,coord]

private theorem quad_actual_domain : IsInvDomain 3 (fullRecord (X := model) quadIdeal 2) := by
  let b : ComplexModel 3 := EuclideanSpace.single (2 : Fin 3) (1 : ℂ)
  refine polynomial_domain quadCoherent quadFunction
    (fun z => isInSpanAt_self ⟨0,rfl⟩ (Eventually.of_forall fun y =>
      (quadDifferentiable y).mdifferentiableAt)) (b := b) ?_ ?_
  · intro z _
    exact (((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 3)).analyticAt z).mul
      ((EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 3)).analyticAt z)).add
      (((EuclideanSpace.proj (𝕜 := ℂ) (2 : Fin 3)).analyticAt z).mul
        ((EuclideanSpace.proj (𝕜 := ℂ) (2 : Fin 3)).analyticAt z))
  · simp [quadFunction,b,coord]

/-- The two explicit coherent ambient records have exactly the same
whole original mark-one initial value at the origin. -/
theorem axes_quad_original_mark_one_initial_value_eq :
    (canonicalInvariant 3).inv (fullRecord (X := model) axesIdeal 1) .refl 0 =
      (canonicalInvariant 3).inv (fullRecord (X := model) quadIdeal 1) .refl 0 := by
  obtain ⟨ha,haOrd⟩ := invariant_order_two axis_actual_domain axes_derivative_ideal
  obtain ⟨hq,hqOrd⟩ := invariant_order_two quad_actual_domain quad_derivative_ideal
  exact mark_one_initial_value_eq_of_quadratic_recoding (X := model) axesIdeal quadIdeal
    axis_actual_domain quad_actual_domain 0 ha hq haOrd hqOrd axes_quad_quadratic_recoding_eq

end
end Hironaka.HironakaG8QuadraticAxesRecoding
