import Hironaka.Resolution.HironakaActualCentreWeightedControlledStalk
import Hironaka.Resolution.HironakaActualSelectedFlatteningHSComparison

/-! The actual exceptional denominator in ANY already given native square,
in the original selected indices. No target ideal identity is an input. -/
set_option autoImplicit false
open Set Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualNativeExceptionalControlledStalk
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  InvertibleIdealQuotient RelativePrincipalizationSpan BlowupFlatCoordinates
  HironakaSmoothSubmersionGermIdealColon HironakaActualSingularChartTransport
  HironakaActualAnalyticBlowupTaylor HironakaActualCoherentWeightedCoefficientMarked
  HironakaActualWeightedCoefficientCompression FiniteGermIdealPullbackGenerators
  ManifoldFiniteSpanChartTransport EuclideanHolomorphicGermSpan
  BlowupExceptionalDivisor BlowupControlledTransform IdealWeightPowers BlowupTowers
  HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetChartInvariance
  HironakaSharpOriginalMemberProduct
  HironakaSharpActualControlledRelativeSaturation MemberPullback
  HironakaActualHistoricalMovingCentreChart

variable {n : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

private theorem adaptedIdeal_eq_span_of_generation
    {r : ℕ} (J : GermIdeal n Y) (hJ : J.IsCoherent) (y : Y)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) y y))
    (h0 : Θ.toFun (chartAt (ComplexModel n) y y)=0)
    (G : Fin r → Y → ℂ) (hG : ∀i,HolomorphicAt n (G i) y)
    (hgen : ∀F,J.mem y F ↔ IsInSpanAt (n:=n) (·∈range G) y F) :
    adaptedIdeal J y Θ h0=Ideal.span (range fun i=>adaptedGerm y Θ h0 (G i) (hG i)) := by
  ext g
  obtain ⟨F,hF,rfl⟩:=exists_original_adapted_representative y Θ h0 g
  rw [mem_adaptedIdeal_iff J hJ y Θ h0 F hF,hgen F]
  exact (isInSpanAt_comp_adapted_iff y Θ h0 G F).trans
    (isInSpanAt_iff_holGerm_mem_span _
      (fun i=>(holomorphic_adapted_iff y Θ h0 (G i)).mpr (hG i))
      ((holomorphic_adapted_iff y Θ h0 F).mpr hF))

private theorem idealPow_principal_mem_iff
    {A : GermIdeal n Y} {y : Y} {a : Y → ℂ} (ha : HolomorphicAt n a y)
    (hA : ∀g,A.mem y g ↔ IsInSpanAt (n:=n) (·=a) y g) :
    ∀q g,(idealPow A q).mem y g ↔ IsInSpanAt (n:=n) (·=a^q) y g := by
  intro q
  induction q with
  | zero => exact unit_mem_iff_principal
  | succ q ih =>
    exact mul_mem_iff_principal (BlowupDerivativeIdeal.holomorphicAt_pow ha q) ha ih hA

/-- The whole actual exceptional denominator is derived internally from the
given source flattening and target square, retaining that SAME target chart. -/
theorem actual_native_exceptional_power_stalk
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π) (y : Y)
    (A : Set (Fin n)) (e : Fin n) (he : e∈A) (b : Fin n → ℂ)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) (π y) (π y)))
    (hFlat : ∀{x : X},x∈(chartAt (ComplexModel n) (π y)).source →
      chartAt (ComplexModel n) (π y) x∈Φ.source →
      (x∈C ↔ Φ.toFun (chartAt (ComplexModel n) (π y) x)∈coordinateSubsetPlane A))
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) y y))
    (hΘsrc : Θ.source⊆(chartAt (ComplexModel n) y).target)
    (hΘ0 : Θ.toFun (chartAt (ComplexModel n) y y)=0)
    (hSquare : ∀z : Y,z∈(chartAt (ComplexModel n) y).source →
      chartAt (ComplexModel n) y z∈Θ.source → π z∈flatDomain Φ ∧
      Φ.toFun (chartAt (ComplexModel n) (π y) (π z))=
        actualAnalyticBlowupMap A e b (Θ.toFun (chartAt (ComplexModel n) y z)))
    (q : ℕ) :
    adaptedIdeal (idealPow (exceptionalDivisor hπ).ideal q) y Θ hΘ0=
      Ideal.span {(coordinateGerm e)^q} := by
  have hflat : ∀{z : Y},z∈(chartAt (ComplexModel n) y).source →
      chartAt (ComplexModel n) y z∈Θ.source →
      (z∈π ⁻¹' C ↔ Θ.toFun (chartAt (ComplexModel n) y z) e=0) := by
    intro z hz hzΘ
    obtain ⟨hDomain,hNormal⟩:=hSquare z hz hzΘ
    have hC:=hFlat hDomain.1 hDomain.2
    constructor
    · intro hzC
      have hp : Φ.toFun (chartAt (ComplexModel n) (π y) (π z)) e=0:=
        (hC.mp hzC) e he
      have hev:=congrArg (fun v : ComplexModel n=>v e) hNormal
      simpa [hp,actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate,he] using hev.symm
    · intro hz0
      apply hC.mpr
      intro i hi
      rw [hNormal,actualAnalyticBlowupMap_apply]
      simp [actualAnalyticBlowupCoordinate,hi,hz0]
  have hE : (exceptionalDivisor hπ).ideal=vanishingIdeal (n:=n) (π ⁻¹' C) := by
    rw [exceptionalDivisor_ideal]
    exact actual_pullback_centre_ideal_eq_exceptional_vanishing
      (X:=CMfd.of (n:=n) X) (Y:=CMfd.of (n:=n) Y) hπ
  let a:=flatCoord Θ e
  have ha : HolomorphicAt n a y:=holomorphicAt_flatCoord Θ e (mem_flatDomain_self Θ)
  have hgen : ∀g,(exceptionalDivisor hπ).ideal.mem y g ↔ IsInSpanAt (n:=n) (·=a) y g := by
    rw [hE]
    exact vanishingIdeal_mem_iff_flatCoord Θ hflat (mem_flatDomain_self Θ)
  have hpow:=idealPow_principal_mem_iff ha hgen q
  have hag : adaptedGerm y Θ hΘ0 (a^q) (BlowupDerivativeIdeal.holomorphicAt_pow ha q)=
      (coordinateGerm e)^q := by
    change HolGerm.mk _ _=(coordinateGerm e)^q
    change HolGerm.mk _ _=(HolGerm.mk (fun u : ComplexModel n=>u e)
      (HolomorphicGermReducednessBridge.eventually_differentiableAt_coordinate e))^q
    rw [←HolGerm.mk_pow]
    apply HolGerm.mk_eq_mk_iff.mpr
    have htar : (0 : ComplexModel n)∈Θ.target:=by
      simpa only [hΘ0] using Θ.mapsTo_toFun Θ.center_mem_source
    filter_upwards [Θ.isOpen_target.mem_nhds htar] with u hu
    have hm:=(flatInverse_mem Θ hu hΘsrc).2
    exact congrArg (fun v : ComplexModel n=>v e^q) hm
  have heq:=adaptedIdeal_eq_span_of_generation _
    (GermIdealPullbackCalculus.isCoherent_idealPow
      (DivisorMetric.isCoherent_of_isInvertible (exceptionalDivisor hπ).isInvertible) q)
    y Θ hΘ0 (fun _ : Fin 1=>a^q) (fun _=>BlowupDerivativeIdeal.holomorphicAt_pow ha q)
    (fun g=>(hpow g).trans (isInSpanAt_range_one_iff (a^q) g).symm)
  rw [heq]
  simp only [hag,range_const]

/-- Every SAME actual analytic quotient family gives the entire weighted
controlled colon, by genuine pivot cancellation, before any target HS law. -/
theorem actual_same_normalized_quotients_weighted_colon
    {ι : Type*} [Fintype ι] (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (w : ι → ℕ) (F N : ι → HolGerm (ComplexModel n))
    (hProduct : ∀i,(coordinateGerm e)^w i*N i=actualAnalyticBlowupPullback A e b (F i)) :
    (Ideal.map (actualAnalyticBlowupPullback A e b).toRingHom
      (weightedCompression w F)).colon {(coordinateGerm e)^weightedCommonMark w}=
        weightedCompression w N := by
  have hmul (x : HolGerm (ComplexModel n)) (g : ι → HolGerm (ComplexModel n)) :
      Ideal.span {x}*Ideal.span (range g)=Ideal.span (range (fun i=>x*g i)) := by
    rw [Ideal.span_mul_span']
    congr 1
    ext z
    simp only [Set.mem_mul,Set.mem_singleton_iff,Set.mem_range]
    constructor
    · rintro ⟨a,rfl,c,⟨i,rfl⟩,rfl⟩
      exact ⟨i,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨x,rfl,g i,⟨i,rfl⟩,rfl⟩
  have hmap : Ideal.map (actualAnalyticBlowupPullback A e b).toRingHom
      (weightedCompression w F)=Ideal.span {(coordinateGerm e)^weightedCommonMark w}*
        weightedCompression w N := by
    rw [weightedCompression,Ideal.map_span,weightedCompression,hmul]
    congr 1
    rw [←range_comp]
    congr 1
    funext i
    change actualAnalyticBlowupPullback A e b (F i^(weightedCommonMark w/w i))=_
    rw [map_pow,←hProduct i,mul_pow,←pow_mul,weight_mul_compressionExponent]
  rw [hmap]
  ext g
  rw [Submodule.mem_colon_singleton]
  change g*(coordinateGerm e)^weightedCommonMark w∈
    Ideal.span {(coordinateGerm e)^weightedCommonMark w}*weightedCompression w N ↔ _
  rw [Ideal.mem_span_singleton_mul]
  constructor
  · rintro ⟨h,hh,heq⟩
    have hEq : h=g:=mul_left_cancel₀
      (pow_ne_zero _ (HolomorphicGermReducednessBridge.coordinate_germ_ne_zero e))
      (heq.trans (mul_comm g ((coordinateGerm e)^weightedCommonMark w)))
    simpa only [hEq] using hh
  · intro hg
    exact ⟨g,hg,mul_comm ((coordinateGerm e)^weightedCommonMark w) g⟩

end
end Hironaka.HironakaActualNativeExceptionalControlledStalk
