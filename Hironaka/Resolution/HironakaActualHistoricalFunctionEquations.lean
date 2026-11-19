import Hironaka.Resolution.HironakaActualNativeAdaptedPullbackSquare
import Hironaka.Resolution.HironakaActualNativeSourceChartComposition
import Hironaka.Resolution.HironakaActualOffCentreGivenCoordinates
import Hironaka.Resolution.HironakaActualAnalyticDirectionRemovalQuotient
import Hironaka.Resolution.HironakaActualFormalMonomialBlowupReflection

/-! Exact SAME original whole-function equations through the actual source,
blowup and off-centre identity squares. A single common NONZERO denominator
is transported; no later family, function or numerator is reselected. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualHistoricalFunctionEquations
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaActualAnalyticBlowupTaylor HironakaActualFormalMonomialBlowupReflection
  HironakaActualAnalyticDirectionRemovalQuotient HironakaActualNativeAdaptedPullbackSquare
  HironakaActualNativeSourceChartComposition HironakaActualOffCentreGivenCoordinates
  HironakaSmoothSubmersionGermIdealColon HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicJetMonomialSpan BlowupFlatCoordinates
  HironakaActualAnalyticFormalNormalPowers HironakaActualCoefficientPresentationCentrePower

variable {n : ℕ}

/-- The WHOLE actual analytic chart is injective, including every actual
direction; literal source shears reduce it to genuine coefficient reflection. -/
theorem actual_analytic_blowup_pullback_injective
    (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    Function.Injective (actualAnalyticBlowupPullback A e b) := by
  have hz : Function.Injective (actualAnalyticBlowupPullback A e (fun _=>0)) := by
    intro F G h
    apply actualUnshiftedTaylorAlgHom_injective n
    apply actualFormalBlowup_zero_injective A e
    have hF:=DFunLike.congr_fun (actualTaylor_analyticBlowupPullback A e (fun _=>0)) F
    have hG:=DFunLike.congr_fun (actualTaylor_analyticBlowupPullback A e (fun _=>0)) G
    exact hF.symm.trans ((congrArg (actualUnshiftedTaylorAlgHom n) h).trans hG)
  intro F G h
  apply (actualAnalyticDirectionShearGermEquiv A e b).injective
  apply hz
  rw [←actualAnalyticBlowupPullback_direction_shear,←actualAnalyticBlowupPullback_direction_shear]
  exact h

variable {X Y : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {V : Type}

/-- The exact common original-function equations follow the GIVEN real
source chart and its actual inverse-coordinate action, without a new family. -/
theorem actual_function_equations_compose_source_chart
    (x : X) (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel n) x).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) x x)=0)
    (D : LocalHolomorphicEquivAt (n:=n) (0 : ComplexModel n)) (hD0 : D.toFun 0=0)
    (μ : V → ℕ) (F : V → X → ℂ) (hF : ∀v,HolomorphicAt n (F v) x)
    (Γ : V → HolGerm (ComplexModel n)) (d : HolGerm (ComplexModel n)) (hd : d≠0)
    (hEq : ∀v,adaptedGerm x Φ hΦ0 (F v) (hF v)=d^(μ v)*Γ v) :
    let E:=(localGermAlgEquiv D hD0).symm
    E d≠0 ∧ ∀v,adaptedGerm x (RegularAtDimTransport.LocalHolomorphicEquivAt.comp Φ D hΦ0)
      (actual_native_source_chart_comp_geometry x Φ hΦsrc hΦ0 D hD0).2 (F v) (hF v)=
        (E d)^(μ v)*E (Γ v) := by
  let E:=(localGermAlgEquiv D hD0).symm
  refine ⟨?_,?_⟩
  · intro hz
    apply hd
    apply E.injective
    simpa only [map_zero] using hz
  · intro v
    rw [actual_native_source_chart_comp_germ x Φ hΦsrc hΦ0 D hD0 (F v) (hF v),hEq v,map_mul,map_pow]

/-- The SAME actual quotient equations transport the exact original
function history with ONE nonzero common new denominator sigma(d)*t. -/
theorem actual_function_equations_blowup_square
    (π : Y → X) (hπ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π)
    (y : Y) (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) (π y) (π y)))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel n) (π y)).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) (π y) (π y))=0)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) y y))
    (hΘsrc : Θ.source⊆(chartAt (ComplexModel n) y).target)
    (hΘ0 : Θ.toFun (chartAt (ComplexModel n) y y)=0)
    (hSquare : ∀z : Y,z∈(chartAt (ComplexModel n) y).source →
      chartAt (ComplexModel n) y z∈Θ.source → π z∈flatDomain Φ ∧
      Φ.toFun (chartAt (ComplexModel n) (π y) (π z))=
        actualAnalyticBlowupMap A e b (Θ.toFun (chartAt (ComplexModel n) y z)))
    (μ : V → ℕ) (F : V → X → ℂ) (hF : ∀v,HolomorphicAt n (F v) (π y))
    (Γ N : V → HolGerm (ComplexModel n)) (d : HolGerm (ComplexModel n)) (hd : d≠0)
    (hEq : ∀v,adaptedGerm (π y) Φ hΦ0 (F v) (hF v)=d^(μ v)*Γ v)
    (hProduct : ∀v,(coordinateGerm e)^(μ v)*N v=actualAnalyticBlowupPullback A e b (Γ v)) :
    let d':=actualAnalyticBlowupPullback A e b d*coordinateGerm e
    d'≠0 ∧ ∀v,adaptedGerm y Θ hΘ0 (F v∘π)
      ((hF v).comp_contMDiff (Eventually.of_forall fun _=>hπ.contMDiffAt))=d'^(μ v)*N v := by
  have hσd : actualAnalyticBlowupPullback A e b d≠0 := by
    intro hz
    apply hd
    apply actual_analytic_blowup_pullback_injective A e b
    simpa only [map_zero] using hz
  refine ⟨mul_ne_zero hσd (HolomorphicGermReducednessBridge.coordinate_germ_ne_zero e),?_⟩
  intro v
  rw [adaptedGerm_native_pullback_square π hπ y A e b Φ hΦsrc hΦ0 Θ hΘsrc hΘ0 hSquare
    (F v) (hF v),hEq v,map_mul,map_pow,←hProduct v,mul_pow,mul_assoc]

/-- The actual off-centre identity square preserves the SAME original
functions/common denominator/family in their entire adapted germ equations. -/
theorem actual_function_equations_identity_square
    (π : Y → X) (hπ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π)
    (y : Y) (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) (π y) (π y)))
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) (π y) (π y))=0)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) y y))
    (hΘsrc : Θ.source⊆(chartAt (ComplexModel n) y).target)
    (hΘ0 : Θ.toFun (chartAt (ComplexModel n) y y)=0)
    (hSquare : ∀z : Y,z∈(chartAt (ComplexModel n) y).source →
      chartAt (ComplexModel n) y z∈Θ.source → π z∈flatDomain Φ ∧
      Φ.toFun (chartAt (ComplexModel n) (π y) (π z))=Θ.toFun (chartAt (ComplexModel n) y z))
    (μ : V → ℕ) (F : V → X → ℂ) (hF : ∀v,HolomorphicAt n (F v) (π y))
    (Γ : V → HolGerm (ComplexModel n)) (d : HolGerm (ComplexModel n))
    (hEq : ∀v,adaptedGerm (π y) Φ hΦ0 (F v) (hF v)=d^(μ v)*Γ v) :
    ∀v,adaptedGerm y Θ hΘ0 (F v∘π)
      ((hF v).comp_contMDiff (Eventually.of_forall fun _=>hπ.contMDiffAt))=d^(μ v)*Γ v := by
  intro v
  exact (actual_native_identity_square_adapted_germ π hπ y Φ hΦ0 Θ hΘsrc hΘ0 hSquare (F v) (hF v)).trans (hEq v)

end
end Hironaka.HironakaActualHistoricalFunctionEquations
