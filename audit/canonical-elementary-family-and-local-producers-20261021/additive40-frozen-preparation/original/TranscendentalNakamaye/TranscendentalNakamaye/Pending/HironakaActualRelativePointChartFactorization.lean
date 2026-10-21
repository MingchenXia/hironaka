import TranscendentalNakamaye.Pending.HironakaActualAnalyticBlowupTaylor

/-!
# Literal analytic relative-to-point chart and SAME normalized family

The genuine point chart factors through the actual relative chart and the
actual zero tangent-scaling chart. Whole original pullbacks and ENTIRE ideal
images agree. Every prescribed relative quotient becomes the point quotient
with the SAME numerator, and actual domain cancellation gives uniqueness.
Blueprint: `hironaka-actual-relative-point-chart-factorization-extension.tex`.
-/

set_option autoImplicit false
open Set Filter Classical
namespace TranscendentalNakamaye.Pending.HironakaActualRelativePointChartFactorization
noncomputable section
open FirstPass HolGerm HironakaActualAnalyticBlowupTaylor
 HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetChartInvariance
variable {n : ℕ}

def actualPointChartDirection (A : Set (Fin n)) (b : Fin n → ℂ) : Fin n → ℂ :=
  fun i => if i∈A then b i else 0

def actualTangentScalingVariables (A : Set (Fin n)) (e : Fin n) : Set (Fin n) :=
  Aᶜ∪{e}

theorem actualAnalyticBlowupMap_relative_point (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (z : ComplexModel n) :
    actualAnalyticBlowupMap A e b
      (actualAnalyticBlowupMap (actualTangentScalingVariables A e) e (fun _ => 0) z)=
      actualAnalyticBlowupMap univ e (actualPointChartDirection A b) z := by
  ext i
  by_cases hi : i=e
  · subst i
    simp [actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate]
  · by_cases hAi : i∈A <;>
      simp [actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate,
        actualTangentScalingVariables,actualPointChartDirection,hi,hAi]

theorem actualAnalyticBlowupPullback_relative_point (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    (actualAnalyticBlowupPullback (actualTangentScalingVariables A e) e (fun _ => 0)).comp
      (actualAnalyticBlowupPullback A e b)=
      actualAnalyticBlowupPullback univ e (actualPointChartDirection A b) := by
  apply AlgHom.ext
  intro g
  induction g using HolGerm.induction_on with
  | h f hf =>
    change actualAnalyticBlowupPullback (actualTangentScalingVariables A e) e (fun _ => 0)
      (actualAnalyticBlowupPullback A e b (HolGerm.mk f hf))=_
    simp only [actualAnalyticBlowupPullback,compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => congrArg f (actualAnalyticBlowupMap_relative_point A e b z)

theorem map_actual_relative_point_ideal (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (I : Ideal (HolGerm (ComplexModel n))) :
    Ideal.map (actualAnalyticBlowupPullback (actualTangentScalingVariables A e) e (fun _ => 0)).toRingHom
      (Ideal.map (actualAnalyticBlowupPullback A e b).toRingHom I)=
    Ideal.map (actualAnalyticBlowupPullback univ e (actualPointChartDirection A b)).toRingHom I := by
  have hc (g : HolGerm (ComplexModel n)) :
      actualAnalyticBlowupPullback (actualTangentScalingVariables A e) e (fun _ => 0)
        (actualAnalyticBlowupPullback A e b g)=
      actualAnalyticBlowupPullback univ e (actualPointChartDirection A b) g :=
    AlgHom.congr_fun (actualAnalyticBlowupPullback_relative_point A e b) g
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.map_le_iff_le_comap.mpr
    intro g hg
    change actualAnalyticBlowupPullback (actualTangentScalingVariables A e) e (fun _ => 0)
      (actualAnalyticBlowupPullback A e b g)∈
        Ideal.map (actualAnalyticBlowupPullback univ e (actualPointChartDirection A b)).toRingHom I
    rw [hc]
    exact Ideal.mem_map_of_mem _ hg
  · apply Ideal.map_le_iff_le_comap.mpr
    intro g hg
    change actualAnalyticBlowupPullback univ e (actualPointChartDirection A b) g∈
      Ideal.map (actualAnalyticBlowupPullback (actualTangentScalingVariables A e) e (fun _ => 0)).toRingHom
        (Ideal.map (actualAnalyticBlowupPullback A e b).toRingHom I)
    rw [←hc]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hg)

theorem actual_relative_quotient_point_equation (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (w : ℕ) (G H : HolGerm (ComplexModel n))
    (hH : (coordinateGerm e)^w*H=actualAnalyticBlowupPullback A e b G) :
    (coordinateGerm e)^w*
      actualAnalyticBlowupPullback (actualTangentScalingVariables A e) e (fun _ => 0) H=
      actualAnalyticBlowupPullback univ e (actualPointChartDirection A b) G := by
  have hh := congrArg (actualAnalyticBlowupPullback (actualTangentScalingVariables A e) e (fun _ => 0)) hH
  have hcomp := AlgHom.congr_fun (actualAnalyticBlowupPullback_relative_point A e b) G
  change actualAnalyticBlowupPullback (actualTangentScalingVariables A e) e (fun _ => 0)
    (actualAnalyticBlowupPullback A e b G)=_ at hcomp
  have he : actualAnalyticBlowupPullback (actualTangentScalingVariables A e) e (fun _ => 0)
      (coordinateGerm e)=coordinateGerm e := by
    rw [actualAnalyticBlowupPullback_coordinate]
    simp [actualTangentScalingVariables]
  rw [map_mul,map_pow,he,hcomp] at hh
  exact hh

theorem actual_relative_quotient_point_unique (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (w : ℕ) (G H K : HolGerm (ComplexModel n))
    (hH : (coordinateGerm e)^w*H=actualAnalyticBlowupPullback A e b G)
    (hK : (coordinateGerm e)^w*K=
      actualAnalyticBlowupPullback univ e (actualPointChartDirection A b) G) :
    K=actualAnalyticBlowupPullback (actualTangentScalingVariables A e) e (fun _ => 0) H := by
  have he : (coordinateGerm e : HolGerm (ComplexModel n))≠0 :=
    HolomorphicGermReducednessBridge.coordinate_germ_ne_zero e
  apply mul_left_cancel₀ (pow_ne_zero w he)
  exact hK.trans (actual_relative_quotient_point_equation A e b w G H hH).symm

end
end TranscendentalNakamaye.Pending.HironakaActualRelativePointChartFactorization
