import Hironaka.Resolution.HironakaG8PlaneLineProducts
import Hironaka.Resolution.HironakaActualRegularIntrinsicHSProfile
import Hironaka.Analytic.FibreDimensionLowerBound
import Hironaka.MarkedIdeal.CodimOneSupport

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8PlaneArrangementSingular
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  HironakaEmbeddedAnalytic HironakaActualRegularIntrinsicHSProfile
  HironakaHolomorphicJetChartInvariance HironakaG8PlaneLineGerms HironakaG8PlaneLineProducts

private theorem lineProductFunction_zero_iff (L : List ℂ) (z : ComplexModel 2) :
    lineProductFunction L z = 0 ↔ ∃ s ∈ L, lineLinear s z = 0 := by
  induction L with
  | nil => simp [lineProductFunction]
  | cons t L ih => simp [lineProductFunction, mul_eq_zero, ih]

private theorem mem_arrangement_zero {r : ℕ} (hr : 0 < r) : (0 : ComplexModel 2) ∈ planeLineArrangement r := by
  change lineProductFunction _ 0 = 0
  rw [lineProductFunction_zero_iff]
  exact ⟨0,List.mem_map.mpr ⟨0,List.mem_range.mpr hr,by norm_num⟩,map_zero _⟩

theorem origin_mem_singularSet_planeLineArrangement {r : ℕ} (hr : 2 ≤ r) :
    (0 : ComplexModel 2) ∈ singularSet (n := 2) (planeLineArrangement r) := by
  apply mem_singularSet_iff.mpr
  refine ⟨mem_arrangement_zero (by omega),?_⟩
  intro d hd
  have h₁ := hilbertSamuelAt_actual_regular hd.1 hd 1
  rw [planeLineArrangement_profile, if_neg (by omega : ¬ r ≤ 1), Nat.sub_zero, Nat.choose_succ_self_right] at h₁
  norm_num at h₁
  have hd2 : d = 2 := by omega
  subst d
  have h := hilbertSamuelAt_actual_regular hd.1 hd r
  rw [planeLineArrangement_profile, if_pos le_rfl, Nat.sub_self, Nat.add_zero] at h
  have hp : 0 < Nat.choose (2+r) 2 := Nat.choose_pos (by omega)
  norm_num at h
  omega


private theorem lineProductFunction_differentiable (L : List ℂ) :
    Differentiable ℂ (lineProductFunction L) := by
  induction L with
  | nil => exact differentiable_const _
  | cons s L ih => exact (lineLinear s).differentiable.mul ih

private theorem slopes_eq {s t : ℂ} {x : ComplexModel 2} (hx : x ≠ 0)
    (hs : lineLinear s x = 0) (ht : lineLinear t x = 0) : s = t := by
  change s * x 0 + x 1 = 0 at hs
  change t * x 0 + x 1 = 0 at ht
  have hx0 : x 0 ≠ 0 := by
    intro h
    apply hx
    have h1 : x 1 = 0 := by simpa [h] using hs
    ext i
    fin_cases i <;> assumption
  apply mul_right_cancel₀ hx0
  exact add_right_cancel (hs.trans ht.symm)

private theorem lineProductFunction_deriv {L : List ℂ} (hL : L.Nodup)
    {x : ComplexModel 2} (hx : x ≠ 0) (hzero : lineProductFunction L x = 0) :
    fderiv ℂ (lineProductFunction L) x
      (AnalyticJacobianSingularCore.coordinateDirection (1 : Fin 2)) ≠ 0 := by
  induction L with
  | nil => simp [lineProductFunction] at hzero
  | cons t L ih =>
    obtain ⟨ht,hL⟩ := List.nodup_cons.mp hL
    change lineLinear t x * lineProductFunction L x = 0 at hzero
    change fderiv ℂ ((lineLinear t : ComplexModel 2 → ℂ) * lineProductFunction L) x _ ≠ 0
    rw [((lineLinear t).hasFDerivAt.mul
      ((lineProductFunction_differentiable L x).hasFDerivAt)).fderiv]
    have hDirection : lineLinear t (AnalyticJacobianSingularCore.coordinateDirection (1 : Fin 2)) = 1 := by
      change t * (EuclideanSpace.single (1 : Fin 2) (1 : ℂ)) 0 + _ = _
      simp [AnalyticJacobianSingularCore.coordinateDirection]
    rcases mul_eq_zero.mp hzero with htx | hLx
    · have hne : lineProductFunction L x ≠ 0 := by
        intro h
        obtain ⟨s,hs,hsx⟩ := (lineProductFunction_zero_iff L x).mp h
        exact ht (slopes_eq hx hsx htx ▸ hs)
      simpa [htx,hDirection] using hne
    · by_cases htx : lineLinear t x = 0
      · obtain ⟨s,hs,hsx⟩ := (lineProductFunction_zero_iff L x).mp hLx
        exact (ht (slopes_eq hx hsx htx ▸ hs)).elim
      · simp [hLx,htx,ih hL hLx]

theorem regularAtDim_planeLineArrangement_of_ne_zero {r : ℕ} {x : ComplexModel 2}
    (hx : x ∈ planeLineArrangement r) (hn : x ≠ 0) :
    RegularAtDim (n := 2) (planeLineArrangement r) x 1 := by
  let L := (List.range r).map (fun i : ℕ => (i : ℂ))
  have hL : L.Nodup := List.nodup_range.map (fun a b h => by exact_mod_cast h)
  refine AnalyticJacobianCriterion.regularAtDim_of_localHypersurfaceMinor_ne_zero
    (N := univ) (f := lineProductFunction L) isOpen_univ (mem_univ _) ?_ ?_ ?_ hx (1 : Fin 2) ?_
  · simp [complexChartAt,chartAt_self_eq]
  · exact (lineProductFunction_differentiable L).differentiableOn
  · intro y _ _
    simp [complexChartAt,chartAt_self_eq,planeLineArrangement,L]
  · simpa only [complexChartAt,chartAt_self_eq,OpenPartialHomeomorph.refl_apply,id_eq] using
      lineProductFunction_deriv hL hn hx

theorem singularSet_planeLineArrangement {r : ℕ} (hr : 2 ≤ r) :
    singularSet (n := 2) (planeLineArrangement r) = {0} := by
  ext x
  constructor
  · intro hx
    by_contra hn
    have h := mem_singularSet_iff.mp hx
    exact h.2 1 (regularAtDim_planeLineArrangement_of_ne_zero h.1 hn)
  · rintro rfl
    exact origin_mem_singularSet_planeLineArrangement hr

theorem isComplexAnalyticSubset_planeLineArrangement (r : ℕ) :
    IsComplexAnalyticSubset (n := 2) (planeLineArrangement r) := by
  let L := (List.range r).map (fun i : ℕ => (i : ℂ))
  intro x
  refine ⟨⟨1, fun _ => lineProductFunction L, univ, isOpen_univ, mem_univ _, ?_,
    fun _ => (lineProductFunction_differentiable L).differentiableOn, ?_⟩⟩
  · simp [complexChartAt,chartAt_self_eq]
  · intro y _ _
    simp [complexChartAt,chartAt_self_eq,planeLineArrangement,L]

end HironakaG8PlaneArrangementSingular
