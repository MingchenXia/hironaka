/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.GermComponentDimension
import Hironaka.Analytic.RegularAtDimChart

set_option autoImplicit false
namespace Hironaka.GermComponentDimension
open Hironaka
noncomputable section
open Set Filter Metric
open scoped Topology
open Hironaka.RegularLocusDense Hironaka.AnalyticGermDecomposition Hironaka.GermParametrization Hironaka.GermParametrizationData Hironaka.AnalyticLocalStatement
open Hironaka.AnalyticDescendingChain Hironaka.RegularPointDimension Hironaka.RegularAtDimChart
variable {n : ℕ}

/-! ### The dimension of a local irreducible component -/

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **The local irreducible components of a closed irreducible analytic subvariety have
dimension `V.dim`.**  This is the pure-dimensionality of `V`
(`Pending.PureDimension.eq_dim_of_regularAtDim`) read at a point of the component: inside an
open set meeting only that component, its regular points of dimension `P.dim` are regular
points of the chart germ of `V`, hence of `V` itself. -/
theorem dim_eq_of_parametrizationData (V : ClosedIrreducibleAnalyticSubvariety n M) {x : M}
    {r : ℕ} {A : Fin r → Set (ComplexModel n)} (hA : ∀ i, IsIrreducibleGerm (A i))
    (hcover : chartGerm (n := n) V.carrier x =ᶠ[𝓝 0] (⋃ i, A i))
    (hpw : Pairwise fun i j => ¬ (A i ≤ᶠ[𝓝 0] A j))
    (i : Fin r) {L : ComplexModel n ≃L[ℂ] ComplexModel n}
    (P : ParametrizationData (L ⁻¹' A i)) (S : SetsData P) :
    P.dim = V.dim := by
  set e := (complexChartAt (n := n) x).val with he
  obtain ⟨Ωp, hΩpo, hΩp0, hΩp⟩ :=
    exists_pure_nhds_dim (hA i) fun ε hε => exists_regularAtDim_near_zero L S hε
  obtain ⟨ρ, hρ, hρs⟩ :=
    Metric.eventually_nhds_iff_ball.1 (Filter.eventuallyEq_set.mp hcover)
  obtain ⟨O', hO'o, hO'sub, hne, hdisj⟩ :=
    exists_isOpen_disjoint_others hA hpw i (isOpen_ball.inter hΩpo)
      ⟨mem_ball_self hρ, hΩp0⟩
  obtain ⟨z, hzO', hzA⟩ := hne
  obtain ⟨y, hyO', hyreg⟩ :=
    mem_closure_iff.mp ((hΩp O' hO'o (hO'sub.trans inter_subset_right)).2 ⟨hzA, hzO'⟩)
      O' hO'o hzO'
  -- on `O'` the chart germ of `V` is the single component `A i`
  have hcg : chartGerm (n := n) V.carrier x ∩ O' = A i ∩ O' := by
    ext w
    constructor
    · rintro ⟨hw, hwO⟩
      obtain ⟨j, hj⟩ := mem_iUnion.mp ((hρs w (hO'sub hwO).1).mp hw)
      by_cases hji : j = i
      · exact ⟨hji ▸ hj, hwO⟩
      · have : w ∈ O' ∩ A j := ⟨hwO, hj⟩
        rw [hdisj j hji] at this
        exact absurd this (notMem_empty w)
    · rintro ⟨hw, hwO⟩
      exact ⟨(hρs w (hO'sub hwO).1).mpr (mem_iUnion.2 ⟨i, hw⟩), hwO⟩
  have hyreg' : RegularAtDim (n := n) (M := ComplexModel n)
      (chartGerm (n := n) V.carrier x) y P.dim :=
    regularAtDim_of_inter_eq hO'o hyO' (by rw [hcg, inter_assoc, inter_self]) hyreg
  -- translate the chart germ back to the chart image
  have hyT : RegularAtDim (n := n) (M := ComplexModel n)
      (e.target ∩ e.symm ⁻¹' V.carrier) (y + e x) P.dim := by
    have hset : chartGerm (n := n) V.carrier x
        = {w : ComplexModel n | w - (-(e x)) ∈ e.target ∩ e.symm ⁻¹' V.carrier} := by
      ext w
      simp [chartGerm, sub_neg_eq_add, he]
    rw [hset] at hyreg'
    have h := (regularAtDim_translate_iff (S := e.target ∩ e.symm ⁻¹' V.carrier)
      (-(e x)) y).mp hyreg'
    simpa [sub_neg_eq_add] using h
  -- and read it on `M`
  have hyt : y + e x ∈ e.target := hyT.2.1.1
  have hwsrc : e.symm (y + e x) ∈ e.source := e.map_target hyt
  have hew : e (e.symm (y + e x)) = y + e x := e.right_inv hyt
  have h1 : RegularAtDim (n := n) (e.source ∩ e ⁻¹' (e.symm ⁻¹' V.carrier))
      (e.symm (y + e x)) P.dim := by
    rw [regularAtDim_chart_iff (complexChartAt (n := n) x) (e.symm ⁻¹' V.carrier) hwsrc, ← he,
      hew]
    rw [inter_comm] at hyT
    exact hyT
  have h2 : RegularAtDim (n := n) V.carrier (e.symm (y + e x)) P.dim := by
    refine regularAtDim_of_inter_eq e.open_source hwsrc ?_ h1
    ext u
    constructor
    · rintro ⟨⟨hu1, hu2⟩, hu3⟩
      refine ⟨?_, hu3⟩
      rw [mem_preimage, mem_preimage, e.left_inv hu1] at hu2
      exact hu2
    · rintro ⟨hu1, hu2⟩
      refine ⟨⟨hu2, ?_⟩, hu2⟩
      rw [mem_preimage, mem_preimage, e.left_inv hu2]
      exact hu1
  exact PureDimension.eq_dim_of_regularAtDim V h2

end
end Hironaka.GermComponentDimension
