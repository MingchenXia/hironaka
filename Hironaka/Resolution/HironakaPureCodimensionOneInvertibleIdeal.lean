/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaPureSingularSetDictionary
import Hironaka.Analytic.RegularComponentClosureGeometry
import Hironaka.Analytic.ActualCodimensionOneLocalEquations
import Hironaka.Resolution.HironakaEmbeddedReducible
import Hironaka.Analytic.GlobalComponents
import Hironaka.Analytic.ActualReducedHolomorphicEquation
import Hironaka.Coherence.CartanIrreducible
import Hironaka.Coherence.CartanLocalReduction

import Hironaka.MarkedIdeal.GermIdealOrderValue
import Hironaka.MarkedIdeal.GermIdealOrderBounds

set_option autoImplicit false

open Set Filter Topology Metric
open scoped Manifold ContDiff

universe u

namespace Hironaka.HironakaPureCodimensionOneInvertibleIdeal

open AnalyticGermDecomposition AnalyticDescendingChain HolGerm
open GlobalComponents RegularLocusComponent OkaRelationSheaf OkaIdealOperations

noncomputable section

private theorem holomorphic_product {d : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → ComplexModel d → ℂ)
    (hf : ∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (f i) z) :
    ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (fun z => ∏ i ∈ s, f i z) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.prod_empty] using eventually_differentiableAt_const
      (E := ComplexModel d) 1
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using eventually_differentiableAt_mul (hf i) ih

private theorem germ_product {d : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → ComplexModel d → ℂ)
    (hf : ∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (f i) z) :
    HolGerm.mk (fun z => ∏ i ∈ s, f i z) (holomorphic_product s f hf) =
      ∏ i ∈ s, HolGerm.mk (f i) (hf i) := by
  apply Subtype.ext
  rw [HolGerm.coe_mk, SubmonoidClass.coe_finsetProd]
  simp only [HolGerm.coe_mk]
  have h := map_prod
    (Germ.coeRingHom (𝓝 (0 : ComplexModel d)) :
      (ComplexModel d → ℂ) →+* Germ (𝓝 (0 : ComplexModel d)) ℂ) f s
  simp only [Germ.coe_coeRingHom] at h
  rw [← h, Finset.prod_fn]


/-- Actual locally finite global irreducible components internally produce
an original nonzero equation for any pure analytic hypersurface chart germ. -/
theorem exists_nonzero_local_equation_of_pure {m : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
    {W : Set M} (hW : IsComplexAnalyticSubset (n := m + 1) W)
    (hpure : W ⊆ closure (regularLocus (n := m + 1) W m)) (x : M) :
    ∃ (f : ComplexModel (m + 1) → ℂ)
      (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z),
      HolGerm.mk f hf ≠ 0 ∧ chartGerm W x =ᶠ[𝓝 0] {z | f z = 0} := by
  classical
  obtain ⟨U, hU, hxU, hfin⟩ := exists_isOpen_finite_globalComponents hW x
  let S := {B | B ∈ globalComponents (n := m + 1) W ∧ (B ∩ U).Nonempty}
  let : Fintype S := hfin.fintype
  have hrep : ∀ i : S, ∃ (f : ComplexModel (m + 1) → ℂ)
      (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z),
      HolGerm.mk f hf ≠ 0 ∧ chartGerm i.1 x =ᶠ[𝓝 0] {z | f z = 0} := by
    intro i
    obtain ⟨c, ⟨k, hc⟩, hcomp⟩ := i.2.1
    have hcm : RegularAtDim (n := m + 1) W c m := by
      by_contra hn
      have hs : c ∈ W \ regularLocus (n := m + 1) W m := ⟨hc.2.1, hn⟩
      rw [HironakaEmbeddedReducible.diff_regularLocus_eq_of_pure hpure] at hs
      exact hs.2 k hc
    have hkm : k = m := RegularPointDimension.eq_of_regularAtDim hc hcm
    subst k
    let V : ClosedIrreducibleAnalyticSubvariety (m + 1) M := {
      carrier := i.1
      isClosed_carrier := by rw [hcomp]; exact isClosed_closure
      irreducible_carrier := isComplexAnalyticallyIrreducible_of_mem_globalComponents hW i.2.1
      dim := m
      dim_le := Nat.le_succ m
      regularLocus_nonempty := ⟨c, by rw [hcomp]; exact regularAtDim_closure_component hcm (mem_component_self hcm)⟩ }
    exact ActualCodimensionOneLocalEquations.exists_nonzero_local_equation V rfl x
  choose f hf hne hzero using hrep
  let F : ComplexModel (m + 1) → ℂ := fun z => ∏ i : S, f i z
  have hF : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ F z := holomorphic_product Finset.univ f hf
  have hLocal : ∀ y ∈ U, y ∈ W ↔ ∃ i : S, y ∈ i.1 := by
    intro y hyU
    constructor
    · intro hyW
      have hyUnion : y ∈ ⋃₀ globalComponents (n := m + 1) W := by
        rw [sUnion_globalComponents hW]
        exact hyW
      obtain ⟨B, hB, hyB⟩ := hyUnion
      exact ⟨⟨B, hB, y, hyB, hyU⟩, hyB⟩
    · rintro ⟨i, hy⟩
      exact subset_of_mem_globalComponents hW i.2.1 hy
  let e := (complexChartAt (n := m + 1) x).val
  let q := e x
  have hxsrc : x ∈ e.source := mem_complexChartAt_source x
  have h0q : (0 : ComplexModel (m + 1)) + q = q := zero_add q
  have hadd : Tendsto (fun z : ComplexModel (m + 1) => z + q) (𝓝 0) (𝓝 q) := by
    simpa only [zero_add] using (continuous_add_const q).tendsto (0 : ComplexModel (m + 1))
  have ht := hadd.eventually (e.open_target.mem_nhds (e.map_source hxsrc))
  have hinv : Tendsto (fun z : ComplexModel (m + 1) => e.symm (z + q)) (𝓝 0) (𝓝 x) := by
    simpa only [Function.comp_def, e.left_inv hxsrc] using (e.continuousAt_symm (e.map_source hxsrc)).tendsto.comp hadd
  refine ⟨F, hF, ?_, ?_⟩
  · rw [germ_product Finset.univ f hf]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hne i
  · apply eventuallyEq_set.mpr
    filter_upwards [ht, hinv.eventually (hU.mem_nhds hxU),
      eventually_all.mpr fun i => eventuallyEq_set.mp (hzero i)] with z hzT hzU hzi
    change (z + q ∈ e.target ∧ e.symm (z + q) ∈ W) ↔ ∏ i : S, f i z = 0
    refine (and_iff_right (show z + q ∈ e.target from hzT)).trans ?_
    rw [hLocal _ hzU]
    simp only [Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
    apply exists_congr
    intro i
    have hi := hzi i
    change (z + q ∈ e.target ∧ e.symm (z + q) ∈ i.1) ↔ f i z = 0 at hi
    exact (and_iff_right (show z + q ∈ e.target from hzT)).symm.trans hi

/-- Actual reduced germ and Cartan all-stalk generators produce one equation
for every nearby original stalk without any volume argument. -/
theorem exists_reduced_generator_neighbourhood {n : ℕ}
    (f : ComplexModel n → ℂ) (hf : HolAt f 0) (hF : HolGerm.mk f hf ≠ 0) :
    ∃ (ε : ℝ) (r : ComplexModel n → ℂ), 0 < ε ∧
      DifferentiableOn ℂ r (ball 0 ε) ∧
      (∀ y ∈ ball 0 ε, ∀ a : ComplexModel n → ℂ,
        vanishingIdealF {x | f x = 0} y a ↔ InSpanAt (fun _ : Fin 1 => r) y a) ∧
      ∀ y ∈ ball 0 ε, (f y = 0 ↔ r y = 0) := by
  classical
  obtain ⟨r, hr, _hR, _, hideal, hzero⟩ :=
    ActualReducedHolomorphicEquation.exists_reduced_equation f hf hF
  obtain ⟨Ω, hΩ, h0Ω, hfΩ⟩ := hf.exists_isOpen
  have hlocal := CartanIrreducibleReduction.localCartan_of_irreducibleLocalCartan
    (CartanIrreducible.irreducibleLocalCartan n)
  have hcoh : IdealFGAt (vanishingIdealF {x | f x = 0}) 0 := by
    simpa only [Fin.forall_fin_one] using
      hlocal Ω hΩ 1 (fun _ => f) (fun _ => hfΩ) 0 h0Ω
  obtain ⟨U, hU, h0U, μ, inst, s, hsU, hsgen⟩ := hcoh
  let : Fintype μ := inst
  have hquot : ∀ i : μ, ∃ (b : ComplexModel n → ℂ) (hb : HolAt b 0),
      s i =ᶠ[𝓝 0] fun x => b x * r x := by
    intro i
    have hsi : vanishingIdealF {x | f x = 0} 0 (s i) :=
      (hsgen 0 h0U _).mpr (inSpanAt_self
        (fun j => holAt_of_differentiableOn hU (hsU j) h0U) i)
    have hdiv : HolGerm.mk r hr ∣ HolGerm.mk (s i) hsi.1 :=
      Ideal.mem_span_singleton.mp (hideal ▸ mem_vanishingIdeal_mk.mpr hsi.2)
    obtain ⟨B, hB⟩ := hdiv
    obtain ⟨b, hb, hrep⟩ := HolGerm.exists_eq_mk B
    have heq : HolGerm.mk (s i) hsi.1 =
        HolGerm.mk (fun x => b x * r x) (eventually_differentiableAt_mul hb hr) := by
      rw [HolGerm.mk_mul b r hb hr, mul_comm, ← hrep]
      exact hB
    exact ⟨b, hb, HolGerm.mk_eq_mk_iff.mp heq⟩
  choose b hb hbeq using hquot
  have hev : ∀ᶠ y in 𝓝 (0 : ComplexModel n), y ∈ U ∧ HolAt r y ∧
      (∀ i, HolAt (b i) y) ∧ (∀ i, s i y = b i y * r y) ∧
      (f y = 0 ↔ r y = 0) := by
    filter_upwards [hU.mem_nhds h0U, OkaRelationSheaf.HolAt.eventually hr,
      eventually_all.mpr (fun i => OkaRelationSheaf.HolAt.eventually (hb i)),
      eventually_all.mpr hbeq, hzero] with y hy hry hby hsy hzy
    exact ⟨hy, hry, hby, hsy, hzy⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hrB : DifferentiableOn ℂ r (ball 0 ε) :=
    fun y hy => (hball y hy).2.1.differentiableAt.differentiableWithinAt
  refine ⟨ε, r, hε, hrB, ?_, ?_⟩
  · intro y hy a
    rcases hball y hy with ⟨hyU, _, hby, _, _⟩
    constructor
    · intro ha
      obtain ⟨hahol, c, hc, hsum⟩ := (hsgen y hyU a).mp ha
      refine ⟨hahol, fun _ x => ∑ i, c i x * b i x,
        fun _ => OkaRelationSheaf.HolAt.fintype_sum (fun i => (hc i).mul (hby i)), ?_⟩
      filter_upwards [hsum, isOpen_ball.mem_nhds hy] with x hsum hx
      simp only [Fin.sum_univ_one]
      rw [hsum]
      calc
        ∑ i, c i x * s i x = ∑ i, (c i x * b i x) * r x := by
          apply Finset.sum_congr rfl
          intro i _
          rw [(hball x hx).2.2.2.1 i, mul_assoc]
        _ = (∑ i, c i x * b i x) * r x := (Finset.sum_mul _ _ _).symm
    · rintro ⟨hahol, c, _, heq⟩
      refine ⟨hahol, ?_⟩
      filter_upwards [heq, isOpen_ball.mem_nhds hy] with x heq hx hfx
      have hrx := (hball x hx).2.2.2.2.mp hfx
      simpa only [Fin.sum_univ_one, hrx, mul_zero] using heq
  · intro y hy
    exact (hball y hy).2.2.2.2


variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (n + 1)) M] [IsComplexManifold (n + 1) M]

omit [IsComplexManifold (n + 1) M] in
/-- The actual original chart germ equation yields one generator of every
nearby original chart stalk, entirely by holomorphic reduction and coherence. -/
theorem exists_original_principal_chart_neighbourhood {W : Set M} (x : M)
    (f : ComplexModel (n + 1) → ℂ) (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z)
    (hF : HolGerm.mk f hf ≠ 0) (hzero : chartGerm W x =ᶠ[𝓝 0] {z | f z = 0}) :
    ∃ (ε : ℝ) (r : ComplexModel (n + 1) → ℂ), 0 < ε ∧
      DifferentiableOn ℂ r (ball 0 ε) ∧
      (∀ y ∈ ball 0 ε, ∀ a : ComplexModel (n + 1) → ℂ,
        vanishingIdealF (chartGerm W x) y a ↔
          InSpanAt (fun _ : Fin 1 => r) y a) ∧
      (∀ y ∈ ball 0 ε, (y ∈ chartGerm W x ↔ r y = 0)) ∧
      ∀ y ∈ ball 0 ε, y + (complexChartAt (n := n + 1) x).val x ∈
        (complexChartAt (n := n + 1) x).val.target := by
  obtain ⟨ε, r, hε, hr, hgen, hfr⟩ :=
    exists_reduced_generator_neighbourhood
      f hf hF
  let e := (complexChartAt (n := n + 1) x).val
  have ht : ∀ᶠ z in 𝓝 (0 : ComplexModel (n + 1)), z + e x ∈ e.target :=
    (continuous_add_const (e x)).tendsto' 0 (e x) (zero_add _) |>.eventually
      (e.open_target.mem_nhds (e.map_source (mem_chart_source _ x)))
  have hev := (CartanIrreducibleReduction.vanishingIdealF_congr_eventually hzero).and
    ((eventuallyEq_set.mp hzero).and ht)
  obtain ⟨δ, hδ, hδprop⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨min ε δ, r, lt_min hε hδ, hr.mono (ball_subset_ball (min_le_left _ _)),
    ?_, ?_, ?_⟩
  · intro y hy a
    exact (hδprop y (ball_subset_ball (min_le_right _ _) hy)).1 a |>.trans
      (hgen y (ball_subset_ball (min_le_left _ _) hy) a)
  · intro y hy
    exact (hδprop y (ball_subset_ball (min_le_right _ _) hy)).2.1 |>.trans
      (hfr y (ball_subset_ball (min_le_left _ _) hy))
  · intro y hy
    exact (hδprop y (ball_subset_ball (min_le_right _ _) hy)).2.2

private theorem holomorphicAt_comp_centered {x y : M}
    (hy : y ∈ (chartAt (ComplexModel (n + 1)) x).source)
    {r : ComplexModel (n + 1) → ℂ}
    (hr : HolAt r ((chartAt (ComplexModel (n + 1)) x y) -
      (chartAt (ComplexModel (n + 1)) x x))) :
    HolomorphicIdealSheaves.HolomorphicAt (n + 1)
      (fun p => r ((chartAt (ComplexModel (n + 1)) x p) -
        (chartAt (ComplexModel (n + 1)) x x))) y := by
  exact CartanLocalReduction.holomorphicAt_comp_chart hy
    (hr.comp (φ := fun z : ComplexModel (n + 1) =>
        z - (chartAt (ComplexModel (n + 1)) x x))
      (y := chartAt (ComplexModel (n + 1)) x y)
      (continuous_id.sub continuous_const)
      (fun _ => differentiableAt_id.sub (differentiableAt_const _)))


/-- Actual original local equations and actual empty interior give a genuine
nondegenerate all-stalk generator, without any zero-volume-set criterion. -/
theorem isInvertible_vanishingIdeal_of_original_equations {W : Set M}
    (hint : interior W = ∅)
    (hEq : ∀ x : M, ∃ (f : ComplexModel (n + 1) → ℂ)
      (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z),
      HolGerm.mk f hf ≠ 0 ∧ chartGerm W x =ᶠ[𝓝 0] {z | f z = 0}) :
    (HolomorphicIdealSheaves.vanishingIdeal (n := n + 1) W).IsInvertible := by
  intro x
  obtain ⟨f, hf, hF, hEqzero⟩ := hEq x
  obtain ⟨ε, r, hε, hr, hgen, hzero, _htarget⟩ :=
    exists_original_principal_chart_neighbourhood x f hf hF hEqzero
  let e := chartAt (ComplexModel (n + 1)) x
  let q := e x
  let c : M → ComplexModel (n + 1) := fun y => e y - q
  let U : Set M := e.source ∩ e ⁻¹' ((fun w => w - q) ⁻¹' ball 0 ε)
  let h : M → ℂ := fun y => r (c y)
  have hU : IsOpen U :=
    e.isOpen_inter_preimage ((isOpen_ball : IsOpen (ball (0 : ComplexModel (n + 1)) ε)).preimage
      (continuous_id.sub continuous_const))
  have hxU : x ∈ U := by
    refine ⟨mem_chart_source _ x, ?_⟩
    change e x - e x ∈ ball (0 : ComplexModel (n + 1)) ε
    simpa only [sub_self] using
      (mem_ball_self hε : (0 : ComplexModel (n + 1)) ∈ ball 0 ε)
  have hhol : ∀ y ∈ U, HolomorphicIdealSheaves.HolomorphicAt (n + 1) h y :=
    fun y hy => holomorphicAt_comp_centered hy.1 (holAt_of_differentiableOn isOpen_ball hr hy.2)
  have hVzero : ∀ y ∈ U, (y ∈ W ↔ h y = 0) := by
    intro y hy
    have hcg : (c y ∈ chartGerm W x ↔ y ∈ W) := by
      change ((e y - q) + q ∈ e.target ∧ e.symm ((e y - q) + q) ∈ W) ↔ _
      rw [sub_add_cancel, e.left_inv hy.1]
      exact and_iff_right (e.map_source hy.1)
    exact hcg.symm.trans (hzero (c y) hy.2)
  refine ⟨U, hU, hxU, h, fun y hy => (hhol y hy).mdifferentiableAt.mdifferentiableWithinAt,
    ?_, ?_⟩
  · intro Z hZ hZU hZne
    by_contra hn
    push Not at hn
    obtain ⟨y, hyZ⟩ := hZne
    have hZW : Z ⊆ W := fun z hz => (hVzero z (hZU hz)).mpr (hn z hz)
    have hyI : y ∈ interior W := mem_interior_iff_mem_nhds.mpr
      (mem_of_superset (hZ.mem_nhds hyZ) hZW)
    rw [hint] at hyI
    exact hyI
  · intro y hy g
    constructor
    · intro hg
      let G : ComplexModel (n + 1) → ℂ := fun z => g (e.symm (z + q))
      have hgchart : HolAt (fun w => g (e.symm w)) (c y + q) := by
        simpa only [c, sub_add_cancel] using
          CartanLocalReduction.holAt_comp_chart_symm hy.1 hg.1
      have hGhol : HolAt G (c y) :=
        hgchart.comp (φ := fun z : ComplexModel (n + 1) => z + q) (y := c y)
          (continuous_add_const q)
          (fun _ => differentiableAt_id.add_const q)
      have hadd : Tendsto (fun z : ComplexModel (n + 1) => z + q)
          (𝓝 (c y)) (𝓝 (e y)) := by
        simpa only [c, sub_add_cancel] using (continuous_add_const q).tendsto (c y)
      have hInv : Tendsto (fun z => e.symm (z + q)) (𝓝 (c y)) (𝓝 y) := by
        simpa only [Function.comp_def, e.left_inv hy.1] using
          (e.continuousAt_symm (e.map_source hy.1)).tendsto.comp hadd
      have hG : vanishingIdealF (chartGerm W x) (c y) G := by
        refine ⟨hGhol, ?_⟩
        filter_upwards [hInv.eventually hg.2] with z hz hzV
        exact hz hzV.2
      obtain ⟨_, a, ha, hGa⟩ := (hgen (c y) hy.2 G).mp hG
      apply HolomorphicIdealSheaves.isInSpanAt_eq_iff.mpr
      refine ⟨hg.1, fun p => a 0 (c p), holomorphicAt_comp_centered hy.1 (ha 0), ?_⟩
      have hC : Tendsto c (𝓝 y) (𝓝 (c y)) :=
        (e.continuousAt hy.1).sub_const q
      filter_upwards [e.open_source.mem_nhds hy.1, hC.eventually hGa] with p hp hpa
      simpa only [G, h, c, sub_add_cancel, e.left_inv hp, Fin.sum_univ_one] using hpa
    · intro hg
      obtain ⟨hghol, a, _, heq⟩ := HolomorphicIdealSheaves.isInSpanAt_eq_iff.mp hg
      refine ⟨hghol, ?_⟩
      filter_upwards [heq, hU.mem_nhds hy] with p hp hpU hpV
      rw [hp, (hVzero p hpU).mp hpV, mul_zero]

/-- The complete original ideal of any pure analytic hypersurface is
invertible; original components and equations are all produced internally. -/
theorem isInvertible_vanishingIdeal_of_pure {W : Set M}
    (hW : IsComplexAnalyticSubset (n := n + 1) W)
    (hpure : W ⊆ closure (regularLocus (n := n + 1) W n)) :
    (HolomorphicIdealSheaves.vanishingIdeal (n := n + 1) W).IsInvertible :=
  isInvertible_vanishingIdeal_of_original_equations
    (HironakaEmbeddedReducible.interior_eq_empty_of_pure (Nat.lt_succ_self n) hpure)
    (exists_nonzero_local_equation_of_pure hW hpure)

end
end Hironaka.HironakaPureCodimensionOneInvertibleIdeal
