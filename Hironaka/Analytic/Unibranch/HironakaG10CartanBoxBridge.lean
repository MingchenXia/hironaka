import Hironaka.Analytic.GAGA.CoreCTheoremB
import Hironaka.Resolution.HironakaG10FlatTheoremAGlue
import Hironaka.Resolution.HironakaG10FlatPrivilegedEuclidean

/-! # Cartan's box theorems in the G10 relation-sheaf interface -/
set_option autoImplicit false
open Set Filter Metric
open scoped Topology
namespace Hironaka.Analytic.Unibranch.HironakaG10CartanBoxBridge
open Hironaka OkaRelationSheaf HironakaG10FlatTheoremAGlue
  HironakaG10FlatPrivilegedEuclidean
open Hironaka.Analytic.GAGA.Core Hironaka.Analytic.GAGA.Core.GermModule Hironaka.Analytic.GAGA.Core.Box Hironaka.Analytic.GAGA.Core.TheoremB

/-- The GAGA kernel module is the same germwise relation predicate used
  in the G10 Frisch development. -/
theorem mem_kernel_iff_relation {X ι κ : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [Fintype ι] [Fintype κ] (F : κ → ι → X → ℂ) (y : X) (a : ι → X → ℂ) :
    (GermModule.ker F).mem y a ↔ IsRelationAt F y a := by
  rw [GermModule.mem_ker_iff]
  constructor
  · rintro ⟨hhol,hrel⟩
    refine ⟨hhol,fun i => ?_⟩
    filter_upwards [hrel i] with x hx
    simpa only [Hironaka.Analytic.GAGA.Core.matApply,mul_comm] using hx
  · rintro ⟨hhol,hrel⟩
    refine ⟨hhol,fun i => ?_⟩
    filter_upwards [hrel i] with x hx
    simpa only [Hironaka.Analytic.GAGA.Core.matApply,mul_comm] using hx

/-- A kernel-module generating family is a G10 relation generating family. -/
theorem generatesRelationsOn_of_kernel_generated
    {X ι κ μ : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [Fintype ι] [Fintype κ] [Fintype μ] {U : Set X} (hU : IsOpen U)
    (F : κ → ι → X → ℂ) (σ : μ → ι → X → ℂ)
    (hσ : (GermModule.ker F).GeneratedOn U σ) : GeneratesRelationsOn F U σ := by
  refine ⟨hσ.1, ?_, ?_⟩
  · intro k i y hy
    have hr := (mem_kernel_iff_relation F y (σ k)).mp (hσ.gen_mem hy k)
    exact ((hr.2 i).and (hU.mem_nhds hy)).self_of_nhds.1
  · intro y hy a ha
    exact (hσ.2 y hy a).mp ((mem_kernel_iff_relation F y a).mpr ha)

/-- A G10 relation-generating family generates the coherent kernel module. -/
theorem kernel_generated_of_generatesRelationsOn
    {X ι κ μ : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [Fintype ι] [Fintype κ] [Fintype μ] {U : Set X} (hU : IsOpen U)
    (F : κ → ι → X → ℂ) (σ : μ → ι → X → ℂ)
    (hM : (GermModule.ker F).IsCoherentOn U)
    (hσ : GeneratesRelationsOn F U σ) : (GermModule.ker F).GeneratedOn U σ := by
  refine ⟨hσ.1,fun y hy a => ⟨?_,?_⟩⟩
  · intro ha
    exact hσ.2.2 y hy a ((mem_kernel_iff_relation F y a).mp ha)
  · intro ha
    apply (hM y hy).mem_of_isCombinationAt _ ha
    intro k
    apply (mem_kernel_iff_relation F y (σ k)).mpr
    refine ⟨fun j => holAt_of_differentiableOn hU (hσ.1 k j) hy, fun i => ?_⟩
    filter_upwards [hU.mem_nhds hy] with x hx
    exact hσ.2.1 k i x hx

/-- Relation Theorem A on any compact convex product box. -/
theorem ta_box (n : ℕ) (C : Fin n → Set ℂ) (hbox : IsBox C) :
    TA (EuclideanSpace ℂ (Fin n)) (boxSet C) := by
  intro U hU hKU κ ι _ _ F hF
  have hM : (GermModule.ker F).IsCoherentOn U := by
    intro y hy
    apply GermModule.CoherentAt.ker (OkaCoherence.okaProperty_euclidean n)
    intro i j
    exact holAt_of_differentiableOn hU (hF i j) hy
  obtain ⟨V,hV,hKV,μ,hμ,σ,hσ⟩ := theoremA_box hbox hU hKU hM
  let : Fintype μ := hμ
  refine ⟨V ∩ U,hV.inter hU,subset_inter hKV hKU,inter_subset_right,μ,hμ,σ,?_⟩
  exact generatesRelationsOn_of_kernel_generated (hV.inter hU) F σ (hσ.mono inter_subset_left)

/-- Relation Theorem B on any compact convex product box. -/
theorem tb_box (n : ℕ) (C : Fin n → Set ℂ) (hbox : IsBox C) :
    TB (EuclideanSpace ℂ (Fin n)) (boxSet C) := by
  intro U hU hKU κ ι μ _ _ _ F σ hF hσ v hv hrel
  have hM : (GermModule.ker F).IsCoherentOn U := by
    intro y hy
    apply GermModule.CoherentAt.ker (OkaCoherence.okaProperty_euclidean n)
    intro i j
    exact holAt_of_differentiableOn hU (hF i j) hy
  have hgen := kernel_generated_of_generatesRelationsOn hU F σ hM hσ
  have hvM : ∀ y ∈ U, (GermModule.ker F).mem y v := by
    intro y hy
    apply (mem_kernel_iff_relation F y v).mpr
    refine ⟨fun j => holAt_of_differentiableOn hU (hv j) hy, fun i => ?_⟩
    filter_upwards [hU.mem_nhds hy] with x hx
    exact hrel i x hx
  obtain ⟨V,hV,hKV,A,hA,hAv⟩ := division_box hbox hU hKU hM U hU hKU μ σ hgen v hvM
  refine ⟨V ∩ U,hV.inter hU,subset_inter hKV hKU,inter_subset_right,A,?_,?_⟩
  · intro k; exact (hA k).mono inter_subset_left
  · intro j x hx; exact hAv x hx.1 j

/-- Closed polydiscs satisfy the relation forms of Cartan's Theorems A and B. -/
theorem ta_tb_closedPolydisc (n : ℕ) {K : Set (EuclideanSpace ℂ (Fin n))}
    (hK : K ∈ closedPolydiscs n) :
    TA (EuclideanSpace ℂ (Fin n)) K ∧ TB (EuclideanSpace ℂ (Fin n)) K := by
  obtain ⟨c,ρ,hρ,rfl⟩ := hK
  let C : Fin n → Set ℂ := fun i => closedBall (c i) (ρ i)
  have hbox : IsBox C := ⟨fun i => isCompact_closedBall (c i) (ρ i),
    fun i => convex_closedBall (c i) (ρ i)⟩
  exact ⟨ta_box n C hbox, tb_box n C hbox⟩

end Hironaka.Analytic.Unibranch.HironakaG10CartanBoxBridge
