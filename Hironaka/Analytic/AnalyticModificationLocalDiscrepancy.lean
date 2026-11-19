import Hironaka.Blowup.BlowupSequenceLocalDiscrepancy
import Hironaka.Analytic.ModificationMassInvariance
import Mathlib.Topology.Maps.Proper.Basic

set_option autoImplicit false

/-! # Actual proper holomorphic modifications and internally produced local discrepancy -/

open Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.AnalyticModificationLocalDiscrepancy

open Hironaka.BlowupSequences DemaillyApproximantDivisorialLelong
  BlowupSequenceLocalDiscrepancy HolomorphicNormalOrderDiscrepancy DivisorialChangeOfVariables

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- Standard proper holomorphic geometry with a genuine holomorphic inverse
off actual closed nowhere-dense analytic exceptional sets. -/
def IsAnalyticModification (π : Y → X) : Prop :=
  ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π ∧ IsProperMap π ∧
    ∃ (A : Set Y) (B : Set X) (s : X → Y),
      IsClosed A ∧ IsComplexAnalyticSubset (n := n) A ∧ interior A = ∅ ∧
      IsClosed B ∧ IsComplexAnalyticSubset (n := n) B ∧ interior B = ∅ ∧
      π ⁻¹' B = A ∧
      ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s Bᶜ ∧
      (∀ x ∉ B, π (s x) = x) ∧ ∀ y ∉ A, s (π y) = y

/-- Genuine inverse equations internally give nonexceptionality, rather
than assuming a Jacobian or differential certificate. -/
theorem exists_analytic_exceptional_set_of_isAnalyticModification
    {π : Y → X} (hπ : IsAnalyticModification (n := n) π) :
    ∃ A : Set Y, IsClosed A ∧ IsComplexAnalyticSubset (n := n) A ∧
      interior A = ∅ ∧ InjOn π Aᶜ ∧ ∀ y ∉ A, y ∉ exceptionalLocus n π := by
  obtain ⟨A, B, s, hAc, hAa, hAi, hBc, _, _, hpre, hs, _, hleft⟩ := hπ.2.2
  refine ⟨A, hAc, hAa, hAi, ?_, ?_⟩
  · intro y hy z hz hyz
    exact (hleft y hy).symm.trans ((congrArg s hyz).trans (hleft z hz))
  · intro y hy
    let I := 𝓘(ℂ, ComplexModel n)
    have hpy : π y ∈ Bᶜ := by
      intro h
      apply hy
      change y ∈ π ⁻¹' B at h
      rwa [hpre] at h
    have hsd : MDifferentiableAt I I s (π y) :=
      (hs.contMDiffAt (hBc.isOpen_compl.mem_nhds hpy)).mdifferentiableAt (by simp)
    have hpd : MDifferentiableAt I I π y := (hπ.1 y).mdifferentiableAt (by simp)
    have heq : (s ∘ π) =ᶠ[𝓝 y] id := by
      filter_upwards [hAc.isOpen_compl.mem_nhds hy] with z hz
      exact hleft z hz
    have hder : (mfderiv I I s (π y)).comp (mfderiv I I π y) =
        ContinuousLinearMap.id ℂ (ComplexModel n) := by
      rw [← mfderiv_comp y hsd hpd, heq.mfderiv_eq, mfderiv_id]
      rfl
    have hinj : Function.Injective (mfderiv I I π y) := by
      have hli : Function.LeftInverse (mfderiv I I s (π y)) (mfderiv I I π y) :=
        fun v => DFunLike.congr_fun hder v
      exact hli.injective
    let T : ComplexModel n →ₗ[ℂ] ComplexModel n :=
      { toFun := mfderiv I I π y
        map_add' := (mfderiv I I π y).map_add
        map_smul' := (mfderiv I I π y).map_smul }
    have hinjT : Function.Injective T := hinj
    have hbij : Function.Bijective (mfderiv I I π y) :=
      ⟨hinj, (LinearMap.injective_iff_surjective (f := T)).mp hinjT⟩
    simpa only [exceptionalLocus, mem_ofPred_eq, not_not] using hbij

private theorem measure_chart_image_analytic_eq_zero
    {A : Set Y} (hA : IsComplexAnalyticSubset (n := n) A)
    (hint : interior A = ∅) (e : ComplexChart n Y) :
    volume (e.val '' (A ∩ e.val.source)) = 0 := by
  have hnull := (ModificationMassInvariance.manifoldLocallyPluripolar_of_isComplexAnalyticSubset
    hA hint).chart_measure_eq_zero e volume
  have heq : e.val '' (A ∩ e.val.source) = pluripolarChartSet A e := by
    ext z
    constructor
    · rintro ⟨y, ⟨hyA, hye⟩, rfl⟩
      exact ⟨e.val.map_source hye, by simpa only [mem_preimage, e.val.left_inv hye] using hyA⟩
    · intro hz
      exact ⟨e.val.symm z, ⟨hz.2, e.val.map_target hz.1⟩, e.val.right_inv hz.1⟩
  rwa [← heq] at hnull

/-- The actual analytic exceptional set supplies the literal chart-null
injectivity predicate without a measure or nullity input. -/
theorem isInjectiveOffNull_of_isAnalyticModification
    {m : ℕ} {Z : Type u} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel (m + 1)) Z] [IsComplexManifold (m + 1) Z]
    {T : Type u} [TopologicalSpace T]
    [ChartedSpace (ComplexModel (m + 1)) T] [IsComplexManifold (m + 1) T]
    {π : T → Z} (hπ : IsAnalyticModification (n := m + 1) π) : IsInjectiveOffNull m π := by
  obtain ⟨A, _, hA, hint, hinj, _⟩ :=
    exists_analytic_exceptional_set_of_isAnalyticModification hπ
  exact ⟨A, fun y => measure_chart_image_analytic_eq_zero hA hint (complexChartAt y), hinj⟩

/-- Positive Haar balls in genuine flattening domains meet the complement
of the actual analytic exceptional set. -/
theorem frequently_complexJacobian_ne_zero_of_isAnalyticModification
    {m : ℕ} {Z : Type u} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel (m + 1)) Z] [IsComplexManifold (m + 1) Z]
    {T : Type u} [TopologicalSpace T]
    [ChartedSpace (ComplexModel (m + 1)) T] [IsComplexManifold (m + 1) T]
    {π : T → Z} (hπ : IsAnalyticModification (n := m + 1) π)
    {E : Set T} {x : T} (Φ : DivisorFlattening (m := m) E x) :
    ∃ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
      complexJacobian (flatCoordMap π Φ) z ≠ 0 := by
  classical
  obtain ⟨A, _, hA, hint, _, hnonexc⟩ :=
    exists_analytic_exceptional_set_of_isAnalyticModification hπ
  let e := complexChartAt (n := m + 1) x
  let S := e.val '' (A ∩ e.val.source) ∩ Φ.Φ.source
  let N := Φ.Φ.toFun '' S
  have hN : volume N = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      ((Φ.Φ.toFun_holomorphic.mono inter_subset_right).restrictScalars ℝ)
      (measure_mono_null inter_subset_left (measure_chart_image_analytic_eq_zero hA hint e))
  have houtside : ∀ {z}, z ∈ Φ.flatDomain π → z ∉ N → Φ.point z ∉ A := by
    intro z hz hzN hzA
    exact hzN ⟨Φ.Φ.invFun z,
      ⟨⟨Φ.point z, ⟨hzA, Φ.point_mem_source hz.1⟩, Φ.chart_point hz.1⟩,
        Φ.Φ.mapsTo_invFun hz.1⟩, Φ.Φ.right_inv z hz.1⟩
  apply frequently_nhds_iff.mpr
  intro U h0U hU
  have hnear : U ∩ Φ.flatDomain π ∈ 𝓝 (0 : ComplexModel (m + 1)) :=
    inter_mem (hU.mem_nhds h0U)
      ((Φ.isOpen_flatDomain hπ.1.continuous).mem_nhds (Φ.zero_mem_flatDomain π))
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hnear
  have hnsub : ¬ ball (0 : ComplexModel (m + 1)) r ⊆ N := by
    intro hsub
    exact (measure_ball_pos volume (0 : ComplexModel (m + 1)) hr).ne'
      (measure_mono_null hsub hN)
  obtain ⟨z, hz, hzN⟩ := Set.not_subset.mp hnsub
  have hzD : z ∈ Φ.flatDomain π := (hrsub hz).2
  exact ⟨z, (hrsub hz).1,
    complexJacobian_flatCoordMap_ne_zero_of_not_exceptional Φ hπ.1 hzD
      (hnonexc (Φ.point z) (houtside hzD hzN))⟩

/-- Finite normal order of the actual nonzero holomorphic Jacobian germ
internally supplies a point-dependent local discrepancy. -/
theorem exists_logDiscrepancyLE_of_isAnalyticModification_regular
    {m : ℕ} {Z : Type u} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel (m + 1)) Z] [IsComplexManifold (m + 1) Z]
    {T : Type u} [TopologicalSpace T]
    [ChartedSpace (ComplexModel (m + 1)) T] [IsComplexManifold (m + 1) T]
    {π : T → Z} (hπ : IsAnalyticModification (n := m + 1) π)
    {E : Set T} {x : T} (hreg : RegularAtDim (n := m + 1) E x m) :
    ∃ A : ℕ, LogDiscrepancyLE m π E x A := by
  obtain ⟨Φ⟩ := DivisorFlattening.nonempty_of_regularAtDim hreg
  exact exists_logDiscrepancyLE_of_nonzero_jacobian_germ Φ hπ.1
    (frequently_complexJacobian_ne_zero_of_isAnalyticModification hπ Φ)

end
end Hironaka.AnalyticModificationLocalDiscrepancy
