import Hironaka.Blowup.BlowupSequenceInjectiveOffNull
import Hironaka.Analytic.HolomorphicNormalOrderDiscrepancy
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

set_option autoImplicit false

/-!
# Actual local discrepancy supplied by finite smooth-centre blowups

The actual exceptional-divisor nullity supplies nonzero coordinate
Jacobian germs. Finite normal order is internally produced, without
monomial-coordinate or discrepancy certificates. No uniform whole-divisor
bound, all-prime dictionary or arbitrary-modification result is claimed.
-/

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BlowupSequenceLocalDiscrepancy

open Hironaka.BlowupSequences Hironaka.HolomorphicMaps
  DemaillyApproximantDivisorialLelong DivisorialChangeOfVariables
  BlowupSequenceInjectiveOffNull HolomorphicNormalOrderDiscrepancy

/-- Actual nonexceptionality makes the literal flattened coordinate
Jacobian nonzero, by genuine derivative composition and inverse charts. -/
theorem complexJacobian_flatCoordMap_ne_zero_of_not_exceptional
    {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
    {π : Y → X} {E : Set Y} {x : Y} (Φ : DivisorFlattening (m := m) E x)
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ π)
    {z : ComplexModel (m + 1)} (hz : z ∈ Φ.flatDomain π)
    (hne : Φ.point z ∉ exceptionalLocus (m + 1) π) :
    complexJacobian (flatCoordMap π Φ) z ≠ 0 := by
  classical
  let I := 𝓘(ℂ, ComplexModel (m + 1))
  have hp : MDifferentiableAt I I Φ.point z := Φ.mdifferentiableAt_point hz.1
  have hchart : MDifferentiableAt I I
      (complexChartAt (n := m + 1) x).val (Φ.point z) :=
    ((contMDiffOn_chart (I := I) (n := ∞) (x := x)).contMDiffAt
      ((chartAt (ComplexModel (m + 1)) x).open_source.mem_nhds
        (Φ.point_mem_source hz.1))).mdifferentiableAt (by simp)
  have hcoord : MDifferentiableAt I I Φ.coord (Φ.point z) := by
    have hto : DifferentiableAt ℂ Φ.Φ.toFun
        ((complexChartAt (n := m + 1) x).val (Φ.point z)) := by
      rw [Φ.chart_point hz.1]
      exact Φ.Φ.toFun_holomorphic.differentiableAt
        (Φ.Φ.isOpen_source.mem_nhds (Φ.Φ.mapsTo_invFun hz.1))
    exact hto.mdifferentiableAt.comp (Φ.point z) hchart
  have heq : (Φ.coord ∘ Φ.point) =ᶠ[𝓝 z] id := by
    filter_upwards [Φ.Φ.isOpen_target.mem_nhds hz.1] with w hw
    exact Φ.coord_point hw
  have hleft : (mfderiv I I Φ.coord (Φ.point z)).comp (mfderiv I I Φ.point z) =
      ContinuousLinearMap.id ℂ (ComplexModel (m + 1)) := by
    rw [← mfderiv_comp z hcoord hp, heq.mfderiv_eq, mfderiv_id]
    rfl
  have hpinj : Function.Injective (mfderiv I I Φ.point z) := by
    have hli : Function.LeftInverse (mfderiv I I Φ.coord (Φ.point z))
        (mfderiv I I Φ.point z) := fun v => DFunLike.congr_fun hleft v
    exact hli.injective
  let P : ComplexModel (m + 1) →ₗ[ℂ] ComplexModel (m + 1) :=
    { toFun := mfderiv I I Φ.point z
      map_add' := (mfderiv I I Φ.point z).map_add
      map_smul' := (mfderiv I I Φ.point z).map_smul }
  have hpinjP : Function.Injective P := hpinj
  have hpbij : Function.Bijective (mfderiv I I Φ.point z) :=
    ⟨hpinj, (LinearMap.injective_iff_surjective (f := P)).mp hpinjP⟩
  have hπbij : Function.Bijective (mfderiv I I π (Φ.point z)) := by
    simpa only [exceptionalLocus, mem_ofPred_eq, not_not] using hne
  have hd : MDifferentiableAt I I
      (complexChartAt (n := m + 1) (π x)).val (π (Φ.point z)) :=
    ((contMDiffOn_chart (I := I) (n := ∞) (x := π x)).contMDiffAt
      ((chartAt (ComplexModel (m + 1)) (π x)).open_source.mem_nhds hz.2)).mdifferentiableAt
        (by simp)
  have hdinv : (mfderiv I I (complexChartAt (n := m + 1) (π x)).val
      (π (Φ.point z))).IsInvertible := by
    have hmem : π (Φ.point z) ∈ (extChartAt I (π x)).source := by
      rw [extChartAt_source]
      exact hz.2
    have h := isInvertible_mfderiv_extChartAt (I := I) (x := π x) hmem
    have hext : (extChartAt I (π x) : X → ComplexModel (m + 1)) =
        (complexChartAt (n := m + 1) (π x)).val := by
      funext y
      rfl
    rw [hext] at h
    exact h
  obtain ⟨L, hL⟩ := hdinv
  have hdbij : Function.Bijective (mfderiv I I (complexChartAt (n := m + 1) (π x)).val
      (π (Φ.point z))) := by
    rw [← hL]
    exact L.bijective
  have hπd : MDifferentiableAt I I π (Φ.point z) :=
    (hπ (Φ.point z)).mdifferentiableAt (by simp)
  have hder : mfderiv I I (flatCoordMap π Φ) z =
      (mfderiv I I (complexChartAt (n := m + 1) (π x)).val (π (Φ.point z))).comp
        ((mfderiv I I π (Φ.point z)).comp (mfderiv I I Φ.point z)) := by
    change mfderiv I I ((complexChartAt (n := m + 1) (π x)).val ∘ π ∘ Φ.point) z = _
    rw [mfderiv_comp z hd (hπd.comp z hp), mfderiv_comp z hπd hp]
    rfl
  have hbij : Function.Bijective (mfderiv I I (flatCoordMap π Φ) z) := by
    rw [hder]
    exact hdbij.comp (hπbij.comp hpbij)
  rw [mfderiv_eq_fderiv] at hbij
  let T := LinearEquiv.ofBijective (fderiv ℂ (flatCoordMap π Φ) z).toLinearMap hbij
  change LinearMap.det (fderiv ℂ (flatCoordMap π Φ) z).toLinearMap ≠ 0
  change LinearMap.det (T : ComplexModel (m + 1) →ₗ[ℂ] ComplexModel (m + 1)) ≠ 0
  rw [← LinearEquiv.coe_det]
  exact Units.ne_zero _


/-- An actual exceptional divisor of a finite smooth-centre blowup
sequence supplies frequent nonvanishing of the actual Jacobian. -/
theorem frequently_complexJacobian_ne_zero_of_isBlowupSequence
    {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
    {π : Y → X} (hπ : IsBlowupSequence (m + 1) X Y π)
    {E : Set Y} {x : Y} (Φ : DivisorFlattening (m := m) E x) :
    ∃ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
      complexJacobian (flatCoordMap π Φ) z ≠ 0 := by
  classical
  obtain ⟨D, hD⟩ := exists_effectiveDivisor_exceptionalLocus_subset hπ
  let e := complexChartAt (n := m + 1) x
  let T := e.val '' (D.support ∩ e.val.source) ∩ Φ.Φ.source
  let N := Φ.Φ.toFun '' T
  have hN : volume N = 0 := by
    exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      ((Φ.Φ.toFun_holomorphic.mono inter_subset_right).restrictScalars ℝ)
      (measure_mono_null inter_subset_left (measure_chart_image_support_eq_zero D x))
  have houtside : ∀ {z}, z ∈ Φ.flatDomain π → z ∉ N → Φ.point z ∉ D.support := by
    intro z hz hzN hzD
    exact hzN ⟨Φ.Φ.invFun z,
      ⟨⟨Φ.point z, ⟨hzD, Φ.point_mem_source hz.1⟩, Φ.chart_point hz.1⟩,
        Φ.Φ.mapsTo_invFun hz.1⟩, Φ.Φ.right_inv z hz.1⟩
  apply frequently_nhds_iff.mpr
  intro U h0U hU
  have hnear : U ∩ Φ.flatDomain π ∈ 𝓝 (0 : ComplexModel (m + 1)) :=
    inter_mem (hU.mem_nhds h0U)
      ((Φ.isOpen_flatDomain hπ.contMDiff.continuous).mem_nhds (Φ.zero_mem_flatDomain π))
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hnear
  have hnsub : ¬ ball (0 : ComplexModel (m + 1)) r ⊆ N := by
    intro hsub
    exact (measure_ball_pos volume (0 : ComplexModel (m + 1)) hr).ne'
      (measure_mono_null hsub hN)
  obtain ⟨z, hz, hzN⟩ := Set.not_subset.mp hnsub
  have hzD : z ∈ Φ.flatDomain π := (hrsub hz).2
  have hne : Φ.point z ∉ exceptionalLocus (m + 1) π :=
    fun h => houtside hzD hzN (hD h)
  exact ⟨z, (hrsub hz).1,
    complexJacobian_flatCoordMap_ne_zero_of_not_exceptional Φ hπ.contMDiff hzD hne⟩

/-- Actual finite smooth-centre geometry internally supplies finite
local discrepancy at every actual regular hypersurface point. -/
theorem exists_logDiscrepancyLE_of_isBlowupSequence_regular
    {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
    {π : Y → X} (hπ : IsBlowupSequence (m + 1) X Y π)
    {E : Set Y} {x : Y} (hreg : RegularAtDim (n := m + 1) E x m) :
    ∃ A : ℕ, LogDiscrepancyLE m π E x A := by
  obtain ⟨Φ⟩ := DivisorFlattening.nonempty_of_regularAtDim hreg
  exact exists_logDiscrepancyLE_of_nonzero_jacobian_germ Φ hπ.contMDiff
    (frequently_complexJacobian_ne_zero_of_isBlowupSequence hπ Φ)

end Hironaka.BlowupSequenceLocalDiscrepancy
