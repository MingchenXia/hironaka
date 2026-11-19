import Hironaka.Resolution.HironakaSmoothCentreRealDomainActualSheafStalk
import Hironaka.Resolution.HironakaActualOpenIntrinsicHS
import Hironaka.Coherence.CartanLocalReduction
import Hironaka.Coherence.OkaGermBridge
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.HironakaG10OpenCoherentProjectionFlatOpen
noncomputable section
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HolGerm
  OkaRelationSheaf OkaGermBridge HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaHolomorphicJetRankLoci
theorem open_chart_apply {n : ℕ} (O : Opens (ComplexModel n)) (x y : O) :
    chartAt (ComplexModel n) x y = y.val := rfl

theorem open_chart_source {n : ℕ} (O : Opens (ComplexModel n)) (x : O) :
    (chartAt (ComplexModel n) x).source = Set.univ := by
  simp only [Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source, chartAt_self_eq,
    OpenPartialHomeomorph.refl_source, Set.preimage_univ]

theorem open_chart_symm_val {n : ℕ} (O : Opens (ComplexModel n)) (x : O)
    {z : ComplexModel n} (hz : z ∈ O) :
    ((chartAt (ComplexModel n) x).symm z).val = z := by
  have ht : z ∈ (chartAt (ComplexModel n) x).target := by
    rw [← (chartAt (ComplexModel n) x).image_source_eq_target]
    exact ⟨⟨z, hz⟩, by rw [open_chart_source]; trivial, rfl⟩
  exact (chartAt (ComplexModel n) x).right_inv ht

theorem chartTranslatedGerm_open_eq_germAt {n : ℕ} (O : Opens (ComplexModel n))
    (x y : O) (f : O → ℂ) (hf : HolomorphicAt n f y) :
    chartTranslatedGerm y y (mem_chart_source _ y) f hf =
      germAt y.val (fun z => f ((chartAt (ComplexModel n) x).symm z)) := by
  have hy : y ∈ (chartAt (ComplexModel n) x).source := by rw [open_chart_source]; trivial
  have hfc := CartanLocalReduction.holAt_comp_chart_symm hy hf
  rw [open_chart_apply] at hfc
  unfold chartTranslatedGerm translatedGerm
  rw [germAt_of_holAt hfc]
  apply HolGerm.mk_eq_mk_iff.mpr
  have hO : ∀ᶠ z in 𝓝 (0 : ComplexModel n), y.val + z ∈ O :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds
      (by simpa only [Pi.add_apply, Function.id_def, add_zero] using O.isOpen.mem_nhds y.property)
  filter_upwards [hO] with z hz
  apply congrArg f
  apply Subtype.ext
  rw [open_chart_apply, add_comm z y.val]
  exact (open_chart_symm_val O y hz).trans (open_chart_symm_val O x hz).symm

end
end Hironaka.Analytic.Unibranch.HironakaG10OpenCoherentProjectionFlatOpen
