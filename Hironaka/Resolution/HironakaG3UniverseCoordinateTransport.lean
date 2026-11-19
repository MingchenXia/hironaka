import Hironaka.Resolution.HironakaG3UniverseComplexTransport
import Hironaka.Blowup.NormalCrossings
set_option autoImplicit false
set_option linter.style.haveILetI false
open Set Function
open scoped Manifold ContDiff
universe u v w
namespace Hironaka.HironakaG3UniverseCoordinateTransport
noncomputable section
open BlowupTowers NormalCrossings HironakaG3UniverseChartTransport

/-- The same coordinate witness works for the transported family. -/
theorem transported_coordinate_family {n : ℕ} {X : Type u} {Y : Type v} {ι : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) X]
    (e : X ≃ₜ Y) (A : ι → Set X) (S : ι → Finset (Fin n)) (y : Y)
    (h : IsCoordinateFamilyAt n A S (e.symm y)) :
    letI : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
    IsCoordinateFamilyAt n (fun i => e.symm ⁻¹' A i) S y := by
  letI : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
  have hpoint : (chartAt (ComplexModel n) y) y = (chartAt (ComplexModel n) (e.symm y)) (e.symm y) := by
    change ((chartAt (ComplexModel n) (e.symm y)).lift_openEmbedding e.isOpenEmbedding) y = _
    simpa only [e.apply_symm_apply] using
      (OpenPartialHomeomorph.lift_openEmbedding_apply (chartAt (ComplexModel n) (e.symm y)) e.isOpenEmbedding (x := e.symm y))
  have htarget : (chartAt (ComplexModel n) y).target = (chartAt (ComplexModel n) (e.symm y)).target := by
    change ((chartAt (ComplexModel n) (e.symm y)).lift_openEmbedding e.isOpenEmbedding).target = _
    exact OpenPartialHomeomorph.lift_openEmbedding_target _ _
  unfold IsCoordinateFamilyAt at h ⊢
  dsimp only [complexChartAt] at h ⊢
  rw [hpoint]
  rcases h with ⟨Φ,hsrc,hzero,hflat⟩
  refine ⟨Φ, ?_, hzero, ?_⟩
  · simpa only [htarget] using hsrc
  · intro i hi z hz hzΦ
    have hz' : e.symm z ∈ (chartAt (ComplexModel n) (e.symm y)).source := by
      change z ∈ e '' (chartAt (ComplexModel n) (e.symm y)).source at hz
      rcases hz with ⟨z',hz',rfl⟩
      simpa only [e.symm_apply_apply] using hz'
    have happly : (chartAt (ComplexModel n) y) z =
        (chartAt (ComplexModel n) (e.symm y)) (e.symm z) := by
      change ((chartAt (ComplexModel n) (e.symm y)).lift_openEmbedding e.isOpenEmbedding) z = _
      simpa only [e.apply_symm_apply] using
        (OpenPartialHomeomorph.lift_openEmbedding_apply (chartAt (ComplexModel n) (e.symm y)) e.isOpenEmbedding (x := e.symm z))
    rw [happly] at hzΦ ⊢
    exact hflat i hi hz' hzΦ
end
end Hironaka.HironakaG3UniverseCoordinateTransport
