import Hironaka.Resolution.HironakaG3UniverseCoordinateTransport
set_option autoImplicit false
set_option linter.style.haveILetI false
open Set Function
open scoped Manifold ContDiff
universe u v w
namespace Hironaka.HironakaG3UniverseCoordinateTransport
noncomputable section
open BlowupTowers NormalCrossings HironakaG3UniverseChartTransport

/-- Conversely, transported coordinate witnesses descend through the same homeomorphism. -/
theorem transported_coordinate_family_reverse {n : ℕ} {X : Type u} {Y : Type v} {ι : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) X]
    (e : X ≃ₜ Y) (A : ι → Set X) (S : ι → Finset (Fin n)) (y : Y)
    (h : letI : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
      IsCoordinateFamilyAt n (fun i => e.symm ⁻¹' A i) S y) :
    IsCoordinateFamilyAt n A S (e.symm y) := by
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
  rw [← hpoint]
  rcases h with ⟨Φ,hsrc,hzero,hflat⟩
  refine ⟨Φ, ?_, hzero, ?_⟩
  · simpa only [htarget] using hsrc
  · intro i hi z hz hzΦ
    have hz' : e z ∈ (chartAt (ComplexModel n) y).source := by
      change e z ∈ e '' (chartAt (ComplexModel n) (e.symm y)).source
      exact ⟨z,hz,rfl⟩
    have happly : (chartAt (ComplexModel n) y) (e z) =
        (chartAt (ComplexModel n) (e.symm y)) z := by
      change ((chartAt (ComplexModel n) (e.symm y)).lift_openEmbedding e.isOpenEmbedding) (e z) = _
      exact OpenPartialHomeomorph.lift_openEmbedding_apply _ _
    have hh := hflat i hi hz' (by simpa only [happly] using hzΦ)
    simpa only [mem_preimage, e.symm_apply_apply, happly] using hh

/-- Regularity is the one-member coordinate-family condition. -/
theorem regularAtDim_iff_coordinate {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    (A : Set X) (x : X) (d : ℕ) :
    RegularAtDim (n := n) A x d ↔ d ≤ n ∧ x ∈ A ∧
      IsCoordinateFamilyAt n (fun _ : Unit => A)
        (fun _ => Finset.univ.filter (fun j : Fin n => d ≤ j.val)) x := by
  constructor
  · rintro ⟨hd,hx,Φ,hsrc,hzero,hflat⟩
    refine ⟨hd,hx,Φ,hsrc,hzero,?_⟩
    intro i _ y hy hyΦ
    simpa only [coordSubspace_eq_complexCoordinatePlane] using hflat hy hyΦ
  · rintro ⟨hd,hx,Φ,hsrc,hzero,hflat⟩
    refine ⟨hd,hx,Φ,hsrc,hzero,?_⟩
    intro y hy hyΦ
    simpa only [coordSubspace_eq_complexCoordinatePlane] using hflat () hx hy hyΦ

/-- A homeomorphism and its transported complex atlas preserve regularity in both directions. -/
theorem transported_regularAtDim_iff {n : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] (e : X ≃ₜ Y) (A : Set X) (y : Y) (d : ℕ) :
    letI : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
    letI : IsComplexManifold n Y := transported_complex_manifold e
    RegularAtDim (n := n) (e.symm ⁻¹' A) y d ↔ RegularAtDim (n := n) A (e.symm y) d := by
  letI : ChartedSpace (ComplexModel n) Y := transportedChartedSpace e
  letI : IsComplexManifold n Y := transported_complex_manifold e
  rw [regularAtDim_iff_coordinate,regularAtDim_iff_coordinate]
  constructor
  · rintro ⟨hd,hy,hcoord⟩
    exact ⟨hd,hy,transported_coordinate_family_reverse e (fun _ : Unit => A) _ y hcoord⟩
  · rintro ⟨hd,hy,hcoord⟩
    exact ⟨hd,hy,transported_coordinate_family e (fun _ : Unit => A) _ y hcoord⟩

end
end Hironaka.HironakaG3UniverseCoordinateTransport
