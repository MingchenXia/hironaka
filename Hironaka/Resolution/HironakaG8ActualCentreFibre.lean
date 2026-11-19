import Hironaka.Resolution.HironakaG8GeneralCentreFibreInclusion
import Hironaka.Blowup.BlowupBiholomorphismLift
import Hironaka.Blowup.BlowupSpaceUniversal
/-! # Fixed exceptional fibres of actual blowups -/
set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG8ActualCentreFibre
noncomputable section
open Hironaka.BlowupSequences BlowupConstruction BlowupStrictSubmanifold
  BlowupSpaceTangent HironakaG8GeneralCentreFibreInclusion

/-- For an arbitrary actual blowup along a smooth nowhere-dense centre, the
whole exceptional fibre of the strict carrier lies in the strict boundary
exactly when the carrier tangent space lies in the boundary tangent space.
Both original submanifolds must contain the centre. -/
theorem strict_fibre_subset_iff_tangentSpace_le
    {n : ℕ} {X Y : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] {C P H : Set X} {π : Y → X}
    (hC : IsClosedSubmanifold n C) (hCint : interior C = ∅)
    (hπ : IsBlowupAlong n C π)
    (hP : IsClosedSubmanifold n P) (hH : IsClosedSubmanifold n H)
    (hCP : C ⊆ P) (hCH : C ⊆ H) {x : X} (hxC : x ∈ C) :
    (∀ z : Y, π z = x → z ∈ geoStrictTransform π C P → z ∈ geoStrictTransform π C H) ↔
      tangentSpace n P x ≤ tangentSpace n H x := by
  let : Fact (IsClosedSubmanifold n C) := ⟨hC⟩
  obtain ⟨e, f, he, hf, hπe, _, hfe, hef⟩ :=
    BlowupUniqueness.exists_biholomorphism_over hπ (isBlowupAlong_blowupProj hCint)
  let χ : Y ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ BlowupSpace n C :=
    ⟨⟨e, f, congrFun hfe, congrFun hef⟩, he, hf⟩
  have hπχ : blowupProj n C ∘ χ = π := hπe
  have hstrict (W : Set X) : geoStrictTransform π C W =
      χ ⁻¹' geoStrictTransform (blowupProj n C) C W := by
    rw [← hπχ]
    exact BlowupBiholomorphismLift.geoStrictTransform_comp_diffeo χ _ C W
  constructor
  · intro hF
    apply (HironakaG8GeneralCentreFibreInclusion.strict_fibre_subset_iff_tangentSpace_le
      hP hH hCP hCH hxC).mp
    intro p hpbase hpP
    have hπz : π (χ.symm p) = x := by
      have hh := congrFun hπχ (χ.symm p)
      have hh' : p.base = π (χ.symm p) := by
        change (blowupProj n C p) = π (χ.symm p)
        simpa only [Function.comp_apply, χ.apply_symm_apply] using hh
      exact hh'.symm.trans hpbase
    have hzP : χ.symm p ∈ geoStrictTransform π C P := by
      rw [hstrict]
      simpa only [mem_preimage, χ.apply_symm_apply] using hpP
    have hzH := hF (χ.symm p) hπz hzP
    rw [hstrict] at hzH
    simpa only [mem_preimage, χ.apply_symm_apply] using hzH
  · intro htan z hz hPz
    have hzbase : (χ z).base = x := by
      have hh := congrFun hπχ z
      exact hh.trans hz
    have hpP : χ z ∈ geoStrictTransform (blowupProj n C) C P := by
      rw [hstrict] at hPz
      exact hPz
    have hpH := (HironakaG8GeneralCentreFibreInclusion.strict_fibre_subset_iff_tangentSpace_le
      hP hH hCP hCH hxC).mpr htan (χ z) hzbase hpP
    rw [hstrict]
    exact hpH

end
end Hironaka.HironakaG8ActualCentreFibre
