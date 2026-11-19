import Hironaka.Resolution.HironakaG8CentredPointBlowupChart
import Hironaka.Resolution.HironakaG8StrictTransformAtlasSquare
import Hironaka.Resolution.HironakaG8OddCuspGeometricSource
import Hironaka.Resolution.HironakaG8FirstFootprintOrder
import Hironaka.Resolution.HironakaG8OddCuspMonomialStrict

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8CuspPointTower

open Hironaka.BlowupSequences BlowupTowers BlowupMonomialCharts
  HironakaG8CentredPointBlowupChart HironakaG8StrictTransformAtlasSquare HironakaBaseChange
  HironakaEmbeddedAnalytic HironakaG8OddCuspVanishingStalk HironakaG8OddCuspGeometricSource
  HironakaResolutionSpaceLocal HironakaSmoothSubmersionOriginalGlobalFinite
  HironakaOriginalCanonicalDimensionList HironakaG8OddCuspMonomialStrict HironakaStageCenters
  HironakaG8FirstFootprintOrder HironakaG8OccupiedSlotComparison

noncomputable section

abbrev CuspAmbient : CMfd.{0} 3 := CMfd.of (n := 3) (ComplexModel 3)

private theorem atlas_singularity {X : CMfd.{0} 3}
    (e : OpenPartialHomeomorph X (ComplexModel 3))
    (he : e ∈ atlas (ComplexModel 3) X) {x : X} (hx : x ∈ e.source)
    (W : Set X) (A : Set (ComplexModel 3))
    (hA : ∀ y ∈ e.source, y ∈ W ↔ e y ∈ A)
    (hs : e x ∈ singularSet (n := 3) A) : x ∈ singularSet (n := 3) W := by
  let U : Opens X := ⟨e.source,e.open_source⟩
  let eu (u : U) := e u.val
  obtain ⟨V,Φ,hΦ⟩ := atlas_open_holo_embedding e he
  let z : U := ⟨x,hx⟩
  have hEq : (Subtype.val : U → X) ⁻¹' W = Φ ⁻¹' ((Subtype.val : V → ComplexModel 3) ⁻¹' A) :=
    Set.ext fun u => (hA u.val u.property).trans ((congrArg (· ∈ A) (hΦ u)).to_iff)
  have hSing := congrArg (singularSet (n := 3)) hEq
  have hSub := singularSet_preimage_eq (X := CMfd.of (n := 3) V)
    (Y := CMfd.of (n := 3) U) (b := (Φ : U → V)) (isSubmersion_biholomorphism (D := CMfd.of (n := 3) U) (C := CMfd.of (n := 3) V) Φ)
    ((Subtype.val : V → ComplexModel 3) ⁻¹' A)
  rw [singularSet_preimage_val,hSub,singularSet_preimage_val] at hSing
  have hz : z ∈ Φ ⁻¹' ((Subtype.val : V → ComplexModel 3) ⁻¹' singularSet (n := 3) A) := by
    change (Φ z).val ∈ singularSet (n := 3) A
    rwa [← hΦ z]
  exact (Set.ext_iff.mp hSing z).mpr hz

/-- One actual successor keeps the exact cusp chart and projects its next
axis point to the previous singleton centre. -/
theorem extend_cusp_point_tower {X Y : CMfd.{0} 3} (W : Set X)
    (P : BlowupTower X Y) (p : ℕ) (hOdd : Odd p) (hp : 2 < p)
    (e : OpenPartialHomeomorph Y (ComplexModel 3)) (he : e ∈ atlas (ComplexModel 3) Y)
    (x : Y) (hx : x ∈ e.source) (h0 : e x = 0)
    (hRead : ∀ y ∈ e.source, y ∈ strictTransform 3 P.proj W ↔ e y ∈ embeddedCuspSet p) :
    ∃ (Z : CMfd.{0} 3) (π : Z → Y) (hπ : IsBlowupAlong 3 {x} π)
      (f : OpenPartialHomeomorph Z (ComplexModel 3)) (z : Z),
      f ∈ atlas (ComplexModel 3) Z ∧ z ∈ f.source ∧ f z = 0 ∧ π z = x ∧
      {x} ⊆ singularSet (n := 3) (strictTransform 3 P.proj W) ∧
      ∀ y ∈ f.source, y ∈ strictTransform 3 (P.step {x} π hπ).proj W ↔
        f y ∈ embeddedCuspSet (p-2) := by
  obtain ⟨f,z,hf,hz,hzf,hzx,hπ,hMap⟩ :=
    exists_centred_point_blowup_chart (n := 2) e he x hx h0 (0 : Fin 3)
  refine ⟨_,_,hπ,f,z,hf,hz,hzf,hzx,singleton_subset_iff.mpr ?_,?_⟩
  · exact atlas_singularity e he hx _ _ hRead (by rw [h0]; exact embedded_odd_cusp_singular_at_zero p hOdd hp)
  · intro y hy
    rw [BlowupTower.proj_step, StrictTransformComposition.strictTransform_comp
      P.contMDiff_proj hπ.contMDiff]
    have h := strict_transform_on_atlas_square _ hπ.contMDiff _ (contDiff_monomial 0 (0 : Fin 3)).contMDiff
      e he f hf hMap _ _ hRead y hy
    rwa [strictTransform_monomial_cusp p hp] at h

/-- Three genuine successive point blowups have intrinsically singular
centres, all with the same exact original footprint, and the final axis
chart reads the smooth-exponent cusp. -/
theorem exists_three_singular_cusp_point_blowups :
    ∃ (Z : CMfd.{0} 3) (T : BlowupTower CuspAmbient Z),
      T.length = 3 ∧
      StageCentres (fun P C => C ⊆ singularSet (n := 3)
        (strictTransform 3 P.proj (embeddedCuspSet 7))) T ∧
      (∀ i < 3, slotFootprint T i = ({0} : Set CuspAmbient)) ∧
      ∃ (e : OpenPartialHomeomorph Z (ComplexModel 3)) (z : Z),
        e ∈ atlas (ComplexModel 3) Z ∧ z ∈ e.source ∧ e z = 0 ∧
        T.proj z = 0 ∧
        ∀ y ∈ e.source, y ∈ strictTransform 3 T.proj (embeddedCuspSet 7) ↔
          e y ∈ embeddedCuspSet 1 := by
  let e := chartAt (ComplexModel 3) (0 : CuspAmbient)
  have he : e = OpenPartialHomeomorph.refl (ComplexModel 3) := chartAt_self_eq
  have hRead : ∀ y ∈ e.source,
      y ∈ strictTransform 3 (id : CuspAmbient → CuspAmbient) (embeddedCuspSet 7) ↔
        e y ∈ embeddedCuspSet 7 := by
    rw [he, strictTransform, exceptionalLocus_id, sdiff_empty, preimage_id,
      (embedded_cusp_isAnalytic 7).isClosed.closure_eq]
    intro y _
    rfl
  have hStart : (0 : CuspAmbient) ∈ e.source := mem_chart_source _ _
  have hZero : e (0 : CuspAmbient) = 0 := by rw [he]; rfl
  let T₀ : BlowupTower CuspAmbient CuspAmbient := .refl
  obtain ⟨Y₁,π₁,H₁,e₁,z₁,ha₁,hs₁,hz₁,he₁,hS₁,hR₁⟩ :=
    extend_cusp_point_tower (X := CuspAmbient) (Y := CuspAmbient) (embeddedCuspSet 7) T₀ 7 (by decide) (by decide) e
      (chart_mem_atlas _ _) 0 hStart hZero (by simpa only [T₀, BlowupTower.proj_refl] using hRead)
  let T₁ := T₀.step {0} π₁ H₁
  obtain ⟨Y₂,π₂,H₂,e₂,z₂,ha₂,hs₂,hz₂,he₂,hS₂,hR₂⟩ :=
    extend_cusp_point_tower (embeddedCuspSet 7) T₁ 5 (by decide) (by decide) e₁
      ha₁ z₁ hs₁ hz₁ hR₁
  let T₂ := T₁.step {z₁} π₂ H₂
  obtain ⟨Y₃,π₃,H₃,e₃,z₃,ha₃,hs₃,hz₃,he₃,hS₃,hR₃⟩ :=
    extend_cusp_point_tower (embeddedCuspSet 7) T₂ 3 (by decide) (by decide) e₂
      ha₂ z₂ hs₂ hz₂ hR₂
  let T₃ := T₂.step {z₂} π₃ H₃
  refine ⟨Y₃,T₃,rfl,⟨⟨⟨trivial,hS₁⟩,hS₂⟩,hS₃⟩,?_,e₃,z₃,ha₃,hs₃,hz₃,?_,hR₃⟩
  · intro i hi
    interval_cases i <;> simp [T₃,T₂,T₁,T₀,slotFootprint,BlowupTower.proj_step,he₁,he₂]
  · simp [T₃,T₂,T₁,T₀,BlowupTower.proj_step,he₁,he₂,he₃]

end
end Hironaka.HironakaG8CuspPointTower
