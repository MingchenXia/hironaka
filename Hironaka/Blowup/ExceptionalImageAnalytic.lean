import Hironaka.Blowup.ExceptionalImageCodimension
import Hironaka.Analytic.PureDimension

set_option autoImplicit false

/-!
# The image of the exceptional locus of a blowup is analytic

Source: Griffiths--Harris, Ch. 1 §4; CT22, Section 4; blueprint
`ana:blowup-exceptional-image`.

Let `π : Z → M` be the blowup of a compact complex manifold along a nowhere dense closed
submanifold `C`.  Then `π (Exc π)` is the union of the connected components of `C` of
codimension at least two, hence an analytic subset of `M`.

**PROVED** (sorry-free).  Write `T = π (Exc π)`; it is closed (`ExceptionalFibres`).  Off `T`
the constant equation `1 = 0` presents `T`.  At `y = π z₀ ∈ T`, flatten `C` near `y` onto
`ℂᵏ × 0` by `Φ ∘ e` (`C` is a closed submanifold).  By
`ExceptionalImageCodimension` (monomial charts of the blowup):

* `k < n`, since a monomial chart index `j` satisfies `k ≤ j < n`;
* `k + 1 = n` is impossible: then no point over the flattening domain is exceptional, but
  `z₀` is;
* so `k + 2 ≤ n`, and then every point of `Z` over `C ∩ flatDomain Φ` is exceptional.  As `π`
  is surjective (`M` compact) and `T ⊆ C`, `T` agrees with `C` on `flatDomain Φ`, and the flat
  coordinates `(Φ)ᵢ`, `i ≥ k`, on `Φ.source` present `T` at `y`.

`Hironaka.StrictTransformSubvariety` uses it.
-/

open Set

universe u

namespace Hironaka.ExceptionalImageAnalytic

open Hironaka.BlowupSequences BlowupFlatCoordinates ExceptionalImageCodimension

noncomputable section

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

/-- **Image of the exceptional locus of a blowup.**  The image of the exceptional locus of a
blowup of a compact complex manifold along a smooth centre is an analytic subset. -/
theorem isComplexAnalyticSubset_image_exceptionalLocus [CompactSpace M] {C : Set M}
    {π : Z → M} (hπ : IsBlowupAlong n C π) :
    IsComplexAnalyticSubset (n := n) (π '' exceptionalLocus n π) := by
  classical
  have hT : IsClosed (π '' exceptionalLocus n π) :=
    ExceptionalFibres.isClosed_image_exceptionalLocus hπ
  have hsurj := StrictTransformComposition.surjective_of_isBlowupAlong hπ
  intro x
  by_cases hx : x ∈ π '' exceptionalLocus n π
  swap
  · exact PureDimension.nonempty_presentation_of_not_mem hT Subset.rfl hx
  have hxC : x ∈ C := ExceptionalFibres.image_exceptionalLocus_subset hπ hx
  obtain ⟨z₀, hz₀, rfl⟩ := hx
  obtain ⟨k, -, -, Φ, hΦt, -, hΦ⟩ := hπ.1.2 _ hxC
  have hz₀Φ : π z₀ ∈ flatDomain Φ := mem_flatDomain_self Φ
  have hkn : k < n := lt_of_mem_flatDomain hπ hΦt hΦ hz₀Φ
  have hk2 : k + 2 ≤ n := by
    by_contra hk
    exact not_mem_exceptionalLocus hπ hΦt hΦ (by omega) hz₀Φ hz₀
  have hTC : ∀ y ∈ flatDomain Φ, y ∈ π '' exceptionalLocus n π ↔ y ∈ C := by
    intro y hy
    refine ⟨fun h => ExceptionalFibres.image_exceptionalLocus_subset hπ h, fun hyC => ?_⟩
    obtain ⟨z, rfl⟩ := hsurj y
    exact ⟨z, mem_exceptionalLocus_of_mem hπ hΦt hΦ hk2 hyC hy, rfl⟩
  refine ⟨{ generatorCount := n
            generator := fun i w => if k ≤ i.1 then Φ.toFun w i else 0
            coordinateNeighborhood := Φ.source
            isOpen_coordinateNeighborhood := Φ.isOpen_source
            center_mem_coordinateNeighborhood := Φ.center_mem_source
            coordinateNeighborhood_subset_target := hΦt
            generator_holomorphic := ?_
            zeroLocus := ?_ }⟩
  · intro i
    by_cases hi : k ≤ i.1
    · simp only [hi, if_true]
      exact (EuclideanSpace.proj (𝕜 := ℂ) i).differentiable.comp_differentiableOn
        Φ.toFun_holomorphic
    · simp only [hi, if_false]
      exact differentiableOn_const 0
  · intro y hy hyU
    rw [hTC y ⟨hy, hyU⟩, hΦ hy hyU]
    simp only [complexCoordinatePlane, mem_ofPred_eq]
    refine forall_congr' fun i => ?_
    by_cases hi : k ≤ i.1 <;> simp [hi]

end

end Hironaka.ExceptionalImageAnalytic
