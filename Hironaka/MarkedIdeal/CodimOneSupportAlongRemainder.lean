/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.CodimOneSupportAlong

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.CodimOneSupportAlong
open Hironaka HolomorphicIdealSheaves BlowupSequences GermIdealOrder RelativePrincipalizationSpan MarkedIdeals CodimOneSupport TangentDirectionAlong GiraudAlong HomogenizedIdealAlong AnalyticDimensionBasics RegularPointDimension DerivativeIdealAlongCoherent CodimOneCentreAlong TransformOffCentre DerivativeIdealAlong
noncomputable section
variable {n : ℕ}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {N : Set M} {𝔞 : GermIdeal n M} {μ : ℕ}

/-- **The codimension-one part along `N` is open in the support.** -/
theorem exists_isOpen_cosupport_inter_eq_codimOnePartAlong :
    ∃ O : Set M, IsOpen O ∧ cosupport n N 𝔞 μ ∩ O = codimOnePartAlong N 𝔞 μ := by
  refine ⟨interior {y | y ∈ cosupport n N 𝔞 μ → y ∈ codimOnePartAlong N 𝔞 μ}, isOpen_interior,
    Subset.antisymm (fun y hy => interior_subset hy.2 hy.1) fun x hx => ⟨codimOnePartAlong_subset hx,
      mem_interior_iff_mem_nhds.mpr ?_⟩⟩
  filter_upwards [eventually_mem_codimOnePartAlong_iff hx] with y h using h.mpr

/-- **The rest of the support along `N` is closed.** -/
theorem isClosed_cosupport_diff_codimOnePartAlong (h𝔞 : 𝔞.IsCoherent)
    (hN : IsClosedSubmanifold n N) :
    IsClosed (cosupport n N 𝔞 μ \ codimOnePartAlong N 𝔞 μ) := by
  obtain ⟨O, hO, hSO⟩ :=
    exists_isOpen_cosupport_inter_eq_codimOnePartAlong (N := N) (𝔞 := 𝔞) (μ := μ)
  have h : cosupport n N 𝔞 μ \ codimOnePartAlong N 𝔞 μ = cosupport n N 𝔞 μ ∩ Oᶜ := by
    rw [← hSO]
    ext y
    simp only [Set.mem_sdiff, mem_inter_iff, mem_compl_iff, not_and]
    exact ⟨fun h => ⟨h.1, h.2 h.1⟩, fun h => ⟨h.1, fun _ => h.2⟩⟩
  rw [h]
  exact (isClosed_cosupport_along h𝔞 hN μ).inter hO.isClosed_compl

/-- **The rest of the support along `N` has codimension at least two in `N`**: at a point where
`N` has dimension `k + 1`, every regular point of `cosupp(𝔞|_N, μ) \ R` has dimension `< k`. -/
theorem lt_of_regularAtDim_cosupport_diff_codimOnePartAlong (h𝔞 : 𝔞.IsCoherent)
    (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ) (hmax : IsMaximalOrderAlong N 𝔞 μ) {y : M}
    {j k : ℕ} (hNk : RegularAtDim (n := n) N y (k + 1))
    (hy : RegularAtDim (n := n) (cosupport n N 𝔞 μ \ codimOnePartAlong N 𝔞 μ) y j) : j < k := by
  have hhol : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  have hyS : y ∈ cosupport n N 𝔞 μ := hy.2.1.1
  have hyR : y ∉ codimOnePartAlong N 𝔞 μ := hy.2.1.2
  have hSy : RegularAtDim (n := n) (cosupport n N 𝔞 μ) y j := by
    refine regularAtDim_of_inter_eq (isClosed_codimOnePartAlong h𝔞 hN hμ hmax).isOpen_compl hyR ?_ hy
    ext z
    simp only [Set.mem_sdiff, mem_inter_iff, mem_compl_iff]
    tauto
  obtain ⟨U, u, hyU, hu⟩ := exists_isTangentDirectionAlong_of_isMaximalOrderAlong h𝔞 hN hμ hmax hyS
  have hux : u y = 0 := hu.cosupport_inter_subset hhol hμ ⟨hyS, hyU⟩
  obtain ⟨k', hNk', hH⟩ := hu.regularAtDim_contact hhol hN ⟨⟨hyS.1, hux⟩, hyU⟩
  have hkk : k' = k + 1 := eq_of_regularAtDim hNk' hNk
  rw [hkk, Nat.add_sub_cancel] at hH
  have hSU : RegularAtDim (n := n) (cosupport n N 𝔞 μ ∩ U) y j :=
    regularAtDim_of_inter_eq hu.isOpen hyU (by rw [inter_assoc, inter_self]) hSy
  have hle : j ≤ k := BlowupStrictSubmanifold.le_of_regularAtDim_subset hSU hH
    fun z hz => ⟨⟨hz.1.1, hu.cosupport_inter_subset hhol hμ hz⟩, hz.2⟩
  refine lt_of_le_of_ne hle fun hj => hyR ⟨k, hNk, ?_⟩
  rw [← hj]
  exact hSy

end
end Hironaka.CodimOneSupportAlong
