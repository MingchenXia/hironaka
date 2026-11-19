import Hironaka.Analytic.UniformLocalBergmanPatch

set_option autoImplicit false

/-!
# Finite atlases of uniform local Bergman patches

Each patch in this atlas retains the weighted Bergman unit-ball witness made
available by `UniformWeightedL2Generators`: its generators, common centre and
radius, and uniform domination estimate.  Compactness is used only to pass
from the pointwise construction to finitely many such concrete patches.
-/

open Set

namespace Hironaka.QuasiEquisingularBergmanAtlas



noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A finite cover by local Bergman patches which retain the universal weighted
unit-ball domination data needed for arbitrary local multiplier-ideal tests. -/
structure FiniteUniformLocalBergmanAtlas (θ : SmoothRealForm n M 2)
    (u : M → EReal) (m : ℕ) where
  count : ℕ
  patch : Fin count → UniformLocalBergmanPatch θ u m
  covers : ∀ x : M, ∃ i, x ∈ (patch i).patch.source

/-- Compactness turns the pointwise uniform local Bergman construction into a
finite atlas without discarding any patch-level weighted unit-ball witness. -/
theorem nonempty_finiteUniformLocalBergmanAtlas [CompactSpace M]
    {θ : SmoothRealForm n M 2} {u : M → EReal}
    (hu : IsThetaPshPotential θ u) (m : ℕ) (hm : 0 < m) :
    Nonempty (FiniteUniformLocalBergmanAtlas θ u m) := by
  classical
  have hcover : (univ : Set M) ⊆ ⋃ D : UniformLocalBergmanPatch θ u m,
      (D.patch.source : Set M) := by
    intro x _
    obtain ⟨D, hx⟩ := exists_uniformLocalBergmanPatch_containing hu m hm x
    exact mem_iUnion.mpr ⟨D, hx⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun D : UniformLocalBergmanPatch θ u m => (D.patch.source : Set M))
    (fun D => D.patch.source.isOpen) hcover
  refine ⟨{
    count := s.card
    patch := fun i => (s.equivFin.symm i).val
    covers := ?_ }⟩
  intro x
  obtain ⟨D, hDx⟩ := mem_iUnion.mp (hs (mem_univ x))
  obtain ⟨hD, hx⟩ := mem_iUnion.mp hDx
  refine ⟨s.equivFin ⟨D, hD⟩, ?_⟩
  change x ∈ (((s.equivFin.symm (s.equivFin ⟨D, hD⟩)).val).patch.source : Set M)
  rw [Equiv.symm_apply_apply]
  exact hx

end

end Hironaka.QuasiEquisingularBergmanAtlas
