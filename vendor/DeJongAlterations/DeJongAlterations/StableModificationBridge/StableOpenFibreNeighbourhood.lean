import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! The actual original proper bad-image complement supplies the whole base neighbourhood. -/

open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u

namespace DeJongAlterations.StableModificationBridge.StableOpenFibreNeighbourhood

/-- Actual opens covering the ORIGINAL closed points of a closed fibre internally contain
an entire ORIGINAL base neighbourhood; no stability-open or finite-subcover certificate. -/
theorem exists_base_open_of_closed_fibre_le {C V : Scheme.{u}} [CompactSpace C]
    (q : C ⟶ V) [UniversallyClosed q] (z : V) (hzc : IsClosed ({z} : Set V))
    (T : C.Opens) (hT : ∀ y : C, IsClosed ({y} : Set C) → q y = z → y ∈ T) :
    ∃ O : V.Opens, z ∈ O ∧ q ⁻¹ᵁ O ≤ T := by
  have hz : z ∉ q '' (T : Set C)ᶜ := by
    rintro ⟨x, hx, hqx⟩
    have hB : IsClosed ((T : Set C)ᶜ ∩ q ⁻¹' ({z} : Set V)) :=
      T.isOpen.isClosed_compl.inter (hzc.preimage q.continuous)
    obtain ⟨y, hy, hyc⟩ := hB.exists_closed_singleton ⟨x, hx, hqx⟩
    exact hy.1 (hT y hyc hy.2)
  let O : V.Opens := ⟨(q '' (T : Set C)ᶜ)ᶜ,
    (q.isClosedMap _ T.isOpen.isClosed_compl).isOpen_compl⟩
  refine ⟨O, hz, fun x hx => ?_⟩
  by_contra hxt
  exact hx ⟨x, hxt, rfl⟩

end DeJongAlterations.StableModificationBridge.StableOpenFibreNeighbourhood
