import Hironaka.Resolution.HironakaG4UnitTraceDerivative
import Hironaka.Resolution.HironakaG8CaseTCoordinateReplacement

/-! Straighten a unit trace in its free coordinate without changing the carrier. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG4UnitCoordinateReplacement
noncomputable section
open Hironaka.BlowupSequences NormalCrossings HironakaG8CaseTCoordinateReplacement
  HironakaG4UnitTraceDerivative

variable {n : ℕ}

/-- The unit trace replaces its free coordinate and preserves the carrier
plane, while every other coordinate remains unchanged. -/
theorem exists_unit_trace_coordinate_replacement
    {f a d : ComplexModel n → ℂ} {U : Set (ComplexModel n)}
    (hU : IsOpen U) (h0U : (0 : ComplexModel n) ∈ U)
    (hfU : DifferentiableOn ℂ f U) (hf0 : f 0 = 0)
    (S : Finset (Fin n)) (t : Fin n) (ht : t ∉ S)
    (ha : DifferentiableAt ℂ a 0) (hd : DifferentiableAt ℂ d 0)
    (ha0 : a 0 ≠ 0) (hd0 : d 0 ≠ 0)
    (htrace : ∀ᶠ z in 𝓝 (0 : ComplexModel n), z ∈ coordSubspace S → f z = a z * (d z * z t)) :
    ∃ Ψ : LocalHolomorphicEquivAt (n := n) 0,
      Ψ.source ⊆ U ∧ Ψ.toFun 0 = 0 ∧
      (∀ z, Ψ.toFun z t = f z) ∧
      (∀ z j, j ≠ t → Ψ.toFun z j = z j) ∧
      ∀ z, z ∈ coordSubspace S ↔ Ψ.toFun z ∈ coordSubspace S := by
  have hf : DifferentiableAt ℂ f 0 := (hfU 0 h0U).differentiableAt (hU.mem_nhds h0U)
  have htderiv := free_partial_ne_zero_of_unit_trace S t ht hf ha hd ha0 hd0 htrace
  obtain ⟨Ψ,hsrc,hzero,htcoord,hother⟩ := exists_coordinate_replacement_at hU h0U hfU hf0 t htderiv
  refine ⟨Ψ,hsrc,hzero,htcoord,hother,?_⟩
  intro z
  constructor <;> intro hz j hj
  · have hjt : j ≠ t := fun h => ht (h ▸ hj)
    rw [hother z j hjt]
    exact hz j hj
  · have hjt : j ≠ t := fun h => ht (h ▸ hj)
    have hh := hz j hj
    rwa [hother z j hjt] at hh

end
end Hironaka.HironakaG4UnitCoordinateReplacement
