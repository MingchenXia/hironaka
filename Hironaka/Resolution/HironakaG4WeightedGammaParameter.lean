import Hironaka.Resolution.HironakaG4WeightedGammaSection

/-!
# The actual parameter type for weighted Gamma scalings

The weighted nonzero vectors form the parameter type, so every parameter
(not merely eventually) has nonzero coordinates and satisfies the weight
equation. The explicit section is continuous at the identity in the
subspace topology and realizes all free coordinates near it.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology
namespace Hironaka.HironakaG4WeightedGammaParameter
noncomputable section
open HironakaG4WeightedGammaSection

variable {n : ℕ}

def weightedScalings (s t : Fin n) (c : Fin n → ℕ) : Set (Fin n → ℂ) :=
  {a | (∀ i, a i ≠ 0) ∧ a s = a t * ∏ j, a j ^ c j}

def weightedIdentity (s t : Fin n) (c : Fin n → ℕ) : weightedScalings s t c :=
  ⟨1, by simp [weightedScalings]⟩

def weightedSection (s t : Fin n) (c : Fin n → ℕ) (hst : t ≠ s) (hcs : c s = 0)
    (b : Fin n → ℂ) : weightedScalings s t c :=
  ⟨gammaSection s t c b, gammaSection_spec s t c hst hcs b⟩

/-- The actual weighted parameter type and explicit section satisfy the
primitive filter and realization hypotheses of the toric history. -/
theorem weightedSection_partial_realization (s t : Fin n) (c : Fin n → ℕ)
    (S : Finset (Fin n)) (hs : s ∈ S) (hst : t ≠ s) (hcs : c s = 0) :
    Tendsto (Subtype.val : weightedScalings s t c → Fin n → ℂ) (𝓝 (weightedIdentity s t c)) (𝓝 1) ∧
    Tendsto (weightedSection s t c hst hcs) (𝓝 1) (𝓝 (weightedIdentity s t c)) ∧
    ∀ᶠ b in 𝓝 (1 : Fin n → ℂ), ∀ i ∉ S,
      (weightedSection s t c hst hcs b : Fin n → ℂ) i = b i := by
  obtain ⟨hlim, hrealize⟩ := gammaSection_partial_realization s t c S hs hst hcs
  refine ⟨continuous_subtype_val.continuousAt, ?_, ?_⟩
  · apply tendsto_subtype_rng.mpr
    exact (tendsto_nhdsWithin_iff.mp hlim).1
  · exact hrealize

end
end Hironaka.HironakaG4WeightedGammaParameter
