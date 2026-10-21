/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalLocalCanonicalIrreducibleFamily

/-! # All-dimensional original irreducible resolution on the SAME prescribed open
Blueprint: `hironaka-original-prescribed-local-irreducible-family-extension.tex`.
-/
set_option autoImplicit false
open Set TopologicalSpace
universe u
namespace Hironaka.HironakaOriginalPrescribedLocalIrreducibleFamily
noncomputable section
open Hironaka Hironaka.BlowupSequences BlowupTowers NormalCrossings
  HironakaOriginalLocalCanonicalIrreducibleFamily
variable {n : ℕ} {X : CMfd.{u} n}

/-- The original prescribed U is retained in BOTH actual dimension branches. -/
theorem exists_original_irreducible_canonical_family_of_subset_isCompact
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (U : Opens X) {K : Set X} (hK : IsCompact K) (hUK : (U : Set X) ⊆ K) :
    (V.dim<n ∧ HasExactIndependentLocalPureBoundaryResolution V.carrier
      V.irreducible_carrier.analytic V.dim [] isSNCDivisor_nil U ∧
      ((Subtype.val : U → X) ⁻¹' V.carrier) \ regularLocus (n := n)
        ((Subtype.val : U → X) ⁻¹' V.carrier) V.dim =
        (Subtype.val : U → X) ⁻¹' singularLocus V) ∨
    (V.dim=n ∧ FullDimensionLocalCanonicalFamily V U) := by
  rcases V.dim_le.lt_or_eq with hd | hd
  · exact Or.inl ⟨hd,local_irreducible_proper_family V hd U hK hUK⟩
  · exact Or.inr ⟨hd,full_dimension_local_canonical_family V hd U⟩

end
end Hironaka.HironakaOriginalPrescribedLocalIrreducibleFamily
