import Hironaka.Resolution.HironakaG3REmbeddedNC

/-! # G3 under target (A): the final statement with global boundaries

Lane G3 (run 0080, round 4).  Blueprint: `hironaka-g3-r-final-global.tex`.

**`g3_final_global`**: on every complex manifold `X` (not necessarily compact), (a) every marked ideal of the domain has a
glued canonical resolution, unique up to unique biholomorphism over `X`, which is a single finite canonical resolution over
every open set contained in a compact set, whose boundary is a locally finite indexed simple normal crossings divisor, and
which principalizes `𝔞` when `M = (X, X, E, 𝔞, 1)`; (b) every closed irreducible analytic `V` with `dim V < n` has a glued
embedded resolution, unique up to unique biholomorphism over `X`, a single stopped canonical prefix over every open set
contained in a compact set, with `Exc P = P⁻¹ V_sing` a locally finite indexed simple normal crossings divisor having only
normal crossings with the strict transform of `V`, `P` an isomorphism over `X ∖ V_sing`, and the strict transform a closed
submanifold of dimension `dim V`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace Function
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG3RFinalGlobal

noncomputable section

open Hironaka.NonKahlerLocus Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  MarkedIdeals NormalCrossings HironakaG3RGluedUniqueness HironakaG3RTowerClass HironakaG3RGluedEmbedded
open ResolutionInvariantSpec (IsInvDomain)
open HironakaActualIndexedBoundaryContinuation (HasNormalCrossingsWithBoundary)
open HironakaActualLocallyFiniteBoundary (IsLocallyFiniteSNCDivisor)

variable {n : ℕ}

/-- **The final G3 theorem under target (A), with global boundaries.** -/
theorem g3_final_global (X : CMfd.{u} n) :
    (∀ M : MarkedIdeal n X, IsInvDomain n M →
      ∃ (X' : CMfd.{u} n) (P : X' → X), IsGluedCanonicalResolution M X' P ∧
        (∀ (X'' : CMfd.{u} n) (P' : X'' → X), IsGluedCanonicalResolution M X'' P' →
          ∃! Ψ : X'' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X', ∀ z, P (Ψ z) = P' z) ∧
        (∀ (U : Opens X) (K : Set X), IsCompact K → (U : Set X) ⊆ K → ∃ c : GluedChart M X' P, c.U = U) ∧
        (∃ (ι : Type u) (D : ι → Set X'), IsLocallyFiniteSNCDivisor n D ∧ (∀ i, (D i).Nonempty) ∧
          (⋃ i, D i) = HironakaG3RGluedBoundary.gluedBoundary M X' P) ∧
        (M.N = univ → M.d = 1 →
          (GermIdeal.pullback (m := n) P M.ideal).IsInvertible ∧
            (GermIdeal.pullback (m := n) P M.ideal).zeroLocus = P ⁻¹' M.ideal.zeroLocus ∧
            IsIsomorphismOver n P M.ideal.zeroLocusᶜ)) ∧
    (∀ V : ClosedIrreducibleAnalyticSubvariety n X, V.dim < n →
      ∃ (X' : CMfd.{u} n) (P : X' → X), IsGluedEmbeddedResolution V X' P ∧
        (∀ (X'' : CMfd.{u} n) (P' : X'' → X), IsGluedEmbeddedResolution V X'' P' →
          ∃! Ψ : X'' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X', ∀ z, P (Ψ z) = P' z) ∧
        (∀ (U : Opens X) (K : Set X), IsCompact K → (U : Set X) ⊆ K →
          ∃ c : TowerChart (embeddedClass V) X' P, c.U = U) ∧
        exceptionalLocus n P = P ⁻¹' singularLocus V ∧
        IsIsomorphismOver n P (singularLocus V)ᶜ ∧
        IsClosedSubmanifold n (strictTransform n P V.carrier) ∧
        (∀ z ∈ strictTransform n P V.carrier, RegularAtDim (n := n) (strictTransform n P V.carrier) z V.dim) ∧
        ∃ (ι : Type u) (D : ι → Set X'), IsLocallyFiniteSNCDivisor n D ∧ (∀ i, (D i).Nonempty) ∧
          (⋃ i, D i) = exceptionalLocus n P ∧ HasNormalCrossingsWithBoundary (strictTransform n P V.carrier) D) := by
  refine ⟨fun M hM => ?_, fun V hV => ?_⟩
  · obtain ⟨X', P, h, huniq⟩ := existsUnique_gluedCanonicalResolution M hM
    exact ⟨X', P, h, huniq, fun U K hK hUK => HironakaG3RChartOfMember.exists_gluedChart_of_subset_isCompact hM h U hK hUK,
      HironakaG3RGlobalSNC.exists_isLocallyFiniteSNCDivisor_gluedBoundary hM h,
      fun hN hd => HironakaG3RFinal.principalization_of_isGluedCanonicalResolution hM h hN hd⟩
  · obtain ⟨X', P, h, huniq⟩ := existsUnique_gluedEmbeddedResolution V hV
    exact ⟨X', P, h, huniq,
      fun U K hK hUK => HironakaG3RChartOfMember.exists_embeddedChart_of_subset_isCompact hV h U hK hUK,
      exceptionalLocus_eq hV h, isIsomorphismOver hV h, strictTransform_isClosedSubmanifold hV h,
      regularAtDim_strictTransform hV h, HironakaG3REmbeddedNC.exists_globalBoundary_embeddedResolution hV h⟩

end

end Hironaka.HironakaG3RFinalGlobal
