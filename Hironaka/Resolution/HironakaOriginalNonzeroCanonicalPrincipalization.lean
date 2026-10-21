/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCanonicalPrincipalizationSpecializations

/-!
# Literal original nonzero-ideal connected canonical principalization

The lower original principalization form uses literal noncontainment in the
whole ambient vanishing ideal. The genuine connected coherent identity principle
supplies nonzero-along before the SAME canonical tower and full source family.
Blueprint: `hironaka-original-nonzero-canonical-principalization-extension.tex`.
-/
set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalNonzeroCanonicalPrincipalization
noncomputable section
open Hironaka.HolomorphicIdealSheaves BlowupTowers NormalCrossings DivisorExponentAlong
  HironakaOriginalCanonicalPrincipalizationSpecializations
variable {n : ℕ} {X : CMfd.{u} n}

/-- The actual original literal nonzero condition suffices on a connected ambient manifold. -/
theorem nonzeroAlong_of_not_le [ConnectedSpace X]
    (I : GermIdeal n X) (hI : I.IsCoherent)
    (hres : ¬ I.Le (vanishingIdeal (n := n) (univ : Set X))) :
    ∀ x,IsNonzeroAlongAt univ I x := fun x =>
  FactorizationDomain.isNonzeroAlongAt_of_not_le
    FactorizationDomain.isClosedConnectedSubmanifold_univ hI hres x (mem_univ x)

/-- Literal noncontainment retains the SAME actual canonical target and all smooth sources. -/
theorem canonical_principalization_of_not_le [ConnectedSpace X]
    (I : GermIdeal n X) (hI : I.IsCoherent)
    (hres : ¬ I.Le (vanishingIdeal (n := n) (univ : Set X)))
    (hZ : IsCompact I.zeroLocus) (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀) :
    CanonicalBoundaryPrincipalizationSpec I hI (nonzeroAlong_of_not_le I hI hres) hZ E₀ hE₀ :=
  canonical_spec_of_nonzeroAlong I hI (nonzeroAlong_of_not_le I hI hres) hZ E₀ hE₀

/-- Actual compact ambient nonzero-ideal data internally give compact cosupport. -/
theorem canonical_principalization_of_not_le_compactSpace [CompactSpace X] [ConnectedSpace X]
    (I : GermIdeal n X) (hI : I.IsCoherent)
    (hres : ¬ I.Le (vanishingIdeal (n := n) (univ : Set X)))
    (E₀ : List (Set X)) (hE₀ : IsSNCDivisor n E₀) :
    let hZ := (CodimOneSupport.isComplexAnalyticSubset_zeroLocus hI).isClosed.isCompact
    CanonicalBoundaryPrincipalizationSpec I hI (nonzeroAlong_of_not_le I hI hres) hZ E₀ hE₀ :=
  canonical_principalization_of_not_le I hI hres
    (CodimOneSupport.isComplexAnalyticSubset_zeroLocus hI).isClosed.isCompact E₀ hE₀

end
end Hironaka.HironakaOriginalNonzeroCanonicalPrincipalization
