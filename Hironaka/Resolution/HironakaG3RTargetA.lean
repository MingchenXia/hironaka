import Hironaka.Resolution.HironakaG3RGluedBoundary

/-! # G3, target (A): the held part of the final statement

Lane G3 (run 0080, round 3).  Blueprint: `hironaka-g3-r-target-a.tex`.  Notes:
`work/hironaka-resume-20261111/G3/G3-TARGET-A.md` (sections 3 and 5).

Human decision I-1339 (option (A)): G3's global target is the glued terminal atlas.  This module packages what is proved of
it, for every marked ideal `M` of the domain of the canonical invariant on an arbitrary (noncompact) complex manifold `X`:

* **`exists_finite_charts_of_isCompact`**: every compact subset of `X` is covered by finitely many chart opens of a glued
  canonical resolution (over each of them `P` is a finite canonical resolution).
* **`g3_targetA`**: a glued canonical resolution `P : X' → X` exists (`exists_glued_canonical_resolution`); it is unique
  up to unique biholomorphism over `X` (`HironakaG3RGluedUniqueness`); compact sets are covered by finitely many charts;
  its boundary is a closed divisor with normal crossings: on every chart the union of the chart's simple normal crossings
  boundary, the chart boundaries having equal ordered nonempty traces on overlaps (`HironakaG3RGluedBoundary`).

NOT included (open): A-miss-3, the embedded resolution of a closed analytic subvariety on a glued space (stopped prefixes
glued); a global indexing of the boundary by smooth hypersurfaces.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace Function
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG3RTargetA

noncomputable section

attribute [local instance] Classical.propDecidable

open Hironaka.BlowupSequences BlowupTowers MarkedIdeals NormalCrossings
  HironakaG3RGluedUniqueness HironakaG3RGluedBoundary
open ResolutionInvariantSpec (IsInvDomain)

variable {n : ℕ} {X : CMfd.{u} n} {M : MarkedIdeal n X}

/-- **Every compact set is covered by finitely many charts** of a glued canonical resolution. -/
theorem exists_finite_charts_of_isCompact {X' : CMfd.{u} n} {P : X' → X} (h : IsGluedCanonicalResolution M X' P)
    {K : Set X} (hK : IsCompact K) : ∃ t : Finset (GluedChart M X' P), K ⊆ ⋃ c ∈ t, (c.U : Set X) := by
  refine hK.elim_finite_subcover (fun c : GluedChart M X' P => (c.U : Set X)) (fun c => c.U.isOpen) ?_
  intro x _
  obtain ⟨c, hc⟩ := h.exists_chart x
  exact mem_iUnion.mpr ⟨c, hc⟩

/-- **Target (A) of G3, held part.**  For a marked ideal `M` of the domain of the canonical invariant on a complex manifold
`X`: there is a glued canonical resolution `P : X' → X` (holomorphic, proper, surjective, locally a finite canonical
resolution); every glued canonical resolution of `M` is identified with it by a unique biholomorphism over `X`; every
compact subset of `X` is covered by finitely many charts; and its boundary is closed, on every chart the union of the
chart's simple normal crossings boundary, the chart boundaries having the same ordered nonempty traces on overlaps. -/
theorem g3_targetA (M : MarkedIdeal n X) (hM : IsInvDomain n M) :
    ∃ (X' : CMfd.{u} n) (P : X' → X), IsGluedCanonicalResolution M X' P ∧
      (∀ (X'' : CMfd.{u} n) (P' : X'' → X), IsGluedCanonicalResolution M X'' P' →
        ∃! Ψ : X'' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X', ∀ z, P (Ψ z) = P' z) ∧
      (∀ K : Set X, IsCompact K → ∃ t : Finset (GluedChart M X' P), K ⊆ ⋃ c ∈ t, (c.U : Set X)) ∧
      IsClosed (gluedBoundary M X' P) ∧
      ∀ c : GluedChart M X' P,
        gluedBoundary M X' P ∩ c.V = ⋃ H ∈ chartBoundary c, H ∧
        IsSNCDivisor n ((chartBoundary c).map ((Subtype.val : c.V → X') ⁻¹' ·)) ∧
        ∀ c' : GluedChart M X' P,
          ((chartBoundary c).map (· ∩ P ⁻¹' ((c.U ⊓ c'.U : Opens X) : Set X))).filter
              (fun H => decide H.Nonempty) =
            ((chartBoundary c').map (· ∩ P ⁻¹' ((c.U ⊓ c'.U : Opens X) : Set X))).filter
              (fun H => decide H.Nonempty) := by
  obtain ⟨X', P, h, huniq⟩ := existsUnique_gluedCanonicalResolution M hM
  obtain ⟨hcl, hch⟩ := gluedBoundary_normalCrossings hM h
  exact ⟨X', P, h, huniq, fun K hK => exists_finite_charts_of_isCompact h hK, hcl, hch⟩

end

end Hironaka.HironakaG3RTargetA
