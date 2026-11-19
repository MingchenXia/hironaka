import Hironaka.Resolution.HironakaG3UniverseConjugateGeometry
import Hironaka.Resolution.HironakaG3RTargetA
import Hironaka.Resolution.HironakaG3RGluedEmbedded
import Hironaka.Resolution.HironakaOriginalGlobalProperModification

/-! # G3 under target (A): the final statement

Lane G3 (run 0080, round 4).  Blueprint: `hironaka-g3-r-final.tex`.  Notes:
`work/hironaka-resume-20261111/G3/G3-TARGET-A.md` (section 5).

Human decision I-1339 (option (A)): G3's global target is the glued terminal atlas.  This module states and proves the final
G3 theorem in the shape of `G3-TARGET-A.md` §5, for an arbitrary (not necessarily compact) complex manifold `X`:

* (a) for every marked ideal `M` of the domain of the canonical invariant: a glued canonical resolution `P : X' → X` exists,
  is unique up to unique biholomorphism over `X`, compact sets are covered by finitely many charts, its boundary is a closed
  divisor with normal crossings (chart-wise simple normal crossings, chart boundaries agreeing on overlaps), and for
  `M = (X, X, E, 𝔞, 1)` the ideal `P^*𝔞` is invertible with zero locus `P⁻¹ Z(𝔞)` and `P` is an isomorphism over
  `X ∖ Z(𝔞)`; the principalization clause holds for EVERY glued canonical resolution
  (**`principalization_of_isGluedCanonicalResolution`**, transported along the unique comparison);
* (b) for every closed irreducible analytic subvariety `V` with `dim V < n`: a glued embedded resolution `P_V : X'_V → X`
  (locally the canonical stopped prefixes) exists, is unique up to unique biholomorphism over `X`, `Exc P_V = P_V⁻¹ V_sing`,
  `P_V` is an isomorphism over `X ∖ V_sing`, the strict transform of `V` is a closed submanifold of dimension `dim V` at each
  of its points, and on each chart the boundary has simple normal crossings, has union `Exc P_V` and has only normal
  crossings with the strict transform (`HironakaG3RGluedEmbedded`).

**`g3_final`** is the conjunction.  NOT included: a global indexing of the boundaries by smooth hypersurfaces (global SNC);
it is chart-wise.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace Function
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG3RFinal

noncomputable section

attribute [local instance] Classical.propDecidable

open Hironaka.NonKahlerLocus Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals
  NormalCrossings
  HironakaG3RGluedUniqueness HironakaOriginalTerminalAtlas HironakaOriginalTerminalManifold
  HironakaOriginalTerminalLocalBiholomorphism
open MarkedIdealBiholomorphism.MarkedIdeal (pullback)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

attribute [local instance] originalTerminalChartedSpace originalTerminalGluedSpace_isComplexManifold

variable {n : ℕ} {X : CMfd.{u} n}

/-- The constructed glued terminal atlas is a glued canonical resolution. -/
theorem isGluedCanonicalResolution_original (M : MarkedIdeal n X) (hM : IsInvDomain n M) :
    IsGluedCanonicalResolution M (originalTerminalManifold M hM)
      (originalTerminalGluedProjection M hM : originalTerminalManifold M hM → X) := by
  let A := actualLocalTerminalAtlas M hM
  refine ⟨originalTerminalGluedProjection_contMDiff M hM,
    HironakaOriginalTerminalProperProjection.originalTerminalGluedProjection_isProperMap M hM,
    HironakaOriginalGlobalOffZero.originalTerminalGluedProjection_surjective M hM, fun x => ?_⟩
  refine ⟨A.openSet x, A.point_mem x, A.finalSpace x, A.tower x, A.canonical x, A.terminal x,
    originalTerminalLocalRangeOpen M hM x, originalTerminalLocalInclusion_range M hM x,
    originalTerminalLocalBiholomorphism M hM x, fun y => ?_⟩
  change originalTerminalGluedProjection M hM (originalTerminalLocalInclusion M hM x y) = _
  rw [originalTerminalGluedProjection_local]
  rfl

/-- Precomposing with a biholomorphism preserves being an isomorphism over a set. -/
theorem isIsomorphismOver_comp_diffeo {X₁ X₂ : CMfd.{u} n} {f : X₂ → X} {S : Set X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f) (h : IsIsomorphismOver n f S)
    (Ψ : X₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X₂) : IsIsomorphismOver n (f ∘ Ψ) S := by
  have h' := HironakaG3UniverseDiffeoDerivative.conjugate_isomorphismOver Ψ.symm
    (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) f hf S h
  change IsIsomorphismOver n (f ∘ (fun x => Ψ.symm.symm x)) S at h'
  have hh : (fun x => Ψ.symm.symm x) = fun x => Ψ x := rfl
  rw [hh] at h'
  exact h'

/-- **Principalization on every glued canonical resolution** of `M = (X, X, E, 𝔞, 1)`: `P^*𝔞` is invertible, its zero locus
is `P⁻¹ Z(𝔞)`, and `P` is an isomorphism over `X ∖ Z(𝔞)` (transported from the constructed glued terminal atlas along the
unique comparison). -/
theorem principalization_of_isGluedCanonicalResolution {M : MarkedIdeal n X} (hM : IsInvDomain n M)
    {X' : CMfd.{u} n} {P : X' → X} (h : IsGluedCanonicalResolution M X' P) (hN : M.N = univ) (hd : M.d = 1) :
    (GermIdeal.pullback (m := n) P M.ideal).IsInvertible ∧
      (GermIdeal.pullback (m := n) P M.ideal).zeroLocus = P ⁻¹' M.ideal.zeroLocus ∧
      IsIsomorphismOver n P M.ideal.zeroLocusᶜ := by
  obtain ⟨Ψ, hΨ, -⟩ := existsUnique_biholomorphism hM h (isGluedCanonicalResolution_original M hM)
  have hP : P = (originalTerminalGluedProjection M hM : originalTerminalManifold M hM → X) ∘ Ψ :=
    funext fun z => (hΨ z).symm
  have hcoh := hM.isWellFormed.isCoherent
  have hP₀ := originalTerminalGluedProjection_contMDiff M hM
  refine ⟨?_, BlowupExceptionalDivisor.zeroLocus_pullback h.1 hcoh, ?_⟩
  · rw [hP, GermIdealTotalTransform.pullback_comp hP₀ Ψ.contMDiff hcoh]
    have hΨ : exceptionalLocus n Ψ = ∅ :=
      eq_empty_of_forall_notMem (MarkedIdealTowerTransport.notMem_exceptionalLocus Ψ)
    exact GermIdealTotalTransform.isInvertible_pullback Ψ.contMDiff (by rw [hΨ, interior_empty])
      (HironakaOriginalGlobalPrincipalization.originalTerminalGluedProjection_pullback_isInvertible M hM hN hd)
  · rw [hP]
    exact isIsomorphismOver_comp_diffeo hP₀
      (HironakaOriginalGlobalOffZero.originalTerminalGluedProjection_isIsomorphismOffZero M hM hN hd) Ψ

/-- **The final G3 theorem under target (A)** (`G3-TARGET-A.md` §5): on every complex manifold `X`, not necessarily compact,
(a) every marked ideal of the domain has a glued canonical resolution, unique up to unique biholomorphism over `X`, with
finite chart covers of compact sets, a closed boundary with normal crossings (chart-wise simple normal crossings, chart
boundaries agreeing on overlaps), and principalization of `𝔞` when `M = (X, X, E, 𝔞, 1)`; (b) every closed irreducible
analytic subvariety `V` with `dim V < n` has a glued embedded resolution, unique up to unique biholomorphism over `X`, with
`Exc P = P⁻¹ V_sing`, `P` an isomorphism over `X ∖ V_sing`, the strict transform of `V` a closed submanifold of dimension
`dim V`, and chart-wise simple normal crossings boundary with union `Exc P`, having only normal crossings with the strict
transform. -/
theorem g3_final (X : CMfd.{u} n) :
    (∀ M : MarkedIdeal n X, IsInvDomain n M →
      ∃ (X' : CMfd.{u} n) (P : X' → X), IsGluedCanonicalResolution M X' P ∧
        (∀ (X'' : CMfd.{u} n) (P' : X'' → X), IsGluedCanonicalResolution M X'' P' →
          ∃! Ψ : X'' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X', ∀ z, P (Ψ z) = P' z) ∧
        (∀ K : Set X, IsCompact K → ∃ t : Finset (GluedChart M X' P), K ⊆ ⋃ c ∈ t, (c.U : Set X)) ∧
        IsClosed (HironakaG3RGluedBoundary.gluedBoundary M X' P) ∧
        (∀ c : GluedChart M X' P,
          HironakaG3RGluedBoundary.gluedBoundary M X' P ∩ c.V = ⋃ H ∈ HironakaG3RGluedBoundary.chartBoundary c, H ∧
          IsSNCDivisor n ((HironakaG3RGluedBoundary.chartBoundary c).map ((Subtype.val : c.V → X') ⁻¹' ·)) ∧
          ∀ c' : GluedChart M X' P,
            ((HironakaG3RGluedBoundary.chartBoundary c).map (· ∩ P ⁻¹' ((c.U ⊓ c'.U : Opens X) : Set X))).filter
                (fun H => decide H.Nonempty) =
              ((HironakaG3RGluedBoundary.chartBoundary c').map (· ∩ P ⁻¹' ((c.U ⊓ c'.U : Opens X) : Set X))).filter
                (fun H => decide H.Nonempty)) ∧
        (M.N = univ → M.d = 1 →
          (GermIdeal.pullback (m := n) P M.ideal).IsInvertible ∧
            (GermIdeal.pullback (m := n) P M.ideal).zeroLocus = P ⁻¹' M.ideal.zeroLocus ∧
            IsIsomorphismOver n P M.ideal.zeroLocusᶜ)) ∧
    (∀ V : ClosedIrreducibleAnalyticSubvariety n X, V.dim < n →
      ∃ (X' : CMfd.{u} n) (P : X' → X), HironakaG3RGluedEmbedded.IsGluedEmbeddedResolution V X' P ∧
        (∀ (X'' : CMfd.{u} n) (P' : X'' → X), HironakaG3RGluedEmbedded.IsGluedEmbeddedResolution V X'' P' →
          ∃! Ψ : X'' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X', ∀ z, P (Ψ z) = P' z) ∧
        exceptionalLocus n P = P ⁻¹' singularLocus V ∧
        IsIsomorphismOver n P (singularLocus V)ᶜ ∧
        IsClosedSubmanifold n (strictTransform n P V.carrier) ∧
        (∀ z ∈ strictTransform n P V.carrier, RegularAtDim (n := n) (strictTransform n P V.carrier) z V.dim) ∧
        ∀ c : HironakaG3RTowerClass.TowerChart (HironakaG3RGluedEmbedded.embeddedClass V) X' P,
          IsSNCDivisor n ((HironakaG3RGluedEmbedded.chartBoundary c).map ((Subtype.val : c.V → X') ⁻¹' ·)) ∧
          (⋃ H ∈ HironakaG3RGluedEmbedded.chartBoundary c, H) = exceptionalLocus n P ∩ c.V ∧
          HasNormalCrossings n ((Subtype.val : c.V → X') ⁻¹' strictTransform n P V.carrier)
            ((HironakaG3RGluedEmbedded.chartBoundary c).map ((Subtype.val : c.V → X') ⁻¹' ·))) := by
  refine ⟨fun M hM => ?_, fun V hV => HironakaG3RGluedEmbedded.exists_glued_embeddedResolution V hV⟩
  obtain ⟨X', P, h, huniq, hfin, hcl, hch⟩ := HironakaG3RTargetA.g3_targetA M hM
  exact ⟨X', P, h, huniq, hfin, hcl, hch, fun hN hd => principalization_of_isGluedCanonicalResolution hM h hN hd⟩

end

end Hironaka.HironakaG3RFinal
