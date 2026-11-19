import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.SingularLocus
import Hironaka.Blowup.ExceptionalLocus
import Hironaka.Blowup.BlowupSequenceIsomorphismOff
import Hironaka.Resolution.StrictTransformSubvarietySequence
import Hironaka.Invariant.CanonicalCentres
import Hironaka.Resolution.HironakaFromSeqInvariant
import Hironaka.Coherence.CartanIrreducible

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Embedded resolution of a subvariety

Source: H. Hironaka, *Resolution of singularities of an algebraic variety over a field of
characteristic zero*, Ann. of Math. 79 (1964); Aroca--Hironaka--Vicente and
Bierstone--Milman for the complex-analytic case; quoted by CT22 in the proof of Lemma 4.4 and
by Copy-4 `lem:resolution` as "after a resolution we may assume `V` smooth".

`X` a compact complex manifold and `V ⊆ X` a closed irreducible analytic subvariety.  There is
a finite sequence of blowups with smooth centres `μ : X̃ → X`, an isomorphism over
`X \ V_sing`, whose strict transform of `V` is a closed connected complex submanifold of `X̃`
of dimension `dim V`.

This statement is **purely geometric**: no Kähler class, no current, no volume enters it.  It
is the embedded-resolution half that human decision I-0198 asks to be isolated out of
`Hironaka.SmoothComponentReduction.exists_modification_smooth_component`; everything else in
that target (compactness, the Kähler background, bigness of the pullback, the
non-Kähler-component property, the non-nef clause and the restricted-volume identity) is
derived from it in `Hironaka.SmoothComponentReduction` itself, with no further RESOLUTION input.

`exists_embeddedResolution_of_smooth` below checks the statement in the case where the
conclusion has to be obtained with the empty sequence: when `V` is already a closed connected
submanifold of dimension `dim V`, the identity is an embedded resolution.  This is the
degenerate case a wrong statement would most likely get wrong (a resolution is not required to
blow anything up, and `strictTransform n id V = V` holds because `V` is closed and
`Exc(id) = ∅`).

Human decisions I-0157/I-0198 kept this statement isolated and named, and I-0458/I-0484/I-1010
had it formalized last, in place, with the statement unchanged.  Together with
`Hironaka.RelativePrincipalization.exists_factorizationData` (relative principalization) it is
one of the two resolution-theoretic statements of the project.  Both are proved from the
canonical resolution invariant (`CanonicalCentres.canonicalInvariant`) through
`HironakaFromSeqInvariant`; this one also uses Cartan's coherence theorem
(`CartanIrreducible.cartanCoherence`) for the ideal sheaf of `V`.

This file is in the root import closure: `Hironaka.SmoothComponentReduction` imports it, and
that module is reachable from the root through `Hironaka.ComponentVanishing` and
`Hironaka.NakamayeMainTheorem`.
-/

open Set

universe u

namespace Hironaka.EmbeddedResolution

open Hironaka.NonKahlerLocus Hironaka.BlowupSequences

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- The conclusion of an embedded resolution of `V`, as a predicate on the modification. -/
def IsEmbeddedResolution (V : ClosedIrreducibleAnalyticSubvariety n X)
    {Xt : Type u} [TopologicalSpace Xt] [ChartedSpace (ComplexModel n) Xt]
    [IsComplexManifold n Xt] (μ : Xt → X) : Prop :=
  IsIsomorphismOver n μ (singularLocus V)ᶜ ∧
    IsClosedConnectedSubmanifold n (strictTransform n μ V.carrier) V.dim

/-- The remaining non-tautological smooth strict-transform data supplied by embedded
resolution.  Closedness and connectedness are reconstructed below. -/
structure EmbeddedResolutionSmoothData (V : ClosedIrreducibleAnalyticSubvariety n X)
    {Xt : Type u} [TopologicalSpace Xt] [ChartedSpace (ComplexModel n) Xt]
    [IsComplexManifold n Xt] (μ : Xt → X) : Prop where
  regularAtDim_strictTransform :
    ∀ x ∈ strictTransform n μ V.carrier,
      RegularAtDim (n := n) (strictTransform n μ V.carrier) x V.dim

/-- **Embedded resolution of singularities** (Hironaka).  Every
closed irreducible analytic subvariety of a compact complex manifold admits a finite sequence
of blowups with smooth centres whose exceptional image lies in its singular locus and whose
strict transform is regular at dimension `dim V` at every point.  The isomorphism away from
the singular locus, and the closedness and connectedness of the strict transform, are
reconstructed below.  Proved from the canonical resolution invariant
`CanonicalCentres.canonicalInvariant n` through
`HironakaFromSeqInvariant.exists_embeddedResolution_data_of_seq_of_isCoherent`, the ideal sheaf
of `V` being coherent by Cartan's theorem (`CartanIrreducible.cartanCoherence`). -/
theorem exists_embeddedResolution_smoothData [CompactSpace X]
    (V : ClosedIrreducibleAnalyticSubvariety n X) :
    ∃ (Xt : Type u) (_ : TopologicalSpace Xt) (_ : ChartedSpace (ComplexModel n) Xt)
      (_ : IsComplexManifold n Xt) (μ : Xt → X) (_ : IsBlowupSequence n X Xt μ),
      μ '' exceptionalLocus n μ ⊆ singularLocus V ∧ EmbeddedResolutionSmoothData V μ := by
  obtain ⟨Xt, _, _, _, μ, hμ, hE, hreg⟩ := HironakaFromSeqInvariant.exists_embeddedResolution_data_of_seq_of_isCoherent (CanonicalCentres.canonicalInvariant n) le_rfl V (CartanIrreducible.cartanCoherence V.carrier V.irreducible_carrier.analytic); exact ⟨Xt, _, _, _, μ, hμ, hE, ⟨hreg⟩⟩

/-- The public embedded-resolution interface, recovering the tautological closedness of the
strict transform from its definition as a closure. -/
theorem exists_embeddedResolution [CompactSpace X]
    (V : ClosedIrreducibleAnalyticSubvariety n X) :
    ∃ (Xt : Type u) (_ : TopologicalSpace Xt) (_ : ChartedSpace (ComplexModel n) Xt)
      (_ : IsComplexManifold n Xt) (μ : Xt → X) (_ : IsBlowupSequence n X Xt μ),
      IsEmbeddedResolution V μ := by
  obtain ⟨Xt, htop, hchart, hmfd, μ, hμ, hExcS, hsmooth⟩ :=
    exists_embeddedResolution_smoothData V
  refine ⟨Xt, htop, hchart, hmfd, μ, hμ, ?_, ?_⟩
  exact BlowupSequenceIsomorphismOff.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
    hμ hExcS
  refine ⟨?_, ?_,
    hsmooth.regularAtDim_strictTransform⟩
  · exact isClosed_closure
  · exact StrictTransformSubvarietySequence.isConnected_strictTransform_of_isBlowupSequence
      hμ V hExcS

/-- Sanity check on the statement above: if `V` is already a closed connected submanifold of
the certified dimension, the empty sequence of blowups resolves it. -/
theorem exists_embeddedResolution_of_smooth
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim) :
    ∃ (Xt : Type u) (_ : TopologicalSpace Xt) (_ : ChartedSpace (ComplexModel n) Xt)
      (_ : IsComplexManifold n Xt) (μ : Xt → X) (_ : IsBlowupSequence n X Xt μ),
      IsEmbeddedResolution V μ := by
  refine ⟨X, ‹_›, ‹_›, ‹_›, id, IsBlowupSequence.refl, ⟨?_, ?_⟩, ?_⟩
  · simpa using (Set.bijOn_id ((singularLocus V)ᶜ))
  · simp [exceptionalLocus_id]
  · simpa [strictTransform, exceptionalLocus_id, V.isClosed_carrier.closure_eq] using hV

end

end Hironaka.EmbeddedResolution
