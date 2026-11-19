import Hironaka.Analytic.PshAnalyticSetExtension
import Hironaka.Analytic.PshAnalyticRemovable

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Removable singularities of quasi-PSH functions (Demailly, CADG I.5.24)

**Proved** (run 0100): `demaillyCadgI524_analyticRemovableThetaPsh` is now
`PshAnalyticRemovable.analyticRemovableThetaPsh`, Demailly's own argument for (5.23)/(5.24)
with `w = log ∑ |gᵢ|²` for local generators of `A`; see that module.  The statement below is
unchanged; the text that follows is the original description of the input.

Demailly, *Complex Analytic and Differential
Geometry*, Chapter I, Theorem (5.24) (`demailly-cadg:I.5.24`): if `A` is a
closed **pluripolar** set in a complex manifold `X`, every `v ∈ PSH(X \ A)`
which is locally bounded above near `A` extends uniquely to `ṽ ∈ PSH(X)`, the
extension being the upper semicontinuous regularization.  Demailly states it as
the complex analogue of his (5.23) for subharmonic functions across a closed
polar set, whose proof he gives in full.  A complex analytic subset with empty
interior is pluripolar by his (5.22), with `u = log Σ |g_i|²` for local
generators; `[ConnectedSpace M]` together with `A ≠ univ` (a hypothesis already
inside `AnalyticRemovableThetaPsh`) is what supplies the empty interior.

`[ConnectedSpace M]` is **defensive**, not a correctness fix — the earlier
claim that it was load-bearing was wrong.  On a disconnected manifold an
analytic `A ≠ univ` can be a whole component and is then not pluripolar there,
so the classical hypothesis really does fail; but the Lean *conclusion* does
not.  At a point of `interior A`, `extensionAcross` replaces `u` by `⊥` on all
of `A` before taking the upper regularization, so the regularized function is
identically `⊥` near that point, and `⊥` is plurisubharmonic in this
development (`Plurisubharmonic.lean`, "the value `⊥` is permitted").
`ThetaPshLocalClosure` is therefore automatic over any open part of `A`, from
`HasSmoothLocalPotentials` alone.  What pluripolarity buys classically is
*uniqueness* of the extension, which `ThetaPshLocalClosure` does not assert.
The instance is kept because it costs the consumers nothing and matches
Demailly's own setting.

`Hironaka.PshAnalyticSetExtension` already reduced the `θ`-PSH form of this
statement to one proposition, `AnalyticRemovableThetaPsh`, and proved everything
around it: chart bookkeeping, the nested-regularization identity, the
codimension-two special case, and the fact that the local closure at points of
`A` is all a consumer needs.  Its docstring calls the residue "the exact
unresolved Grauert--Remmert implication".  This module **names** that residue,
once, as a source-anchored interface, instead of every consumer carrying it as
an ad-hoc hypothesis.

The hypothesis `HasSmoothLocalPotentials θ` **is** load-bearing: the conclusion
`ThetaPshLocalClosure` has to *exhibit* a smooth local potential of `θ` at each
point of `A`, and the `ThetaPshOff` hypothesis only supplies potentials off `A`.
It is not a restriction relative to Demailly — for a closed form it would
follow from the local `ddᶜ`-lemma, which this project does not have.
Every other hypothesis of the classical theorem — that `A` is analytic, proper,
that `v` is `θ`-PSH off `A` and locally bounded above there — is already inside
`AnalyticRemovableThetaPsh`.

Consumers so far: `Hironaka.ResidualNef` (Copy-4 `lem:residual-nef`, across
`Supp D`) and, as a hypothesis it can now discharge,
`Hironaka.DemaillyRegularizationStep3Integration`.  Both already work on a
connected manifold, as does
`PshAnalyticSetExtension.thetaPlurisubharmonic_extensionAcross_of_analyticRemovable`.
-/

open Set Filter
open scoped Topology

namespace Hironaka.PshRemovableSingularity

open ThetaPshCodimTwoExtension PshAnalyticSetExtension

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Demailly, CADG I.5.24** (`demailly-cadg:I.5.24`), proved in
`PshAnalyticRemovable.analyticRemovableThetaPsh`.
A `θ`-PSH function off a proper closed analytic subset `A`, locally bounded
above there, has the local `θ`-PSH closure conclusion at the points of `A`,
provided `θ` itself has smooth local potentials. -/
theorem demaillyCadgI524_analyticRemovableThetaPsh [ConnectedSpace M]
    (theta : SmoothRealForm n M 2) (_htheta : HasSmoothLocalPotentials theta)
    (A : Set M) (u : M → EReal) :
    AnalyticRemovableThetaPsh theta A u :=
  PshAnalyticRemovable.analyticRemovableThetaPsh _htheta A u

end

end Hironaka.PshRemovableSingularity
