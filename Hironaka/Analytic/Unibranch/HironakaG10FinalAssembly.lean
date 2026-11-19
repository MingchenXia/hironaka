import Hironaka.Analytic.Unibranch.HironakaG10GlOffCentrePresentation
import Hironaka.Analytic.Unibranch.HironakaG10NfFibreModel
import Hironaka.Analytic.Unibranch.HironakaG10GnHF1
import Hironaka.Analytic.Unibranch.HironakaG10EpChowBridge

/-!
# G10 final assembly: Hironaka's Chow lemma from the two step-level inputs of Lemma 4.4.5

Lane G10FN, run 0081 (blueprint `hironaka-g10-final-assembly.tex`).  Everything in the proof of Hironaka's Chow
lemma for compact reduced complex spaces (`HironakaG10GenStatement.HironakaChowLemmaGeneral`, book
`thm:HironakaChow`) is proved except two LOCAL, step-level inputs of Hironaka 1975, Lemma 4.4.5 (one blowup step of
the flattening algorithm along a flat sum-centre), stated here as named propositions so that the remaining contract
of G10 can be grepped:

* `PresentationsOverCentre` — at every point `y''` of the strict source `Y'` of a blowup step lying over the centre,
  a pulled torsion presentation (`HironakaG10GlStrictFlatAssembly.PulledPresentation`): the local ring of the fibre
  product `Y ×_X X'`, a generator of the pulled centre, the strict-source stalk as the quotient by its torsion and
  the base change of the pointed flattener (Hironaka 1975, Th. 2.5; HLT 1973).  Producer: lanes G10GL (assembly
  `hpres_of_flattener`) and G10N34 (its flattener field, N3/N4).
* `FibreModelsOverCentre` — at every pair `(y, x')` over the centre with `x' ∈ T(Z) ∩ |Z₁|`, a local model of the
  fibre product (`HironakaG10NfFibreModel.FibreModel`; the chart-level content of Hironaka 1975, p. 538, step
  (ii)).  Producer: lanes G10H3 / G10FI (H3, canonical charts).

Both are TRUE (independent audit G10AU, `work/hironaka-run0081-20261117/G10AU/AUDIT-chain.md`, sections "hfib
reduced to FibreModels" and "hT from hN5, hpres, hfib"), local, and not restatements of the goal: each concerns one
blowup step at one point (resp. one pair of points) and is consumed through the proved splices below.  They are
TEMPORARY: the producer lanes discharge them in this run, after which `hironakaChowLemmaGeneral_of_presentations`
applied to the two producers is the unconditional Chow lemma.

* `hT_of_presentations` — the literal `hT` binder of `HironakaG10GnHF1.hironakaFlattening_of_hT` (Lemma 4.4.5 for
  one sum-centre step and every local flattener), from `HironakaG10GlOffCentrePresentation.hT_of_presentation_centre`
  with the proved `HironakaG10NfN5.hN5` and `HironakaG10NfFibreModel.hfib_of_fibreModels`;
* `nonempty_roundData_of_presentations` — complete `RoundData` of the actual run (G10-03 deliverable);
* `hironakaFlattening_of_presentations` — Hironaka's flattening theorem over a compact base;
* `hironakaChowLemmaGeneral_of_presentations` — **Hironaka's Chow lemma for compact reduced complex spaces**;
* `hironakaChowLemmaManifold_of_presentations` — the manifold Chow lemma consumed by the Hironaka book;
* variants from the coarser forms (`hfib` instead of the fibre models; `hT` itself).
-/

set_option autoImplicit false

open Set CategoryTheory Filter
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10FinalAssembly

open Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine
  Hironaka.Analytic.Unibranch.HironakaG10RdPermRun Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum
  Hironaka.Analytic.Unibranch.HironakaG10SbFlattenerSupportGerm Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus
  Hironaka.Analytic.Unibranch.HironakaG10GlStrictFlatAssembly Hironaka.Analytic.Unibranch.HironakaG10GlLeavingContradiction
  Hironaka.Analytic.Unibranch.HironakaG10ChowFibreChain Hironaka.Analytic.Unibranch.HironakaG10NfFibreModel

/-! ### The two remaining inputs (named; TRUE; discharged by the producer lanes of run 0081) -/

/-- **Remaining input 1 of G10: pulled torsion presentations over the centre** (the `hpres` binder of
`HironakaG10GlOffCentrePresentation.hT_of_presentation_centre`, verbatim).  For every stage `s` of the flattening
algorithm, every admissible centre `c` and every point `y''` of the strict source of the blowup step `nextWith s c`
whose image in the old base lies in the centre (the non-unit locus of the centre ideal), there is a pulled torsion
presentation `PulledPresentation s c y''`: the analytic local ring `B` of `Y ×_X X'` at `(q y'', f' y'')` with its
structure map, a regular generator `g` of the pulled centre, `𝒪_{Y',y''} ≅ B ⧸ (g-power torsion)` over `𝒪_{X',f' y''}`,
and the base change of the pointed flattener of `f` at `q y''` (Hironaka 1975, Th. 2.5; HLT 1973).  Off the centre
the presentation is proved (`pulledPresentation_of_not_mem_nonunitLocus`).  TRUE (G10AU `AUDIT-chain.md`).
Producer: G10GL (`hpres_of_flattener`) with G10N34 (`isFlattenerIdeal_canonical`, N3/N4). -/
def PresentationsOverCentre : Prop :=
  ∀ (s : Stage) (c : AdmissibleCentre s.f) (y'' : (nextWith s c).Y.obj.left),
    (stepσ s c).hom.left.base ((nextWith s c).f.hom.left.base y'') ∈ nonunitLocus c.B c.b →
    Nonempty (PulledPresentation s c y'')

/-- **Remaining input 2 of G10: local models of the fibre product over the centre** (the `hmodel` binder of
`HironakaG10NfFibreModel.hfib_of_fibreModels`, verbatim).  For a stage with compact base and proper map, a flat
sum-centre `c`, a local flattener `Z` of the old family, a point `x' ∈ T(Z)` of the transported support lying in the
support of a local flattener `Z₁` of the new family and over the centre, and every old source point `y` over
`σ x'`, there is a `FibreModel s c Z₁ y x'`: a parametrisation of `Y ×_X X'` near `(y, x')` with its Noetherian
local rings, a regular generator of the pulled centre, base change of the old flatness, the strict transform at the
pairs whose torsion lies in the closed fibre, and the spreading of a torsion bound along `Z₁` (Hironaka 1975,
Lemma 4.4.5, proof, p. 538, step (ii)).  TRUE (G10AU `AUDIT-chain.md`).  Producer: G10H3 / G10FI (H3: canonical
charts). -/
def FibreModelsOverCentre : Prop :=
  ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
    ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
      (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
      ∀ Z : LocalFlattener s.f, ∀ x' ∈ transportedSupport s c Z,
        ∀ Z₁ : LocalFlattener (nextWith s c).f, x' ∈ Z₁.support →
          (stepσ s c).hom.left.base x' ∈ nonunitLocus c.B c.b →
          ∀ y : s.Y.obj.left, s.f.hom.left.base y = (stepσ s c).hom.left.base x' →
            Nonempty (FibreModel s c Z₁ y x')

/-! ### Assembly -/

/-- **Hironaka 1975, Lemma 4.4.5 for one flat sum-centre step** (the literal `hT` binder of
`HironakaG10GnHF1.hironakaFlattening_of_hT`) from the two remaining inputs: every local flattener `Z` of the old
family has a local flattener of the new family with support the transported support `T(Z)`. -/
theorem hT_of_presentations (hPresentationsOverCentre : PresentationsOverCentre)
    (hFibreModelsOverCentre : FibreModelsOverCentre) :
    ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∃ Z' : LocalFlattener (nextWith s c).f,
          Z'.support = transportedSupport s c Z :=
  HironakaG10GlOffCentrePresentation.hT_of_presentation_centre HironakaG10NfN5.hN5
    hPresentationsOverCentre (hfib_of_fibreModels hFibreModelsOverCentre)

/-- **Complete round data** (the G10-03 deliverable `HironakaG10ChowLeavingRounds.RoundData`: compatible global
sum-centres, tracked sets, start/leave/finish of the actual run) for every compact stage with a proper family, from
the two remaining inputs: `HironakaG10RdFinal.nonempty_roundData_of_frisch` with the proved Frisch inputs
(`HironakaG10GnHF1.hF1`, `HironakaG10GfFinal.hF2_stage`). -/
theorem nonempty_roundData_of_presentations (hPresentationsOverCentre : PresentationsOverCentre)
    (hFibreModelsOverCentre : FibreModelsOverCentre) (s₀ : Stage) (hX : CompactSpace s₀.X.obj.left)
    (hf : IsProperMap s₀.f.hom.left.base) :
    Nonempty (HironakaG10ChowLeavingRounds.RoundData s₀ hf) :=
  HironakaG10RdFinal.nonempty_roundData_of_frisch HironakaG10GnHF1.hF1 HironakaG10GfFinal.hF2_stage
    (hT_of_presentations hPresentationsOverCentre hFibreModelsOverCentre) s₀ hX hf

/-- **Hironaka's flattening theorem over a compact base** from the two remaining inputs. -/
theorem hironakaFlattening_of_presentations (hPresentationsOverCentre : PresentationsOverCentre)
    (hFibreModelsOverCentre : FibreModelsOverCentre) :
    HironakaG10ChowFlatteningReduction.HironakaFlattening :=
  HironakaG10GnHF1.hironakaFlattening_of_hT
    (hT_of_presentations hPresentationsOverCentre hFibreModelsOverCentre)

/-- **Hironaka's Chow lemma for compact reduced complex spaces** (`HironakaChowLemmaGeneral`, book
`thm:HironakaChow`) from the two remaining inputs: every proper bimeromorphic morphism to a compact reduced complex
space is dominated by a finite composition of blowups with smooth nowhere dense centres. -/
theorem hironakaChowLemmaGeneral_of_presentations (hPresentationsOverCentre : PresentationsOverCentre)
    (hFibreModelsOverCentre : FibreModelsOverCentre) :
    HironakaG10GenStatement.HironakaChowLemmaGeneral :=
  HironakaG10EpChowBridge.hironakaChowLemmaGeneral_of_hironakaFlattening
    (hironakaFlattening_of_presentations hPresentationsOverCentre hFibreModelsOverCentre)

/-- **The manifold Chow lemma consumed by the Hironaka book** (TN `HironakaChowLemmaManifold`, in the universe of the
native category) from the two remaining inputs. -/
theorem hironakaChowLemmaManifold_of_presentations (hPresentationsOverCentre : PresentationsOverCentre)
    (hFibreModelsOverCentre : FibreModelsOverCentre) :
    Hironaka.HironakaChowLemma.HironakaChowLemmaManifold.{0} :=
  HironakaG10EpChowBridge.hironakaChowLemmaManifold_of_hironakaChowLemmaGeneral
    (hironakaChowLemmaGeneral_of_presentations hPresentationsOverCentre hFibreModelsOverCentre)

/-! ### Variants from the coarser forms of the step-level input -/

/-- The Chow lemma from Lemma 4.4.5 itself (the literal `hT` binder), for a producer that delivers `hT` directly. -/
theorem hironakaChowLemmaGeneral_of_hT
    (hT : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∃ Z' : LocalFlattener (nextWith s c).f,
          Z'.support = transportedSupport s c Z) :
    HironakaG10GenStatement.HironakaChowLemmaGeneral :=
  HironakaG10EpChowBridge.hironakaChowLemmaGeneral_of_hironakaFlattening
    (HironakaG10GnHF1.hironakaFlattening_of_hT hT)

/-- The Chow lemma from the presentations over the centre and the fibre comparison `hfib` (the literal binder of
`HironakaG10GlOffCentrePresentation.hT_of_presentation_centre`), for a producer that delivers `hfib` directly
(e.g. `hfib_of_fibreModels` of a fibre-model producer). -/
theorem hironakaChowLemmaGeneral_of_presentations_of_fibreComparison
    (hPresentationsOverCentre : PresentationsOverCentre)
    (hFibreComparison : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∀ x' ∈ transportedSupport s c Z,
          ∀ Z₁ : LocalFlattener (nextWith s c).f, x' ∈ Z₁.support →
            ∀ᶠ y' in 𝓝 x', y' ∈ Z₁.support →
              ∀ y : s.Y.obj.left, s.f.hom.left.base y = (stepσ s c).hom.left.base y' →
                ∃ y'' : (nextWith s c).Y.obj.left, (stepQ s c).hom.left.base y'' = y ∧
                  (nextWith s c).f.hom.left.base y'' = y' ∧
                  Ideal.comap ((stepQ s c).hom.left.stalkMap y'').hom
                      (fibreIdealAt (nextWith s c).f y'') ≤
                    fibreIdealAt s.f ((stepQ s c).hom.left.base y'')) :
    HironakaG10GenStatement.HironakaChowLemmaGeneral :=
  hironakaChowLemmaGeneral_of_hT
    (HironakaG10GlOffCentrePresentation.hT_of_presentation_centre HironakaG10NfN5.hN5
      hPresentationsOverCentre hFibreComparison)

end Hironaka.Analytic.Unibranch.HironakaG10FinalAssembly
