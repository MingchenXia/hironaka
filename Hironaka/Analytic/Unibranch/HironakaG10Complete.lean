import Hironaka.Analytic.Unibranch.HironakaG10FinalAssembly
import Hironaka.Analytic.Unibranch.HironakaG10GlPresentationStep
import Hironaka.Analytic.Unibranch.HironakaG10NfFibreModelCanonical
import Hironaka.Analytic.Unibranch.HironakaG10EpChowBridge
import Hironaka.Analytic.Unibranch.HironakaG10RdFinal

/-!
# G10 complete: Hironaka's flattening theorem and Chow lemma for compact reduced complex spaces

Run 0081 (orchestrator, from lane G10FN's draft). The two inputs of the final assembly
(`HironakaG10FinalAssembly`) are proved without hypotheses:

* the pulled torsion presentations over the centre: `HironakaG10GlPresentationStep.hpres`
  (lanes G10HP, G10S1, G10N34, G10GL);
* the fibre comparison `hfib` (the literal binder of `HironakaG10GlOffCentrePresentation.hT_of_presentation_centre`):
  `HironakaG10NfFibreModelCanonical.hfib_of_canonical` (lanes G10H3, G10FI, G10N34).

Hence, with no hypothesis:

* `lemma445` — Hironaka's Lemma 4.4.5 for one blowup step along an arbitrary flat sum-centre (the `hT` binder of
  `HironakaG10GnHF1.hironakaFlattening_of_hT` and `HironakaG10RdFinal.nonempty_roundData_of_frisch`);
* `nonempty_roundData` — the round data of the flattening algorithm for every compact stage with proper `f`;
* `hironakaFlattening` — Hironaka's flattening theorem over a compact base (`HironakaFlattening`);
* `hironakaChowLemmaGeneral` — Hironaka's Chow lemma (`HironakaChowLemmaGeneral`, book `thm:HironakaChow`);
* `hironakaChowLemmaManifold` — the manifold form consumed by the Hironaka book (TN `HironakaChowLemmaManifold`).

No named input.
-/

set_option autoImplicit false

open Set CategoryTheory Filter
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10Complete

open Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine
  Hironaka.Analytic.Unibranch.HironakaG10RdPermRun Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum
  Hironaka.Analytic.Unibranch.HironakaG10SbFlattenerSupportGerm Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus
  Hironaka.Analytic.Unibranch.HironakaG10GlStrictFlatAssembly Hironaka.Analytic.Unibranch.HironakaG10GlLeavingContradiction
  Hironaka.Analytic.Unibranch.HironakaG10ChowFibreChain Hironaka.Analytic.Unibranch.HironakaG10NfFibreModel

/-- **Hironaka's Lemma 4.4.5 for one sum-centre step** (the `hT` binder of
`HironakaG10GnHF1.hironakaFlattening_of_hT`): after one blowup along a flat sum-centre, every local flattener `Z` of
the old family has a local flattener of the new family with support the transported support `T(Z)`. -/
theorem lemma445 :
    ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∃ Z' : LocalFlattener (nextWith s c).f,
          Z'.support = transportedSupport s c Z :=
  HironakaG10GlOffCentrePresentation.hT_of_presentation_centre HironakaG10NfN5.hN5
    HironakaG10GlPresentationStep.hpres HironakaG10NfFibreModelCanonical.hfib_of_canonical

/-- **The round data of the flattening algorithm exist** for every compact stage with proper `f`. -/
theorem nonempty_roundData (s₀ : Stage) (hX : CompactSpace s₀.X.obj.left)
    (hf : IsProperMap s₀.f.hom.left.base) :
    Nonempty (HironakaG10ChowLeavingRounds.RoundData s₀ hf) :=
  HironakaG10RdFinal.nonempty_roundData_of_frisch HironakaG10GnHF1.hF1 HironakaG10GfFinal.hF2_stage lemma445
    s₀ hX hf

/-- **Hironaka's flattening theorem over a compact base** (`HironakaFlattening`). -/
theorem hironakaFlattening : HironakaG10ChowFlatteningReduction.HironakaFlattening :=
  HironakaG10GnHF1.hironakaFlattening_of_hT lemma445

/-- **Hironaka's Chow lemma for compact reduced complex spaces** (`HironakaChowLemmaGeneral`, book
`thm:HironakaChow`, goal G10): every proper bimeromorphic morphism to a compact reduced complex space is dominated
by a finite composition of blowups with smooth nowhere dense centres. -/
theorem hironakaChowLemmaGeneral : HironakaG10GenStatement.HironakaChowLemmaGeneral :=
  HironakaG10FinalAssembly.hironakaChowLemmaGeneral_of_presentations_of_fibreComparison
    HironakaG10GlPresentationStep.hpres HironakaG10NfFibreModelCanonical.hfib_of_canonical

/-- **The manifold Chow lemma consumed by the Hironaka book** (TN `HironakaChowLemmaManifold`, universe of the native
category). -/
theorem hironakaChowLemmaManifold :
    Hironaka.HironakaChowLemma.HironakaChowLemmaManifold.{0} :=
  HironakaG10EpChowBridge.hironakaChowLemmaManifold_of_hironakaChowLemmaGeneral hironakaChowLemmaGeneral

end Hironaka.Analytic.Unibranch.HironakaG10Complete
