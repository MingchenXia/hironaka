import Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener

/-!
# P5 — flattening from round data and the local input

Lane G10H, run 0080, round 3 (plan P5 of `work/hironaka-resume-20261111/G10H/PSEUDOFREE-ROUTE.md` §4;
r1 note `HIRONAKA75-GLOBAL-STEP.md` §3.1).  Source: H. Hironaka, *Flattening theorem in
complex-analytic geometry*, Amer. J. Math. 97 (1975), proof of `I_n ⇒ II_n` with `B = X`
(pp. 544–546), Lemma 4.6.1 (p. 544).

Lane G10C's `HironakaG10ChowLeavingRounds` landed the round bookkeeping of Hironaka's algorithm
(`RoundData`: a centre machine, rounds, tracked sets with the start / leaving / end properties) and
`exists_flattening_of_roundData`, which still assumes closed non-flat images (`hclosed`) along the
run.  This module discharges `hclosed` from the ONE local input (P2):

* `hclosed_of_roundData` — every stage of the run has a closed non-flat image, from
  `PersistentLocalFlattener`;
* `exists_flattening_of_roundData_of_persistent` — **the conclusion of `HironakaFlattening` for
  `s₀.f`** from round data, the local input and `hfg` (coherence of the fibre kernels, lane G10P)
  only.  The existence of round data is the content of Theorems `I_n`/`II_n` (lane G10C, skeleton
  S1–S6), against the same input.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10HirRoundData

open Hironaka HironakaG10PNIdealFamily
open Hironaka.Analytic.Unibranch
open Hironaka.Analytic.Unibranch.HironakaG10ChowStrictTransformCalculus Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver
  Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningReduction
  Hironaka.Analytic.Unibranch.HironakaG10ChowTowerDomination Hironaka.Analytic.Unibranch.HironakaG10ChowFlatBimeromorphicIso
  Hironaka.Analytic.Unibranch.HironakaG10ChowLeavingRounds Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener

noncomputable section

/-- Closed non-flat images along the run of round data, from the local input. -/
theorem hclosed_of_roundData (hP : PersistentLocalFlattener) (s₀ : Stage)
    (hf : IsProperMap s₀.f.hom.left.base) (R : RoundData s₀ hf) (n : ℕ) :
    IsClosed ((toFlatteningSequence R.M s₀ R.d₀ hf).nonflatImage n) :=
  machine_hclosed hP R.M s₀ R.d₀ hf n

/-- **Flattening from round data and the local input** (G10C's round data + P2): the conclusion of
`HironakaFlattening` for `s₀.f`; besides the round data only `hfg` (lane G10P) and the named input
`PersistentLocalFlattener` (= leaf `G10.FLAT.07`) remain. -/
theorem exists_flattening_of_roundData_of_persistent (hP : PersistentLocalFlattener) (s₀ : Stage)
    (hX : CompactSpace s₀.X.obj.left) (hf : IsProperMap s₀.f.hom.left.base) (R : RoundData s₀ hf)
    (hfg : ∀ (z : ∀ n, ((toFlatteningSequence R.M s₀ R.d₀ hf).X n).obj.left) n,
      IsLocallyFinitelyGenerated ((toFlatteningSequence R.M s₀ R.d₀ hf).Y 0).obj.left
        (HironakaG10ChowSequenceFibreChain.fibreKernel (toFlatteningSequence R.M s₀ R.d₀ hf) z n)) :
    ∃ (X' : SourceReducedComplexSpace) (σ : X' ⟶ s₀.X) (E : Set X'.obj.left),
      IsNativeBlowupTower s₀.X X' σ ∧ IsClosed E ∧ interior E = ∅ ∧ IsOpenImmersionOn σ Eᶜ ∧
      ∃ (Y' : SourceReducedComplexSpace) (p : Y' ⟶ X') (q : Y' ⟶ s₀.Y),
        IsStrictTransform s₀.f σ E p q ∧ IsFlatMorphism p :=
  exists_flattening_of_roundData s₀ hX hf R (hclosed_of_roundData hP s₀ hf R) hfg

end

end Hironaka.Analytic.Unibranch.HironakaG10HirRoundData
