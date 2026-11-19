import Hironaka.Analytic.Unibranch.HironakaG10ChowSequenceFibreChain
import Hironaka.Analytic.Unibranch.HironakaG10ChowFibreSurjective

/-!
# Stateful centre machines (module M2 of lane G10H's plan)

Hironaka's flattening algorithm (Hironaka 1975, §4) chooses each centre from data carried along the
sequence (tracked local flatteners, the position in the recursion of Theorems `I_n`, `II_n`), so the
stateless driver `HironakaG10ChowFlatteningDriver.stage rule s₀` cannot express it.  A
`CentreMachine` carries a state `St s` over every stage, chooses an admissible centre from the state
and updates the state along the step (`work/hironaka-resume-20261111/G10H/HIRONAKA75-GLOBAL-STEP.md`
§4, M2; drafted by lane G10H and proved there modulo M1).

* `nextWith`, `CentreMachine`, `run`, `centreAt`, `run_proper`;
* `toFlatteningSequence` — the run as a `FlatteningSequence` (one-step strict transforms,
  `HironakaG10ChowPairInjective.isFlatteningData_step`), `toFlatteningSequence_mapsTo`;
* `machine_stepFibreSurjective` — N6 for every step of every machine
  (`HironakaG10ChowFibreSurjective.strict_fibreSurjective`);
* `exists_flattening_of_machine` (with `hsurj`) and `exists_flattening_of_machine'` (N6 discharged):
  the conclusion of `HironakaFlattening` for `s₀.f` from closed non-flat images, coherent fibre
  kernels and FREQUENT strict decrease along every branch of non-flat points.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine

open Hironaka HironakaG10ChowFibreAlgebra HironakaG10PNIdealFamily
  HironakaG10ChowCompactBranch HironakaG10ChowStrictTransformCalculus
  HironakaG10ChowFlatteningReduction HironakaG10ChowTowerDomination HironakaG10ChowFlatBimeromorphicIso
  HironakaG10ChowFlatteningDriver HironakaG10ChowOneStepStrictTransform HironakaG10ChowStrictFlatLocus

noncomputable section

/-- One step with a given admissible centre (`Stage.next rule s` is `nextWith s (rule s)`). -/
def nextWith (s : Stage) (c : AdmissibleCentre s.f) : Stage :=
  let _ := c.finiteType
  ⟨OriginalFiniteIdealBlowup.sourceObject c.B c.b c.dense, strictSource c.B c.b s.f,
    strictP c.B c.b c.dense s.f⟩

example (rule : ∀ s : Stage, AdmissibleCentre s.f) (s : Stage) :
    Stage.next rule s = nextWith s (rule s) := rfl

/-- A **centre machine**: a state over every stage (Hironaka: the (F)-datum with its tracked local
flatteners and the recursion position), an admissible centre chosen from the state, and the state
of the next stage. -/
structure CentreMachine where
  St : Stage → Type 1
  centre : ∀ s : Stage, St s → AdmissibleCentre s.f
  upd : ∀ (s : Stage) (d : St s), St (nextWith s (centre s d))

variable (M : CentreMachine) (s₀ : Stage) (d₀ : M.St s₀)

/-- The run of a machine. -/
def run : ℕ → Σ s : Stage, M.St s
  | 0 => ⟨s₀, d₀⟩
  | n + 1 => ⟨nextWith (run n).1 (M.centre _ (run n).2), M.upd _ (run n).2⟩

/-- The centre used at step `n`. -/
def centreAt (n : ℕ) : AdmissibleCentre (run M s₀ d₀ n).1.f := M.centre _ (run M s₀ d₀ n).2

theorem run_succ (n : ℕ) :
    (run M s₀ d₀ (n + 1)).1 = nextWith (run M s₀ d₀ n).1 (centreAt M s₀ d₀ n) := rfl

theorem run_proper (hf : IsProperMap s₀.f.hom.left.base) :
    ∀ n, IsProperMap (run M s₀ d₀ n).1.f.hom.left.base
  | 0 => hf
  | n + 1 => by
    let c := centreAt M s₀ d₀ n
    let _ := c.finiteType
    exact strictP_isProperMap c.B c.b c.dense _ (run_proper hf n)

/-- The flattening sequence of a run (pair-injectivity from `strict_pairInjective`). -/
def toFlatteningSequence (hf : IsProperMap s₀.f.hom.left.base) : FlatteningSequence where
  X n := (run M s₀ d₀ n).1.X
  Y n := (run M s₀ d₀ n).1.Y
  f n := (run M s₀ d₀ n).1.f
  σ n := let c := centreAt M s₀ d₀ n; let _ := c.finiteType; stepProj c.B c.b c.dense
  E n := let c := centreAt M s₀ d₀ n; let _ := c.finiteType; stepExcep c.B c.b c.dense
  q n := let c := centreAt M s₀ d₀ n; let _ := c.finiteType; strictQ c.B c.b (run M s₀ d₀ n).1.f
  data n := by
    let c := centreAt M s₀ d₀ n
    let _ := c.finiteType
    exact Hironaka.Analytic.Unibranch.HironakaG10ChowPairInjective.isFlatteningData_step c.B c.b c.dense
      (run M s₀ d₀ n).1.f (run_proper M s₀ d₀ hf n)

/-- Admissible steps map non-flat images into non-flat images (`mapsTo_nonflatImage`). -/
theorem toFlatteningSequence_mapsTo (hf : IsProperMap s₀.f.hom.left.base) (n : ℕ) :
    MapsTo ((toFlatteningSequence M s₀ d₀ hf).σ n).hom.left.base
      ((toFlatteningSequence M s₀ d₀ hf).nonflatImage (n + 1))
      ((toFlatteningSequence M s₀ d₀ hf).nonflatImage n) := by
  let c := centreAt M s₀ d₀ n
  let _ := c.finiteType
  exact Hironaka.Analytic.Unibranch.HironakaG10ChowStrictFlatLocus.mapsTo_nonflatImage c.B c.b c.dense
    (run M s₀ d₀ n).1.f c.admissible

/-- **Flattening by a centre machine** (M2 + M1): the conclusion of `HironakaFlattening` for `s₀.f`
from closed non-flat images, N6 for every step, coherent fibre kernels and frequent strict decrease
along every branch of non-flat points (Hironaka: once per round of `II_n`, Lemma 4.6.1). -/
theorem exists_flattening_of_machine (hX : CompactSpace s₀.X.obj.left)
    (hf : IsProperMap s₀.f.hom.left.base)
    (hclosed : ∀ n, IsClosed ((toFlatteningSequence M s₀ d₀ hf).nonflatImage n))
    (hsurj : ∀ n, HironakaG10ChowSequenceFibreChain.StepFibreSurjective (toFlatteningSequence M s₀ d₀ hf) n)
    (hfg : ∀ (z : ∀ n, ((toFlatteningSequence M s₀ d₀ hf).X n).obj.left) n,
      IsLocallyFinitelyGenerated ((toFlatteningSequence M s₀ d₀ hf).Y 0).obj.left
        (HironakaG10ChowSequenceFibreChain.fibreKernel (toFlatteningSequence M s₀ d₀ hf) z n))
    (hfreq : ∀ z : ∀ n, ((toFlatteningSequence M s₀ d₀ hf).X n).obj.left,
      IsBranch (fun n => ((toFlatteningSequence M s₀ d₀ hf).σ n).hom.left.base)
        (toFlatteningSequence M s₀ d₀ hf).nonflatImage z →
        ∀ N, ∃ m, N ≤ m ∧
          HironakaG10ChowSequenceFibreChain.StepFibreDecreasesAt (toFlatteningSequence M s₀ d₀ hf) m (z (m + 1))) :
    ∃ (X' : SourceReducedComplexSpace) (σ : X' ⟶ s₀.X) (E : Set X'.obj.left),
      IsNativeBlowupTower s₀.X X' σ ∧ IsClosed E ∧ interior E = ∅ ∧ IsOpenImmersionOn σ Eᶜ ∧
      ∃ (Y' : SourceReducedComplexSpace) (p : Y' ⟶ X') (q : Y' ⟶ s₀.Y),
        IsStrictTransform s₀.f σ E p q ∧ IsFlatMorphism p :=
  HironakaG10ChowSequenceFibreChain.exists_flattening_of_frequentDecrease hX hf hclosed
    (toFlatteningSequence_mapsTo M s₀ d₀ hf) hsurj hfg hfreq

/-- **N6 for every step of every centre machine.** -/
theorem machine_stepFibreSurjective (hf : IsProperMap s₀.f.hom.left.base) (n : ℕ) :
    HironakaG10ChowSequenceFibreChain.StepFibreSurjective (toFlatteningSequence M s₀ d₀ hf) n := by
  let c := centreAt M s₀ d₀ n
  let _ := c.finiteType
  intro y b
  exact HironakaG10ChowFibreSurjective.strict_fibreSurjective c.B c.b c.dense (run M s₀ d₀ n).1.f y b

/-- **Flattening by a centre machine, N6 discharged**: the conclusion of `HironakaFlattening` for
`s₀.f` from closed non-flat images, coherent fibre kernels and frequent strict decrease along every
branch of non-flat points. -/
theorem exists_flattening_of_machine' (hX : CompactSpace s₀.X.obj.left)
    (hf : IsProperMap s₀.f.hom.left.base)
    (hclosed : ∀ n, IsClosed ((toFlatteningSequence M s₀ d₀ hf).nonflatImage n))
    (hfg : ∀ (z : ∀ n, ((toFlatteningSequence M s₀ d₀ hf).X n).obj.left) n,
      IsLocallyFinitelyGenerated ((toFlatteningSequence M s₀ d₀ hf).Y 0).obj.left
        (HironakaG10ChowSequenceFibreChain.fibreKernel (toFlatteningSequence M s₀ d₀ hf) z n))
    (hfreq : ∀ z : ∀ n, ((toFlatteningSequence M s₀ d₀ hf).X n).obj.left,
      IsBranch (fun n => ((toFlatteningSequence M s₀ d₀ hf).σ n).hom.left.base)
        (toFlatteningSequence M s₀ d₀ hf).nonflatImage z →
        ∀ N, ∃ m, N ≤ m ∧
          HironakaG10ChowSequenceFibreChain.StepFibreDecreasesAt (toFlatteningSequence M s₀ d₀ hf) m
            (z (m + 1))) :
    ∃ (X' : SourceReducedComplexSpace) (σ : X' ⟶ s₀.X) (E : Set X'.obj.left),
      IsNativeBlowupTower s₀.X X' σ ∧ IsClosed E ∧ interior E = ∅ ∧ IsOpenImmersionOn σ Eᶜ ∧
      ∃ (Y' : SourceReducedComplexSpace) (p : Y' ⟶ X') (q : Y' ⟶ s₀.Y),
        IsStrictTransform s₀.f σ E p q ∧ IsFlatMorphism p :=
  exists_flattening_of_machine M s₀ d₀ hX hf hclosed (machine_stepFibreSurjective M s₀ d₀ hf) hfg hfreq

end

end Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine
