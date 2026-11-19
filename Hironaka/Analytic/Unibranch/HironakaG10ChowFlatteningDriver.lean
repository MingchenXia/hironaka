import Hironaka.Analytic.Unibranch.HironakaG10ChowStrictFlatLocus

/-!
# The flattening algorithm as an iteration of admissible one-step blowups (route N1b, N1c)

Assembly of the global flattening skeleton (route
`work/hironaka-resume-20261111/G10C/GLOBAL-FLATTENING-ROUTE.md`, §§3–4): a *centre rule* assigns to every
proper family `f : Y ⟶ X` an admissible centre — a finite-type ideal with dense unit locus whose
nonunit locus lies in the non-flat image of `f` (Rydh's `U`-admissible blow-ups).  Iterating the
one-step strict transform (`HironakaG10ChowOneStepStrictTransform`) gives a sequence of stages; it is a
`FlatteningSequence` once the strict transforms are pair-injective, and its compatibility hypothesis
holds automatically (`HironakaG10ChowStrictFlatLocus.mapsTo_nonflatImage`).  So the conclusion of
`HironakaFlattening` for `f` follows from: pair-injectivity of the steps, closedness of the non-flat
images, and the absence of infinite branches (`exists_flattening_of_rule`).  These three, and the rule
itself, are the remaining mathematical content (route N2, (4.1), (4.3), §3.3); none is assumed here
beyond the explicit hypotheses of the theorems.

* `isClosed_nonflatImage` — the non-flat image of a proper morphism is closed if its flat locus is
  open (route N1c);
* `AdmissibleCentre`, `Stage`, `Stage.next`, `stage`, `stage_proper`;
* `toFlatteningSequence` — the sequence of one-step rounds;
* **`exists_flattening_of_rule`**.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver

open Hironaka HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  SourceReducedComplexSpace EmbeddedIdealBlowupNonunitLocus HironakaG10ChowTowerDomination
  HironakaG10ChowFlatteningReduction HironakaG10ChowStrictTransformCalculus
  HironakaG10ChowOneStepStrictTransform HironakaG10ChowStrictFlatLocus
  HironakaG10ChowFlatBimeromorphicIso HironakaG10ChowCompactBranch

noncomputable section

/-- **Closedness of the non-flat image** (route N1c): for a proper morphism whose flat locus is
open, the image of the non-flat locus is closed. -/
theorem isClosed_nonflatImage {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (hf : IsProperMap f.hom.left.base)
    (hopen : IsOpen {y : Y.obj.left | (f.hom.left.stalkMap y).hom.Flat}) :
    IsClosed (nonflatImage f) :=
  hf.isClosedMap _ hopen.isClosed_compl

/-- An **admissible centre** for `f : Y ⟶ X`: a finite-type ideal with dense unit locus whose
nonunit locus lies in the non-flat image of `f`. -/
structure AdmissibleCentre {X Y : SourceReducedComplexSpace} (f : Y ⟶ X) where
  B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf)
  b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf)
  finiteType : B.IsFiniteType
  dense : Dense {x : X.obj.left |
    LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊤}
  admissible : nonunitLocus B b ⊆ nonflatImage f

/-- A stage of the algorithm: a family `f : Y ⟶ X`. -/
structure Stage where
  X : SourceReducedComplexSpace
  Y : SourceReducedComplexSpace
  f : Y ⟶ X

namespace Stage

variable (rule : ∀ s : Stage, AdmissibleCentre s.f)

/-- One step: blow up the chosen centre and pass to the strict transform. -/
def next (s : Stage) : Stage :=
  let c := rule s
  let _ := c.finiteType
  ⟨OriginalFiniteIdealBlowup.sourceObject c.B c.b c.dense, strictSource c.B c.b s.f,
    strictP c.B c.b c.dense s.f⟩

/-- The blowup map of a step. -/
def σ (s : Stage) : (next rule s).X ⟶ s.X :=
  let c := rule s
  let _ := c.finiteType
  stepProj c.B c.b c.dense

/-- The exceptional set of a step. -/
def E (s : Stage) : Set (next rule s).X.obj.left :=
  let c := rule s
  let _ := c.finiteType
  stepExcep c.B c.b c.dense

/-- The strict-transform map of a step. -/
def q (s : Stage) : (next rule s).Y ⟶ s.Y :=
  let c := rule s
  let _ := c.finiteType
  strictQ c.B c.b s.f

/-- Pair-injectivity of the strict transform of a step (route N2). -/
def PairInjective (s : Stage) : Prop :=
  ∀ a c : (next rule s).Y.obj.left,
    (next rule s).f.hom.left.base a = (next rule s).f.hom.left.base c →
      (q rule s).hom.left.base a = (q rule s).hom.left.base c → a = c

theorem next_proper (s : Stage) (hf : IsProperMap s.f.hom.left.base) :
    IsProperMap (next rule s).f.hom.left.base := by
  let c := rule s
  let _ := c.finiteType
  exact strictP_isProperMap c.B c.b c.dense s.f hf

theorem isFlatteningData (s : Stage) (hf : IsProperMap s.f.hom.left.base)
    (hpair : PairInjective rule s) :
    IsFlatteningData s.f (σ rule s) (E rule s) (next rule s).f (q rule s) := by
  let c := rule s
  let _ := c.finiteType
  exact isFlatteningData_of_pairInjective c.B c.b c.dense s.f hf hpair

theorem mapsTo_nonflatImage (s : Stage) :
    MapsTo (σ rule s).hom.left.base (nonflatImage (next rule s).f) (nonflatImage s.f) := by
  let c := rule s
  let _ := c.finiteType
  exact HironakaG10ChowStrictFlatLocus.mapsTo_nonflatImage c.B c.b c.dense s.f c.admissible

end Stage

variable (rule : ∀ s : Stage, AdmissibleCentre s.f) (s₀ : Stage)

/-- The `n`-th stage of the algorithm started at `s₀`. -/
def stage : ℕ → Stage
  | 0 => s₀
  | n + 1 => Stage.next rule (stage n)

theorem stage_proper (hf : IsProperMap s₀.f.hom.left.base) :
    ∀ n, IsProperMap (stage rule s₀ n).f.hom.left.base
  | 0 => hf
  | n + 1 => Stage.next_proper rule (stage rule s₀ n) (stage_proper hf n)

/-- **The sequence of one-step rounds** of the algorithm, given pair-injectivity of every step. -/
def toFlatteningSequence (hf : IsProperMap s₀.f.hom.left.base)
    (hpair : ∀ n, Stage.PairInjective rule (stage rule s₀ n)) : FlatteningSequence where
  X n := (stage rule s₀ n).X
  Y n := (stage rule s₀ n).Y
  f n := (stage rule s₀ n).f
  σ n := Stage.σ rule (stage rule s₀ n)
  E n := Stage.E rule (stage rule s₀ n)
  q n := Stage.q rule (stage rule s₀ n)
  data n := Stage.isFlatteningData rule (stage rule s₀ n) (stage_proper rule s₀ hf n) (hpair n)

/-- **Flattening by an admissible centre rule.**  Let `s₀ = (f : Y ⟶ X)` with `X` compact and `f`
proper.  If every step of the algorithm driven by `rule` has a pair-injective strict transform, every
non-flat image is closed, and there is no infinite compatible branch of non-flat points, then `f` has
flattening data with a flat strict transform (the conclusion of `HironakaFlattening` for `f`). -/
theorem exists_flattening_of_rule (hX : CompactSpace s₀.X.obj.left)
    (hf : IsProperMap s₀.f.hom.left.base)
    (hpair : ∀ n, Stage.PairInjective rule (stage rule s₀ n))
    (hclosed : ∀ n, IsClosed (nonflatImage (stage rule s₀ n).f))
    (hno : ∀ s : ∀ n, (stage rule s₀ n).X.obj.left,
      ¬ IsBranch (fun n => (Stage.σ rule (stage rule s₀ n)).hom.left.base)
        (fun n => nonflatImage (stage rule s₀ n).f) s) :
    ∃ (X' : SourceReducedComplexSpace) (σ : X' ⟶ s₀.X) (E : Set X'.obj.left),
      IsNativeBlowupTower s₀.X X' σ ∧ IsClosed E ∧ interior E = ∅ ∧ IsOpenImmersionOn σ Eᶜ ∧
      ∃ (Y' : SourceReducedComplexSpace) (p : Y' ⟶ X') (q : Y' ⟶ s₀.Y),
        IsStrictTransform s₀.f σ E p q ∧ IsFlatMorphism p :=
  (toFlatteningSequence rule s₀ hf hpair).exists_flattening hX hf hclosed
    (fun n => Stage.mapsTo_nonflatImage rule (stage rule s₀ n)) hno

end

end Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver
