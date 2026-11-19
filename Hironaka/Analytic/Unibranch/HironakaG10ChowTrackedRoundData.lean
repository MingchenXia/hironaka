import Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum

/-!
# Round data from tracked flatteners transported along permissible steps (Phase C)

Hironaka 1975, Theorem `II_n` (pp. 544–546): within a round the tracked flatteners are transported
along every step (Lemma 4.4.5) and every step is permissible; the round starts with the non-flat
locus tracked and ends with no non-flat point tracked.  Here: the machine form of
`HironakaG10ChowTrackedDatum.principalPullbackAt_of_leave` and the construction of
`HironakaG10ChowLeavingRounds.RoundData` from such tracked rounds.

* `machine_principalPullback_of_leave`;
* `TrackedRounds` — rounds `r k`, tracked data `d k n` on the stages of the run, transported along
  every step of the round, every step a sum centre or avoiding the tracked set, start/finish;
* `TrackedRounds.toRoundData`, `exists_flattening_of_trackedRounds`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry IsLocalRing
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedRoundData

open Hironaka Hironaka
  SourceReducedComplexSpace HironakaG10ChowOneStepStrictTransform
  HironakaG10ChowFlatteningDriver HironakaG10ChowStrictTransformCalculus
  HironakaG10ChowLeavingRounds HironakaG10ChowTrackedDatum HironakaG10ChowCentreMachine
  EmbeddedIdealBlowupNonunitLocus HironakaG10ChowFlatteningReduction HironakaG10ChowTowerDomination
  HironakaG10ChowFlatBimeromorphicIso HironakaG10PNIdealFamily

noncomputable section

variable (M : CentreMachine) (s₀ : Stage) (d₀ : M.St s₀) (hf : IsProperMap s₀.f.hom.left.base)

/-- The transported tracked datum along step `n` of the run of a machine. -/
def stepTransport (n : ℕ) (d : TrackedDatum ((toFlatteningSequence M s₀ d₀ hf).X n)) :
    TrackedDatum ((toFlatteningSequence M s₀ d₀ hf).X (n + 1)) :=
  @TrackedDatum.transport _ _ (centreAt M s₀ d₀ n).B (centreAt M s₀ d₀ n).b
    (centreAt M s₀ d₀ n).finiteType (centreAt M s₀ d₀ n).dense (run M s₀ d₀ n).1.f d

/-- Step `n` of the run is **permissible** for `d` (sum centre for some exponent, or centre avoiding
the tracked set). -/
def StepPermissible (n : ℕ) (d : TrackedDatum ((toFlatteningSequence M s₀ d₀ hf).X n)) : Prop :=
  (∃ β, IsSumCentreFor (centreAt M s₀ d₀ n).B (centreAt M s₀ d₀ n).b (run M s₀ d₀ n).1.f β) ∨
    Disjoint (nonunitLocus (centreAt M s₀ d₀ n).B (centreAt M s₀ d₀ n).b) d.tracked

/-- **Leaving points of a permissible machine step satisfy the leaving condition.** -/
theorem machine_principalPullback_of_leave (n : ℕ)
    (d : TrackedDatum ((toFlatteningSequence M s₀ d₀ hf).X n))
    (hc : StepPermissible M s₀ d₀ hf n d)
    (x' : ((toFlatteningSequence M s₀ d₀ hf).X (n + 1)).obj.left)
    (hx : ((toFlatteningSequence M s₀ d₀ hf).σ n).hom.left.base x' ∈ d.tracked)
    (hx' : x' ∉ (stepTransport M s₀ d₀ hf n d).tracked) :
    PrincipalPullback (toFlatteningSequence M s₀ d₀ hf) n x' := by
  let c := centreAt M s₀ d₀ n
  let _ := c.finiteType
  rcases hc with ⟨β, hβ⟩ | hdisj
  · exact principalPullbackAt_of_leave c.B c.b c.dense (run M s₀ d₀ n).1.f d β (Or.inl hβ) x' hx hx'
  · exact principalPullbackAt_of_leave c.B c.b c.dense (run M s₀ d₀ n).1.f d 0 (Or.inr hdisj) x'
      hx hx'

/-- **Tracked rounds** of a machine run (Hironaka's Theorem `II_n` for a compact base). -/
structure TrackedRounds where
  r : ℕ → ℕ
  hr : ∀ k, r k < r (k + 1)
  d : ℕ → ∀ n, TrackedDatum ((toFlatteningSequence M s₀ d₀ hf).X n)
  transport : ∀ k n, r k ≤ n → n < r (k + 1) →
    (d k (n + 1)).tracked = (stepTransport M s₀ d₀ hf n (d k n)).tracked
  permissible : ∀ k n, r k ≤ n → n < r (k + 1) → StepPermissible M s₀ d₀ hf n (d k n)
  start : ∀ k, (toFlatteningSequence M s₀ d₀ hf).nonflatImage (r k) ⊆ (d k (r k)).tracked
  finish : ∀ k, (toFlatteningSequence M s₀ d₀ hf).nonflatImage (r (k + 1)) ∩
    (d k (r (k + 1))).tracked = ∅

/-- Tracked rounds give round data. -/
def TrackedRounds.toRoundData (T : TrackedRounds M s₀ d₀ hf) : RoundData s₀ hf where
  M := M
  d₀ := d₀
  r := T.r
  hr := T.hr
  Tr k n := (T.d k n).tracked
  start := T.start
  leave k n h1 h2 x' _ hx hx' :=
    machine_principalPullback_of_leave M s₀ d₀ hf n (T.d k n) (T.permissible k n h1 h2) x' hx
      (fun h => hx' ((T.transport k n h1 h2).symm ▸ h))
  finish := T.finish

/-- **Flattening from tracked rounds**: the conclusion of `HironakaFlattening` for `s₀.f` (compact
base, proper `f`) from a centre machine with tracked rounds, closed non-flat images and coherent fibre
kernels of its run. -/
theorem exists_flattening_of_trackedRounds (hX : CompactSpace s₀.X.obj.left)
    (T : TrackedRounds M s₀ d₀ hf)
    (hclosed : ∀ n, IsClosed ((toFlatteningSequence M s₀ d₀ hf).nonflatImage n))
    (hfg : ∀ (z : ∀ n, ((toFlatteningSequence M s₀ d₀ hf).X n).obj.left) n,
      IsLocallyFinitelyGenerated ((toFlatteningSequence M s₀ d₀ hf).Y 0).obj.left
        (HironakaG10ChowSequenceFibreChain.fibreKernel (toFlatteningSequence M s₀ d₀ hf) z n)) :
    ∃ (X' : SourceReducedComplexSpace) (σ : X' ⟶ s₀.X) (E : Set X'.obj.left),
      IsNativeBlowupTower s₀.X X' σ ∧ IsClosed E ∧ interior E = ∅ ∧ IsOpenImmersionOn σ Eᶜ ∧
      ∃ (Y' : SourceReducedComplexSpace) (p : Y' ⟶ X') (q : Y' ⟶ s₀.Y),
        IsStrictTransform s₀.f σ E p q ∧ IsFlatMorphism p :=
  exists_flattening_of_roundData s₀ hX hf (T.toRoundData M s₀ d₀ hf) hclosed hfg

end

end Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedRoundData
