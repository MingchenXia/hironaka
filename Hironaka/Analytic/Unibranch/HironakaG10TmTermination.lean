import Hironaka.Analytic.Unibranch.HironakaG10MachineFibreKernel
import Hironaka.Analytic.Unibranch.HironakaG10HirRoundData
import Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedRoundData
import Hironaka.Analytic.Unibranch.HironakaG10SmoothBaseReduction

/-!
# Noether/compactness termination for centre-machine runs and the terminal splices (lane G10TM)

Plan items G10-04-05.b/.c/.d and G10-04-06.a/.b of `THREE-HOUR-GOALS.md` §G10-04 (re-split in
`work/hironaka-run0081-20261117/G10TM/G10-04-01-hclosed-hfg-first-gap.md`).  Source: H. Hironaka,
*Flattening theorem in complex-analytic geometry*, Amer. J. Math. 97 (1975), proof of `I_n ⇒ II_n`,
printed pp. 545–546 ("an infinite sequence of strictly increasing coherent subsheaves … on the compact
complex space `(f^{(i_0)})^{-1}(y^{(i_0)})` … is impossible by a theorem of Cartan").

The coherence of all fibre kernels of every centre-machine run is already proved
(`HironakaG10MachineFibreKernel.machine_fibreKernel_isLocallyFinitelyGenerated`), as are N6
(`machine_stepFibreSurjective`) and the Noether property of the source
(`HironakaG10PNSourceNoether.hasLocalNoetherProperty`).  This module packages them as termination
tools in the form the round recursion (`I_n ⇒ II_n`) consumes, and splices the terminal theorem.

* `machine_not_frequently_fibreDecreases`, `machine_not_frequently_kernelGrowth` — along every
  compatible branch of every machine run the fibre cannot strictly decrease infinitely often (no
  compactness of the base, no hypothesis besides properness of the initial family);
* `machine_exists_eq_empty_of_frequentDecrease` — over a compact base, ARBITRARY closed compatible sets
  `S n` (Hironaka's relative non-flat loci `S^{(i)}`) along whose branches the fibre decreases
  infinitely often are eventually empty;
* `machine_exists_eq_empty_of_rounds` — the same from rounds relative to `S` (start / leave / finish);
* `exists_flattening_of_isFlatMorphism` — a flat stage of any flattening sequence gives the conclusion of
  `HironakaFlattening` for the initial family;
* `machine_exists_flat_of_rounds_while_nonflat`, `exists_flattening_of_persistent_of_rounds_while_nonflat`
  — rounds are needed only while the run is not yet flat (no padding rounds after flatness);
* `machine_exists_flat_of_roundData`, `exists_flattening_of_persistent_of_roundData` — the literal run of
  round data reaches a flat stage; the conclusion of `HironakaFlattening` for `s₀.f` from round data
  and the named input `PersistentLocalFlattener` only (no `hfg`, no `hclosed`);
* `hironakaFlattening_of_roundData`, `hironakaFlattening_of_trackedRounds`,
  `hironakaFlattening_of_smooth_roundData` — `HironakaFlattening` from `PersistentLocalFlattener` and a
  producer of round data (for every compact proper family, resp. tracked rounds, resp. only over
  compact smooth initial bases).

The remaining inputs are exactly G10-01-14 (prove `PersistentLocalFlattener`) and G10-03-17 (produce
`RoundData`).  No named `Prop` is introduced.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10TmTermination

open Hironaka HironakaG10PNIdealFamily HironakaG10ChowCompactBranch
  HironakaG10ChowTrackedRounds
open Hironaka.Analytic.Unibranch
open Hironaka.Analytic.Unibranch.HironakaG10ChowStrictTransformCalculus Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver
  Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningReduction
  Hironaka.Analytic.Unibranch.HironakaG10ChowTowerDomination Hironaka.Analytic.Unibranch.HironakaG10ChowFlatBimeromorphicIso
  Hironaka.Analytic.Unibranch.HironakaG10ChowLeavingRounds Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10ChowSequenceFibreChain Hironaka.Analytic.Unibranch.HironakaG10MachineFibreKernel

noncomputable section

/-! ### Noether termination along branches of a machine run -/

section Machine

variable (M : CentreMachine) (s₀ : Stage) (d₀ : M.St s₀) (hf : IsProperMap s₀.f.hom.left.base)

/-- **No infinitely frequent strict fibre decrease along a compatible branch of a machine run**
(Hironaka p. 546, Cartan's theorem): unconditional, for every centre machine and every compatible
sequence of base points; no compactness of the base is needed. -/
theorem machine_not_frequently_fibreDecreases
    (z : ∀ n, ((toFlatteningSequence M s₀ d₀ hf).X n).obj.left)
    (hz : ∀ n, ((toFlatteningSequence M s₀ d₀ hf).σ n).hom.left.base (z (n + 1)) = z n) :
    ¬ ∀ N, ∃ m, N ≤ m ∧ StepFibreDecreasesAt (toFlatteningSequence M s₀ d₀ hf) m (z (m + 1)) :=
  not_frequently_fibreDecreases' (F := toFlatteningSequence M s₀ d₀ hf) hf
    (machine_stepFibreSurjective M s₀ d₀ hf) z hz
    (machine_fibreKernel_isLocallyFinitelyGenerated M s₀ d₀ hf z)

/-- **Composite form**: along a compatible branch of a machine run the fibre-kernel family over the
fibre of the initial family cannot change between two times infinitely often (no N6 used). -/
theorem machine_not_frequently_kernelGrowth
    (z : ∀ n, ((toFlatteningSequence M s₀ d₀ hf).X n).obj.left)
    (hz : ∀ n, ((toFlatteningSequence M s₀ d₀ hf).σ n).hom.left.base (z (n + 1)) = z n) :
    ¬ ∀ N, ∃ m m', N ≤ m ∧ m < m' ∧ ∃ y : ((toFlatteningSequence M s₀ d₀ hf).Y 0).obj.left,
      ((toFlatteningSequence M s₀ d₀ hf).f 0).hom.left.base y = z 0 ∧
        fibreKernel (toFlatteningSequence M s₀ d₀ hf) z m y ≠
          fibreKernel (toFlatteningSequence M s₀ d₀ hf) z m' y :=
  not_frequently_kernelGrowth' (F := toFlatteningSequence M s₀ d₀ hf) hf z hz
    (machine_fibreKernel_isLocallyFinitelyGenerated M s₀ d₀ hf z)

/-- **Termination for arbitrary closed compatible sets** (Hironaka p. 546, `I_n ⇒ II_n`): over a
compact base, if closed sets `S n` of the stages of a machine run are mapped into each other by the
blowups and the fibre decreases infinitely often along every branch through them, some `S n` is
empty.  (`S n` = the non-flat image gives flatness; Hironaka's `S^{(i)}` are non-flat loci relative to
closed subspaces.) -/
theorem machine_exists_eq_empty_of_frequentDecrease (hX : CompactSpace s₀.X.obj.left)
    (S : ∀ n, Set ((toFlatteningSequence M s₀ d₀ hf).X n).obj.left) (hS : ∀ n, IsClosed (S n))
    (hSπ : ∀ n, MapsTo ((toFlatteningSequence M s₀ d₀ hf).σ n).hom.left.base (S (n + 1)) (S n))
    (hfreq : ∀ z : ∀ n, ((toFlatteningSequence M s₀ d₀ hf).X n).obj.left,
      IsBranch (fun n => ((toFlatteningSequence M s₀ d₀ hf).σ n).hom.left.base) S z →
        ∀ N, ∃ m, N ≤ m ∧ StepFibreDecreasesAt (toFlatteningSequence M s₀ d₀ hf) m (z (m + 1))) :
    ∃ N, S N = ∅ := by
  have hc : ∀ n, CompactSpace ((toFlatteningSequence M s₀ d₀ hf).X n).obj.left :=
    fun n => (toFlatteningSequence M s₀ d₀ hf).compactSpace hX n hf
  have ht : ∀ n, T2Space ((toFlatteningSequence M s₀ d₀ hf).X n).obj.left :=
    fun n => ((toFlatteningSequence M s₀ d₀ hf).X n).property.1
  exact exists_eq_empty_of_forall_not_isBranch
    (S := fun n => ((toFlatteningSequence M s₀ d₀ hf).X n).obj.left)
    (fun n => ((toFlatteningSequence M s₀ d₀ hf).σ n).hom.left.base)
    (fun n => ((toFlatteningSequence M s₀ d₀ hf).σ n).hom.left.base.hom.continuous) S hS hSπ
    (fun z hz => machine_not_frequently_fibreDecreases M s₀ d₀ hf z hz.2 (hfreq z hz))

/-- **Termination from rounds relative to closed compatible sets**: rounds `[r k, r (k+1))` with
tracked sets `Tr k n` that contain `S` at the start of each round, leave it only at points satisfying
the leaving condition (Lemma 4.6.1), and meet `S` nowhere at the end of the round. -/
theorem machine_exists_eq_empty_of_rounds (hX : CompactSpace s₀.X.obj.left)
    (S : ∀ n, Set ((toFlatteningSequence M s₀ d₀ hf).X n).obj.left) (hS : ∀ n, IsClosed (S n))
    (hSπ : ∀ n, MapsTo ((toFlatteningSequence M s₀ d₀ hf).σ n).hom.left.base (S (n + 1)) (S n))
    (r : ℕ → ℕ) (hr : ∀ k, r k < r (k + 1))
    (Tr : ℕ → ∀ n, Set ((toFlatteningSequence M s₀ d₀ hf).X n).obj.left)
    (hstart : ∀ k, S (r k) ⊆ Tr k (r k))
    (hleave : ∀ k n, r k ≤ n → n < r (k + 1) → ∀ x' ∈ S (n + 1),
      ((toFlatteningSequence M s₀ d₀ hf).σ n).hom.left.base x' ∈ Tr k n → x' ∉ Tr k (n + 1) →
        PrincipalPullback (toFlatteningSequence M s₀ d₀ hf) n x')
    (hend : ∀ k, S (r (k + 1)) ∩ Tr k (r (k + 1)) = ∅) :
    ∃ N, S N = ∅ :=
  machine_exists_eq_empty_of_frequentDecrease M s₀ d₀ hf hX S hS hSπ fun z hz =>
    frequently_of_trackedRounds (fun n => ((toFlatteningSequence M s₀ d₀ hf).σ n).hom.left.base) S
      (fun n x' => StepFibreDecreasesAt (toFlatteningSequence M s₀ d₀ hf) n x') r hr Tr hstart
      (fun k n h1 h2 x' hx h3 h4 =>
        stepFibreDecreasesAt_of_principalPullback _ n x' (hleave k n h1 h2 x' hx h3 h4))
      hend z hz

end Machine

/-! ### The terminal splices -/

/-- **A flat stage of a flattening sequence gives the conclusion of `HironakaFlattening`** for the
initial family (the composite tower, exceptional set and strict transform of the first `N` rounds). -/
theorem exists_flattening_of_isFlatMorphism (F : FlatteningSequence)
    (hf : IsProperMap (F.f 0).hom.left.base) {N : ℕ} (hN : IsFlatMorphism (F.f N)) :
    ∃ (X' : SourceReducedComplexSpace) (σ : X' ⟶ F.X 0) (E : Set X'.obj.left),
      IsNativeBlowupTower (F.X 0) X' σ ∧ IsClosed E ∧ interior E = ∅ ∧ IsOpenImmersionOn σ Eᶜ ∧
      ∃ (Y' : SourceReducedComplexSpace) (p : Y' ⟶ X') (q : Y' ⟶ F.Y 0),
        IsStrictTransform (F.f 0) σ E p q ∧ IsFlatMorphism p := by
  have hd := F.isFlatteningData hf N
  exact ⟨F.X N, F.tower N, F.excep N, hd.tower, hd.closed, hd.thin, hd.openImmersion,
    F.Y N, F.f N, F.strict N, hd.strict, hN⟩

/-- **Rounds are needed only while the run is not yet flat**: a machine run over a compact base with
closed non-flat images reaches a flat stage as soon as every round `k` whose END stage `r (k+1)` is still
non-flat has the start / leave / finish properties.  (A producer of rounds need not pad the run with
trivial rounds after flatness.) -/
theorem machine_exists_flat_of_rounds_while_nonflat (M : CentreMachine) (s₀ : Stage) (d₀ : M.St s₀)
    (hf : IsProperMap s₀.f.hom.left.base) (hX : CompactSpace s₀.X.obj.left)
    (hclosed : ∀ n, IsClosed ((toFlatteningSequence M s₀ d₀ hf).nonflatImage n))
    (r : ℕ → ℕ) (hr : ∀ k, r k < r (k + 1))
    (Tr : ℕ → ∀ n, Set ((toFlatteningSequence M s₀ d₀ hf).X n).obj.left)
    (hstart : ∀ k, ((toFlatteningSequence M s₀ d₀ hf).nonflatImage (r (k + 1))).Nonempty →
      (toFlatteningSequence M s₀ d₀ hf).nonflatImage (r k) ⊆ Tr k (r k))
    (hleave : ∀ k, ((toFlatteningSequence M s₀ d₀ hf).nonflatImage (r (k + 1))).Nonempty →
      ∀ n, r k ≤ n → n < r (k + 1) → ∀ x' ∈ (toFlatteningSequence M s₀ d₀ hf).nonflatImage (n + 1),
        ((toFlatteningSequence M s₀ d₀ hf).σ n).hom.left.base x' ∈ Tr k n → x' ∉ Tr k (n + 1) →
          PrincipalPullback (toFlatteningSequence M s₀ d₀ hf) n x')
    (hend : ∀ k, ((toFlatteningSequence M s₀ d₀ hf).nonflatImage (r (k + 1))).Nonempty →
      (toFlatteningSequence M s₀ d₀ hf).nonflatImage (r (k + 1)) ∩ Tr k (r (k + 1)) = ∅) :
    ∃ N, IsFlatMorphism ((toFlatteningSequence M s₀ d₀ hf).f N) := by
  by_contra hno
  have hne : ∀ n, ((toFlatteningSequence M s₀ d₀ hf).nonflatImage n).Nonempty := fun n =>
    nonempty_iff_ne_empty.mpr fun h =>
      hno ⟨n, (toFlatteningSequence M s₀ d₀ hf).isFlatMorphism_of_nonflatImage_eq_empty h⟩
  obtain ⟨N, hN⟩ := machine_exists_eq_empty_of_rounds M s₀ d₀ hf hX
    (toFlatteningSequence M s₀ d₀ hf).nonflatImage hclosed (toFlatteningSequence_mapsTo M s₀ d₀ hf)
    r hr Tr (fun k => hstart k (hne _)) (fun k => hleave k (hne _)) (fun k => hend k (hne _))
  exact (hne N).ne_empty hN


/-- **Flattening from rounds while non-flat and the local input**: the conclusion of
`HironakaFlattening` for `s₀.f` from a machine run whose rounds have the start / leave / finish
properties as long as the run is not yet flat (no `hfg`, no `hclosed`, no padding rounds). -/
theorem exists_flattening_of_persistent_of_rounds_while_nonflat (hP : PersistentLocalFlattener)
    (M : CentreMachine) (s₀ : Stage) (d₀ : M.St s₀)
    (hf : IsProperMap s₀.f.hom.left.base) (hX : CompactSpace s₀.X.obj.left)
    (r : ℕ → ℕ) (hr : ∀ k, r k < r (k + 1))
    (Tr : ℕ → ∀ n, Set ((toFlatteningSequence M s₀ d₀ hf).X n).obj.left)
    (hstart : ∀ k, ((toFlatteningSequence M s₀ d₀ hf).nonflatImage (r (k + 1))).Nonempty →
      (toFlatteningSequence M s₀ d₀ hf).nonflatImage (r k) ⊆ Tr k (r k))
    (hleave : ∀ k, ((toFlatteningSequence M s₀ d₀ hf).nonflatImage (r (k + 1))).Nonempty →
      ∀ n, r k ≤ n → n < r (k + 1) → ∀ x' ∈ (toFlatteningSequence M s₀ d₀ hf).nonflatImage (n + 1),
        ((toFlatteningSequence M s₀ d₀ hf).σ n).hom.left.base x' ∈ Tr k n → x' ∉ Tr k (n + 1) →
          PrincipalPullback (toFlatteningSequence M s₀ d₀ hf) n x')
    (hend : ∀ k, ((toFlatteningSequence M s₀ d₀ hf).nonflatImage (r (k + 1))).Nonempty →
      (toFlatteningSequence M s₀ d₀ hf).nonflatImage (r (k + 1)) ∩ Tr k (r (k + 1)) = ∅) :
    ∃ (X' : SourceReducedComplexSpace) (σ : X' ⟶ s₀.X) (E : Set X'.obj.left),
      IsNativeBlowupTower s₀.X X' σ ∧ IsClosed E ∧ interior E = ∅ ∧ IsOpenImmersionOn σ Eᶜ ∧
      ∃ (Y' : SourceReducedComplexSpace) (p : Y' ⟶ X') (q : Y' ⟶ s₀.Y),
        IsStrictTransform s₀.f σ E p q ∧ IsFlatMorphism p := by
  obtain ⟨N, hN⟩ := machine_exists_flat_of_rounds_while_nonflat M s₀ d₀ hf hX
    (machine_hclosed hP M s₀ d₀ hf) r hr Tr hstart hleave hend
  exact exists_flattening_of_isFlatMorphism (toFlatteningSequence M s₀ d₀ hf) hf hN

/-- **The literal run of round data reaches a flat stage**, given closed non-flat images. -/
theorem machine_exists_flat_of_roundData (s₀ : Stage) (hX : CompactSpace s₀.X.obj.left)
    (hf : IsProperMap s₀.f.hom.left.base) (R : RoundData s₀ hf)
    (hclosed : ∀ n, IsClosed ((toFlatteningSequence R.M s₀ R.d₀ hf).nonflatImage n)) :
    ∃ N, IsFlatMorphism ((toFlatteningSequence R.M s₀ R.d₀ hf).f N) := by
  obtain ⟨N, hN⟩ := machine_exists_eq_empty_of_rounds R.M s₀ R.d₀ hf hX
    (toFlatteningSequence R.M s₀ R.d₀ hf).nonflatImage hclosed
    (toFlatteningSequence_mapsTo R.M s₀ R.d₀ hf) R.r R.hr R.Tr R.start R.leave R.finish
  exact ⟨N, (toFlatteningSequence R.M s₀ R.d₀ hf).isFlatMorphism_of_nonflatImage_eq_empty hN⟩

/-- **The literal run of round data reaches a flat stage**, from the local input. -/
theorem machine_exists_flat_of_persistent_of_roundData (hP : PersistentLocalFlattener) (s₀ : Stage)
    (hX : CompactSpace s₀.X.obj.left) (hf : IsProperMap s₀.f.hom.left.base) (R : RoundData s₀ hf) :
    ∃ N, IsFlatMorphism ((toFlatteningSequence R.M s₀ R.d₀ hf).f N) :=
  machine_exists_flat_of_roundData s₀ hX hf R (machine_hclosed hP R.M s₀ R.d₀ hf)

/-- **Flattening from round data and the local input** (no `hfg`, no `hclosed`): the conclusion of
`HironakaFlattening` for `s₀.f`. -/
theorem exists_flattening_of_persistent_of_roundData (hP : PersistentLocalFlattener) (s₀ : Stage)
    (hX : CompactSpace s₀.X.obj.left) (hf : IsProperMap s₀.f.hom.left.base) (R : RoundData s₀ hf) :
    ∃ (X' : SourceReducedComplexSpace) (σ : X' ⟶ s₀.X) (E : Set X'.obj.left),
      IsNativeBlowupTower s₀.X X' σ ∧ IsClosed E ∧ interior E = ∅ ∧ IsOpenImmersionOn σ Eᶜ ∧
      ∃ (Y' : SourceReducedComplexSpace) (p : Y' ⟶ X') (q : Y' ⟶ s₀.Y),
        IsStrictTransform s₀.f σ E p q ∧ IsFlatMorphism p :=
  HironakaG10MachineFibreKernel.exists_flattening_of_roundData s₀ hX hf R
    (machine_hclosed hP R.M s₀ R.d₀ hf)

/-- **`HironakaFlattening` from the local input and a producer of round data** for every compact
proper family (the outputs of G10-01-14 and G10-03-17). -/
theorem hironakaFlattening_of_roundData (hP : PersistentLocalFlattener)
    (hR : ∀ s₀ : Stage, CompactSpace s₀.X.obj.left →
      ∀ hf : IsProperMap s₀.f.hom.left.base, Nonempty (RoundData s₀ hf)) :
    HironakaFlattening := by
  intro X Y f hX hf
  obtain ⟨R⟩ := hR ⟨X, Y, f⟩ hX hf
  exact exists_flattening_of_persistent_of_roundData hP ⟨X, Y, f⟩ hX hf R

/-- **`HironakaFlattening` from the local input and tracked rounds** (Hironaka's Theorem `II_n` in the
form of `HironakaG10ChowTrackedRoundData.TrackedRounds`). -/
theorem hironakaFlattening_of_trackedRounds (hP : PersistentLocalFlattener)
    (hT : ∀ s₀ : Stage, CompactSpace s₀.X.obj.left → ∀ hf : IsProperMap s₀.f.hom.left.base,
      ∃ (M : CentreMachine) (d₀ : M.St s₀),
        Nonempty (HironakaG10ChowTrackedRoundData.TrackedRounds M s₀ d₀ hf)) :
    HironakaFlattening :=
  hironakaFlattening_of_roundData hP fun s₀ hX hf => by
    obtain ⟨M, d₀, ⟨T⟩⟩ := hT s₀ hX hf
    exact ⟨T.toRoundData M s₀ d₀ hf⟩

/-- **`HironakaFlattening` from the local input and round data over compact SMOOTH initial bases
only** (the G11 resolution `HironakaG10SmoothBaseReduction.hironakaFlattening_of_smooth_initialBase`
handles a singular initial base; later stages of the run need no smoothness). -/
theorem hironakaFlattening_of_smooth_roundData (hP : PersistentLocalFlattener)
    (hR : ∀ s₀ : Stage, CompactSpace s₀.X.obj.left → SourceReducedComplexSpace.IsSmooth s₀.X →
      ∀ hf : IsProperMap s₀.f.hom.left.base, Nonempty (RoundData s₀ hf)) :
    HironakaFlattening :=
  HironakaG10SmoothBaseReduction.hironakaFlattening_of_smooth_initialBase fun X Y f hX hXs hf => by
    obtain ⟨R⟩ := hR ⟨X, Y, f⟩ hX hXs hf
    exact exists_flattening_of_persistent_of_roundData hP ⟨X, Y, f⟩ hX hf R

end

end Hironaka.Analytic.Unibranch.HironakaG10TmTermination
