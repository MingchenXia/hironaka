import Hironaka.Analytic.Unibranch.HironakaG10RdPermRun
import Hironaka.Analytic.Unibranch.HironakaG10RdFinish
import Hironaka.Analytic.Unibranch.HironakaG10TmUnitCentre

/-!
# Round data from Theorem `I_n` with `B = X`: the round machine (lane G10RD)

Plan items G10-03-16 and G10-03-17 in conditional form (contract
`work/hironaka-run0081-20261117/G10RD/G10-03-01-double-induction-contract.md` §3.3, §4).  Source:
H. Hironaka, *Flattening theorem in complex-analytic geometry*, Amer. J. Math. 97 (1975), proof of
`I_n ⇒ II_n`, printed pp. 544–546, with `B = Y` (our compact base `X`): at the start of each round new
flatteners `Z_{q+r}` cover `s_1` (p. 544), Theorem `I_n` gives a permissible sequence after which every
tracked flattener is open in `B'`, and Lemma 4.6.1 (p. 545) decreases the fibre at every leaving point.

* `unitStep` — the step with lane G10TM's unit centre `HironakaG10TmUnitCentre.unitCentre` (empty centre) is
  a permissible step of every datum (it pads rounds to positive length);
* `RState`, `machine` — **the round machine**: the state over a stage is the current (F)-datum and the
  remaining permissible run of the current round; when the run is exhausted the machine starts a new round
  with the fresh flatteners `fresh s`, one unit step, and the run `ρ` of Theorem `I_n`;
* `roundBoundary`, `trackedRounds` — the round boundaries and the `TrackedRounds` of the literal run;
* **`nonempty_roundData_of_theoremI`** — `RoundData s₀ hf` for every compact proper family from
  (a) round covers: every stage has finitely many actual local flatteners covering its non-flat image
  (Hironaka p. 544, Th. 2.4 around the strata), and (b) Theorem `I_n` with `B = X`: for every datum with
  `B = X` a permissible run after which every tracked support is open in `B'`.

Neither hypothesis mentions rounds, tracked sets of a run, `RoundData` or any of its fields; they are
Hironaka's Theorem 2.4 (for the strata) and Theorem `I_n` (for `B = Y`).  No named input is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG10RdRoundMachine

open Hironaka Hironaka
  HironakaSingularModuleSheafStalk HironakaG10HirIdealGerms
open Hironaka.Analytic.Unibranch.SourceReducedComplexSpace
  Hironaka.Analytic.Unibranch.HironakaG10ChowOneStepStrictTransform
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver
  Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine
  Hironaka.Analytic.Unibranch.HironakaG10ChowStrictTransformCalculus
  Hironaka.Analytic.Unibranch.HironakaG10ChowStrictFlatLocus
  Hironaka.Analytic.Unibranch.HironakaG10ChowLeavingRounds
  Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum
  Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedRoundData
  Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10SourceCSet
  Hironaka.Analytic.Unibranch.HironakaG10RdPermRun
  Hironaka.Analytic.Unibranch.HironakaG10RdFinish
  Hironaka.Analytic.Unibranch.HironakaG10TmUnitCentre
  Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus

noncomputable section

/-! ### The unit step (the unit centre is lane G10TM's `HironakaG10TmUnitCentre.unitCentre`) -/

/-- **The unit step** of a datum: a permissible step (disjoint from everything). -/
def unitStep {s : Stage} {q : ℕ} (R : FDatum s q) : PermStep R :=
  PermStep.ofDisjoint R (unitCentre s.f)
    (fun x hx => by
      rw [nonunitLocus_unitCentre] at hx
      exact absurd hx (notMem_empty x))
    (by rw [nonunitLocus_unitCentre]; exact empty_subset _)
    (by rw [nonunitLocus_unitCentre]; exact empty_disjoint _)

/-! ### Strict transforms of the whole base -/

theorem strictSet_univ (s : Stage) (c : AdmissibleCentre s.f) :
    strictSet s c (univ : Set s.X.obj.left) = univ := by
  let _ := c.finiteType
  have h : (stepσ s c).hom.left.base ⁻¹' ((univ : Set s.X.obj.left) \ nonunitLocus c.B c.b) =
      (stepExcep c.B c.b c.dense)ᶜ := by
    ext x'
    simp only [mem_preimage, mem_sdiff, mem_univ, true_and, mem_compl_iff]
    rfl
  unfold strictSet
  rw [h, closure_compl, interior_stepExcep, compl_empty]

theorem permStep_next_B_univ {s : Stage} {q : ℕ} {R : FDatum s q} (st : PermStep R)
    (hB : R.B = univ) : st.next.B = univ := by
  rw [st.next_B, hB, strictSet_univ]

theorem permRun_final_B_univ {q : ℕ} : {s : Stage} → {R : FDatum s q} → (l : PermRun s R) →
    R.B = univ → l.final.2.B = univ
  | _, _, .nil _ _, hB => hB
  | _, _, .cons _ _ st rest, hB => permRun_final_B_univ rest (permStep_next_B_univ st hB)

theorem permStep_next_tracked {s : Stage} {q : ℕ} {R : FDatum s q} (st : PermStep R) :
    st.next.tracked.tracked = (R.trackedTransport st.c).tracked := by
  rw [FDatum.tracked_tracked]
  exact iUnion_congr st.next_support

/-! ### The round machine -/

variable (fresh : ∀ s : Stage, Σ m : ℕ, Fin m → LocalFlattener s.f)
  (ρ : ∀ (s : Stage) (q : ℕ) (R : FDatum s q), PermRun s R)

/-- The datum starting a round: the same `B`, the fresh flatteners (Hironaka's `R̃`, p. 544). -/
def roundStart (s : Stage) {q : ℕ} (R : FDatum s q) : FDatum s (fresh s).1 :=
  ⟨R.B, R.closed, (fresh s).2⟩

/-- **The state of the round machine** over a stage: the current (F)-datum and the remaining
permissible run of the current round. -/
structure RState (s : Stage) : Type 1 where
  q : ℕ
  R : FDatum s q
  plan : PermRun s R

/-- The centre chosen from a state: the next centre of the plan, or the unit centre at a round start. -/
def RState.centre {s : Stage} : RState s → AdmissibleCentre s.f
  | ⟨_, _, .cons _ _ st _⟩ => st.c
  | ⟨_, _, .nil _ _⟩ => unitCentre s.f

/-- The next state: pop the plan, or start a new round (fresh flatteners, unit step, run of `ρ`). -/
def RState.next {s : Stage} : (d : RState s) → RState (nextWith s d.centre)
  | ⟨q, _, .cons _ _ st rest⟩ => ⟨q, st.next, rest⟩
  | ⟨_, R, .nil _ _⟩ =>
      ⟨(fresh s).1, (unitStep (roundStart fresh s R)).next,
        ρ _ _ (unitStep (roundStart fresh s R)).next⟩

/-- The tracked datum governing the step taken from a state (the fresh ones at a round start). -/
def RState.startTracked {s : Stage} : RState s → TrackedDatum s.X
  | ⟨_, R, .nil _ _⟩ => (roundStart fresh s R).tracked
  | ⟨_, R, .cons _ _ _ _⟩ => R.tracked

/-- **The round machine.** -/
def machine : CentreMachine where
  St := RState
  centre := fun _ d => d.centre
  upd := fun _ d => d.next fresh ρ

/-- The initial state: the whole base, no tracked flattener, a round starts. -/
def initState (s₀ : Stage) : RState s₀ :=
  ⟨0, ⟨univ, isClosed_univ, fun p => p.elim0⟩, .nil s₀ _⟩

/-! ### One-state lemmas -/

theorem RState.next_tracked {s : Stage} (d : RState s) :
    (d.next fresh ρ).R.tracked.tracked =
      (@TrackedDatum.transport _ _ d.centre.B d.centre.b d.centre.finiteType d.centre.dense s.f
        (d.startTracked fresh)).tracked := by
  obtain ⟨q, R, plan⟩ := d
  cases plan with
  | nil => exact permStep_next_tracked (unitStep (roundStart fresh _ R))
  | cons _ _ st rest => exact permStep_next_tracked st

theorem RState.permissible {s : Stage} (d : RState s) :
    (∃ β, IsSumCentreFor d.centre.B d.centre.b s.f β) ∨
      Disjoint (nonunitLocus d.centre.B d.centre.b) (d.startTracked fresh).tracked := by
  obtain ⟨q, R, plan⟩ := d
  cases plan with
  | nil =>
    refine Or.inr ?_
    show Disjoint (nonunitLocus (unitCentre _).B (unitCentre _).b) _
    rw [nonunitLocus_unitCentre]
    exact empty_disjoint _
  | cons _ _ st rest => exact st.perm

theorem RState.startTracked_of_length_eq_zero {s : Stage} (d : RState s)
    (h : d.plan.length = 0) :
    (d.startTracked fresh).tracked = ⋃ p, ((fresh s).2 p).support := by
  rcases d with ⟨q, R, _ | ⟨_, _, st, rest⟩⟩
  · rfl
  · exact absurd h (Nat.succ_ne_zero _)

theorem RState.startTracked_of_length_ne_zero {s : Stage} (d : RState s)
    (h : d.plan.length ≠ 0) : d.startTracked fresh = d.R.tracked := by
  rcases d with ⟨q, R, _ | ⟨_, _, st, rest⟩⟩
  · exact absurd rfl h
  · rfl

theorem RState.next_length_of_ne_zero {s : Stage} (d : RState s) (h : d.plan.length ≠ 0) :
    (d.next fresh ρ).plan.length = d.plan.length - 1 := by
  rcases d with ⟨q, R, _ | ⟨_, _, st, rest⟩⟩
  · exact absurd rfl h
  · simp only [RState.next, PermRun.length, Nat.add_sub_cancel]

/-- The invariant of the states of the run: `B` is the whole base and the remaining plan ends with open
tracked supports. -/
def RState.Good {s : Stage} (d : RState s) : Prop :=
  d.R.B = univ ∧ d.plan.final.2.B = univ ∧
    ∀ p, IsRelOpen d.plan.final.2.B (d.plan.final.2.Z p).support

variable {fresh ρ}

theorem RState.good_next {s : Stage} (d : RState s) (hd : d.Good)
    (hρ : ∀ {q : ℕ} (R : FDatum (nextWith s (unitCentre s.f)) q), R.B = univ →
      ∀ p, IsRelOpen (ρ _ q R).final.2.B ((ρ _ q R).final.2.Z p).support) :
    (d.next fresh ρ).Good := by
  obtain ⟨q, R, plan⟩ := d
  cases plan with
  | nil =>
    obtain ⟨hB, -, -⟩ := hd
    have hB' : (unitStep (roundStart fresh _ R)).next.B = univ :=
      permStep_next_B_univ (unitStep (roundStart fresh _ R)) hB
    exact ⟨hB', permRun_final_B_univ _ hB', hρ _ hB'⟩
  | cons _ _ st rest =>
    obtain ⟨hB, hfin, hopen⟩ := hd
    exact ⟨permStep_next_B_univ st hB, hfin, hopen⟩

theorem RState.isOpen_of_good {s : Stage} (d : RState s) (hd : d.Good)
    (h : d.plan.length = 0) : ∀ p, IsOpen (d.R.Z p).support := by
  rcases d with ⟨q, R, _ | ⟨_, _, st, rest⟩⟩
  · obtain ⟨hB, -, hopen⟩ := hd
    intro p
    have hp := hopen p
    change IsRelOpen R.B (R.Z p).support at hp
    rw [hB] at hp
    exact isOpen_of_isRelOpen_univ hp
  · exact absurd h (Nat.succ_ne_zero _)

/-! ### The run -/

variable (fresh ρ) (s₀ : Stage) (hf : IsProperMap s₀.f.hom.left.base)

/-- The state of the run at time `n`. -/
abbrev st (n : ℕ) : RState (run (machine fresh ρ) s₀ (initState s₀) n).1 :=
  (run (machine fresh ρ) s₀ (initState s₀) n).2

theorem st_succ (n : ℕ) : st fresh ρ s₀ (n + 1) = (st fresh ρ s₀ n).next fresh ρ := rfl

theorem length_st_zero : (st fresh ρ s₀ 0).plan.length = 0 := rfl

theorem length_st_add (m : ℕ) : ∀ j, j ≤ (st fresh ρ s₀ m).plan.length →
    (st fresh ρ s₀ (m + j)).plan.length = (st fresh ρ s₀ m).plan.length - j
  | 0, _ => rfl
  | j + 1, hj => by
      have ih := length_st_add m j (by omega)
      have hne : (st fresh ρ s₀ (m + j)).plan.length ≠ 0 := by omega
      rw [show m + (j + 1) = m + j + 1 by omega, st_succ,
        RState.next_length_of_ne_zero _ _ _ hne, ih]
      omega

/-- **The round boundaries**: a round starts at `r k` and lasts one unit step plus the run of `ρ`. -/
def roundBoundary : ℕ → ℕ
  | 0 => 0
  | k + 1 => roundBoundary k + 1 + (st fresh ρ s₀ (roundBoundary k + 1)).plan.length

theorem roundBoundary_lt (k : ℕ) : roundBoundary fresh ρ s₀ k < roundBoundary fresh ρ s₀ (k + 1) := by
  simp only [roundBoundary]
  omega

theorem length_st_roundBoundary : ∀ k, (st fresh ρ s₀ (roundBoundary fresh ρ s₀ k)).plan.length = 0
  | 0 => rfl
  | k + 1 => by
      have h := length_st_add fresh ρ s₀ (roundBoundary fresh ρ s₀ k + 1)
        ((st fresh ρ s₀ (roundBoundary fresh ρ s₀ k + 1)).plan.length) le_rfl
      simp only [Nat.sub_self] at h
      exact h

theorem length_st_ne_zero_of_lt (k n : ℕ) (h1 : roundBoundary fresh ρ s₀ k < n)
    (h2 : n < roundBoundary fresh ρ s₀ (k + 1)) : (st fresh ρ s₀ n).plan.length ≠ 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, n = roundBoundary fresh ρ s₀ k + 1 + j := ⟨n - (roundBoundary fresh ρ s₀ k + 1),
    by omega⟩
  have h2' : j < (st fresh ρ s₀ (roundBoundary fresh ρ s₀ k + 1)).plan.length := by
    simp only [roundBoundary] at h2
    omega
  rw [length_st_add fresh ρ s₀ _ j h2'.le]
  omega

/-- The tracked datum of round `k` at time `n` (the end datum at the end of the round, the datum governing
the step otherwise). -/
def roundTracked (k n : ℕ) : TrackedDatum ((toFlatteningSequence (machine fresh ρ) s₀ (initState s₀) hf).X n) :=
  if n = roundBoundary fresh ρ s₀ (k + 1) then (st fresh ρ s₀ n).R.tracked
  else (st fresh ρ s₀ n).startTracked fresh

theorem roundTracked_of_lt (k n : ℕ) (h : n < roundBoundary fresh ρ s₀ (k + 1)) :
    roundTracked fresh ρ s₀ hf k n = (st fresh ρ s₀ n).startTracked fresh := by
  simp only [roundTracked, if_neg (Nat.ne_of_lt h)]

theorem roundTracked_succ (k n : ℕ) (h1 : roundBoundary fresh ρ s₀ k ≤ n)
    (h2 : n < roundBoundary fresh ρ s₀ (k + 1)) :
    roundTracked fresh ρ s₀ hf k (n + 1) = (st fresh ρ s₀ (n + 1)).R.tracked := by
  by_cases he : n + 1 = roundBoundary fresh ρ s₀ (k + 1)
  · simp only [roundTracked, if_pos he]
  · simp only [roundTracked, if_neg he]
    exact RState.startTracked_of_length_ne_zero fresh _
      (length_st_ne_zero_of_lt fresh ρ s₀ k (n + 1) (by omega) (by omega))

/-! ### The invariant along the run -/

theorem compactSpace_nextWith (s : Stage) (c : AdmissibleCentre s.f) [CompactSpace s.X.obj.left] :
    CompactSpace (nextWith s c).X.obj.left := by
  let _ := c.finiteType
  have hc := (OriginalFiniteIdealBlowup.projection_isProperMap c.B c.b c.dense).isCompact_preimage
    (isCompact_univ (X := s.X.obj.left))
  rw [preimage_univ] at hc
  exact ⟨hc⟩

include hf in
theorem good_st (hX : CompactSpace s₀.X.obj.left)
    (hρ : ∀ (s : Stage) (q : ℕ) (R : FDatum s q), CompactSpace s.X.obj.left →
      IsProperMap s.f.hom.left.base → R.B = univ →
        ∀ p, IsRelOpen (ρ s q R).final.2.B ((ρ s q R).final.2.Z p).support) :
    ∀ n, (st fresh ρ s₀ n).Good
  | 0 => ⟨rfl, rfl, fun p => p.elim0⟩
  | n + 1 => by
      rw [st_succ]
      have : CompactSpace (run (machine fresh ρ) s₀ (initState s₀) n).1.X.obj.left :=
        (toFlatteningSequence (machine fresh ρ) s₀ (initState s₀) hf).compactSpace hX n hf
      have hpn := run_proper (machine fresh ρ) s₀ (initState s₀) hf n
      refine RState.good_next _ (good_st hX hρ n) fun R hB => hρ _ _ R ?_ ?_ hB
      · exact compactSpace_nextWith _ _
      · let _ := (unitCentre (run (machine fresh ρ) s₀ (initState s₀) n).1.f).finiteType
        exact strictP_isProperMap _ _ _ _ hpn

theorem roundTracked_end (k : ℕ) :
    roundTracked fresh ρ s₀ hf k (roundBoundary fresh ρ s₀ (k + 1)) =
      (st fresh ρ s₀ (roundBoundary fresh ρ s₀ (k + 1))).R.tracked := by
  unfold roundTracked
  exact if_pos rfl

/-! ### Tracked rounds and round data -/

/-- **The tracked rounds of the round machine** (Hironaka's Theorem `II_n` with `B = Y`, pp. 544–546),
from round covers and Theorem `I_n` with `B = Y`. -/
def trackedRounds (hX : CompactSpace s₀.X.obj.left)
    (hfresh : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      nonflatImage s.f ⊆ ⋃ p, ((fresh s).2 p).support)
    (hρ : ∀ (s : Stage) (q : ℕ) (R : FDatum s q), CompactSpace s.X.obj.left →
      IsProperMap s.f.hom.left.base → R.B = univ →
        ∀ p, IsRelOpen (ρ s q R).final.2.B ((ρ s q R).final.2.Z p).support) :
    TrackedRounds (machine fresh ρ) s₀ (initState s₀) hf where
  r := roundBoundary fresh ρ s₀
  hr := roundBoundary_lt fresh ρ s₀
  d := roundTracked fresh ρ s₀ hf
  transport k n h1 h2 := by
    rw [roundTracked_succ fresh ρ s₀ hf k n h1 h2, roundTracked_of_lt fresh ρ s₀ hf k n h2]
    exact RState.next_tracked fresh ρ (st fresh ρ s₀ n)
  permissible k n _ h2 := by
    rw [roundTracked_of_lt fresh ρ s₀ hf k n h2]
    exact RState.permissible fresh (st fresh ρ s₀ n)
  start k := by
    rw [roundTracked_of_lt fresh ρ s₀ hf k _ (roundBoundary_lt fresh ρ s₀ k),
      RState.startTracked_of_length_eq_zero fresh _ (length_st_roundBoundary fresh ρ s₀ k)]
    exact hfresh _ ((toFlatteningSequence (machine fresh ρ) s₀ (initState s₀) hf).compactSpace hX _ hf)
      (run_proper (machine fresh ρ) s₀ (initState s₀) hf _)
  finish k := by
    rw [roundTracked_end, FDatum.tracked_tracked]
    exact nonflatImage_inter_iUnion_support_eq_empty _ _
      ((st fresh ρ s₀ _).isOpen_of_good (good_st fresh ρ s₀ hf hX hρ _)
        (length_st_roundBoundary fresh ρ s₀ (k + 1)))

end

/-! ### Round data from round covers and Theorem `I_n` -/

noncomputable section Existence

variable {s : Stage}

/-- Fresh round covers chosen from a cover statement. -/
def freshOf (hcover : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∃ (m : ℕ) (Z : Fin m → LocalFlattener s.f), nonflatImage s.f ⊆ ⋃ p, (Z p).support)
    (s : Stage) : Σ m : ℕ, Fin m → LocalFlattener s.f := by
  classical
  exact if h : CompactSpace s.X.obj.left ∧ IsProperMap s.f.hom.left.base then
    ⟨Classical.choose (hcover s h.1 h.2), Classical.choose (Classical.choose_spec (hcover s h.1 h.2))⟩
  else ⟨0, fun p => p.elim0⟩

theorem freshOf_spec (hcover : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∃ (m : ℕ) (Z : Fin m → LocalFlattener s.f), nonflatImage s.f ⊆ ⋃ p, (Z p).support)
    (s : Stage) (h1 : CompactSpace s.X.obj.left) (h2 : IsProperMap s.f.hom.left.base) :
    nonflatImage s.f ⊆ ⋃ p, (((freshOf hcover s).2) p).support := by
  have h : CompactSpace s.X.obj.left ∧ IsProperMap s.f.hom.left.base := ⟨h1, h2⟩
  unfold freshOf
  rw [dif_pos h]
  exact Classical.choose_spec (Classical.choose_spec (hcover s h.1 h.2))

/-- The runs of Theorem `I_n` with `B = Y`, chosen. -/
def runOf (hI : ∀ (s : Stage) (q : ℕ) (R : FDatum s q), CompactSpace s.X.obj.left →
      IsProperMap s.f.hom.left.base → R.B = univ →
        ∃ l : PermRun s R, ∀ p, IsRelOpen l.final.2.B (l.final.2.Z p).support)
    (s : Stage) (q : ℕ) (R : FDatum s q) : PermRun s R := by
  classical
  exact if h : CompactSpace s.X.obj.left ∧ IsProperMap s.f.hom.left.base ∧ R.B = univ then
    Classical.choose (hI s q R h.1 h.2.1 h.2.2) else .nil s R

theorem runOf_spec (hI : ∀ (s : Stage) (q : ℕ) (R : FDatum s q), CompactSpace s.X.obj.left →
      IsProperMap s.f.hom.left.base → R.B = univ →
        ∃ l : PermRun s R, ∀ p, IsRelOpen l.final.2.B (l.final.2.Z p).support)
    (s : Stage) (q : ℕ) (R : FDatum s q) (h1 : CompactSpace s.X.obj.left)
    (h2 : IsProperMap s.f.hom.left.base) (h3 : R.B = univ) :
    ∀ p, IsRelOpen (runOf hI s q R).final.2.B ((runOf hI s q R).final.2.Z p).support := by
  have h : CompactSpace s.X.obj.left ∧ IsProperMap s.f.hom.left.base ∧ R.B = univ := ⟨h1, h2, h3⟩
  unfold runOf
  rw [dif_pos h]
  exact Classical.choose_spec (hI s q R h.1 h.2.1 h.2.2)

/-- **Round data from round covers and Theorem `I_n` with `B = Y`** (Hironaka, proof of `I_n ⇒ II_n`,
pp. 544–546): for a compact base and a proper family, if (a) every stage has finitely many actual local
flatteners whose supports cover its non-flat image (p. 544, Th. 2.4 around the strata), and (b) every
(F)-datum with `B = X` admits a permissible run after which every tracked support is open in the strict
transform of `B` (Theorem `I_n`, p. 540), then round data exist. -/
theorem nonempty_roundData_of_theoremI (s₀ : Stage) (hX : CompactSpace s₀.X.obj.left)
    (hf : IsProperMap s₀.f.hom.left.base)
    (hcover : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∃ (m : ℕ) (Z : Fin m → LocalFlattener s.f), nonflatImage s.f ⊆ ⋃ p, (Z p).support)
    (hI : ∀ (s : Stage) (q : ℕ) (R : FDatum s q), CompactSpace s.X.obj.left →
      IsProperMap s.f.hom.left.base → R.B = univ →
        ∃ l : PermRun s R, ∀ p, IsRelOpen l.final.2.B (l.final.2.Z p).support) :
    Nonempty (RoundData s₀ hf) :=
  ⟨(trackedRounds (freshOf hcover) (runOf hI) s₀ hf hX (freshOf_spec hcover) (runOf_spec hI)).toRoundData
    (machine (freshOf hcover) (runOf hI)) s₀ (initState s₀) hf⟩

end Existence

end Hironaka.Analytic.Unibranch.HironakaG10RdRoundMachine
