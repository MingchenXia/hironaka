import Hironaka.Analytic.Unibranch.HironakaG10RdRoundMachine
import Hironaka.Analytic.Unibranch.HironakaG10RdRelativeStep
import Hironaka.Analytic.Unibranch.HironakaG10TmTermination

/-!
# Theorem `II_n` from Theorem `I_n` relative to a closed set `B` (lane G10RD)

Plan item G10-03-15.a (conditional form; contract `G10-03-01-double-induction-contract.md` §3.2).  Source:
H. Hironaka, *Flattening theorem in complex-analytic geometry*, Amer. J. Math. 97 (1975), proof of
`I_n ⇒ II_n`, printed pp. 544–546, for an arbitrary (F)-datum `R = (F, f; B; V_p, Z_p)`: each round adds
flatteners `Z_{q+r}` around the strata of `f/B`, runs Theorem `I_n` on `R̃`, and keeps the `q` original
flatteners; Lemma 4.6.1 and Cartan bound the number of rounds.

* `PermStep.restrict`, `trackedTransport_Z_congr` — a step permissible for a datum is permissible for any
  datum whose flatteners are among its own (re-indexing);
* `RelState`, `relMachine` — the relative round machine (state: a datum with `q` kept flatteners followed by
  the fresh ones of the current round, and the remaining run);
* `RelState.baseRun` — the first `N` steps of the run read as a permissible run of the KEPT datum;
* **`exists_flatOverB_of_theoremI`** — for a compact base, a proper family and an (F)-datum whose `B` satisfies
  a property `D` stable under strict transforms (in the application: `dim B ≤ n`), if (a) relative round
  covers exist (finitely many actual local flatteners covering `s_1(f/B)` for closed `B`), and (b) Theorem `I_n`
  holds for every datum whose `B` satisfies `D`, then the datum admits a permissible run after which `f` is flat
  over `B'` (Theorem `II_n`), given the local input `PersistentLocalFlattener` (closedness of the relative
  non-flat sets).

Termination: the relative form of Hironaka's Cartan argument is lane G10TM's
`HironakaG10TmTermination.machine_exists_eq_empty_of_rounds`, fed with `S n = s_1(f_n/B_n)`, whose closedness and
compatibility are `HironakaG10RdRelativeStep.isClosed_relNonflat` and `PermStep.mapsTo_relNonflat`.
No named input is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG10RdRelativeRounds

open Hironaka Hironaka
  HironakaSingularModuleSheafStalk HironakaG10ChowCompactBranch HironakaG10ChowTrackedRounds
open Hironaka.Analytic.Unibranch.SourceReducedComplexSpace
  Hironaka.Analytic.Unibranch.HironakaG10ChowOneStepStrictTransform
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver
  Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine
  Hironaka.Analytic.Unibranch.HironakaG10ChowStrictTransformCalculus
  Hironaka.Analytic.Unibranch.HironakaG10ChowStrictFlatLocus
  Hironaka.Analytic.Unibranch.HironakaG10ChowLeavingRounds
  Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum
  Hironaka.Analytic.Unibranch.HironakaG10ChowSequenceFibreChain
  Hironaka.Analytic.Unibranch.HironakaG10MachineFibreKernel
  Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10SourceCSet
  Hironaka.Analytic.Unibranch.HironakaG10CSetRelativeFlat
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
  Hironaka.Analytic.Unibranch.HironakaG10RdPermRun
  Hironaka.Analytic.Unibranch.HironakaG10RdRoundMachine
  Hironaka.Analytic.Unibranch.HironakaG10RdRelativeStep
  Hironaka.Analytic.Unibranch.HironakaG10TmUnitCentre
  Hironaka.Analytic.Unibranch.HironakaG10TmTermination
  Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus

noncomputable section

/-! ### Re-indexing tracked flatteners -/

/-- **A step permissible for `R'` is permissible for every datum `R` with the same `B` whose flatteners
are among those of `R'`.** -/
def PermStep.restrict {s : Stage} {q q' : ℕ} {R' : FDatum s q'} (R : FDatum s q) (ι : Fin q → Fin q')
    (hZ : ∀ p, R.Z p = R'.Z (ι p)) (hB : R.B = R'.B) (st : PermStep R') : PermStep R where
  c := st.c
  flat := st.flat
  sub := hB ▸ st.sub
  perm := st.perm.imp id fun h => h.mono_right fun x hx => by
    obtain ⟨p, hp⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨ι p, show x ∈ (R'.Z (ι p)).support from hZ p ▸ hp⟩
  next := ⟨st.next.B, st.next.closed, fun p => st.next.Z (ι p)⟩
  next_B := by
    show st.next.B = strictSet s st.c R.B
    rw [st.next_B, hB]
  next_support := fun p => (st.next_support (ι p)).trans
    (trackedTransport_Z_congr st.c (by rw [hZ p])).symm


/-! ### The relative round machine -/

variable (q : ℕ) (fresh : ∀ s : Stage, Set s.X.obj.left → Σ m : ℕ, Fin m → LocalFlattener s.f)
  (ρ : ∀ (s : Stage) (q' : ℕ) (R : FDatum s q'), PermRun s R)

/-- The datum starting a relative round: the kept flatteners followed by fresh ones around the strata of
`f/B` (Hironaka's `R̃`, p. 544). -/
def relRoundStart {s : Stage} (R : FDatum s q) : FDatum s (q + (fresh s R.B).1) :=
  ⟨R.B, R.closed, Fin.append R.Z (fresh s R.B).2⟩

/-- **The state of the relative round machine**: a datum with the `q` kept flatteners followed by `m`
fresh ones, and the remaining run of the current round. -/
structure RelState (s : Stage) : Type 1 where
  m : ℕ
  R : FDatum s (q + m)
  plan : PermRun s R

variable {q}

/-- The kept datum of a state. -/
def RelState.base {s : Stage} (d : RelState q s) : FDatum s q :=
  ⟨d.R.B, d.R.closed, fun p => d.R.Z (Fin.castAdd d.m p)⟩

def RelState.centre {s : Stage} : RelState q s → AdmissibleCentre s.f
  | ⟨_, _, .cons _ _ st _⟩ => st.c
  | ⟨_, _, .nil _ _⟩ => unitCentre s.f

def RelState.next {s : Stage} : (d : RelState q s) → RelState q (nextWith s d.centre)
  | ⟨m, _, .cons _ _ st rest⟩ => ⟨m, st.next, rest⟩
  | ⟨m, R, .nil _ _⟩ =>
      ⟨(fresh s R.B).1,
        (unitStep (relRoundStart q fresh (⟨R.B, R.closed, fun p => R.Z (Fin.castAdd m p)⟩ :
          FDatum s q))).next,
        ρ _ _ (unitStep (relRoundStart q fresh (⟨R.B, R.closed, fun p => R.Z (Fin.castAdd m p)⟩ :
          FDatum s q))).next⟩

def RelState.startTracked {s : Stage} : RelState q s → TrackedDatum s.X
  | ⟨m, R, .nil _ _⟩ =>
      (relRoundStart q fresh (⟨R.B, R.closed, fun p => R.Z (Fin.castAdd m p)⟩ : FDatum s q)).tracked
  | ⟨_, R, .cons _ _ _ _⟩ => R.tracked

/-- **The relative round machine.** -/
def relMachine : CentreMachine where
  St := RelState q
  centre := fun _ d => d.centre
  upd := fun _ d => d.next fresh ρ

/-- The initial state of a datum `R₀`: a round starts. -/
def relInit {s₀ : Stage} (R₀ : FDatum s₀ q) : RelState q s₀ :=
  ⟨0, ⟨R₀.B, R₀.closed, R₀.Z⟩, .nil s₀ _⟩

/-! ### The kept run -/

/-- **The first `N` steps of the run as a permissible run of the kept datum.** -/
def RelState.baseRun : {s : Stage} → (d : RelState q s) → ℕ → PermRun s d.base
  | _, _, 0 => .nil _ _
  | s, ⟨m, R, .cons _ _ st rest⟩, N + 1 =>
      .cons s _ (PermStep.restrict (⟨R.B, R.closed, fun p => R.Z (Fin.castAdd m p)⟩ : FDatum s q)
          (Fin.castAdd m) (fun _ => rfl) rfl st)
        (RelState.baseRun (s := nextWith s st.c) ⟨m, st.next, rest⟩ N)
  | s, ⟨m, R, .nil _ _⟩, N + 1 =>
      .cons s _ (PermStep.restrict (⟨R.B, R.closed, fun p => R.Z (Fin.castAdd m p)⟩ : FDatum s q)
          (Fin.castAdd (fresh s R.B).1) (fun p => (Fin.append_left _ _ p).symm) rfl
          (unitStep (relRoundStart q fresh (⟨R.B, R.closed, fun p => R.Z (Fin.castAdd m p)⟩ :
            FDatum s q))))
        (RelState.baseRun (s := nextWith s (unitCentre s.f))
          ((⟨m, R, .nil _ _⟩ : RelState q s).next fresh ρ) N)

theorem RelState.baseRun_final_succ {s : Stage} (d : RelState q s) (N : ℕ) :
    (d.baseRun fresh ρ (N + 1)).final = ((d.next fresh ρ).baseRun fresh ρ N).final := by
  obtain ⟨m, R, plan⟩ := d
  cases plan with
  | nil => rfl
  | cons _ _ st rest => rfl

/-! ### One-state lemmas -/

theorem RelState.next_tracked {s : Stage} (d : RelState q s) :
    (d.next fresh ρ).R.tracked.tracked =
      (@TrackedDatum.transport _ _ d.centre.B d.centre.b d.centre.finiteType d.centre.dense s.f
        (d.startTracked fresh)).tracked := by
  obtain ⟨m, R, plan⟩ := d
  cases plan with
  | nil => exact permStep_next_tracked (unitStep _)
  | cons _ _ st rest => exact permStep_next_tracked st

theorem RelState.mapsTo {s : Stage} (d : RelState q s) :
    MapsTo (stepσ s d.centre).hom.left.base (relNonflat (nextWith s d.centre).f (d.next fresh ρ).R.B)
      (relNonflat s.f d.R.B) := by
  obtain ⟨m, R, plan⟩ := d
  cases plan with
  | nil => exact PermStep.mapsTo_relNonflat (unitStep _)
  | cons _ _ st rest => exact PermStep.mapsTo_relNonflat st

theorem RelState.principalPullbackAt_of_leave {s : Stage} (d : RelState q s)
    (x' : (nextWith s d.centre).X.obj.left)
    (hx : (stepσ s d.centre).hom.left.base x' ∈ (d.startTracked fresh).tracked)
    (hx' : x' ∉ (d.next fresh ρ).R.tracked.tracked) :
    PrincipalPullbackAt s.f (stepσ s d.centre) (nextWith s d.centre).f x' := by
  obtain ⟨m, R, plan⟩ := d
  cases plan with
  | nil => exact (unitStep _).principalPullbackAt_of_leave x' hx hx'
  | cons _ _ st rest => exact st.principalPullbackAt_of_leave x' hx hx'

theorem RelState.startTracked_of_length_eq_zero {s : Stage} (d : RelState q s)
    (h : d.plan.length = 0) :
    relNonflat s.f d.R.B ⊆ ⋃ p, ((fresh s d.R.B).2 p).support →
      relNonflat s.f d.R.B ⊆ (d.startTracked fresh).tracked := by
  obtain ⟨m, R, plan⟩ := d
  cases plan with
  | nil =>
    intro hcov x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcov hx)
    refine mem_iUnion.mpr ⟨Fin.natAdd q j, ?_⟩
    show x ∈ (Fin.append _ (fresh _ R.B).2 (Fin.natAdd q j)).support
    rw [Fin.append_right]
    exact hj
  | cons _ _ st rest => exact absurd h (Nat.succ_ne_zero _)

theorem RelState.startTracked_of_length_ne_zero {s : Stage} (d : RelState q s)
    (h : d.plan.length ≠ 0) : d.startTracked fresh = d.R.tracked := by
  obtain ⟨m, R, plan⟩ := d
  cases plan with
  | nil => exact absurd rfl h
  | cons _ _ st rest => rfl

theorem RelState.next_length_of_ne_zero {s : Stage} (d : RelState q s) (h : d.plan.length ≠ 0) :
    (d.next fresh ρ).plan.length = d.plan.length - 1 := by
  obtain ⟨m, R, plan⟩ := d
  cases plan with
  | nil => exact absurd rfl h
  | cons _ _ st rest => simp only [RelState.next, PermRun.length, Nat.add_sub_cancel]

/-- The invariant: `B` satisfies `D` and the remaining plan ends with relatively open tracked supports. -/
def RelState.Good (D : ∀ s : Stage, Set s.X.obj.left → Prop) {s : Stage} (d : RelState q s) : Prop :=
  D s d.R.B ∧ ∀ p, IsRelOpen d.plan.final.2.B (d.plan.final.2.Z p).support

variable {fresh ρ}

theorem permRun_final_D (D : ∀ s : Stage, Set s.X.obj.left → Prop)
    (hD : ∀ (s : Stage) (c : AdmissibleCentre s.f) (B : Set s.X.obj.left), D s B →
      D (nextWith s c) (strictSet s c B)) {q' : ℕ} :
    {s : Stage} → {R : FDatum s q'} → (l : PermRun s R) → D s R.B → D l.final.1 l.final.2.B
  | _, _, .nil _ _, h => h
  | s, _, .cons _ _ st rest, h =>
      permRun_final_D D hD rest (st.next_B ▸ hD s st.c _ h)

theorem RelState.good_next (D : ∀ s : Stage, Set s.X.obj.left → Prop)
    (hD : ∀ (s : Stage) (c : AdmissibleCentre s.f) (B : Set s.X.obj.left), D s B →
      D (nextWith s c) (strictSet s c B))
    {s : Stage} (d : RelState q s) (hB : D s d.R.B)
    (hopen : d.plan.length ≠ 0 → ∀ p, IsRelOpen d.plan.final.2.B (d.plan.final.2.Z p).support)
    (hρ : ∀ {q' : ℕ} (R : FDatum (nextWith s (unitCentre s.f)) q'),
      D (nextWith s (unitCentre s.f)) R.B →
        ∀ p, IsRelOpen (ρ _ q' R).final.2.B ((ρ _ q' R).final.2.Z p).support) :
    (d.next fresh ρ).Good D := by
  obtain ⟨m, R, plan⟩ := d
  cases plan with
  | nil =>
    have hB' := (unitStep (relRoundStart q fresh (⟨R.B, R.closed, fun p => R.Z (Fin.castAdd m p)⟩ :
      FDatum _ q))).next_B ▸ hD _ (unitCentre _) _ hB
    exact ⟨hB', hρ _ hB'⟩
  | cons _ _ st rest =>
    exact ⟨st.next_B ▸ hD _ st.c _ hB, hopen (Nat.succ_ne_zero _)⟩

theorem RelState.relNonflat_inter_eq_empty_of_good (D : ∀ s : Stage, Set s.X.obj.left → Prop)
    {s : Stage} (d : RelState q s) (hd : d.Good D) (h : d.plan.length = 0) :
    relNonflat s.f d.R.B ∩ d.R.tracked.tracked = ∅ := by
  obtain ⟨m, R, plan⟩ := d
  cases plan with
  | nil =>
    obtain ⟨-, hopen⟩ := hd
    rw [FDatum.tracked_tracked, inter_iUnion, iUnion_eq_empty]
    exact fun p => relNonflat_disjoint_support_of_relOpen s.f (R.Z p) R.B (hopen p)
  | cons _ _ st rest => exact absurd h (Nat.succ_ne_zero _)

/-! ### The relative run -/

variable (fresh ρ) {s₀ : Stage} (R₀ : FDatum s₀ q) (hf : IsProperMap s₀.f.hom.left.base)

/-- The state of the relative run at time `n`. -/
abbrev rst (n : ℕ) : RelState q (run (relMachine fresh ρ) s₀ (relInit R₀) n).1 :=
  (run (relMachine fresh ρ) s₀ (relInit R₀) n).2

theorem rst_succ (n : ℕ) : rst fresh ρ R₀ (n + 1) = (rst fresh ρ R₀ n).next fresh ρ := rfl

theorem length_rst_add (k : ℕ) : ∀ j, j ≤ (rst fresh ρ R₀ k).plan.length →
    (rst fresh ρ R₀ (k + j)).plan.length = (rst fresh ρ R₀ k).plan.length - j
  | 0, _ => rfl
  | j + 1, hj => by
      have ih := length_rst_add k j (by omega)
      have hne : (rst fresh ρ R₀ (k + j)).plan.length ≠ 0 := by omega
      rw [show k + (j + 1) = k + j + 1 by omega, rst_succ,
        RelState.next_length_of_ne_zero _ _ _ hne, ih]
      omega

/-- The round boundaries of the relative run. -/
def relBoundary : ℕ → ℕ
  | 0 => 0
  | k + 1 => relBoundary k + 1 + (rst fresh ρ R₀ (relBoundary k + 1)).plan.length

theorem relBoundary_lt (k : ℕ) : relBoundary fresh ρ R₀ k < relBoundary fresh ρ R₀ (k + 1) := by
  simp only [relBoundary]
  omega

theorem length_rst_relBoundary : ∀ k, (rst fresh ρ R₀ (relBoundary fresh ρ R₀ k)).plan.length = 0
  | 0 => rfl
  | k + 1 => by
      have h := length_rst_add fresh ρ R₀ (relBoundary fresh ρ R₀ k + 1)
        ((rst fresh ρ R₀ (relBoundary fresh ρ R₀ k + 1)).plan.length) le_rfl
      simp only [Nat.sub_self] at h
      exact h

theorem length_rst_ne_zero_of_lt (k n : ℕ) (h1 : relBoundary fresh ρ R₀ k < n)
    (h2 : n < relBoundary fresh ρ R₀ (k + 1)) : (rst fresh ρ R₀ n).plan.length ≠ 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, n = relBoundary fresh ρ R₀ k + 1 + j :=
    ⟨n - (relBoundary fresh ρ R₀ k + 1), by omega⟩
  have h2' : j < (rst fresh ρ R₀ (relBoundary fresh ρ R₀ k + 1)).plan.length := by
    simp only [relBoundary] at h2
    omega
  rw [length_rst_add fresh ρ R₀ _ j h2'.le]
  omega

/-- The tracked set of round `k` at time `n`. -/
def relTracked (k n : ℕ) :
    Set ((toFlatteningSequence (relMachine fresh ρ) s₀ (relInit R₀) hf).X n).obj.left :=
  if n = relBoundary fresh ρ R₀ (k + 1) then (rst fresh ρ R₀ n).R.tracked.tracked
  else ((rst fresh ρ R₀ n).startTracked fresh).tracked

theorem relTracked_of_lt (k n : ℕ) (h : n < relBoundary fresh ρ R₀ (k + 1)) :
    relTracked fresh ρ R₀ hf k n = ((rst fresh ρ R₀ n).startTracked fresh).tracked := by
  unfold relTracked
  exact if_neg (Nat.ne_of_lt h)

theorem relTracked_succ (k n : ℕ) (h1 : relBoundary fresh ρ R₀ k ≤ n)
    (h2 : n < relBoundary fresh ρ R₀ (k + 1)) :
    relTracked fresh ρ R₀ hf k (n + 1) = (rst fresh ρ R₀ (n + 1)).R.tracked.tracked := by
  by_cases he : n + 1 = relBoundary fresh ρ R₀ (k + 1)
  · unfold relTracked
    exact if_pos he
  · unfold relTracked
    rw [if_neg he, RelState.startTracked_of_length_ne_zero fresh _
      (length_rst_ne_zero_of_lt fresh ρ R₀ k (n + 1) (by omega) (by omega))]

theorem relTracked_end (k : ℕ) :
    relTracked fresh ρ R₀ hf k (relBoundary fresh ρ R₀ (k + 1)) =
      (rst fresh ρ R₀ (relBoundary fresh ρ R₀ (k + 1))).R.tracked.tracked := by
  unfold relTracked
  exact if_pos rfl

theorem baseRun_final (N : ℕ) : ∀ k, ((rst fresh ρ R₀ k).baseRun fresh ρ N).final =
    ⟨(run (relMachine fresh ρ) s₀ (relInit R₀) (k + N)).1, (rst fresh ρ R₀ (k + N)).base⟩ := by
  induction N with
  | zero => intro k; rfl
  | succ N ih =>
    intro k
    rw [RelState.baseRun_final_succ, ← rst_succ, ih (k + 1), show k + 1 + N = k + (N + 1) by omega]

include hf in
/-- The invariant holds at every positive time (time `0` is a round start). -/
theorem good_rst (D : ∀ s : Stage, Set s.X.obj.left → Prop)
    (hD : ∀ (s : Stage) (c : AdmissibleCentre s.f) (B : Set s.X.obj.left), D s B →
      D (nextWith s c) (strictSet s c B))
    (hX : CompactSpace s₀.X.obj.left) (hD₀ : D s₀ R₀.B)
    (hρ : ∀ (s : Stage) (q' : ℕ) (R : FDatum s q'), CompactSpace s.X.obj.left →
      IsProperMap s.f.hom.left.base → D s R.B →
        ∀ p, IsRelOpen (ρ s q' R).final.2.B ((ρ s q' R).final.2.Z p).support) :
    ∀ n, (rst fresh ρ R₀ (n + 1)).Good D := by
  have step : ∀ n, D _ (rst fresh ρ R₀ n).R.B →
      ((rst fresh ρ R₀ n).plan.length ≠ 0 → ∀ p, IsRelOpen (rst fresh ρ R₀ n).plan.final.2.B
        ((rst fresh ρ R₀ n).plan.final.2.Z p).support) → (rst fresh ρ R₀ (n + 1)).Good D := by
    intro n hB hopen
    rw [rst_succ]
    have : CompactSpace (run (relMachine fresh ρ) s₀ (relInit R₀) n).1.X.obj.left :=
      (toFlatteningSequence (relMachine fresh ρ) s₀ (relInit R₀) hf).compactSpace hX n hf
    have hpn := run_proper (relMachine fresh ρ) s₀ (relInit R₀) hf n
    refine RelState.good_next D hD _ hB hopen fun R hB' => hρ _ _ R ?_ ?_ hB'
    · exact compactSpace_nextWith _ _
    · let _ := (unitCentre (run (relMachine fresh ρ) s₀ (relInit R₀) n).1.f).finiteType
      exact strictP_isProperMap _ _ _ _ hpn
  intro n
  induction n with
  | zero => exact step 0 hD₀ fun h => absurd rfl h
  | succ n ih => exact step (n + 1) ih.1 fun _ => ih.2

include hf in
/-- **Theorem `II_n` from Theorem `I_n`, relative form, with given covers and runs.** -/
theorem exists_flatOverB_of_runs (hP : PersistentLocalFlattener)
    (D : ∀ s : Stage, Set s.X.obj.left → Prop)
    (hD : ∀ (s : Stage) (c : AdmissibleCentre s.f) (B : Set s.X.obj.left), D s B →
      D (nextWith s c) (strictSet s c B))
    (hX : CompactSpace s₀.X.obj.left) (hD₀ : D s₀ R₀.B)
    (hfresh : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ B : Set s.X.obj.left, IsClosed B → relNonflat s.f B ⊆ ⋃ p, ((fresh s B).2 p).support)
    (hρ : ∀ (s : Stage) (q' : ℕ) (R : FDatum s q'), CompactSpace s.X.obj.left →
      IsProperMap s.f.hom.left.base → D s R.B →
        ∀ p, IsRelOpen (ρ s q' R).final.2.B ((ρ s q' R).final.2.Z p).support) :
    ∃ N, FlatOverB (((rst fresh ρ R₀ 0).baseRun fresh ρ N).final.2) := by
  let F := toFlatteningSequence (relMachine fresh ρ) s₀ (relInit R₀) hf
  have hc : ∀ n, CompactSpace (F.X n).obj.left := fun n => F.compactSpace hX n hf
  have hp : ∀ n, IsProperMap (F.f n).hom.left.base :=
    run_proper (relMachine fresh ρ) s₀ (relInit R₀) hf
  obtain ⟨N, hN⟩ := machine_exists_eq_empty_of_rounds (relMachine fresh ρ) s₀ (relInit R₀) hf hX
    (fun n => relNonflat (F.f n) (rst fresh ρ R₀ n).R.B)
    (fun n => isClosed_relNonflat hP _ (hp n) (rst fresh ρ R₀ n).R.closed)
    (fun n => RelState.mapsTo fresh ρ (rst fresh ρ R₀ n))
    (relBoundary fresh ρ R₀) (relBoundary_lt fresh ρ R₀) (relTracked fresh ρ R₀ hf)
    (fun k => by
      rw [relTracked_of_lt fresh ρ R₀ hf k _ (relBoundary_lt fresh ρ R₀ k)]
      exact RelState.startTracked_of_length_eq_zero fresh _ (length_rst_relBoundary fresh ρ R₀ k)
        (hfresh _ (hc _) (hp _) _ (rst fresh ρ R₀ _).R.closed))
    (fun k n h1 h2 x' _ hx hx' => by
      rw [relTracked_of_lt fresh ρ R₀ hf k n h2] at hx
      rw [relTracked_succ fresh ρ R₀ hf k n h1 h2] at hx'
      exact RelState.principalPullbackAt_of_leave fresh ρ (rst fresh ρ R₀ n) x' hx hx')
    (fun k => by
      rw [relTracked_end]
      obtain ⟨m, hm⟩ : ∃ m, relBoundary fresh ρ R₀ (k + 1) = m + 1 :=
        ⟨relBoundary fresh ρ R₀ (k + 1) - 1, by have := relBoundary_lt fresh ρ R₀ k; omega⟩
      have hlen := length_rst_relBoundary fresh ρ R₀ (k + 1)
      rw [hm] at hlen ⊢
      exact RelState.relNonflat_inter_eq_empty_of_good D _
        (good_rst fresh ρ R₀ hf D hD hX hD₀ hρ m) hlen)
  refine ⟨N, ?_⟩
  rw [baseRun_final fresh ρ R₀ N 0, show (0 : ℕ) + N = N from Nat.zero_add N]
  exact hN

end

/-! ### Theorem `II_n` from Theorem `I_n` -/

noncomputable section Existence

/-- Relative round covers chosen from a cover statement. -/
def freshRelOf (hcover : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ B : Set s.X.obj.left, IsClosed B →
        ∃ (m : ℕ) (Z : Fin m → LocalFlattener s.f), relNonflat s.f B ⊆ ⋃ p, (Z p).support)
    (s : Stage) (B : Set s.X.obj.left) : Σ m : ℕ, Fin m → LocalFlattener s.f := by
  classical
  exact if h : CompactSpace s.X.obj.left ∧ IsProperMap s.f.hom.left.base ∧ IsClosed B then
    ⟨Classical.choose (hcover s h.1 h.2.1 B h.2.2),
      Classical.choose (Classical.choose_spec (hcover s h.1 h.2.1 B h.2.2))⟩
  else ⟨0, fun p => p.elim0⟩

theorem freshRelOf_spec (hcover : ∀ s : Stage, CompactSpace s.X.obj.left →
      IsProperMap s.f.hom.left.base → ∀ B : Set s.X.obj.left, IsClosed B →
        ∃ (m : ℕ) (Z : Fin m → LocalFlattener s.f), relNonflat s.f B ⊆ ⋃ p, (Z p).support)
    (s : Stage) (h1 : CompactSpace s.X.obj.left) (h2 : IsProperMap s.f.hom.left.base)
    (B : Set s.X.obj.left) (h3 : IsClosed B) :
    relNonflat s.f B ⊆ ⋃ p, (((freshRelOf hcover s B).2) p).support := by
  have h : CompactSpace s.X.obj.left ∧ IsProperMap s.f.hom.left.base ∧ IsClosed B := ⟨h1, h2, h3⟩
  unfold freshRelOf
  rw [dif_pos h]
  exact Classical.choose_spec (Classical.choose_spec (hcover s h.1 h.2.1 B h.2.2))

/-- The runs of Theorem `I_n` for data whose `B` satisfies `D`, chosen. -/
def runRelOf (D : ∀ s : Stage, Set s.X.obj.left → Prop)
    (hI : ∀ (s : Stage) (q' : ℕ) (R : FDatum s q'), CompactSpace s.X.obj.left →
      IsProperMap s.f.hom.left.base → D s R.B → ∃ l : PermRun s R, OpenTracked l.final.2)
    (s : Stage) (q' : ℕ) (R : FDatum s q') : PermRun s R := by
  classical
  exact if h : CompactSpace s.X.obj.left ∧ IsProperMap s.f.hom.left.base ∧ D s R.B then
    Classical.choose (hI s q' R h.1 h.2.1 h.2.2) else .nil s R

theorem runRelOf_spec (D : ∀ s : Stage, Set s.X.obj.left → Prop)
    (hI : ∀ (s : Stage) (q' : ℕ) (R : FDatum s q'), CompactSpace s.X.obj.left →
      IsProperMap s.f.hom.left.base → D s R.B → ∃ l : PermRun s R, OpenTracked l.final.2)
    (s : Stage) (q' : ℕ) (R : FDatum s q') (h1 : CompactSpace s.X.obj.left)
    (h2 : IsProperMap s.f.hom.left.base) (h3 : D s R.B) :
    ∀ p, IsRelOpen (runRelOf D hI s q' R).final.2.B ((runRelOf D hI s q' R).final.2.Z p).support := by
  have h : CompactSpace s.X.obj.left ∧ IsProperMap s.f.hom.left.base ∧ D s R.B := ⟨h1, h2, h3⟩
  unfold runRelOf
  rw [dif_pos h]
  exact Classical.choose_spec (hI s q' R h.1 h.2.1 h.2.2)

/-- **Theorem `II_n` from Theorem `I_n`** (Hironaka, proof of `I_n ⇒ II_n`, pp. 544–546), for an
(F)-datum `R₀` on a compact base with a proper family: let `D` be a property of closed sets stable under
strict transforms along admissible steps (in the application: `dim B ≤ n`) with `D B₀`. If (a) for every
closed `B` of a compact proper stage finitely many actual local flatteners cover `s_1(f/B)` (Hironaka's
`Z_{q+r}`, Th. 2.4 around the strata), and (b) every datum whose `B` satisfies `D` admits a permissible run
ending with relatively open tracked supports (Theorem `I_n`), then `R₀` admits a permissible run after which
`f` is flat over the strict transform of `B₀`; the local input `PersistentLocalFlattener` gives the
closedness of the relative non-flat sets. -/
theorem exists_flatOverB_of_theoremI (hP : PersistentLocalFlattener)
    (D : ∀ s : Stage, Set s.X.obj.left → Prop)
    (hD : ∀ (s : Stage) (c : AdmissibleCentre s.f) (B : Set s.X.obj.left), D s B →
      D (nextWith s c) (strictSet s c B))
    (hcover : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ B : Set s.X.obj.left, IsClosed B →
        ∃ (m : ℕ) (Z : Fin m → LocalFlattener s.f), relNonflat s.f B ⊆ ⋃ p, (Z p).support)
    (hI : ∀ (s : Stage) (q' : ℕ) (R : FDatum s q'), CompactSpace s.X.obj.left →
      IsProperMap s.f.hom.left.base → D s R.B → ∃ l : PermRun s R, OpenTracked l.final.2)
    (s₀ : Stage) (hX : CompactSpace s₀.X.obj.left) (hf : IsProperMap s₀.f.hom.left.base)
    {q : ℕ} (R₀ : FDatum s₀ q) (hD₀ : D s₀ R₀.B) :
    ∃ l : PermRun s₀ R₀, FlatOverB l.final.2 := by
  obtain ⟨N, hN⟩ := exists_flatOverB_of_runs (freshRelOf hcover) (runRelOf D hI) R₀ hf hP D hD hX hD₀
    (freshRelOf_spec hcover) (runRelOf_spec D hI)
  exact ⟨_, hN⟩

end Existence

end Hironaka.Analytic.Unibranch.HironakaG10RdRelativeRounds
