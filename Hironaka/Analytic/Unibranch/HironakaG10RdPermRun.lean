import Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedRoundData
import Hironaka.Analytic.Unibranch.HironakaG10HirFlattenerGluing
import Hironaka.Analytic.Unibranch.HironakaG10DisjointFlattenerTransport
import Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
import Hironaka.Analytic.Unibranch.HironakaG10SourceCSet

/-!
# (F)-data, permissible steps and permissible runs (lane G10RD)

Plan item G10-03-12.a (contract of `work/hironaka-run0081-20261117/G10RD/G10-03-01-double-induction-contract.md`
§3.1, `G10-03-02-tracked-flattener-state.md` §3).  Source: H. Hironaka, *Flattening theorem in
complex-analytic geometry*, Amer. J. Math. 97 (1975), Def. 4.4.2 (printed pp. 536–537), Def. 4.4.3 (p. 537),
Lemma 4.4.5 and Defs. 4.4.6–4.4.7 (pp. 537–539), and p. 544: a run "permissible for R̄ (and hence permissible
for R, too)".

* `FDatum s q` — Hironaka's (F)-datum on a stage: a closed set `B` and `q` ACTUAL tracked local flatteners;
  `FDatum.tracked` is its germ shadow (the library `TrackedDatum`), `FDatum.trackedTransport` its germ-level
  transport along a centre;
* `PermStep R` — a permissible centre (Def. 4.4.3 (1), (2), and (3) in the germ form consumed by
  `TrackedRoundData.StepPermissible`) together with the transported datum, whose actual supports are the
  germ-level transport (Lemma 4.4.5 (1));
* `PermRun s R` — finite permissible sequences (Def. 4.4.7 over a compact base), `PermRun.final`,
  `PermRun.length`;
* `PermStep.ofDisjoint` — **every centre disjoint from the tracked supports is a permissible step**, with
  the transport `HironakaG10DisjointFlattenerTransport.disjointTransport` (the steps of the lower-dimensional
  run `II_{n-1}` inside `I_n`, Lemma 4.5.1 (2));
* `relNonflat_mono`, `strictSet_mono`, `PermStep.liftB`, `PermRun.liftB` — a run permissible for
  `R̄ = (f; C; Z)` is permissible for `R = (f; B; Z)` when `C ⊆ B` (p. 544);
* `PermStep.principalPullbackAt_of_leave` — the leaving condition (hence the fibre decrease, Lemma 4.6.1) at
  every point that leaves the tracked set at a permissible step.

No named input is introduced; no `RoundData` field is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG10RdPermRun

open Hironaka Hironaka
  HironakaSingularModuleSheafStalk
open Hironaka.Analytic.Unibranch.SourceReducedComplexSpace
  Hironaka.Analytic.Unibranch.HironakaG10ChowOneStepStrictTransform
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver
  Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine
  Hironaka.Analytic.Unibranch.HironakaG10ChowLeavingRounds
  Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum
  Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener
  Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10HirFlattenerGluing
  Hironaka.Analytic.Unibranch.HironakaG10DisjointFlattenerTransport
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
  Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus

noncomputable section

/-! ### Centres, blowup maps and strict transforms of sets -/

/-- The stalk ideal of an admissible centre. -/
def centreIdeal {X Y : SourceReducedComplexSpace} {f : Y ⟶ X} (c : AdmissibleCentre f)
    (x : X.obj.left) : Ideal (X.obj.left.presheaf.stalk x) :=
  (LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf c.B c.b x) :)

/-- The blowup map of one step. -/
def stepσ (s : Stage) (c : AdmissibleCentre s.f) : (nextWith s c).X ⟶ s.X :=
  letI := c.finiteType
  stepProj c.B c.b c.dense

/-- **Strict transform of a set** under one step (Hironaka Rem. 4.3.2, p. 535): the closure of the inverse
image of the part off the centre. -/
def strictSet (s : Stage) (c : AdmissibleCentre s.f) (A : Set s.X.obj.left) :
    Set (nextWith s c).X.obj.left :=
  closure ((stepσ s c).hom.left.base ⁻¹' (A \ nonunitLocus c.B c.b))

theorem strictSet_mono (s : Stage) (c : AdmissibleCentre s.f) {A A' : Set s.X.obj.left}
    (h : A ⊆ A') : strictSet s c A ⊆ strictSet s c A' :=
  closure_mono (preimage_mono (sdiff_subset_sdiff_left h))

/-! ### (F)-data -/

/-- **An (F)-datum** (Hironaka Def. 4.4.2) on a stage: a closed set `B` and `q` actual tracked local
flatteners of the current family.  (`F = 𝒪_Y`; condition (2), zero `f`-torsion, is not imposed: the
native strict transform kills only exceptional torsion.) -/
structure FDatum (s : Stage) (q : ℕ) where
  B : Set s.X.obj.left
  closed : IsClosed B
  Z : Fin q → LocalFlattener s.f

variable {s : Stage} {q : ℕ}

/-- The germ shadow of an (F)-datum: the library tracked datum `(V_p, |Z_p|)`. -/
def FDatum.tracked (R : FDatum s q) : TrackedDatum s.X :=
  trackedDatumOfLocalFlatteners R.Z

theorem FDatum.tracked_tracked (R : FDatum s q) :
    R.tracked.tracked = ⋃ p, (R.Z p).support := rfl

/-- The germ-level transport of the tracked datum along a centre (Lemma 4.4.5 at germ level). -/
def FDatum.trackedTransport (R : FDatum s q) (c : AdmissibleCentre s.f) :
    TrackedDatum (nextWith s c).X :=
  letI := c.finiteType
  R.tracked.transport c.B c.b c.dense s.f

/-- The datum with `B` replaced (Hironaka's `R̄ = (F, f; C_i; V_p, Z_p)`, p. 544). -/
def FDatum.withB (R : FDatum s q) (C : Set s.X.obj.left) (hC : IsClosed C) : FDatum s q :=
  ⟨C, hC, R.Z⟩

/-! ### Permissible steps -/

/-- **A permissible step** of an (F)-datum (Hironaka Def. 4.4.3 with Def. 4.4.6 and Lemma 4.4.5):
(1) the family is flat over the centre; (2) the centre lies in `s_1(f/B)`; (3) the centre is a sum centre
for the whole-fibre flattener, or misses the tracked supports (the germ form of (3) consumed by
`TrackedRoundData.StepPermissible`); and the transported datum: `B` goes to its strict transform, and the
actual supports of the transported flatteners are the germ-level transport. -/
structure PermStep (R : FDatum s q) where
  c : AdmissibleCentre s.f
  flat : ∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)
  sub : nonunitLocus c.B c.b ⊆ relNonflat s.f R.B
  perm : (∃ β, IsSumCentreFor c.B c.b s.f β) ∨
    Disjoint (nonunitLocus c.B c.b) R.tracked.tracked
  next : FDatum (nextWith s c) q
  next_B : next.B = strictSet s c R.B
  next_support : ∀ p, (next.Z p).support = (R.trackedTransport c).Z p

/-- **Finite permissible sequences** (Hironaka Def. 4.4.7; over a compact base proper sequences are
finite). -/
inductive PermRun : (s : Stage) → FDatum s q → Type 1
  | nil (s : Stage) (R : FDatum s q) : PermRun s R
  | cons (s : Stage) (R : FDatum s q) (st : PermStep R)
      (rest : PermRun (nextWith s st.c) st.next) : PermRun s R

/-- The final stage and datum of a permissible run. -/
def PermRun.final : {s : Stage} → {R : FDatum s q} → PermRun s R → Σ s' : Stage, FDatum s' q
  | s, R, .nil _ _ => ⟨s, R⟩
  | _, _, .cons _ _ _ rest => rest.final

/-- The number of steps of a permissible run. -/
def PermRun.length : {s : Stage} → {R : FDatum s q} → PermRun s R → ℕ
  | _, _, .nil _ _ => 0
  | _, _, .cons _ _ _ rest => rest.length + 1

/-- Concatenation of permissible runs (the second starts at the final datum of the first). -/
def PermRun.append : {s : Stage} → {R : FDatum s q} → (l : PermRun s R) →
    PermRun l.final.1 l.final.2 → PermRun s R
  | _, _, .nil _ _, l' => l'
  | s, R, .cons _ _ st rest, l' => .cons s R st (rest.append l')

theorem PermRun.final_append : {s : Stage} → {R : FDatum s q} → (l : PermRun s R) →
    (l' : PermRun l.final.1 l.final.2) → (l.append l').final = l'.final
  | _, _, .nil _ _, _ => rfl
  | _, _, .cons _ _ _ rest, l' => PermRun.final_append rest l'

theorem PermRun.length_append : {s : Stage} → {R : FDatum s q} → (l : PermRun s R) →
    (l' : PermRun l.final.1 l.final.2) → (l.append l').length = l.length + l'.length
  | _, _, .nil _ _, _ => (Nat.zero_add _).symm
  | _, _, .cons _ _ _ rest, l' =>
      (congrArg (· + 1) (PermRun.length_append rest l')).trans (Nat.succ_add _ _).symm

/-- Hironaka's conclusion of Theorem `I_n` (p. 540): every tracked support meets `B` in a relatively
open set. -/
def OpenTracked (R : FDatum s q) : Prop :=
  ∀ p, HironakaG10SourceCSet.IsRelOpen R.B (R.Z p).support

/-- Hironaka's conclusion of Theorem `II_n` (p. 540): the family is flat over `B`. -/
def FlatOverB (R : FDatum s q) : Prop :=
  relNonflat s.f R.B = ∅

/-! ### Steps disjoint from the tracked supports -/

/-- **A centre disjoint from the tracked supports is a permissible step**, with the actual transport of
the tracked flatteners by pull-back (`disjointTransport`); its supports are the germ-level transport
(`disjointTransport_support_eq_tracked`). -/
def PermStep.ofDisjoint (R : FDatum s q) (c : AdmissibleCentre s.f)
    (hflat : ∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x))
    (hsub : nonunitLocus c.B c.b ⊆ relNonflat s.f R.B)
    (hdisj : Disjoint (nonunitLocus c.B c.b) R.tracked.tracked) : PermStep R :=
  letI := c.finiteType
  { c := c
    flat := hflat
    sub := hsub
    perm := Or.inr hdisj
    next := ⟨strictSet s c R.B, isClosed_closure, fun p =>
      disjointTransport c.B c.b c.dense s.f (R.Z p)
        (hdisj.mono_right (subset_iUnion (fun p => (R.Z p).support) p))⟩
    next_B := rfl
    next_support := fun p =>
      disjointTransport_support_eq_tracked c.B c.b c.dense s.f (R.Z p)
        (hdisj.mono_right (subset_iUnion (fun p => (R.Z p).support) p)) R.tracked p rfl }

/-! ### Changing `B`: permissible for `R̄` hence for `R` (Hironaka p. 544) -/

/-- Flatness over a larger reduced set gives flatness over a smaller one, so `s_1(f/C) ⊆ s_1(f/B)` for
`C ⊆ B`. -/
theorem relNonflat_mono {X Y : SourceReducedComplexSpace} (f : Y ⟶ X) {C B : Set X.obj.left}
    (h : C ⊆ B) : relNonflat f C ⊆ relNonflat f B := by
  rintro x ⟨hxC, hnf⟩
  refine ⟨h hxC, fun hB => hnf (FlatOverAt.mono ?_ hB)⟩
  refine Ideal.span_mono ?_
  rintro g ⟨U, hxU, t, ht, hvan⟩
  exact ⟨U, hxU, t, ht, fun z hz hzC => hvan z hz (h hzC)⟩

theorem FDatum.tracked_eq_of_Z_eq {R R' : FDatum s q} (h : R'.Z = R.Z) :
    R'.tracked = R.tracked := by
  simp only [FDatum.tracked, h]

/-- The germ-level transport of one tracked flattener depends only on its support. -/
theorem trackedTransport_Z_congr {q' : ℕ} {R : FDatum s q} {R' : FDatum s q'}
    (c : AdmissibleCentre s.f) {p : Fin q} {p' : Fin q'}
    (h : (R.Z p).support = (R'.Z p').support) :
    (R.trackedTransport c).Z p = (R'.trackedTransport c).Z p' := by
  ext x'
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨show _ ∈ (R'.Z p').support from h ▸ (show _ ∈ (R.Z p).support from h1), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨show _ ∈ (R.Z p).support from h.symm ▸ (show _ ∈ (R'.Z p').support from h1), h2⟩

/-- A step permissible for a datum with smaller `B` and the same tracked flatteners is permissible for
the datum with larger `B`. -/
def PermStep.liftB {R' : FDatum s q} (R : FDatum s q) (hZ : R'.Z = R.Z) (hB : R'.B ⊆ R.B)
    (st : PermStep R') : PermStep R where
  c := st.c
  flat := st.flat
  sub := st.sub.trans (relNonflat_mono s.f hB)
  perm := FDatum.tracked_eq_of_Z_eq hZ ▸ st.perm
  next := ⟨strictSet s st.c R.B, isClosed_closure, st.next.Z⟩
  next_B := rfl
  next_support := fun p => (st.next_support p).trans
    (trackedTransport_Z_congr st.c (by rw [hZ]))

theorem PermStep.liftB_next_Z {R' : FDatum s q} (R : FDatum s q) (hZ : R'.Z = R.Z) (hB : R'.B ⊆ R.B)
    (st : PermStep R') : (st.liftB R hZ hB).next.Z = st.next.Z := rfl

theorem PermStep.liftB_c {R' : FDatum s q} (R : FDatum s q) (hZ : R'.Z = R.Z) (hB : R'.B ⊆ R.B)
    (st : PermStep R') : (st.liftB R hZ hB).c = st.c := rfl

/-- **A run permissible for `R̄` is permissible for `R`** (Hironaka p. 544), same centres. -/
def PermRun.liftB : {s : Stage} → {R' : FDatum s q} → (R : FDatum s q) → R'.Z = R.Z → R'.B ⊆ R.B →
    PermRun s R' → PermRun s R
  | s, _, R, _, _, .nil _ _ => .nil s R
  | s, _, R, hZ, hB, .cons _ _ st rest =>
      .cons s R (st.liftB R hZ hB)
        (PermRun.liftB (R' := st.next) (st.liftB R hZ hB).next rfl
          (by show st.next.B ⊆ strictSet s st.c R.B; rw [st.next_B]; exact strictSet_mono s st.c hB)
          rest)

theorem PermRun.liftB_length : {s : Stage} → {R' : FDatum s q} → (R : FDatum s q) →
    (hZ : R'.Z = R.Z) → (hB : R'.B ⊆ R.B) → (l : PermRun s R') → (l.liftB R hZ hB).length = l.length
  | _, _, _, _, _, .nil _ _ => rfl
  | s, _, R, hZ, hB, .cons _ _ st rest =>
      congrArg (· + 1) (PermRun.liftB_length (R' := st.next) (st.liftB R hZ hB).next rfl
        (by show st.next.B ⊆ strictSet s st.c R.B; rw [st.next_B]; exact strictSet_mono s st.c hB)
        rest)

/-! ### Leaving points of a permissible step -/

/-- **The leaving condition at a permissible step** (Hironaka Lemma 4.6.1 with Def. 4.4.3 (3)): a point
over a tracked point which is not tracked after the step satisfies `PrincipalPullbackAt`, hence (by
`exists_fibre_decrease_of_principal`) the fibre strictly decreases there. -/
theorem PermStep.principalPullbackAt_of_leave {R : FDatum s q} (st : PermStep R)
    (x' : (nextWith s st.c).X.obj.left)
    (hx : (stepσ s st.c).hom.left.base x' ∈ R.tracked.tracked)
    (hx' : x' ∉ ⋃ p, (st.next.Z p).support) :
    PrincipalPullbackAt s.f (stepσ s st.c) (nextWith s st.c).f x' := by
  let _ := st.c.finiteType
  have hx'' : x' ∉ (R.trackedTransport st.c).tracked := by
    intro h
    obtain ⟨p, hp⟩ := mem_iUnion.mp h
    exact hx' (mem_iUnion.mpr ⟨p, (st.next_support p).symm ▸ hp⟩)
  rcases st.perm with ⟨β, hβ⟩ | hdisj
  · exact HironakaG10ChowTrackedDatum.principalPullbackAt_of_leave st.c.B st.c.b st.c.dense s.f R.tracked β (Or.inl hβ) x' hx hx''
  · exact HironakaG10ChowTrackedDatum.principalPullbackAt_of_leave st.c.B st.c.b st.c.dense s.f R.tracked 0 (Or.inr hdisj) x' hx
      hx''

end

end Hironaka.Analytic.Unibranch.HironakaG10RdPermRun
