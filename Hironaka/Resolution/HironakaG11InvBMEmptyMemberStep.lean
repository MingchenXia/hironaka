import Hironaka.Resolution.HironakaG11InvBMRepresentative
import Hironaka.Resolution.HironakaG11InvBMEmptyMember
import Hironaka.Invariant.StepOneEmptyPrefix
import Hironaka.Invariant.DropMembers

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Bierstone--Milman's Step 1 value does not see empty members of the divisor (repair (B'), induction for property (4'))

Blueprint: `hironaka-g11-inv-bm-max-order.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §6d.

For marked ideals `A`, `B` differing only by empty members of the divisor (`SameUpToEmptyMembers`), the values of
`stepOneInvBM R A` and `stepOneInvBM R B` coincide along EVERY tower, for EVERY `R`: the transforms of `J̄(A)` and `J̄(B)` have the
same submanifold, ideal and mark (`DropMembers.geoTransformAlong_withE`), the original members differ only by empty sets
(`StepOneValue.origMembers_eq`, strict transforms of `∅` are empty), so levels, special points, regimes, masks and the members
through a point agree, and the lower ideals forget the divisor (`emptyBoundary`).  Hence `stepOneInvBM R` satisfies
`EmptyMemberIndep` (the part of the induction of plan module 12 carried by the Step 1 value).

* list tools: `filter_mem_map_eq_of_filter_nonempty`, `boundaryCount_eq_countP`;
* **`stepOneInvBM_eq_of_sameUpToEmptyMembers`**, **`emptyMemberIndep_stepOneInvBM`**.

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG11InvBMEmptyMemberStep

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.BlowupTowerSplit Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.StepOneRegime
  Hironaka.StepOneValue Hironaka.StepOneLowerDomain
  Hironaka.StepOneValueMasked Hironaka.MarkedIdealRestrictOpen
  Hironaka.HomogenizedIdealAlong Hironaka.BlowupTowerIsomorphism
  Hironaka.BlowupTowerIsoTail Hironaka.MarkedIdealBiholomorphism
  Hironaka.HironakaG11InvBMMask Hironaka.HironakaG11InvBMLower
  Hironaka.HironakaG11InvBMCanonicalTail Hironaka.HironakaG11InvBMAdmissible
  Hironaka.HironakaG11InvBMTangentIndep Hironaka.HironakaG11InvBMNaturality
  Hironaka.HironakaG11InvBMRestrictOpen Hironaka.HironakaG11InvBMEmptyMember
  Hironaka.BoundaryCount Hironaka.MemberInterLocusAlong
open Hironaka.TangentDirectionAlong (IsTangentDirectionAlong)
open Hironaka.ResolutionDriver (maxLocus)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical DimLE)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant isGeoTestTower_of_isCanonical)

noncomputable section

variable {n : ℕ}

/-! ### Lists of members -/

section Lists

open Classical

/-- **The members through a point of the images of two lists with the same nonempty members agree**, for a map sending `∅`
to `∅`. -/
theorem filter_mem_map_eq_of_filter_nonempty {α β : Type*} {L₁ L₂ : List (Set α)}
    (h : L₁.filter (fun H => decide H.Nonempty) = L₂.filter (fun H => decide H.Nonempty)) (f : Set α → Set β)
    (hf : f ∅ = ∅) (x : β) :
    (L₁.map f).filter (fun H => decide (x ∈ H)) = (L₂.map f).filter (fun H => decide (x ∈ H)) := by
  have key : ∀ L : List (Set α), (L.map f).filter (fun H => decide (x ∈ H)) =
      ((L.filter (fun H => decide H.Nonempty)).map f).filter (fun H => decide (x ∈ H)) := by
    intro L
    induction L with
    | nil => rfl
    | cons H L ih =>
      by_cases hH : H.Nonempty
      · simp only [List.map_cons, List.filter_cons, hH, decide_true, if_true, ih]
      · obtain rfl : H = ∅ := Set.not_nonempty_iff_eq_empty.mp hH
        simp only [List.map_cons, List.filter_cons, hf, Set.mem_empty_iff_false, decide_false,
          Set.not_nonempty_empty, Bool.false_eq_true, if_false, ih]
  rw [key L₁, key L₂, h]

/-- The number of members through a point is the count of the members containing it. -/
theorem boundaryCount_eq_countP {X : Type*} (E : List (Set X)) (x : X) :
    boundaryCount E x = E.countP (fun H => decide (x ∈ H)) := by
  unfold boundaryCount
  rw [Finset.card_filter]
  induction E with
  | nil => simp
  | cons H E ih =>
    rw [List.countP_cons, ← ih, add_comm]
    refine (Fin.sum_univ_succ (fun i : Fin (E.length + 1) => if x ∈ (H :: E).get i then (1 : ℕ) else 0)).trans ?_
    simp
    split_ifs with hx <;> simp [hx]

/-- **Membership quantifiers over two lists with the same members through `x` agree.** -/
theorem forall_mem_imp_iff_of_filter_eq {α : Type*} {L₁ L₂ : List (Set α)} {x : α}
    (h : L₁.filter (fun H => decide (x ∈ H)) = L₂.filter (fun H => decide (x ∈ H))) (P : Set α → Prop) :
    (∀ H ∈ L₁, x ∈ H → P H) ↔ ∀ H ∈ L₂, x ∈ H → P H := by
  have e : ∀ L : List (Set α), (∀ H ∈ L, x ∈ H → P H) ↔ ∀ H ∈ L.filter (fun H => decide (x ∈ H)), P H := by
    intro L
    simp only [List.mem_filter, decide_eq_true_eq, and_imp]
  rw [e L₁, e L₂, h]

/-- **The member locus only sees the members through each point.** -/
theorem memberInterLocus_congr {Y : Type*} [TopologicalSpace Y] {N S : Set Y} {L₁ L₂ : List (Set Y)}
    (h : ∀ x, L₁.filter (fun H => decide (x ∈ H)) = L₂.filter (fun H => decide (x ∈ H))) :
    memberInterLocus N L₁ S = memberInterLocus N L₂ S := by
  ext x
  have e : ∀ z, (∀ i : Fin L₁.length, x ∈ L₁.get i → z ∈ L₁.get i) ↔
      (∀ i : Fin L₂.length, x ∈ L₂.get i → z ∈ L₂.get i) := by
    intro z
    rw [forall_get_iff (P := fun H => x ∈ H → z ∈ H), forall_get_iff (P := fun H => x ∈ H → z ∈ H)]
    exact forall_mem_imp_iff_of_filter_eq (h x) (fun H => z ∈ H)
  simp only [memberInterLocus, Set.mem_ofPred, e]

end Lists

/-! ### The Step 1 value of marked ideals differing by empty members -/

section Values

variable {X : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ] (R : ResolutionInvariant.{u, v} n k Λ)

open Classical in
/-- The lower value only sees the mask and the lower ideal at the image of the point. -/
theorem lowerValueG_congr (𝔍 𝔍' : MarkedIdeal n X) (Mk : MaskFamily 𝔍) (Mk' : MaskFamily 𝔍')
    (LI LI' : ∀ (_s : ℕ) {Y₀ : CMfd.{u} n} (_T₀ : BlowupTower X Y₀) (_y₀ : Y₀), MarkedIdeal n Y₀) {s : ℕ}
    {Y₀ Y : CMfd.{u} n} {T₀ : BlowupTower X Y₀} {T₁ : BlowupTower Y₀ Y} {y : Y}
    (hM : Mk s T₀ (T₁.proj y) = Mk' s T₀ (T₁.proj y)) (hL : LI s T₀ (T₁.proj y) = LI' s T₀ (T₁.proj y)) :
    lowerValueG R 𝔍 Mk (fun s _ T₀ y₀ => MarkedIdeal.pullback (Subtype.val : Mk s T₀ y₀ → _) (LI s T₀ y₀)) s T₀ T₁ y =
      lowerValueG R 𝔍' Mk' (fun s _ T₀ y₀ => MarkedIdeal.pullback (Subtype.val : Mk' s T₀ y₀ → _) (LI' s T₀ y₀))
        s T₀ T₁ y := by
  have key : ∀ (M M' : Opens Y₀) (_ : M = M') (L L' : MarkedIdeal n Y₀) (_ : L = L'),
      (if h : T₁.proj y ∈ M then ((R.inv (MarkedIdeal.pullback (Subtype.val : M → Y₀) L) (restrict M T₁)
        (⟨y, h⟩ : openPreimage T₁ M) : Λ) : WithTop Λ) else ⊤) =
      (if h : T₁.proj y ∈ M' then ((R.inv (MarkedIdeal.pullback (Subtype.val : M' → Y₀) L') (restrict M' T₁)
        (⟨y, h⟩ : openPreimage T₁ M') : Λ) : WithTop Λ) else ⊤) := by
    intro M M' hMM L L' hLL
    subst hMM hLL
    rfl
  exact key _ _ hM _ _ hL

variable {E₁ E₂ : List (Set X)} {N : Set X} {I : GermIdeal n X} {d : ℕ}

open Classical in
/-- **Marked ideals differing by empty members have the same Step 1 skeleton**: the transforms of `J̄` have the same
submanifold, ideal, mark and cosupport, the original members through every point agree, and so do the levels, the special
points, the regimes, the tangent choices, the masks and the members through a point. -/
theorem skeleton_eq (h : (E₁.filter fun H => decide H.Nonempty) = E₂.filter fun H => decide H.Nonempty)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    (geoTransformAlong (barMarked (⟨N, E₂, I, d⟩ : MarkedIdeal n X)) T).N =
        (geoTransformAlong (barMarked (⟨N, E₁, I, d⟩ : MarkedIdeal n X)) T).N ∧
      (geoTransformAlong (barMarked (⟨N, E₂, I, d⟩ : MarkedIdeal n X)) T).ideal =
        (geoTransformAlong (barMarked (⟨N, E₁, I, d⟩ : MarkedIdeal n X)) T).ideal ∧
      (geoTransformAlong (barMarked (⟨N, E₂, I, d⟩ : MarkedIdeal n X)) T).d =
        (geoTransformAlong (barMarked (⟨N, E₁, I, d⟩ : MarkedIdeal n X)) T).d ∧
      (geoTransformAlong (barMarked (⟨N, E₂, I, d⟩ : MarkedIdeal n X)) T).cosupp =
        (geoTransformAlong (barMarked (⟨N, E₁, I, d⟩ : MarkedIdeal n X)) T).cosupp ∧
      (∀ x : Y, (origMembers (⟨N, E₁, I, d⟩ : MarkedIdeal n X) T).filter (fun H => decide (x ∈ H)) =
        (origMembers (⟨N, E₂, I, d⟩ : MarkedIdeal n X) T).filter (fun H => decide (x ∈ H))) ∧
      ∀ y : Y, level (⟨N, E₁, I, d⟩ : MarkedIdeal n X) T y = level (⟨N, E₂, I, d⟩ : MarkedIdeal n X) T y ∧
        (IsSpecial (⟨N, E₁, I, d⟩ : MarkedIdeal n X) T y ↔ IsSpecial (⟨N, E₂, I, d⟩ : MarkedIdeal n X) T y) := by
  classical
  have hbar : barMarked (⟨N, E₂, I, d⟩ : MarkedIdeal n X) =
      { barMarked (⟨N, E₁, I, d⟩ : MarkedIdeal n X) with E := E₂ } := rfl
  obtain ⟨hN, hI, hd⟩ := DropMembers.geoTransformAlong_withE (barMarked (⟨N, E₁, I, d⟩ : MarkedIdeal n X)) E₂ T
  have hC := DropMembers.cosupp_geoTransformAlong_withE (barMarked (⟨N, E₁, I, d⟩ : MarkedIdeal n X)) E₂ T
  rw [← hbar] at hN hI hd hC
  have hO : ∀ x : Y, (origMembers (⟨N, E₁, I, d⟩ : MarkedIdeal n X) T).filter (fun H => decide (x ∈ H)) =
      (origMembers (⟨N, E₂, I, d⟩ : MarkedIdeal n X) T).filter (fun H => decide (x ∈ H)) := by
    intro x
    rw [origMembers_eq, origMembers_eq]
    exact filter_mem_map_eq_of_filter_nonempty h _ (StepOneEmptyPrefix.strictAlong_empty T) x
  have hl : ∀ y : Y, level (⟨N, E₁, I, d⟩ : MarkedIdeal n X) T y = level (⟨N, E₂, I, d⟩ : MarkedIdeal n X) T y := by
    intro y
    unfold level
    rw [boundaryCount_eq_countP, boundaryCount_eq_countP, List.countP_eq_length_filter, List.countP_eq_length_filter,
      hO y]
  refine ⟨hN, hI, hd, hC, hO, fun y => ⟨hl y, ?_⟩⟩
  have hmem := memberInterLocus_congr (N := (geoTransformAlong (barMarked (⟨N, E₁, I, d⟩ : MarkedIdeal n X)) T).N)
    (S := (geoTransformAlong (barMarked (⟨N, E₁, I, d⟩ : MarkedIdeal n X)) T).cosupp) hO
  unfold IsSpecial
  rw [hl y, hN, hI, hd, hC, hmem]

/-- **Canonical segments only see the values and the cosupports**: two value functions agreeing along every tower for two
marked ideals whose transforms have the same cosupports have the same canonical segments. -/
theorem isCanonical_iff_of_eq {Λ' : Type*} [LinearOrder Λ'] {A B : MarkedIdeal n X}
    (f g : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ') (hfg : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), f T = g T)
    (hcos : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), (geoTransformAlong A T).cosupp = (geoTransformAlong B T).cosupp) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical A f T ↔ IsCanonical B g T
  | _, .refl => Iff.rfl
  | _, .step T C π hπ => by
      show (IsCanonical A f T ∧ (C = ∅ ∨ C = maxLocus (f T) (geoTransformAlong A T).cosupp)) ↔
        (IsCanonical B g T ∧ (C = ∅ ∨ C = maxLocus (g T) (geoTransformAlong B T).cosupp))
      rw [isCanonical_iff_of_eq f g hfg hcos T, hfg T, hcos T]

open Classical in
/-- **The Step 1 value of marked ideals differing only by empty members** (stated for the two records). -/
theorem stepOneInvBM_eq_aux (h : (E₁.filter fun H => decide H.Nonempty) = E₂.filter fun H => decide H.Nonempty)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) :
    stepOneInvBM R (⟨N, E₁, I, d⟩ : MarkedIdeal n X) T y = stepOneInvBM R (⟨N, E₂, I, d⟩ : MarkedIdeal n X) T y := by
  have hsk := fun {Y : CMfd.{u} n} (T : BlowupTower X Y) => skeleton_eq (N := N) (I := I) (d := d) h T
  have hl : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y),
      level (⟨N, E₁, I, d⟩ : MarkedIdeal n X) T y = level (⟨N, E₂, I, d⟩ : MarkedIdeal n X) T y :=
    fun T y => ((hsk T).2.2.2.2.2 y).1
  have hs : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y),
      IsSpecial (⟨N, E₁, I, d⟩ : MarkedIdeal n X) T y ↔ IsSpecial (⟨N, E₂, I, d⟩ : MarkedIdeal n X) T y :=
    fun T y => ((hsk T).2.2.2.2.2 y).2
  have hreg : ∀ (s : ℕ) {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y),
      stepRegime (⟨N, E₁, I, d⟩ : MarkedIdeal n X) s T y ↔ stepRegime (⟨N, E₂, I, d⟩ : MarkedIdeal n X) s T y := by
    intro s Y T y
    unfold stepRegime
    rw [hl, hs]
  have htc : ∀ x : X, tangentChoice (⟨N, E₁, I, d⟩ : MarkedIdeal n X) x = tangentChoice (⟨N, E₂, I, d⟩ : MarkedIdeal n X) x :=
    fun _ => rfl
  have hthr : ∀ {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (y₀ : Y₀),
      throughMembers (⟨N, E₁, I, d⟩ : MarkedIdeal n X) T₀ y₀ = throughMembers (⟨N, E₂, I, d⟩ : MarkedIdeal n X) T₀ y₀ :=
    fun T₀ y₀ => (hsk T₀).2.2.2.2.1 y₀
  have hmem : ∀ {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (z : Y₀) (P : Set Y₀ → Prop),
      (∀ H ∈ origMembers (⟨N, E₁, I, d⟩ : MarkedIdeal n X) T₀, z ∈ H → P H) ↔
        ∀ H ∈ origMembers (⟨N, E₂, I, d⟩ : MarkedIdeal n X) T₀, z ∈ H → P H :=
    fun T₀ z P => forall_mem_imp_iff_of_filter_eq ((hsk T₀).2.2.2.2.1 z) P
  have hmask : ∀ (s : ℕ) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (y₀ : Y₀),
      maskBM (⟨N, E₁, I, d⟩ : MarkedIdeal n X) s T₀ y₀ = maskBM (⟨N, E₂, I, d⟩ : MarkedIdeal n X) s T₀ y₀ := by
    intro s Y₀ T₀ y₀
    obtain ⟨hN, hI, hd, -, -, -⟩ := hsk T₀
    have hnot : ∀ z : Y₀, (∀ H ∈ origMembers (⟨N, E₁, I, d⟩ : MarkedIdeal n X) T₀, z ∉ H) ↔
        ∀ H ∈ origMembers (⟨N, E₂, I, d⟩ : MarkedIdeal n X) T₀, z ∉ H := fun z => hmem T₀ z (fun _ => False)
    have hA : ∀ z : Y₀, (∀ H ∈ origMembers (⟨N, E₁, I, d⟩ : MarkedIdeal n X) T₀, z ∈ H → y₀ ∈ H) ↔
        ∀ H ∈ origMembers (⟨N, E₂, I, d⟩ : MarkedIdeal n X) T₀, z ∈ H → y₀ ∈ H := fun z => hmem T₀ z (fun H => y₀ ∈ H)
    cases s with
    | zero => simp only [maskBM_zero, maskB, hnot, hN, hI, hd, htc]
    | succ s => simp only [maskBM_succ, maskA, tangentOpen, hA, hl, hs, htc]
  have hLI : ∀ (s : ℕ) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (y₀ : Y₀),
      lowerIdealBM (⟨N, E₁, I, d⟩ : MarkedIdeal n X) s T₀ y₀ = lowerIdealBM (⟨N, E₂, I, d⟩ : MarkedIdeal n X) s T₀ y₀ := by
    intro s Y₀ T₀ y₀
    rw [lowerIdealBM_eq_lowerIdealWBM, lowerIdealBM_eq_lowerIdealWBM, hthr, htc]
    cases s <;> rfl
  unfold stepOneInvBM
  by_cases hsp : IsSpecial (⟨N, E₁, I, d⟩ : MarkedIdeal n X) T y
  · rw [stepOneInvG_of_isSpecial R _ _ _ T hsp, stepOneInvG_of_isSpecial R _ _ _ T ((hs T y).mp hsp), hl]
  · rw [stepOneInvG_of_not_isSpecial R _ _ _ T hsp,
      stepOneInvG_of_not_isSpecial R _ _ _ T (fun h' => hsp ((hs T y).mpr h')), ← hl T y,
      StepOneRepresentative.regimeRun_congr (stepRegime (⟨N, E₁, I, d⟩ : MarkedIdeal n X) (level _ T y))
        (stepRegime (⟨N, E₂, I, d⟩ : MarkedIdeal n X) (level _ T y)) (fun T' y' => hreg _ T' y') T y]
    congr 2
    exact lowerValueG_congr R _ _ (maskBM _) (maskBM _) (fun s _ T₀ y₀ => lowerIdealBM (⟨N, E₁, I, d⟩ : MarkedIdeal n X) s T₀ y₀)
      (fun s _ T₀ y₀ => lowerIdealBM (⟨N, E₂, I, d⟩ : MarkedIdeal n X) s T₀ y₀) (hmask _ _ _) (hLI _ _ _)

/-- **Bierstone--Milman's Step 1 value does not see empty members of the divisor**: for marked ideals differing only by
empty members, the values agree along every tower (any lower invariant `R`, no hypothesis). -/
theorem stepOneInvBM_eq_of_sameUpToEmptyMembers {A B : MarkedIdeal n X} (h : SameUpToEmptyMembers A B)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) : stepOneInvBM R A T y = stepOneInvBM R B T y := by
  obtain ⟨N, E₁, I, d⟩ := A
  obtain ⟨N', E₂, I', d'⟩ := B
  obtain ⟨hN, hI, hd, hE⟩ := h
  change N = N' at hN
  change I = I' at hI
  change d = d' at hd
  subst hN hI hd
  exact stepOneInvBM_eq_aux R hE T y

/-- **`stepOneInvBM R` has the property `EmptyMemberIndep`** (in every dimension, for every lower invariant `R`; the domain
hypotheses are not used): the canonical segments and the values agree. -/
theorem emptyMemberIndep_stepOneInvBM (k' : ℕ) :
    EmptyMemberIndep k' (fun {X : CMfd.{u} n} 𝔍 {Y : CMfd.{u} n} T y => stepOneInvBM (X := X) R 𝔍 (Y := Y) T y) := by
  intro X A B _ _ h Y T hcan
  have hval : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), (fun y => stepOneInvBM R A T y) = fun y => stepOneInvBM R B T y :=
    fun T => funext fun y => stepOneInvBM_eq_of_sameUpToEmptyMembers R h T y
  have hcos : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      (geoTransformAlong A T).cosupp = (geoTransformAlong B T).cosupp := by
    intro Y T
    obtain ⟨N, E₁, I, d⟩ := A
    obtain ⟨N', E₂, I', d'⟩ := B
    obtain ⟨hN, hI, hd, -⟩ := h
    change N = N' at hN
    change I = I' at hI
    change d = d' at hd
    subst hN hI hd
    exact (DropMembers.cosupp_geoTransformAlong_withE (⟨N, E₁, I, d⟩ : MarkedIdeal n X) E₂ T).symm
  exact ⟨(isCanonical_iff_of_eq _ _ hval hcos T).mp hcan,
    fun y _ => stepOneInvBM_eq_of_sameUpToEmptyMembers R h T y⟩

end Values

end

end Hironaka.HironakaG11InvBMEmptyMemberStep
