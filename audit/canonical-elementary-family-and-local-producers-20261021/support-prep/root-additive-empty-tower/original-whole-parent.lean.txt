import TranscendentalNakamaye.Pending.ResolutionInvariantExt
import TranscendentalNakamaye.Pending.BlowupTowerSplit

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# A restricted tower whose centres miss the open set is an empty tower

Hironaka phase H2 (TN3), tower calculus for TN-CLASSICAL's Step 1 value function and general step
(`hir:maximal-order-step`, `hir:general-step`; claim I-0977 C-0130, offered C-0128).  Blueprint
`bcalc:restrict-empty-tower` (chapter `blowup-calculus.tex`).  Source: Włodarczyk 2005 (`wlodarczyk05-hironaka`),
Step 2a and the commutativity with étale morphisms (the invariant at a point is computed along the part of the
resolution after the last stage at which the relevant order changed near the point; before it, the centres lie over a
closed set missing a neighbourhood of the point, so over that neighbourhood the blowups are isomorphisms -- here,
blowups along the empty set).

Let `T` be a tower over `X` and `U ⊆ X` open; `restrict U T` is its restriction to the open preimages of `U`
(`BlowupTowerTransforms.restrict`), whose centres are the traces of the centres of `T`.

* `CentresAvoid U T`: every centre of `T` is disjoint from the preimage of `U` at its stage; `CentresOver F T`: every
  centre lies in the preimage of `F` (both by recursion, like `CoefficientIdealRestriction.CentresIn`).
* `isEmptyTower_restrict_iff`: **`restrict U T` has only empty centres** (TN-CLASSICAL's
  `ResolutionInvariantExt.IsEmptyTower`) **if and only if `CentresAvoid U T`**.
* `centresAvoid_of_centresOver`, `isEmptyTower_restrict_of_centresOver`: centres over `F` with `U ∩ F = ∅` avoid `U`.
* `centresAvoid_append_iff`, `centresOver_append_iff`: along a concatenation `T₀.append T₁` (the tail over the open
  preimage of `U`, resp. over the preimage of `F`); `centresAvoid_head`, `isEmptyTower_restrict_head`,
  `centresOver_head`: for the head of `BlowupTowerSplit.split` (TN-CLASSICAL).

Import discipline (Hironaka phase): this module does not import, even transitively,
`Pending.RelativePrincipalization` or `Pending.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace TranscendentalNakamaye.Pending.RestrictEmptyTower

open FirstPass FirstPass.BlowupSequences
open TranscendentalNakamaye.Pending.BlowupTowers TranscendentalNakamaye.Pending.BlowupTowerTransforms
  TranscendentalNakamaye.Pending.BlowupTowerSplit
open TranscendentalNakamaye.Pending.ResolutionInvariantExt (IsEmptyTower)

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n}

/-- **The centres of `T` miss the open set `U`**: each centre is disjoint from the preimage of `U` at its stage. -/
def CentresAvoid (U : Opens X) : {Y : CMfd.{u} n} → BlowupTower X Y → Prop
  | _, .refl => True
  | _, .step T C _ _ => CentresAvoid U T ∧ Disjoint C (T.proj ⁻¹' (U : Set X))

/-- **The centres of `T` lie over `F`**: each centre lies in the preimage of `F` at its stage. -/
def CentresOver (F : Set X) : {Y : CMfd.{u} n} → BlowupTower X Y → Prop
  | _, .refl => True
  | _, .step T C _ _ => CentresOver F T ∧ C ⊆ T.proj ⁻¹' F

@[simp] theorem centresAvoid_refl (U : Opens X) : CentresAvoid U (BlowupTower.refl : BlowupTower X X) := trivial

@[simp] theorem centresOver_refl (F : Set X) : CentresOver F (BlowupTower.refl : BlowupTower X X) := trivial

theorem centresAvoid_step_iff (U : Opens X) {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) :
    CentresAvoid U (.step T C π hπ) ↔ CentresAvoid U T ∧ Disjoint C (T.proj ⁻¹' (U : Set X)) :=
  Iff.rfl

theorem centresOver_step_iff (F : Set X) {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) : CentresOver F (.step T C π hπ) ↔ CentresOver F T ∧ C ⊆ T.proj ⁻¹' F :=
  Iff.rfl

/-- The trace of a set on an open subset is empty iff the set misses it. -/
theorem preimage_val_eq_empty_iff {Y : Type*} [TopologicalSpace Y] (V : Opens Y) (C : Set Y) :
    ((↑) ⁻¹' C : Set V) = ∅ ↔ Disjoint C (V : Set Y) := by
  rw [Set.disjoint_left]
  constructor
  · intro h y hyC hyV
    have hp : (⟨y, hyV⟩ : V) ∈ ((↑) ⁻¹' C : Set V) := hyC
    rw [h] at hp
    exact hp
  · intro h
    ext p
    simp only [mem_preimage, mem_empty_iff_false, iff_false]
    exact fun hp => h hp p.2

/-- **A restricted tower has only empty centres iff the centres of the tower miss the open set.** -/
theorem isEmptyTower_restrict_iff (U : Opens X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsEmptyTower (restrict U T) ↔ CentresAvoid U T
  | _, .refl => Iff.rfl
  | _, .step T C π hπ => by
    show IsEmptyTower (restrict U T) ∧ ((↑) ⁻¹' C : Set (openPreimage T U)) = ∅ ↔
      CentresAvoid U T ∧ Disjoint C (T.proj ⁻¹' (U : Set X))
    rw [isEmptyTower_restrict_iff U T, preimage_val_eq_empty_iff]
    rfl

/-- **Centres over a set disjoint from the open set avoid it.** -/
theorem centresAvoid_of_centresOver (U : Opens X) {F : Set X} (hUF : Disjoint (U : Set X) F) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), CentresOver F T → CentresAvoid U T
  | _, .refl, _ => trivial
  | _, .step T _ _ _, h =>
    ⟨centresAvoid_of_centresOver U hUF T h.1,
      Set.disjoint_left.mpr fun _ hyC hyU => Set.disjoint_left.mp hUF hyU (h.2 hyC)⟩

/-- **If the centres lie over a set disjoint from `U`, the restriction to `U` has only empty centres.** -/
theorem isEmptyTower_restrict_of_centresOver (U : Opens X) {F : Set X} (hUF : Disjoint (U : Set X) F)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (h : CentresOver F T) : IsEmptyTower (restrict U T) :=
  (isEmptyTower_restrict_iff U T).mpr (centresAvoid_of_centresOver U hUF T h)

/-- **Along a concatenation**: the centres of `T₀.append T₁` avoid `U` iff those of `T₀` avoid `U` and those of `T₁`
avoid the open preimage of `U` in the last stage of `T₀`. -/
theorem centresAvoid_append_iff (U : Opens X) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) :
    ∀ {Y : CMfd.{u} n} (T₁ : BlowupTower Y₀ Y),
      CentresAvoid U (T₀.append T₁) ↔ CentresAvoid U T₀ ∧ CentresAvoid (openPreimage T₀ U) T₁
  | _, .refl => by simp
  | _, .step T₁ C π hπ => by
    rw [BlowupTower.append_step, centresAvoid_step_iff, centresAvoid_step_iff, centresAvoid_append_iff U T₀ T₁,
      BlowupTower.proj_append, and_assoc]
    rfl

/-- **Along a concatenation**: the centres of `T₀.append T₁` lie over `F` iff those of `T₀` do and those of `T₁` lie
over the preimage of `F` in the last stage of `T₀`. -/
theorem centresOver_append_iff (F : Set X) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) :
    ∀ {Y : CMfd.{u} n} (T₁ : BlowupTower Y₀ Y),
      CentresOver F (T₀.append T₁) ↔ CentresOver F T₀ ∧ CentresOver (T₀.proj ⁻¹' F) T₁
  | _, .refl => by simp
  | _, .step T₁ C π hπ => by
    rw [BlowupTower.append_step, centresOver_step_iff, centresOver_step_iff, centresOver_append_iff F T₀ T₁,
      BlowupTower.proj_append, and_assoc]
    rfl

/-- **The head of a split avoids `U` if the tower does** (TN-CLASSICAL's `BlowupTowerSplit.head`). -/
theorem centresAvoid_head (U : Opens X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (j : ℕ) (h : CentresAvoid U T) :
    CentresAvoid U (head T j) := by
  have h' : CentresAvoid U ((head T j).append (tail T j)) := (head_append_tail T j).symm ▸ h
  exact ((centresAvoid_append_iff U (head T j) (tail T j)).mp h').1

/-- **The head of a split lies over `F` if the tower does.** -/
theorem centresOver_head (F : Set X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (j : ℕ) (h : CentresOver F T) :
    CentresOver F (head T j) := by
  have h' : CentresOver F ((head T j).append (tail T j)) := (head_append_tail T j).symm ▸ h
  exact ((centresOver_append_iff F (head T j) (tail T j)).mp h').1

/-- **The restriction of the head of a split to `U` has only empty centres** if the centres of the head lie over a set
disjoint from `U` (in the general step: the centres before the order `o` was reached near `x` lie over the closed set
where the order exceeds `o`). -/
theorem isEmptyTower_restrict_head (U : Opens X) {F : Set X} (hUF : Disjoint (U : Set X) F) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (j : ℕ) (h : CentresOver F (head T j)) : IsEmptyTower (restrict U (head T j)) :=
  isEmptyTower_restrict_of_centresOver U hUF (head T j) h

end

end TranscendentalNakamaye.Pending.RestrictEmptyTower
