import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.Blowup.BlowupExistence
import Hironaka.Blowup.BlowupCompact
import Hironaka.Invariant.ResolutionInvariantOrder

set_option autoImplicit false

/-!
# The driver of the canonical resolution: iterate the blowup of the maximum locus

Blueprint `hir:resolution-driver` (`blueprint/src/hironaka.tex`, Hironaka phase H4; the existence half of
`hir:canonical-resolution`).  Sources: Bierstone--Milman 2008 §7 (the centre of each blowup is the maximum locus of an
upper semicontinuous invariant), Włodarczyk 2005 (Theorem 2.0.1 and the end of the proof of the resolution theorem), Kollár
2007 (§3.4: the resolution is obtained by iterating the blowup of the maximum locus).

A tower is a *canonical segment* for an invariant `inv` (a function on the last stage of every tower) if each of its centres
is nonempty and is the set where `inv` of the preceding part attains its maximum on the cosupport
(`IsCanonicalSegment`; Definition `hir:centre-function`, with no empty steps).  Given the properties (1) (the maximum locus
is an admissible centre) and (2) (upper semicontinuity) of `hir:centre-function`, closed cosupports, and either

* (8) a bound on the length of canonical segments over a compact base (`exists_isGeoResolution_of_bounded_invariant`), or
* (3) a strict drop of the invariant under the blowup of its maximum locus, with values in a well-founded order
  (`exists_isGeoResolution_of_wellFounded_invariant`),

the blowup of the maximum locus can be iterated until the cosupport is empty: a resolution (`IsGeoResolution`).  The
blowups exist by Demailly's construction (`BlowupExistence.exists_isBlowupAlong`), and every stage over a compact base is
compact (`BlowupCompact.compactSpace_of_isBlowupAlong`), so the maximum is attained
(`ResolutionInvariantOrder.IsInvUSCOn.exists_isMaxOn`).

## Main results

* `compactSpace_of_tower`, `exists_blowup`: stages of towers over a compact base are compact; admissible centres with empty
  interior can be blown up;
* `exists_isGeoResolution_of_bounded`: the abstract driver -- for a class `P` of towers stable under some admissible
  blowup while the cosupport is nonempty, with a bound on the lengths, some tower of the class is a resolution;
* `maxLocus_nonempty`: on a compact stage the maximum locus of an upper semicontinuous invariant on a nonempty closed
  cosupport is nonempty;
* `exists_isGeoResolution_of_bounded_invariant`, `exists_isGeoResolution_of_wellFounded_invariant`: the two forms above.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution` (checked by script).

Sorry-free.
-/

open Set

namespace Hironaka.ResolutionDriver

open Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals
open Hironaka.MarkedIdeals.MarkedIdeal
open Hironaka.ResolutionInvariantOrder

universe u

variable {n : ℕ} {X : CMfd.{u} n}

/-- **Every stage of a tower over a compact manifold is compact.** -/
theorem compactSpace_of_tower [CompactSpace X] :
    ∀ {Y : CMfd.{u} n} (_ : BlowupTower X Y), CompactSpace Y
  | _, .refl => inferInstance
  | _, .step T _ _ hπ => by
    have := compactSpace_of_tower T
    exact BlowupCompact.compactSpace_of_isBlowupAlong hπ

/-- **A closed submanifold with empty interior can be blown up** (Demailly's blowup). -/
theorem exists_blowup {Y : CMfd.{u} n} (C : Set Y) (hC : IsClosedSubmanifold n C) (hint : interior C = ∅) :
    ∃ (Z : CMfd.{u} n) (π : Z → Y), IsBlowupAlong n C π := by
  obtain ⟨Z, _, _, _, π, hπ⟩ := BlowupExistence.exists_isBlowupAlong C hC hint
  exact ⟨CMfd.of Z, π, hπ⟩

/-- **The abstract driver.**  Let `P` be a class of towers over `X` containing the empty tower such that every multiple
test blow-up `T ∈ P` with nonempty cosupport has an admissible centre `C` with empty interior all of whose blowups extend
`T` inside `P`.  If the multiple test blow-ups in `P` have bounded length, some tower of `P` is a resolution. -/
theorem exists_isGeoResolution_of_bounded (𝔪 : MarkedIdeal n X)
    (P : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Prop) (hP : P (BlowupTower.refl : BlowupTower X X))
    (hstep : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), P T → IsGeoTestTower 𝔪 T →
      (geoTransformAlong 𝔪 T).cosupp.Nonempty →
      ∃ C : Set Y, (geoTransformAlong 𝔪 T).IsAdmissibleCentre C ∧ interior C = ∅ ∧
        ∀ {Z : CMfd.{u} n} (π : Z → Y) (hπ : IsBlowupAlong n C π), P (BlowupTower.step T C π hπ))
    (k : ℕ) (hbound : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), P T → IsGeoTestTower 𝔪 T → T.length ≤ k) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y), P T ∧ IsGeoResolution 𝔪 T := by
  suffices h : ∀ j : ℕ, ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), P T → IsGeoTestTower 𝔪 T →
      T.length + j = k → ∃ (Y' : CMfd.{u} n) (T' : BlowupTower X Y'), P T' ∧ IsGeoResolution 𝔪 T' by
    exact h k BlowupTower.refl hP trivial (by simp)
  intro j
  induction j with
  | zero =>
    intro Y T hPT hT hlen
    by_cases hne : (geoTransformAlong 𝔪 T).cosupp.Nonempty
    · obtain ⟨C, hC, hint, hPstep⟩ := hstep T hPT hT hne
      obtain ⟨Z, π, hπ⟩ := exists_blowup C hC.1 hint
      have := hbound (BlowupTower.step T C π hπ) (hPstep π hπ)
        ((isGeoTestTower_step_iff 𝔪 T C π hπ).mpr ⟨hT, hC⟩)
      simp only [BlowupTower.length_step] at this
      omega
    · exact ⟨Y, T, hPT, hT, not_nonempty_iff_eq_empty.mp hne⟩
  | succ j ih =>
    intro Y T hPT hT hlen
    by_cases hne : (geoTransformAlong 𝔪 T).cosupp.Nonempty
    · obtain ⟨C, hC, hint, hPstep⟩ := hstep T hPT hT hne
      obtain ⟨Z, π, hπ⟩ := exists_blowup C hC.1 hint
      exact ih (BlowupTower.step T C π hπ) (hPstep π hπ)
        ((isGeoTestTower_step_iff 𝔪 T C π hπ).mpr ⟨hT, hC⟩) (by simp only [BlowupTower.length_step]; omega)
    · exact ⟨Y, T, hPT, hT, not_nonempty_iff_eq_empty.mp hne⟩

section Invariant

variable {Λ : Type*} [LinearOrder Λ]

/-- The **maximum locus** of `f` on `s`: the points of `s` at which `f` attains its maximum on `s`. -/
def maxLocus {Y : Type*} (f : Y → Λ) (s : Set Y) : Set Y :=
  {y | y ∈ s ∧ ∀ y' ∈ s, f y' ≤ f y}

/-- **Canonical segment** of `𝔪` for the invariant `inv` (Definition `hir:centre-function`, without empty steps): every
centre is nonempty and is the maximum locus of the invariant of the preceding part on its cosupport. -/
def IsCanonicalSegment (𝔪 : MarkedIdeal n X) (inv : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) :
    ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Prop
  | _, .refl => True
  | _, .step T C _ _ =>
    IsCanonicalSegment 𝔪 inv T ∧ C.Nonempty ∧ C = maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp

@[simp] theorem isCanonicalSegment_refl (𝔪 : MarkedIdeal n X)
    (inv : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) :
    IsCanonicalSegment 𝔪 inv (BlowupTower.refl : BlowupTower X X) := trivial

theorem isCanonicalSegment_step_iff (𝔪 : MarkedIdeal n X) (inv : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ)
    {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π) :
    IsCanonicalSegment 𝔪 inv (BlowupTower.step T C π hπ) ↔
      IsCanonicalSegment 𝔪 inv T ∧ C.Nonempty ∧ C = maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp :=
  Iff.rfl

/-- **The maximum locus is nonempty** on a compact space, for an upper semicontinuous invariant on a nonempty closed set. -/
theorem maxLocus_nonempty {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] {f : Y → Λ} {s : Set Y}
    (hs : IsClosed s) (hf : IsInvUSCOn f s) (hne : s.Nonempty) : (maxLocus f s).Nonempty := by
  obtain ⟨x, hx, hmax⟩ := hf.exists_isMaxOn hs.isCompact hne
  exact ⟨x, hx, hmax⟩

/-- **The canonical resolution exists, by local finiteness** (`hir:canonical-resolution`, existence; clauses (1), (2) and
(8) of `hir:centre-function` with `K = X`): over a compact base, if along canonical segments the cosupports are closed,
the invariant is upper semicontinuous on them, its maximum locus is an admissible centre with empty interior, and canonical
segments have length at most `k`, then some canonical segment is a resolution. -/
theorem exists_isGeoResolution_of_bounded_invariant [CompactSpace X] (𝔪 : MarkedIdeal n X)
    (inv : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ)
    (hclosed : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonicalSegment 𝔪 inv T → IsGeoTestTower 𝔪 T →
      IsClosed (geoTransformAlong 𝔪 T).cosupp)
    (husc : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonicalSegment 𝔪 inv T → IsGeoTestTower 𝔪 T →
      IsInvUSCOn (inv T) (geoTransformAlong 𝔪 T).cosupp)
    (hadm : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonicalSegment 𝔪 inv T → IsGeoTestTower 𝔪 T →
      (geoTransformAlong 𝔪 T).cosupp.Nonempty →
      (geoTransformAlong 𝔪 T).IsAdmissibleCentre (maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp) ∧
        interior (maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp) = ∅)
    (k : ℕ) (hbound : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonicalSegment 𝔪 inv T →
      IsGeoTestTower 𝔪 T → T.length ≤ k) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y), IsCanonicalSegment 𝔪 inv T ∧ IsGeoResolution 𝔪 T := by
  refine exists_isGeoResolution_of_bounded 𝔪 (fun T => IsCanonicalSegment 𝔪 inv T) trivial ?_ k hbound
  intro Y T hPT hT hne
  have := compactSpace_of_tower T
  obtain ⟨hC, hint⟩ := hadm T hPT hT hne
  refine ⟨_, hC, hint, fun π hπ => ⟨hPT, maxLocus_nonempty (hclosed T hPT hT) (husc T hPT hT) hne, rfl⟩⟩

/-- **The canonical resolution exists, by a well-founded drop** (`hir:canonical-resolution`, existence; clauses (1)--(3) of
`hir:centre-function`): over a compact base, with values in a well-founded order, if along canonical segments the
cosupports are closed, the invariant is upper semicontinuous, its maximum locus is an admissible centre with empty interior,
and after blowing up the maximum locus the invariant at every point of the new cosupport is below the old maximum, then some
canonical segment is a resolution. -/
theorem exists_isGeoResolution_of_wellFounded_invariant [CompactSpace X] [WellFoundedLT Λ] (𝔪 : MarkedIdeal n X)
    (inv : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ)
    (hclosed : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonicalSegment 𝔪 inv T → IsGeoTestTower 𝔪 T →
      IsClosed (geoTransformAlong 𝔪 T).cosupp)
    (husc : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonicalSegment 𝔪 inv T → IsGeoTestTower 𝔪 T →
      IsInvUSCOn (inv T) (geoTransformAlong 𝔪 T).cosupp)
    (hadm : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonicalSegment 𝔪 inv T → IsGeoTestTower 𝔪 T →
      (geoTransformAlong 𝔪 T).cosupp.Nonempty →
      (geoTransformAlong 𝔪 T).IsAdmissibleCentre (maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp) ∧
        interior (maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp) = ∅)
    (hdec : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonicalSegment 𝔪 inv T → IsGeoTestTower 𝔪 T →
      ∀ x₀ ∈ maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp,
      ∀ {Z : CMfd.{u} n} (π : Z → Y)
        (hπ : IsBlowupAlong n (maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp) π),
      ∀ z ∈ (geoTransformAlong 𝔪
          (BlowupTower.step T (maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp) π hπ)).cosupp,
        inv (BlowupTower.step T (maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp) π hπ) z < inv T x₀) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y), IsCanonicalSegment 𝔪 inv T ∧ IsGeoResolution 𝔪 T := by
  -- strong induction on a bound `l` for the values on the cosupport
  suffices h : ∀ l : Λ, ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonicalSegment 𝔪 inv T →
      IsGeoTestTower 𝔪 T → (∀ y ∈ (geoTransformAlong 𝔪 T).cosupp, inv T y ≤ l) →
      ∃ (Y' : CMfd.{u} n) (T' : BlowupTower X Y'), IsCanonicalSegment 𝔪 inv T' ∧ IsGeoResolution 𝔪 T' by
    by_cases hne : (geoTransformAlong 𝔪 (BlowupTower.refl : BlowupTower X X)).cosupp.Nonempty
    · obtain ⟨x₀, -, hmax⟩ := maxLocus_nonempty
        (hclosed (BlowupTower.refl : BlowupTower X X) trivial trivial)
        (husc (BlowupTower.refl : BlowupTower X X) trivial trivial) hne
      exact h _ BlowupTower.refl trivial trivial fun y hy => hmax y hy
    · exact ⟨X, BlowupTower.refl, trivial, trivial, not_nonempty_iff_eq_empty.mp hne⟩
  intro l
  induction l using WellFoundedLT.induction with
  | _ l ih =>
  intro Y T hPT hT hl
  by_cases hne : (geoTransformAlong 𝔪 T).cosupp.Nonempty
  · have := compactSpace_of_tower T
    obtain ⟨hC, hint⟩ := hadm T hPT hT hne
    obtain ⟨x₀, hx₀⟩ := maxLocus_nonempty (hclosed T hPT hT) (husc T hPT hT) hne
    obtain ⟨Z, π, hπ⟩ := exists_blowup _ hC.1 hint
    set T' := BlowupTower.step T (maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp) π hπ with hT'def
    have hPT' : IsCanonicalSegment 𝔪 inv T' := ⟨hPT, ⟨x₀, hx₀⟩, rfl⟩
    have hT' : IsGeoTestTower 𝔪 T' := (isGeoTestTower_step_iff 𝔪 T _ π hπ).mpr ⟨hT, hC⟩
    by_cases hne' : (geoTransformAlong 𝔪 T').cosupp.Nonempty
    · have := compactSpace_of_tower T'
      obtain ⟨z₀, hz₀, hzmax⟩ := maxLocus_nonempty (hclosed T' hPT' hT') (husc T' hPT' hT') hne'
      have hlt : inv T' z₀ < l := (hdec T hPT hT x₀ hx₀ π hπ z₀ hz₀).trans_le (hl x₀ hx₀.1)
      exact ih _ hlt T' hPT' hT' hzmax
    · exact ⟨_, T', hPT', hT', not_nonempty_iff_eq_empty.mp hne'⟩
  · exact ⟨Y, T, hPT, hT, not_nonempty_iff_eq_empty.mp hne⟩

end Invariant

end Hironaka.ResolutionDriver
