import Hironaka.Resolution.HironakaOriginalNCCausalHistoryValue
import Hironaka.Blowup.BlowupTowerSplitIso

set_option autoImplicit false

/-!
# The actual original causal value across an unchanged-count continuation

These are literal identities for the ONE original causalHistoryValue, not
an independently defined phase value. No canonicality is needed to keep
the true first-attainment year and complete birth marked record when the
actual old count does not drop. The entire dependent split and literal
uncompressed restricted suffix are retained.

The internally selected canonical phase must next use the real existing
restrict-append tower isomorphism and its actual canonical birth-tail
domain to read this identity as the whole original-Phi maximum dictionary.
The complete phase/finite-driver mathematics is in the same blueprint;
those last two nodes do not yet have declarations in this source.

Blueprint: hironaka-original-nc-causal-canonical-driver-extension.tex.
Source-only draft; no kernel-check claim.
-/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaOriginalNCCausalAppendFrame

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal CoefficientIdeal
  HironakaStepOneZeroContactRemainderExtension
  HironakaOriginalNCCountHistory HironakaOriginalNCCausalHistoryValue

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- Every ORIGINAL literal year has exactly its original count after a
continuation; no compression or canonicality hypothesis is involved. -/
theorem countAt_append_initial_year (H : Set X) (T : BlowupTower X Y) :
    ∀ {Z : CMfd.{u} n} (P : BlowupTower Y Z) (y : Z) (j : ℕ), j ≤ T.length →
      countAt H (T.append P) y j = countAt H T (P.proj y) j
  | _, .refl, _y, _j, _hj => rfl
  | _, .step P C π hπ, y, j, hj => by
      have hj' : j ≤ (T.append P).length := by
        rw [BlowupTower.length_append]
        omega
      simp only [BlowupTower.append_step, countAt, if_pos hj']
      exact countAt_append_initial_year H T P (π y) j hj

/-- Equality of the actual old counts internally gives equality of the
true Nat.find birth years, including beta=0 and every actual empty year. -/
theorem birthYear_append_of_count_eq (H : Set X) (T : BlowupTower X Y)
    (P : BlowupTower Y Z) (y : Z)
    (he : oldCount H (T.append P) y = oldCount H T (P.proj y)) :
    birthYear H (T.append P) y = birthYear H T (P.proj y) := by
  have hb := birthYear_le_length H T (P.proj y)
  have hLe : birthYear H (T.append P) y ≤ birthYear H T (P.proj y) := by
    apply Nat.find_min'
    rw [countAt_append_initial_year H T P y _ hb, he]
    exact birthYear_spec H T (P.proj y)
  have hNewLe : birthYear H (T.append P) y ≤ T.length := hLe.trans hb
  apply le_antisymm hLe
  apply Nat.find_min'
  have hs := birthYear_spec H (T.append P) y
  rw [countAt_append_initial_year H T P y _ hNewLe, he] at hs
  exact hs

/-- The WHOLE dependent split record, not just its length or projection,
retains the SAME head and appends the prescribed literal continuation. -/
theorem split_append_removed_tail (T : BlowupTower X Y) (k : ℕ) :
    ∀ {Z : CMfd.{u} n} (P : BlowupTower Y Z),
      split (T.append P) (k + P.length) =
        ⟨(split T k).1, head T k, (tail T k).append P⟩
  | _, .refl => by simp only [BlowupTower.length_refl, Nat.add_zero, BlowupTower.append_refl]
  | _, .step P C π hπ => by
      exact congrArg
        (fun s : (Σ B : CMfd.{u} n, BlowupTower X B × BlowupTower B _) =>
          (⟨s.1, s.2.1, .step s.2.2 C π hπ⟩ : Σ B : CMfd.{u} n, BlowupTower X B × BlowupTower B _))
        (split_append_removed_tail T k P)

/- A private total evaluator lets equality transport the WHOLE dependent
split at once. Its extra branch is never used for a genuine birth frame.
This proof abstraction does not replace or modify causalHistoryValue. -/
private def evaluateFrame (M : MarkedIdeal n X) (H : Set X) {Z : CMfd.{u} n}
    (y : Z) (q : ℕ)
    (frame : Σ B : CMfd.{u} n, BlowupTower X B × BlowupTower B Z) :
    ℕ ×ₗ WithBot (CanonicalCentres.ValTy n) :=
  let K := frame.2.1
  let D := frame.2.2
  let W := oldCountLowOpen H K q
  let MW := MarkedIdealBiholomorphism.MarkedIdeal.pullback
    (Subtype.val : W → frame.1) (geoTransformAlong M K)
  let A := contactRemainderMarked (CoefficientIdealRestriction.withN (coeffMarked MW)
    {z : W | q ≤ oldCount H K z.val}) 0
  let S := restrict W D
  if hp : y ∈ openPreimage D W then
    let p : openPreimage D W := ⟨y, hp⟩
    toLex (q, if p ∈ (geoTransformAlong A S).cosupp then
      ((CanonicalCentres.canonicalInvariant n).inv A S p : WithBot (CanonicalCentres.ValTy n)) else ⊥)
  else toLex (q, ⊥)

private theorem causalHistoryValue_eq_evaluateFrame
    (M : MarkedIdeal n X) (H : Set X) (T : BlowupTower X Y) (y : Y) :
    causalHistoryValue M H T y =
      evaluateFrame M H y (oldCount H T y) (split T (T.length - birthYear H T y)) := by
  have hp : y ∈ openPreimage (split T (T.length - birthYear H T y)).2.2
      (oldCountLowOpen H (split T (T.length - birthYear H T y)).2.1 (oldCount H T y)) :=
    (causalBirthPoint H T y).property
  unfold evaluateFrame
  dsimp only
  rw [dif_pos hp]
  rfl

/-- This is the DEFINED original Phi at the current append, expressed on
the SAME old birth datum and its literal continued restricted suffix.
The no-count-drop condition is a pointwise geometric case, not a future
canonicality or value certificate. The natural highest phase derives it
internally at each surviving highest-count point by actual antitonicity. -/
theorem causalHistoryValue_append_of_count_eq (M : MarkedIdeal n X) (H : Set X)
    (T : BlowupTower X Y) (P : BlowupTower Y Z) (y : Z)
    (he : oldCount H (T.append P) y = oldCount H T (P.proj y)) :
    let x := P.proj y
    let k := T.length - birthYear H T x
    let D := tail T k
    let W := causalBirthOpen H T x
    let A := causalBirthRemainder M H T x
    let S := restrict W (D.append P)
    let p : openPreimage (D.append P) W :=
      ⟨y, by
        change (D.append P).proj y ∈ W
        rw [BlowupTower.proj_append]
        exact (causalBirthPoint H T (P.proj y)).property⟩
    causalHistoryValue M H (T.append P) y =
      toLex (oldCount H T x,
        if p ∈ (geoTransformAlong A S).cosupp then
          ((CanonicalCentres.canonicalInvariant n).inv A S p : WithBot (CanonicalCentres.ValTy n))
        else ⊥) := by
  have hβ := birthYear_append_of_count_eq H T P y he
  have hIndex : (T.append P).length - birthYear H (T.append P) y =
      (T.length - birthYear H T (P.proj y)) + P.length := by
    rw [BlowupTower.length_append, hβ]
    have hb := birthYear_le_length H T (P.proj y)
    omega
  let k := T.length - birthYear H T (P.proj y)
  let frame : Σ B : CMfd.{u} n, BlowupTower X B × BlowupTower B Z :=
    ⟨(split T k).1, head T k, (tail T k).append P⟩
  have hFrame : split (T.append P) ((T.append P).length - birthYear H (T.append P) y) = frame := by
    rw [hIndex, split_append_removed_tail T k P]
  have hAux : evaluateFrame M H y (oldCount H (T.append P) y)
      (split (T.append P) ((T.append P).length - birthYear H (T.append P) y)) =
      evaluateFrame M H y (oldCount H T (P.proj y)) frame := by
    rw [he, hFrame]
  dsimp only
  rw [causalHistoryValue_eq_evaluateFrame]
  refine hAux.trans ?_
  have hp : y ∈ openPreimage frame.2.2
      (oldCountLowOpen H frame.2.1 (oldCount H T (P.proj y))) := by
    change ((tail T k).append P).proj y ∈ causalBirthOpen H T (P.proj y)
    rw [BlowupTower.proj_append]
    exact (causalBirthPoint H T (P.proj y)).property
  unfold evaluateFrame
  dsimp only
  rw [dif_pos hp]
  rfl

end
end Hironaka.HironakaOriginalNCCausalAppendFrame
