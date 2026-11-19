/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm36.Affine
import Hironaka.Scheme.BlowUpSequence.Restrict
import Hironaka.Scheme.BlowUpSequence.StrictTransformIntegral
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Before the first containing centre

Kollár's construction of the resolution of an embedded affine scheme `X ⊆ A` truncates the
principalization sequence of `I_X` at the first index `j` whose centre `Z_j` contains the strict
transform of `X` [Kol07, Corollary 22, proof]: before that index "`π_0 ⋯ π_{j−1}` is a local
isomorphism around `η_X`". This file records what holds at the stages `i ≤ j`, on top of the
definitions `CenterContains`, `firstCenterIndex` and `BR_affine` of
`Hironaka.Resolution.Algebraic.Kol07.Thm36.Affine`:

* `not_centerContains_of_lt_firstCenterIndex'`: no centre before `firstCenterIndex S I` contains
  the strict transform of `V(I)`, whether or not a containing centre exists (if there is none,
  `firstCenterIndex S I = S.length` and the statement covers every centre of `S`);
* `isIntegral_strictTransformSeq_of_le_firstCenterIndex`: for an integral `V(I)` the strict
  transforms `X̄_i`, `i ≤ firstCenterIndex S I`, are integral;
  `exists_isGenericPoint_strictTransformSeq_of_le_firstCenterIndex`: their generic points `η_i`
  are the unique points of the stages over the generic point `η` of `V(I)`;
  `notMem_center_support_of_stageMap_eq_of_lt_firstCenterIndex`: no point of a centre `Z_i`,
  `i < firstCenterIndex S I`, lies over `η`;
* `ker_pullbackStageHom_last_BR_affine`: the end result of `BR_affine TA emb` embeds in the last
  stage of the truncated principalization sequence with kernel the strict transform of `I_X`
  [Kol07, Definition 30, 30.2].

The identification of `X̄_j` with the irreducible component of the smooth centre `Z_j` through
`η_j` is `Hironaka.Resolution.Algebraic.Kol07.Thm36.Identification`; the transport of the generic
point by local isomorphisms is `Hironaka.Resolution.Algebraic.Wlo05.FirstCenterLocalIso`.

## Conventions

`CenterContains S I n` is the ideal inequality `S.center ⟨n, _⟩ ≤ S.strictTransformSeq I ⟨n, _⟩`
(`Z_n ⊇ X̄_n` as closed subschemes of the stage), and `firstCenterIndex S I` is the least such
`n`, or `S.length` if there is none.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme Hironaka BlowUpSequence
  Scheme.IdealSheafData

namespace Hironaka.Resolution

variable {A : Scheme.{u}}

/-! ### Before the first containing centre -/

/-- No centre before `firstCenterIndex S I` contains the strict transform, whether or not a
containing centre exists. -/
theorem not_centerContains_of_lt_firstCenterIndex' (S : BlowUpSequence A) (I : A.IdealSheafData)
    {n : ℕ} (hn : n < firstCenterIndex S I) : ¬ CenterContains S I n := by
  by_cases h : ∃ m, CenterContains S I m
  · exact not_centerContains_of_lt_firstCenterIndex h hn
  · exact fun hc => h ⟨n, hc⟩

/-- The hypothesis of `AlgebraicGeometry.isIntegral_strictTransformSeq` at an index
`i ≤ firstCenterIndex S I`: no earlier centre contains the strict transform. -/
theorem not_center_le_strictTransformSeq_of_lt_firstCenterIndex (S : BlowUpSequence A)
    (I : A.IdealSheafData) {m : Fin S.length} (hm : m.val < firstCenterIndex S I) :
    ¬ S.center m ≤ S.strictTransformSeq I m.castSucc := fun hle =>
  not_centerContains_of_lt_firstCenterIndex' S I hm ⟨m.2, hle⟩

/-- Before the first containing centre the strict transforms of an integral closed subscheme are
integral [Kol07, Corollary 22, proof]. -/
theorem isIntegral_strictTransformSeq_of_le_firstCenterIndex [IsLocallyNoetherian A]
    (S : BlowUpSequence A) (I : A.IdealSheafData) [IsIntegral I.subscheme]
    (i : Fin (S.length + 1)) (hi : i.val ≤ firstCenterIndex S I) :
    IsIntegral (S.strictTransformSeq I i).subscheme :=
  isIntegral_strictTransformSeq S I i fun _ hm =>
    not_center_le_strictTransformSeq_of_lt_firstCenterIndex S I (lt_of_lt_of_le hm hi)

/-- "`π_0 ⋯ π_{j−1}` is a local isomorphism around `η_X`" [Kol07, Corollary 22, proof]: before the
first containing centre, the generic point `η_i` of the strict transform is the unique point of
the stage over the generic point `η` of `V(I)`. -/
theorem exists_isGenericPoint_strictTransformSeq_of_le_firstCenterIndex [IsLocallyNoetherian A]
    (S : BlowUpSequence A) (I : A.IdealSheafData) [IsIntegral I.subscheme] {η : A}
    (hη : IsGenericPoint η (I.support : Set A)) (i : Fin (S.length + 1))
    (hi : i.val ≤ firstCenterIndex S I) :
    ∃ η' : S.stage i, IsGenericPoint η' ((S.strictTransformSeq I i).support : Set (S.stage i)) ∧
      S.stageMap i η' = η ∧ ∀ y, S.stageMap i y = η → y = η' :=
  exists_isGenericPoint_strictTransformSeq S I hη i fun _ hm =>
    not_center_le_strictTransformSeq_of_lt_firstCenterIndex S I (lt_of_lt_of_le hm hi)

/-- No point of a centre before the first containing one lies over the generic point of `V(I)`:
the starting point of the proof that the affine resolution is an isomorphism over the smooth
locus (`Hironaka.Resolution.Algebraic.Kol07.Thm36.IsoOverSmoothLocus`). -/
theorem notMem_center_support_of_stageMap_eq_of_lt_firstCenterIndex [IsLocallyNoetherian A]
    (S : BlowUpSequence A) (I : A.IdealSheafData) [IsIntegral I.subscheme] {η : A}
    (hη : IsGenericPoint η (I.support : Set A)) (i : Fin S.length)
    (hi : i.val < firstCenterIndex S I) (y : S.stage i.castSucc)
    (hy : S.stageMap i.castSucc y = η) : y ∉ (S.center i).support :=
  notMem_center_support_of_stageMap_eq S I hη i
    (fun _ hm => not_center_le_strictTransformSeq_of_lt_firstCenterIndex S I
      (lt_of_le_of_lt (Fin.le_def.mp hm) hi)) y hy

/-! ### The end result of `BR_affine` -/

variable {k : Type u} [Field k] [CharZero k]

/-- The end result of `BR_affine TA emb` embeds in the last stage of the truncated principalization
sequence with kernel the strict transform of `I_X`: the identification of `S_{i+1}` with the
birational transform `(π_i)^{-1}_* S_i ⊂ X_{i+1}` of [Kol07, Definition 30, 30.2]. This is
`ker_pullbackStageHom` at the truncated sequence `(BP TA).take j`, with `emb.ker = TA.I`. -/
theorem ker_pullbackStageHom_last_BR_affine (TA : Triple k) {X : Scheme.{u}} (emb : X ⟶ TA.X.left)
    [IsClosedImmersion emb] (hI : emb.ker = TA.I) :
    (((Hironaka.Sequence.BP TA).take
        (firstCenterIndex (Hironaka.Sequence.BP TA) TA.I)).pullbackStageHom emb
          (Fin.last _)).ker =
      ((Hironaka.Sequence.BP TA).take
        (firstCenterIndex (Hironaka.Sequence.BP TA) TA.I)).strictTransformSeq TA.I
          (Fin.last _) := by
  rw [ker_pullbackStageHom, hI]

end Hironaka.Resolution
