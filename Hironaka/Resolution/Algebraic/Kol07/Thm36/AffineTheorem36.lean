/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm36.Affine
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization.Centers
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization.Monomial
import Hironaka.Resolution.Algebraic.Kol07.Thm36.Absorption
import Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineEndResult
import Hironaka.Resolution.Algebraic.Kol07.Thm36.CentersOverSupport
import Hironaka.Resolution.Algebraic.Kol07.Thm36.FirstCenter
import Hironaka.Resolution.Algebraic.Kol07.Thm36.Identification
import Hironaka.Resolution.Algebraic.Snc.SncInvertible
import Hironaka.Scheme.BlowUpSequence.InducedData
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Clause (1) of Theorem 36 for the affine resolution

The lemmas of `Hironaka.Resolution.Algebraic.Kol07.Thm36.Absorption` and
`Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineEndResult` take the conclusions of Kollár's
principalization theorem [Kol07, Theorem 35] as hypotheses. Here they are supplied by the library's
proofs of that theorem for the sequence `BP TA`:

* clause (2), `Π^* I_X` is the ideal of a simple normal crossing divisor (`BP_isIdealOfSncDivisor`),
  hence invertible on the smooth end result (`isInvertible_comap_composite_BP`);
* clause (1), every centre is smooth over `k` (`BP_center_smooth_hasSncWith`), so the centre at the
  first containing index is;
* the centres of `BP(A, I_X, ∅)` lie over `V(I_X)` (`stageMap_mem_support_of_mem_center_BP`,
  Kollár's `π_0 ⋯ π_{j−1}(Z_j) ⊂ X̄` by (21.2) in the proof of [Kol07, Corollary 22]).

The results, for an integral algebraic `k`-scheme `X` embedded in the ambient of a triple `TA`
with empty boundary, with `I_X = ker emb` and `X` of codimension `≥ 2` at its generic point: some
centre of `BP TA` contains the strict transform of `X`, so the first-centre index is an index of
the sequence (`exists_centerContains_BP_affine`, `firstCenterIndex_lt_length_BP_affine`,
`centerContains_firstCenterIndex_BP_affine`, `not_centerContains_of_lt_BP_affine`); `BR_affine`
has exactly that many steps (`length_BR_affine_of_integral`); its end result embeds in the last
stage with kernel the strict transform (`ker_pullbackStageHom_last_BR_affine'`); and the end
result is smooth over `k` (`smooth_composite_BR_affine_of_integral`), which is clause (1) of
[Kol07, Theorem 36] for the affine resolution. Clauses (2) and (3) are
`Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineTheorem36IsoSnc`.

The emptiness of the boundary enters only through the last item (the centres over `V(I_X)`); the
standing hypotheses of an algebraic `k`-scheme on `X` (locally of finite type, quasi-compact,
separated over `k`) are carried by every statement although not every proof uses them.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme.BlowUpSequence
  Hironaka.Sequence

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k] (TA : Triple k)

/-! ### Theorem 35 read for the absorption argument -/

/-- Clause (1) of [Kol07, Theorem 35]: `BP TA` is a smooth blow-up sequence (every centre smooth
over `k`). -/
theorem BP_isSmooth : (BP TA).IsSmooth (TA.X.left ↘ Spec (CommRingCat.of k)) :=
  fun i => (BP_center_smooth_hasSncWith TA i).1

/-- The end result of `BP TA` is smooth over `k`: the composite of smooth blow-ups of the smooth
ambient. -/
theorem smooth_composite_BP :
    Smooth ((BP TA).composite ≫ (TA.X.left ↘ Spec (CommRingCat.of k))) := by
  obtain ⟨n, hn⟩ := TA.smoothOfRelativeDimension
  exact IsSmooth.smooth_stageMap (n := n) (BP_isSmooth TA) (Fin.last _)

/-- Clause (2) of [Kol07, Theorem 35] read as in the proof of [Kol07, Corollary 22]: `Π^* I_X` is
invertible, being the ideal of a simple normal crossing divisor on the smooth end result
(`IsIdealOfSncDivisor.isInvertible`). -/
theorem isInvertible_comap_composite_BP : (TA.I.comap (BP TA).composite).IsInvertible := by
  have : IsNoetherian TA.X.left := (TA.X.left ↘ Spec (CommRingCat.of k)).isNoetherian_of_field
  have : IsNoetherian (BP TA).last := isNoetherian_stage (BP TA) (Fin.last _)
  have := smooth_composite_BP TA
  exact (BP_isIdealOfSncDivisor TA).isInvertible
    ((BP TA).composite ≫ (TA.X.left ↘ Spec (CommRingCat.of k)))

/-! ### The first containing centre, the length, and the smooth end result -/

/-! The theorems below are stated for an algebraic `k`-scheme `X` (locally of finite type,
quasi-compact and separated over `k`) embedded by `emb` over `k`, the setting of
[Kol07, Theorem 36], carried by all of them so that they read in one setting; the proofs need
only some of the instances. -/

/-- Some centre of `BP(A, I_X, ∅)` contains the strict transform of `X` [Kol07, Corollary 22,
proof]: `exists_centerContains_BP_of_isInvertible` with clause (2) of [Kol07, Theorem 35]. The
hypothesis `_hE` of an empty boundary is present because Kollár runs the principalization on the
triple `(A, I_X, ∅)` and the statement keeps that setting; the proof does not need it, because
the argument is local at `η_X` and uses only clause (2) of Theorem 35. -/
theorem exists_centerContains_BP_affine {X : Scheme.{u}}
    (emb : X ⟶ TA.X.left) [IsClosedImmersion emb]
    [IsIntegral X] (_hE : IsEmpty TA.E.ι)
    (hI : emb.ker = TA.I)
    (hcodim : ∀ η ∈ genericPoints X, 2 ≤ ringKrullDim (TA.X.left.presheaf.stalk (emb η))) :
    ∃ n, CenterContains (BP TA) TA.I n :=
  exists_centerContains_BP_of_isInvertible TA emb hI hcodim (isInvertible_comap_composite_BP TA)

/-- The first containing index is an index of the sequence `BP TA`. -/
theorem firstCenterIndex_lt_length_BP_affine {X : Scheme.{u}}
    (emb : X ⟶ TA.X.left) [IsClosedImmersion emb]
    [IsIntegral X] (hE : IsEmpty TA.E.ι)
    (hI : emb.ker = TA.I)
    (hcodim : ∀ η ∈ genericPoints X, 2 ≤ ringKrullDim (TA.X.left.presheaf.stalk (emb η))) :
    firstCenterIndex (BP TA) TA.I < (BP TA).length :=
  firstCenterIndex_lt_length (exists_centerContains_BP_affine TA emb hE hI hcodim)

/-- The centre at the first containing index contains the strict transform of `X` [Kol07,
Corollary 22, proof]. -/
theorem centerContains_firstCenterIndex_BP_affine {X : Scheme.{u}}
    (emb : X ⟶ TA.X.left) [IsClosedImmersion emb]
    [IsIntegral X] (hE : IsEmpty TA.E.ι) (hI : emb.ker = TA.I)
    (hcodim : ∀ η ∈ genericPoints X, 2 ≤ ringKrullDim (TA.X.left.presheaf.stalk (emb η))) :
    CenterContains (BP TA) TA.I (firstCenterIndex (BP TA) TA.I) :=
  firstCenterIndex_of_exists (exists_centerContains_BP_affine TA emb hE hI hcodim)

/-- No centre before the first containing index contains the strict transform of `X`. -/
theorem not_centerContains_of_lt_BP_affine {X : Scheme.{u}}
    (emb : X ⟶ TA.X.left) [IsClosedImmersion emb]
    [IsIntegral X] (hE : IsEmpty TA.E.ι)
    (hI : emb.ker = TA.I)
    (hcodim : ∀ η ∈ genericPoints X, 2 ≤ ringKrullDim (TA.X.left.presheaf.stalk (emb η))) {n : ℕ}
    (hn : n < firstCenterIndex (BP TA) TA.I) : ¬ CenterContains (BP TA) TA.I n :=
  not_centerContains_of_lt_firstCenterIndex (exists_centerContains_BP_affine TA emb hE hI hcodim) hn

/-- The affine resolution has exactly `firstCenterIndex (BP TA) TA.I` steps. -/
theorem length_BR_affine_of_integral {X : Scheme.{u}}
    (emb : X ⟶ TA.X.left) [IsClosedImmersion emb]
    [IsIntegral X] (hE : IsEmpty TA.E.ι)
    (hI : emb.ker = TA.I)
    (hcodim : ∀ η ∈ genericPoints X, 2 ≤ ringKrullDim (TA.X.left.presheaf.stalk (emb η))) :
    (BR_affine TA emb).length = firstCenterIndex (BP TA) TA.I := by
  rw [length_BR_affine]
  exact Nat.min_eq_left (firstCenterIndex_lt_length_BP_affine TA emb hE hI hcodim).le

/-- The kernel of the last stage embedding of the affine resolution is the strict transform of `I_X`
[Kol07, Definition 30, 30.2]; `ker_pullbackStageHom_last_BR_affine` restated for a scheme `X`
over `k`. -/
theorem ker_pullbackStageHom_last_BR_affine' {X : Scheme.{u}}
    (emb : X ⟶ TA.X.left) [IsClosedImmersion emb]
    (hI : emb.ker = TA.I) :
    (((BP TA).take (firstCenterIndex (BP TA) TA.I)).pullbackStageHom emb (Fin.last _)).ker =
      ((BP TA).take (firstCenterIndex (BP TA) TA.I)).strictTransformSeq TA.I (Fin.last _) :=
  ker_pullbackStageHom_last_BR_affine TA emb hI

/-- Clause (1) of [Kol07, Theorem 36] for the affine resolution ("`Z_j` is smooth since we blow it
up", [Kol07, Corollary 22, proof]): the end result of `BR_affine TA emb` is smooth over `k`. This is
`smooth_composite_BR_affine_of_smooth_center` with clause (1) of [Kol07, Theorem 35] at the first
containing index and the centres of `BP(A, I_X, ∅)` over `V(I_X)`
(`stageMap_mem_support_of_mem_center_BP`, the one use of the empty boundary). -/
theorem smooth_composite_BR_affine_of_integral {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    (emb : X ⟶ TA.X.left) [IsClosedImmersion emb]
    [emb.IsOver (Spec (CommRingCat.of k))] [IsIntegral X] (hE : IsEmpty TA.E.ι)
    (hI : emb.ker = TA.I)
    (hcodim : ∀ η ∈ genericPoints X, 2 ≤ ringKrullDim (TA.X.left.presheaf.stalk (emb η))) :
    Smooth ((BR_affine TA emb).composite ≫ (X ↘ Spec (CommRingCat.of k))) :=
  smooth_composite_BR_affine_of_smooth_center TA emb hI
    (firstCenterIndex_lt_length_BP_affine TA emb hE hI hcodim)
    (BP_center_smooth_hasSncWith TA ⟨_, firstCenterIndex_lt_length_BP_affine TA emb hE hI hcodim⟩).1
    (fun _ hy => stageMap_mem_support_of_mem_center_BP TA hE _ hy)

end Hironaka.Resolution
