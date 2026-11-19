/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm36.Affine
public import Hironaka.Scheme.BlowUpSequence.RestrictedCenters
import Hironaka.Resolution.Algebraic.Kol07.IsoRestrict
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization.Centers
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization.Functorial
import Hironaka.Resolution.Algebraic.Kol07.Thm36.Absorption
import Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineTheorem36
import Hironaka.Resolution.Algebraic.Kol07.Thm36.CentersOverSupport
import Hironaka.Resolution.Algebraic.Kol07.Thm36.FirstCenter
import Hironaka.Resolution.Algebraic.Kol07.Thm36.Identification
import Hironaka.Resolution.Algebraic.Kol07.Thm36.IsoOverSmoothLocus
import Hironaka.Resolution.Algebraic.Kol07.Thm36.SncPreimageSingular
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Clauses (2) and (3) of Theorem 36 for the affine resolution of an integral scheme

For the resolution `BR_affine TA emb` of an integral affine scheme `X ↪ A`
(`Hironaka.Resolution.Algebraic.Kol07.Thm36.Affine`), clause (2) of [Kol07, Theorem 36], `Π : X_j →
X` is an isomorphism over the smooth locus of `X`, and clause (3), `Π⁻¹(Sing X)` is the support of a
simple normal crossing family on `X_j`, in the forms used by Hironaka's Main Theorem I
(`Hironaka.Resolution.Algebraic.Hir64.MainTheoremI`); the versions for a reduced `X` whose smooth
locus has one relative dimension, used by the resolution functor, are
`Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineTheorem36Reduced`:

* `not_restrictedCenterHasPointOver_BP_genericPoint`: before the first containing centre no
  restricted centre of `BP TA` has a point over the generic point of `X`
  (`notMem_center_support_of_stageMap_eq_of_lt_firstCenterIndex`);
* `not_restrictedCenterHasPointOver_BP_of_mem_smoothLocus`: Kollár's localisation argument
  [Kol07, 4.2] on the truncation, with the functoriality of the principalization sequence under
  smooth surjections [Kol07, Theorem 35 (4)]: no restricted centre has a point over any smooth
  point of `X` (`not_restrictedCenterHasPointOver_of_mem_smoothLocus`);
* `isIso_composite_restrict_smoothLocus_BR_affine_of_integral`: clause (2);
* `exists_snc_preimage_singularLocus_BR_affine_of_integral`: clause (3), by
  `Hironaka.Resolution.Algebraic.Kol07.Thm36.SncPreimageSingular` on `BP TA` at the first containing
  index, with the first containing centre and clause (1) from
  `Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineTheorem36`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme BlowUpSequence
  Hironaka.Sequence

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k] (TA : Triple k) {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k))] [IsSeparated (X ↘ Spec (CommRingCat.of k))]
  (emb : X ⟶ TA.X.left) [IsClosedImmersion emb] [emb.IsOver (Spec (CommRingCat.of k))]

omit [X.Over (Spec (CommRingCat.of k))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k))] [IsSeparated (X ↘ Spec (CommRingCat.of k))]
  [emb.IsOver (Spec (CommRingCat.of k))] in
/-- Before the first containing centre no restricted centre of the truncation of `BP TA` has a
point over the generic point of `X` [Kol07, Corollary 22, proof]
(`notMem_center_support_of_stageMap_eq_of_lt_firstCenterIndex` through the truncation bridge
`restrictedCenterHasPointOver_take`). -/
theorem not_restrictedCenterHasPointOver_BP_genericPoint [IsIntegral X] (hI : emb.ker = TA.I)
    (i : Fin ((BP TA).take (firstCenterIndex (BP TA) TA.I)).length) :
    ¬ RestrictedCenterHasPointOver ((BP TA).take (firstCenterIndex (BP TA) TA.I)) TA.I i
      (emb (genericPoint X)) := by
  have hInt : IsIntegral TA.I.subscheme := by
    have := isIntegral_image emb
    change IsIntegral emb.ker.subscheme at this
    rwa [hI] at this
  have hη : IsGenericPoint (emb (genericPoint X)) (TA.I.support : Set TA.X.left) := by
    have := isGenericPoint_ker_support emb
    rwa [hI] at this
  have : IsLocallyNoetherian TA.X.left :=
    (TA.X.left ↘ Spec (CommRingCat.of k)).isLocallyNoetherian_of_field
  intro hi
  rw [restrictedCenterHasPointOver_take] at hi
  obtain ⟨p, hZ, -, hp⟩ := hi
  have hlt : i.val < firstCenterIndex (BP TA) TA.I :=
    lt_of_lt_of_le i.2 (by rw [length_take]; exact min_le_left _ _)
  exact notMem_center_support_of_stageMap_eq_of_lt_firstCenterIndex (BP TA) TA.I hη ⟨i.val, _⟩
    hlt p hp hZ

omit [QuasiCompact (X ↘ Spec (CommRingCat.of k))] [IsSeparated (X ↘ Spec (CommRingCat.of k))] in
/-- Kollár's localisation argument [Kol07, 4.2] on the truncation: no restricted centre of the
truncation of `BP TA` at the first containing index has a point over a smooth point of `X`
(`not_restrictedCenterHasPointOver_of_mem_smoothLocus`, with the functoriality of the
principalization sequence under smooth surjections `BP_pullback_of_surjective` as the
functoriality of the assignment `T ↦ BP T`). -/
theorem not_restrictedCenterHasPointOver_BP_of_mem_smoothLocus [IsIntegral X]
    (hE : IsEmpty TA.E.ι) (hI : emb.ker = TA.I) {x : X}
    (hx : x ∈ (X ↘ Spec (CommRingCat.of k)).smoothLocus)
    (i : Fin ((BP TA).take (firstCenterIndex (BP TA) TA.I)).length) :
    ¬ RestrictedCenterHasPointOver ((BP TA).take (firstCenterIndex (BP TA) TA.I)) TA.I i
      (emb x) :=
  not_restrictedCenterHasPointOver_of_mem_smoothLocus TA emb hE hI (fun T => BP T)
    (fun T' g _ hs hp => BP_pullback_of_surjective TA T' g hs hp) (firstCenterIndex (BP TA) TA.I)
    (not_restrictedCenterHasPointOver_BP_genericPoint TA emb hI) hx i

omit [QuasiCompact (X ↘ Spec (CommRingCat.of k))] [IsSeparated (X ↘ Spec (CommRingCat.of k))] in
/-- Clause (2) of [Kol07, Theorem 36] for the affine resolution of an integral scheme:
`Π : X_j → X` is an isomorphism over the smooth locus of `X`. The restricted centres avoid
`X^{ns}`, so `isIso_composite_restrict_of_centers_disjoint` applies to `BR_affine TA emb`. -/
theorem isIso_composite_restrict_smoothLocus_BR_affine_of_integral [IsIntegral X]
    (hE : IsEmpty TA.E.ι) (hI : emb.ker = TA.I) :
    IsIso ((BR_affine TA emb).composite ∣_ (X ↘ Spec (CommRingCat.of k)).smoothLocus) := by
  refine isIso_composite_restrict_of_centers_disjoint (BR_affine TA emb) _ fun i => ?_
  rw [Set.disjoint_left]
  intro p hp hpU
  let i' : Fin ((BP TA).take (firstCenterIndex (BP TA) TA.I)).length :=
    ⟨i.val, lt_of_lt_of_eq i.2 (length_pullback _ emb)⟩
  have hbr := (restrictedCenterHasPointOver_iff_of_isClosedImmersion
    ((BP TA).take (firstCenterIndex (BP TA) TA.I)) emb i'
    ((BR_affine TA emb).stageMap i.castSucc p)).1 ⟨p, hp, rfl⟩
  rw [hI] at hbr
  exact not_restrictedCenterHasPointOver_BP_of_mem_smoothLocus TA emb hE hI hpU i' hbr

omit [QuasiCompact (X ↘ Spec (CommRingCat.of k))] [IsSeparated (X ↘ Spec (CommRingCat.of k))] in
/-- Clause (3) of [Kol07, Theorem 36] for the affine resolution of an integral scheme, after the
proof of [Kol07, Theorem 27]: `Π⁻¹(Sing X)` is the support of a simple normal crossing family, the
restriction `Ex_tot|_{X_j}` of the total exceptional divisor. This is
`Hironaka.Resolution.Algebraic.Kol07.Thm36.SncPreimageSingular` on `BP TA` at the first containing
index, the hypotheses being the first containing centre and
clause (1) of Theorem 36 (`Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineTheorem36`), clause (1)
of [Kol07, Theorem 35] at `j`, the identification `X̄_j = Z_j^η`
(`Hironaka.Resolution.Algebraic.Kol07.Thm36.Identification`, with the centres over `V(I_X)`), "no
earlier centre contains `X̄`", and the mechanism of clause (2). -/
theorem exists_snc_preimage_singularLocus_BR_affine_of_integral [IsIntegral X]
    (hE : IsEmpty TA.E.ι) (hI : emb.ker = TA.I)
    (hcodim : ∀ η ∈ genericPoints X, 2 ≤ ringKrullDim (TA.X.left.presheaf.stalk (emb η))) :
    ∃ F : DivisorFamily (BR_affine TA emb).last, F.IsSnc ∧
      (F.support : Set (BR_affine TA emb).last) =
        (BR_affine TA emb).composite ⁻¹'
          ((X ↘ Spec (CommRingCat.of k)).smoothLocus : Set X)ᶜ := by
  have hsmA := TA.smooth
  have hAn : IsNoetherian TA.X.left := (TA.X.left ↘ Spec (CommRingCat.of k)).isNoetherian_of_field
  have hInt : IsIntegral TA.I.subscheme := by
    have := isIntegral_image emb
    change IsIntegral emb.ker.subscheme at this
    rwa [hI] at this
  -- the first containing centre
  obtain ⟨hj, hle⟩ := centerContains_firstCenterIndex_BP_affine TA emb hE hI hcodim
  -- Theorem 35 (1) at `j`
  obtain ⟨hZsm, hsnc⟩ := BP_center_smooth_hasSncWith TA ⟨_, hj⟩
  -- the identification `X̄_j = Z_j^η`
  have hZreg : IsRegular ((BP TA).center ⟨_, hj⟩).subscheme := ⟨fun x =>
    isRegularLocalRing_stalk
      (((BP TA).center ⟨_, hj⟩).subschemeι ≫ (BP TA).stageMap (Fin.castSucc ⟨_, hj⟩) ≫
        (TA.X.left ↘ Spec (CommRingCat.of k))) x⟩
  have hopen : IsOpenImmersion (Scheme.IdealSheafData.inclusion hle) :=
    isOpenImmersion_inclusion_of_firstCenterIndex (BP TA) TA.I ⟨_, hj⟩ rfl hle hZreg
      fun y hy => stageMap_mem_support_of_mem_center_BP TA hE ⟨_, hj⟩ hy
  -- no earlier centre contains the strict transform
  have hnotle : ∀ m : Fin (BP TA).length, m.val < firstCenterIndex (BP TA) TA.I →
      ¬ (BP TA).center m ≤ (BP TA).strictTransformSeq TA.I m.castSucc :=
    fun m hm => not_center_le_strictTransformSeq_of_lt_firstCenterIndex (BP TA) TA.I hm
  -- Theorem 36 (1)
  have hsmX : Smooth ((((BP TA).take (firstCenterIndex (BP TA) TA.I)).pullback emb).composite ≫
      (X ↘ Spec (CommRingCat.of k))) :=
    smooth_composite_BR_affine_of_integral TA emb hE hI hcodim
  exact exists_isSnc_comap_totalTransformSeq_take (TA.X.left ↘ Spec (CommRingCat.of k)) (BP TA)
    (BP_isOrderGeSeq_zero TA).1 TA.I TA.E hE emb hI hj hle hsnc hnotle hsmX
    fun x hx i => not_restrictedCenterHasPointOver_BP_of_mem_smoothLocus TA emb hE hI hx i

end Hironaka.Resolution
