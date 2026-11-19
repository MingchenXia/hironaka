/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Truncate
public import Hironaka.Scheme.BlowUpSequence.Pullback
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.Restrict
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Restricted centers and their points over the base

The restriction of a blow-up sequence on `A` to a closed subscheme `X ⊆ A` [Kol07, 30.2]
intersects the centers `Z_i` with the birational transforms `X̄_i`. In the proof that the
resolution of a quasi-projective variety is an isomorphism over the smooth locus
([Kol07, Theorem 36 (2)], following the proof of [Kol07, Theorem 27] and the locality of
functorial resolutions in [Kol07, 4.2]), the statement "the restricted center `Z_i ∩ X̄_i` has a
point over the point `x` of `X`" is transported along the functoriality of the whole sequence
under a smooth surjection (the first clause of [Kol07, 34.1]). This module holds that
bookkeeping, for arbitrary schemes:

* `take_pullback`: truncation commutes with pullback,
  `(S.take k).pullback h = (S.pullback h).take k`, a structural induction, so that a statement
  about the pulled-back whole sequence restricts to its first `j` steps;
* `RestrictedCenterHasPointOver S J i x`: the `i`-th center of `S` meets the `i`-th strict
  transform of `V(J)` at a point lying over `x`, i.e. Kollár's restricted center `Z_i ∩ X̄_i` has
  a point over `x`;
* `restrictedCenterHasPointOver_pullback_iff`: along a flat `h : Y ⟶ X` the predicate for the
  pulled-back sequence at `y` is the predicate for `S` at `h y`: the stage square `X_i ×_X Y` is
  cartesian (`isPullback_pullbackStageHom`), the centers and strict transforms pull back
  (`center_pullback`, `strictTransformSeq_pullback`), and a point of the fibre product exists
  over every compatible pair (`Scheme.exists_preimage_of_isPullback`);
* `restrictedCenterHasPointOver_iff_of_isClosedImmersion`: along a closed immersion `emb : X ⟶ A`
  the centers of the restriction `S.pullback emb` have a point over `x ∈ X` iff the restricted
  center of `S` has a point over `emb x`: the stage lift `X_i ↪ A_i` is a closed immersion onto
  the strict transform (`isClosedImmersion_pullbackStageHom`, `ker_pullbackStageHom`).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Scheme BlowUpSequence

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-! ### Truncation commutes with pullback -/

/-- The pullback of the first `k` blow-ups is the first `k` blow-ups of the pullback. -/
theorem take_pullback : ∀ {X : Scheme.{u}} (S : BlowUpSequence X) {Y : Scheme.{u}} (h : Y ⟶ X)
    (k : ℕ), (S.take k).pullback h = (S.pullback h).take k
  | _, nil _, _, _, _ => rfl
  | _, cons _ _ _, _, _, 0 => rfl
  | _, cons X D rest, _, h, k + 1 => by
    rw [take_cons_succ, pullback_cons, pullback_cons, take_cons_succ,
      take_pullback rest (Scheme.Hom.blowUpMap h D) k]

/-! ### The restricted center has a point over the base point -/

/-- The restricted center `Z_i ∩ X̄_i` of [Kol07, 30.2] of the sequence `S` relative to the closed
subscheme `V(J)` **has a point over `x`**: a point of the `i`-th stage lying in the center `Z_i`,
in the `i`-th strict transform of `V(J)`, and over `x` under the stage map `Π_i`. -/
def RestrictedCenterHasPointOver (S : BlowUpSequence X) (J : X.IdealSheafData) (i : Fin S.length)
    (x : X) : Prop :=
  ∃ p : S.stage i.castSucc, p ∈ (S.center i).support ∧
    p ∈ (S.strictTransformSeq J i.castSucc).support ∧ S.stageMap i.castSucc p = x

/-- Along a flat `h : Y ⟶ X`, the restricted center of the pulled-back sequence relative to
`h⁻¹(V(J))` has a point over `y` iff the restricted center of `S` relative to `V(J)` has a point
over `h y`: the stage squares are cartesian (`isPullback_pullbackStageHom`), so the points of the
pulled-back stage over `y` are exactly the points of `X_i ×_X Y` over the points of `X_i` over
`h y`. -/
theorem restrictedCenterHasPointOver_pullback_iff (S : BlowUpSequence X) (h : Y ⟶ X) [Flat h]
    (J : X.IdealSheafData) (i : Fin S.length) (y : Y) :
    RestrictedCenterHasPointOver (S.pullback h) (J.comap h) (S.pullbackCenterIdx h i) y ↔
      RestrictedCenterHasPointOver S J i (h y) := by
  unfold RestrictedCenterHasPointOver
  have hsq := isPullback_pullbackStageHom S h i.castSucc
  have hc := center_pullback S h i
  have hs := strictTransformSeq_pullback_castSucc S h J i
  have hm := pullbackStageHom_stageMap S h i.castSucc
  constructor
  · rintro ⟨p', hZ, hT, rfl⟩
    refine ⟨S.pullbackStageHom h i.castSucc p', ?_, ?_, ?_⟩
    · rw [hc, mem_support_comap_iff_apply] at hZ
      exact hZ
    · rw [hs, mem_support_comap_iff_apply] at hT
      exact hT
    · rw [← Scheme.Hom.comp_apply, hm, Scheme.Hom.comp_apply]
      rfl
  · rintro ⟨p, hZ, hT, hp⟩
    obtain ⟨p', hp'p, hp'y⟩ := Scheme.exists_preimage_of_isPullback hsq p y hp
    refine ⟨p', ?_, ?_, hp'y⟩
    · rw [hc, mem_support_comap_iff_apply, hp'p]
      exact hZ
    · rw [hs, mem_support_comap_iff_apply, hp'p]
      exact hT

/-! ### The restriction to a closed subscheme -/

/-- Along a closed immersion `emb : X ⟶ A`, the `i`-th center of the restriction `S.pullback emb`
has a point over `x ∈ X` iff the restricted center `Z_i ∩ X̄_i` of `S` relative to `V(emb.ker)`
has a point over `emb x` [Kol07, 30.2]: the stage lift `X_i ↪ A_i` is a closed immersion whose
image is the strict transform `X̄_i` (`isClosedImmersion_pullbackStageHom`,
`ker_pullbackStageHom`). -/
theorem restrictedCenterHasPointOver_iff_of_isClosedImmersion (S : BlowUpSequence X)
    (emb : Y ⟶ X) [IsClosedImmersion emb] (i : Fin S.length) (y : Y) :
    (∃ p : (S.pullback emb).stage (S.pullbackCenterIdx emb i).castSucc,
        p ∈ ((S.pullback emb).center (S.pullbackCenterIdx emb i)).support ∧
        (S.pullback emb).stageMap (S.pullbackCenterIdx emb i).castSucc p = y) ↔
      RestrictedCenterHasPointOver S emb.ker i (emb y) := by
  unfold RestrictedCenterHasPointOver
  have := isClosedImmersion_pullbackStageHom S emb i.castSucc
  have hker := ker_pullbackStageHom S emb i.castSucc
  have hc := center_pullback S emb i
  have hm := pullbackStageHom_stageMap S emb i.castSucc
  have hrange : Set.range (S.pullbackStageHom emb i.castSucc) =
      (S.strictTransformSeq emb.ker i.castSucc).support := by
    rw [← hker, Scheme.Hom.support_ker,
      (S.pullbackStageHom emb i.castSucc).isClosedEmbedding.isClosed_range.closure_eq]
  constructor
  · rintro ⟨p', hZ, rfl⟩
    refine ⟨S.pullbackStageHom emb i.castSucc p', ?_, ?_, ?_⟩
    · rw [hc, mem_support_comap_iff_apply] at hZ
      exact hZ
    · have hmem : S.pullbackStageHom emb i.castSucc p' ∈
          Set.range (S.pullbackStageHom emb i.castSucc) := ⟨p', rfl⟩
      rw [hrange] at hmem
      exact hmem
    · rw [← Scheme.Hom.comp_apply, hm, Scheme.Hom.comp_apply]
      rfl
  · rintro ⟨p, hZ, hT, hp⟩
    have hT' : p ∈ Set.range (S.pullbackStageHom emb i.castSucc) := by
      rw [hrange]
      exact hT
    obtain ⟨p', rfl⟩ := hT'
    refine ⟨p', ?_, ?_⟩
    · rw [hc, mem_support_comap_iff_apply]
      exact hZ
    · apply emb.isClosedEmbedding.injective
      change emb ((S.pullback emb).stageMap (S.pullbackStageIdx emb i.castSucc) p') = emb y
      rw [← Scheme.Hom.comp_apply, ← hm, Scheme.Hom.comp_apply]
      exact hp

end AlgebraicGeometry
