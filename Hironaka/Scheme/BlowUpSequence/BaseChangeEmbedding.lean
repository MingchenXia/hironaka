/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Hironaka.Scheme.BlowUp.BlowUpMapSquare

/-!
# The base change of a closed embedding

In the proof of [Kol07, Theorem 36], the change of fields for the resolution functor follows from
that of the principalization functor, since an embedding `i : X ↪ A` over `K` and `σ : K ↪ L`
give "another embedding `i_{σ,L} : X_{σ,L} ↪ A_{σ,L}`": a closed embedding over `k` base-changes
to a closed embedding over `L`, with the base-changed ideal. This module proves it in the
pullback-square form of `IsBaseChangeOf` (two cartesian squares over the same `q : S' ⟶ S`):

* `baseChangeEmbedding emb hemb hX hA : X' ⟶ A'`, the morphism induced on the base changes by
  `emb : X ⟶ A` over `S`; `baseChangeEmbedding_comp` (`⋯ ≫ pA = pX ≫ emb`) and
  `baseChangeEmbedding_over` (`⋯ ≫ fA' = fX'`);
* `isPullback_baseChangeEmbedding`: the square `X' → A'`, `X → A` over `pX`, `pA` is a pullback
  (pasting, `IsPullback.of_right`);
* `isClosedImmersion_baseChangeEmbedding`: a closed immersion base-changes to a closed immersion;
* `ker_baseChangeEmbedding`: its kernel is the inverse image `emb.ker.comap pA` of the kernel
  (`ker_fst_of_isClosedImmersion` on the canonical pullback);
* `baseChangeEmbedding_eq_pullback_map`: on the canonical pullbacks it is `pullback.map`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

variable {X A S X' A' S' : Scheme.{u}} (emb : X ⟶ A) {fX : X ⟶ S} {fA : A ⟶ S}
  (hemb : emb ≫ fA = fX) {q : S' ⟶ S} {pX : X' ⟶ X} {fX' : X' ⟶ S'} (hX : IsPullback pX fX' fX q)
  {pA : A' ⟶ A} {fA' : A' ⟶ S'} (hA : IsPullback pA fA' fA q)

/-- The morphism induced on the base changes `X' → X`, `A' → A` (two pullback squares over
`q : S' → S`) by a morphism `emb : X ⟶ A` over `S`: Kollár's `i_{σ,L} : X_{σ,L} ↪ A_{σ,L}` in the
proof of [Kol07, Theorem 36]. -/
noncomputable def baseChangeEmbedding : X' ⟶ A' :=
  hA.lift (pX ≫ emb) fX' (by rw [Category.assoc, hemb]; exact hX.w)

@[reassoc (attr := simp)]
theorem baseChangeEmbedding_comp : baseChangeEmbedding emb hemb hX hA ≫ pA = pX ≫ emb :=
  hA.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem baseChangeEmbedding_over : baseChangeEmbedding emb hemb hX hA ≫ fA' = fX' :=
  hA.lift_snd _ _ _

/-- The base change of `emb` is a pullback square over `pA`, `pX` (pasting with the square of
`A`). -/
theorem isPullback_baseChangeEmbedding :
    IsPullback (baseChangeEmbedding emb hemb hX hA) pX pA emb := by
  have s : IsPullback (baseChangeEmbedding emb hemb hX hA ≫ fA') pX q (emb ≫ fA) := by
    rw [baseChangeEmbedding_over, hemb]
    exact hX.flip
  exact IsPullback.of_right s (baseChangeEmbedding_comp emb hemb hX hA) hA.flip

/-- A closed immersion base-changes to a closed immersion. -/
theorem isClosedImmersion_baseChangeEmbedding [IsClosedImmersion emb] :
    IsClosedImmersion (baseChangeEmbedding emb hemb hX hA) :=
  property_of_isPullback @IsClosedImmersion
    (isPullback_baseChangeEmbedding emb hemb hX hA) ‹_›

/-- The kernel of the base-changed embedding is the inverse image of the kernel,
`I_{X_L} = p^* I_X` (the proof of [Kol07, Theorem 36]). -/
theorem ker_baseChangeEmbedding [IsClosedImmersion emb] :
    (baseChangeEmbedding emb hemb hX hA).ker = emb.ker.comap pA := by
  have hsq := isPullback_baseChangeEmbedding emb hemb hX hA
  rw [← hsq.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

/-- On the canonical pullbacks `X ×_S S'`, `A ×_S S'`, the induced morphism is `pullback.map`. -/
theorem baseChangeEmbedding_eq_pullback_map (fX : X ⟶ S) (fA : A ⟶ S) (hemb : emb ≫ fA = fX)
    (q : S' ⟶ S) :
    baseChangeEmbedding emb hemb (IsPullback.of_hasPullback fX q) (IsPullback.of_hasPullback fA q) =
      pullback.map fX q fA q emb (𝟙 S') (𝟙 S) (by rw [hemb, Category.comp_id])
        (by rw [Category.id_comp, Category.comp_id]) := by
  apply pullback.hom_ext
  · rw [baseChangeEmbedding_comp, pullback.lift_fst]
  · rw [baseChangeEmbedding_over, pullback.lift_snd, Category.comp_id]

end AlgebraicGeometry
