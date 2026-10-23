/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.NormalizationCurve
import DeJongAlterations.StableModification.Projectivity.Reduction

/-!
# Projectivity bookkeeping for the blow-down (PLAN-T5 node B1)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), Prop. 4.4.6
(T:3188–3229) contracts an exceptional component `Z` of a semi-stable `V`-curve `C'` by a
morphism `h̄ : C' → ℙ¹_C` and takes `C'' = Nor_{C'}(h̄(C'))`. In the de Jong route every curve is
projective over the valuation ring `V` (PLAN-T5 §2.2, DJA-O17), and the toolbox
(constancy of `χ`, Stein finiteness, Zariski connectedness, the stability criterion) is proved
for projective curves only. This file records the projectivity of the curves produced by
relative normalization (blueprint `lem:sm-bdg-projective`, `sm-blow-down-global.tex`):

* `isRelativelyProjective_of_isProjectiveOver_comp`: a projective `V`-scheme mapping to a
  separated `V`-scheme `T` is projective relative to `T` (cancellation along the separated
  projection `T ×_V ℙⁿ_V → ℙⁿ_V`; lane OM3A's
  `Projectivity.isRelativelyProjective_of_isProjectiveOver`, restated here for the blow-down);
* `isFinite_fromNormalization_of_isProjectiveOver`: for `π : B → T` with `B` projective and flat
  over `V` and `T` separated and of finite presentation over `V`, the relative normalization
  `Nor_B(T) = Spec π_* 𝒪_B` is finite over `T` (Stein finiteness, lane COH3B's
  `Cohomology.isFinite_fromNormalization_of_isRelativelyProjective`);
* `isProjectiveOver_fromNormalization`: if moreover `T` is projective over `V`, so is `Nor_B(T)`
  (Codex's `Geometry.FiniteProjective.isProjectiveOver_comp_of_isFinite`);
* `isRelativelyProjective_toNormalization`: `B → Nor_B(T)` is projective relative to
  `Nor_B(T) → Spec V`.
-/

namespace DeJongAlterations.StableModification.BlowDown

open AlgebraicGeometry CategoryTheory Limits

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

noncomputable section

section Cancellation

variable {k : Type u} [CommRing k] {X T : Scheme.{u}}

/-- **Cancellation** (blueprint `lem:sm-bdg-projective`): a `k`-morphism `f : X ⟶ T` from a
projective `k`-scheme to a separated `k`-scheme is projective relative to `pT`: the graph
`X → T ×_k ℙⁿ_k` of a closed immersion `X → ℙⁿ_k` is a closed immersion, since its composite with
the separated projection to `ℙⁿ_k` is (lane OM3A's
`Projectivity.isRelativelyProjective_of_isProjectiveOver`). -/
theorem isRelativelyProjective_of_isProjectiveOver_comp (pT : T ⟶ Spec (.of k)) [IsSeparated pT]
    (f : X ⟶ T) (hX : IsProjectiveOver (f ≫ pT)) : DeJong.IsRelativelyProjective pT f :=
  Projectivity.isRelativelyProjective_of_isProjectiveOver pT f hX

/-- A morphism from a scheme proper over `k` to a separated `k`-scheme is proper. -/
theorem isProper_of_isProper_comp (pT : T ⟶ Spec (.of k)) [IsSeparated pT] (f : X ⟶ T)
    [IsProper (f ≫ pT)] : IsProper f :=
  IsProper.of_comp f pT

end Cancellation

section Normalization

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] {B T : Scheme.{u}}
  (pT : T ⟶ Spec (CommRingCat.of V)) (π : B ⟶ T) [IsProper π]

/-- **Stein finiteness for a projective source** (lane COH3B's
`Cohomology.isFinite_fromNormalization_of_isRelativelyProjective` with the cancellation lemma):
`Nor_B(T) → T` is finite if `B` is projective and flat over `V` and `T` is separated and of finite
presentation over `V`. -/
theorem isFinite_fromNormalization_of_isProjectiveOver [IsSeparated pT]
    [LocallyOfFinitePresentation pT] [Flat (π ≫ pT)] (hB : IsProjectiveOver (π ≫ pT)) :
    IsFinite π.fromNormalization := by
  exact Cohomology.isFinite_fromNormalization_of_isRelativelyProjective V π pT
    (isRelativelyProjective_of_isProjectiveOver_comp pT π hB)

/-- **The relative normalization of a projective `V`-curve in a projective flat one is
projective** (blueprint `lem:sm-bdg-projective`): `Nor_B(T)` is finite over the projective `T`
(`isFinite_fromNormalization_of_isProjectiveOver`), hence projective over `V` (Codex's
`Geometry.FiniteProjective.isProjectiveOver_comp_of_isFinite`). -/
theorem isProjectiveOver_fromNormalization [IsSeparated pT] [LocallyOfFinitePresentation pT]
    [Flat (π ≫ pT)] (hT : IsProjectiveOver pT) (hB : IsProjectiveOver (π ≫ pT)) :
    IsProjectiveOver (π.fromNormalization ≫ pT) := by
  have := isFinite_fromNormalization_of_isProjectiveOver pT π hB
  exact Geometry.FiniteProjective.isProjectiveOver_comp_of_isFinite pT hT π.fromNormalization

/-- **`B → Nor_B(T)` is projective relative to `Nor_B(T) → Spec V`** (cancellation: `B` is
projective over `V`, `Nor_B(T)` is separated over `V`). -/
theorem isRelativelyProjective_toNormalization [IsSeparated pT] [LocallyOfFinitePresentation pT]
    [Flat (π ≫ pT)] (hB : IsProjectiveOver (π ≫ pT)) :
    DeJong.IsRelativelyProjective (π.fromNormalization ≫ pT) π.toNormalization := by
  have := isFinite_fromNormalization_of_isProjectiveOver pT π hB
  refine isRelativelyProjective_of_isProjectiveOver_comp _ _ ?_
  rwa [Scheme.Hom.toNormalization_fromNormalization_assoc]

end Normalization

end

end DeJongAlterations.StableModification.BlowDown
