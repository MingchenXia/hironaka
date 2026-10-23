/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.Unconditional
import DeJongAlterations.StableModification.BlowDown.ClosureLocalAssembly

/-!
# The blow-down results without named hypotheses

The last named hypothesis of the blow-down lanes, `ExcSpecialize.ClosureComponentLocal`, is a
theorem (`ExcSpecialize.closureComponentLocal`, `BlowDown/ClosureLocalAssembly.lean`). This file
restates the results of `BlowDown.Unconditional` (and lane T44A3's specialization lemma) without
it (M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010),
`references/temkin10-stable-modification/source/semi-stable.tex`, Lemma 4.4.4 `emptylem`,
T:3158–3176, and Proposition 4.4.6):

* `exists_isCombExceptional_closedFibre`: lane T44A3's `lem:sm-bd-exc-specialize`;
* `numericallyStableFibre_residuePt_of_closedPoint`, `numericallyStableFibre_of_closedPoint`,
  `numericallyStable_iff_closedPoint`, `isStableModification_of_numericallyStableFibre_closedPoint`,
  `numericallyStableFibre_of_forall_not_isCombExceptional`,
  `isStableModification_of_forall_not_isCombExceptional`: **Temkin's Lemma 4.4.4** in the forms
  of `BlowDown.NoClosedExc`, with no named hypothesis;
* `exists_isStableModification_of_isSemistableStage`: Temkin's Proposition 4.4.6 with only the
  contracting morphisms (`ContractingMorphismExists`) as a hypothesis;
* `exists_isStableModification_of_isSemistableStage_of_isProjectiveOver`: **the stable
  blow-down for `C` projective over `V`, with no named hypothesis**.

Blueprint: `sm-blow-down-closure-local.tex`, `cor:sm-bdcl-unconditional`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

namespace DeJongAlterations.StableModification.BlowDown.UnconditionalFinal

universe u

open DeJongAlterations.StableModification.CurvesField
open DeJongAlterations.StableModification.CurvesField.Genus
open ClosureComponent (residuePt closureScheme closureι)
open NoClosedExc ExcSpecialize
open Curves (pullbackCompMap)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

section Specialize

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [Finite (PrimeSpectrum V)]
  {X C : Scheme.{u}} (β : X ⟶ C) (g : C ⟶ Spec (CommRingCat.of V)) (D' : X.IdealSheafData)

/-- **Exceptional components specialize** (lane T44A3's
`ExcSpecialize.exists_isCombExceptional_closedFibre`, blueprint `lem:sm-bde-exc-specialize`,
without `ClosureComponentLocal`): a numerically exceptional component of `X_t` produces a
combinatorially exceptional component of the closed fibre. -/
theorem exists_isCombExceptional_closedFibre
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsProper (β ≫ g)] [IsProper g] (hp : IsProjectiveOver (β ≫ g))
    (hpair : DeJong.IsSemistablePair (β ≫ g) D')
    [IsAlgClosed (IsLocalRing.closedPoint V).asIdeal.ResidueField]
    {t : PrimeSpectrum V} [IsAlgClosed t.asIdeal.ResidueField]
    (ζ : pullback (C := Scheme.{u}) (β ≫ g) (residuePt t))
    (hζ : ζ ∈ genericPoints (pullback (C := Scheme.{u}) (β ≫ g) (residuePt t)))
    (hcontr : (pullbackCompMap β g (residuePt t) '' closure {ζ}).Subsingleton)
    (hχ : eulerChar (closureScheme ζ)
      (Cohomology.structureCoeff (closureι ζ ≫ pullback.snd (β ≫ g) (residuePt t))) = 1)
    (hspec : (closure {ζ} ∩ specialPoints (β ≫ g) D' (residuePt t)).encard ≤ 2) :
    ∃ v, IsCombExceptional β g D' (residuePt (IsLocalRing.closedPoint V)) v :=
  ExcSpecialize.exists_isCombExceptional_closedFibre β g D' closureComponentLocal hsep hp hpair ζ
    hζ hcontr hχ hspec

end Specialize

section NoClosedExc

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [Finite (PrimeSpectrum V)]
  {X C : Scheme.{u}} (β : X ⟶ C) (g : C ⟶ Spec (CommRingCat.of V)) (D' : X.IdealSheafData)

/-- **Temkin's Lemma 4.4.4, numerical form, over the residue points**, with no named hypothesis
(`Unconditional.numericallyStableFibre_residuePt_of_closedPoint` without
`ClosureComponentLocal`). -/
theorem numericallyStableFibre_residuePt_of_closedPoint
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsProper (β ≫ g)] [IsProper g] (hp : IsProjectiveOver (β ≫ g))
    (hpair : DeJong.IsSemistablePair (β ≫ g) D')
    [IsAlgClosed (IsLocalRing.closedPoint V).asIdeal.ResidueField]
    (hE₀ : NumericallyStableFibre β g D' (residuePt (IsLocalRing.closedPoint V)))
    (t : PrimeSpectrum V) [IsAlgClosed t.asIdeal.ResidueField] :
    NumericallyStableFibre β g D' (residuePt t) :=
  Unconditional.numericallyStableFibre_residuePt_of_closedPoint β g D' closureComponentLocal hsep
    hp hpair hE₀ t

/-- **Temkin's Lemma 4.4.4, numerical form, for all geometric fibres**, with no named hypothesis
(`Unconditional.numericallyStableFibre_of_closedPoint` without `ClosureComponentLocal`). -/
theorem numericallyStableFibre_of_closedPoint
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    (halg : ∀ t : PrimeSpectrum V, IsAlgClosed t.asIdeal.ResidueField)
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsProper (β ≫ g)] [IsProper g] (hp : IsProjectiveOver (β ≫ g))
    (hpair : DeJong.IsSemistablePair (β ≫ g) D')
    (hE₀ : NumericallyStableFibre β g D' (residuePt (IsLocalRing.closedPoint V)))
    (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ Spec (CommRingCat.of V)) :
    NumericallyStableFibre β g D' a :=
  Unconditional.numericallyStableFibre_of_closedPoint β g D' closureComponentLocal hsep halg hp
    hpair hE₀ K a

/-- **Temkin's Lemma 4.4.4, numerical form, as an equivalence**, with no named hypothesis
(`Unconditional.numericallyStable_iff_closedPoint` without `ClosureComponentLocal`): all
geometric fibres are numerically stable iff the closed fibre is. -/
theorem numericallyStable_iff_closedPoint
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    (halg : ∀ t : PrimeSpectrum V, IsAlgClosed t.asIdeal.ResidueField)
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsProper (β ≫ g)] [IsProper g] (hp : IsProjectiveOver (β ≫ g))
    (hpair : DeJong.IsSemistablePair (β ≫ g) D') :
    (∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ Spec (CommRingCat.of V)),
        NumericallyStableFibre β g D' a) ↔
      NumericallyStableFibre β g D' (residuePt (IsLocalRing.closedPoint V)) :=
  Unconditional.numericallyStable_iff_closedPoint β g D' closureComponentLocal hsep halg hp hpair

/-- **Temkin's Lemma 4.4.4 for Temkin's stability**, with no named hypothesis
(`Unconditional.isStableModification_of_numericallyStableFibre_closedPoint` without
`ClosureComponentLocal`). -/
theorem isStableModification_of_numericallyStableFibre_closedPoint
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    (halg : ∀ t : PrimeSpectrum V, IsAlgClosed t.asIdeal.ResidueField)
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsProper (β ≫ g)] [IsProper g] (hp : IsProjectiveOver (β ≫ g))
    (D : C.IdealSheafData) (hη : Curves.IsEtaModification β g)
    (hmarks : D' = Curves.genericMarksClosure β g D (genericPoint (Spec (CommRingCat.of V))))
    (hpair : DeJong.IsSemistablePair (β ≫ g) D')
    (hE₀ : NumericallyStableFibre β g D' (residuePt (IsLocalRing.closedPoint V))) :
    Curves.IsStableModification β g D D' :=
  Unconditional.isStableModification_of_numericallyStableFibre_closedPoint β g D'
    closureComponentLocal hsep halg hp D hη hmarks hpair hE₀

/-- **Lemma 4.4.4, combinatorial form, for all geometric fibres**, with no named hypothesis
(`Unconditional.numericallyStableFibre_of_forall_not_isCombExceptional` without
`ClosureComponentLocal`). -/
theorem numericallyStableFibre_of_forall_not_isCombExceptional
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    (halg : ∀ t : PrimeSpectrum V, IsAlgClosed t.asIdeal.ResidueField)
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsProper (β ≫ g)] [IsProper g] (hp : IsProjectiveOver (β ≫ g))
    (hpair : DeJong.IsSemistablePair (β ≫ g) D')
    (hE₀ : ∀ v, ¬ IsCombExceptional β g D' (residuePt (IsLocalRing.closedPoint V)) v)
    (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ Spec (CommRingCat.of V)) :
    NumericallyStableFibre β g D' a :=
  Unconditional.numericallyStableFibre_of_forall_not_isCombExceptional β g D'
    closureComponentLocal hsep halg hp hpair hE₀ K a

/-- **Temkin's Lemma 4.4.4 for Temkin's stability, combinatorial form**, with no named
hypothesis (`Unconditional.isStableModification_of_forall_not_isCombExceptional` without
`ClosureComponentLocal`). -/
theorem isStableModification_of_forall_not_isCombExceptional
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    (halg : ∀ t : PrimeSpectrum V, IsAlgClosed t.asIdeal.ResidueField)
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsProper (β ≫ g)] [IsProper g] (hp : IsProjectiveOver (β ≫ g))
    (D : C.IdealSheafData) (hη : Curves.IsEtaModification β g)
    (hmarks : D' = Curves.genericMarksClosure β g D (genericPoint (Spec (CommRingCat.of V))))
    (hpair : DeJong.IsSemistablePair (β ≫ g) D')
    (hE₀ : ∀ v, ¬ IsCombExceptional β g D' (residuePt (IsLocalRing.closedPoint V)) v) :
    Curves.IsStableModification β g D D' :=
  Unconditional.isStableModification_of_forall_not_isCombExceptional β g D' closureComponentLocal
    hsep halg hp D hη hmarks hpair hE₀

end NoClosedExc

section Stable

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [Finite (PrimeSpectrum V)]
  {C : Scheme.{u}} (φ : C ⟶ Spec (CommRingCat.of V)) (D : C.IdealSheafData)
  [IsIntegral C] [IsProper φ] [Flat φ] [HenselianLocalRing V]

/-- **Temkin's Proposition 4.4.6** (`Unconditional.exists_isStableModification_of_isSemistableStage`
without `ClosureComponentLocal`): every semi-stable stage dominates a semi-stable stage which is a
stable modification with numerically stable geometric fibres, given Temkin's contracting
morphisms (`ContractingMorphismExists`). -/
theorem exists_isStableModification_of_isSemistableStage
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    (halg : ∀ t : PrimeSpectrum V, IsAlgClosed t.asIdeal.ResidueField)
    (hdimC : ValuationRing.fiberTrdeg φ (genericPoint C) ≤ 1)
    (hcontract : ContractingMorphismExists φ D)
    (Y : Scheme.{u}) (β : Y ⟶ C) (hY : IsSemistableStage φ D β) :
    ∃ (Y'' : Scheme.{u}) (β'' : Y'' ⟶ C) (b : Y ⟶ Y''), b ≫ β'' = β ∧
      IsSemistableStage φ D β'' ∧
      Curves.IsStableModification β'' φ D
        (Curves.genericMarksClosure β'' φ D (genericPoint (Spec (CommRingCat.of V)))) ∧
      ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ Spec (CommRingCat.of V)),
        NumericallyStableFibre β'' φ
          (Curves.genericMarksClosure β'' φ D (genericPoint (Spec (CommRingCat.of V)))) a :=
  Unconditional.exists_isStableModification_of_isSemistableStage φ D closureComponentLocal hsep
    halg hdimC hcontract Y β hY

/-- **The stable blow-down for `C` projective over `V`, with no named hypothesis** (Temkin's
Proposition 4.4.6; the `Unconditional` theorem of the same name without
`ClosureComponentLocal`, blueprint `cor:sm-bdcl-unconditional`): for a valuation ring `V`
with finitely many primes, henselian, with all `Frac(V/𝔭)` separably closed and all residue
fields `κ(t)` algebraically closed, and `C` integral, flat, proper and projective over `V` with
generic fibre of dimension at most one, every semi-stable stage `β : Y → C` is dominated by a
semi-stable stage `β''` which is a stable modification of `(C, D)` with numerically stable
geometric fibres. -/
theorem exists_isStableModification_of_isSemistableStage_of_isProjectiveOver
    (hC : IsProjectiveOver φ)
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    (halg : ∀ t : PrimeSpectrum V, IsAlgClosed t.asIdeal.ResidueField)
    (hdimC : ValuationRing.fiberTrdeg φ (genericPoint C) ≤ 1)
    (Y : Scheme.{u}) (β : Y ⟶ C) (hY : IsSemistableStage φ D β) :
    ∃ (Y'' : Scheme.{u}) (β'' : Y'' ⟶ C) (b : Y ⟶ Y''), b ≫ β'' = β ∧
      IsSemistableStage φ D β'' ∧
      Curves.IsStableModification β'' φ D
        (Curves.genericMarksClosure β'' φ D (genericPoint (Spec (CommRingCat.of V)))) ∧
      ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ Spec (CommRingCat.of V)),
        NumericallyStableFibre β'' φ
          (Curves.genericMarksClosure β'' φ D (genericPoint (Spec (CommRingCat.of V)))) a :=
  Unconditional.exists_isStableModification_of_isSemistableStage_of_isProjectiveOver φ D
    closureComponentLocal hC hsep halg hdimC Y β hY

end Stable

end DeJongAlterations.StableModification.BlowDown.UnconditionalFinal
