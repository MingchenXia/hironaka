/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane T45C)
-/
import DeJongAlterations.StableModification.Gluing.CofinalProjective

/-!
# A nodal modification of a curve over a valuation ring, unconditionally

Lane T45A proved `Gluing.exists_nodal_modification` (`PLAN-T5.md` §2.2 steps 1–8, nodes A1–A8;
Temkin, proof of Proposition 4.5.1, T:3243–3266) under the hypothesis `ProjectiveCofinality R`
(node A4). Lane T45C proved that hypothesis (`CofinalProjective.projectiveCofinality`, Temkin,
Proposition 4.3.1 with the projectivity of the output, through SERRE-I). This file removes the
hypothesis.

## Main results

* `exists_nodal_modification_of_isAlgClosed`: the statement of `Gluing.exists_nodal_modification`
  without `ProjectiveCofinality R`.
-/

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

namespace DeJongAlterations.StableModification.Gluing

open ValCurves Curves
open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg)
open DeJong (IsNodalCurve)

variable {K : Type u} [Field K] {R : ValuationSubring K}

/-- **A semi-stable modification of a curve over a valuation ring, unconditionally**
(`PLAN-T5.md` §2.2 steps 1–8, nodes A1–A8; Temkin, proof of Proposition 4.5.1, T:3243–3266):
`Gluing.exists_nodal_modification` with its node-A4 hypothesis `ProjectiveCofinality R`
discharged by `CofinalProjective.projectiveCofinality`. Let `K` be algebraically closed,
`R ⊆ K` a valuation ring of finite height and equal characteristic, and `φ : C → Spec R` a proper
flat relative curve, integral, with `trdeg K(C)/K = 1`. Then there are a projective refinement
`p : C' → C` with finite normalization `N → C'` (flat and of finite presentation over `R`,
projective over `R` if `C` is), and a modification `β : X → N` with `X → C` a modification and
`X` a nodal curve over `R`, locally projective over `N`, and an η-modification of `C` if `C` is
normal along its generic fibre. -/
theorem exists_nodal_modification_of_isAlgClosed [IsAlgClosed K] [Finite (PrimeSpectrum R)]
    (hchar : ∃ p : ℕ, ExpChar K p ∧ ExpChar (ResidueField R) p)
    {C : Scheme.{u}} [IsIntegral C] [C.IsSeparated] [CompactSpace C] (φ : C ⟶ Spec (.of R))
    [IsProper φ] [Flat φ] (htr : fiberTrdeg φ (genericPoint C) = 1) :
    ∃ (C' : Scheme.{u}) (p : C' ⟶ C) (_ : IsIntegral C'), IsModification p ∧
      DeJong.IsRelativelyProjective φ p ∧ IsFinite (genericPt C').fromNormalization ∧
      Flat ((genericPt C').fromNormalization ≫ p ≫ φ) ∧
      LocallyOfFinitePresentation ((genericPt C').fromNormalization ≫ p ≫ φ) ∧
      (IsProjectiveOver φ → IsProjectiveOver ((genericPt C').fromNormalization ≫ p ≫ φ)) ∧
      ∃ (X : Scheme.{u}) (β : X ⟶ (genericPt C').normalization), IsModification β ∧
        IsModification (β ≫ (genericPt C').fromNormalization ≫ p) ∧
        IsNodalCurve (β ≫ (genericPt C').fromNormalization ≫ p ≫ φ) ∧
        Projectivity.LocallyRelativelyProjective ((genericPt C').fromNormalization ≫ p ≫ φ) β ∧
        ((∀ x : C, φ x = genericPoint (Spec (.of R)) → IsIntegrallyClosed (C.presheaf.stalk x)) →
          Curves.IsEtaModification (β ≫ (genericPt C').fromNormalization ≫ p) φ) :=
  exists_nodal_modification hchar (CofinalProjective.projectiveCofinality R) φ htr

end DeJongAlterations.StableModification.Gluing
