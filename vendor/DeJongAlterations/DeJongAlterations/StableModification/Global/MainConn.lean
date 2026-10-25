/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Global.DeJongTheorem
import DeJongAlterations.StableModification.Global.SpreadPieceConn
import DeJongAlterations.StableModification.Global.StableOpenReduce

/-!
# The global assembly from the corrected spreading statement

The consumer chain of `Global.deJongAlterationTheorem` (`Global/Main.lean`,
`Global/DeJongTheorem.lean`; node G8 of `PLAN-T5.md`; Temkin, *Stable modification of relative
curves*, J. Algebraic Geom. 19 (2010), proof of Theorem 1.5, T:3379–3399, with Theorem 1.1) with
the corrected statement `StableOpenNbhdConn k` (ERRATA DJA-O36) in place of `StableOpenNbhd k`:

* `hasLocallyProjectiveStableModification_conn` (from `exists_localStablePiece_conn`);
* `temkinStableModification_conn` (`DeJong.TemkinStableModification k`);
* `deJongAlterationTheorem_conn` (de Jong's alteration theorem over an algebraically closed `k`
  from `ValuationStableExistence`, `ValuationStableUniqueness`, `StableOpenNbhdConn k` and
  `StableModificationProjectivity k`);
* `temkinStableModification_of_rational`, `deJongAlterationTheorem_of_rational`: the same with
  `StableOpenNbhdConn k` replaced by the ω step `StableOpenNbhdRational K` for all algebraically
  closed `K` (`stableOpenNbhdConn_of_rational`, `Global/StableOpenReduce.lean`).

Since `StableOpenNbhd k` implies `StableOpenNbhdConn k` (`StableOpenNbhd.conn`), these results
generalize the integrated ones. The integrated files are not edited.

Blueprint: `sm-global-stable-open.tex`, `thm:sm-gso-locally-projective`, `thm:sm-gso-tsm`,
`cor:sm-gso-dejong`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.StableModification.Global

universe u

open DeJong (IsSemistablePair IsMultipointedCurve)
open RiemannZariskiSpace

/-- **A locally projective stable modification exists, from the corrected spreading statement**
(`PLAN-T5.md` §1.2, node G8; obligations E1–E4 of PLAN-OM3 §6; ERRATA DJA-O36). The statement of
`hasLocallyProjectiveStableModification` with `StableOpenNbhdConn k` in place of
`StableOpenNbhd k`. -/
theorem hasLocallyProjectiveStableModification_conn {k : Type u} [Field k]
    (hE : ValuationStableExistence.{u}) (hU : ValuationStableUniqueness.{u})
    (hO : StableOpenNbhdConn k) :
    ∀ (S : Scheme.{u}) (pS : S ⟶ Spec (.of k)) (_ : IsVariety pS), IsNormalScheme S →
      IsProjectiveOver pS →
      ∀ (C : Scheme.{u}) (g : C ⟶ S) (D : C.IdealSheafData),
        IsProjectiveOver (g ≫ pS) → IsMultipointedCurve g D →
        Smooth (g.fiberToSpecResidueField (genericPoint S)) →
        IsSemistablePair (g.fiberToSpecResidueField (genericPoint S))
          (DeJong.fiberMarks g D (genericPoint S)) →
        GeometricallyIntegral (g.fiberToSpecResidueField (genericPoint S)) →
        HasLocallyProjectiveStableModification k pS g D := by
  intro S pS hv _ hSp C g D hC hD hsm hss hgi
  have : IsProper pS := hSp.isProper
  have : S.IsSeparated := ⟨by rw [← terminal.comp_from pS]; infer_instance⟩
  have : IsProper (g ≫ pS) := hC.isProper
  have : IsProper g := IsProper.of_comp g pS
  let L := AlgebraicClosure S.functionField
  have hUo : StableModelUniqueOver pS g D L :=
    stableModelUniqueOver_of hU hC hD hsm hss hgi
      (fun W hW ↦ finite_primeSpectrum_of_mem (pS := pS) W hW)
      (fun W hW ↦ exists_expChar_of_mem (pS := pS) W hW)
  exact hasLocallyProjectiveStableModification_of_pieces pS hSp g D hC hD L
    (fun W hW ↦ exists_localStablePiece_conn pS hSp g D hC hD hsm hss hgi hE hO W hW)
    (fun P₁ P₂ W h₁ h₂ ↦ exists_comparisonPiece hUo P₁ P₂ W h₁ h₂)

/-- **Temkin's stable modification theorem from the corrected spreading statement**
(`DeJong.TemkinStableModification k`, Temkin Thm 1.5 with Thm 1.1; `PLAN-T5.md` §1.1, node G8;
ERRATA DJA-O36): the statement of `temkinStableModification` with `StableOpenNbhdConn k` in place
of `StableOpenNbhd k`. -/
theorem temkinStableModification_conn {k : Type u} [Field k] [IsAlgClosed k]
    (hE : ValuationStableExistence.{u}) (hU : ValuationStableUniqueness.{u})
    (hO : StableOpenNbhdConn k) (hP : StableModificationProjectivity k) :
    DeJong.TemkinStableModification k :=
  temkinStableModification_of_hasLocallyProjective hP
    (hasLocallyProjectiveStableModification_conn hE hU hO)

/-- **De Jong's alteration theorem from the corrected inputs** (blueprint `cor:sm-gso-dejong`):
from existence and uniqueness of stable modifications over valuation rings, the corrected
spreading of numerical stability `StableOpenNbhdConn k` (ERRATA DJA-O36) and the projectivity of
locally projective stable modifications. -/
theorem deJongAlterationTheorem_conn {k : Type u} [Field k] [IsAlgClosed k]
    (hE : ValuationStableExistence.{u}) (hU : ValuationStableUniqueness.{u})
    (hO : StableOpenNbhdConn k) (hP : StableModificationProjectivity k) :
    DeJongAlterationTheorem k :=
  DeJong.deJongAlterationTheorem_of_stableModification (temkinStableModification_conn hE hU hO hP)

/-- **Temkin's stable modification theorem from the ω step** (`DeJong.TemkinStableModification k`;
ERRATA DJA-O36): `temkinStableModification_conn` with `StableOpenNbhdConn k` obtained from
`StableOpenNbhdRational K` for all algebraically closed `K` (`stableOpenNbhdConn_of_rational`). -/
theorem temkinStableModification_of_rational {k : Type u} [Field k] [IsAlgClosed k]
    (hE : ValuationStableExistence.{u}) (hU : ValuationStableUniqueness.{u})
    (hR : ∀ (K : Type u) [Field K] [IsAlgClosed K], StableOpenNbhdRational K)
    (hP : StableModificationProjectivity k) :
    DeJong.TemkinStableModification k :=
  temkinStableModification_conn hE hU (stableOpenNbhdConn_of_rational k hR) hP

/-- **De Jong's alteration theorem from the ω step** (blueprint `cor:sm-gso-dejong`): from
existence and uniqueness of stable modifications over valuation rings, the ω step
`StableOpenNbhdRational K` at rational points of normal varieties over every algebraically closed
`K`, and the projectivity of locally projective stable modifications. -/
theorem deJongAlterationTheorem_of_rational {k : Type u} [Field k] [IsAlgClosed k]
    (hE : ValuationStableExistence.{u}) (hU : ValuationStableUniqueness.{u})
    (hR : ∀ (K : Type u) [Field K] [IsAlgClosed K], StableOpenNbhdRational K)
    (hP : StableModificationProjectivity k) :
    DeJongAlterationTheorem k :=
  deJongAlterationTheorem_conn hE hU (stableOpenNbhdConn_of_rational k hR) hP

end DeJongAlterations.StableModification.Global
