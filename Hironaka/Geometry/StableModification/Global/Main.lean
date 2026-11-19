import Hironaka.Geometry.StableModification.Global.SpreadPiece
import Hironaka.Geometry.StableModification.Global.MainPieces

/-!
# The global assembly of Temkin's stable modification theorem

The proof of Theorem 1.5 (Temkin, *Stable modification of relative curves*, `semi-stable.tex`,
T:3379–3399, with Theorem 1.1 for the projectivity),
conditional on the published producer statements of the lanes that are still running:

* `ValuationStableExistence` and `ValuationStableUniqueness` (lane T45B: Temkin Prop. 4.5.1
  over a valuation ring of finite height with algebraically closed fraction field);
* `StableOpenNbhd k` (Temkin Lemma 5.1 (ii) in open form, via `ω`, lanes
  OM3B–OM3D);
* `StableModificationProjectivity k` (lane OM3D: Temkin Thm 1.1 for the glued modification).

With `L = K(S)ᵃ` (no generic étaleness is needed downstream): every valuation ring of `RZ_L(S)`
lies in a local stable piece (`exists_localStablePiece`), any two pieces are compared by
comparison pieces (`exists_comparisonPiece`, from the uniqueness via `stableModelUniqueOver_of`),
and the pieces glue after one refinement, a Chow modification and a normalization
(`hasLocallyProjectiveStableModification_of_pieces`). This proves
`hasLocallyProjectiveStableModification` and
`temkinStableModification` (`DeJong.TemkinStableModification k`), each from the hypotheses
named above. The normality of `S` is not used.

Blueprint: `sm-global.tex`, `thm:sm-global-locally-projective`, `thm:sm-global-tsm`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.StableModification.Global

universe u

open DeJong (IsSemistablePair IsMultipointedCurve)
open RiemannZariskiSpace

/-- **A locally projective stable modification exists**,
from the existence and uniqueness of stable modifications over valuation
rings (lane T45B) and the spreading of numerical stability. For every family of
`DeJong.TemkinStableModification k` there are a normal alteration `S' ⟶ S` projective over `k`
and a stable, numerically stable η-modification of `C ×_S S'`, locally projective over `k`, with
finite marks and an isomorphism over a nonempty open of `S'`. -/
theorem hasLocallyProjectiveStableModification {k : Type u} [Field k]
    (hE : ValuationStableExistence.{u}) (hU : ValuationStableUniqueness.{u})
    (hO : StableOpenNbhd k) :
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
    (fun W hW ↦ exists_localStablePiece pS hSp g D hC hD hsm hss hgi hE hO W hW)
    (fun P₁ P₂ W h₁ h₂ ↦ exists_comparisonPiece hUo P₁ P₂ W h₁ h₂)

/-- **Temkin's stable modification theorem** (`DeJong.TemkinStableModification k`, Temkin
Thm 1.5 with Thm 1.1), from the existence and uniqueness of stable
modifications over valuation rings (lane T45B), the spreading of numerical stability
and the projectivity of locally projective stable modifications (lane OM3D). -/
theorem temkinStableModification {k : Type u} [Field k] [IsAlgClosed k]
    (hE : ValuationStableExistence.{u}) (hU : ValuationStableUniqueness.{u})
    (hO : StableOpenNbhd k) (hP : StableModificationProjectivity k) :
    DeJong.TemkinStableModification k :=
  temkinStableModification_of_hasLocallyProjective hP
    (hasLocallyProjectiveStableModification hE hU hO)

end Hironaka.StableModification.Global
