import Hironaka.Resolution.HironakaG8SuccExponents
import Hironaka.Resolution.HironakaG8BFamilyTangent

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The single input of lane G8B's plan module 6 (G8 lane, run 0080, round 7)

Blueprint: `hironaka-g8-resume-tangent-exp-succ.tex`.  Lane G8B's `HironakaG8BFamilyTangent` (I-1390) proves lane G11B's
`TangentIndepBM 𝔍 R` for every class-functorial `R` from one input, `TangentExpAgreeSuccBM n k`: the boundary exponents below the
mark of the two restricted lower ideals of level `s + 1` (two tangent directions, the original members through an anchor of level
`s + 1`) agree on every open of the stage over `U ∩ U'` on which both are in the native domain.  It follows from
`HironakaG8SuccExponents.expAgree_stage_lowerIdealWBM_succ_throughMembers` (full agreement, `0 < n`); in dimension `0` the
cosupports are empty.

* `expAgree_of_dimZero`, **`tangentExpAgreeSuccBM`**.

Sorry-free.  Universe `0`.  Import discipline: no import of `Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8TangentExpSucc

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal
open Hironaka.ResolutionInvariantSpec (IsInvDomain cosupp_eq_empty_of_dimLE_zero)
open Hironaka.HironakaG11InvBMClass (ExpAgree)

noncomputable section

/-- **In dimension `0` exponent agreement is vacuous** (the cosupport of a marked ideal of the domain is empty). -/
theorem expAgree_of_dimZero {Y : CMfd.{0} 0} {P Q : MarkedIdeal 0 Y} {k : ℕ} (hP : IsInvDomain k P) : ExpAgree P Q := by
  have h0 : IsInvDomain 0 P := ⟨hP.isWellFormed, fun x hx => by
      obtain ⟨j, -, hj⟩ := hP.dimLE x hx
      exact ⟨j, BlowupStrictSubmanifold.le_of_regularAtDim_subset hj
        (AnalyticIrreducibleComponents.regularAtDim_univ x) (subset_univ _), hj⟩,
    hP.one_le_d, hP.isNonzeroAlongAt⟩
  intro H _ y hy
  rw [cosupp_eq_empty_of_dimLE_zero h0] at hy
  exact absurd hy (notMem_empty y)

/-- **The input of lane G8B's module 6** (`HironakaG8BFamilyTangent.TangentExpAgreeSuccBM`), in every dimension. -/
theorem tangentExpAgreeSuccBM (n k : ℕ) : HironakaG8BFamilyTangent.TangentExpAgreeSuccBM (n := n) k := by
  intro X 𝔍 h𝔍 _ Y₀ T₀ hT₀ s a _ hl U U' w w' hw hw' O hOU hOU' hdom hdom'
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact HironakaG8ClassStepExp.ExpAgree.belowMark (expAgree_of_dimZero hdom)
  · exact HironakaG8ClassStepExp.ExpAgree.belowMark
      (HironakaG8SuccExponents.expAgree_stage_lowerIdealWBM_succ_throughMembers h𝔍.isWellFormed h𝔍.one_le_d hn hw hw'
        T₀ hT₀ a hl O hOU hOU' hdom hdom')

end

end Hironaka.HironakaG8TangentExpSucc
