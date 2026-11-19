import Hironaka.Resolution.HironakaG8ClassStepResidual
import Hironaka.Resolution.HironakaG11PresPadClose

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The last input of G11 reduced to the residual boundary exponents (G8C lane, run 0080, round 3; (B') plan module 10)

Blueprint: `hironaka-g8-class-step-bridge.tex`.  Lane G11C's padded closing (`HironakaG11PresPadClose`) derives `g11:general` from
the single `R`-free input `LowerExpStepBM N (k + 1)` (for all `k < N`): the exponents of the lower ideals of class-equivalent
marked ideals agree below the mark.  This module reduces it to the narrower residual of `HironakaG8ClassStepResidual`:

* `LowerExpResidualStepBM n k`: `LowerExpResidual A B` for every pair of class-equivalent marked ideals of the domain of maximal
  order (exponents below the mark only at level-`0` points whose base point lies on an original member, and at level-`(s + 1)`
  points where the `ℰ`-term is divisible by `𝓘_H` along a carrier);
* **`lowerExpStepBM_of_residualStep`**: `LowerExpResidualStepBM n k → HironakaG11PresPadClose.LowerExpStepBM n k`.

Sorry-free.  Universe `0`.  Import discipline: no import of `Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.
-/

namespace Hironaka.HironakaG8ClassStepBridge

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka.HomogenizedIdealAlong (IsMaximalOrderAlong)
open Hironaka.HironakaG8LocalHistory (LocWPEquiv)
open Hironaka.HironakaG11InvBMClass (SameCarrierDim ExpAgree)
open Hironaka.HironakaG8ClassStepResidual (LowerExpResidual lowerPairs_expAgree_of_residual)

/-- **The residual boundary-exponent statement at level `k`** (`R`-free): for every pair of class-equivalent marked ideals of the
domain of maximal order in dimension `≤ k`, the residual `LowerExpResidual A B` of `HironakaG8ClassStepResidual`. -/
def LowerExpResidualStepBM (n k : ℕ) : Prop :=
  ∀ {X : CMfd.{0} n} (A B : MarkedIdeal n X), IsInvDomain k A → IsInvDomain k B →
    IsMaximalOrderAlong A.N A.ideal A.d → IsMaximalOrderAlong B.N B.ideal B.d → LocWPEquiv A B →
    A.d = B.d → A.E = B.E → SameCarrierDim A B → ExpAgree A B → LowerExpResidual A B

/-- **Lane G11C's last input from the residual**: `LowerExpResidualStepBM n k` implies `LowerExpStepBM n k`. -/
theorem lowerExpStepBM_of_residualStep {n k : ℕ} (hn : 0 < n) (h : LowerExpResidualStepBM n k) :
    HironakaG11PresPadClose.LowerExpStepBM n k := by
  intro X A B hA hB hmA hmB hAB hd hE hdim h0 Y₀ T₀ hT₀ s y₀ hy₀ hreg O hOA hOB r r' hdA hdB
  exact HironakaG8ClassStepExp.ExpAgree.belowMark
    (lowerPairs_expAgree_of_residual hn hA hB hmA hmB hAB hd hE hdim (h A B hA hB hmA hmB hAB hd hE hdim h0)
      T₀ hT₀ s y₀ hy₀ hreg O hOA hOB r r' hdA hdB)

end Hironaka.HironakaG8ClassStepBridge
