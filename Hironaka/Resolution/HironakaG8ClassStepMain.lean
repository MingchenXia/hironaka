import Hironaka.Resolution.HironakaG8ClassStepCut

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Module 10 with the `LocWPEquiv` part of the class data discharged (G8C lane, run 0080, round 2; (B') plan module 10)

Blueprint: `hironaka-g8-class-step-skeleton.tex` (node `hir:g8c-class-step-main`).  Lane G11B's module-10 statement (inbox
I-1361) given only the two remaining parts of the class data of the lower ideals: carriers of the same dimension on the
cosupport (`SameCarrierDim`) and agreeing boundary exponents (`ExpAgree`) of the two restricted lower ideals.  The local
`s(i,ii)`-equivalence of the lower ideals is proved (`HironakaG8ClassStepCut.lowerPairs_locWPEquiv`).

Sorry-free.  Import discipline: no import of `Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.
-/

universe v

namespace Hironaka.HironakaG8ClassStepMain

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant)
open Hironaka.HomogenizedIdealAlong (IsMaximalOrderAlong)
open Hironaka.HironakaG8LocalHistory (LocWPEquiv)
open Hironaka.HironakaG11InvBMClass (SameCarrierDim ExpAgree ClassFunctorialFor)
open Hironaka.HironakaG8P1GenInv (ClassFunctorialMaxOrderFor)
open Hironaka.HironakaG8ClassStep (LowerPairs)

variable {n k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **(B') plan module 10, given the carrier dimensions and the boundary exponents of the lower ideals**: lane G11B's statement
(I-1361) with the two remaining parts of the class data of the lower ideals as hypotheses (`hDim`, `hExp`; both `R`-free); the
local `s(i,ii)`-equivalence of the lower ideals is proved (`HironakaG8ClassStepCut.lowerPairs_locWPEquiv`). -/
theorem classFunctorialMaxOrder_stepOneInvBM_of_dimExp (hn : 0 < n)
    (R : ResolutionInvariant.{0, v} n (k - 1) Λ)
    (hR : ClassFunctorialFor (fun {Y} A B => LocWPEquiv (X := Y) A B) (k - 1) R.inv)
    (hTI : ∀ {X : CMfd.{0} n} (𝔍 : MarkedIdeal n X), IsInvDomain k 𝔍 → IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d →
      HironakaG11InvBMTangentIndep.TangentIndepBM 𝔍 R)
    (hDim : ∀ {X : CMfd.{0} n} (A B : MarkedIdeal n X), IsInvDomain k A → IsInvDomain k B →
      IsMaximalOrderAlong A.N A.ideal A.d → IsMaximalOrderAlong B.N B.ideal B.d → LocWPEquiv A B →
      A.d = B.d → A.E = B.E → SameCarrierDim A B → ExpAgree A B → LowerPairs A B fun {_} P Q => SameCarrierDim P Q)
    (hExp : ∀ {X : CMfd.{0} n} (A B : MarkedIdeal n X), IsInvDomain k A → IsInvDomain k B →
      IsMaximalOrderAlong A.N A.ideal A.d → IsMaximalOrderAlong B.N B.ideal B.d → LocWPEquiv A B →
      A.d = B.d → A.E = B.E → SameCarrierDim A B → ExpAgree A B → LowerPairs A B fun {_} P Q => ExpAgree P Q) :
    ClassFunctorialMaxOrderFor (fun {Y} A B => LocWPEquiv (X := Y) A B) k
      (fun {X} 𝔍 {Y} T y => HironakaG11InvBMLower.stepOneInvBM (X := X) R 𝔍 (Y := Y) T y) :=
  HironakaG8ClassStep.classFunctorialMaxOrder_stepOneInvBM_of_lowerClass hn R hR hTI
    fun A B hA hB hmA hmB h hd hE hdim h0 => HironakaG8ClassStep.lowerClassBM_of_parts
      (HironakaG8ClassStepCut.lowerPairs_locWPEquiv hn hA hB hmA hmB h hE)
      (hDim A B hA hB hmA hmB h hd hE hdim h0) (hExp A B hA hB hmA hmB h hd hE hdim h0)

end Hironaka.HironakaG8ClassStepMain
