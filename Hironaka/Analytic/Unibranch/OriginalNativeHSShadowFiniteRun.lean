import Hironaka.Analytic.Unibranch.OriginalNativeHSShadowSuccessor
import Hironaka.Analytic.Unibranch.OriginalNativeHSFirstStageInput

/-! A genuine FINITE run of the actually constructed compact-shadow successors.
Termination uses the ORIGINAL invariant order/actual next_level_lt.
Blueprint FIRST: original-native-hs-shadow-finite-run.tex.
No endpoint supplier, compactcosupp, Lex-WF or step budget. -/
set_option autoImplicit false
open Set TopologicalSpace
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSShadowFiniteRun
noncomputable section
open OriginalNativeHSUniformRestrictedStage

variable {n : ℕ} {Λ : Type} [LinearOrder Λ] [Nonempty Λ]

/-- The ACTUAL next native threshold shadow, after the actual constructed step. -/
def afterShadow (P : Input n Λ) : Set (OriginalNativeHSShadowSuccessor.nativeStage P).Y.obj.left :=
  OriginalIntrinsicHSSuperlevels.originalSingularHSThreshold
      (OriginalNativeHSShadowSuccessor.nativeStage P).Y P.profile ∩
    (OriginalNativeHSShadowSuccessor.nativeStage P).q.hom.left.base ⁻¹' compact P

/-- Every transition is the genuine computed successor, not a supplied endpoint. -/
inductive Run : Input n Λ → Type 1
  | stop (P : Input n Λ) (hempty : afterShadow P = ∅) : Run P
  | next (P : Input n Λ) (hne : (afterShadow P).Nonempty)
      (tail : Run (OriginalNativeHSShadowSuccessor.nextInput P hne)) : Run P

theorem exists_run [WellFoundedLT Λ] (P : Input n Λ) : Nonempty (Run P) := by
  classical
  have hw : WellFounded (fun Q P : Input n Λ => level Q < level P) :=
    InvImage.wf (fun Q : Input n Λ => level Q) wellFounded_lt
  apply hw.induction P
  intro Q ih
  rcases (afterShadow Q).eq_empty_or_nonempty with hempty | hne
  · exact ⟨Run.stop Q hempty⟩
  · obtain ⟨r⟩ := ih (OriginalNativeHSShadowSuccessor.nextInput Q hne)
      (OriginalNativeHSShadowSuccessor.next_level_lt Q hne)
    exact ⟨Run.next Q hne r⟩

/-- Choose the ACTUAL finite run whose existence was proved by original-value descent. -/
def run [WellFoundedLT Λ] (P : Input n Λ) : Run P := (exists_run P).some

/-- Concrete ORIGINAL-family seed, preserving the SAME frozen first native step. -/
theorem exists_original_run {X : SourceReducedComplexSpace} {K : Set X.obj.left}
    (M : OriginalNativeHSCompactShadowWindows.Maximum X K) (hK : IsCompact K)
    (s : OriginalNativeShadowFirstBlowup.Step M hK)
    (hne : (OriginalIntrinsicHSSuperlevels.originalSingularHSThreshold s.source
      (OriginalLocalEmbeddingStalkHS.originalStalkHS X M.point) ∩
        s.projection.hom.left.base ⁻¹' OriginalNativeHSFirstStageInput.compact M hK).Nonempty) :
    letI : Nonempty (Hironaka.CanonicalCentres.ValTy
      (OriginalLocalEmbeddingStalkHS.originalStalkHS X M.point 1 - 1)) :=
        ⟨OriginalNativeShadowInvariantCentre.level M hK⟩
    Nonempty (Run (OriginalNativeHSFirstStageInput.phaseInput M hK s hne)) := by
  let : Nonempty (Hironaka.CanonicalCentres.ValTy
    (OriginalLocalEmbeddingStalkHS.originalStalkHS X M.point 1 - 1)) :=
      ⟨OriginalNativeShadowInvariantCentre.level M hK⟩
  exact exists_run (OriginalNativeHSFirstStageInput.phaseInput M hK s hne)

namespace Run

def terminalInput : {P : Input n Λ} → Run P → Input n Λ
  | _, .stop P _ => P
  | _, .next _ _ r => terminalInput r

theorem terminal_empty : {P : Input n Λ} → (r : Run P) → afterShadow (terminalInput r) = ∅
  | _, .stop _ h => h
  | _, .next _ _ r => terminal_empty r

theorem profile_eq : {P : Input n Λ} → (r : Run P) → (terminalInput r).profile = P.profile
  | _, .stop _ _ => rfl
  | _, .next _ _ r => profile_eq r

theorem invariant_eq : {P : Input n Λ} → (r : Run P) → (terminalInput r).invariant = P.invariant
  | _, .stop _ _ => rfl
  | _, .next _ _ r => invariant_eq r

end Run
end
end Hironaka.Analytic.Unibranch.OriginalNativeHSShadowFiniteRun
