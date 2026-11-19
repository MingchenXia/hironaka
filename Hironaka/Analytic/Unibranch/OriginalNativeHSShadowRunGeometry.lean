import Hironaka.Analytic.Unibranch.OriginalNativeHSShadowFiniteRun
import Hironaka.Analytic.Unibranch.OriginalNativeHSShadowFinitePhase
import Hironaka.Analytic.Unibranch.OriginalNativeShadowFirstHSNonincrease
import Hironaka.Analytic.Unibranch.OriginalNativeHSThresholdIsomorphism

/-! Actual HS/nonincrease and FULL off-initial-threshold geometry of the literal
terminal computed prefix of a genuine finite Run. The original first-step
consumer derives its incoming geometry internally, not from an Input packet.
Blueprint FIRST: original-native-hs-shadow-run-geometry.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSShadowRunGeometry
noncomputable section
open Hironaka SourceReducedComplexSpace OriginalLocalEmbeddingStalkHS
  OriginalIntrinsicHSSuperlevels HironakaG11HSPhaseInduction
  HironakaG11CompatibleAnalyticCover HironakaIntrinsicComplexAnalyticRegularLocus
  OriginalRelativelyCompactRestriction OriginalNativeHSUniformRestrictedStage
  OriginalNativeHSShadowFiniteRun

private theorem hs_of_open_square {X Y A B : SourceReducedComplexSpace}
    (q : Y ⟶ X) (p : A ⟶ B) (l : A ⟶ Y) (j : B ⟶ X)
    (hl : LocallyRingedSpace.IsOpenImmersion l.hom.left)
    (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left) (hsq : p ≫ j = l ≫ q)
    (hOld : ∀ y, originalStalkHS Y y ≤ originalStalkHS X (q.hom.left.base y))
    (y : A.obj.left) : originalStalkHS A y ≤ originalStalkHS B (p.hom.left.base y) := by
  have hs := originalStalkHS_openImmersion l hl y
  have hb := originalStalkHS_openImmersion j hj (p.hom.left.base y)
  have hp := congrArg (fun a => a.hom.left.base y) hsq
  intro k
  exact (congrFun hs k).symm.trans_le ((hOld _ k).trans_eq
    ((congrArg (fun x => originalStalkHS X x k) hp.symm).trans (congrFun hb k)))

variable {n : ℕ} {Λ : Type} [LinearOrder Λ] [Nonempty Λ]

private abbrev oldSourceInclusion (P : Input n Λ) :=
  OriginalNativeHSBaseOpenNativeStage.sourceInclusion P.history
    (neighbourhood P).openSet (neighbourhood P).compactClosure

private theorem oldSourceInclusion_open (P : Input n Λ) :
    LocallyRingedSpace.IsOpenImmersion (oldSourceInclusion P).hom.left :=
  inclusion_isOpenImmersion _ _ _

private theorem restricted_square (P : Input n Λ) :
    (nativeStage P).q ≫ (neighbourhood P).inclusion = oldSourceInclusion P ≫ P.nativeStage.q :=
  (OriginalNativeHSBaseOpenNativeStage.projection_square P.history
    (neighbourhood P).openSet (neighbourhood P).compactClosure).trans
      (congrArg (fun a => oldSourceInclusion P ≫ a) P.history_projection)

private theorem restricted_range (P : Input n Λ) :
    range (oldSourceInclusion P).hom.left.base =
      P.nativeStage.q.hom.left.base ⁻¹' range (neighbourhood P).inclusion.hom.left.base := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    rw [(neighbourhood P).inclusion_range]
    change P.nativeStage.q.hom.left.base z.val ∈ (neighbourhood P).openSet
    have hz : P.history.projection.hom.left.base z.val ∈ (neighbourhood P).openSet := z.property
    exact (congrArg (fun q => q.hom.left.base z.val) P.history_projection) ▸ hz
  · intro hy
    rw [(neighbourhood P).inclusion_range] at hy
    have hz : P.history.projection.hom.left.base y ∈ (neighbourhood P).openSet := by
      rw [P.history_projection]
      exact hy
    exact ⟨⟨y, hz⟩, rfl⟩

private theorem restricted_hs_nonincrease (P : Input n Λ)
    (hOld : ∀ y, originalStalkHS P.nativeStage.Y y ≤
      originalStalkHS P.base (P.nativeStage.q.hom.left.base y))
    (y : (nativeStage P).Y.obj.left) :
    originalStalkHS (nativeStage P).Y y ≤ originalStalkHS (neighbourhood P).source
      ((nativeStage P).q.hom.left.base y) :=
  hs_of_open_square P.nativeStage.q (nativeStage P).q (oldSourceInclusion P) (neighbourhood P).inclusion
    (oldSourceInclusion_open P) (neighbourhood P).inclusion_isOpenImmersion (restricted_square P) hOld y

private theorem restricted_off_threshold (P : Input n Λ)
    (hOld : IsIsoOver P.nativeStage.q (originalSingularHSThreshold P.base P.profile)ᶜ) :
    IsIsoOver (nativeStage P).q (originalSingularHSThreshold (neighbourhood P).source P.profile)ᶜ :=
  OriginalNativeHSThresholdIsomorphism.isIsoOver_open_square_threshold_compl P.profile
    P.nativeStage.q (nativeStage P).q (oldSourceInclusion P) (neighbourhood P).inclusion
    (oldSourceInclusion_open P) (neighbourhood P).inclusion_isOpenImmersion
    (restricted_square P) (restricted_range P) hOld

/-- SAME computed whole successor projection, with incoming PRESENT-map geometry only. -/
theorem successor_hs_nonincrease (P : Input n Λ)
    (hOld : ∀ y, originalStalkHS P.nativeStage.Y y ≤
      originalStalkHS P.base (P.nativeStage.q.hom.left.base y))
    (y : (OriginalNativeHSShadowSuccessor.nativeStage P).Y.obj.left) :
    originalStalkHS (OriginalNativeHSShadowSuccessor.nativeStage P).Y y ≤
      originalStalkHS (neighbourhood P).source
        ((OriginalNativeHSShadowSuccessor.nativeStage P).q.hom.left.base y) :=
  (OriginalNativeHSShadowSuccessor.hs_nonincrease P y).trans
    (restricted_hs_nonincrease P hOld ((OriginalNativeHSShadowSuccessor.step P).projection.hom.left.base y))

/-- The FULL inverse is over the original fixed profile on the ACTUAL new base. -/
theorem successor_off_threshold (P : Input n Λ)
    (hOld : IsIsoOver P.nativeStage.q (originalSingularHSThreshold P.base P.profile)ᶜ) :
    IsIsoOver (OriginalNativeHSShadowSuccessor.nativeStage P).q
      (originalSingularHSThreshold (neighbourhood P).source P.profile)ᶜ :=
  OriginalNativeHSThresholdIsomorphism.isIsoOver_comp_threshold_compl P.profile
    (nativeStage P).q (OriginalNativeHSShadowSuccessor.step P).projection
    (restricted_off_threshold P hOld) (OriginalNativeHSShadowSuccessor.off_threshold P)

private theorem terminalInput_hs : {P : Input n Λ} → (r : Run P) →
    (∀ y, originalStalkHS P.nativeStage.Y y ≤ originalStalkHS P.base (P.nativeStage.q.hom.left.base y)) →
    ∀ y, originalStalkHS r.terminalInput.nativeStage.Y y ≤
      originalStalkHS r.terminalInput.base (r.terminalInput.nativeStage.q.hom.left.base y)
  | _, .stop _ _, hOld => hOld
  | P, .next _ _hne tail, hOld =>
      terminalInput_hs tail (successor_hs_nonincrease P hOld)

private theorem terminalInput_off : {P : Input n Λ} → (r : Run P) →
    IsIsoOver P.nativeStage.q (originalSingularHSThreshold P.base P.profile)ᶜ →
    IsIsoOver r.terminalInput.nativeStage.q
      (originalSingularHSThreshold r.terminalInput.base r.terminalInput.profile)ᶜ
  | _, .stop _ _, hOld => hOld
  | P, .next _ _hne tail, hOld => terminalInput_off tail (successor_off_threshold P hOld)

/-- WHOLE literal terminal computed prefix; the existing actual Run supplies the induction. -/
theorem terminal_hs_nonincrease (P : Input n Λ) (r : Run P)
    (hOld : ∀ y, originalStalkHS P.nativeStage.Y y ≤
      originalStalkHS P.base (P.nativeStage.q.hom.left.base y))
    (y : (OriginalNativeHSShadowSuccessor.nativeStage r.terminalInput).Y.obj.left) :
    originalStalkHS (OriginalNativeHSShadowSuccessor.nativeStage r.terminalInput).Y y ≤
      originalStalkHS (neighbourhood r.terminalInput).source
        ((OriginalNativeHSShadowSuccessor.nativeStage r.terminalInput).q.hom.left.base y) :=
  successor_hs_nonincrease r.terminalInput (terminalInput_hs r hOld) y

/-- The original incoming profile is retained through EVERY actual Run base restriction. -/
theorem terminal_off_threshold (P : Input n Λ) (r : Run P)
    (hOld : IsIsoOver P.nativeStage.q (originalSingularHSThreshold P.base P.profile)ᶜ) :
    IsIsoOver (OriginalNativeHSShadowSuccessor.nativeStage r.terminalInput).q
      (originalSingularHSThreshold (neighbourhood r.terminalInput).source P.profile)ᶜ := by
  simpa only [r.profile_eq] using
    successor_off_threshold r.terminalInput (terminalInput_off r hOld)

omit [Nonempty Λ] in
/-- Same internally computed EMPTY-stop source/base square, retaining arbitrary incoming HS geometry. -/
theorem empty_stop_hs_nonincrease (S : OriginalNativeHSEmptyStop.Input n Λ)
    (hOld : ∀ y, originalStalkHS S.nativeStage.Y y ≤
      originalStalkHS S.base (S.nativeStage.q.hom.left.base y))
    (y : (OriginalNativeHSEmptyStop.nativeStage S).Y.obj.left) :
    originalStalkHS (OriginalNativeHSEmptyStop.nativeStage S).Y y ≤
      originalStalkHS (OriginalNativeHSEmptyStop.neighbourhood S).source
        ((OriginalNativeHSEmptyStop.nativeStage S).q.hom.left.base y) :=
  hs_of_open_square S.nativeStage.q (OriginalNativeHSEmptyStop.nativeStage S).q
    (OriginalNativeHSEmptyStop.sourceInclusion S) (OriginalNativeHSEmptyStop.neighbourhood S).inclusion
    (OriginalNativeHSEmptyStop.sourceInclusion_isOpenImmersion S)
    (OriginalNativeHSEmptyStop.neighbourhood S).inclusion_isOpenImmersion
    (OriginalNativeHSEmptyStop.projection_square S) hOld y

omit [Nonempty Λ] in
private theorem empty_stop_range (S : OriginalNativeHSEmptyStop.Input n Λ) :
    range (OriginalNativeHSEmptyStop.sourceInclusion S).hom.left.base = S.nativeStage.q.hom.left.base ⁻¹'
      range (OriginalNativeHSEmptyStop.neighbourhood S).inclusion.hom.left.base := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    rw [(OriginalNativeHSEmptyStop.neighbourhood S).inclusion_range]
    change S.nativeStage.q.hom.left.base z.val ∈ (OriginalNativeHSEmptyStop.neighbourhood S).openSet
    have hz : S.history.projection.hom.left.base z.val ∈
        (OriginalNativeHSEmptyStop.neighbourhood S).openSet := z.property
    exact (congrArg (fun q => q.hom.left.base z.val) S.history_projection) ▸ hz
  · intro hy
    rw [(OriginalNativeHSEmptyStop.neighbourhood S).inclusion_range] at hy
    have hz : S.history.projection.hom.left.base y ∈
        (OriginalNativeHSEmptyStop.neighbourhood S).openSet := by
      rw [S.history_projection]
      exact hy
    exact ⟨⟨y, hz⟩, rfl⟩

omit [Nonempty Λ] in
/-- Full off-H inverse after the actual EMPTY-stop restriction, also for the immediate-empty branch. -/
theorem empty_stop_off_threshold (S : OriginalNativeHSEmptyStop.Input n Λ)
    (hOld : IsIsoOver S.nativeStage.q (originalSingularHSThreshold S.base S.profile)ᶜ) :
    IsIsoOver (OriginalNativeHSEmptyStop.nativeStage S).q
      (originalSingularHSThreshold (OriginalNativeHSEmptyStop.neighbourhood S).source S.profile)ᶜ :=
  OriginalNativeHSThresholdIsomorphism.isIsoOver_open_square_threshold_compl S.profile
    S.nativeStage.q (OriginalNativeHSEmptyStop.nativeStage S).q
    (OriginalNativeHSEmptyStop.sourceInclusion S) (OriginalNativeHSEmptyStop.neighbourhood S).inclusion
    (OriginalNativeHSEmptyStop.sourceInclusion_isOpenImmersion S)
    (OriginalNativeHSEmptyStop.neighbourhood S).inclusion_isOpenImmersion
    (OriginalNativeHSEmptyStop.projection_square S) (empty_stop_range S) hOld

/-- HS geometry on the EXISTING literal final phase object, with no second output choice. -/
theorem final_hs_nonincrease (P : Input n Λ) (r : Run P)
    (hOld : ∀ y, originalStalkHS P.nativeStage.Y y ≤
      originalStalkHS P.base (P.nativeStage.q.hom.left.base y))
    (y : (OriginalNativeHSShadowFinitePhase.Run.finalSource r).obj.left) :
    originalStalkHS (OriginalNativeHSShadowFinitePhase.Run.finalSource r) y ≤
      originalStalkHS (OriginalNativeHSShadowFinitePhase.Run.finalBase r)
        ((OriginalNativeHSShadowFinitePhase.Run.finalNativeStage r).q.hom.left.base y) :=
  empty_stop_hs_nonincrease (OriginalNativeHSShadowFinitePhase.Run.finalInput r)
    (terminal_hs_nonincrease P r hOld) y

theorem final_off_threshold (P : Input n Λ) (r : Run P)
    (hOld : IsIsoOver P.nativeStage.q (originalSingularHSThreshold P.base P.profile)ᶜ) :
    IsIsoOver (OriginalNativeHSShadowFinitePhase.Run.finalNativeStage r).q
      (originalSingularHSThreshold (OriginalNativeHSShadowFinitePhase.Run.finalBase r) P.profile)ᶜ := by
  have h : IsIsoOver (OriginalNativeHSShadowFinitePhase.Run.finalNativeStage r).q
      (originalSingularHSThreshold (OriginalNativeHSShadowFinitePhase.Run.finalBase r) r.terminalInput.profile)ᶜ :=
    empty_stop_off_threshold (OriginalNativeHSShadowFinitePhase.Run.finalInput r)
      (successor_off_threshold r.terminalInput (terminalInput_off r hOld))
  simpa only [r.profile_eq] using h

section Original
variable {X : SourceReducedComplexSpace} {K : Set X.obj.left}
  (M : OriginalNativeHSCompactShadowWindows.Maximum X K) (hK : IsCompact K)
  (s : OriginalNativeShadowFirstBlowup.Step M hK)

variable (hne : (originalSingularHSThreshold s.source (originalStalkHS X M.point) ∩
  s.projection.hom.left.base ⁻¹' OriginalNativeHSFirstStageInput.compact M hK).Nonempty)

/-- Actual first-step pointwise geometry is DERIVED internally, never a caller packet. -/
theorem original_terminal_hs_nonincrease :
    letI : Nonempty (CanonicalCentres.ValTy (originalStalkHS X M.point 1 - 1)) :=
      ⟨OriginalNativeShadowInvariantCentre.level M hK⟩
    ∀ (r : Run (OriginalNativeHSFirstStageInput.phaseInput M hK s hne))
      (y : (OriginalNativeHSShadowSuccessor.nativeStage r.terminalInput).Y.obj.left),
      originalStalkHS (OriginalNativeHSShadowSuccessor.nativeStage r.terminalInput).Y y ≤
      originalStalkHS (neighbourhood r.terminalInput).source
        ((OriginalNativeHSShadowSuccessor.nativeStage r.terminalInput).q.hom.left.base y) := by
  let : Nonempty (CanonicalCentres.ValTy (originalStalkHS X M.point 1 - 1)) :=
    ⟨OriginalNativeShadowInvariantCentre.level M hK⟩
  intro r y
  exact terminal_hs_nonincrease (OriginalNativeHSFirstStageInput.phaseInput M hK s hne) r
    (OriginalNativeShadowFirstHSNonincrease.hs_nonincrease M hK s) y

/-- Actual original seed derives the FULL off-H inverse for the SAME terminal prefix. -/
theorem original_terminal_off_threshold :
    letI : Nonempty (CanonicalCentres.ValTy (originalStalkHS X M.point 1 - 1)) :=
      ⟨OriginalNativeShadowInvariantCentre.level M hK⟩
    ∀ r : Run (OriginalNativeHSFirstStageInput.phaseInput M hK s hne),
    IsIsoOver (OriginalNativeHSShadowSuccessor.nativeStage r.terminalInput).q
      (originalSingularHSThreshold (neighbourhood r.terminalInput).source (originalStalkHS X M.point))ᶜ := by
  let : Nonempty (CanonicalCentres.ValTy (originalStalkHS X M.point 1 - 1)) :=
    ⟨OriginalNativeShadowInvariantCentre.level M hK⟩
  intro r
  exact terminal_off_threshold (OriginalNativeHSFirstStageInput.phaseInput M hK s hne) r
    (OriginalNativeShadowFirstHSNonincrease.isIsoOver_threshold_compl M hK s)

theorem original_terminal_hs_eq_off_threshold :
    letI : Nonempty (CanonicalCentres.ValTy (originalStalkHS X M.point 1 - 1)) :=
      ⟨OriginalNativeShadowInvariantCentre.level M hK⟩
    ∀ (r : Run (OriginalNativeHSFirstStageInput.phaseInput M hK s hne))
    (y : (OriginalNativeHSShadowSuccessor.nativeStage r.terminalInput).Y.obj.left)
    (_hy : (OriginalNativeHSShadowSuccessor.nativeStage r.terminalInput).q.hom.left.base y ∉
      originalSingularHSThreshold (neighbourhood r.terminalInput).source (originalStalkHS X M.point)),
    originalStalkHS (OriginalNativeHSShadowSuccessor.nativeStage r.terminalInput).Y y =
      originalStalkHS (neighbourhood r.terminalInput).source
        ((OriginalNativeHSShadowSuccessor.nativeStage r.terminalInput).q.hom.left.base y) := by
  let : Nonempty (CanonicalCentres.ValTy (originalStalkHS X M.point 1 - 1)) :=
    ⟨OriginalNativeShadowInvariantCentre.level M hK⟩
  intro r y hy
  exact originalStalkHS_isIsoOver (original_terminal_off_threshold M hK s hne r) hy

/-- The original actual first-step seed gives final phase HS geometry with NO incoming packet. -/
theorem original_final_hs_nonincrease :
    letI : Nonempty (CanonicalCentres.ValTy (originalStalkHS X M.point 1 - 1)) :=
      ⟨OriginalNativeShadowInvariantCentre.level M hK⟩
    ∀ (r : Run (OriginalNativeHSFirstStageInput.phaseInput M hK s hne))
      (y : (OriginalNativeHSShadowFinitePhase.Run.finalSource r).obj.left),
      originalStalkHS (OriginalNativeHSShadowFinitePhase.Run.finalSource r) y ≤
        originalStalkHS (OriginalNativeHSShadowFinitePhase.Run.finalBase r)
          ((OriginalNativeHSShadowFinitePhase.Run.finalNativeStage r).q.hom.left.base y) := by
  let : Nonempty (CanonicalCentres.ValTy (originalStalkHS X M.point 1 - 1)) :=
    ⟨OriginalNativeShadowInvariantCentre.level M hK⟩
  intro r y
  exact final_hs_nonincrease (OriginalNativeHSFirstStageInput.phaseInput M hK s hne) r
    (OriginalNativeShadowFirstHSNonincrease.hs_nonincrease M hK s) y

theorem original_final_off_threshold :
    letI : Nonempty (CanonicalCentres.ValTy (originalStalkHS X M.point 1 - 1)) :=
      ⟨OriginalNativeShadowInvariantCentre.level M hK⟩
    ∀ r : Run (OriginalNativeHSFirstStageInput.phaseInput M hK s hne),
      IsIsoOver (OriginalNativeHSShadowFinitePhase.Run.finalNativeStage r).q
        (originalSingularHSThreshold (OriginalNativeHSShadowFinitePhase.Run.finalBase r)
          (originalStalkHS X M.point))ᶜ := by
  let : Nonempty (CanonicalCentres.ValTy (originalStalkHS X M.point 1 - 1)) :=
    ⟨OriginalNativeShadowInvariantCentre.level M hK⟩
  intro r
  exact final_off_threshold (OriginalNativeHSFirstStageInput.phaseInput M hK s hne) r
    (OriginalNativeShadowFirstHSNonincrease.isIsoOver_threshold_compl M hK s)

theorem original_final_hs_eq_off_threshold :
    letI : Nonempty (CanonicalCentres.ValTy (originalStalkHS X M.point 1 - 1)) :=
      ⟨OriginalNativeShadowInvariantCentre.level M hK⟩
    ∀ (r : Run (OriginalNativeHSFirstStageInput.phaseInput M hK s hne))
      (y : (OriginalNativeHSShadowFinitePhase.Run.finalSource r).obj.left)
      (_hy : (OriginalNativeHSShadowFinitePhase.Run.finalNativeStage r).q.hom.left.base y ∉
        originalSingularHSThreshold (OriginalNativeHSShadowFinitePhase.Run.finalBase r)
          (originalStalkHS X M.point)),
      originalStalkHS (OriginalNativeHSShadowFinitePhase.Run.finalSource r) y =
        originalStalkHS (OriginalNativeHSShadowFinitePhase.Run.finalBase r)
          ((OriginalNativeHSShadowFinitePhase.Run.finalNativeStage r).q.hom.left.base y) := by
  let : Nonempty (CanonicalCentres.ValTy (originalStalkHS X M.point 1 - 1)) :=
    ⟨OriginalNativeShadowInvariantCentre.level M hK⟩
  intro r y hy
  exact originalStalkHS_isIsoOver (original_final_off_threshold M hK s hne r) hy

end Original
end
end Hironaka.Analytic.Unibranch.OriginalNativeHSShadowRunGeometry
