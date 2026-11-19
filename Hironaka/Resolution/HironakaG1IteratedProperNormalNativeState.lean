import Hironaka.Resolution.HironakaG1ProperNormalNativeState
import Hironaka.Resolution.HironakaG11PresLineStable

/-! Actual closed normal padding in arbitrary finite codimension. -/

set_option autoImplicit false

open Set TopologicalSpace

namespace Hironaka.HironakaG1IteratedProperNormalNativeState

noncomputable section

open BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  HironakaActualOpenZeroSectionDifferentials
  HironakaG1ProperCarrierNormalContact HironakaG1ProperNormalNativeState
  HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG11PresLineState HironakaG11PresLineStable HironakaG8LocalHistory

variable {n : ℕ}

/-- The coordinate open obtained by adjoining one complex normal
coordinate at each step. -/
def iteratedNormalOpen (U : Opens (ComplexModel n)) : ∀ t, Opens (ComplexModel (n + t))
  | 0 => U
  | t + 1 => productOpen (iteratedNormalOpen U t)

/-- The actual composition of all coordinate projections. -/
def iteratedNormalProjection (U : Opens (ComplexModel n)) : ∀ t, iteratedNormalOpen U t → U
  | 0 => id
  | t + 1 => iteratedNormalProjection U t ∘ projection (iteratedNormalOpen U t)

variable {U : Opens (ComplexModel n)}

/-- The whole cylindrical marked ideal after each true normal padding. -/
def iteratedNormalMarked (Q : MarkedIdeal n U) : ∀ t, MarkedIdeal (n + t) (iteratedNormalOpen U t)
  | 0 => Q
  | t + 1 => properNormalMarked (iteratedNormalMarked Q t)

/-- The closed section carrier in the same iterated normal open. -/
def iteratedNormalCarrier (W : Set U) : ∀ t, Set (iteratedNormalOpen U t)
  | 0 => W
  | t + 1 => liftedCarrier (iteratedNormalCarrier W t)

/-- Each actual step preserves the original mark and pulls back every
ordered boundary member along the composite projection. -/
theorem iteratedNormalMarked_data (Q : MarkedIdeal n U) (t : ℕ) :
    (iteratedNormalMarked Q t).d = Q.d ∧
      (iteratedNormalMarked Q t).E = Q.E.map (iteratedNormalProjection U t ⁻¹' ·) := by
  induction t with
  | zero =>
    refine ⟨rfl, ?_⟩
    change Q.E = Q.E.map (id ⁻¹' ·)
    simp
  | succ t ih =>
    refine ⟨ih.1, ?_⟩
    change (iteratedNormalMarked Q t).E.map (projection (iteratedNormalOpen U t) ⁻¹' ·) = _
    rw [ih.2, List.map_map]
    rfl

/-- All iterated actual proper normal records have their ordinary domain,
and their full native Hilbert--Samuel states refer to the actual closed
section carrier and original profile. -/
theorem iteratedNormalMarked_nativeHSState {W : Set U} {Q : MarkedIdeal n U} (H : ℕ → ℕ)
    (hQ : NativeHSState (X := CMfd.of (n := n) U) Q W H)
    (hDomain : IsInvDomain n Q) (t : ℕ) :
    IsInvDomain (n + t) (iteratedNormalMarked Q t) ∧
      NativeHSState (X := CMfd.of (n := n + t) (iteratedNormalOpen U t))
        (iteratedNormalMarked Q t) (iteratedNormalCarrier W t) H := by
  induction t with
  | zero => exact ⟨hDomain, hQ⟩
  | succ t ih =>
    exact ⟨properNormalMarked_isInvDomain _ ih.1, properNormalMarked_nativeHSState H ih.2 ih.1⟩

/-- Independent original native marks on a common source cut retain the
same native weak test class through every actual finite normal padding. -/
theorem locWPEquiv_iteratedNormalMarked_of_native (P Q : MarkedIdeal n U)
    {W : Set U} {H : ℕ → ℕ}
    (hP : NativeHSState (X := CMfd.of (n := n) U) P W H)
    (hQ : NativeHSState (X := CMfd.of (n := n) U) Q W H)
    (hPD : IsInvDomain n P) (hQD : IsInvDomain n Q) (hE : Q.E = P.E) (t : ℕ) :
    LocWPEquiv (X := CMfd.of (n := n + t) (iteratedNormalOpen U t))
      (iteratedNormalMarked P t) (iteratedNormalMarked Q t) := by
  apply locWPEquiv_native
    (iteratedNormalMarked_nativeHSState H hP hPD t).2
    (iteratedNormalMarked_nativeHSState H hQ hQD t).2
  rw [(iteratedNormalMarked_data Q t).2, (iteratedNormalMarked_data P t).2, hE]

end

end Hironaka.HironakaG1IteratedProperNormalNativeState
