import Hironaka.Resolution.HironakaG11PresLineStable

/-!
# Boundary-independent native HS state and the actual plain line product

Only the STATE witnesses ignore the ordered boundary field. This does
not assert canonicality, test-tower or value invariance under erasure.
Blueprint FIRST: `hironaka-g1-native-state-boundary-transport.tex`.
-/
set_option autoImplicit false
open Set Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1NativeStateBoundaryTransport
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers HironakaEmbeddedAnalytic MarkedIdeals MarkedIdeals.MarkedIdeal HironakaG11PresLineState
  HironakaG11PresLineStable HironakaActualProjectionTestRecord
  RelativePrincipalizationSpan
open scoped ProductComplexManifold

variable {n : ℕ} {X : CMfd.{0} n} {W : Set X} {H : ℕ → ℕ}

/-- The native STATE and its actual point presentations do not inspect E.
No test/canonical/value invariance is asserted by this equivalence. -/
theorem native_state_withE_iff (Q : MarkedIdeal n X) (E' : List (Set X)) :
    NativeHSState ({ Q with E := E' } : MarkedIdeal n X) W H ↔
      NativeHSState Q W H := Iff.rfl

/-- The literal plain line product retains the whole carrier/ideal/mark
of the actual projection test, with actual EMPTY boundary. -/
def plainLineRecord (Q : MarkedIdeal n X) :
    MarkedIdeal (n+1) (projectionAmbient X) :=
  { projectionTest Q with E := [] }

/-- All four literal fields, including the entire pulled ideal. -/
theorem plainLineRecord_eq (Q : MarkedIdeal n X) :
    plainLineRecord Q =
      (⟨(Prod.fst : projectionAmbient X → X) ⁻¹' Q.N, [],
        GermIdeal.pullback (m := n+1) Prod.fst Q.ideal, Q.d⟩ :
          MarkedIdeal (n+1) (projectionAmbient X)) := rfl

/-- Genuine line stability followed ONLY by state-boundary transport
gives the actual plain product state, without any order/value premise. -/
theorem native_state_plainLine {Q : MarkedIdeal n X}
    (hState : NativeHSState Q W H) :
    NativeHSState (plainLineRecord Q)
      ((Prod.fst : projectionAmbient X → X) ⁻¹' W) (lineHS H) :=
  (native_state_withE_iff (projectionTest Q) []).mpr
    (nativeLineStability Q W H hState)

end
end Hironaka.HironakaG1NativeStateBoundaryTransport
