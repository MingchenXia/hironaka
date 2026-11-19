import Hironaka.Resolution.HironakaG4LocalizedSliceIdentity
import Hironaka.Resolution.HironakaG4ToricProtectedWindow

/-! A locally presented slice yields the protected certificate after a local test. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4LocalizedProtectedWindow
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupStrictSubmanifold HomogenizedGlueingTower MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism NormalCrossings HironakaG4LocalToricDivisors
  HironakaG4ToricProtectedWindow HironakaG4LocalizedSliceIdentity HironakaG34LowerCleanupLift

variable {n : ℕ} {X Y : CMfd.{u} n} {A : Type*} {G : Filter A}

/-- Local source slice equality, local enlarged testness, and a toric state
produce the actual ambient protected-window certificate at a point over U. -/
theorem protected_window_of_local_test_history
    (D : MarkedIdeal n X) (U : Opens X)
    (hD : (MarkedIdeal.pullback (Subtype.val : U → X) D).IsWellFormed)
    (T : BlowupTower X Y)
    (hTest : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) D) (restrict U T))
    (i : Fin D.E.length) (S : Set X)
    (hSlice : (Subtype.val : U → X) ⁻¹' S =
      (Subtype.val : U → X) ⁻¹' (D.N ∩ D.E.get i))
    {F : List (Set Y)} {C : Set Y} {x : Y} {act : A → Y → Y}
    (hxU : T.proj x ∈ U) (hCclosed : IsClosed C)
    (hEclosed : ∀ K ∈ strictAlong T (D.E.get i) :: F, IsClosed K)
    (hCN : C ⊆ strictAlong T D.N) (hCan : IsComplexAnalyticSubset (n := n) C)
    {k : ℕ} (hreg : RegularAtDim (n := n) C x k)
    (hstate : LocalToricDivisorState (n := n) G (strictAlong T D.N)
      (fun j : Fin (strictAlong T (D.E.get i) :: F).length => (strictAlong T (D.E.get i) :: F).get j) x act)
    (hpreserve : ∀ᶠ p in G ×ˢ 𝓝 x, p.2 ∈ C → act p.1 p.2 ∈ C) :
    ProtectedWindowAt (strictAlong T D.N) (strictAlong T S) F C x := by
  have hident := locally_presented_slice_identity_on_open_preimage D U hD T hTest i S hSlice
  apply protectedWindowAt_of_invariant_toric_state hCclosed hEclosed hCN hCan hreg hstate hpreserve
  filter_upwards [(openPreimage T U).isOpen.mem_nhds hxU] with y hy
  exact Set.ext_iff.mp hident ⟨y,hy⟩

end
end Hironaka.HironakaG4LocalizedProtectedWindow
