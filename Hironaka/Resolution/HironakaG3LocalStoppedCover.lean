import Hironaka.Resolution.HironakaG3StoppedAmbientBridge
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3LocalStoppedCover
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  SubmanifoldChartedSpace HironakaActualNativeSectionFiniteHistory
  HironakaDisjointNativeReferenceWindow HironakaG3RStoppedOverlap
  HironakaG3RTowerClass HironakaOriginalTerminalAtlas
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open ResolutionDriver (maxLocus)

/-- Native stopped histories cover the ambient manifold by literal ambient
opens, using the empty history off the closed contact. -/
theorem exists_ambient_open_with_stopped_native_history
    {d t : ℕ} {X : CMfd.{0} (d+t)} (N : Set X) (hNc : IsClosed N)
    (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d)
    (M : MarkedIdeal d (nativeManifold (Nat.le_add_right d t) N hN))
    (hM : IsInvDomain d M) (O : Opens (nativeManifold (Nat.le_add_right d t) N hN))
    (x : X) :
    ∃ U : Opens X, x ∈ U ∧ ∃ (Y : CMfd.{0} d)
      (T : BlowupTower (CMfd.of (n := d) (nativeWindow (Nat.le_add_right d t) N hN U)) Y),
      stoppedClass M O (nativeWindow (Nat.le_add_right d t) N hN U) Y T := by
  let := chartedSpace (Nat.le_add_right d t) hN
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
  by_cases hx : x ∈ N
  · obtain ⟨A,hxA,Y,T,hStop⟩ := covers_stoppedClass hM O (⟨x,hx⟩ : nativeManifold (Nat.le_add_right d t) N hN)
    obtain ⟨W,hW,hWA⟩ := isOpen_induced_iff.mp A.isOpen
    let U : Opens X := ⟨W,hW⟩
    have hxU : x ∈ U := by
      have h : (⟨x,hx⟩ : nativeManifold (Nat.le_add_right d t) N hN) ∈
          (A : Set (nativeManifold (Nat.le_add_right d t) N hN)) := hxA
      rw [← hWA] at h
      exact h
    have hUA : nativeWindow (Nat.le_add_right d t) N hN U = A := by
      apply Opens.ext
      exact hWA
    subst A
    exact ⟨U,hxU,Y,T,hStop⟩
  · let U : Opens X := ⟨Nᶜ,hNc.isOpen_compl⟩
    have hempty : IsEmpty (nativeWindow (Nat.le_add_right d t) N hN U) := by
      refine ⟨fun p => ?_⟩
      exact p.property p.val.property
    refine ⟨U,hx,CMfd.of (n := d) (nativeWindow (Nat.le_add_right d t) N hN U),.refl,?_⟩
    refine ⟨True.intro,True.intro,Or.inr ⟨True.intro,?_⟩⟩
    ext p
    exact isEmptyElim p

end
end Hironaka.HironakaG3LocalStoppedCover
