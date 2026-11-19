import Hironaka.Resolution.HironakaG4ToricDivisorHistory

/-! Identify the indexed boundary history with the literal ordered boundary. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4TrackedBoundaryIndex
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupStrictSubmanifold MarkedIdeals MarkedIdeals.MarkedIdeal HironakaG4ToricDivisorHistory
  HironakaG4OptionalDivisorMasks HironakaG4LocalToricDivisors

variable {n : ℕ} {X : CMfd.{u} n}

/-- The chronological boundary indices identify with the recursively tracked
initial and exceptional indices. -/
def trackedBoundaryEquiv (D : MarkedIdeal n X) : {Y : CMfd.{u} n} →
    (T : BlowupTower X Y) → Fin (geoTransformAlong D T).E.length ≃ TrackedIndex (Fin D.E.length) T
  | _, .refl => Equiv.refl _
  | _, .step T C π hπ =>
    (finCongr (by simp [geoTransformAlong, MarkedIdeal.geoTransform])).trans
      (finSumFinEquiv.symm.trans (Equiv.sumCongr (trackedBoundaryEquiv D T) (Equiv.ofUnique (Fin 1) Unit)))


/-- The indexed sets are precisely the literal ordered boundary entries. -/
theorem trackedAlong_eq_boundary_get (D : MarkedIdeal n X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y) (i : Fin (geoTransformAlong D T).E.length),
      trackedAlong (fun j : Fin D.E.length => D.E.get j) T (trackedBoundaryEquiv D T i) =
        (geoTransformAlong D T).E.get i
  | _, .refl, i => rfl
  | _, .step T C π hπ, i => by
    let e : Fin (geoTransformAlong D (.step T C π hπ)).E.length ≃
        Fin ((geoTransformAlong D T).E.length + 1) :=
      finCongr (by simp [geoTransformAlong, MarkedIdeal.geoTransform])
    have heq (j : Fin ((geoTransformAlong D T).E.length + 1)) :
        trackedBoundaryEquiv D (.step T C π hπ) (e.symm j) =
          (Equiv.sumCongr (trackedBoundaryEquiv D T) (Equiv.ofUnique (Fin 1) Unit))
            (finSumFinEquiv.symm j) := by
      change (Equiv.sumCongr (trackedBoundaryEquiv D T) (Equiv.ofUnique (Fin 1) Unit))
        (finSumFinEquiv.symm (e (e.symm j))) = _
      rw [e.apply_symm_apply]
    have hval (j : Fin ((geoTransformAlong D T).E.length + 1)) : (e.symm j).val = j.val := rfl
    have h : ∀ j : Fin ((geoTransformAlong D T).E.length + 1),
        trackedAlong (fun a : Fin D.E.length => D.E.get a) (.step T C π hπ)
          (trackedBoundaryEquiv D (.step T C π hπ) (e.symm j)) =
            (geoTransformAlong D (.step T C π hπ)).E.get (e.symm j) := by
      intro j
      rw [heq]
      change Sum.elim (fun a => geoStrictTransform π C (trackedAlong (fun a : Fin D.E.length => D.E.get a) T a))
        (fun _ => π ⁻¹' C)
          ((Equiv.sumCongr (trackedBoundaryEquiv D T) (Equiv.ofUnique (Fin 1) Unit))
            (finSumFinEquiv.symm j)) = _
      simp only [List.get_eq_getElem, hval]
      refine Fin.lastCases ?_ (fun q => ?_) j
      · have hlast : Fin.last (geoTransformAlong D T).E.length =
            Fin.natAdd (geoTransformAlong D T).E.length (0 : Fin 1) := Fin.ext rfl
        rw [hlast, finSumFinEquiv_symm_apply_natAdd]
        simp [geoTransformAlong, MarkedIdeal.geoTransform]
      · simpa [geoTransformAlong, MarkedIdeal.geoTransform, Fin.castSucc,
          finSumFinEquiv_symm_apply_castAdd, List.get_eq_getElem] using
            congrArg (geoStrictTransform π C) (trackedAlong_eq_boundary_get D T q)
    simpa only [e.symm_apply_apply] using h (e i)

/-- A tracked strong state is a strong state for the actual ordered boundary. -/
theorem toric_state_for_ordered_boundary (D : MarkedIdeal n X) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) {A : Type*} (G : Filter A) {N : Set Y} {x : Y}
    {act : A → Y → Y}
    (hstate : LocalToricDivisorState (n := n) G N
      (trackedAlong (fun j : Fin D.E.length => D.E.get j) T) x act) :
    LocalToricDivisorState (n := n) G N (fun i : Fin (geoTransformAlong D T).E.length =>
      (geoTransformAlong D T).E.get i) x act := by
  obtain ⟨S, μ, sec, Φ, m, hsrc, hN, hD, hm, hμ, hdiag, hsec, hrealize⟩ := hstate
  let e := trackedBoundaryEquiv D T
  refine ⟨S, μ, sec, Φ, m ∘ e, hsrc, hN, ?_, ?_, hμ, hdiag, hsec, hrealize⟩
  · intro i y hy
    have hh := hD (e i) y hy
    rw [trackedAlong_eq_boundary_get D T i] at hh
    exact hh
  · constructor
    · intro i j hj
      exact hm.1 (e i) j hj
    · intro i j k hi hj
      exact e.injective (hm.2 (e i) (e j) k hi hj)

end
end Hironaka.HironakaG4TrackedBoundaryIndex
