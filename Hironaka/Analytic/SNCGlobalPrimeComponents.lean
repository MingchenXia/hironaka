/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.GlobalSmoothHypersurfacePrimeComponent
import Hironaka.Blowup.NormalCrossings

set_option autoImplicit false

/-! # Actual ordered SNC members internally produce whole-source prime components -/

open Set Filter
open scoped Topology

namespace Hironaka.SNCGlobalPrimeComponents

open NormalCrossings

noncomputable section

variable {m : ℕ} {Y : Type*} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]

omit [IsComplexManifold (m + 1) Y] in
/-- Actual SNC coordinates and a genuine coordinate swap internally supply the member flattening. -/
theorem regularAtDim_member {E : List (Set Y)} (hE : IsSNCDivisor (m + 1) E)
    (i : Fin E.length) {x : Y} (hx : x ∈ E.get i) :
    RegularAtDim (n := m + 1) (E.get i) x m := by
  classical
  obtain ⟨S, ⟨Φ, hsrc, h0, hflat⟩, hcard, _⟩ := hE.2 x
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp (hcard i hx)
  let e : Equiv.Perm (Fin (m + 1)) := Equiv.swap j (Fin.last m)
  let L : ComplexModel (m + 1) ≃L[ℂ] ComplexModel (m + 1) :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toContinuousLinearEquiv
  have hlast (z : ComplexModel (m + 1)) : (L z) (Fin.last m) = z j := by
    change z (e.symm (Fin.last m)) = z j
    simp [e]
  have hplane (z : ComplexModel (m + 1)) :
      z ∈ coordSubspace ({j} : Finset (Fin (m + 1))) ↔
        L z ∈ complexCoordinatePlane (m + 1) m := by
    constructor
    · intro hz k hk
      have hk' : k = Fin.last m := Fin.ext (by simp only [Fin.val_last]; omega)
      rw [hk', hlast]
      exact hz j (Finset.mem_singleton_self j)
    · intro hz k hk
      rw [Finset.mem_singleton.mp hk]
      rw [← hlast]
      exact hz (Fin.last m) le_rfl
  let Θ : LocalHolomorphicEquivAt (n := m + 1) ((complexChartAt (n := m + 1) x).val x) := {
    source := Φ.source
    target := L.symm ⁻¹' Φ.target
    isOpen_source := Φ.isOpen_source
    isOpen_target := Φ.isOpen_target.preimage L.symm.continuous
    center_mem_source := Φ.center_mem_source
    toFun := fun z => L (Φ.toFun z)
    invFun := fun z => Φ.invFun (L.symm z)
    toFun_holomorphic := L.differentiable.comp_differentiableOn Φ.toFun_holomorphic
    invFun_holomorphic := Φ.invFun_holomorphic.comp L.symm.differentiable.differentiableOn
      (fun _ hz => hz)
    mapsTo_toFun := by
      intro z hz
      change L.symm (L (Φ.toFun z)) ∈ Φ.target
      rw [L.symm_apply_apply]
      exact Φ.mapsTo_toFun hz
    mapsTo_invFun := fun _ hz => Φ.mapsTo_invFun hz
    left_inv := by
      intro z hz
      rw [L.symm_apply_apply]
      exact Φ.left_inv z hz
    right_inv := by
      intro z hz
      rw [Φ.right_inv _ hz, L.apply_symm_apply] }
  refine ⟨Nat.le_succ m, hx, Θ, hsrc, ?_, ?_⟩
  · change L (Φ.toFun ((complexChartAt (n := m + 1) x).val x)) = 0
    rw [h0, L.map_zero]
  · intro y hy hyΦ
    have hfi := hflat i hx hy hyΦ
    rw [hj] at hfi
    exact hfi.trans (hplane (Φ.toFun ((complexChartAt (n := m + 1) x).val y)))

/-- Genuine whole SNC data supply the actual global connected smooth prime without an extra component premise. -/
theorem exists_global_prime_component {E : List (Set Y)} (hE : IsSNCDivisor (m + 1) E)
    (i : Fin E.length) {x : Y} (hx : x ∈ E.get i) :
    ∃ V : ClosedIrreducibleAnalyticSubvariety (m + 1) Y,
      V.dim = m ∧ V.carrier = connectedComponentIn (E.get i) x ∧ x ∈ V.carrier ∧
      V.carrier ⊆ E.get i ∧ IsConnected V.carrier ∧
      (∀ y ∈ V.carrier, RegularAtDim (n := m + 1) V.carrier y m) ∧
      ∀ y ∈ V.carrier, ∃ W : Set Y, IsOpen W ∧ y ∈ W ∧
        E.get i ∩ W = V.carrier ∩ W :=
  GlobalSmoothHypersurfacePrimeComponent.exists_global_prime_component
    (hE.1 _ (List.get_mem _ _)) (fun _y hy => regularAtDim_member hE i hy) hx

end
end Hironaka.SNCGlobalPrimeComponents
