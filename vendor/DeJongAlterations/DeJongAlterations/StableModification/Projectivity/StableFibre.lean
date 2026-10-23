/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3D)
-/
import DeJongAlterations.StableModification.Projectivity.StableHypotheses
import DeJongAlterations.StableModification.BlowDown.ContractionDimension
import DeJongAlterations.StableModification.CurvesField.AmpleFiber
import DeJongAlterations.StableModification.DeJong.BaseStepProjective

/-!
# Bookkeeping for the projectivity of the stable modification

The routine inputs of the local-to-global theorem (`isRelativelyProjective_of_fiberSections`) in the situation of
`Global.StableModificationProjectivity` (M. Temkin, *Stable modification of relative curves*,
J. Algebraic Geom. 19 (2010), Thm 1.1, T:1713–1749; PLAN-OM3 §3, §5 M5):

* `isProjectiveOver_pullback_snd_comp`: `T = C ×_S S'` is projective over `k` when `C` and `S'`
  are;
* `infinite_residueField`: the residue fields of a scheme over an infinite field are infinite;
* `topologicalKrullDim_fiber_le_one`: for `β : X ⟶ Y` over `q : Y ⟶ S` with `β ≫ q` a nodal
  curve, every fibre of `β` has dimension at most one (it is a subspace of a fibre of the curve);
* `hasFiberSection_of_forall_isClosed`: on a fibre all of whose points are closed the section
  hypothesis of the local-to-global theorem holds trivially (Temkin, T:1721).

Blueprint: `sm-projectivity-stable.tex`, `lem:sm-tsm-bookkeeping`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry Topology

namespace DeJongAlterations.StableModification.Projectivity

noncomputable section

variable {k : Type u} [Field k]

/-- **`C ×_S S'` is projective over `k`** when `S` is projective over `k` and `C`, `S'` are
(`DeJong.isProjectiveOver_pullback`, i.e. the Segre embedding). -/
theorem isProjectiveOver_pullback_snd_comp {S C S' : Scheme.{u}} {pS : S ⟶ Spec (.of k)}
    (hS : IsProjectiveOver pS) {g : C ⟶ S} (hC : IsProjectiveOver (g ≫ pS)) {ψ : S' ⟶ S}
    (hS' : IsProjectiveOver (ψ ≫ pS)) :
    IsProjectiveOver (pullback.snd g ψ ≫ ψ ≫ pS) := by
  have : IsProper pS := hS.isProper
  have h := DeJong.isProjectiveOver_pullback g ψ pS hC hS'
  rw [← Category.assoc, ← pullback.condition, Category.assoc]
  exact h

/-- **Residue fields over an infinite field are infinite.** -/
theorem infinite_residueField [Infinite k] {T : Scheme.{u}} (pT : T ⟶ Spec (.of k)) (y : T) :
    Infinite (T.residueField y) := by
  let φ : k →+* T.residueField y := (Spec.preimage (T.fromSpecResidueField y ≫ pT)).hom
  exact Infinite.of_injective φ φ.injective

/-- **The fibres of a morphism from a nodal curve have dimension at most one**: for
`β : X ⟶ Y` and `q : Y ⟶ S` with `β ≫ q` a nodal curve, `β⁻¹(y) ⊆ (β ≫ q)⁻¹(q y)`, and the
fibres of a nodal curve have dimension at most one (`BlowDown.topologicalKrullDim_fiber_le_one_of_nodal`). -/
theorem topologicalKrullDim_fiber_le_one {X Y S : Scheme.{u}} (β : X ⟶ Y) (q : Y ⟶ S)
    [DeJong.IsNodalCurve (β ≫ q)] (y : Y) : topologicalKrullDim (β.fiber y) ≤ 1 := by
  rw [IsHomeomorph.topologicalKrullDim_eq _ (β.fiberHomeo y).isHomeomorph]
  have hsub : β ⁻¹' {y} ⊆ (β ≫ q) ⁻¹' {q y} := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
    rw [Scheme.Hom.comp_apply, hx]
  have h1 : topologicalKrullDim (β ⁻¹' {y}) ≤ topologicalKrullDim ((β ≫ q) ⁻¹' {q y}) :=
    (Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le
  have h2 : topologicalKrullDim ((β ≫ q) ⁻¹' {q y}) = topologicalKrullDim ((β ≫ q).fiber (q y)) :=
    IsHomeomorph.topologicalKrullDim_eq _ ((β ≫ q).fiberHomeo (q y)).symm.isHomeomorph
  exact h1.trans (h2.le.trans (BlowDown.topologicalKrullDim_fiber_le_one_of_nodal (β ≫ q) (q y)))

/-- **Fibres consisting of closed points**: if every point of the fibre `X_y` is closed (a
zero-dimensional fibre; Temkin, T:1721: "otherwise `Z` is zero-dimensional and so `ω|_Z` is
ample"), the section hypothesis `HasFiberSection` of the local-to-global theorem holds with the
zero section, for which both conditions are vacuous. -/
theorem hasFiberSection_of_forall_isClosed {X Y : Scheme.{u}} (L : LineBundleData X) (β : X ⟶ Y)
    (y : Y) (hcl : ∀ x : β.fiber y, IsClosed ({x} : Set (β.fiber y))) : HasFiberSection β L y :=
  ⟨1, 0, one_pos, fun x hx => absurd (hcl x) hx, fun x hx => absurd (hcl x) hx⟩

end

end DeJongAlterations.StableModification.Projectivity
