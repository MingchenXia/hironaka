/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Smooth.Graph
import Hironaka.Scheme.Smooth.Adapted
import Hironaka.Scheme.Smooth.BlowUpSmoothChart
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The graph of two coordinate systems: projections and the coordinate identity

For two coordinate systems `u, v` on the affine open `U` (`CoordinateSystem.lean`),
`W = U ×_{𝔸ⁿ} U` with projections `ψ_u, ψ_v` (`Hironaka/Scheme/Smooth/Graph.lean`). Kollár's
`U_1(p)` and its coordinate projections ([Kol07, 95], the proof of Theorem 92); Włodarczyk's `U
×_{𝔸ⁿ} U` and the functions `w_i` on it ([Wlo05, Lemma 2.9.5], step (0) of the proof).

* `φ_u ∘ ψ_u = φ_v ∘ ψ_v` (`pullback.condition`); `W ⟶ U ×_k U` is a closed immersion,
  `𝔸ⁿ_k ⟶ Spec k` being separated (Mathlib's `IsClosedImmersion (pullback.mapDesc f g i)`); and
  `W` is the locus where the pulled back coordinates agree: a pair of `k`-morphisms `a, b : T ⟶ U`
  with `a^*(u_i) = b^*(v_i)` has `a ≫ φ_u = b ≫ φ_v`, because a morphism into the affine
  `𝔸ⁿ_k = Spec k[t]` is determined by its map on global sections (Mathlib's `ext_of_isAffine`),
  that map on `k[t]` by the images of the `t_i` and of the constants (`MvPolynomial.ringHom_ext`),
  the `t_i` go to the coordinates (`toAffineSpace_appTop_X`) and the constants to the pullbacks
  along `U ⟶ Spec k` (`toAffineSpace_appTop_C`, from `toAffineSpace_comp_structure`); so the pair
  factors uniquely through `W` (`existsUnique_lift_graph`).
* The projections are étale, as base changes of étale maps (Mathlib's instances).
* The coordinate identity `ψ_u^*(u_i) = ψ_v^*(v_i)` in `Γ(W, 𝒪_W)`: `pullback.condition` applied
  to the coordinate functions (`graphFst_appTop_eq`).
-/

public section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {n : ℕ} {U : X.affineOpens}

/-- The coordinate morphism pulls the constant `C r` of `k[t]` back to the pullback of `r` along
`U ⟶ Spec k` (`toAffineSpace_comp_structure`). -/
theorem toAffineSpace_appTop_C (v : Fin n → Γ(X, U.1)) (r : k) :
    (toAffineSpace f U.1 v).appTop
        ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) k))).inv (MvPolynomial.C r)) =
      (U.1.ι ≫ f).appTop ((Scheme.ΓSpecIso (.of k)).inv r) := by
  rw [← toAffineSpace_comp_structure f U.1 v, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  congr 1
  symm
  have h := Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin n) k)))
  rw [← CommRingCat.comp_apply, ← h, CommRingCat.comp_apply]
  rfl

/-- Two `k`-morphisms `a, b : T ⟶ U` with `a^*(u_i) = b^*(v_i)` for all `i` have
`a ≫ φ_u = b ≫ φ_v`: a morphism to `𝔸ⁿ_k` is determined by the coordinates and the `k`-structure. -/
theorem toAffineSpace_ext {T : Scheme.{u}} (v v' : Fin n → Γ(X, U.1))
    (a b : T ⟶ (U.1 : Scheme.{u})) (hk : a ≫ U.1.ι ≫ f = b ≫ U.1.ι ≫ f)
    (hcoord : ∀ i, a.appTop (U.1.topIso.inv (v i)) = b.appTop (U.1.topIso.inv (v' i))) :
    a ≫ toAffineSpace f U.1 v = b ≫ toAffineSpace f U.1 v' := by
  apply ext_of_isAffine
  rw [← cancel_epi (Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) k))).inv]
  ext1
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · have hC : ∀ (w : Fin n → Γ(X, U.1)) (g : T ⟶ (U.1 : Scheme.{u})),
        ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) k))).inv ≫
          (g ≫ toAffineSpace f U.1 w).appTop).hom (MvPolynomial.C r) =
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (g ≫ U.1.ι ≫ f).appTop).hom r := by
      intro w g
      simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
      congr 1
      exact toAffineSpace_appTop_C f w r
    rw [hC, hC, hk]
  · have hX : ∀ (w : Fin n → Γ(X, U.1)) (g : T ⟶ (U.1 : Scheme.{u})),
        ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) k))).inv ≫
          (g ≫ toAffineSpace f U.1 w).appTop).hom (MvPolynomial.X i) =
        g.appTop (U.1.topIso.inv (w i)) := by
      intro w g
      simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
      exact congrArg _ (toAffineSpace_appTop_X f U.1 w i)
    rw [hX, hX]
    exact hcoord i

namespace EtaleCoordinates

variable {f} (c c' : EtaleCoordinates f n U)

/-- `φ_u ∘ ψ_u = φ_v ∘ ψ_v`. -/
theorem graphFst_comp_toAffineSpace :
    c.graphFst c' ≫ toAffineSpace f U.1 c.v = c.graphSnd c' ≫ toAffineSpace f U.1 c'.v :=
  pullback.condition

/-- The coordinate identity `ψ_u^*(u_i) = ψ_v^*(v_i)` in `Γ(W, 𝒪_W)` (Włodarczyk's
`w_i = φ_u^*(u_i) = φ_v^*(v_i)`, the proof of [Wlo05, Lemma 2.9.5]). -/
theorem graphFst_appTop_eq (i : Fin n) :
    (c.graphFst c').appTop (U.1.topIso.inv (c.v i)) =
      (c.graphSnd c').appTop (U.1.topIso.inv (c'.v i)) := by
  have h := congrArg (fun g : c.graph c' ⟶ Spec (.of (MvPolynomial (Fin n) k)) =>
    g.appTop.hom ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) k))).inv.hom (MvPolynomial.X i)))
    (c.graphFst_comp_toAffineSpace c')
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h
  have e1 : (toAffineSpace f U.1 c.v).appTop.hom
      ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) k))).inv.hom (MvPolynomial.X i)) =
      U.1.topIso.inv.hom (c.v i) := toAffineSpace_appTop_X f U.1 c.v i
  have e2 : (toAffineSpace f U.1 c'.v).appTop.hom
      ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) k))).inv.hom (MvPolynomial.X i)) =
      U.1.topIso.inv.hom (c'.v i) := toAffineSpace_appTop_X f U.1 c'.v i
  rw [e1, e2] at h
  exact h

/-- `W` is the locus of `U ×_k U` where the pulled-back coordinate vectors agree: a pair of
`k`-morphisms `a, b : T ⟶ U` with `a^*(u_i) = b^*(v_i)` factors uniquely through `W`. -/
theorem existsUnique_lift_graph {T : Scheme.{u}} (a b : T ⟶ (U.1 : Scheme.{u}))
    (hk : a ≫ U.1.ι ≫ f = b ≫ U.1.ι ≫ f)
    (hcoord : ∀ i, a.appTop (U.1.topIso.inv (c.v i)) = b.appTop (U.1.topIso.inv (c'.v i))) :
    ∃! h : T ⟶ c.graph c', h ≫ c.graphFst c' = a ∧ h ≫ c.graphSnd c' = b := by
  have hab := toAffineSpace_ext f c.v c'.v a b hk hcoord
  refine ⟨pullback.lift a b hab, ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩,
    fun h ⟨h1, h2⟩ => ?_⟩
  apply pullback.hom_ext
  · rw [pullback.lift_fst]; exact h1
  · rw [pullback.lift_snd]; exact h2

end EtaleCoordinates

end AlgebraicGeometry
