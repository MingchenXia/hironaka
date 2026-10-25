/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Omega.Invertible
import DeJongAlterations.Geometry.GenericSmoothness

/-!
# The smooth locus of a geometric fibre of a nodal curve

Let `f : X ⟶ S` be a nodal curve, `K` an algebraically closed field, `a : Spec K ⟶ S`, and
`X_K = X ×_S Spec K` with projections `ψ = pullback.fst f a : X_K ⟶ X` and
`f_K = pullback.snd f a : X_K ⟶ Spec K`. This file proves

  `ψ⁻¹ Sm(f) = Sm(f_K)` (`preimage_smoothLocus_eq_of_isNodalCurve`),

one of the three connections between the scheme `X_K` and the algebra of the geometric fibre of
an étale node chart (`Omega/RosenlichtFibre.lean`) that the comparison of `ω_{X/S}` with
Rosenlicht's sheaf of `X_K` needs (blueprint `sm-omega-base-change-fibre.tex`,
`lem:sm-omega-bcf-smooth-locus`; the proof of `thm:sm-omega-base-change-fibre` in
`sm-omega-base-change.tex`, step "the smooth locus"). Consequently the closed points of `X_K`
over the non-smooth locus of `f` are geometric ordinary double points
(`isGeometricOrdinaryDoublePoint_of_not_mem_smoothLocus`).

* `preimage_smoothLocus_le_of_isPullback`: for any pullback square, smooth points of `f` pull back
  to smooth points of the base change (smoothness is stable under base change; the restriction of
  `f` to its smooth locus is smooth, `GenericSmoothness.smooth_smoothLocus`).
* `mem_smoothLocus_of_isClosed_of_mem_smoothLocus`: a closed point of `X_K` at which `f_K` is
  smooth lies over `Sm(f)`; this is OM1B's fibre criterion `mem_smoothLocus_of_tensorChart_spec`
  (blueprint `lem:sm-omega-smooth-geometric-point`) transported from the tensor chart
  `Spec (K ⊗_{Γ(S,V)} Γ(X,W)) ⟶ X_K` (`Curves.SemistableOpen.tensorChart`) to `X_K`.
* `smoothLocus_le_preimage_of_isNodalCurve`: all points, since `X_K` is a Jacobson space
  (locally of finite type over a field) and `Sm(f_K) ∖ ψ⁻¹ Sm(f)` is locally closed.

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), §1.2
(`semi-stable.tex`, T:1676–1681: `(C,D)` is semi-stable iff its geometric fibres are).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace DeJongAlterations.StableModification.Omega

open Curves.SemistableOpen
open DeJong (IsNodalCurve)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section BaseChange

variable {X Y S T : Scheme.{u}} {f : X ⟶ S} {f' : Y ⟶ T} {ψ : Y ⟶ X} {h : T ⟶ S}

/-- **Smooth points base change to smooth points**: in a pullback square
`ψ ≫ f = f' ≫ h`, the preimage of the smooth locus of `f` lies in the smooth locus of `f'`. -/
theorem preimage_smoothLocus_le_of_isPullback [LocallyOfFinitePresentation f]
    [LocallyOfFinitePresentation f'] (H : IsPullback ψ f' f h) :
    ψ ⁻¹ᵁ f.smoothLocus ≤ f'.smoothLocus := by
  set U := f.smoothLocus
  have hs : Smooth (U.ι ≫ f) := Geometry.GenericSmoothness.smooth_smoothLocus f
  have H' : IsPullback (ψ ∣_ U) ((ψ ⁻¹ᵁ U).ι ≫ f') (U.ι ≫ f) h :=
    (isPullback_morphismRestrict ψ U).paste_vert H
  have hs' : Smooth ((ψ ⁻¹ᵁ U).ι ≫ f') := MorphismProperty.of_isPullback H' hs
  intro y hy
  have htop : ((ψ ⁻¹ᵁ U).ι ≫ f').smoothLocus = ⊤ := Scheme.Hom.smoothLocus_eq_top _
  have hmem : (⟨y, hy⟩ : (ψ ⁻¹ᵁ U : Scheme)) ∈ ((ψ ⁻¹ᵁ U).ι ≫ f').smoothLocus := by
    rw [htop]; trivial
  rw [← Scheme.Hom.preimage_smoothLocus_eq] at hmem
  exact hmem

end BaseChange

section Fibre

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsNodalCurve f]
  (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S)

omit [IsNodalCurve f] [IsAlgClosed K] in
/-- A morphism from the spectrum of a field factors through every affine open containing the
image of its point. -/
theorem exists_eq_specMap_comp_fromSpec {V : S.Opens} (hV : IsAffineOpen V)
    (hmem : ∀ z, a z ∈ V) :
    ∃ φ : Γ(S, V) →+* K, a = Spec.map (CommRingCat.ofHom φ) ≫ hV.fromSpec := by
  have hrange : Set.range a ⊆ Set.range hV.fromSpec := by
    rintro _ ⟨z, rfl⟩
    rw [hV.range_fromSpec]
    exact hmem z
  set a' := IsOpenImmersion.lift hV.fromSpec a hrange
  refine ⟨(Spec.preimage a').hom, ?_⟩
  rw [show CommRingCat.ofHom (Spec.preimage a').hom = Spec.preimage a' from rfl,
    Spec.map_preimage, IsOpenImmersion.lift_fac]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- **The fibre criterion at closed points**: a closed point of the geometric fibre `X_K` at which
`X_K → Spec K` is smooth lies over the smooth locus of the nodal curve `f`. -/
theorem mem_smoothLocus_of_isClosed_of_mem_smoothLocus (x : pullback (C := Scheme.{u}) f a)
    (hx : IsClosed ({x} : Set (pullback (C := Scheme.{u}) f a))) (hs : x ∈ (pullback.snd f a).smoothLocus) :
    pullback.fst f a x ∈ f.smoothLocus := by
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := f (pullback.fst f a x)) (U := ⊤) trivial
  obtain ⟨W, hW, hxW, hWV⟩ :=
    exists_isAffineOpen_mem_and_subset (x := pullback.fst f a x) (U := f ⁻¹ᵁ V) hxV
  have hle : W ≤ f ⁻¹ᵁ V := hWV
  have hmem : ∀ z, a z ∈ V := by
    intro z
    have hz : z = pullback.snd f a x := Subsingleton.elim _ _
    subst hz
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
    exact hxV
  obtain ⟨φ, rfl⟩ := exists_eq_specMap_comp_fromSpec K a hV hmem
  let : Algebra Γ(S, V) K := φ.toAlgebra
  let := (f.appLE V W hle).hom.toAlgebra
  have hsq : hW.fromSpec ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, W))) ≫ hV.fromSpec :=
    (IsAffineOpen.SpecMap_appLE_fromSpec f hV hW hle).symm
  have ha : Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) K)) ≫ hV.fromSpec =
      Spec.map (CommRingCat.ofHom φ) ≫ hV.fromSpec := rfl
  have hxB : pullback.fst f _ x ∈ Set.range hW.fromSpec := by
    rw [hW.range_fromSpec]; exact hxW
  obtain ⟨zp, hzp, hzc⟩ := exists_tensorChart_eq f hsq ha x hx hxB
  have key := mem_smoothLocus_of_tensorChart_spec f hV hW hle K zp hzc
    (by rw [show tensorChart f (IsAffineOpen.SpecMap_appLE_fromSpec f hV hW hle).symm
      (a := Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) K)) ≫ hV.fromSpec) rfl zp = x
        from hzp]; exact hs)
  rw [jB_comap_eq f hsq ha zp, hzp] at key
  exact key

/-- The geometric fibre of a curve locally of finite type is a Jacobson space. -/
instance jacobsonSpace_pullback : JacobsonSpace (pullback (C := Scheme.{u}) f a) :=
  LocallyOfFiniteType.jacobsonSpace (pullback.snd f a)

/-- **The smooth locus of a geometric fibre lies over the smooth locus** of the nodal curve. -/
theorem smoothLocus_le_preimage_of_isNodalCurve :
    (pullback.snd f a).smoothLocus ≤ pullback.fst f a ⁻¹ᵁ f.smoothLocus := by
  intro x hx
  by_contra hxU
  set Z : Set (pullback (C := Scheme.{u}) f a) :=
    ((pullback.snd f a).smoothLocus : Set (pullback (C := Scheme.{u}) f a)) ∩
      ((pullback.fst f a ⁻¹ᵁ f.smoothLocus : (pullback (C := Scheme.{u}) f a).Opens) :
        Set (pullback (C := Scheme.{u}) f a))ᶜ
  have hZ : Z.Nonempty := ⟨x, hx, hxU⟩
  have hZ' : IsLocallyClosed Z :=
    (pullback.snd f a).smoothLocus.isOpen.isLocallyClosed.inter
      (pullback.fst f a ⁻¹ᵁ f.smoothLocus).isOpen.isClosed_compl.isLocallyClosed
  obtain ⟨z, ⟨hzs, hzU⟩, hzc⟩ := nonempty_inter_closedPoints hZ hZ'
  exact hzU (mem_smoothLocus_of_isClosed_of_mem_smoothLocus f K a z
    (mem_closedPoints_iff.mp hzc) hzs)

/-- **`ψ⁻¹ Sm(f) = Sm(f_K)`** for a nodal curve `f` and a geometric point `Spec K ⟶ S`
(blueprint `lem:sm-omega-bcf-smooth-locus`). -/
theorem preimage_smoothLocus_eq_of_isNodalCurve :
    pullback.fst f a ⁻¹ᵁ f.smoothLocus = (pullback.snd f a).smoothLocus :=
  le_antisymm (preimage_smoothLocus_le_of_isPullback (IsPullback.of_hasPullback f a))
    (smoothLocus_le_preimage_of_isNodalCurve f K a)

/-- The closed points of a geometric fibre of a nodal curve lying over the non-smooth locus are
geometric ordinary double points. -/
theorem isGeometricOrdinaryDoublePoint_of_not_mem_smoothLocus
    (x : pullback (C := Scheme.{u}) f a) (hx : IsClosed ({x} : Set (pullback (C := Scheme.{u}) f a))) (hxU : pullback.fst f a x ∉ f.smoothLocus) :
    Geometry.IsGeometricOrdinaryDoublePoint (pullback.snd f a) x := by
  rcases IsNodalCurve.geometricNodes (g := f) K a x hx with h | h
  · exact absurd (mem_smoothLocus_of_isClosed_of_mem_smoothLocus f K a x hx h) hxU
  · exact h

end Fibre

end DeJongAlterations.StableModification.Omega
