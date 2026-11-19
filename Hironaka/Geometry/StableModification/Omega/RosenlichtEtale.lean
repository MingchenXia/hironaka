/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.StableModification.Omega.RosenlichtAlgebra
import Hironaka.Geometry.StableModification.Omega.EtaleNode

/-!
# Algebras étale over a node in which the node parameter vanishes

Let `K → O` be formally unramified, `c ∈ O`, and `A` a flat, formally étale algebra over the
node `N = O[u,v]/(uv - c)` (`Node O c`) in which `c` vanishes; `u, v ∈ A` are the images of the
coordinates. This is the local form of the geometric fibre of a nodal curve near its nodes: the
fibre `K ⊗ Γ(X, W)` of an étale node chart `O[u,v]/(uv - c) → Γ(X, W)` over an algebraically
closed field `K`, localized at an element of `K ⊗ O` killing `c`
(`Omega/RosenlichtFibre.lean`). Then the hypotheses of the Rosenlicht description
(`Omega/RosenlichtAlgebra.lean`) hold:

* `isNodeBranching_of_flat`: `uv = 0`, `u` is a non-zero-divisor modulo `v` and `v` modulo `u`
  (`node_sat`: in `N`, `xᵢ · a ∈ (xⱼ)` forces `a ∈ (xⱼ)`, because `N/(xⱼ) ≅ (O/(c))[xᵢ]`
  (`branchEval`, `branchSection`); it ascends along the flat `N → A`, `sat_of_flat`);
* `smul_D_bijective_away`: on a localization `A_u`, `Ω[A_u/K]` is free on `du` (OM1B's
  `etaleNodeKaehler_bijective`);
* `span_D_branch`: on the branch `A/(v)`, `Ω[(A/(v))/K]` is spanned by `du`.

Consequently (`rosenlicht_injective_of_etale`, `residue₁_eq_zero_iff_of_etale`,
`kaehlerMap₁_injective_of_etale`) Rosenlicht's module of `A` is free of rank one on
`(du/u, -dv/v)` (`isRosenlicht_iff` needs no hypothesis beyond `uv = 0`) and regular forms on
the branch are the forms `a·du/u` with vanishing residue, i.e. `Ω_{B₁}(E₁)/Ω_{B₁} ≅ 𝒪_E`.

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), §1.2,
property (b) (`semi-stable.tex`, T:1700–1704; sign corrected, ERRATA T58). Blueprint
`sm-omega-base-change.tex`, `lem:sm-node-branch-sat`, `lem:sm-sat-flat`,
`prop:sm-rosenlicht-etale`.
-/

noncomputable section

universe u

namespace Hironaka.StableModification.Omega.Rosenlicht

open Hironaka.Algebra Hironaka.Algebra.NodeBlowupChart KaehlerDifferential
open MvPolynomial TensorProduct

section NodeModel

variable {O : Type*} [CommRing O] (c : O)

/-- The `i`-th branch of the node: `O[u,v]/(uv - c) → (O/(c))[X]`, `xᵢ ↦ X`, `xⱼ ↦ 0`. -/
def branchEval (i : Fin 2) : Node O c →+* Polynomial (O ⧸ Ideal.span {c}) :=
  Ideal.Quotient.lift _
    (MvPolynomial.eval₂Hom (Polynomial.C.comp (Ideal.Quotient.mk _))
      (fun k => if k = i then Polynomial.X else 0)) (by
    intro a ha
    rw [NodeChart.uChartIdeal] at ha
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    have hc : (Ideal.Quotient.mk (Ideal.span {c}) c) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self c)
    rw [map_mul, map_sub, map_mul, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X',
      MvPolynomial.eval₂Hom_C, RingHom.comp_apply, hc, map_zero, sub_zero]
    fin_cases i <;> simp)

theorem branchEval_coordinate_self (i : Fin 2) :
    branchEval c i (coordinate c i) = Polynomial.X := by
  change MvPolynomial.eval₂Hom _ _ (MvPolynomial.X i) = _
  rw [MvPolynomial.eval₂Hom_X', if_pos rfl]

theorem branchEval_coordinate_other {i j : Fin 2} (hij : i ≠ j) :
    branchEval c i (coordinate c j) = 0 := by
  change MvPolynomial.eval₂Hom _ _ (MvPolynomial.X j) = _
  rw [MvPolynomial.eval₂Hom_X', if_neg (Ne.symm hij)]

/-- The inverse of `branchEval` modulo `xⱼ`: `(O/(c))[X] → O[u,v]/(uv - c, xⱼ)`, `X ↦ xᵢ`. -/
def branchSection {i j : Fin 2} (hij : i ≠ j) :
    Polynomial (O ⧸ Ideal.span {c}) →+* Node O c ⧸ Ideal.span {coordinate c j} :=
  Polynomial.eval₂RingHom
    (Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (algebraMap O (Node O c))) (by
      intro a ha
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      have hprod : coordinate c 0 * coordinate c 1 = algebraMap O (Node O c) c :=
        NodeDomain.nodeCoordinateProduct c
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, map_mul, ← hprod]
      fin_cases j
      · exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
      · exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))))
    (Ideal.Quotient.mk _ (coordinate c i))

theorem branchSection_comp_branchEval {i j : Fin 2} (hij : i ≠ j) :
    (branchSection c hij).comp (branchEval c i) = Ideal.Quotient.mk _ := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply]
    change branchSection c hij (MvPolynomial.eval₂Hom _ _ (MvPolynomial.C r)) = _
    rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply, branchSection, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_C, Ideal.Quotient.lift_mk, RingHom.comp_apply]
    rfl
  · intro k
    simp only [RingHom.comp_apply]
    change branchSection c hij (MvPolynomial.eval₂Hom _ _ (MvPolynomial.X k)) =
      Ideal.Quotient.mk _ (coordinate c k)
    rw [MvPolynomial.eval₂Hom_X']
    by_cases hki : k = i
    · subst hki
      rw [if_pos rfl, branchSection, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    · have hkj : k = j := by
        fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
      subst hkj
      rw [if_neg hki, map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton_self _

/-- In the node `O[u,v]/(uv - c)`, `xᵢ` is a non-zero-divisor modulo `xⱼ` for `i ≠ j`
(`O[u,v]/(uv - c, xⱼ) ≅ (O/(c))[xᵢ]`). -/
theorem node_sat {i j : Fin 2} (hij : i ≠ j) (a : Node O c)
    (ha : coordinate c i * a ∈ Ideal.span {coordinate c j}) :
    a ∈ Ideal.span {coordinate c j} := by
  have h0 : branchEval c i a = 0 := by
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp ha
    have := congrArg (branchEval c i) hr
    rw [map_mul, map_mul, branchEval_coordinate_other c hij, mul_zero,
      branchEval_coordinate_self] at this
    exact (Polynomial.isRegular_X.left (this.symm.trans (mul_zero _).symm))
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← branchSection_comp_branchEval c hij, RingHom.comp_apply,
    h0, map_zero]

theorem coordinate_mul_coordinate (c : O) :
    coordinate c 0 * coordinate c 1 = algebraMap O (Node O c) c :=
  NodeDomain.nodeCoordinateProduct c

end NodeModel

section Flat

variable {N A : Type*} [CommRing N] [CommRing A] [Algebra N A] [Module.Flat N A]

/-- **Saturation ascends along flat maps**: if `x` is a non-zero-divisor modulo `y` in `N`, its
image is a non-zero-divisor modulo the image of `y` in a flat `N`-algebra. -/
theorem sat_of_flat {x y : N} (H : ∀ a : N, x * a ∈ Ideal.span {y} → a ∈ Ideal.span {y})
    (a : A) (ha : algebraMap N A x * a ∈ Ideal.span {algebraMap N A y}) :
    a ∈ Ideal.span {algebraMap N A y} := by
  set I : Ideal N := Ideal.span {y}
  have hI : I.map (algebraMap N A) = Ideal.span {algebraMap N A y} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hregq : IsSMulRegular (N ⧸ I) x := by
    intro a b hab
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    dsimp only at hab
    rw [Ideal.Quotient.eq]
    apply H
    rw [mul_sub]
    rw [Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul,
      Ideal.Quotient.eq] at hab
    exact hab
  have hregT : IsSMulRegular (A ⊗[N] (N ⧸ I)) x := hregq.lTensor A
  let e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I
  have ha' : Ideal.Quotient.mk (I.map (algebraMap N A)) a = 0 := by
    apply e.injective
    rw [map_zero]
    apply hregT
    dsimp only
    rw [smul_zero]
    change x • (a ⊗ₜ[N] (1 : N ⧸ I)) = 0
    rw [TensorProduct.smul_tmul', Algebra.smul_def]
    change e (Ideal.Quotient.mk _ (algebraMap N A x * a)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (by rw [hI]; exact ha), map_zero]
  rw [Ideal.Quotient.eq_zero_iff_mem, hI] at ha'
  exact ha'

end Flat

section Etale

variable {K O : Type u} [CommRing K] [CommRing O] [Algebra K O] {c : O}
  {A : Type u} [CommRing A] [Algebra (Node O c) A]

/-- **An algebra flat over the node `O[u,v]/(uv - c)` in which `c` vanishes branches like a
node.** -/
theorem isNodeBranching_of_flat [Module.Flat (Node O c) A]
    (hc : algebraMap (Node O c) A (algebraMap O (Node O c) c) = 0) :
    IsNodeBranching (algebraMap (Node O c) A (coordinate c 0))
      (algebraMap (Node O c) A (coordinate c 1)) where
  mul_eq_zero := by rw [← map_mul, coordinate_mul_coordinate, hc]
  sat₁ := sat_of_flat (node_sat c (by decide : (0 : Fin 2) ≠ 1))
  sat₂ := sat_of_flat (node_sat c (by decide : (1 : Fin 2) ≠ 0))

variable [Algebra K A] [IsScalarTower K (Node O c) A] [Algebra.FormallyUnramified K O]
  [Algebra.FormallyEtale (Node O c) A]

/-- **`Ω` on `D(xᵢ)` is free on `dxᵢ`**: on a localization `A_x` of `A` at a coordinate `x = xᵢ`,
`Ω[A_x/K]` is free on `dx`. -/
theorem smul_D_bijective_away (i : Fin 2) (Aₓ : Type u) [CommRing Aₓ] [Algebra A Aₓ]
    [IsLocalization.Away (algebraMap (Node O c) A (coordinate c i)) Aₓ] [Algebra K Aₓ]
    [IsScalarTower K A Aₓ] :
    Function.Bijective fun x : Aₓ =>
      x • D K Aₓ (algebraMap A Aₓ (algebraMap (Node O c) A (coordinate c i))) := by
  let : Algebra (Node O c) Aₓ := ((algebraMap A Aₓ).comp (algebraMap (Node O c) A)).toAlgebra
  have : IsScalarTower (Node O c) A Aₓ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower K (Node O c) Aₓ :=
      IsScalarTower.of_algebraMap_eq (S := Node O c) (A := Aₓ) fun k => by
    change algebraMap K Aₓ k = algebraMap A Aₓ (algebraMap (Node O c) A (algebraMap K _ k))
    rw [← IsScalarTower.algebraMap_apply K (Node O c) A, ← IsScalarTower.algebraMap_apply K A Aₓ]
  have : Algebra.FormallyEtale A Aₓ :=
    Algebra.FormallyEtale.of_isLocalization
      (Submonoid.powers (algebraMap (Node O c) A (coordinate c i)))
  have : Algebra.FormallyEtale (Node O c) Aₓ := Algebra.FormallyEtale.comp (Node O c) A Aₓ
  have hu : IsUnit (algebraMap (Node O c) Aₓ (coordinate c i)) := by
    rw [IsScalarTower.algebraMap_apply (Node O c) A Aₓ]
    exact IsLocalization.Away.algebraMap_isUnit _
  have h := etaleNodeKaehler_bijective (R := K) (O := O) (T := Aₓ) c i hu
  rw [IsScalarTower.algebraMap_apply (Node O c) A Aₓ] at h
  exact h

/-- **Differentials on a branch**: `Ω[(A/(xⱼ))/K]` is spanned by `dxᵢ`, `{i, j} = {0, 1}`. -/
theorem span_D_branch {i j : Fin 2} (hij : i ≠ j) :
    Submodule.span (A ⧸ Ideal.span {algebraMap (Node O c) A (coordinate c j)})
        {D K _ (Ideal.Quotient.mk (Ideal.span {algebraMap (Node O c) A (coordinate c j)})
          (algebraMap (Node O c) A (coordinate c i)))} = ⊤ := by
  set I := Ideal.span {algebraMap (Node O c) A (coordinate c j)}
  set B := A ⧸ I
  set Nb := Submodule.span B {D K B (Ideal.Quotient.mk I
    (algebraMap (Node O c) A (coordinate c i)))}
  -- differentials of functions on the node
  have hnode : ∀ n : Node O c,
      D K B (Ideal.Quotient.mk I (algebraMap (Node O c) A n)) ∈ Nb := by
    intro n
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective n
    induction p using MvPolynomial.induction_on with
    | C r =>
      have h0 := D_algebraMap_base_eq_zero (R := K) (T := B) c r
      change D K B (algebraMap (Node O c) B (algebraMap O (Node O c) r)) ∈ Nb
      rw [h0]
      exact Nb.zero_mem
    | add p q hp hq =>
      rw [map_add, map_add, map_add, map_add]
      exact Nb.add_mem hp hq
    | mul_X p k hp =>
      rw [map_mul, map_mul, map_mul, Derivation.leibniz]
      refine Nb.add_mem (Nb.smul_mem _ ?_) (Nb.smul_mem _ hp)
      by_cases hki : k = i
      · subst hki
        exact Submodule.subset_span rfl
      · have hkj : k = j := by
          fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
        subst hkj
        have : Ideal.Quotient.mk I (algebraMap (Node O c) A
            (Ideal.Quotient.mk (NodeChart.uChartIdeal O c) (X k))) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
        rw [this, map_zero]
        exact Nb.zero_mem
  -- differentials of functions on `A`
  have hA : ∀ a : A, D K B (Ideal.Quotient.mk I a) ∈ Nb := by
    intro a
    have hDa : D K A a ∈ Submodule.span A
        (Set.range fun n : Node O c => D K A (algebraMap (Node O c) A n)) := by
      rw [span_D_algebraMap_eq_top (R := K) (S := Node O c) (T := A)]
      trivial
    have hmap : ∀ ω ∈ Submodule.span A
        (Set.range fun n : Node O c => D K A (algebraMap (Node O c) A n)),
        KaehlerDifferential.map K K A B ω ∈ Nb := by
      intro ω hω
      induction hω using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨n, rfl⟩ := hx
        rw [KaehlerDifferential.map_D]
        exact hnode n
      | zero => rw [map_zero]; exact Nb.zero_mem
      | add x y _ _ hx hy => rw [map_add]; exact Nb.add_mem hx hy
      | smul t x _ hx =>
        rw [LinearMap.map_smul, ← algebraMap_smul B t]
        exact Nb.smul_mem _ hx
    have := hmap _ hDa
    rwa [KaehlerDifferential.map_D] at this
  rw [eq_top_iff, ← span_range_derivation K B, Submodule.span_le]
  rintro _ ⟨b, rfl⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact hA a

end Etale

section Consequences

variable {K O : Type u} [CommRing K] [CommRing O] [Algebra K O] {c : O}
  {A : Type u} [CommRing A] [Algebra (Node O c) A] [Algebra K A] [IsScalarTower K (Node O c) A]
  [Algebra.FormallyUnramified K O] [Algebra.FormallyEtale (Node O c) A] [Module.Flat (Node O c) A]
  (hc : algebraMap (Node O c) A (algebraMap O (Node O c) c) = 0)
  (Aᵤ Aᵥ : Type u) [CommRing Aᵤ] [CommRing Aᵥ] [Algebra A Aᵤ] [Algebra A Aᵥ]
  [IsLocalization.Away (algebraMap (Node O c) A (coordinate c 0)) Aᵤ]
  [IsLocalization.Away (algebraMap (Node O c) A (coordinate c 1)) Aᵥ]
  [Algebra K Aᵤ] [Algebra K Aᵥ] [IsScalarTower K A Aᵤ] [IsScalarTower K A Aᵥ]

include hc

/-- **The Rosenlicht module of an étale node chart is free of rank one** on `(du/u, -dv/v)`. -/
theorem rosenlicht_injective_of_etale :
    Function.Injective (rosenlicht K (algebraMap (Node O c) A (coordinate c 0))
      (algebraMap (Node O c) A (coordinate c 1)) Aᵤ Aᵥ) :=
  rosenlicht_injective K Aᵤ Aᵥ (isNodeBranching_of_flat hc)
    (smul_D_bijective_away (K := K) 0 Aᵤ).1 (smul_D_bijective_away (K := K) 1 Aᵥ).1

/-- **Regular forms on the first branch** of an étale node chart are the forms `a·du/u` with
vanishing residue on the node locus. -/
theorem residue₁_eq_zero_iff_of_etale
    (a : A ⧸ Ideal.span {algebraMap (Node O c) A (coordinate c 1)}) :
    residue₁ (algebraMap (Node O c) A (coordinate c 0)) _ a = 0 ↔
      branchMap Aᵤ (isNodeBranching_of_flat hc).mul_eq_zero a •
          logForm K (algebraMap (Node O c) A (coordinate c 0)) Aᵤ ∈
        Set.range (kaehlerMap₁ K (isNodeBranching_of_flat hc) Aᵤ) :=
  residue₁_eq_zero_iff (isNodeBranching_of_flat hc) Aᵤ
    (span_D_branch (K := K) (by decide : (0 : Fin 2) ≠ 1))
    (smul_D_bijective_away (K := K) 0 Aᵤ).1 a

/-- **Regular forms on the first branch embed** into the forms on `D(u)`. -/
theorem kaehlerMap₁_injective_of_etale :
    Function.Injective (kaehlerMap₁ K (isNodeBranching_of_flat hc) Aᵤ) :=
  kaehlerMap₁_injective (isNodeBranching_of_flat hc) Aᵤ
    (span_D_branch (K := K) (by decide : (0 : Fin 2) ≠ 1))
    (smul_D_bijective_away (K := K) 0 Aᵤ).1

end Consequences

end Hironaka.StableModification.Omega.Rosenlicht
