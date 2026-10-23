/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.StableDownGeometricLocal
import Mathlib.Data.Set.Card.Arithmetic

/-!
# Contracting a subcurve to a point: the δ-count with the semi-stable inputs (Temkin, Cor. B.2)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, l. 4442–4446), proof of
Corollary B.2: "`g(x) = ∑_{z ∈ Z} g_{C'}(z) - |Z⁰|`. Set `n = |∂Z|`, then the number of double
points on `Z` equals `n + l` …". The first identity is CRV3's scheme-level δ-count
(`deltaInvariant_contraction_of_arithmeticGenus_eq`); this file supplies the semi-stable input:
**if every closed point of `Z = f⁻¹(x)` is a smooth point or an ordinary double point of `C'`,
then `∑ᶠ_{z ∈ Z} g_{C'}(z)` is the number of ordinary double points of `C'` on `Z`**
(`finsum_deltaInvariant_eq_ncard_nodes`), so that

  `δ_b(x) = #(double points of C' on Z) + ∑_{v ∈ Z⁰} g(v) - |Z⁰|`

(`deltaInvariant_contraction_eq_ncard_nodes`). The values `g = 1` at double points and `g = 0` at
smooth points are `CurvesField.StableDownGeometricLocal`; the points of `Z` other than its generic
points are closed since `C'` is a curve (`isClosed_singleton_of_not_mem_genericPoints`).

Blueprint: `sm-curves-fields-stabdown.tex`, `lem:sm-stabdown-count-nodes`.
-/

namespace DeJongAlterations.StableModification.CurvesField.Genus

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace Module
open DeJongAlterations.StableModification.Cohomology

set_option autoImplicit false

universe u

noncomputable section

section Topology

variable {T : Type*} [TopologicalSpace T] [QuasiSober T] [T0Space T]

/-- **On a quasi-compact curve every point which is not generic is closed**: otherwise a generic
point, the point and a closed point in its closure would form a chain of length two. -/
theorem isClosed_singleton_of_not_mem_genericPoints [CompactSpace T]
    (hdim : topologicalKrullDim T ≤ 1) {y : T} (hy : y ∉ genericPoints T) : IsClosed {y} := by
  obtain ⟨z, hzy, hz⟩ := IsClosed.exists_closed_singleton (S := closure {y}) isClosed_closure
    ⟨y, subset_closure rfl⟩
  have hyz : y ⤳ z := specializes_iff_mem_closure.2 hzy
  by_cases hzy' : z = y
  · rw [← hzy']
    exact hz
  exfalso
  obtain ⟨ξ, hξy, hne⟩ := exists_ne_specializes_of_not_mem_genericPoints hy
  let a : IrreducibleCloseds T := ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩
  let b : IrreducibleCloseds T := ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩
  let c : IrreducibleCloseds T := ⟨closure {ξ}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hab : a < b := by
    refine lt_of_le_of_ne (show closure {z} ⊆ closure {y} from
      specializes_iff_closure_subset.1 hyz) fun h => hzy' ?_
    have h' : closure {z} = closure {y} := congrArg IrreducibleCloseds.carrier h
    exact (inseparable_iff_closure_eq.2 h').eq
  have hbc : b < c := by
    refine lt_of_le_of_ne (show closure {y} ⊆ closure {ξ} from
      specializes_iff_closure_subset.1 hξy) fun h => hne ?_
    have h' : closure {y} = closure {ξ} := congrArg IrreducibleCloseds.carrier h
    exact (inseparable_iff_closure_eq.2 h').eq.symm
  rcases (Order.krullDim_le_one_iff.1 hdim) b with hmin | hmax
  · exact hmin.not_lt hab
  · exact hmax.not_lt hbc

end Topology

section Nodes

variable {X : Scheme.{u}} [IsAffineHom (pullback.diagonal (terminal.from X))]
  [Finite (genericPoints X)] {k : Type u} [Field k] (q : X ⟶ Spec (.of k))
  [LocallyOfFiniteType q] [LocallyOfFinitePresentation q]

/-- The ordinary double points of `X` (over `k`) in a set `Z`: the closed points of `Z` which are
not generic and whose completed local ring is `k[[u, v]]/(uv)`. -/
def nodesIn (Z : Set X) : Set X :=
  {y | y ∈ Z ∧ IsClosed {y} ∧ y ∉ genericPoints X ∧ Geometry.IsGeometricOrdinaryDoublePoint q y}

open scoped Classical in
/-- **The δ-invariant on a nodal subset**: at the points of `Z` it is `1` at the ordinary double
points and `0` elsewhere, if every closed point of `Z` is smooth or an ordinary double point. -/
theorem deltaInvariant_eq_ite_of_nodal [IsReduced X] [CompactSpace X]
    (hdim : topologicalKrullDim X ≤ 1) (Z : Set X)
    (hnodal : ∀ y ∈ Z, IsClosed {y} →
      DeJong.IsSmoothAt q y ∨ Geometry.IsGeometricOrdinaryDoublePoint q y)
    (y : X) (hy : y ∈ Z) :
    deltaInvariant (normalizationPointsMap (genericPoints X)) (structureCoeff q) y =
      if y ∈ nodesIn q Z then 1 else 0 := by
  classical
  by_cases hyg : y ∈ genericPoints X
  · have hy' : y ∉ nodesIn q Z := fun h => h.2.2.1 hyg
    rw [if_neg hy']
    exact deltaInvariant_eq_zero_of_mem_genericPoints (genericPoints X) rfl _ y hyg
  · have hyc := isClosed_singleton_of_not_mem_genericPoints hdim hyg
    by_cases hn : Geometry.IsGeometricOrdinaryDoublePoint q y
    · rw [if_pos (show y ∈ nodesIn q Z from ⟨hy, hyc, hyg, hn⟩)]
      exact (deltaInvariant_eq_one_of_isGeometricOrdinaryDoublePoint q hdim y hyc hyg hn).1
    · have hy' : y ∉ nodesIn q Z := fun h => hn h.2.2.2
      rw [if_neg hy']
      have hsm := (hnodal y hy hyc).resolve_right hn
      exact (deltaInvariant_eq_zero_of_isSmoothAt q hdim y hyc hyg hsm).1

/-- **`∑ᶠ_{z ∈ Z} g(z)` counts the double points on `Z`**: if every closed point of `Z` is a
smooth point or an ordinary double point of the reduced curve `X`, then the sum over `Z` of the
δ-invariants of the normalization is the number of ordinary double points of `X` in `Z` (Temkin,
Cor. B.2, l. 4444–4446). -/
theorem finsum_deltaInvariant_eq_ncard_nodes [IsReduced X] [CompactSpace X]
    (hdim : topologicalKrullDim X ≤ 1) (Z : Set X)
    (hnodal : ∀ y ∈ Z, IsClosed {y} →
      DeJong.IsSmoothAt q y ∨ Geometry.IsGeometricOrdinaryDoublePoint q y) :
    (∑ᶠ y ∈ Z, deltaInvariant (normalizationPointsMap (genericPoints X)) (structureCoeff q) y) =
      (nodesIn q Z).ncard := by
  classical
  have hsub : nodesIn q Z ⊆ Z := fun y hy => hy.1
  rw [← finsum_mem_inter_support]
  have hset : Z ∩ Function.support
      (deltaInvariant (normalizationPointsMap (genericPoints X)) (structureCoeff q)) =
        nodesIn q Z := by
    ext y
    simp only [Set.mem_inter_iff, Function.mem_support]
    constructor
    · rintro ⟨hy, hδ⟩
      rw [deltaInvariant_eq_ite_of_nodal q hdim Z hnodal y hy] at hδ
      by_contra h
      exact hδ (if_neg h)
    · intro h
      refine ⟨hsub h, ?_⟩
      rw [deltaInvariant_eq_ite_of_nodal q hdim Z hnodal y (hsub h), if_pos h]
      exact one_ne_zero
  rw [hset, finsum_mem_congr rfl fun y hy => (deltaInvariant_eq_ite_of_nodal q hdim Z hnodal y
    (hsub hy)).trans (if_pos hy)]
  exact finsum_one

end Nodes

section Contraction

variable {C C' : Scheme.{u}} (f : C' ⟶ C) (x : C) (U : C.Opens) (hU : ∀ y, y ∈ U ↔ y ≠ x)
  [IsIso (f ∣_ U)] [IsAffineHom (pullback.diagonal (terminal.from C'))] {k : Type u} [Field k]
  [Finite (genericPoints C')]

include hU in
/-- **The δ-count of a contraction with a nodal fibre** (Temkin, Cor. B.2, l. 4442–4446). In the
situation of `deltaInvariant_contraction_of_arithmeticGenus_eq` (`f : C' → C` a proper morphism of
reduced projective curves over `k`, an isomorphism off `Z = f⁻¹(x)`, `p_a(C') = p_a(C)`), if every
closed point of `Z` is a smooth point or an ordinary double point of `C'`, then

  `δ_b(x) = #(ordinary double points of C' on Z) + ∑_{v ∈ Z⁰} g(v) - |Z⁰|`,

where `b : N → C` is the outer normalization and `g(v) = p_a(C̃'_v)`. -/
theorem deltaInvariant_contraction_eq_ncard_nodes [CompactSpace C]
    [IsAffineHom (pullback.diagonal (terminal.from C))] [IsReduced C] [CompactSpace C']
    [IsReduced C'] [IsProper f] (p : C ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (p' : C' ⟶ Spec (.of k)) [LocallyOfFiniteType p'] [LocallyOfFinitePresentation p']
    (hfp : f ≫ p = p') (hxg : x ∉ genericPoints C) (hx : IsClosed {x})
    (hdim : topologicalKrullDim C ≤ 1) (hdim' : topologicalKrullDim C' ≤ 1)
    (hp : IsProjectiveOver p) (hp' : IsProjectiveOver p')
    (hpa : arithmeticGenus C' (structureCoeff p') = arithmeticGenus C (structureCoeff p))
    (G : Finset C') (hG : (G : Set C') = innerPoints f x)
    (hnodal : ∀ y ∈ f ⁻¹' {x}, IsClosed {y} →
      DeJong.IsSmoothAt p' y ∨ Geometry.IsGeometricOrdinaryDoublePoint p' y) :
    (deltaInvariant (outerMap f x) (structureCoeff p) x : ℤ) =
      ((nodesIn p' (f ⁻¹' {x})).ncard : ℤ) +
        ∑ v ∈ G, componentGenus (structureCoeff p') v - G.card := by
  rw [deltaInvariant_contraction_of_arithmeticGenus_eq f x U hU p p' hfp hxg hx hdim hdim' hp hp'
    hpa G hG, finsum_deltaInvariant_eq_ncard_nodes p' hdim' _ hnodal]

end Contraction

end

end DeJongAlterations.StableModification.CurvesField.Genus
