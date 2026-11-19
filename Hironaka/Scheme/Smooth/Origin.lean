/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Smooth.CoordinateSystem
import Hironaka.Scheme.Smooth.EtaleCoordinates
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# The image point of a coordinate system, and its stalks

* Kollár chooses the two coordinate systems `x_1, x_2, …` and `x_1', x_2, …` with
  `x_1, x_1' ∈ MC(I) ⊆ 𝔪_p`, so that both send `p` to `0` ([Kol07, 95], the proof of Theorem 92).
  The point `φ_v(x) ∈ 𝔸ⁿ_k` of the coordinate morphism `φ_v = toAffineSpace f U v` is the prime
  `(aeval v)⁻¹(𝔭_x)` of `k[t]` (`toAffineSpace_base_apply`), which contains the coordinate `t_i`
  iff `v_i ∈ 𝔭_x`, i.e. iff the germ `(v_i)_x` is not a unit, i.e. lies in `𝔪_x`
  (`X_mem_toAffineSpace_base_iff`). A prime of `k[t]` containing every `t_i` is the maximal ideal
  of the origin (`eq_origin_iff_forall_X_mem`: the kernel of evaluation at `0` consists of the
  polynomials without constant term, all in `(t_0, …, t_{n-1})`, and it is maximal). Hence
  `φ_v(x) = 0` iff all `(v_i)_x ∈ 𝔪_x` (`toAffineSpace_base_eq_origin_iff`), and two coordinate
  systems with all coordinates vanishing at `x` have the same image point
  (`toAffineSpace_base_eq`).
* For an étale `g : Y ⟶ Z` and `y ∈ Y`, the stalk map `𝒪_{Z,g(y)} → 𝒪_{Y,y}` is an unramified
  local homomorphism, so `𝔪_{g(y)} 𝒪_{Y,y} = 𝔪_y` (`map_maximalIdeal_stalkMap_of_etale`;
  [Sta, Tag 00UW]; Mathlib's `FormallyUnramified.stalkMap`,
  `Algebra.FormallyUnramified.map_maximalIdeal`). For a coordinate system this says that the
  coordinates together with parameters of `φ_u(x)` generate `𝔪_x`; at a `k`-rational point,
  `𝔪_x = (u_i − u_i(x))`.

Used for the point `(p, p)` of the graph of two coordinate systems (`GraphCompletion.lean`,
`TwoPointEtalePair.lean`) and in `HironakaExamples/OrderReduction/Example106.lean` and
`HironakaExamples/Sequence/Remark33Warning63.lean`.
-/

public section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory IsLocalRing MvPolynomial

universe u

/-! ### The origin of `𝔸ⁿ_k` -/

section Origin

variable (k : Type u) [Field k] (n : ℕ)

theorem X_mem_origin_asIdeal (i : Fin n) :
    (X i : MvPolynomial (Fin n) k) ∈ (origin k n).asIdeal := by
  rw [mem_ratPoint_asIdeal_iff, aeval_X]

/-- A polynomial vanishing at the origin lies in the ideal `(t_0, …, t_{n-1})`. -/
theorem origin_asIdeal_le_of_forall_X_mem (I : Ideal (MvPolynomial (Fin n) k))
    (hI : ∀ i, (X i : MvPolynomial (Fin n) k) ∈ I) : (origin k n).asIdeal ≤ I := by
  intro q hq
  rw [mem_ratPoint_asIdeal_iff, aeval_zero', Algebra.algebraMap_self, RingHom.id_apply] at hq
  have hq' : q ∈ Ideal.span (X '' (Set.univ : Set (Fin n)) : Set (MvPolynomial (Fin n) k)) := by
    rw [mem_ideal_span_X_image]
    intro m hm
    by_contra h
    push Not at h
    have hm0 : m = 0 := Finsupp.ext fun i => h i (Set.mem_univ i)
    rw [hm0, mem_support_iff, ← constantCoeff_eq] at hm
    exact hm hq
  refine Ideal.span_le.mpr ?_ hq'
  rintro _ ⟨i, -, rfl⟩
  exact hI i

/-- A point of `𝔸ⁿ_k` is the origin iff its prime contains every coordinate `t_i`. -/
theorem eq_origin_iff_forall_X_mem (y : Spec (.of (MvPolynomial (Fin n) k))) :
    y = origin k n ↔ ∀ i, (X i : MvPolynomial (Fin n) k) ∈ y.asIdeal := by
  constructor
  · rintro rfl
    exact X_mem_origin_asIdeal k n
  · intro hy
    exact PrimeSpectrum.ext ((isMaximal_ratPoint_asIdeal _).eq_of_le y.isPrime.ne_top
      (origin_asIdeal_le_of_forall_X_mem k n _ hy)).symm

end Origin

/-! ### The image point of a coordinate morphism -/

section Base

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {n : ℕ} {U : X.Opens}

/-- The point `φ_v(x) ∈ 𝔸ⁿ_k`: the prime `(aeval v)⁻¹(𝔭_x)` of `k[t]`, `𝔭_x` the prime of `x` in
`Γ(X, U)`. -/
theorem toAffineSpace_base_apply (hU : IsAffineOpen U) (v : Fin n → Γ(X, U)) (x : U) :
    (toAffineSpace f U v).base x =
      letI := f.sectionsAlgebra U
      PrimeSpectrum.comap (MvPolynomial.aeval (R := k) v).toRingHom (hU.primeIdealOf x) :=
  rfl

/-- The coordinate `t_i` vanishes at `φ_v(x)` iff the germ `(v_i)_x` lies in `𝔪_x`. -/
theorem X_mem_toAffineSpace_base_iff (hU : IsAffineOpen U) (v : Fin n → Γ(X, U)) (x : U)
    (i : Fin n) :
    MvPolynomial.X i ∈ ((toAffineSpace f U v).base x).asIdeal ↔
      X.presheaf.germ U x.1 x.2 (v i) ∈ maximalIdeal (X.presheaf.stalk x.1) := by
  let _ := f.sectionsAlgebra U
  have h0 : MvPolynomial.X i ∈ ((toAffineSpace f U v).base x).asIdeal ↔
      v i ∈ (hU.primeIdealOf x).asIdeal := by
    rw [toAffineSpace_base_apply f hU v x]
    change (MvPolynomial.aeval v) (MvPolynomial.X i) ∈ (hU.primeIdealOf x).asIdeal ↔ _
    rw [aeval_X]
  have h1 : v i ∈ (hU.primeIdealOf x).asIdeal ↔ ¬ IsUnit (X.presheaf.germ U x.1 x.2 (v i)) := by
    have h := mem_basicOpen_iff_notMem_primeIdealOf hU x.2 (v i)
    rw [X.mem_basicOpen (v i) x.1 x.2] at h
    exact not_not.symm.trans (not_congr h).symm
  rw [h0, h1, mem_maximalIdeal, mem_nonunits_iff]

/-- `φ_v(x) = 0` iff every coordinate `v_i` vanishes at `x` (the coordinate systems of [Kol07, 95]
send `p` to `0`). -/
theorem toAffineSpace_base_eq_origin_iff (hU : IsAffineOpen U) (v : Fin n → Γ(X, U)) (x : U) :
    (toAffineSpace f U v).base x = origin k n ↔
      ∀ i, X.presheaf.germ U x.1 x.2 (v i) ∈ maximalIdeal (X.presheaf.stalk x.1) :=
  (eq_origin_iff_forall_X_mem k n _).trans
    (forall_congr' fun i => X_mem_toAffineSpace_base_iff f hU v x i)

/-- Two coordinate morphisms whose coordinates all vanish at `x` send `x` to the same point (the
origin). -/
theorem toAffineSpace_base_eq (hU : IsAffineOpen U) (v v' : Fin n → Γ(X, U)) (x : U)
    (hv : ∀ i, X.presheaf.germ U x.1 x.2 (v i) ∈ maximalIdeal (X.presheaf.stalk x.1))
    (hv' : ∀ i, X.presheaf.germ U x.1 x.2 (v' i) ∈ maximalIdeal (X.presheaf.stalk x.1)) :
    (toAffineSpace f U v).base x = (toAffineSpace f U v').base x :=
  ((toAffineSpace_base_eq_origin_iff f hU v x).mpr hv).trans
    ((toAffineSpace_base_eq_origin_iff f hU v' x).mpr hv').symm

end Base

/-! ### The stalks of an étale morphism -/

/-- The stalk map of an étale morphism is an unramified local homomorphism essentially of finite
type, so `𝔪_{g(y)} 𝒪_{Y,y} = 𝔪_y` [Sta, Tag 00UW]. -/
theorem map_maximalIdeal_stalkMap_of_etale {Y Z : Scheme.{u}} (g : Y ⟶ Z) [Etale g] (y : Y) :
    (maximalIdeal (Z.presheaf.stalk (g.base y))).map (g.stalkMap y).hom =
      maximalIdeal (Y.presheaf.stalk y) := by
  algebraize [(g.stalkMap y).hom]
  have : IsLocalHom (algebraMap (Z.presheaf.stalk (g.base y)) (Y.presheaf.stalk y)) :=
    inferInstanceAs <| IsLocalHom (g.stalkMap y).hom
  have : Algebra.EssFiniteType (Z.presheaf.stalk (g.base y)) (Y.presheaf.stalk y) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap g y
  have : Algebra.FormallyUnramified (Z.presheaf.stalk (g.base y)) (Y.presheaf.stalk y) := by
    rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
    exact FormallyUnramified.stalkMap g y
  exact Algebra.FormallyUnramified.map_maximalIdeal

end AlgebraicGeometry
