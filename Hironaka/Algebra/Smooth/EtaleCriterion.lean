/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.RingTheory.RingHom.Etale

/-!
# An étale criterion through the Jacobi–Zariski sequence

For algebras `k → A → S` with `S` formally smooth over `k`, the map `A → S` is formally étale as
soon as the base-change map `S ⊗_A Ω[A⁄k] → Ω[S⁄k]` is bijective ([Sta, Tags 00S2, 00UO]):

* surjectivity gives `Ω[S⁄A] = 0` (the exact sequence `S ⊗_A Ω[A⁄k] → Ω[S⁄k] → Ω[S⁄A] → 0`,
  [Sta, Tag 00RS]), i.e. `A → S` is formally unramified;
* injectivity gives `H¹(L_{S/A}) = 0` through the Jacobi–Zariski sequence
  `H¹(L_{S/k}) → H¹(L_{S/A}) → S ⊗_A Ω[A⁄k] → Ω[S⁄k]` [Sta, Tag 00S2]: `H¹(L_{S/k}) = 0` because
  `S/k` is formally smooth, and the connecting map is zero because the next map is injective;
  with `Ω[S⁄A] = 0` projective, `A → S` is formally smooth (Mathlib's definition of formal
  smoothness, [Sta, Tag 00TI]).

Finite presentation of `S/A` follows from that of `S/k` when `A/k` is of finite type, so `A → S` is
étale (`Algebra.Etale`). The application (`etale_aeval_of_span_eq_top`): `A = k[t_0, …, t_{n-1}]`
and `t_i ↦ v_i ∈ S` where `Ω[S⁄k]` is free of rank `n` and the `d v_i` generate it; the base-change
map is then a surjection `S^n → S^n` between free modules of the same rank, hence bijective
(`OrzechProperty.bijective_of_surjective_of_finrank_le`). This replaces the flatness argument of
the obvious proof of [Sta, Tag 054L] in given coordinates, which would need the flatness of
`k[t] → S` before étaleness is known. Used to produce étale coordinates on a smooth scheme
(`Hironaka/Scheme/Smooth/EtaleCoordinates.lean`).
-/

public section

namespace Algebra

open KaehlerDifferential _root_.TensorProduct

universe u

section Criterion

variable (k A S : Type u) [CommRing k] [CommRing A] [CommRing S] [Algebra k A] [Algebra k S]
  [Algebra A S] [IsScalarTower k A S]

/-- `Ω[S⁄A] → Ω[S⁄A]`, the map induced by the identity of `S`, is surjective (it is the
identity on the generators `d s`). -/
theorem surjective_map_self : Function.Surjective (KaehlerDifferential.map k A S S) := by
  rw [← LinearMap.range_eq_top, ← top_le_iff, ← KaehlerDifferential.span_range_derivation A S,
    Submodule.span_le]
  rintro _ ⟨s, rfl⟩
  exact ⟨KaehlerDifferential.D k S s, by simp [KaehlerDifferential.map_D]⟩

/-- If `S ⊗_A Ω[A⁄k] → Ω[S⁄k]` is surjective then `Ω[S⁄A] = 0`, i.e. `A → S` is formally
unramified [Sta, Tag 00RS]. -/
theorem formallyUnramified_of_surjective_mapBaseChange
    (h : Function.Surjective (mapBaseChange k A S)) : Algebra.FormallyUnramified A S := by
  refine ⟨subsingleton_of_forall_eq 0 fun w => ?_⟩
  obtain ⟨u, rfl⟩ := surjective_map_self k A S w
  obtain ⟨t, rfl⟩ := h u
  exact (KaehlerDifferential.exact_mapBaseChange_map k A S).apply_apply_eq_zero t

/-- If `S` is formally smooth over `k` and `S ⊗_A Ω[A⁄k] → Ω[S⁄k]` is bijective, then `S` is
formally smooth over `A` (the Jacobi–Zariski sequence, [Sta, Tags 00S2, 00TI]). -/
theorem formallySmooth_of_bijective_mapBaseChange [Algebra.FormallySmooth k S]
    (h : Function.Bijective (mapBaseChange k A S)) : Algebra.FormallySmooth A S := by
  have hunr := formallyUnramified_of_surjective_mapBaseChange k A S h.2
  refine ⟨Module.Projective.of_free, subsingleton_of_forall_eq 0 fun x => ?_⟩
  have h1 := Algebra.H1Cotangent.exact_map_δ k A S
  have h2 := Algebra.H1Cotangent.exact_δ_mapBaseChange k A S
  have hδ : Algebra.H1Cotangent.δ k A S x = 0 :=
    h.1 (by rw [map_zero]; exact h2.apply_apply_eq_zero x)
  obtain ⟨y, rfl⟩ := (h1 x).mp hδ
  rw [Subsingleton.elim y 0, map_zero]

/-- The étale criterion: `A → S` is étale when `S` is smooth over `k`, `A` is of finite type over
`k`, and `S ⊗_A Ω[A⁄k] → Ω[S⁄k]` is bijective. -/
theorem etale_of_bijective_mapBaseChange [Algebra.FormallySmooth k S]
    [Algebra.FinitePresentation k S] [Algebra.FiniteType k A]
    (h : Function.Bijective (mapBaseChange k A S)) : Algebra.Etale A S where
  formallyEtale := by
    have := formallyUnramified_of_surjective_mapBaseChange k A S h.2
    have := formallySmooth_of_bijective_mapBaseChange k A S h
    exact Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth
  finitePresentation := Algebra.FinitePresentation.of_restrict_scalars_finitePresentation k A S

end Criterion

section Polynomial

variable {k S : Type u} [CommRing k] [CommRing S] [Algebra k S] {n : ℕ} (v : Fin n → S)

/-- If `Ω[S⁄k]` is free of rank `n` and the differentials of `v_0, …, v_{n-1} ∈ S` generate it, then
`k[t_0, …, t_{n-1}] → S`, `t_i ↦ v_i`, is étale (the argument of [Sta, Tag 054L] in given
coordinates). -/
theorem etale_aeval_of_span_eq_top [Nontrivial S] [Algebra.FormallySmooth k S]
    [Algebra.FinitePresentation k S] [Module.Free S Ω[S⁄k]] [Module.Finite S Ω[S⁄k]]
    (hrank : Module.finrank S Ω[S⁄k] = n)
    (hspan : Submodule.span S (Set.range fun i => D k S (v i)) = ⊤) :
    (MvPolynomial.aeval (R := k) v).toRingHom.Etale := by
  let _ : Algebra (MvPolynomial (Fin n) k) S :=
    (MvPolynomial.aeval (R := k) v).toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin n) k) S :=
    IsScalarTower.of_algebraMap_eq fun c => by
      change algebraMap k S c = (MvPolynomial.aeval v) (algebraMap k (MvPolynomial (Fin n) k) c)
      rw [MvPolynomial.algebraMap_eq, MvPolynomial.aeval_C]
  change Algebra.Etale (MvPolynomial (Fin n) k) S
  set A := MvPolynomial (Fin n) k
  -- the base-change map sends the basis `1 ⊗ d t_i` of `S ⊗_A Ω[A⁄k]` to `d v_i`
  let b : Module.Basis (Fin n) S (S ⊗[A] Ω[A⁄k]) :=
    (KaehlerDifferential.mvPolynomialBasis k (Fin n)).baseChange S
  have hb : ∀ i, mapBaseChange k A S (b i) = D k S (v i) := by
    intro i
    rw [Module.Basis.baseChange_apply, KaehlerDifferential.mvPolynomialBasis_apply,
      mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
    exact congrArg (D k S) (MvPolynomial.aeval_X v i)
  have hsurj : Function.Surjective (mapBaseChange k A S) := by
    rw [← LinearMap.range_eq_top, ← top_le_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨b i, hb i⟩
  have hfin : Module.Finite S (S ⊗[A] Ω[A⁄k]) := Module.Finite.of_basis b
  have hrk : Module.finrank S (S ⊗[A] Ω[A⁄k]) = n := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hbij : Function.Bijective (mapBaseChange k A S) :=
    OrzechProperty.bijective_of_surjective_of_finrank_le _ hsurj (by rw [hrk, hrank])
  exact etale_of_bijective_mapBaseChange k A S hbij

end Polynomial

end Algebra
