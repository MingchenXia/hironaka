/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.StableModification.CurvesField.DualityCurve
import Hironaka.Geometry.StableModification.CurvesField.CohomologyP1

/-!
# The projective line: `deg Ω¹_{ℙ¹} = -2`

The projective line `ℙ¹_k` with its standard charts `U = Spec k[t]`, `V = Spec k[s]`,
`U ∩ V = Spec k[t, t⁻¹]` (`s = t⁻¹`) and function field `k(t)` satisfies the hypotheses of the
numerical Serre duality of `DualityCurve` (with `f = id : ℙ¹ → ℙ¹`). Combined with
`χ(𝒪_{ℙ¹}) = 1` (`P1Model.finrank_H0`, `P1Model.finrank_H1`) this gives
`h⁰(Ω¹_{ℙ¹}) = 0`, `h¹(Ω¹_{ℙ¹}) = 1` and `deg Ω¹_{ℙ¹} = χ(Ω¹) - χ(𝒪) = -2` (the genus `0`
case of `thm:sm-omega-degree`). It also shows that the hypotheses of `Duality.finrank_H0_kaehler`
can be met.

The ring `k[s]` of the chart at infinity is the type synonym `P1.InfChart k` of `k[X]`, so that
its two algebra structures over `k[X]` (the identity, as a `k[s]`-algebra) and towards
`k[t, t⁻¹]` (`s ↦ T⁻¹`) do not clash with those of `k[t] = k[X]`.

Reference: M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010),
`references/temkin10-stable-modification/source/semi-stable.tex`, lines 1717–1741 (the degree of
`ω` on the components). Blueprint: `sm-omega-degree.tex`, `lem:sm-omega-degree-p1`.
-/

universe u

open Polynomial LaurentPolynomial Module

namespace Hironaka.StableModification.CurvesField.Duality

noncomputable section

namespace P1

variable (k : Type u) [Field k]

/-- The coordinate ring `k[s]` of the chart at infinity of `ℙ¹` (a synonym of `k[X]`). -/
def InfChart : Type u := k[X]

instance : CommRing (InfChart k) := inferInstanceAs (CommRing k[X])
instance : IsDomain (InfChart k) := inferInstanceAs (IsDomain k[X])
instance : Algebra k (InfChart k) := inferInstanceAs (Algebra k k[X])
instance : Algebra k[X] (InfChart k) := inferInstanceAs (Algebra k[X] k[X])
instance : IsScalarTower k k[X] (InfChart k) := inferInstanceAs (IsScalarTower k k[X] k[X])
instance : Module.Finite k[X] (InfChart k) := inferInstanceAs (Module.Finite k[X] k[X])
instance : Module.IsTorsionFree k[X] (InfChart k) :=
  inferInstanceAs (Module.IsTorsionFree k[X] k[X])
instance : IsIntegrallyClosed (InfChart k) := inferInstanceAs (IsIntegrallyClosed k[X])

/-- `Ω¹_{k[t]/k}` is free (on `dt`). -/
instance free_kaehler : Module.Free k[X] Ω[k[X]⁄k] :=
  Module.Free.of_equiv (KaehlerDifferential.polynomialEquiv k).symm

instance : Module.IsTorsionFree (InfChart k) Ω[InfChart k⁄k] :=
  inferInstanceAs (Module.IsTorsionFree k[X] Ω[k[X]⁄k])

instance : IsScalarTower k k[X] k[T;T⁻¹] := IsScalarTower.of_algebraMap_eq fun c => by
  rw [algebraMap_eq_toLaurent, ← Polynomial.C_eq_algebraMap, Polynomial.toLaurent_C]
  rfl

/-- `k[s] → k[t, t⁻¹]`, `s ↦ t⁻¹`. -/
instance algebraInf : Algebra (InfChart k) k[T;T⁻¹] :=
  RingHom.toAlgebra (R := InfChart k)
    ((invert (R := k)).toRingEquiv.toRingHom.comp (toLaurent (R := k)))

lemma algebraMap_inf (p : InfChart k) :
    algebraMap (InfChart k) k[T;T⁻¹] p = invert (toLaurent (R := k) p) := rfl

instance : IsScalarTower k (InfChart k) k[T;T⁻¹] := IsScalarTower.of_algebraMap_eq fun c => by
  rw [algebraMap_inf]
  change algebraMap k k[T;T⁻¹] c = invert (toLaurent (Polynomial.C c))
  rw [Polynomial.toLaurent_C, invert_C]
  rfl

instance : IsLocalization.Away (algebraMap k[X] k[X] X) k[T;T⁻¹] :=
  inferInstanceAs (IsLocalization.Away (X : k[X]) k[T;T⁻¹])

instance : IsLocalization.Away (algebraMap k[X] (InfChart k) X) k[T;T⁻¹] := by
  refine (isLocalization_iff (Submonoid.powers (algebraMap k[X] (InfChart k) X)) k[T;T⁻¹]).mpr ?_
  refine ⟨?_, fun z => ?_, fun {x y} h => ⟨1, ?_⟩⟩
  · rintro ⟨_, n, rfl⟩
    rw [map_pow]
    refine IsUnit.pow n ?_
    change IsUnit (invert (toLaurent (R := k) X))
    rw [Polynomial.toLaurent_X, invert_T]
    exact isUnit_T _
  · obtain ⟨n, f, hf⟩ := exists_T_pow (invert z)
    refine ⟨⟨f, ⟨_, n, rfl⟩⟩, ?_⟩
    change z * invert (toLaurent ((X : k[X]) ^ n)) = invert (toLaurent f)
    rw [hf, map_mul, involutive_invert, Polynomial.toLaurent_X_pow, invert_T]
  · rw [algebraMap_inf, algebraMap_inf] at h
    have h' := Polynomial.toLaurent_injective (invert.injective h)
    simp only [OneMemClass.coe_one, one_mul]
    exact h'

/-- `k[t, t⁻¹] → k(t)` (a scoped instance: Mathlib has no such algebra structure). -/
scoped instance algebraLaurent : Algebra k[T;T⁻¹] (RatFunc k) :=
  (laurentToField (RatFunc k) (k := k)).toAlgebra

lemma algebraMap_laurent (f : k[T;T⁻¹]) :
    algebraMap k[T;T⁻¹] (RatFunc k) f = laurentToField (RatFunc k) f := rfl

scoped instance : IsFractionRing k[T;T⁻¹] (RatFunc k) := by
  have : FaithfulSMul k[T;T⁻¹] (RatFunc k) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (laurentToField_injective (RatFunc k))
  refine IsFractionRing.of_field _ _ fun z => ?_
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := k[X]) z
  exact ⟨toLaurent a, toLaurent b, by
    rw [algebraMap_laurent, algebraMap_laurent, laurentToField_toLaurent,
      laurentToField_toLaurent]⟩

/-- `k[s] → k(t)`, `s ↦ t⁻¹`. -/
instance algebraInfField : Algebra (InfChart k) (RatFunc k) :=
  RingHom.toAlgebra (R := InfChart k)
    (aeval (R := k) (algebraMap k[X] (RatFunc k) X)⁻¹).toRingHom

scoped instance : IsScalarTower k[X] k[T;T⁻¹] (RatFunc k) :=
  IsScalarTower.of_algebraMap_eq fun p => by
    rw [algebraMap_laurent, algebraMap_eq_toLaurent, laurentToField_toLaurent]

scoped instance : IsScalarTower (InfChart k) k[T;T⁻¹] (RatFunc k) :=
  IsScalarTower.of_algebraMap_eq fun p =>
    (laurentToField_invert_toLaurent (RatFunc k) (p : k[X])).symm

scoped instance : IsScalarTower k k[T;T⁻¹] (RatFunc k) := IsScalarTower.of_algebraMap_eq fun c => by
  rw [algebraMap_laurent, show algebraMap k k[T;T⁻¹] c = LaurentPolynomial.C c from rfl,
    laurentToField_C]

instance : IsScalarTower k (InfChart k) (RatFunc k) := IsScalarTower.of_algebraMap_eq fun c => by
  change algebraMap k (RatFunc k) c =
    aeval (R := k) (algebraMap k[X] (RatFunc k) X)⁻¹ (algebraMap k k[X] c)
  exact ((aeval (R := k) (algebraMap k[X] (RatFunc k) X)⁻¹).commutes c).symm

/-- `t · s = 1` on `U ∩ V`. -/
lemma hts : algebraMap k[X] k[T;T⁻¹] (algebraMap k[X] k[X] X) *
    algebraMap (InfChart k) k[T;T⁻¹] (algebraMap k[X] (InfChart k) X) = 1 := by
  change toLaurent (R := k) X * invert (toLaurent (R := k) X) = 1
  rw [Polynomial.toLaurent_X, invert_T, ← T_add, add_neg_cancel, T_zero]

lemma γ_zero (w : k[T;T⁻¹]) : P1Model.γ k 0 w = w := by
  change T (-0) * w = w
  rw [neg_zero, T_zero, one_mul]

/-- The two-chart complex of `𝒪_{ℙ¹}` is the model complex of `P1Model` (`H⁰`). -/
def H0StructureEquiv : H0 (P1Model.ρ₀ k) (P1Model.ρInf k) (P1Model.γ k 0) ≃ₗ[k]
    H0 (resO k k[X] k[T;T⁻¹]) (resO k (InfChart k) k[T;T⁻¹]) LinearMap.id :=
  H0Congr (LinearEquiv.refl k k[X]) (LinearEquiv.refl k k[X] : k[X] ≃ₗ[k] InfChart k)
    (LinearEquiv.refl k k[T;T⁻¹]) (fun _ => rfl) (fun _ => rfl) (fun w => γ_zero k w)

/-- The two-chart complex of `𝒪_{ℙ¹}` is the model complex of `P1Model` (`H¹`). -/
def H1StructureEquiv : H1 (P1Model.ρ₀ k) (P1Model.ρInf k) (P1Model.γ k 0) ≃ₗ[k]
    H1 (resO k k[X] k[T;T⁻¹]) (resO k (InfChart k) k[T;T⁻¹]) LinearMap.id :=
  H1Congr (LinearEquiv.refl k k[X]) (LinearEquiv.refl k k[X] : k[X] ≃ₗ[k] InfChart k)
    (LinearEquiv.refl k k[T;T⁻¹]) (fun _ => rfl) (fun _ => rfl) (fun w => γ_zero k w)

/-- `h⁰(ℙ¹, 𝒪) = 1`. -/
theorem finrank_H0_structure :
    finrank k (H0 (resO k k[X] k[T;T⁻¹]) (resO k (InfChart k) k[T;T⁻¹]) LinearMap.id) = 1 := by
  have h := P1Model.finrank_H0 k 0
  rw [(H0StructureEquiv k).finrank_eq] at h
  norm_num at h
  exact_mod_cast h

/-- `h¹(ℙ¹, 𝒪) = 0`. -/
theorem finrank_H1_structure :
    finrank k (H1 (resO k k[X] k[T;T⁻¹]) (resO k (InfChart k) k[T;T⁻¹]) LinearMap.id) = 0 := by
  have h := P1Model.finrank_H1 k 0
  rw [(H1StructureEquiv k).finrank_eq] at h
  norm_num at h
  exact_mod_cast h

variable [IsAlgClosed k]

/-- `h⁰(ℙ¹, Ω¹) = 0`. -/
theorem finrank_H0_kaehler :
    finrank k (H0 (resΩ k k[X] k[T;T⁻¹]) (resΩ k (InfChart k) k[T;T⁻¹]) LinearMap.id) = 0 := by
  rw [Duality.finrank_H0_kaehler (RatFunc k) (RatFunc k) (hts k), finrank_H1_structure]

/-- `h¹(ℙ¹, Ω¹) = 1`. -/
theorem finrank_H1_kaehler :
    finrank k (H1 (resΩ k k[X] k[T;T⁻¹]) (resΩ k (InfChart k) k[T;T⁻¹]) LinearMap.id) = 1 := by
  rw [Duality.finrank_H1_kaehler (RatFunc k) (RatFunc k) (hts k), finrank_H0_structure]

/-- **`deg Ω¹_{ℙ¹} = -2`** (the genus `0` case): `χ(Ω¹_{ℙ¹}) - χ(𝒪_{ℙ¹}) = -2`. -/
theorem deg_kaehler :
    ((finrank k (H0 (resΩ k k[X] k[T;T⁻¹]) (resΩ k (InfChart k) k[T;T⁻¹]) LinearMap.id) : ℤ) -
        finrank k (H1 (resΩ k k[X] k[T;T⁻¹]) (resΩ k (InfChart k) k[T;T⁻¹]) LinearMap.id)) -
      ((finrank k (H0 (resO k k[X] k[T;T⁻¹]) (resO k (InfChart k) k[T;T⁻¹]) LinearMap.id) : ℤ) -
        finrank k (H1 (resO k k[X] k[T;T⁻¹]) (resO k (InfChart k) k[T;T⁻¹]) LinearMap.id)) =
      -2 := by
  rw [finrank_H0_kaehler, finrank_H1_kaehler, finrank_H0_structure, finrank_H1_structure]
  norm_num

end P1

end

end Hironaka.StableModification.CurvesField.Duality
