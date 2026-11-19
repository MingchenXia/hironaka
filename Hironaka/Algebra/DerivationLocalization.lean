/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.GroupTheory.MonoidLocalization.Basic
public import Mathlib.RingTheory.OreLocalization.Ring
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.Localization.Defs
import Mathlib.Tactic.LinearCombination

/-!
# Extending a derivation to a localization

A derivation `D : A → A` over `k` extends to the localization `M⁻¹A` by the quotient rule
`D (a / s) = (s · D a - a · D s) / s²`, and the extension is the unique derivation of `M⁻¹A`
compatible with `D` on `A`. The sources use this silently: Włodarczyk notes that the derivations
`∂/∂uᵢ` of a local ring extend to the field of rational functions [Wlo05, Lemma 2.6.3, proof], and
Kollár's chart formulas for the transform of a marked ideal [Kol07, Definition 60] are
computations in the localization at the exceptional coordinate `xᵣ`. Mathlib has no such
extension, so it is built here for an arbitrary submonoid `M`; the localization away from one
element `r` is the case `M = Submonoid.powers r`.

## Main declarations

* `Derivation.localization M D : Derivation k (Localization M) (Localization M)`, with
  `Derivation.localizationFun_mk` giving its value on `Localization.mk a s`.
* `Derivation.localization_algebraMap`: compatibility with `D` on the image of `A`.
* `Derivation.eq_localization_of_algebraMap`: uniqueness.
* `Derivation.localization_comm`: the extensions of commuting derivations commute.

## Proof

Well-definedness on fractions is the only computation: if `u (t a) = u (s c)` for some `u ∈ M`,
then applying `D` and multiplying out shows `u² t² (s D a - a D s) = u² s² (t D c - c D t)`,
so the two candidate values agree in `M⁻¹A`.  Additivity, `k`-linearity and the Leibniz rule are
polynomial identities checked after clearing denominators.  Uniqueness: a derivation of `M⁻¹A`
agreeing with `D` on `A` is determined on `1/s` by `D'(1/s) = -(1/s)² D'(s)`
(`Derivation.leibniz_of_mul_eq_one`) and hence on every `a/s`.
-/

@[expose] public section

namespace Derivation

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A] (M : Submonoid A)
  (D : Derivation k A A)

/-- The value of the extended derivation on the fraction `a / s`: `(s · D a - a · D s) / s²`,
the quotient rule. -/
noncomputable def localizationFun (x : Localization M) : Localization M :=
  Localization.liftOn x (fun a s => Localization.mk (↑s * D a - a * D ↑s) (s * s))
    fun {a c} {s t} h => by
      rw [Localization.r_iff_exists] at h
      obtain ⟨u, hu⟩ := h
      rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      refine ⟨u * u, ?_⟩
      have E := congrArg D hu
      simp only [Derivation.leibniz, smul_eq_mul] at E
      push_cast
      linear_combination (↑u * ↑s * ↑t) * E -
        (↑u * ↑t * D ↑s + ↑u * ↑s * D ↑t + ↑s * ↑t * D ↑u) * hu

@[simp]
theorem localizationFun_mk (a : A) (s : M) :
    D.localizationFun M (Localization.mk a s) =
      Localization.mk (↑s * D a - a * D ↑s) (s * s) :=
  Localization.liftOn_mk _ _ _ _

/-- **Extension of a derivation to a localization**: the derivation
`a / s ↦ (s · D a - a · D s) / s²` of `M⁻¹A`. Not stated in the sources, which use it silently
[Wlo05, Lemma 2.6.3, proof]. -/
noncomputable def localization : Derivation k (Localization M) (Localization M) where
  toFun := D.localizationFun M
  map_add' x y := by
    refine Localization.induction_on₂ x y fun ⟨a, s⟩ ⟨c, t⟩ => ?_
    simp only [Localization.add_mk, localizationFun_mk]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [Submonoid.coe_mul, map_add, Derivation.leibniz, smul_eq_mul]
    push_cast
    ring
  map_smul' r x := by
    refine Localization.induction_on x fun ⟨a, s⟩ => ?_
    simp only [Localization.smul_mk, localizationFun_mk, RingHom.id_apply, D.map_smul, smul_sub,
      mul_smul_comm, smul_mul_assoc]
  map_one_eq_zero' := by
    change D.localizationFun M 1 = 0
    rw [← Localization.mk_one, localizationFun_mk]
    simp only [Submonoid.coe_one, map_one_eq_zero, mul_zero, sub_self, mul_one]
    rw [Localization.mk_one_eq_algebraMap, map_zero]
  leibniz' x y := by
    refine Localization.induction_on₂ x y fun ⟨a, s⟩ ⟨c, t⟩ => ?_
    change D.localizationFun M (Localization.mk a s * Localization.mk c t) =
      Localization.mk a s • D.localizationFun M (Localization.mk c t) +
        Localization.mk c t • D.localizationFun M (Localization.mk a s)
    simp only [Localization.mk_mul, localizationFun_mk, smul_eq_mul, Localization.add_mk]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [Submonoid.coe_mul, Derivation.leibniz, smul_eq_mul]
    push_cast
    ring

@[simp]
theorem localization_mk (a : A) (s : M) :
    D.localization M (Localization.mk a s) = Localization.mk (↑s * D a - a * D ↑s) (s * s) :=
  localizationFun_mk M D a s

/-- The extension agrees with `D` on the image of `A`. -/
@[simp]
theorem localization_algebraMap (a : A) :
    D.localization M (algebraMap A (Localization M) a) = algebraMap A (Localization M) (D a) := by
  rw [← Localization.mk_one_eq_algebraMap, ← Localization.mk_one_eq_algebraMap, localization_mk]
  simp

/-- Uniqueness: a derivation of `M⁻¹A` that agrees with `D` on `A` is the extension. -/
theorem eq_localization_of_algebraMap (D' : Derivation k (Localization M) (Localization M))
    (h : ∀ a, D' (algebraMap A (Localization M) a) = algebraMap A (Localization M) (D a)) :
    D' = D.localization M := by
  ext x
  refine Localization.induction_on x fun ⟨a, s⟩ => ?_
  have hs : Localization.mk (1 : A) s * algebraMap A (Localization M) (s : A) = 1 := by
    rw [← Localization.mk_one_eq_algebraMap, Localization.mk_mul, one_mul, mul_one,
      Localization.mk_self]
  have h1 : D' (Localization.mk 1 s) =
      -(Localization.mk 1 s) ^ 2 • algebraMap A (Localization M) (D s) := by
    rw [D'.leibniz_of_mul_eq_one hs, h]
  have hx : Localization.mk a s = algebraMap A (Localization M) a * Localization.mk 1 s := by
    rw [← Localization.mk_one_eq_algebraMap, Localization.mk_mul, mul_one, one_mul]
  have hD' : D' (Localization.mk a s) =
      algebraMap A (Localization M) a • (-(Localization.mk 1 s) ^ 2 •
        algebraMap A (Localization M) (D s)) +
        Localization.mk 1 s • algebraMap A (Localization M) (D a) := by
    rw [hx, D'.leibniz, h1, h]
  rw [hD', localization_mk]
  simp only [← Localization.mk_one_eq_algebraMap, smul_eq_mul, pow_two, Localization.mk_mul,
    Localization.neg_mk, Localization.add_mk]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  push_cast
  ring

/-- The extension of the zero derivation is zero. -/
theorem zero_localization : (0 : Derivation k A A).localization M = 0 := by
  symm
  apply Derivation.eq_localization_of_algebraMap
  intro a
  simp

/-- The extensions of two commuting derivations commute: their commutator is a derivation of
`M⁻¹A` vanishing on `A`, hence zero by uniqueness. -/
theorem localization_comm (D₁ D₂ : Derivation k A A) (h : ∀ a, D₁ (D₂ a) = D₂ (D₁ a))
    (z : Localization M) :
    D₁.localization M (D₂.localization M z) = D₂.localization M (D₁.localization M z) := by
  have hcomm : ⁅D₁.localization M, D₂.localization M⁆ = (0 : Derivation k A A).localization M := by
    apply Derivation.eq_localization_of_algebraMap
    intro a
    rw [Derivation.commutator_apply, Derivation.localization_algebraMap,
      Derivation.localization_algebraMap, Derivation.localization_algebraMap,
      Derivation.localization_algebraMap, h a, sub_self, Derivation.zero_apply, map_zero]
  have hz := congrArg (fun D : Derivation k (Localization M) (Localization M) => D z) hcomm
  rw [zero_localization] at hz
  simpa [Derivation.commutator_apply, sub_eq_zero] using hz

end Derivation
