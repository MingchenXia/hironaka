/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Derivative.Logarithmic
import Hironaka.Algebra.Derivative.Localization
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The logarithmic derivative ideal commutes with localization

For a localization `B = M⁻¹A` of a `k`-algebra `A` and ideals `J, I` of `A`,
`D(−log (J B))(I B) = D(−log J)(I) · B`, provided `Ω_{A/k}` is finitely presented and `J` is
finitely generated (`Ideal.logDerivative_map`; `logDerivativeIter_map` for the iterates). This is
the compatibility with restriction to basic opens that makes the affine family
`U ↦ D(−log S(U))(I(U))` of `Hironaka/Scheme/IdealSheaf/Derivative/Logarithmic.lean` an ideal sheaf
(`Hironaka/Scheme/IdealSheaf/Derivative/LogarithmicSheaf.lean`); Kollár treats `D(−log S)(I)` as a
sheaf from the start ([Kol07, 87]).

* Preservation passes to the localization (`Derivation.PreservesIdeal.map_of_forall`): if
  `δ' ∘ φ = φ ∘ δ` and `δ(J) ⊆ J` then `δ'(J B) ⊆ J B`, by Leibniz on the generators `φ(J)`. So the
  extension `δ̃` of a `J`-preserving derivation (`extendToLocalization`,
  `Hironaka/Algebra/Derivative/Localization.lean`) preserves `J B`, which gives `⊇`
  (`map_logDerivative_le`).
* `⊆`: a `k`-derivation `δ'` of `B` preserving `J B` is, up to the unit `φ(s)`, the extension of a
  derivation `δ` of `A` (`exists_derivation_smul_eq`); `δ` need not preserve `J`, only its
  `M`-saturation. **Clearing denominators** (`exists_smul_preservesIdeal`): for each of the
  finitely many generators `g` of `J`, `φ(δ g) = φ(s) δ'(φ g) ∈ J B`, so `m_g · δ g ∈ J` for some
  `m_g ∈ M`; with `m = ∏ m_g`, the derivation `m δ` maps the generators into `J`, hence preserves
  `J` (Leibniz), and `φ(m δ f) = φ(m s) δ'(φ f)` with `φ(m s)` a unit. So
  `δ'(φ f) ∈ D(−log J)(I) B` for `f ∈ I`, and Leibniz extends this to `I B`
  (`logDerivative_map_le`).

Used for the logarithmic derivative ideal sheaf
(`Hironaka/Scheme/IdealSheaf/Derivative/LogarithmicSheaf.lean`), for Theorem 88 and (87.3) on
schemes (`Hironaka/Resolution/Algebraic/Kol07/Theorem88BlowUp.lean`,
`Hironaka/Scheme/BlowUpSequence/TransformLogDerivative.lean`) and for the blow-up chart
(`Hironaka/Algebra/Local/BlowUpLiftLog.lean`). The statement is not in the sources.
-/

public section

namespace Derivation

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

/-- A derivation preserves `span s` iff it maps the generators into `span s` (Leibniz). -/
theorem preservesIdeal_span_iff (δ : Derivation k A A) (s : Set A) :
    δ.PreservesIdeal (Ideal.span s) ↔ ∀ g ∈ s, δ g ∈ Ideal.span s := by
  refine ⟨fun h g hg => h g (Ideal.subset_span hg), fun h a ha => ?_⟩
  induction ha using Submodule.span_induction with
  | mem g hg => exact h g hg
  | zero => rw [map_zero]; exact Ideal.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Ideal.add_mem _ ha hb
  | smul c a ha' ha =>
    rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_right _ _ ha')

/-- If `δ'` extends `δ` along the ring map `φ` (`δ' ∘ φ = φ ∘ δ`) and `δ` preserves `J`, then `δ'`
preserves the extended ideal `J B = span (φ(J))`. -/
theorem PreservesIdeal.map_of_forall {δ : Derivation k A A} {J : Ideal A}
    (hδ : δ.PreservesIdeal J) (φ : A →+* B) (δ' : Derivation k B B)
    (h : ∀ a, δ' (φ a) = φ (δ a)) : δ'.PreservesIdeal (J.map φ) := by
  have hJ : J.map φ = Ideal.span (φ '' (J : Set A)) := rfl
  rw [hJ, preservesIdeal_span_iff]
  rintro _ ⟨a, ha, rfl⟩
  rw [h a]
  exact Ideal.subset_span ⟨δ a, hδ a ha, rfl⟩

end Derivation

namespace Ideal

open KaehlerDifferential

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra A B]
  [Algebra k B] [IsScalarTower k A B]

/-- The inclusion `D(−log J)(I) B ⊆ D(−log (J B))(I B)`: a `J`-preserving derivation of `A`
extends to a `J B`-preserving derivation of `B`. -/
theorem map_logDerivative_le (M : Submonoid A) [IsLocalization M B] (J I : Ideal A) :
    (logDerivative k J I).map (algebraMap A B) ≤
      logDerivative k (J.map (algebraMap A B)) (I.map (algebraMap A B)) := by
  rw [Ideal.map_le_iff_le_comap]
  refine logDerivative_le_iff.mpr ⟨fun f hf => Ideal.mem_comap.mpr
    (le_logDerivative _ _ (Ideal.mem_map_of_mem _ hf)), fun δ hδ f hf => ?_⟩
  rw [Ideal.mem_comap, ← δ.extendToLocalization_algebraMap M]
  exact derivation_apply_mem_logDerivative
    (hδ.map_of_forall (algebraMap A B) _ (δ.extendToLocalization_algebraMap M))
    (Ideal.mem_map_of_mem _ hf)

omit [IsScalarTower k A B] in
/-- Clearing denominators: if `δ'` preserves `J B` and `φ ∘ δ = φ(s) · δ' ∘ φ`, then for a finitely
generated `J` some multiple `m δ`, `m ∈ M`, preserves `J`. -/
theorem exists_smul_preservesIdeal (M : Submonoid A) [IsLocalization M B] {J : Ideal A}
    (hJ : J.FG) {δ' : Derivation k B B} (hδ' : δ'.PreservesIdeal (J.map (algebraMap A B)))
    {δ : Derivation k A A} {s : M}
    (h : ∀ a : A, algebraMap A B (δ a) = algebraMap A B s * δ' (algebraMap A B a)) :
    ∃ m : M, ((m : A) • δ).PreservesIdeal J := by
  classical
  obtain ⟨T, rfl⟩ := hJ
  have key : ∀ g ∈ Ideal.span (T : Set A), ∃ m : M, (m : A) * δ g ∈ Ideal.span (T : Set A) := by
    intro g hg
    have h1 : algebraMap A B (δ g) ∈ (Ideal.span (T : Set A)).map (algebraMap A B) := by
      rw [h g]
      exact Ideal.mul_mem_left _ _ (hδ' _ (Ideal.mem_map_of_mem _ hg))
    obtain ⟨⟨⟨j, hj⟩, t⟩, ht⟩ := (IsLocalization.mem_map_algebraMap_iff M B).mp h1
    rw [← map_mul, IsLocalization.eq_iff_exists M B] at ht
    obtain ⟨c, hc⟩ := ht
    refine ⟨c * t, ?_⟩
    rw [Submonoid.coe_mul, mul_assoc, mul_comm (t : A), hc]
    exact Ideal.mul_mem_left _ _ hj
  choose! m hm using key
  refine ⟨∏ g ∈ T, m g, (Derivation.preservesIdeal_span_iff _ _).mpr fun g hg => ?_⟩
  rw [Derivation.smul_apply, smul_eq_mul, Submonoid.coe_finsetProd,
    ← Finset.mul_prod_erase T (fun g => (m g : A)) hg, mul_comm (m g : A), mul_assoc]
  exact Ideal.mul_mem_left _ _ (hm g (Ideal.subset_span hg))

/-- The inclusion `D(−log (J B))(I B) ⊆ D(−log J)(I) B` for a localization `B = M⁻¹A`, `Ω_{A/k}`
finitely presented and `J` finitely generated. -/
theorem logDerivative_map_le (M : Submonoid A) [IsLocalization M B]
    [Module.FinitePresentation A (Ω[A⁄k])] {J : Ideal A} (hJ : J.FG) (I : Ideal A) :
    logDerivative k (J.map (algebraMap A B)) (I.map (algebraMap A B)) ≤
      (logDerivative k J I).map (algebraMap A B) := by
  refine logDerivative_le_iff.mpr ⟨Ideal.map_mono (le_logDerivative J I), fun δ' hδ' x hx => ?_⟩
  obtain ⟨δ, s, hδ⟩ := exists_derivation_smul_eq (k := k) (B := B) M δ'
  obtain ⟨m, hm⟩ := exists_smul_preservesIdeal M hJ hδ' hδ
  have hu : IsUnit (algebraMap A B ((m * s : M) : A)) := IsLocalization.map_units B (m * s)
  have key : ∀ f ∈ I, δ' (algebraMap A B f) ∈ (logDerivative k J I).map (algebraMap A B) := by
    intro f hf
    have h1 : algebraMap A B (((m : A) • δ) f) =
        algebraMap A B ((m * s : M) : A) * δ' (algebraMap A B f) := by
      simp only [Derivation.smul_apply, smul_eq_mul, map_mul, Submonoid.coe_mul, hδ f, mul_assoc]
    rw [← Ideal.unit_mul_mem_iff_mem _ hu, ← h1]
    exact Ideal.mem_map_of_mem _ (derivation_apply_mem_logDerivative hm hf)
  change x ∈ Ideal.span (algebraMap A B '' (I : Set A)) at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    exact key f hf
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Ideal.add_mem _ hx hy
  | smul b x hx' hx =>
    rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx)
      (Ideal.mul_mem_right _ _ (Ideal.map_mono (le_logDerivative J I) hx'))

/-- `D(−log (J B))(I B) = D(−log J)(I) B` for a localization `B = M⁻¹A` when `Ω_{A/k}` is finitely
presented and `J` is finitely generated. -/
theorem logDerivative_map (M : Submonoid A) [IsLocalization M B]
    [Module.FinitePresentation A (Ω[A⁄k])] {J : Ideal A} (hJ : J.FG) (I : Ideal A) :
    logDerivative k (J.map (algebraMap A B)) (I.map (algebraMap A B)) =
      (logDerivative k J I).map (algebraMap A B) :=
  le_antisymm (logDerivative_map_le M hJ I) (map_logDerivative_le M J I)

/-- The iterates: `D^r(−log (J B))(I B) = D^r(−log J)(I) B`. -/
theorem logDerivativeIter_map (M : Submonoid A) [IsLocalization M B]
    [Module.FinitePresentation A (Ω[A⁄k])] {J : Ideal A} (hJ : J.FG) (r : ℕ) (I : Ideal A) :
    logDerivativeIter k (J.map (algebraMap A B)) r (I.map (algebraMap A B)) =
      (logDerivativeIter k J r I).map (algebraMap A B) := by
  induction r with
  | zero => rfl
  | succ r ih => rw [logDerivativeIter_succ, logDerivativeIter_succ, ih, logDerivative_map M hJ]

end Ideal
