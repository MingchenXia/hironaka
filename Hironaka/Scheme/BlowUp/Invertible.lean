/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Invertible ideals

Invertibility of ideals and of ideal sheaves is the library's notion of "effective Cartier
divisor", in the form the blow-up construction uses: a morphism `f : Y ⟶ X` is *admissible* for an
ideal sheaf `I` when `(I.comap f).IsInvertible`, that is, when the inverse image of the subscheme
of `I` is an effective Cartier divisor on `Y` [Sta, Tag 0806]. An ideal sheaf is invertible
(`AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible`) when it is generated on an affine
neighbourhood of every point by a nonzerodivisor [Sta, Tag 01WS]; this file defines the ring-level
notion in the same local form and proves its algebra.

## Main declarations

* `Ideal.IsInvertible J` [Sta, Tags 01WR and 01WS]; [Hau14, Definition 4.3]: an ideal `J ⊆ A` is
  invertible if for every prime `𝔭` of `A` there are `s ∉ 𝔭` and `a ∈ J` with `J A_s = a A_s` and
  `a` a nonzerodivisor of `A_s`.
* `Ideal.IsRegularGeneratorIn J B a`: the local datum "`a` generates `J B` and is a nonzerodivisor
  of `B`", with its transport lemmas (`of_algEquiv`, `of_isLocalization`,
  `of_isLocalization_away_mul`): the datum passes along `A`-algebra isomorphisms and along
  further localizations.
* `Ideal.isInvertible_top`, `Ideal.IsInvertible.mul`, `Ideal.IsInvertible.map_away`
  (localization stability), `Ideal.IsInvertible.of_mul` (factors of an invertible ideal are
  invertible).

## The arguments

*Products.*  At a prime `𝔭`, with `J₁ A_{s₁} = (a₁)` and `J₂ A_{s₂} = (a₂)`, pass to `A_{s₁ s₂}`:
both data survive (localization preserves nonzerodivisors), and
`(J₁ J₂) A_{s₁s₂} = (a₁)(a₂) = (a₁ a₂)` with `a₁ a₂` a nonzerodivisor.

*Localization.*  A prime `𝔮` of `A_s` lies over a prime `𝔭 ∌ s` of `A`; the datum of `J` at `𝔭`,
in `A_{s'}`, survives in `(A_s)_{s'} = A_{s s'}`, which is the required neighbourhood of `𝔮`.

*Factors* (the argument of [Hau14, Theorem 4.18, proof (c)], run on a neighbourhood).  Let
`(J₁ J₂) A_s = (g)` with `g` a nonzerodivisor, `𝔮` the prime of `A_s` over `𝔭`.  Write
`g = ∑ aᵢ bᵢ` with `aᵢ ∈ J₁ A_s`, `bᵢ ∈ J₂ A_s`; each `aᵢ bᵢ = tᵢ g`, so `∑ tᵢ = 1` after
cancelling `g`, and some `tᵢ ∉ 𝔮`.  Localizing further at `tᵢ`, `aᵢ bᵢ` is a unit multiple of `g`,
hence a nonzerodivisor, so `aᵢ` and `bᵢ` are; and for `x ∈ J₁`, `x bᵢ ∈ (g) = (aᵢ bᵢ)` gives
`x = r aᵢ` by cancelling `bᵢ`.  So `J₁ = (aᵢ)` with `aᵢ` a nonzerodivisor on the neighbourhood
`D(s tᵢ)`, which is the form of the definition (the fraction `aᵢ` is a unit multiple of an
element of `J₁`, and `tᵢ` of an element of `A`).

## Conventions

"Nonzerodivisor" is `nonZeroDivisors` (multiplication by the element is injective), never
`≠ 0`: on the zero ring every element is a nonzerodivisor, so the unit ideal and the zero ring
are covered without special cases.  The condition is existential at each point (a neighbourhood
exists), not a condition on every affine open containing the point; the equivalence with the
latter is proved in `Hironaka.Scheme.BlowUp.InvertibleSheaf`.

## Boundary cases

Every ideal of the zero ring is invertible (no primes).  The unit ideal is invertible (`s = 1`,
`a = 1`).  The zero ideal of a nonzero ring is not: its only element `0` is a nonzerodivisor of
`A_s` only when `A_s = 0`, i.e. `s` nilpotent, which `s ∉ 𝔭` forbids.  On the empty scheme every
ideal sheaf is invertible; `⊤` is invertible on every scheme.

## Namespace

The predicates extend Mathlib's `Ideal`, so they live in Mathlib's namespace (dot notation
`J.IsInvertible`), as the invertibility of ideal sheaves lives in `IdealSheafData`
(`(I.comap f).IsInvertible`).
-/

@[expose] public section

universe u v w

/-- An ideal `J ⊆ A` is *invertible* (locally principal with a nonzerodivisor generator) if for
every prime `𝔭` there are `s ∉ 𝔭` and `a ∈ J` such that `J A_s = a A_s` and the image of `a` is a
nonzerodivisor of `A_s` — the local characterisation of [Sta, Tags 01WR and 01WS] taken as the
definition; [Hau14, Definition 4.3]. -/
def Ideal.IsInvertible {A : Type u} [CommRing A] (J : Ideal A) : Prop :=
  ∀ p : PrimeSpectrum A, ∃ s ∉ p.asIdeal, ∃ a ∈ J,
    J.map (algebraMap A (Localization.Away s)) =
        Ideal.span {algebraMap A (Localization.Away s) a} ∧
      algebraMap A (Localization.Away s) a ∈ nonZeroDivisors (Localization.Away s)

namespace AlgebraicGeometry

/-- A ring isomorphism preserves nonzerodivisors. -/
theorem map_mem_nonZeroDivisors_of_ringEquiv {B : Type v} {C : Type w} [CommRing B] [CommRing C]
    (e : B ≃+* C) {b : B} (hb : b ∈ nonZeroDivisors B) : e b ∈ nonZeroDivisors C := by
  rw [mem_nonZeroDivisors_iff] at hb ⊢
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · have h1 : b * e.symm x = 0 :=
      e.injective (by rw [map_mul, e.apply_symm_apply, map_zero]; exact hx)
    rw [← e.apply_symm_apply x, hb.1 _ h1, map_zero]
  · have h1 : e.symm x * b = 0 :=
      e.injective (by rw [map_mul, e.apply_symm_apply, map_zero]; exact hx)
    rw [← e.apply_symm_apply x, hb.2 _ h1, map_zero]

end AlgebraicGeometry

namespace Ideal

variable {A : Type u} [CommRing A]

/-- The local datum of invertibility (the condition on one basic open): `a` generates the
extended ideal `J B` and is a nonzerodivisor of `B`. -/
def IsRegularGeneratorIn (J : Ideal A) (B : Type v) [CommRing B] [Algebra A B] (a : A) : Prop :=
  J.map (algebraMap A B) = Ideal.span {algebraMap A B a} ∧
    algebraMap A B a ∈ nonZeroDivisors B

theorem isInvertible_iff_forall_exists (J : Ideal A) :
    J.IsInvertible ↔ ∀ p : PrimeSpectrum A, ∃ s ∉ p.asIdeal, ∃ a ∈ J,
      J.IsRegularGeneratorIn (Localization.Away s) a :=
  Iff.rfl

namespace IsRegularGeneratorIn

variable {J : Ideal A} {a : A}

/-- The datum passes along `A`-algebra isomorphisms. -/
theorem of_algEquiv {B : Type v} {C : Type w} [CommRing B] [CommRing C] [Algebra A B]
    [Algebra A C] (e : B ≃ₐ[A] C) (h : J.IsRegularGeneratorIn B a) :
    J.IsRegularGeneratorIn C a := by
  obtain ⟨h₁, h₂⟩ := h
  have he : algebraMap A C = (e : B →+* C).comp (algebraMap A B) := by
    ext x; simp
  refine ⟨?_, ?_⟩
  · rw [he, ← Ideal.map_map, h₁, Ideal.map_span, Set.image_singleton, RingHom.comp_apply]
  · rw [he, RingHom.comp_apply]
    exact AlgebraicGeometry.map_mem_nonZeroDivisors_of_ringEquiv e.toRingEquiv h₂

/-- The datum passes to a further localization: if `C` is a localization of the `A`-algebra `B`,
the image of `a` still generates `J C` and is still a nonzerodivisor. -/
theorem of_isLocalization {B : Type v} {C : Type w} [CommRing B] [CommRing C] [Algebra A B]
    [Algebra B C] [Algebra A C] [IsScalarTower A B C] (M : Submonoid B) [IsLocalization M C]
    (h : J.IsRegularGeneratorIn B a) : J.IsRegularGeneratorIn C a := by
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨?_, ?_⟩
  · rw [IsScalarTower.algebraMap_eq A B C, ← Ideal.map_map, h₁, Ideal.map_span,
      Set.image_singleton, RingHom.comp_apply]
  · rw [IsScalarTower.algebraMap_apply A B C]
    exact IsLocalization.nonZeroDivisors_le_comap M C h₂

/-- The datum in `A_s` passes to every localization of `A` away from `s * t`. -/
theorem of_isLocalization_away_mul {s t : A}
    (h : J.IsRegularGeneratorIn (Localization.Away s) a) (C : Type w) [CommRing C] [Algebra A C]
    [IsLocalization.Away (s * t) C] : J.IsRegularGeneratorIn C a := by
  have : IsLocalization.Away (t * s)
      (Localization.Away (algebraMap A (Localization.Away s) t)) :=
    IsLocalization.Away.mul (Localization.Away s) _ s t
  have : IsLocalization.Away (t * s) C := by rw [mul_comm t s]; infer_instance
  have hC' : J.IsRegularGeneratorIn (Localization.Away (algebraMap A (Localization.Away s) t)) a :=
    of_isLocalization (Submonoid.powers (algebraMap A (Localization.Away s) t)) h
  exact of_algEquiv (IsLocalization.algEquiv (Submonoid.powers (t * s)) _ C) hC'

end IsRegularGeneratorIn

/-- The unit ideal is invertible (`s = 1`, `a = 1`). -/
theorem isInvertible_top : (⊤ : Ideal A).IsInvertible := fun p =>
  ⟨1, (Ideal.ne_top_iff_one _).mp p.isPrime.ne_top, 1, trivial, by
    rw [Ideal.map_top, map_one, Ideal.span_singleton_one], by rw [map_one]; exact one_mem _⟩

/-- A product of invertible ideals is invertible: multiply the local generators on the common
neighbourhood `D(s₁ s₂)`. -/
theorem IsInvertible.mul {J₁ J₂ : Ideal A} (h₁ : J₁.IsInvertible) (h₂ : J₂.IsInvertible) :
    (J₁ * J₂).IsInvertible := by
  intro p
  obtain ⟨s₁, hs₁, a₁, ha₁, hg₁⟩ := h₁ p
  obtain ⟨s₂, hs₂, a₂, ha₂, hg₂⟩ := h₂ p
  refine ⟨s₁ * s₂, fun h => (p.isPrime.mem_or_mem h).elim hs₁ hs₂, a₁ * a₂,
    Ideal.mul_mem_mul ha₁ ha₂, ?_⟩
  have : IsLocalization.Away (s₂ * s₁) (Localization.Away (s₁ * s₂)) := by
    rw [mul_comm s₂ s₁]; infer_instance
  have g₁ := IsRegularGeneratorIn.of_isLocalization_away_mul (t := s₂) hg₁
    (Localization.Away (s₁ * s₂))
  have g₂ := IsRegularGeneratorIn.of_isLocalization_away_mul (t := s₁) hg₂
    (Localization.Away (s₁ * s₂))
  refine ⟨?_, ?_⟩
  · rw [Ideal.map_mul, g₁.1, g₂.1, Ideal.span_singleton_mul_span_singleton, map_mul]
  · rw [map_mul]; exact mul_mem g₁.2 g₂.2

/-- Invertibility is stable under localization at an element: a prime of `A_s` lies over a prime
`𝔭 ∌ s` of `A`, and the datum of `J` at `𝔭` survives in `(A_s)_{s'} = A_{s s'}`. -/
theorem IsInvertible.map_away {J : Ideal A} (hJ : J.IsInvertible) (s : A) :
    (J.map (algebraMap A (Localization.Away s))).IsInvertible := by
  intro q
  obtain ⟨s', hs', a, ha, hg⟩ := hJ (PrimeSpectrum.comap (algebraMap A (Localization.Away s)) q)
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at hs'
  refine ⟨algebraMap A (Localization.Away s) s', hs', algebraMap A (Localization.Away s) a,
    Ideal.mem_map_of_mem _ ha, ?_⟩
  have : IsLocalization.Away (s' * s)
      (Localization.Away (algebraMap A (Localization.Away s) s')) :=
    IsLocalization.Away.mul (Localization.Away s) _ s s'
  have hg' := IsRegularGeneratorIn.of_isLocalization_away_mul (t := s) hg
    (Localization.Away (algebraMap A (Localization.Away s) s'))
  refine ⟨?_, ?_⟩
  · rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq A (Localization.Away s), hg'.1,
      ← IsScalarTower.algebraMap_apply A (Localization.Away s)]
  · rw [← IsScalarTower.algebraMap_apply A (Localization.Away s)]
    exact hg'.2


/-- If `J₁ J₂` is invertible then `J₁` is: the argument of [Hau14, Theorem 4.18, proof (c)], run
on a neighbourhood (see the module docstring). -/
theorem IsInvertible.of_mul_left {J₁ J₂ : Ideal A} (h : (J₁ * J₂).IsInvertible) :
    J₁.IsInvertible := by
  intro p
  obtain ⟨s, hs, g, hg, hspan, hnz⟩ := h p
  -- the prime `𝔮` of `B = A_s` over `𝔭`
  have hdisj : Disjoint (Submonoid.powers s : Set A) (p.asIdeal : Set A) := by
    rw [Set.disjoint_left]
    rintro _ ⟨k, rfl⟩ hk
    exact hs (p.isPrime.mem_of_pow_mem k hk)
  have hq : (p.asIdeal.map (algebraMap A (Localization.Away s))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers s) _ p.asIdeal p.isPrime hdisj
  -- `g = ∑ aᵢ bᵢ` with `aᵢ ∈ J₁ B`, `bᵢ ∈ J₂ B`
  have hg' : algebraMap A (Localization.Away s) g ∈
      J₁.map (algebraMap A (Localization.Away s)) *
        J₂.map (algebraMap A (Localization.Away s)) := by
    rw [← Ideal.map_mul]; exact Ideal.mem_map_of_mem _ hg
  rw [Submodule.mul_eq_span_mul_set] at hg'
  obtain ⟨T, hTs, hgT⟩ := Submodule.mem_span_finite_of_mem_span hg'
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp hgT
  have hxy : ∀ z ∈ T, ∃ x ∈ J₁.map (algebraMap A (Localization.Away s)),
      ∃ y ∈ J₂.map (algebraMap A (Localization.Away s)), x * y = z :=
    fun z hz => Set.mem_mul.mp (hTs hz)
  choose! x hx y hy hxy using hxy
  -- each `cᵢ aᵢ bᵢ = tᵢ g`
  have ht : ∀ z ∈ T, ∃ t : Localization.Away s,
      t * algebraMap A (Localization.Away s) g = c z * x z * y z := fun z hz => by
    have : c z * x z * y z ∈ J₁.map (algebraMap A (Localization.Away s)) *
        J₂.map (algebraMap A (Localization.Away s)) :=
      Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ (hx z hz)) (hy z hz)
    rw [← Ideal.map_mul, hspan] at this
    exact Ideal.mem_span_singleton'.mp this
  choose! t ht using ht
  -- `∑ tᵢ = 1`, so some `tᵢ ∉ 𝔮`
  have hsum : (∑ z ∈ T, t z) * algebraMap A (Localization.Away s) g =
      algebraMap A (Localization.Away s) g :=
    calc (∑ z ∈ T, t z) * algebraMap A (Localization.Away s) g
        = ∑ z ∈ T, c z * x z * y z := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun z hz => ht z hz
      _ = ∑ z ∈ T, c z • z :=
          Finset.sum_congr rfl fun z hz => by rw [smul_eq_mul, mul_assoc, hxy z hz]
      _ = algebraMap A (Localization.Away s) g := hc
  have hsum' : ∑ z ∈ T, t z = 1 :=
    (mul_cancel_right_mem_nonZeroDivisors hnz).mp (by rw [one_mul]; exact hsum)
  obtain ⟨z₀, hz₀, htq⟩ : ∃ z ∈ T, t z ∉ p.asIdeal.map (algebraMap A (Localization.Away s)) := by
    by_contra hcon
    push Not at hcon
    have h1 : (1 : Localization.Away s) ∈ p.asIdeal.map (algebraMap A (Localization.Away s)) :=
      hsum' ▸ Submodule.sum_mem _ hcon
    exact hq.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  -- `t = t₀ / sᵏ` with `t₀ ∉ 𝔭`
  obtain ⟨⟨t₀, ⟨_, k, rfl⟩⟩, ht₀⟩ := IsLocalization.surj (Submonoid.powers s) (t z₀)
  have ht₀' : t z₀ * algebraMap A (Localization.Away s) (s ^ k) =
      algebraMap A (Localization.Away s) t₀ := ht₀
  have hsk : IsUnit (algebraMap A (Localization.Away s) (s ^ k)) :=
    by rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit s).pow k
  -- `C := (A_s)_t` is a localization of `A` away from `t₀ s`
  have hassoc : Associated (t z₀) (algebraMap A (Localization.Away s) t₀) :=
    ht₀' ▸ associated_mul_unit_right (t z₀) _ hsk
  have : IsLocalization.Away (algebraMap A (Localization.Away s) t₀) (Localization.Away (t z₀)) :=
    IsLocalization.Away.of_associated hassoc
  have hC : IsLocalization.Away (t₀ * s) (Localization.Away (t z₀)) :=
    IsLocalization.Away.mul (Localization.Away s) _ s t₀
  have ht₀p : t₀ ∉ p.asIdeal := fun h => htq (by
    have h1 : algebraMap A (Localization.Away s) t₀ ∈
        p.asIdeal.map (algebraMap A (Localization.Away s)) := Ideal.mem_map_of_mem _ h
    rw [← ht₀'] at h1
    exact (Ideal.mul_unit_mem_iff_mem _ hsk).mp h1)
  -- the generator `a₀ ∈ J₁` with `x z₀ = a₀ / sⁱ`
  obtain ⟨⟨⟨a₀, ha₀⟩, ⟨_, i, rfl⟩⟩, hxa⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers s) _).mp (hx z₀ hz₀)
  have hxa' : x z₀ * algebraMap A (Localization.Away s) (s ^ i) =
      algebraMap A (Localization.Away s) a₀ := hxa
  refine ⟨t₀ * s, fun h => (p.isPrime.mem_or_mem h).elim ht₀p hs, a₀, ha₀, ?_⟩
  suffices hgen : J₁.IsRegularGeneratorIn (Localization.Away (t z₀)) a₀ from
    hgen.of_algEquiv (IsLocalization.algEquiv (Submonoid.powers (t₀ * s)) _ _)
  -- in `C`: `t` is a unit, `g` a nonzerodivisor, `c x y = t g`
  set C := Localization.Away (t z₀) with hCdef
  set φ := algebraMap (Localization.Away s) C with hφ
  have hτ : IsUnit (φ (t z₀)) := IsLocalization.Away.algebraMap_isUnit (t z₀)
  have hG : φ (algebraMap A (Localization.Away s) g) ∈ nonZeroDivisors C :=
    IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers (t z₀)) C hnz
  have hcxy : φ (c z₀ * x z₀ * y z₀) ∈ nonZeroDivisors C := by
    rw [← ht z₀ hz₀, map_mul]; exact mul_mem hτ.mem_nonZeroDivisors hG
  have hX : φ (x z₀) ∈ nonZeroDivisors C := by
    rw [map_mul, map_mul, mul_mem_nonZeroDivisors, mul_mem_nonZeroDivisors] at hcxy
    exact hcxy.1.2
  have hY : φ (y z₀) ∈ nonZeroDivisors C := by
    rw [map_mul, mul_mem_nonZeroDivisors] at hcxy
    exact hcxy.2
  have htower : algebraMap A C = φ.comp (algebraMap A (Localization.Away s)) :=
    IsScalarTower.algebraMap_eq A (Localization.Away s) C
  -- `J₁ C = (x z₀)`
  have hspanC : J₁.map (algebraMap A C) = Ideal.span {φ (x z₀)} := by
    apply le_antisymm
    · intro w hw
      have hwY : w * φ (y z₀) ∈ Ideal.span {φ (c z₀ * x z₀ * y z₀)} := by
        have h1 : w * φ (y z₀) ∈ (J₁ * J₂).map (algebraMap A C) := by
          rw [Ideal.map_mul]
          refine Ideal.mul_mem_mul hw ?_
          rw [htower, ← Ideal.map_map]
          exact Ideal.mem_map_of_mem _ (hy z₀ hz₀)
        rw [htower, ← Ideal.map_map, hspan, Ideal.map_span, Set.image_singleton,
          ← Ideal.span_singleton_mul_left_unit hτ (φ (algebraMap A (Localization.Away s) g)),
          ← map_mul, ht z₀ hz₀] at h1
        exact h1
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hwY
      rw [Ideal.mem_span_singleton']
      refine ⟨r * φ (c z₀), (mul_cancel_right_mem_nonZeroDivisors hY).mp ?_⟩
      rw [← hr, map_mul, map_mul]
      simp only [mul_assoc]
    · rw [Ideal.span_le, Set.singleton_subset_iff, htower, ← Ideal.map_map]
      exact Ideal.mem_map_of_mem _ (hx z₀ hz₀)
  -- from `x z₀` to `a₀ = x z₀ · sⁱ`, a unit multiple
  have hsi : IsUnit (φ (algebraMap A (Localization.Away s) (s ^ i))) := by
    rw [map_pow, map_pow]
    exact ((IsLocalization.Away.algebraMap_isUnit s).map φ).pow i
  have ha₀C : algebraMap A C a₀ = φ (x z₀) * φ (algebraMap A (Localization.Away s) (s ^ i)) := by
    rw [htower, RingHom.comp_apply, ← hxa', map_mul]
  refine ⟨?_, ?_⟩
  · rw [hspanC, ha₀C, Ideal.span_singleton_mul_right_unit hsi]
  · rw [ha₀C]; exact mul_mem hX hsi.mem_nonZeroDivisors

/-- If `J₁ J₂` is invertible then `J₁` and `J₂` are. -/
theorem IsInvertible.of_mul {J₁ J₂ : Ideal A} (h : (J₁ * J₂).IsInvertible) :
    J₁.IsInvertible ∧ J₂.IsInvertible :=
  ⟨IsInvertible.of_mul_left h, IsInvertible.of_mul_left (mul_comm J₁ J₂ ▸ h)⟩

end Ideal
