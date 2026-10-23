/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Spectrum.Prime.Module
import Mathlib.RingTheory.Noetherian.Basic

/-! Spreading the actual whole ideal and its regular generator from a native
prime localization. Blueprint: `stable-marked-cartier-spread-algebra.tex`. -/

noncomputable section

namespace DeJongAlterations.StableModificationBridge.StableMarkedCartierSpreadAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem exists_uniform_mul_mem {R : Type*} [CommRing R]
    (I J : Ideal R) (hI : I.FG) (p : Ideal R) [p.IsPrime]
    (h : ∀ x ∈ I, ∃ s ∉ p, s * x ∈ J) :
    ∃ s ∉ p, ∀ x ∈ I, s * x ∈ J := by
  let Q : Submodule R I := Submodule.comap I.subtype J
  let M := I ⧸ Q
  have : Module.Finite R I := Module.Finite.iff_fg.mpr hI
  have hp : (⟨p, inferInstance⟩ : PrimeSpectrum R) ∉ Module.support R M := by
    rw [Module.notMem_support_iff']
    intro m
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective Q m
    obtain ⟨s, hs, hsx⟩ := h x x.2
    refine ⟨s, hs, ?_⟩
    change Submodule.Quotient.mk (p := Q) (s • x) = 0
    exact (Submodule.Quotient.mk_eq_zero Q).mpr hsx
  rw [Module.mem_support_iff_of_finite, SetLike.not_le_iff_exists] at hp
  obtain ⟨s, hs, hsp⟩ := hp
  refine ⟨s, hsp, fun x hx => ?_⟩
  have hz := Module.mem_annihilator.mp hs (Submodule.Quotient.mk (p := Q) ⟨x, hx⟩)
  change Submodule.Quotient.mk (p := Q) (s • (⟨x, hx⟩ : I)) = 0 at hz
  exact (Submodule.Quotient.mk_eq_zero Q).mp hz

/-- A native regular generator of the ACTUAL localized ideal gives an original
regular equation for the SAME whole ideal on a genuine principal neighborhood. -/
theorem exists_regular_generator_away {R S : Type*} [CommRing R] [CommRing S]
    [IsNoetherianRing R] (p : Ideal R) [p.IsPrime] [Algebra R S]
    [IsLocalization p.primeCompl S] (I : Ideal R)
    (hloc : ∃ g : S, IsRegular g ∧ I.map (algebraMap R S) = Ideal.span {g}) :
    ∃ (s : R) (_ : s ∉ p) (t : R), t ∈ I ∧
      IsRegular (algebraMap R (Localization.Away s) t) ∧
      I.map (algebraMap R (Localization.Away s)) =
        Ideal.span {algebraMap R (Localization.Away s) t} := by
  obtain ⟨g, hg, hIg⟩ := hloc
  have hgI : g ∈ I.map (algebraMap R S) := hIg.symm ▸ Ideal.subset_span (Set.mem_singleton _)
  obtain ⟨⟨t, d⟩, htd⟩ := (IsLocalization.mem_map_algebraMap_iff p.primeCompl S).mp hgI
  have hd : IsUnit (algebraMap R S d) := IsLocalization.map_units S d
  have htreg : IsRegular (algebraMap R S t) := htd ▸ hg.mul hd.isRegular
  have hIt : I.map (algebraMap R S) = Ideal.span {algebraMap R S t} := by
    rw [← htd, Ideal.span_singleton_mul_right_unit hd]
    exact hIg
  let J : Ideal R := Ideal.span {(t : R)}
  have hIJ : ∀ x ∈ I, ∃ u ∉ p, u * x ∈ J := by
    intro x hx
    have hx' : algebraMap R S x ∈ J.map (algebraMap R S) := by
      dsimp only [J]
      rw [Ideal.map_span, Set.image_singleton, ← hIt]
      exact Ideal.mem_map_of_mem _ hx
    exact (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl S J x).mp hx'
  obtain ⟨u, hu, huI⟩ := exists_uniform_mul_mem I J (IsNoetherian.noetherian I) p hIJ
  let A : Ideal R := (Ideal.span {(t : R)}).annihilator
  have hA : ∀ x ∈ A, ∃ v ∉ p, v * x ∈ (⊥ : Ideal R) := by
    intro x hx
    have hxt : x * (t : R) = 0 := (Submodule.mem_annihilator_span_singleton (t : R) x).mp hx
    have hx0 : algebraMap R S x = 0 := by
      apply (mul_right_mem_nonZeroDivisors_eq_zero_iff htreg.mem_nonZeroDivisors).mp
      rw [← map_mul, hxt, map_zero]
    obtain ⟨⟨v, hv⟩, hvx⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl S x).mp hx0
    exact ⟨v, hv, hvx⟩
  obtain ⟨v, hv, hvA⟩ := exists_uniform_mul_mem A ⊥ (IsNoetherian.noetherian A) p hA
  let s := u * v
  have hs : s ∉ p := p.primeCompl.mul_mem hu hv
  let φ := algebraMap R (Localization.Away s)
  have hsI : ∀ x ∈ I, s * x ∈ J := by
    intro x hx
    simpa only [s, mul_assoc, mul_left_comm u v] using J.mul_mem_left v (huI x hx)
  refine ⟨s, hs, t, t.2, ?_, ?_⟩
  · rw [isRegular_iff_mem_nonZeroDivisors]
    apply mem_nonZeroDivisors_iff_right.mpr
    intro y hy
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) y
    rw [← IsLocalization.mk'_one (M := Submonoid.powers s) (Localization.Away s) (t : R),
      ← IsLocalization.mk'_mul, mul_one, IsLocalization.mk'_eq_zero_iff] at hy
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := hy
    have haA : s ^ m * a ∈ A := by
      apply (Submodule.mem_annihilator_span_singleton (t : R) _).mpr
      change s ^ m * a * t = 0
      rw [mul_assoc]
      exact hm
    have hz : v * (s ^ m * a) = 0 := hvA _ haA
    rw [IsLocalization.mk'_eq_zero_iff]
    refine ⟨⟨s ^ (m + 1), m + 1, rfl⟩, ?_⟩
    change s ^ (m + 1) * a = 0
    rw [pow_succ', mul_assoc]
    change (u * v) * (s ^ m * a) = 0
    rw [mul_assoc, hz, mul_zero]
  · have hunit : IsUnit (φ s) := IsLocalization.map_units
      (M := Submonoid.powers s) (Localization.Away s) ⟨s, 1, pow_one s⟩
    apply le_antisymm
    · apply Ideal.map_le_iff_le_comap.mpr
      intro x hx
      change φ x ∈ Ideal.span {φ (t : R)}
      apply (Ideal.unit_mul_mem_iff_mem _ hunit).mp
      have hmem := Ideal.mem_map_of_mem φ (hsI x hx)
      simpa only [J, Ideal.map_span, Set.image_singleton, map_mul] using hmem
    · apply Ideal.span_le.mpr
      rintro x rfl
      exact Ideal.mem_map_of_mem φ t.2

end DeJongAlterations.StableModificationBridge.StableMarkedCartierSpreadAlgebra
