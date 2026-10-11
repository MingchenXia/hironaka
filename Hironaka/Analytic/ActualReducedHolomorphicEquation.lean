/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.ActualHolomorphicGermFactoriality
import Hironaka.Analytic.RueckertNullstellensatz
import Mathlib.RingTheory.Radical.Basic


set_option autoImplicit false

/-! # Actual reduced holomorphic equations and their unit transitions

The actual factorial germ ring and radical Nullstellensatz produce a
reduced equation for a given nonzero holomorphic equation, including
singular zero germs.  Pure codimension-one analytic sets without a given
equation and global divisor currents remain separate tasks.
-/

open Hironaka

noncomputable section
open Filter Topology
namespace Hironaka.ActualReducedHolomorphicEquation
open HolGerm AnalyticGermDecomposition

private theorem vanishingIdeal_eq_radical_span {n : ℕ}
    (f : ComplexModel n → ℂ)
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) :
    vanishingIdeal {z | f z = 0} = (Ideal.span {HolGerm.mk f hf}).radical := by
  let I := vanishingIdeal {z | f z = 0}
  have hI : I.IsRadical := by
    intro A hA
    obtain ⟨N, hN⟩ := Ideal.mem_radical_iff.mp hA
    obtain ⟨a, ha, rfl⟩ := HolGerm.exists_eq_mk A
    have hpow : HolGerm.mk (fun z => a z ^ N)
        (eventually_differentiableAt_pow ha N) ∈ I := by
      rwa [HolGerm.mk_pow]
    apply mem_vanishingIdeal_mk.mpr
    filter_upwards [mem_vanishingIdeal_mk.mp hpow] with z hz hzf
    exact (pow_eq_zero_iff'.mp (hz hzf)).1
  apply le_antisymm
  · simpa only [Fin.forall_fin_one] using
      RueckertNullstellensatz.vanishingIdeal_le_radical
        (Ideal.span {HolGerm.mk f hf}) (fun _ : Fin 1 => f)
        (fun _ => ⟨hf, Ideal.subset_span (Set.mem_singleton _)⟩)
  · apply (hI.radical_le_iff).mpr
    apply Ideal.span_le.mpr
    rintro _ rfl
    exact mem_vanishingIdeal_mk.mpr (Eventually.of_forall fun _ h => h)

/-- A given nonzero holomorphic equation internally produces an actual
nonzero squarefree equation for its entire vanishing ideal and zero germ. -/
theorem exists_reduced_equation {n : ℕ} (f : ComplexModel n → ℂ)
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z)
    (hF : HolGerm.mk f hf ≠ 0) :
    ∃ (r : ComplexModel n → ℂ)
      (hr : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ r z),
      HolGerm.mk r hr ≠ 0 ∧ Squarefree (HolGerm.mk r hr) ∧
      vanishingIdeal {z | f z = 0} = Ideal.span {HolGerm.mk r hr} ∧
      ∀ᶠ z in 𝓝 0, (f z = 0 ↔ r z = 0) := by
  let : UniqueFactorizationMonoid (HolGerm (ComplexModel n)) :=
    ActualHolomorphicGermFactoriality.uniqueFactorizationMonoid_holGerm_euclidean n
  let : StrongNormalizationMonoid (HolGerm (ComplexModel n)) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let R := UniqueFactorizationMonoid.radical (HolGerm.mk f hf)
  have hrad : (Ideal.span {HolGerm.mk f hf}).radical = Ideal.span {R} := by
    ext A
    simp only [Ideal.mem_radical_iff, Ideal.mem_span_singleton]
    exact UniqueFactorizationMonoid.exists_dvd_pow_iff_radical_dvd hF
  obtain ⟨r, hr, hR⟩ := HolGerm.exists_eq_mk R
  have hideal : vanishingIdeal {z | f z = 0} = Ideal.span {HolGerm.mk r hr} := by
    rw [vanishingIdeal_eq_radical_span f hf, hrad, hR]
  have hz : ∀ᶠ z in 𝓝 0, f z = 0 → r z = 0 :=
    mem_vanishingIdeal_mk.mp (hideal ▸ Ideal.subset_span (Set.mem_singleton _))
  obtain ⟨B, hB⟩ := UniqueFactorizationMonoid.radical_dvd_self (a := HolGerm.mk f hf)
  obtain ⟨b, hb, hrep⟩ := HolGerm.exists_eq_mk B
  have hmul : HolGerm.mk f hf =
      HolGerm.mk (fun z => r z * b z) (eventually_differentiableAt_mul hr hb) := by
    rw [HolGerm.mk_mul r b hr hb, ← hR, ← hrep]
    exact hB
  refine ⟨r, hr, ?_, ?_, hideal, ?_⟩
  · rw [← hR]
    exact UniqueFactorizationMonoid.radical_ne_zero
  · rw [← hR]
    exact UniqueFactorizationMonoid.squarefree_radical
  · filter_upwards [hz, HolGerm.mk_eq_mk_iff.mp hmul] with z hz hmul
    refine ⟨hz, fun h => ?_⟩
    rw [hmul, h, zero_mul]

/-- Equal actual zero germs of reduced nonzero equations produce a genuine
holomorphic unit transition, including nonvanishing on a neighbourhood. -/
theorem exists_unit_transition_of_reduced_zero_germ {n : ℕ}
    (f g : ComplexModel n → ℂ)
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z)
    (hg : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ g z)
    (hsF : Squarefree (HolGerm.mk f hf)) (hsG : Squarefree (HolGerm.mk g hg))
    (hz : ∀ᶠ z in 𝓝 0, (f z = 0 ↔ g z = 0)) :
    ∃ (h : ComplexModel n → ℂ),
      (∀ᶠ z in 𝓝 0, DifferentiableAt ℂ h z) ∧ h 0 ≠ 0 ∧
      (∀ᶠ z in 𝓝 0, h z ≠ 0) ∧ f =ᶠ[𝓝 0] fun z => h z * g z := by
  let : UniqueFactorizationMonoid (HolGerm (ComplexModel n)) :=
    ActualHolomorphicGermFactoriality.uniqueFactorizationMonoid_holGerm_euclidean n
  have hred (a : HolGerm (ComplexModel n)) (ha : Squarefree a) :
      (Ideal.span {a}).radical = Ideal.span {a} := by
    apply Ideal.radical_eq_iff.mpr
    intro b hb
    obtain ⟨N, hN⟩ := Ideal.mem_radical_iff.mp hb
    exact Ideal.mem_span_singleton.mpr
      (ha.isRadical N b (Ideal.mem_span_singleton.mp hN))
  have heq : Ideal.span {HolGerm.mk f hf} = Ideal.span {HolGerm.mk g hg} := by
    rw [← hred _ hsF, ← hred _ hsG,
      ← vanishingIdeal_eq_radical_span f hf, ← vanishingIdeal_eq_radical_span g hg]
    apply vanishingIdeal_congr
    exact eventuallyEq_set.mpr hz
  have hGF : HolGerm.mk g hg ∣ HolGerm.mk f hf :=
    Ideal.mem_span_singleton.mp (heq ▸ Ideal.subset_span (Set.mem_singleton _))
  have hFG : HolGerm.mk f hf ∣ HolGerm.mk g hg :=
    Ideal.mem_span_singleton.mp (heq.symm ▸ Ideal.subset_span (Set.mem_singleton _))
  obtain ⟨H, hH⟩ := associated_of_dvd_dvd hGF hFG
  obtain ⟨h, hh, hrep⟩ := HolGerm.exists_eq_mk (H : HolGerm (ComplexModel n))
  have hh0 : h 0 ≠ 0 := by
    have hv := (HolGerm.isUnit_iff_eval_ne_zero _).mp H.isUnit
    rwa [hrep, HolGerm.eval_mk] at hv
  have hmul : HolGerm.mk f hf =
      HolGerm.mk (fun z => h z * g z) (eventually_differentiableAt_mul hh hg) := by
    rw [HolGerm.mk_mul h g hh hg, ← hrep, mul_comm]
    exact hH.symm
  exact ⟨h, hh, hh0, hh.self_of_nhds.continuousAt.eventually_ne hh0,
    HolGerm.mk_eq_mk_iff.mp hmul⟩

end Hironaka.ActualReducedHolomorphicEquation
