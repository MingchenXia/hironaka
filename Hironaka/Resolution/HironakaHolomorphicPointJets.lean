import Hironaka.Analytic.HolomorphicGermMaximalIdeal
import Hironaka.Invariant.IdealPowerAddition
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.OrderMultiplicativity
import Hironaka.Analytic.EuclideanHolomorphicGermSpan
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional

import Hironaka.MarkedIdeal.GermIdealOrderValue
import Hironaka.MarkedIdeal.GermIdealOrderBounds

set_option autoImplicit false

/-! # Faithful finite jets of the entire holomorphic germ ring

Actual local-ring powers and literal point powers agree. The true finite
linear jet has exactly that whole maximal-ideal power as its kernel and
internally proves finite dimension of R/(I + m^q) for every actual ideal.
No finite quotient, normal-flat centre, HS transformation or descent
certificate is supplied. Blueprint:
`hironaka-holomorphic-point-jets-extension.tex`.
-/

open Set Filter Module
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaHolomorphicPointJets

open Hironaka.HolomorphicIdealSheaves HolGerm
open IdealWeightPowers GermIdealOrder OrderTaylor RelativePrincipalizationSpan

open Hironaka

noncomputable section

variable {n : ℕ}

private theorem holomorphicAt_zero {f : ComplexModel n → ℂ}
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) : HolomorphicAt n f 0 :=
  hf.mono fun _ h => h.mdifferentiableAt

private theorem complex_differentiable_near_zero {f : ComplexModel n → ℂ}
    (hf : HolomorphicAt n f 0) : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z :=
  hf.mono fun _ h => h.differentiableAt

private theorem point_power_zero (q : ℕ) :
    (idealPow (pointIdeal n (0 : ComplexModel n)) q).mem 0 (fun _ => 0) := by
  cases q with
  | zero => exact holomorphicAt_const 0
  | succ q =>
    exact ⟨holomorphicAt_const 0, 0, Fin.elim0, Fin.elim0,
      fun i => Fin.elim0 i, fun i => Fin.elim0 i, Eventually.of_forall fun _ => by simp⟩

private theorem point_power_holomorphic_mul {q : ℕ} {f c : ComplexModel n → ℂ}
    (hc : HolomorphicAt n c 0)
    (hf : (idealPow (pointIdeal n (0 : ComplexModel n)) q).mem 0 f) :
    (idealPow (pointIdeal n (0 : ComplexModel n)) q).mem 0 (fun z => c z * f z) := by
  cases q with
  | zero => exact hc.mul hf
  | succ q => exact mem_idealPow_succ_iff.mpr (IsInSpanAt.mul_left hc (mem_idealPow_succ_iff.mp hf))

/-- The original whole point-power expression belongs to the actual ring power. -/
theorem mem_maximalIdeal_pow_of_point_power {f : ComplexModel n → ℂ}
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) (q : ℕ)
    (hp : (idealPow (pointIdeal n (0 : ComplexModel n)) q).mem 0 f) :
    HolGerm.mk f hf ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q := by
  induction q generalizing f with
  | zero => simp
  | succ q ih =>
    obtain ⟨hfh, K, s, a, hs, ha, heq⟩ := hp
    have hsh : ∀ i, HolomorphicAt n (s i) 0 := by
      intro i
      obtain ⟨b, c, hb, hc, hbc⟩ := hs i
      rw [hbc]
      exact (holomorphicAt_of_mem_idealPow hb).mul hc.1
    have hsr : IsInSpanAt (n := n) (· ∈ range s) 0 f :=
      ⟨hfh, K, s, a, fun i => ⟨i, rfl⟩, ha, heq⟩
    have hring := (EuclideanHolomorphicGermSpan.isInSpanAt_iff_holGerm_mem_span
      s (fun i => complex_differentiable_near_zero (hsh i)) hf).mp hsr
    apply (Ideal.span_le.mpr ?_) hring
    rintro g ⟨i, rfl⟩
    obtain ⟨b, c, hb, hc, hbc⟩ := hs i
    have hbhol := complex_differentiable_near_zero (holomorphicAt_of_mem_idealPow hb)
    have hchol := complex_differentiable_near_zero hc.1
    have hmul : HolGerm.mk (s i) (complex_differentiable_near_zero (hsh i)) =
        HolGerm.mk b hbhol * HolGerm.mk c hchol := by
      rw [← HolGerm.mk_mul]
      exact HolGerm.mk_eq_mk_iff.mpr (Eventually.of_forall fun z => congrFun hbc z)
    change HolGerm.mk (s i) (complex_differentiable_near_zero (hsh i)) ∈ _
    rw [hmul, pow_succ]
    have hc0 : c 0 = 0 := apply_eq_zero_of_mem_pointIdeal (n := n) hc
    exact Ideal.mul_mem_mul (ih hbhol hb)
      ((HolGerm.mem_maximalIdeal_iff _).mpr hc0)

private def pointPowerIdeal (q : ℕ) : Ideal (HolGerm (ComplexModel n)) where
  carrier := {g | ∃ (f : ComplexModel n → ℂ)
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z),
    g = HolGerm.mk f hf ∧ (idealPow (pointIdeal n (0 : ComplexModel n)) q).mem 0 f}
  zero_mem' := ⟨fun _ => 0, eventually_differentiableAt_zero, rfl, point_power_zero q⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl, hp⟩ ⟨g, hg, rfl, hq⟩
    exact ⟨fun z => f z + g z, eventually_differentiableAt_add hf hg,
      (HolGerm.mk_add f g hf hg).symm, mem_idealPow_add hp hq⟩
  smul_mem' := by
    rintro c g ⟨f, hf, rfl, hp⟩
    obtain ⟨a, ha, rfl⟩ := HolGerm.exists_eq_mk c
    exact ⟨fun z => a z * f z, eventually_differentiableAt_mul ha hf,
      (HolGerm.mk_mul a f ha hf).symm,
      point_power_holomorphic_mul (holomorphicAt_zero ha) hp⟩

private theorem maximalIdeal_pow_le_pointPowerIdeal (q : ℕ) :
    IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q ≤ pointPowerIdeal (n := n) q := by
  induction q with
  | zero =>
    intro g _
    obtain ⟨f, hf, rfl⟩ := HolGerm.exists_eq_mk g
    exact ⟨f, hf, rfl, holomorphicAt_zero hf⟩
  | succ q ih =>
    rw [pow_succ]
    apply Ideal.mul_le.mpr
    rintro g hg h hh
    obtain ⟨f, hf, rfl, hp⟩ := ih hg
    obtain ⟨a, ha, rfl⟩ := HolGerm.exists_eq_mk h
    have hap : (pointIdeal n (0 : ComplexModel n)).mem 0 a :=
      mem_pointIdeal_of_apply_eq_zero (holomorphicAt_zero ha)
        ((HolGerm.mem_maximalIdeal_iff _).mp hh)
    exact ⟨fun z => f z * a z, eventually_differentiableAt_mul hf ha,
      (HolGerm.mk_mul f a hf ha).symm,
      mul_mem_idealPow_succ hp hap ((holomorphicAt_zero hf).mul (holomorphicAt_zero ha))⟩

/-- Entire ring powers and the literal original point powers agree in both directions. -/
theorem mem_maximalIdeal_pow_iff_point_power {f : ComplexModel n → ℂ}
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) (q : ℕ) :
    HolGerm.mk f hf ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q ↔
      (idealPow (pointIdeal n (0 : ComplexModel n)) q).mem 0 f := by
  constructor
  · intro hg
    obtain ⟨a, ha, heq, hp⟩ := maximalIdeal_pow_le_pointPowerIdeal q hg
    exact mem_idealPow_congr hp (HolGerm.mk_eq_mk_iff.mp heq).symm
  · exact mem_maximalIdeal_pow_of_point_power hf q

/-- The actual full holomorphic ring power is the exact low-derivative kernel. -/
theorem mem_maximalIdeal_pow_iff_iteratedFDeriv {f : ComplexModel n → ℂ}
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) (q : ℕ) :
    HolGerm.mk f hf ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q ↔
      ∀ j < q, iteratedFDeriv ℂ j f 0 = 0 := by
  rw [mem_maximalIdeal_pow_iff_point_power hf q]
  simpa only [complexChartAt, chartAt_self_eq, OpenPartialHomeomorph.refl_symm,
    Function.comp_def, OpenPartialHomeomorph.refl_apply, id_eq] using
    OrderMultiplicativity.mem_idealPow_pointIdeal_iff_iteratedFDeriv (holomorphicAt_zero hf) q

/-- The complex algebra structure is the original constant-germ map. -/
instance holGermComplexAlgebra (n : ℕ) : Algebra ℂ (HolGerm (ComplexModel n)) :=
  (HolGerm.constHom : ℂ →+* HolGerm (ComplexModel n)).toAlgebra

private theorem analyticAt_zero {f : ComplexModel n → ℂ}
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) : AnalyticAt ℂ f 0 := by
  obtain ⟨U, hUf, hU, h0⟩ := eventually_nhds_iff.mp hf
  exact HolomorphicAnalytic.analyticAt_of_differentiableOn hU
    (fun z hz => (hUf z hz).differentiableWithinAt) h0

/-- The actual finite tuple of original derivatives, descended to the entire germ ring. -/
def finiteJet (q : ℕ) : HolGerm (ComplexModel n) →ₗ[ℂ]
    (∀ j : Fin q, MultilinearMap ℂ (fun _ : Fin j.val => ComplexModel n) ℂ) where
  toFun g := Germ.liftOn (g : Germ (𝓝 (0 : ComplexModel n)) ℂ)
    (fun f j => (iteratedFDeriv ℂ j.val f 0).toMultilinearMap)
    (fun f g h => funext fun j => congrArg ContinuousMultilinearMap.toMultilinearMap
      ((h.iteratedFDeriv ℂ j.val).eq_of_nhds))
  map_add' g h := by
    induction g using HolGerm.induction_on with
    | h f hf =>
      induction h using HolGerm.induction_on with
      | h g hg =>
        change (fun j : Fin q => (iteratedFDeriv ℂ j.val (fun z => f z + g z) 0).toMultilinearMap) = _
        funext j
        rw [show (fun z => f z + g z) = f + g from rfl,
          iteratedFDeriv_add_apply ((analyticAt_zero hf).contDiffAt.of_le le_top)
            ((analyticAt_zero hg).contDiffAt.of_le le_top),
          ContinuousMultilinearMap.toMultilinearMap_add]
        rfl
  map_smul' c g := by
    induction g using HolGerm.induction_on with
    | h f hf =>
      have hcf := eventually_differentiableAt_mul (eventually_differentiableAt_const c) hf
      have heq : c • HolGerm.mk f hf = HolGerm.mk (fun z => c * f z) hcf := by
        rw [Algebra.smul_def]
        rfl
      rw [heq]
      change (fun j : Fin q => (iteratedFDeriv ℂ j.val (fun z => c * f z) 0).toMultilinearMap) = _
      funext j
      change (iteratedFDeriv ℂ j.val (c • f) 0).toMultilinearMap =
        c • (iteratedFDeriv ℂ j.val f 0).toMultilinearMap
      rw [iteratedFDeriv_const_smul_apply ((analyticAt_zero hf).contDiffAt.of_le le_top),
        ContinuousMultilinearMap.toMultilinearMap_smul]

/-- Evaluation on any genuine original representative is the unmodified derivative tuple. -/
theorem finiteJet_mk (q : ℕ) {f : ComplexModel n → ℂ}
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) (j : Fin q) :
    finiteJet (n := n) q (HolGerm.mk f hf) j =
      (iteratedFDeriv ℂ j.val f 0).toMultilinearMap := rfl

/-- The complete actual maximal-ideal power, not a supplied jet-kernel certificate. -/
theorem ker_finiteJet (q : ℕ) :
    LinearMap.ker (finiteJet (n := n) q) =
      (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q).restrictScalars ℂ := by
  ext g
  induction g using HolGerm.induction_on with
  | h f hf =>
    rw [LinearMap.mem_ker]
    change finiteJet (n := n) q (HolGerm.mk f hf) = 0 ↔
      HolGerm.mk f hf ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q
    rw [mem_maximalIdeal_pow_iff_iteratedFDeriv hf q]
    constructor
    · intro hz j hj
      have heq := congrFun hz (⟨j, hj⟩ : Fin q)
      rw [finiteJet_mk] at heq
      exact ContinuousMultilinearMap.toMultilinearMap_injective heq
    · intro hz
      funext j
      rw [finiteJet_mk, hz j.val j.isLt]
      rfl

/-- The actual entire point quotient injects into the genuine finite jet target. -/
theorem finiteDimensional_quotient_maximalIdeal_pow (n q : ℕ) :
    FiniteDimensional ℂ
      (HolGerm (ComplexModel n) ⧸ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q) := by
  let e := (finiteJet (n := n) q).quotKerEquivRange
  have hfd : FiniteDimensional ℂ
      (HolGerm (ComplexModel n) ⧸ LinearMap.ker (finiteJet (n := n) q)) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  rw [ker_finiteJet q] at hfd
  exact hfd

/-- Adding any original ideal still gives an actual finite-dimensional point quotient. -/
theorem finiteDimensional_quotient_sup_maximalIdeal_pow (n q : ℕ)
    (I : Ideal (HolGerm (ComplexModel n))) :
    FiniteDimensional ℂ (HolGerm (ComplexModel n) ⧸
      (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q)) := by
  let := finiteDimensional_quotient_maximalIdeal_pow n q
  have hle : IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q ≤
      I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q := le_sup_right
  let f := Ideal.Quotient.factorₐ ℂ hle
  exact FiniteDimensional.of_surjective f.toLinearMap
    (show Function.Surjective f from Ideal.Quotient.factor_surjective hle)

/-- The actual finite complex dimension of the whole original local ring quotient. -/
def hilbertSamuelValue (I : Ideal (HolGerm (ComplexModel n))) (ℓ : ℕ) : ℕ :=
  finrank ℂ (HolGerm (ComplexModel n) ⧸
    (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ (ℓ + 1)))

end
end Hironaka.HironakaHolomorphicPointJets
