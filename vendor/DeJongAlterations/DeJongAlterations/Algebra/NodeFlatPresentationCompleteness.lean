import DeJongAlterations.Algebra.NodeFlatPresentationCoefficientIdeal

/-! # Actual adic completeness for an extended finitely generated coefficient ideal -/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFlatPresentation

open MvPowerSeries

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {A : Type u} [CommRing A] {σ : Type v}

/-- Each actual ideal power has the exact original coefficient-power membership criterion. -/
theorem mem_extended_power_iff (I : Ideal A) (hI : I.FG) (n : ℕ) (f : MvPowerSeries σ A) :
    f ∈ (I.map C) ^ n ↔ ∀ d, coeff d f ∈ I ^ n := by
  rw [← Ideal.map_pow]
  exact mem_extended_iff (I ^ n) hI.pow f

/-- Actual coefficient separatedness implies separatedness for the extended coefficient ideal. -/
theorem isHausdorff_extended (I : Ideal A) [IsHausdorff I A] :
    IsHausdorff (I.map (C : A →+* MvPowerSeries σ A)) (MvPowerSeries σ A) where
  haus' f hf := by
    apply MvPowerSeries.ext
    intro d
    apply NodeFormalMorse.CoefficientLimit.scalar_ext I
    intro n
    have hm : f ∈ (I.map (C : A →+* MvPowerSeries σ A)) ^ n := by
      simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using SModEq.zero.mp (hf n)
    have hc := coeff_mem_of_mem_extended (I ^ n)
      (show f ∈ (I ^ n).map C by simpa only [Ideal.map_pow] using hm) d
    simpa only [map_zero] using Ideal.Quotient.eq_zero_iff_mem.mpr hc

/-- Actual coefficient precompleteness lifts every extended-ideal Cauchy sequence. -/
theorem isPrecomplete_extended (I : Ideal A) (hI : I.FG) [IsPrecomplete I A] :
    IsPrecomplete (I.map (C : A →+* MvPowerSeries σ A)) (MvPowerSeries σ A) where
  prec' f hf := by
    have hcoeff (d : σ →₀ ℕ) : ∃ a : A, ∀ n : ℕ,
        coeff d (f n) ≡ a [SMOD (I ^ n • ⊤ : Submodule A A)] := by
      apply IsPrecomplete.prec (inferInstance : IsPrecomplete I A)
      intro m n hmn
      rw [SModEq.sub_mem]
      have hm : f m - f n ∈ (I.map C) ^ m := by
        simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using SModEq.sub_mem.mp (hf hmn)
      have hc := (mem_extended_power_iff I hI m _).mp hm d
      simpa only [map_sub, Ideal.smul_eq_mul, Ideal.mul_top] using hc
    choose a ha using hcoeff
    let L : MvPowerSeries σ A := fun d => a d
    refine ⟨L, fun n => ?_⟩
    rw [SModEq.sub_mem]
    have hm : f n - L ∈ (I.map C) ^ n := by
      apply (mem_extended_power_iff I hI n _).mpr
      intro d
      change coeff d (f n) - a d ∈ I ^ n
      simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using SModEq.sub_mem.mp (ha d n)
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using hm

/-- Native base completeness supplies native completeness for the actual extended coefficient ideal. -/
theorem isAdicComplete_extended (I : Ideal A) (hI : I.FG) [IsAdicComplete I A] :
    IsAdicComplete (I.map (C : A →+* MvPowerSeries σ A)) (MvPowerSeries σ A) where
  toIsHausdorff := isHausdorff_extended I
  toIsPrecomplete := isPrecomplete_extended I hI

end DeJongAlterations.Algebra.NodeFlatPresentation
