import DeJongAlterations.Algebra.NodeFieldUVJetNondegenerate
import DeJongAlterations.Algebra.NodeVariableMorseFieldExtension

/-! Recover actual original-field nondegeneracy from a genuine scalar cubic-jet surjection. -/

noncomputable section

open MvPowerSeries

namespace DeJongAlterations.Algebra.NodeFieldUVJetScalarRelation

open NodeFormalMorse NodeVariableMorse NodeFieldUVJetTangent

universe u v
variable {K : Type u} {L : Type v} [Field K] [Field L] (ρ : K →+* L)

theorem map_mem_variablePower_iff (F : Series K) (n : ℕ) :
    MvPowerSeries.map ρ F ∈ variableIdeal L ^ n ↔ F ∈ variableIdeal K ^ n := by
  constructor
  · intro h
    apply (mem_variableIdeal_pow_iff_order n F).mpr
    apply nat_le_order
    intro d hd
    apply RingHom.injective ρ
    have hz := coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd)
      ((mem_variableIdeal_pow_iff_order n _).mp h))
    simpa only [coeff_map, map_zero] using hz
  · intro h
    apply (mem_variableIdeal_pow_iff_order n _).mpr
    exact le_trans ((mem_variableIdeal_pow_iff_order n F).mp h) (le_order_map ρ)

theorem original_discriminant_ne_zero (F : Series K)
    (hF2 : F ∈ variableIdeal K ^ 2) (hF3 : F ∉ variableIdeal K ^ 3)
    (ψ : Series L →ₐ[L] Jet L) (hψ : Function.Surjective ψ)
    (hF : ψ (MvPowerSeries.map ρ F) = 0) : jetDiscriminant F ≠ 0 := by
  have h2 := (map_mem_variablePower_iff ρ F 2).mpr hF2
  have h3 : MvPowerSeries.map ρ F ∉ variableIdeal L ^ 3 :=
    fun h => hF3 ((map_mem_variablePower_iff ρ F 3).mp h)
  have hd := NodeFieldUVJetNondegenerate.relation_discriminant_ne_zero L ψ hψ
    (MvPowerSeries.map ρ F) hF h2 h3
  intro hz
  apply hd
  rw [jetDiscriminant_map, hz, map_zero]

end DeJongAlterations.Algebra.NodeFieldUVJetScalarRelation
