import DeJongAlterations.Algebra.NodeFieldUVJetTangent
import DeJongAlterations.Algebra.NodeFieldQuadraticChangeSeries

/-! The multiplicative geometric cubic jet internally forces actual quadratic nondegeneracy. -/

noncomputable section

open IsLocalRing MvPowerSeries

namespace DeJongAlterations.Algebra.NodeFieldUVJetNondegenerate

open NodeFormalMorse NodeVariableMorse NodeFieldUVJetKernel NodeFieldUVJetTangent
  NodeFieldCotangentGeneratorsJet NodeFieldQuadraticChangeSeries

universe u
variable (K : Type u) [Field K]
  (ψ : Series K →ₐ[K] Jet K) (hψ : Function.Surjective ψ)

def coordinateLift (i : Fin 2) : Series K :=
  Classical.choose (Ideal.Quotient.mk_surjective (ψ (X i)))

theorem coordinateLift_spec (i : Fin 2) :
    Ideal.Quotient.mk _ (coordinateLift K ψ i) = ψ (X i) :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective (ψ (X i)))

include hψ in
theorem coordinateLift_constantCoeff (i : Fin 2) : constantCoeff (coordinateLift K ψ i) = 0 := by
  have hm : ψ (X i) ∈ maximalIdeal (Jet K) := by
    rw [← map_maximalIdeal_of_surjective ψ.toRingHom hψ]
    apply Ideal.mem_map_of_mem
    rw [series_maximalIdeal K]
    exact Ideal.subset_span (Set.mem_range_self i)
  have hk : RingHom.ker (NodeFieldUVJetTangent.coefficientMap K).toRingHom = maximalIdeal (Jet K) :=
    ker_eq_maximalIdeal _ (coefficientMap_surjective K)
  have hz : ψ (X i) ∈ RingHom.ker (NodeFieldUVJetTangent.coefficientMap K).toRingHom := by
    rw [hk]
    exact hm
  have he := congrArg (NodeFieldUVJetTangent.coefficientMap K) (coordinateLift_spec K ψ i)
  exact he.trans hz

theorem maximalIdeal_cube : maximalIdeal (Jet K) ^ 3 = ⊥ := by
  rw [maximalPower_eq_map_variables, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  exact le_sup_right

include hψ in
theorem cube_le_kernel : variableIdeal K ^ 3 ≤ RingHom.ker ψ.toRingHom := by
  have hm : (variableIdeal K ^ 3).map ψ.toRingHom = maximalIdeal (Jet K) ^ 3 := by
    rw [Ideal.map_pow, ← series_maximalIdeal K,
      map_maximalIdeal_of_surjective ψ.toRingHom hψ]
  apply (Ideal.map_eq_bot_iff_le_ker _).mp
  exact hm.trans (maximalIdeal_cube K)

include hψ in
theorem relation_discriminant_ne_zero (F : Series K)
    (hF : ψ F = 0) (hF2 : F ∈ variableIdeal K ^ 2) (hF3 : F ∉ variableIdeal K ^ 3) :
    jetDiscriminant F ≠ 0 := by
  have hcoord := (mem_variableSquare_iff K F).mp hF2
  have hc : constantCoeff F = 0 := congrArg Prod.fst hcoord
  have h0 : coeff (Finsupp.single 0 1) F = 0 := congrArg (fun p => p.2 0) hcoord
  have h1 : coeff (Finsupp.single 1 1) F = 0 := congrArg (fun p => p.2 1) hcoord
  have hsub := sub_quadraticJet_mem_pow F hc h0 h1
  have habc : ¬ (quadraticCoefficient0 F = 0 ∧ quadraticCoefficient1 F = 0 ∧
      quadraticCoefficient2 F = 0) := by
    rintro ⟨ha, hb, hc⟩
    apply hF3
    simpa only [quadraticJet, ha, hb, hc, map_zero, zero_add, sub_zero] using hsub
  have hkill : ψ (quadraticJet F) = 0 := by
    have he := cube_le_kernel K ψ hψ hsub
    change ψ (F - quadraticJet F) = 0 at he
    rw [map_sub, hF, zero_sub, neg_eq_zero] at he
    exact he
  have hcoeff (a : K) : ψ (C a) = Ideal.Quotient.mk _ (C a : Series K) := by
    simpa only [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Ideal.Quotient.mkₐ_eq_mk] using
      (ψ.commutes a).trans ((Ideal.Quotient.mkₐ K (jetIdeal K 3)).commutes a).symm
  have hquad : quadraticJet F = quadraticSeries
      (quadraticCoefficient0 F) (quadraticCoefficient1 F) (quadraticCoefficient2 F) :=
    (quadraticSeries_monomials _ _ _).symm
  have he : Ideal.Quotient.mk (jetIdeal K 3)
      (composition (quadraticCoefficient0 F) (quadraticCoefficient1 F) (quadraticCoefficient2 F)
        (coordinateLift K ψ 0) (coordinateLift K ψ 1)) = ψ (quadraticJet F) := by
    rw [hquad]
    simp only [composition, quadraticSeries, map_add, map_mul, map_pow, hcoeff,
      coordinateLift_spec]
  have hmem : composition (quadraticCoefficient0 F) (quadraticCoefficient1 F) (quadraticCoefficient2 F)
      (coordinateLift K ψ 0) (coordinateLift K ψ 1) ∈ jetIdeal K 3 :=
    Ideal.Quotient.eq_zero_iff_mem.mp (he.trans hkill)
  have hdet : NodeFieldQuadraticChange.determinant
      (coeff (Finsupp.single 0 1) (coordinateLift K ψ 0))
      (coeff (Finsupp.single 1 1) (coordinateLift K ψ 0))
      (coeff (Finsupp.single 0 1) (coordinateLift K ψ 1))
      (coeff (Finsupp.single 1 1) (coordinateLift K ψ 1)) ≠ 0 := by
    have hd := determinant_ne_zero K ψ hψ
    rw [← coordinateLift_spec K ψ 0, ← coordinateLift_spec K ψ 1] at hd
    exact hd
  apply discriminant_ne_zero_of_diagonal_coefficients
    (quadraticCoefficient0 F) (quadraticCoefficient1 F) (quadraticCoefficient2 F)
    (coordinateLift K ψ 0) (coordinateLift K ψ 1)
    (coordinateLift_constantCoeff K ψ hψ 0) (coordinateLift_constantCoeff K ψ hψ 1) hdet habc
  · exact (mem_jetIdeal_iff 3 _).mp hmem _ (by simp) (by simp)
  · exact (mem_jetIdeal_iff 3 _).mp hmem _ (by simp) (by simp)

end DeJongAlterations.Algebra.NodeFieldUVJetNondegenerate
