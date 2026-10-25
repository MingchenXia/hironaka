import DeJongAlterations.Algebra.CompletionFlatMapLevels

/-! EVERY finite maximal-point jet through the ACTUAL original completion map. -/

noncomputable section

open IsLocalRing

namespace DeJongAlterations.Algebra.NodeGeometricCompletionJets

open CompletionRegularityBasics

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The WHOLE completed maximal power contracts to the SAME original power. -/
theorem maximalPower_comap (n : ℕ) :
    (maximalIdeal (Completion R) ^ n).comap (algebraMap R (Completion R)) =
      maximalIdeal R ^ n := by
  rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, comap_map]

/-- The literal original completion quotient map at EVERY exponent. -/
def jetMap (n : ℕ) : (R ⧸ maximalIdeal R ^ n) →ₐ[R]
    (Completion R ⧸ maximalIdeal (Completion R) ^ n) :=
  Ideal.quotientMapₐ _ (Algebra.ofId R (Completion R)) (maximalPower_comap R n).symm.le

/-- Every original representative retains the SAME literal completion image. -/
theorem jetMap_mk (n : ℕ) (r : R) :
    jetMap R n (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ (algebraMap R (Completion R) r) := rfl

/-- Native faithful-flat ideal contraction proves injectivity of the SAME quotient map. -/
theorem jetMap_injective (n : ℕ) : Function.Injective (jetMap R n) :=
  Ideal.quotientMap_injective' (H := (maximalPower_comap R n).symm.le)
    (maximalPower_comap R n).le

/-- Native completion coordinates supply actual original representatives at EVERY exponent. -/
theorem jetMap_surjective (n : ℕ) : Function.Surjective (jetMap R n) := by
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨r, hr⟩ := CompletionFlatMap.exists_original_congr R n x
  refine ⟨Ideal.Quotient.mk _ r, ?_⟩
  rw [jetMap_mk]
  symm
  apply Ideal.Quotient.eq.mpr
  rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow]
  exact hr

/-- EVERY original finite jet is genuinely the SAME actual completed finite jet. -/
def jetEquiv (n : ℕ) : (R ⧸ maximalIdeal R ^ n) ≃ₐ[R]
    (Completion R ⧸ maximalIdeal (Completion R) ^ n) :=
  AlgEquiv.ofBijective (jetMap R n) ⟨jetMap_injective R n, jetMap_surjective R n⟩

/-- The completed finite-jet equivalence retains EVERY original representative. -/
theorem jetEquiv_mk (n : ℕ) (r : R) :
    jetEquiv R n (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ (algebraMap R (Completion R) r) := rfl

end DeJongAlterations.Algebra.NodeGeometricCompletionJets
