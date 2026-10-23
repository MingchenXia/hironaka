import DeJongAlterations.Algebra.CompletionRegularityBasics

/-!
The actual cotangent map of original local completion. The level-two
surjectivity proof follows the proof of `AdicCompletion.spanFinrank_maximalIdeal_eq`
in Mathlib/RingTheory/AdicCompletion/LocalRing.lean (Nailin Guan, Apache 2.0),
retaining the actual map and its bijectivity as a reusable declaration.
-/

noncomputable section

open IsLocalRing AdicCompletion Ideal Quotient

namespace DeJongAlterations.Algebra.CompletionRegularityCotangent

open CompletionRegularityBasics

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- The native ideal cotangent map induced by the literal original coefficient homomorphism. -/
def cotangentMap : CotangentSpace R →ₗ[R] CotangentSpace (Completion R) :=
  Ideal.mapCotangent _ _ (Algebra.ofId R (Completion R))
    (le_of_eq (IsLocalRing.maximalIdeal_comap (algebraMap R (Completion R))).symm)

/-- The actual map preserves every original maximal-ideal cotangent class. -/
theorem cotangentMap_toCotangent (r : maximalIdeal R) :
    cotangentMap R ((maximalIdeal R).toCotangent r) =
      (maximalIdeal (Completion R)).toCotangent
        ⟨algebraMap R (Completion R) r,
          (show r.val ∈ (maximalIdeal (Completion R)).comap (algebraMap R (Completion R)) from by
            rw [IsLocalRing.maximalIdeal_comap]; exact r.property)⟩ :=
  Ideal.mapCotangent_toCotangent _ _ _ _ r

/-- Injectivity is genuine reflection of the original maximal square by the actual faithfully flat map. -/
theorem cotangentMap_injective : Function.Injective (cotangentMap R) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  obtain ⟨r, rfl⟩ := Ideal.toCotangent_surjective (maximalIdeal R) z
  rw [cotangentMap_toCotangent, Ideal.toCotangent_eq_zero] at hz
  exact ((maximalIdeal R).toCotangent_eq_zero r).mpr ((mem_maximalIdeal_sq_iff R r).mp hz)

/-- Every actual completed cotangent class comes from an original coefficient class. -/
theorem cotangentMap_surjective : Function.Surjective (cotangentMap R) := by
  intro m
  rcases Ideal.toCotangent_surjective _ m with ⟨m', hm'⟩
  rcases Submodule.Quotient.mk_surjective _ (m'.1.1 2) with ⟨l, hl⟩
  have lmem : (transitionMap _ R (Nat.le_succ 1)) (m'.1.1 2) = m'.1.1 1 := m'.1.2 (Nat.le_succ 1)
  simp only [smul_eq_mul, Nat.succ_eq_add_one, Nat.reduceAdd, transitionMap, Submodule.factorPow,
    Submodule.mapQ_eq_factor, Submodule.factor_eq_factor, ← hl, Ideal.Quotient.mk_eq_mk,
    Ideal.Quotient.factor_mk, pow_one, (mem_maximalIdeal_iff_eval_one_eq_zero m'.1).mp m'.2,
    eq_zero_iff_mem, mul_top] at lmem
  use (maximalIdeal R).toCotangent ⟨l, lmem⟩
  simp only [cotangentMap, Ideal.mapCotangent_toCotangent, Algebra.ofId_apply, ← hm', Ideal.toCotangent_eq]
  change (of (maximalIdeal R) R l) - m' ∈ _
  simp only [maximalIdeal_eq_map, ← Ideal.map_pow]
  rw [← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map]
  simpa [pow_smul_top_eq_ker_eval (maximalIdeal R).fg_of_isNoetherianRing, AdicCompletion.eval, sub_eq_zero] using hl

/-- The actual original coefficient cotangent map is bijective. -/
theorem cotangentMap_bijective : Function.Bijective (cotangentMap R) :=
  ⟨cotangentMap_injective R, cotangentMap_surjective R⟩

/-- The actual cotangent map is semilinear for the literal induced residue-field map. -/
theorem cotangentMap_residue_smul (a : ResidueField R) (v : CotangentSpace R) :
    cotangentMap R (a • v) = ResidueField.map (algebraMap R (Completion R)) a • cotangentMap R v := by
  obtain ⟨r, rfl⟩ := residue_surjective a
  rw [ResidueField.map_residue]
  exact map_smul (cotangentMap R) r v

/-- The actual cotangent equivalence, with forward map exactly the original coefficient map. -/
def cotangentEquiv : CotangentSpace R ≃ₗ[R] CotangentSpace (Completion R) :=
  LinearEquiv.ofBijective (cotangentMap R) (cotangentMap_bijective R)

end DeJongAlterations.Algebra.CompletionRegularityCotangent
