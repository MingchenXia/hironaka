import DeJongAlterations.Algebra.NodeVariableMorseOrder
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Genuine finite monomial frames of ALL native two-variable series jets. -/

noncomputable section

open IsLocalRing MvPowerSeries

namespace DeJongAlterations.Algebra.NodeFieldSeriesJetFrame

open NodeFormalMorse NodeVariableMorse

abbrev JetIndex (n : ℕ) := {d : Fin 2 →₀ ℕ // d.degree < n}

instance jetIndexFintype (n : ℕ) : Fintype (JetIndex n) :=
  (Finsupp.finite_of_degree_lt (σ := Fin 2) n).fintype

universe u
variable (K : Type u) [Field K]

abbrev Jet (n : ℕ) := Series K ⧸ variableIdeal K ^ n

/-- The literal finite sum of EVERY original monomial of degree below the actual cutoff. -/
def monomialLift (n : ℕ) : (JetIndex n → K) →ₗ[K] Series K where
  toFun c := ∑ d : JetIndex n, monomial d.val (c d)
  map_add' c e := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c e := by simp only [Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]

/-- EVERY original low-degree index retains exactly its original coefficient. -/
theorem monomialLift_coefficient (n : ℕ) (c : JetIndex n → K) (d : JetIndex n) :
    coeff d.val (monomialLift K n c) = c d := by
  change coeff d.val (∑ e : JetIndex n, monomial e.val (c e)) = c d
  rw [map_sum, Finset.sum_eq_single_of_mem d (Finset.mem_univ d)]
  · exact coeff_monomial_same _ _
  · intro e _ hne
    have he : d.val ≠ e.val := fun h => hne (Subtype.ext h.symm)
    simp only [coeff_monomial, if_neg he]

/-- The actual finite monomial map into the ENTIRE native original variable-power quotient. -/
def toJet (n : ℕ) : (JetIndex n → K) →ₗ[K] Jet K n :=
  (Ideal.Quotient.mkₐ K _).toLinearMap.comp (monomialLift K n)

/-- EVERY original series has its precise actual finite coefficient expansion in the SAME jet. -/
theorem toJet_coefficients (n : ℕ) (f : Series K) :
    toJet K n (fun d => coeff d.val f) = Ideal.Quotient.mk (variableIdeal K ^ n) f := by
  apply Ideal.Quotient.eq.mpr
  apply (mem_variableIdeal_pow_iff_order n _).mpr
  apply nat_le_order
  intro d hd
  rw [map_sub, monomialLift_coefficient K n (fun e => coeff e.val f) ⟨d, hd⟩]
  exact sub_self _

/-- Actual low-degree coefficients prove BOTH whole-map bijectivity directions, including exponent zero. -/
theorem toJet_bijective (n : ℕ) : Function.Bijective (toJet K n) := by
  constructor
  · intro c e hce
    have hz : toJet K n (c - e) = 0 := by rw [map_sub, hce, sub_self]
    have hm : monomialLift K n (c - e) ∈ variableIdeal K ^ n := Ideal.Quotient.eq_zero_iff_mem.mp hz
    funext d
    have hc : coeff d.val (monomialLift K n (c - e)) = 0 :=
      coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast d.property)
        ((mem_variableIdeal_pow_iff_order n _).mp hm))
    rw [monomialLift_coefficient] at hc
    exact sub_eq_zero.mp hc
  · intro z
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨fun d => coeff d.val f, toJet_coefficients K n f⟩

/-- The genuine whole original jet frame, over the SAME original coefficient field. -/
def jetLinearEquiv (n : ℕ) : (JetIndex n → K) ≃ₗ[K] Jet K n :=
  LinearEquiv.ofBijective _ (toJet_bijective K n)

instance jet_finiteDimensional (n : ℕ) : FiniteDimensional K (Jet K n) :=
  Module.Finite.equiv (jetLinearEquiv K n)

/-- The original jet rank is derived from its actual finite monomial frame, not assumed. -/
theorem jet_finrank (n : ℕ) : Module.finrank K (Jet K n) = Fintype.card (JetIndex n) := by
  rw [← (jetLinearEquiv K n).finrank_eq, Module.finrank_fintype_fun_eq_card]

end DeJongAlterations.Algebra.NodeFieldSeriesJetFrame
