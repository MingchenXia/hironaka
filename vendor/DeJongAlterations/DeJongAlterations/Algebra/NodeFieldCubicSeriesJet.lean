import DeJongAlterations.Algebra.NodeVariableMorseOrder
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! The actual six-monomial frame of the original two-variable cubic-power quotient. -/

noncomputable section

open MvPowerSeries

namespace DeJongAlterations.Algebra.NodeFieldCubicSeriesJet

open NodeFormalMorse NodeVariableMorse

def exponent : Fin 6 → (Fin 2 →₀ ℕ) :=
  ![0, Finsupp.single 0 1, Finsupp.single 1 1, Finsupp.single 0 2,
    Finsupp.single 0 1 + Finsupp.single 1 1, Finsupp.single 1 2]

theorem exponent_injective : Function.Injective exponent := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [exponent, Finsupp.ext_iff, Fin.forall_fin_two]

theorem exponent_degree (i : Fin 6) : (exponent i).degree < 3 := by
  fin_cases i <;> simp [exponent]

theorem exponent_surjective_low (d : Fin 2 →₀ ℕ) (hd : d.degree < 3) :
    ∃ i : Fin 6, exponent i = d := by
  have he : d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) := by
    ext i
    fin_cases i <;> simp
  have hdegree : d.degree = d 0 + d 1 := by
    calc
      d.degree = (Finsupp.single (0 : Fin 2) (d 0) +
        Finsupp.single (1 : Fin 2) (d 1)).degree := congrArg Finsupp.degree he
      _ = d 0 + d 1 := by simp
  have h0 : d 0 = 0 ∨ d 0 = 1 ∨ d 0 = 2 := by omega
  have h1 : d 1 = 0 ∨ d 1 = 1 ∨ d 1 = 2 := by omega
  rcases h0 with h0 | h0 | h0
  · rcases h1 with h1 | h1 | h1
    · exact ⟨0, by simpa [exponent, h0, h1] using he.symm⟩
    · exact ⟨2, by simpa [exponent, h0, h1] using he.symm⟩
    · exact ⟨5, by simpa [exponent, h0, h1] using he.symm⟩
  · rcases h1 with h1 | h1 | h1
    · exact ⟨1, by simpa [exponent, h0, h1] using he.symm⟩
    · exact ⟨4, by simpa [exponent, h0, h1] using he.symm⟩
    · omega
  · rcases h1 with h1 | h1 | h1
    · exact ⟨3, by simpa [exponent, h0, h1] using he.symm⟩
    · omega
    · omega

universe u
variable (K : Type u) [Field K]

def monomialLift : (Fin 6 → K) →ₗ[K] Series K where
  toFun c := ∑ i : Fin 6, monomial (exponent i) (c i)
  map_add' c e := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c e := by simp only [Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]

theorem monomialLift_coefficient (c : Fin 6 → K) (i : Fin 6) :
    coeff (exponent i) (monomialLift K c) = c i := by
  change coeff (exponent i) (∑ j : Fin 6, monomial (exponent j) (c j)) = c i
  rw [map_sum, Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · exact coeff_monomial_same _ _
  · intro j _ hne
    have he : exponent i ≠ exponent j := fun h => hne (exponent_injective h).symm
    simp only [coeff_monomial, if_neg he]

def toJet : (Fin 6 → K) →ₗ[K] (Series K ⧸ variableIdeal K ^ 3) :=
  (Ideal.Quotient.mkₐ K _).toLinearMap.comp (monomialLift K)

theorem toJet_bijective : Function.Bijective (toJet K) := by
  constructor
  · intro c e hce
    have hz : toJet K (c - e) = 0 := by rw [map_sub, hce, sub_self]
    have hm : monomialLift K (c - e) ∈ variableIdeal K ^ 3 :=
      Ideal.Quotient.eq_zero_iff_mem.mp hz
    funext i
    have hc := coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast exponent_degree i)
      ((mem_variableIdeal_pow_iff_order 3 _).mp hm))
    rw [monomialLift_coefficient] at hc
    exact sub_eq_zero.mp hc
  · intro z
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
    let c : Fin 6 → K := fun i => coeff (exponent i) f
    refine ⟨c, Ideal.Quotient.eq.mpr ?_⟩
    apply (mem_variableIdeal_pow_iff_order 3 _).mpr
    apply nat_le_order
    intro d hd
    obtain ⟨i, rfl⟩ := exponent_surjective_low d hd
    rw [map_sub, monomialLift_coefficient]
    exact sub_self _

def jetLinearEquiv : (Fin 6 → K) ≃ₗ[K] (Series K ⧸ variableIdeal K ^ 3) :=
  LinearEquiv.ofBijective _ (toJet_bijective K)

instance jet_finiteDimensional : FiniteDimensional K (Series K ⧸ variableIdeal K ^ 3) :=
  Module.Finite.equiv (jetLinearEquiv K)

theorem jet_finrank : Module.finrank K (Series K ⧸ variableIdeal K ^ 3) = 6 := by
  rw [← (jetLinearEquiv K).finrank_eq, Module.finrank_fintype_fun_eq_card]
  rfl

end DeJongAlterations.Algebra.NodeFieldCubicSeriesJet
