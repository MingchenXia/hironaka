import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Recover the SAME actual local algebra map from its original finite jet ranks.
The Noetherian Krull separation argument generalizes the repository's Hironaka
whole-ideal jet detection; no complex coefficients or geometric normal form are used. -/

noncomputable section

open IsLocalRing

namespace DeJongAlterations.Algebra.NodeFieldJetRigidity

universe u v w
variable (K : Type u) [Field K] {R : Type v} {T : Type w}
  [CommRing R] [CommRing T] [IsLocalRing R] [IsLocalRing T]
  [Algebra K R] [Algebra K T] (q : R →ₐ[K] T) (hq : Function.Surjective q)

include hq

/-- Every original maximal power has the SAME actual target maximal power as image. -/
theorem maximalPower_image (n : ℕ) :
    (maximalIdeal R ^ n).map q.toRingHom = maximalIdeal T ^ n := by
  rw [Ideal.map_pow, map_maximalIdeal_of_surjective q.toRingHom hq]

/-- The literal quotient map induced by the SAME original algebra homomorphism. -/
def jetMap (n : ℕ) : (R ⧸ maximalIdeal R ^ n) →ₐ[K] (T ⧸ maximalIdeal T ^ n) :=
  Ideal.quotientMapₐ _ q (Ideal.map_le_iff_le_comap.mp (maximalPower_image K q hq n).le)

/-- Every original representative retains its actual original image. -/
theorem jetMap_mk (n : ℕ) (r : R) :
    jetMap K q hq n (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (q r) := rfl

/-- Surjectivity is proved for the actual original induced map at EVERY order. -/
theorem jetMap_surjective (n : ℕ) : Function.Surjective (jetMap K q hq n) := by
  intro z
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨r, rfl⟩ := hq t
  exact ⟨Ideal.Quotient.mk _ r, rfl⟩

/-- Finite equal ranks prove injectivity of the actual map, without a jet-map certificate. -/
theorem jetMap_injective_of_finrank_eq (n : ℕ)
    [FiniteDimensional K (R ⧸ maximalIdeal R ^ n)]
    [FiniteDimensional K (T ⧸ maximalIdeal T ^ n)]
    (hdim : Module.finrank K (R ⧸ maximalIdeal R ^ n) =
      Module.finrank K (T ⧸ maximalIdeal T ^ n)) :
    Function.Injective (jetMap K q hq n) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (jetMap K q hq n).toLinearMap) hdim).mpr
    (jetMap_surjective K q hq n)

variable [IsNoetherianRing R]
  [∀ n : ℕ, FiniteDimensional K (R ⧸ maximalIdeal R ^ n)]
  [∀ n : ℕ, FiniteDimensional K (T ⧸ maximalIdeal T ^ n)]

/-- Native local Noetherian Krull intersection recovers the WHOLE original kernel. -/
theorem injective_of_all_jet_finrank_eq
    (hdim : ∀ n : ℕ, Module.finrank K (R ⧸ maximalIdeal R ^ n) =
      Module.finrank K (T ⧸ maximalIdeal T ^ n)) : Function.Injective q := by
  intro r s hrs
  have hmem : r - s ∈ ⨅ n : ℕ, maximalIdeal R ^ n := by
    simp only [Ideal.mem_iInf]
    intro n
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply jetMap_injective_of_finrank_eq K q hq n (hdim n)
    rw [jetMap_mk, map_sub, hrs, sub_self, map_zero, map_zero]
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top] at hmem
  exact sub_eq_zero.mp hmem

/-- The resulting isomorphism is on the SAME original algebras, over the SAME field. -/
def equivOfJetRanks
    (hdim : ∀ n : ℕ, Module.finrank K (R ⧸ maximalIdeal R ^ n) =
      Module.finrank K (T ⧸ maximalIdeal T ^ n)) : R ≃ₐ[K] T :=
  AlgEquiv.ofBijective q ⟨injective_of_all_jet_finrank_eq K q hq hdim, hq⟩

/-- EVERY original element retains its literal original image. -/
theorem equivOfJetRanks_apply
    (hdim : ∀ n : ℕ, Module.finrank K (R ⧸ maximalIdeal R ^ n) =
      Module.finrank K (T ⧸ maximalIdeal T ^ n)) (r : R) :
    equivOfJetRanks K q hq hdim r = q r := rfl

end DeJongAlterations.Algebra.NodeFieldJetRigidity
