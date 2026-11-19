import Hironaka.Analytic.RueckertNullstellensatz

/-! # Analytic Nullstellensatz through an arbitrary quotient -/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10AnalyticNullstellensatzQuotient

open Hironaka Hironaka
  AnalyticGermDecomposition

/-- If the common zero germ of actual holomorphic functions lies in `A`,
  then every germ vanishing on `A` lies in the radical of any ideal
  containing their germs. -/
theorem vanishingIdeal_le_radical_of_local_zero_containment {n r : ℕ}
    (I : Ideal (HolGerm (ComplexModel n))) (F : Fin r → ComplexModel n → ℂ)
    (hF : ∀ j, ∃ hj : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (F j) z,
      HolGerm.mk (F j) hj ∈ I) (A : Set (ComplexModel n))
    (hzero : ∀ᶠ z in 𝓝 0, (∀ j, F j z = 0) → z ∈ A) :
    vanishingIdeal A ≤ I.radical := by
  have hanti : vanishingIdeal A ≤ vanishingIdeal {z | ∀ j, F j z = 0} :=
    vanishingIdeal_anti hzero
  exact hanti.trans (RueckertNullstellensatz.vanishingIdeal_le_radical I F hF)

/-- The same geometric-to-radical implication after any ring map from the
  holomorphic germ ring; no radical or reducedness assumption is imposed on
  the target ideal. -/
theorem map_vanishingIdeal_le_radical_of_local_zero_containment {n r : ℕ}
    {R : Type*} [CommRing R] (φ : HolGerm (ComplexModel n) →+* R) (I : Ideal R)
    (F : Fin r → ComplexModel n → ℂ)
    (hF : ∀ j, ∃ hj : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (F j) z,
      φ (HolGerm.mk (F j) hj) ∈ I) (A : Set (ComplexModel n))
    (hzero : ∀ᶠ z in 𝓝 0, (∀ j, F j z = 0) → z ∈ A) :
    Ideal.map φ (vanishingIdeal A) ≤ I.radical := by
  rw [Ideal.map_le_iff_le_comap, Ideal.comap_radical]
  exact vanishingIdeal_le_radical_of_local_zero_containment (Ideal.comap φ I) F hF A hzero

end Hironaka.Analytic.Unibranch.HironakaG10AnalyticNullstellensatzQuotient
