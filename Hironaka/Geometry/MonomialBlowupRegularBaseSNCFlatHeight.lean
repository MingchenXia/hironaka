import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-! Actual minimal-prime contraction and prime-height bounds from native flatness. -/

noncomputable section

namespace Hironaka.Geometry.MonomialBlowupRegularBaseSNCFlatHeight

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

/-- Actual minimal primes contract to actual minimal primes under a flat algebra, without Noetherian assumptions. -/
theorem minimalPrime_under_of_flat (P : Ideal S) (hP : P ∈ minimalPrimes S) :
    P.under R ∈ minimalPrimes R := by
  let : P.IsPrime := hP.isPrime
  let p := P.under R
  refine ⟨⟨inferInstance, bot_le⟩, ?_⟩
  intro q hq hqp
  let : q.IsPrime := hq.1
  obtain ⟨Q, hQP, hQ, hQp⟩ :=
    P.exists_ideal_le_liesOver_of_le (p := q) (q := p) hqp
  have hPQ : P ≤ Q := hP.2 ⟨hQ, bot_le⟩ hQP
  have heq : P = Q := le_antisymm hPQ hQP
  have hqeq : q = p := by
    rw [hQp.over, ← heq]
  exact hqeq.symm.le

/-- Native flat going down gives the genuine contracted-prime height inequality. -/
theorem height_under_le_of_flat [IsNoetherianRing R] [IsNoetherianRing S]
    (P : Ideal S) [P.IsPrime] : (P.under R).height ≤ P.height := by
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (P.under R) P]
  exact le_self_add

end Hironaka.Geometry.MonomialBlowupRegularBaseSNCFlatHeight
