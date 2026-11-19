import Hironaka.Analytic.IdealPowers
import Hironaka.Analytic.RueckertNullstellensatz

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Uniform power in the analytic Nullstellensatz: source interface

## Source

J.-P. Demailly, *Complex Analytic and Differential Geometry* (2012 online
edition), Chapter II, Theorem 4.22 (Rückert's analytic Nullstellensatz).
For the coherent-sheaf formulation and its finite-cover globalization, see
H. Grauert--R. Remmert, *Coherent Analytic Sheaves*, Ch. 2, §§3--4.

At each stalk, Rückert's theorem turns inclusion of zero loci into a power
containment.  Finite generation of coherent ideals gives a local exponent, and
compactness chooses a finite cover and its largest exponent.

**PROVED** (TN-CLASSICAL run 0113): `Hironaka.GermPrimeNullstellensatz` proves the
Nullstellensatz for prime ideals of holomorphic germs from the local parametrization, and
`Hironaka.RueckertNullstellensatz.exists_idealPow_le_of_zeroLocus_subset` proves the
statement below (radical form, power form, the chart reading of coherent ideals, and
compactness).  The statement of the theorem below is unchanged.
-/

open Set

namespace Hironaka.UniformNullstellensatzPower

open Hironaka.HolomorphicIdealSheaves
open Hironaka.IdealWeightPowers

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **Uniform power in Rückert's Nullstellensatz — PROVED** (Demailly, CADG II.4.22;
compactness): `RueckertNullstellensatz.exists_idealPow_le_of_zeroLocus_subset`.
For coherent ideal sheaves on a compact complex manifold, containment
`Z(𝔯) ⊆ Z(𝔞)` yields a positive uniform exponent with `𝔞^N ⊆ 𝔯`. -/
theorem demaillyII422_exists_idealPow_le_of_zeroLocus_subset [CompactSpace M]
    {𝔞 𝔯 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) (h𝔯 : 𝔯.IsCoherent)
    (hz : 𝔯.zeroLocus ⊆ 𝔞.zeroLocus) :
    ∃ N : ℕ, 0 < N ∧ (idealPow 𝔞 N).Le 𝔯 := by
  exact RueckertNullstellensatz.exists_idealPow_le_of_zeroLocus_subset h𝔞 h𝔯 hz

end

end Hironaka.UniformNullstellensatzPower
