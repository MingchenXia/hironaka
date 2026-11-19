import Hironaka.Analytic.HiepSliceAssembly
import Hironaka.Analytic.GermKrullIntersectionProof
import Hironaka.Analytic.BoxCoeffsIdeal

set_option autoImplicit false

/-!
# Strong openness for increasing sequences from the Ohsawa--Takegoshi theorem alone

`increasingStrongOpenness_of_ohsawaTakegoshi_krull` (`Hironaka.HiepSliceAssembly`) proves
`IncreasingStrongOpenness n` for every `n` from two stated interfaces: the Ohsawa--Takegoshi
extension theorem `OhsawaTakegoshiHyperplane` and Krull's intersection theorem for ideals of
holomorphic germs `GermKrullIntersection`.  The second is now a theorem:
`germKrullIntersection` combines the Noetherianity of the ring of holomorphic germs
(`Hironaka.HolomorphicGermNoetherian`, Rückert's basis theorem via Weierstrass division),
Krull's intersection theorem in Noetherian local rings (`Hironaka.GermKrullIntersectionProof`)
and the box-coefficient lemma (`Hironaka.BoxCoeffsIdeal`).  The only remaining analytic
input is the Ohsawa--Takegoshi interface (`Hironaka.OhsawaTakegoshiInterface`).
-/

namespace Hironaka

/-- **Krull's intersection theorem for ideals of holomorphic germs** at a point of
`ℂ^{m+1}`, in the form consumed by the strong-openness argument. -/
theorem germKrullIntersection (m : ℕ) : GermKrullIntersection m :=
  germKrullIntersection_of_boxCoeffsIdeal fun _ _ _ hs hss' _ he K hzero =>
    exists_eq_sum_pow_mul_of_boxCoeffs_eq_zero hs hss' he K hzero

/-- **Strong openness for increasing sequences** (Xia, Theorem 1.4.4; Guan--Zhou, Hiep) in
every dimension, from the Ohsawa--Takegoshi extension theorem. -/
theorem increasingStrongOpenness_of_ohsawaTakegoshi (hOT : OhsawaTakegoshiHyperplane) (n : ℕ) :
    IncreasingStrongOpenness n :=
  increasingStrongOpenness_of_ohsawaTakegoshi_krull hOT germKrullIntersection n

end Hironaka
