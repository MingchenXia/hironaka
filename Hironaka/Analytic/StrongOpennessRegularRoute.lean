import Hironaka.Analytic.StrongOpennessFromRegularOhsawaTakegoshi
import Hironaka.Analytic.OhsawaTakegoshiRegularProof

set_option autoImplicit false

/-!
# Strong openness from the proved regular Ohsawa--Takegoshi theorem

The route to `IncreasingStrongOpenness n` is

  `OhsawaTakegoshiHyperplaneRegular`  (bounded convex domains, weights smooth and
                                       plurisubharmonic near the closure)
      ⟹ `OhsawaTakegoshiHyperplane`   (`Hironaka.StrongOpennessFromRegularOhsawaTakegoshi`)
      ⟹ `IncreasingStrongOpenness n` (`Hironaka.StrongOpennessFromOhsawaTakegoshi`)

and the regular case is now a theorem, `ohsawaTakegoshiHyperplaneRegular_proved`
(`Hironaka.OhsawaTakegoshiRegularProof`): Hörmander's `L²` estimate for `∂̄` on convex domains
with three weights (`Hironaka.HormanderL2Theorem`) and B.-Y. Chen's derivation of the
Ohsawa--Takegoshi extension from it (`Hironaka.OTRegularFromHormander`).  This module contains no
`sorry`.
-/

namespace Hironaka

/-- The Ohsawa--Takegoshi theorem, regular case. -/
theorem ohsawaTakegoshiHyperplaneRegular : OhsawaTakegoshiHyperplaneRegular :=
  ohsawaTakegoshiHyperplaneRegular_proved

/-- Strong openness for increasing sequences in every dimension. -/
theorem increasingStrongOpenness_ofRegularRoute (n : ℕ) : IncreasingStrongOpenness n :=
  increasingStrongOpenness_of_ohsawaTakegoshiRegular ohsawaTakegoshiHyperplaneRegular n

end Hironaka
