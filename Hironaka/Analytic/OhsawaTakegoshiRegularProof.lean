import Hironaka.Analytic.OTRegularFromHormander
import Hironaka.Analytic.HormanderL2Theorem

set_option autoImplicit false

/-!
# The regular Ohsawa--Takegoshi theorem, unconditionally

`ohsawaTakegoshiHyperplaneRegular_proved` combines Hörmander's `L²` estimate
(`Hormander.hormanderL2Estimate`, `Hironaka.HormanderL2Theorem`) with Chen's derivation of the
Ohsawa--Takegoshi extension theorem from it (`ohsawaTakegoshiHyperplaneRegular_of_hormander`,
`Hironaka.OTRegularFromHormander`).  The Weyl lemma for `∂̄` enters through
`Hironaka.WeakDbarWeyl`.
-/

namespace Hironaka

/-- **The Ohsawa--Takegoshi theorem, regular case.** -/
theorem ohsawaTakegoshiHyperplaneRegular_proved : OhsawaTakegoshiHyperplaneRegular :=
  ohsawaTakegoshiHyperplaneRegular_of_hormander Hormander.hormanderL2Estimate

end Hironaka
