import Hironaka.Analytic.DemaillyRegularizedMaxBergmanDataInterface

set_option autoImplicit false

/-!
# Demailly regularization of Kähler currents: the superseded Bergman route (retired)

This module used to export the global Kähler-current consequence of Demailly's
Bergman-kernel regularization from the finite regularized-max Bergman chart-frame
package of `DemaillyRegularizedMaxBergmanDataInterface`.  That route is superseded:
`KahlerCurrentRegularization.exists_kahlerCurrent_poleSet_subset_lelongNumber_pos`
is proved from Demailly's approximation theorem
(`KahlerCurrentRegularizationAlgebraicApproximation`), and the theorem that lived here
had no consumer.  It was deleted under the human decision I-0902 item 2 (I-0826: retire
the superseded record #7 and the code that only serves it; coordination I-0913).

The import is kept so that the structures of the Bergman route, which other modules
still use, stay reachable from `KahlerCurrentRegularization` (I-0459).
-/
