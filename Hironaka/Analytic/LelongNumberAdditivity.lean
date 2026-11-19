import Hironaka.Analytic.LelongNumberComparison
import Hironaka.Analytic.LelongNumberFiniteness
import Hironaka.Analytic.LelongNumberSubadditivity

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Arithmetic of Lelong numbers

Source: Demailly, *Complex analytic and differential geometry*, III.5 (the Lelong number as a
normalised mass, and Demailly's comparison theorem), III.7.

The development defines `lelongNumber u x` as the supremum of the `γ ≥ 0` admitting a bound
`u ≤ γ log ‖· - x‖ + C` on a punctured neighbourhood of `x`.  For a quasi-psh `u` this agrees
with the mass-theoretic Lelong number (Demailly III.5), and in that description the following
are immediate; in the sup-of-log-bounds description they are not, because an admissible
exponent for a sum need not split.  Only the two facts consumed by the non-nef locus argument
are recorded.

* `lelongNumber_add_le`: subadditivity.  (Equality holds; only `≤` is used.)  PROVED, from
  `Hironaka.LelongNumberSubadditivity`.  The sup-of-log-bounds description does not see it
  directly — the sphere-supremum functional is not additive — so the proof goes through the
  ball mean, whose slope is identified with the supremum's by a Harnack sandwich.
* `lelongNumber_ne_top`: PROVED, from `Hironaka.LelongNumberFiniteness`, which reduces it to
  Hadamard's three-circle inequality.  In positive dimension, a quasi-psh function that is not
  identically `-∞` has finite Lelong numbers.  BOTH extra hypotheses are essential.
  `ManifoldQuasiPlurisubharmonic` is the raw criterion and admits the identically `⊥` germ
  (`Hironaka.QuasiPshSingularities`), for which every exponent is admissible and the Lelong
  number is `⊤`; and in dimension `0` the punctured-neighbourhood filter is `⊥`, so every
  exponent is admissible for every function (compare
  `Hironaka.BlowupNonKahlerLocus.lelongNumber_pos_of_dim_eq_zero`).

No module in the root import closure imports this file.
-/

open Set Filter
open scoped Topology ENNReal

namespace Hironaka.LelongNumberAdditivity

open Hironaka.NonKahlerLocus

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **Demailly, CADG III.5.**  Lelong numbers are subadditive.  Equality holds; only `≤` is
recorded, because only `≤` is used.  Proved in `Hironaka.LelongNumberSubadditivity`. -/
theorem lelongNumber_add_le {u v : M → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := n) u)
    (hv : ManifoldQuasiPlurisubharmonic (n := n) v) (x : M) :
    lelongNumber (n := n) (fun y => u y + v y) x ≤
      lelongNumber (n := n) u x + lelongNumber (n := n) v x :=
  LelongNumberSubadditivity.lelongNumber_add_le_of_quasiPsh hu hv x

/-- **Demailly, CADG III.5.**  In positive dimension, a quasi-psh function which is not
identically `-∞` has finite Lelong numbers.  Neither hypothesis can be dropped: the identically
`⊥` germ satisfies `ManifoldQuasiPlurisubharmonic` and has Lelong number `⊤`, and in dimension
`0` every function has Lelong number `⊤`.  Proved in `Hironaka.LelongNumberFiniteness`. -/
theorem lelongNumber_ne_top (hn : 0 < n) {u : M → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := n) u)
    (hnd : LocallyNondegenerate u) (x : M) :
    lelongNumber (n := n) u x ≠ ⊤ :=
  LelongNumberFiniteness.lelongNumber_ne_top_of_quasiPsh hn hu hnd x

end

end Hironaka.LelongNumberAdditivity
