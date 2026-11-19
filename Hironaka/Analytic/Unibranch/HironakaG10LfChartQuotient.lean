import Hironaka.Analytic.Unibranch.HironakaG10LfQuotientCoker
import Hironaka.Analytic.Unibranch.HironakaG10MwWindowFamily

/-!
# `ChartFlat` in quotient form (lane G10LF, ALG-3 for G10GN's route N)

**`chartFlat_iff_flat_quotientCoker`**: lane G10MW's `ChartFlat d t F p I` (flatness over `𝒪_d ⧸ I` of
`(𝒪_d ⧸ I) ⊗ coker F`) is flatness over `𝒪_d ⧸ I` of `(𝒪_{d×t} ⧸ I 𝒪)ᵃ ⧸ range (F mod I 𝒪)`, with the
first-projection algebra `basePullback` (same local instance as `HironakaG10MwWindowFamily`).

No named input. BP: hironaka-g10lf-generic-freeness.tex.
-/

set_option autoImplicit false

namespace Hironaka.Analytic.Unibranch.HironakaG10LfChartQuotient

open Hironaka Hironaka OkaGermBridge
  Hironaka.Analytic.Unibranch.HironakaG10SmoothBaseFlatOpen

noncomputable section

local instance (d t : ℕ) :
    Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel d × ComplexModel t)) :=
  (basePullback d t).toAlgebra

local instance (d t : ℕ) (I : Ideal (HolGerm (ComplexModel d))) :
    Algebra (HolGerm (ComplexModel d) ⧸ I) (HolGerm (ComplexModel d × ComplexModel t) ⧸
      I.map (algebraMap (HolGerm (ComplexModel d)) (HolGerm (ComplexModel d × ComplexModel t)))) :=
  Ideal.Quotient.algebraQuotientMapQuotient

/-- **`ChartFlat` is flatness of the cokernel of `F` modulo `I 𝒪`.** -/
theorem chartFlat_iff_flat_quotientCoker (d t : ℕ) {a b : ℕ}
    (F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ) (p : ComplexModel d × ComplexModel t)
    (I : Ideal (HolGerm (ComplexModel d))) :
    HironakaG10MwWindowFamily.ChartFlat d t F p I ↔
      Module.Flat (HolGerm (ComplexModel d) ⧸ I)
        ((Fin a → HolGerm (ComplexModel d × ComplexModel t) ⧸
            I.map (algebraMap (HolGerm (ComplexModel d)) (HolGerm (ComplexModel d × ComplexModel t)))) ⧸
          LinearMap.range (Matrix.map (fun i j => germAt p (F i j) :
              Matrix (Fin a) (Fin b) (HolGerm (ComplexModel d × ComplexModel t)))
            (Ideal.Quotient.mk (I.map (algebraMap (HolGerm (ComplexModel d))
              (HolGerm (ComplexModel d × ComplexModel t)))))).mulVecLin) :=
  HironakaG10LfQuotientCoker.flat_baseChange_coker_iff I _

end

end Hironaka.Analytic.Unibranch.HironakaG10LfChartQuotient
