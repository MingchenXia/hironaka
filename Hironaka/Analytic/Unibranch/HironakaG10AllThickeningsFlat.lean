import Hironaka.Analytic.Unibranch.HironakaG10MatrixQuotientBaseFlattener
import Hironaka.Resolution.HironakaActualWholeIdealJetDetection
import Hironaka.Resolution.HironakaG10ArtinianFlatQuotient

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10AllThickeningsFlat
open Hironaka Hironaka
  HolGerm HironakaRelativeNormalIdeal HironakaHolomorphicJetChartInvariance
  HironakaActualWholeIdealJetDetection HironakaG10ArtinianFlatQuotient HironakaG10ArtinianBaseChange
  HironakaChowPresentationIndependentFlattener HironakaG10HirFlatQuotient
  HironakaG10HirChartFlattener
  Hironaka.Analytic.Unibranch.HironakaG10MatrixSmoothBaseFlattener
  Hironaka.Analytic.Unibranch.HironakaG10ReassociatedSquareZeroIdeal
  Hironaka.Analytic.Unibranch.HironakaG10MatrixQuotientBaseFlattener
noncomputable section
local instance (d t : ℕ) : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
  tangentAlgebra d t

theorem matrix_flat_of_all_truncated_flat (d t a : ℕ) {b : ℕ}
    (F : Matrix (Fin a) (Fin b) (HolGerm (ComplexModel (d+t))))
    (I : Ideal (HolGerm (ComplexModel d)))
    (hflat : I ≠ ⊤ → ∀ q : ℕ,
      Module.Flat (HolGerm (ComplexModel d) ⧸ truncatedParameterIdeal d q I)
        ((HolGerm (ComplexModel d) ⧸ truncatedParameterIdeal d q I) ⊗[HolGerm (ComplexModel d)]
          ((Fin a → HolGerm (ComplexModel (d+t))) ⧸ LinearMap.range F.mulVecLin))) :
    Module.Flat (HolGerm (ComplexModel d) ⧸ I)
      ((HolGerm (ComplexModel d) ⧸ I) ⊗[HolGerm (ComplexModel d)]
        ((Fin a → HolGerm (ComplexModel (d+t))) ⧸ LinearMap.range F.mulVecLin)) := by
  classical
  let R := HolGerm (ComplexModel d)
  let M := (Fin a → HolGerm (ComplexModel (d+t))) ⧸ LinearMap.range F.mulVecLin
  have hcriterion (J : Ideal R) : Module.Flat (R ⧸ J) ((R ⧸ J) ⊗[R] M) ↔
      matrixFlattenerIdeal d t a F ≤ J := by
    have hf := (isFlattenerIdeal_chartMap d (t+a) (reassociatedSquareZeroIdeal d t a F)) J
    change (quotMap (chartMap d (t+a) (reassociatedSquareZeroIdeal d t a F)) J).Flat ↔ _ at hf
    exact (chartMap_quot_flat_iff_tensor_matrix d t a F J).symm.trans hf
  apply (hcriterion I).mpr
  by_cases hI : I = ⊤
  · rw [hI]
    exact le_top
  intro g hg
  apply (mem_original_ideal_iff_all_positive_thickenings I g).mpr
  intro q
  exact (hcriterion (truncatedParameterIdeal d q I)).mp (hflat hI q) hg
end
end Hironaka.Analytic.Unibranch.HironakaG10AllThickeningsFlat
