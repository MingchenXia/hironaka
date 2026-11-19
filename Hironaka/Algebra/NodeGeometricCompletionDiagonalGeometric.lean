import Hironaka.Algebra.NodeGeometricCompletionDiagonalPoint
import Hironaka.Algebra.NodeGeometricCompletionTensorLocalization

/-! The ACTUAL diagonal local neighbourhood at the SAME selected tensor-kernel point. -/

noncomputable section

open IsLocalRing TensorProduct

namespace Hironaka.Algebra.NodeGeometricCompletionDiagonalGeometric


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000
set_option quotPrecheck false

universe u
variable (K R L : Type u) [Field K] [CommRing R] [IsLocalRing R] [Algebra K R]
  [Field L] [Algebra (ResidueField R) L] [Algebra K L] [IsScalarTower K (ResidueField R) L]

local notation "κ" => ResidueField R
local notation "D" => NodeGeometricCompletionDiagonalPoint.TensorRing K R
local notation "T" => NodeGeometricCompletionDiagonalPoint.DiagonalLocal K R

attribute [local instance] Algebra.TensorProduct.rightAlgebra NodeGeometricCompletionDiagonalPoint.diagonalPoint_isMaximal
  NodeGeometricCompletionDiagonalPoint.pointFieldAlgebra NodeGeometricCompletionDiagonalPoint.originalAlgebra

/-- The selected diagonal coefficient evaluation uses the SAME actual residue embedding. -/
def diagonalEvaluation : D →ₐ[κ] L :=
  (IsScalarTower.toAlgHom κ κ L).comp (NodeGeometricCompletionDiagonalPoint.augmentation K R)

omit [Algebra K L] [IsScalarTower K κ L] in
/-- Every original diagonal denominator has a unit image, derived internally. -/
theorem diagonal_denominator_unit (s : (NodeGeometricCompletionDiagonalPoint.diagonalPoint K R).primeCompl) :
    IsUnit (diagonalEvaluation K R L s) :=
  (NodeGeometricCompletionDiagonalPoint.augmentation_denominator_unit K R s).map (algebraMap κ L)

/-- The selected original local evaluation, over the SAME actual original field. -/
def originalEvaluation : R →ₐ[K] L where
  toRingHom := (algebraMap κ L).comp (residue R)
  commutes' k := by
    change algebraMap κ L (algebraMap K κ k) = algebraMap K L k
    exact (IsScalarTower.algebraMap_apply K κ L k).symm

/-- The actual original geometric tensor augmentation. -/
def originalAugmentation : (L ⊗[K] R) →ₐ[L] L :=
  AlgHom.liftEquiv K L R L (originalEvaluation K R L)

/-- The entire native cancellation retains the SAME original K and prescribed κ coefficients. -/
def cancelEquiv : (L ⊗[κ] D) ≃ₐ[L] (L ⊗[K] R) :=
  Algebra.TensorProduct.cancelBaseChange K κ L L R

/-- Every actual iterated pure tensor retains exactly the prescribed original augmentation. -/
theorem augmentation_cancel_tmul (l : L) (a : κ) (r : R) :
    originalAugmentation K R L (cancelEquiv K R L (l ⊗ₜ[κ] (a ⊗ₜ[K] r))) =
      NodeGeometricCompletionTensorLocalization.augmentation κ D L (diagonalEvaluation K R L) (l ⊗ₜ[κ] (a ⊗ₜ[K] r)) := by
  change (a • l) * algebraMap κ L (residue R r) = l * algebraMap κ L (a * residue R r)
  rw [map_mul]
  simp only [Algebra.smul_def, mul_left_comm, mul_assoc]

/-- The WHOLE actual augmentation triangle commutes, not only selected generators. -/
theorem augmentation_cancel :
    (originalAugmentation K R L).comp (cancelEquiv K R L).toAlgHom =
      NodeGeometricCompletionTensorLocalization.augmentation κ D L (diagonalEvaluation K R L) := by
  apply AlgHom.ext
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul l d =>
      induction d using TensorProduct.induction_on with
      | zero => simp
      | tmul a r => exact augmentation_cancel_tmul K R L l a r
      | add d e hd he => simpa only [tmul_add, map_add] using congrArg₂ (· + ·) hd he
  | add t s ht hs => simpa only [map_add] using congrArg₂ (· + ·) ht hs

/-- The SAME actual original geometric point, as its literal augmentation kernel. -/
def originalPoint : Ideal (L ⊗[K] R) := RingHom.ker (originalAugmentation K R L).toRingHom

/-- Its native maximality is internally derived from the entire external field action. -/
theorem originalPoint_isMaximal : (originalPoint K R L).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (originalAugmentation K R L) (by
    intro l
    exact ⟨algebraMap L (L ⊗[K] R) l, (originalAugmentation K R L).commutes l⟩)

attribute [local instance] originalPoint_isMaximal NodeGeometricCompletionTensorLocalization.originalPoint_isMaximal
  NodeGeometricCompletionTensorLocalization.localizedPoint_isMaximal

/-- Exact WHOLE selected kernel contraction through the SAME actual tensor cancellation. -/
theorem originalPoint_comap :
    (originalPoint K R L).comap (cancelEquiv K R L).toRingHom =
      NodeGeometricCompletionTensorLocalization.originalPoint κ D L (diagonalEvaluation K R L) := by
  change RingHom.ker ((originalAugmentation K R L).comp (cancelEquiv K R L).toAlgHom).toRingHom = _
  rw [augmentation_cancel]
  rfl

/-- The actual prime complements, in their entirety, are preserved by this SAME coefficient map. -/
theorem primeCompl_map :
    Submonoid.map (cancelEquiv K R L)
      (NodeGeometricCompletionTensorLocalization.originalPoint κ D L (diagonalEvaluation K R L)).primeCompl =
        (originalPoint K R L).primeCompl := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    change cancelEquiv K R L z ∉ originalPoint K R L
    change z ∉ NodeGeometricCompletionTensorLocalization.originalPoint κ D L (diagonalEvaluation K R L) at hz
    rw [← originalPoint_comap] at hz
    exact hz
  · intro hy
    change y ∉ originalPoint K R L at hy
    refine ⟨(cancelEquiv K R L).symm y, ?_, (cancelEquiv K R L).apply_symm_apply y⟩
    change (cancelEquiv K R L).symm y ∉ NodeGeometricCompletionTensorLocalization.originalPoint κ D L (diagonalEvaluation K R L)
    rw [← originalPoint_comap]
    change cancelEquiv K R L ((cancelEquiv K R L).symm y) ∉ originalPoint K R L
    simpa only [AlgEquiv.apply_symm_apply] using hy

/-- The actual original geometric local ring at its internally selected kernel point. -/
abbrev OriginalGeometricStalk := Localization.AtPrime (originalPoint K R L)

/-- The actual iterated-tensor local ring at its internally selected kernel point. -/
abbrev IteratedGeometricStalk :=
  Localization.AtPrime (NodeGeometricCompletionTensorLocalization.originalPoint κ D L (diagonalEvaluation K R L))

/-- Native localization under the whole cancellation isomorphism retains the SAME external field. -/
def cancelStalkEquiv : IteratedGeometricStalk K R L ≃ₐ[L] OriginalGeometricStalk K R L :=
  IsLocalization.algEquivOfAlgEquiv (IteratedGeometricStalk K R L)
    (OriginalGeometricStalk K R L) (cancelEquiv K R L) (primeCompl_map K R L)

/-- The actual geometric local ring of the SAME diagonal neighbourhood and selected embedding. -/
abbrev DiagonalGeometricStalk :=
  NodeGeometricCompletionTensorLocalization.LocalizedStalk κ D (NodeGeometricCompletionDiagonalPoint.diagonalPoint K R).primeCompl T L
    (diagonalEvaluation K R L) (diagonal_denominator_unit K R L)

/-- The SAME original selected geometric stalk is the ACTUAL selected diagonal-neighbourhood stalk. -/
def geometricStalkEquiv : OriginalGeometricStalk K R L ≃ₐ[L] DiagonalGeometricStalk K R L :=
  (cancelStalkEquiv K R L).symm.trans
    (NodeGeometricCompletionTensorLocalization.stalkEquiv κ D (NodeGeometricCompletionDiagonalPoint.diagonalPoint K R).primeCompl T L
      (diagonalEvaluation K R L) (diagonal_denominator_unit K R L))

/-- The cancellation stalk equivalence retains EVERY original pure-tensor representative. -/
theorem cancelStalkEquiv_tmul (l : L) (r : R) :
    cancelStalkEquiv K R L
      (algebraMap (L ⊗[κ] D) (IteratedGeometricStalk K R L) (l ⊗ₜ[κ] ((1 : κ) ⊗ₜ[K] r))) =
      algebraMap (L ⊗[K] R) (OriginalGeometricStalk K R L) (l ⊗ₜ[K] r) := by
  change IsLocalization.algEquivOfAlgEquiv (IteratedGeometricStalk K R L)
    (OriginalGeometricStalk K R L) (cancelEquiv K R L) (primeCompl_map K R L) _ = _
  rw [IsLocalization.algEquivOfAlgEquiv_eq]
  change algebraMap (L ⊗[K] R) (OriginalGeometricStalk K R L)
    (((1 : κ) • l) ⊗ₜ[K] r) = _
  rw [one_smul]

/-- Every original scalar and local germ retain exactly the SAME actual diagonal-localization image. -/
theorem geometricStalkEquiv_tmul (l : L) (r : R) :
    geometricStalkEquiv K R L
      (algebraMap (L ⊗[K] R) (OriginalGeometricStalk K R L) (l ⊗ₜ[K] r)) =
      algebraMap (L ⊗[κ] T) (DiagonalGeometricStalk K R L)
        (l ⊗ₜ[κ] algebraMap R T r) := by
  rw [← cancelStalkEquiv_tmul K R L l r]
  change NodeGeometricCompletionTensorLocalization.stalkEquiv κ D
    (NodeGeometricCompletionDiagonalPoint.diagonalPoint K R).primeCompl T L
    (diagonalEvaluation K R L) (diagonal_denominator_unit K R L)
    ((cancelStalkEquiv K R L).symm (cancelStalkEquiv K R L _)) = _
  rw [AlgEquiv.symm_apply_apply]
  exact NodeGeometricCompletionTensorLocalization.stalkEquiv_tmul κ D
    (NodeGeometricCompletionDiagonalPoint.diagonalPoint K R).primeCompl T L
    (diagonalEvaluation K R L) (diagonal_denominator_unit K R L) l ((1 : κ) ⊗ₜ[K] r)

local instance geometricStalkEquiv_isLocalHom : IsLocalHom (geometricStalkEquiv K R L).toRingHom :=
  CompletionLocalMap.instIsLocalHomRingEquivToRingHom (geometricStalkEquiv K R L).toRingEquiv

/-- The SAME actual selected completed geometric stalks are equivalent over the entire original external field. -/
def completedGeometricStalkEquiv :
    AdicCompletion (maximalIdeal (OriginalGeometricStalk K R L)) (OriginalGeometricStalk K R L) ≃ₐ[L]
      AdicCompletion (maximalIdeal (DiagonalGeometricStalk K R L)) (DiagonalGeometricStalk K R L) := by
  refine AlgEquiv.ofRingEquiv
    (f := CompletionLocalMap.completionEquiv (geometricStalkEquiv K R L).toRingEquiv) ?_
  intro l
  change CompletionLocalMap.completionMap (geometricStalkEquiv K R L).toRingHom
    (algebraMap (OriginalGeometricStalk K R L) (AdicCompletion _ _)
      (algebraMap L (OriginalGeometricStalk K R L) l)) = _
  rw [CompletionLocalMap.completionMap_algebraMap]
  exact congrArg (algebraMap (DiagonalGeometricStalk K R L) (AdicCompletion _ _))
    ((geometricStalkEquiv K R L).commutes l)

/-- The WHOLE completed map is the native completion of the SAME actual local-ring map. -/
theorem completedGeometricStalkEquiv_toRingHom :
    (completedGeometricStalkEquiv K R L).toRingHom =
      CompletionLocalMap.completionMap (geometricStalkEquiv K R L).toRingHom := rfl

/-- EVERY original selected local representative retains its SAME actual completion image. -/
theorem completedGeometricStalkEquiv_original (r : OriginalGeometricStalk K R L) :
    completedGeometricStalkEquiv K R L (algebraMap _ (AdicCompletion _ _) r) =
      algebraMap _ (AdicCompletion _ _) (geometricStalkEquiv K R L r) :=
  CompletionLocalMap.completionMap_algebraMap (geometricStalkEquiv K R L).toRingHom r

end Hironaka.Algebra.NodeGeometricCompletionDiagonalGeometric
