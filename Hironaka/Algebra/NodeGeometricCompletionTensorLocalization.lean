import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Hironaka.Algebra.CompletionLocalMap

/-! The SAME actual augmentation point after tensoring an actual localization. -/

noncomputable section

open TensorProduct

namespace Hironaka.Algebra.NodeGeometricCompletionTensorLocalization

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000

universe u v w z
variable (K : Type u) [CommRing K] (B : Type v) [CommRing B] [Algebra K B]
  (M : Submonoid B) (T : Type w) [CommRing T] [Algebra K T] [Algebra B T]
  [IsScalarTower K B T] [IsLocalization M T]
  (L : Type z) [Field L] [Algebra K L]
  (b : B →ₐ[K] L) (hu : ∀ s : M, IsUnit (b s))

/-- The actual selected coefficient evaluation extends through the SAME original localization. -/
def localizedEvaluation : T →ₐ[K] L := IsLocalization.liftAlgHom hu

/-- Every original representative retains precisely its actual selected coefficient image. -/
theorem localizedEvaluation_original (r : B) :
    localizedEvaluation K B M T L b hu (algebraMap B T r) = b r :=
  IsLocalization.lift_eq hu r

/-- The literal original tensor augmentation at the selected coefficient map. -/
def augmentation : (L ⊗[K] B) →ₐ[L] L := AlgHom.liftEquiv K L B L b

/-- The literal localization tensor augmentation at the SAME selected coefficient map. -/
def localizedAugmentation : (L ⊗[K] T) →ₐ[L] L :=
  AlgHom.liftEquiv K L T L (localizedEvaluation K B M T L b hu)

/-- The actual tensor of the ORIGINAL localization map, with its SAME external coefficients. -/
def tensorMap : (L ⊗[K] B) →ₐ[L] (L ⊗[K] T) where
  toRingHom := (Algebra.TensorProduct.map (AlgHom.id K L)
    (IsScalarTower.toAlgHom K B T)).toRingHom
  commutes' l := by simp

/-- Every original pure tensor has its literal native localization image. -/
theorem tensorMap_tmul (l : L) (r : B) :
    tensorMap K B T L (l ⊗ₜ[K] r) = l ⊗ₜ[K] algebraMap B T r := rfl

/-- The entire actual tensor augmentation triangle commutes. -/
theorem augmentation_triangle :
    (localizedAugmentation K B M T L b hu).comp (tensorMap K B T L) =
      augmentation K B L b := by
  apply AlgHom.ext
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul l r =>
      change l * localizedEvaluation K B M T L b hu (algebraMap B T r) = l * b r
      rw [localizedEvaluation_original]
  | add t s ht hs =>
      simp only [map_add, ht, hs]

/-- The actual tensor map supplies the SAME original tensor coefficient action. -/
@[instance_reducible]
def tensorAlgebra : Algebra (L ⊗[K] B) (L ⊗[K] T) :=
  (tensorMap K B T L).toAlgebra

attribute [local instance] tensorAlgebra

/-- All actual external coefficients retain their original tensor action. -/
theorem tensor_scalarTower : IsScalarTower L (L ⊗[K] B) (L ⊗[K] T) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext fun l =>
    ((tensorMap K B T L).commutes l).symm)

attribute [local instance] tensor_scalarTower

/-- The actual tensor base change is internally the localization at the actual image denominators. -/
theorem tensor_isLocalization :
    IsLocalization (M.map (Algebra.TensorProduct.includeRight (R := K) (A := L)))
      (L ⊗[K] T) := by
  apply IsLocalization.tensorProduct_tensorProduct_right K L M T
  ext r
  rfl

attribute [local instance] tensor_isLocalization

/-- The first selected point is the actual original tensor augmentation kernel. -/
def originalPoint : Ideal (L ⊗[K] B) := RingHom.ker (augmentation K B L b).toRingHom

/-- Its maximality follows internally from EVERY actual external coefficient. -/
theorem originalPoint_isMaximal : (originalPoint K B L b).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (augmentation K B L b) (by
    intro l
    exact ⟨algebraMap L (L ⊗[K] B) l, (augmentation K B L b).commutes l⟩)

/-- The second selected point is the SAME actual localization tensor augmentation kernel. -/
def localizedPoint : Ideal (L ⊗[K] T) :=
  RingHom.ker (localizedAugmentation K B M T L b hu).toRingHom

/-- Its maximality also follows internally, with no residue-point certificate. -/
theorem localizedPoint_isMaximal : (localizedPoint K B M T L b hu).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (localizedAugmentation K B M T L b hu) (by
    intro l
    exact ⟨algebraMap L (L ⊗[K] T) l,
      (localizedAugmentation K B M T L b hu).commutes l⟩)

attribute [local instance] originalPoint_isMaximal localizedPoint_isMaximal

/-- The actual selected localization point contracts to the SAME original tensor point. -/
theorem localizedPoint_comap :
    (localizedPoint K B M T L b hu).comap
      (algebraMap (L ⊗[K] B) (L ⊗[K] T)) = originalPoint K B L b := by
  change RingHom.ker ((localizedAugmentation K B M T L b hu).comp
    (tensorMap K B T L)).toRingHom = _
  rw [augmentation_triangle]
  rfl

/-- The actual local ring at the SAME localization tensor point. -/
abbrev LocalizedStalk := Localization.AtPrime (localizedPoint K B M T L b hu)

/-- Native iterated localization makes this SAME local ring the ORIGINAL selected localization. -/
theorem stalk_isLocalization :
    IsLocalization.AtPrime (LocalizedStalk K B M T L b hu) (originalPoint K B L b) := by
  have h := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (M.map (Algebra.TensorProduct.includeRight (R := K) (A := L)))
    (LocalizedStalk K B M T L b hu) (localizedPoint K B M T L b hu)
  simpa only [localizedPoint_comap] using h

attribute [local instance] stalk_isLocalization

/-- The actual selected stalk equivalence, over the SAME original external field. -/
def stalkEquiv :
    Localization.AtPrime (originalPoint K B L b) ≃ₐ[L] LocalizedStalk K B M T L b hu :=
  (IsLocalization.algEquiv (originalPoint K B L b).primeCompl
    (Localization.AtPrime (originalPoint K B L b))
    (LocalizedStalk K B M T L b hu)).restrictScalars L

/-- Every original tensor representative retains the SAME actual tensor/localization image. -/
theorem stalkEquiv_original (t : L ⊗[K] B) :
    stalkEquiv K B M T L b hu
      (algebraMap (L ⊗[K] B) (Localization.AtPrime (originalPoint K B L b)) t) =
      algebraMap (L ⊗[K] B) (LocalizedStalk K B M T L b hu) t :=
  (IsLocalization.algEquiv (originalPoint K B L b).primeCompl
    (Localization.AtPrime (originalPoint K B L b))
    (LocalizedStalk K B M T L b hu)).commutes t

/-- Every pure tensor retains precisely its actual tensor followed by localization image. -/
theorem stalkEquiv_tmul (l : L) (r : B) :
    stalkEquiv K B M T L b hu
      (algebraMap (L ⊗[K] B) (Localization.AtPrime (originalPoint K B L b)) (l ⊗ₜ[K] r)) =
      algebraMap (L ⊗[K] T) (LocalizedStalk K B M T L b hu)
        (l ⊗ₜ[K] algebraMap B T r) := by
  rw [stalkEquiv_original,
    IsScalarTower.algebraMap_eq (L ⊗[K] B) (L ⊗[K] T) (LocalizedStalk K B M T L b hu)]
  rfl

local instance stalkEquiv_isLocalHom : IsLocalHom (stalkEquiv K B M T L b hu).toRingHom :=
  CompletionLocalMap.instIsLocalHomRingEquivToRingHom (stalkEquiv K B M T L b hu).toRingEquiv

/-- Completion of these SAME actual selected stalks preserves the entire original external field. -/
def completedStalkEquiv :
    AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime (originalPoint K B L b)))
      (Localization.AtPrime (originalPoint K B L b)) ≃ₐ[L]
    AdicCompletion (IsLocalRing.maximalIdeal (LocalizedStalk K B M T L b hu))
      (LocalizedStalk K B M T L b hu) := by
  refine AlgEquiv.ofRingEquiv
    (f := CompletionLocalMap.completionEquiv (stalkEquiv K B M T L b hu).toRingEquiv) ?_
  intro l
  change CompletionLocalMap.completionMap (stalkEquiv K B M T L b hu).toRingHom
    (algebraMap (Localization.AtPrime (originalPoint K B L b))
      (AdicCompletion _ _) (algebraMap L (Localization.AtPrime (originalPoint K B L b)) l)) = _
  rw [CompletionLocalMap.completionMap_algebraMap]
  exact congrArg (algebraMap (LocalizedStalk K B M T L b hu) (AdicCompletion _ _))
    ((stalkEquiv K B M T L b hu).commutes l)

/-- The ENTIRE completed equivalence is exactly the completion of the SAME actual stalk map. -/
theorem completedStalkEquiv_toRingHom :
    (completedStalkEquiv K B M T L b hu).toRingHom =
      CompletionLocalMap.completionMap (stalkEquiv K B M T L b hu).toRingHom := rfl

/-- Every actual selected local representative retains its original completion image. -/
theorem completedStalkEquiv_original (r : Localization.AtPrime (originalPoint K B L b)) :
    completedStalkEquiv K B M T L b hu (algebraMap _ (AdicCompletion _ _) r) =
      algebraMap _ (AdicCompletion _ _) (stalkEquiv K B M T L b hu r) :=
  CompletionLocalMap.completionMap_algebraMap (stalkEquiv K B M T L b hu).toRingHom r

end Hironaka.Algebra.NodeGeometricCompletionTensorLocalization
