import Hironaka.Algebra.NodeGeometricCompletionDiagonalGeometric
import Hironaka.Algebra.NodeGeometricCompletionRationalJets

/-! The ACTUAL diagonal geometric point and EVERY actual rational finite jet. -/

noncomputable section

open IsLocalRing TensorProduct

namespace Hironaka.Algebra.NodeGeometricCompletionDiagonalJets

open NodeGeometricCompletionDiagonalGeometric

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000
set_option quotPrecheck false

universe u
variable (K R L : Type u) [Field K] [CommRing R] [IsLocalRing R] [Algebra K R]
  [Field L] [Algebra (ResidueField R) L]

local notation "κ" => ResidueField R
local notation "D" => NodeGeometricCompletionDiagonalPoint.TensorRing K R
local notation "T" => NodeGeometricCompletionDiagonalPoint.DiagonalLocal K R
local notation "B" => L ⊗[κ] T
local notation "G" => DiagonalGeometricStalk K R L
local notation "M" => (NodeGeometricCompletionDiagonalPoint.diagonalPoint K R).primeCompl

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  NodeGeometricCompletionDiagonalPoint.diagonalPoint_isMaximal
  NodeGeometricCompletionDiagonalPoint.pointFieldAlgebra
  NodeGeometricCompletionDiagonalPoint.originalAlgebra
  NodeGeometricCompletionTensorLocalization.localizedPoint_isMaximal

/-- The actual localization lift is the WHOLE original diagonal residue map followed by the prescribed embedding. -/
theorem localizedEvaluation_eq :
    (NodeGeometricCompletionTensorLocalization.localizedEvaluation κ D M T L
      (diagonalEvaluation K R L) (diagonal_denominator_unit K R L)).toRingHom =
        (algebraMap κ L).comp (NodeGeometricCompletionDiagonalPoint.residueLift K R) := by
  apply IsLocalization.ringHom_ext M
  apply RingHom.ext
  intro d
  change NodeGeometricCompletionTensorLocalization.localizedEvaluation κ D M T L
    (diagonalEvaluation K R L) (diagonal_denominator_unit K R L) (algebraMap D T d) =
      algebraMap κ L (NodeGeometricCompletionDiagonalPoint.residueLift K R (algebraMap D T d))
  rw [NodeGeometricCompletionTensorLocalization.localizedEvaluation_original,
    NodeGeometricCompletionDiagonalPoint.residueLift_tensor]
  rfl

/-- The literal extended actual diagonal maximal ideal. -/
abbrev rationalPoint : Ideal B :=
  NodeGeometricCompletionRationalJets.tensorPoint κ L (maximalIdeal T)

/-- Its maximality is DERIVED from the actual native diagonal residue quotient, not supplied. -/
theorem rationalPoint_isMaximal : (rationalPoint K R L).IsMaximal :=
  NodeGeometricCompletionRationalJets.tensorPoint_isMaximal κ L (maximalIdeal T)
    (NodeGeometricCompletionDiagonalPoint.localResidueQuotientEquiv K R)

attribute [local instance] rationalPoint_isMaximal

/-- The SAME actual rational tensor residue augmentation, constructed from the actual quotient. -/
def rationalAugmentation : B →ₐ[L] L :=
  (NodeGeometricCompletionRationalJets.tensorResidueEquiv κ L (maximalIdeal T)
    (NodeGeometricCompletionDiagonalPoint.localResidueQuotientEquiv K R)).toAlgHom.comp
      (Ideal.Quotient.mkₐ L (rationalPoint K R L))

/-- Every tensor representative has the SAME prescribed original diagonal residue value. -/
theorem rationalAugmentation_tmul (l : L) (t : T) :
    rationalAugmentation K R L (l ⊗ₜ[κ] t) =
      NodeGeometricCompletionDiagonalPoint.residueLift K R t • l := by
  change Algebra.TensorProduct.rid κ L L
    (l ⊗ₜ[κ] (NodeGeometricCompletionDiagonalPoint.localResidueQuotientEquiv K R
      (Ideal.Quotient.mk (maximalIdeal T) t))) = _
  rw [NodeGeometricCompletionDiagonalPoint.localResidueQuotientEquiv_mk,
    Algebra.TensorProduct.rid_tmul]

/-- The WHOLE actual localized augmentation is the SAME canonical rational quotient augmentation. -/
theorem localizedAugmentation_eq :
    NodeGeometricCompletionTensorLocalization.localizedAugmentation κ D M T L
      (diagonalEvaluation K R L) (diagonal_denominator_unit K R L) =
        rationalAugmentation K R L := by
  apply AlgHom.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l t =>
      rw [rationalAugmentation_tmul]
      change l * NodeGeometricCompletionTensorLocalization.localizedEvaluation κ D M T L
        (diagonalEvaluation K R L) (diagonal_denominator_unit K R L) t =
          NodeGeometricCompletionDiagonalPoint.residueLift K R t • l
      have h := RingHom.congr_fun (localizedEvaluation_eq K R L) t
      change NodeGeometricCompletionTensorLocalization.localizedEvaluation κ D M T L
        (diagonalEvaluation K R L) (diagonal_denominator_unit K R L) t =
          algebraMap κ L (NodeGeometricCompletionDiagonalPoint.residueLift K R t) at h
      rw [h, Algebra.smul_def, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The selected actual augmentation kernel is EXACTLY the extended actual maximal ideal. -/
theorem selectedPoint_eq_rationalPoint :
    NodeGeometricCompletionTensorLocalization.localizedPoint κ D M T L
      (diagonalEvaluation K R L) (diagonal_denominator_unit K R L) = rationalPoint K R L := by
  apply Ideal.ext
  intro a
  change NodeGeometricCompletionTensorLocalization.localizedAugmentation κ D M T L
    (diagonalEvaluation K R L) (diagonal_denominator_unit K R L) a = 0 ↔ a ∈ rationalPoint K R L
  rw [localizedAugmentation_eq]
  let e := NodeGeometricCompletionRationalJets.tensorResidueEquiv κ L (maximalIdeal T)
    (NodeGeometricCompletionDiagonalPoint.localResidueQuotientEquiv K R)
  change e (Ideal.Quotient.mk (rationalPoint K R L) a) = 0 ↔ a ∈ rationalPoint K R L
  constructor
  · intro ha
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply e.injective
    simpa only [map_zero] using ha
  · intro ha
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]

/-- This SAME actual geometric local ring is internally localized at the exact rational ideal. -/
theorem selectedStalk_isLocalization : IsLocalization.AtPrime G (rationalPoint K R L) := by
  have h : (rationalPoint K R L).primeCompl =
      (NodeGeometricCompletionTensorLocalization.localizedPoint κ D M T L
        (diagonalEvaluation K R L) (diagonal_denominator_unit K R L)).primeCompl := by
    ext x
    change x ∉ rationalPoint K R L ↔ x ∉
      NodeGeometricCompletionTensorLocalization.localizedPoint κ D M T L
        (diagonalEvaluation K R L) (diagonal_denominator_unit K R L)
    rw [selectedPoint_eq_rationalPoint]
  let P (m : Submonoid B) : Prop := IsLocalization m G
  have hP : P (NodeGeometricCompletionTensorLocalization.localizedPoint κ D M T L
    (diagonalEvaluation K R L) (diagonal_denominator_unit K R L)).primeCompl :=
      inferInstanceAs (IsLocalization
    (NodeGeometricCompletionTensorLocalization.localizedPoint κ D M T L
      (diagonalEvaluation K R L) (diagonal_denominator_unit K R L)).primeCompl G)
  exact Eq.mp (congrArg P h.symm) hP

attribute [local instance] selectedStalk_isLocalization

/-- Every actual extended ideal power is exactly the SAME selected local maximal-ideal power. -/
theorem jetIdeal_eq (n : ℕ) :
    (rationalPoint K R L ^ n).map (algebraMap B G) = maximalIdeal G ^ n := by
  rw [Ideal.map_pow, IsLocalization.AtPrime.map_eq_maximalIdeal]

/-- EVERY original finite jet after the prescribed field extension is the SAME actual selected stalk jet. -/
def jetEquiv (n : ℕ) :
    (L ⊗[κ] (T ⧸ maximalIdeal T ^ n)) ≃ₐ[L] (G ⧸ maximalIdeal G ^ n) :=
  (NodeGeometricCompletionRationalJets.tensorJetEquiv κ L (maximalIdeal T) n).trans
    (((NodeGeometricCompletionLocalizedJets.powerQuotientEquiv
      (rationalPoint K R L) G n).restrictScalars L).trans
        (Ideal.quotientEquivAlgOfEq L (jetIdeal_eq K R L n)))

/-- Every original local representative and external coefficient retain the literal actual localization class. -/
theorem jetEquiv_tmul (n : ℕ) (l : L) (t : T) :
    jetEquiv K R L n (l ⊗ₜ[κ] Ideal.Quotient.mk (maximalIdeal T ^ n) t) =
      Ideal.Quotient.mk (maximalIdeal G ^ n) (algebraMap B G (l ⊗ₜ[κ] t)) := by
  change (Ideal.quotientEquivAlgOfEq L (jetIdeal_eq K R L n))
    (NodeGeometricCompletionLocalizedJets.powerQuotientEquiv (rationalPoint K R L) G n
      (NodeGeometricCompletionRationalJets.tensorJetEquiv κ L (maximalIdeal T) n
        (l ⊗ₜ[κ] Ideal.Quotient.mk (maximalIdeal T ^ n) t))) = _
  rw [NodeGeometricCompletionRationalJets.tensorJetEquiv_tmul,
    NodeGeometricCompletionLocalizedJets.powerQuotientEquiv_mk]
  rfl

end Hironaka.Algebra.NodeGeometricCompletionDiagonalJets
