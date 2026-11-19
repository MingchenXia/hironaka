import Hironaka.Algebra.NodeGeometricCompletionFiberResidue
import Hironaka.Algebra.NodeGeometricCompletionDiagonalCoefficients
import Hironaka.Algebra.NoetherianCompletion
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Filtration

/-! The SAME original Hensel coefficients agree with the actual diagonal-induced original point coefficients. -/

noncomputable section

open IsLocalRing

namespace Hironaka.Algebra.NodeGeometricCompletionOriginalCoefficientAgreement

open NodeGeometricCompletionOriginalFiberSection CompletionRegularityBasics
  NodeGeometricCompletionDiagonalCoefficients

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000

universe u
variable (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B]
  [FiniteDimensional (ResidueField A) (ResidueField B)]
  [Algebra.IsSeparable (ResidueField A) (ResidueField B)]

local notation "k" => ResidueField A
local notation "Q" => FiberRing A B
local notation "C" => Completion Q

local instance actualFiberLocalRing : IsLocalRing Q :=
  CompletionIdealQuotient.quotientLocalRing _
    (CompletionLocalMap.closedFiberIdeal_le_maximalIdeal (algebraMap A B))

attribute [local instance] baseResidueAlgebra
  NodeGeometricCompletionFiberResidue.quotientResidue_finite
  NodeGeometricCompletionFiberResidue.quotientResidue_separable

/-- The actual diagonal coefficient map, reindexed by the SAME canonical ORIGINAL quotient residue map, preserves the entire original base field. -/
def originalDiagonalSection : ResidueField B →ₐ[k] C where
  toRingHom := (pointCoefficientMap k Q).comp
    (NodeGeometricCompletionFiberResidue.quotientResidueAlgEquiv A B).toRingHom
  commutes' a := by
    change pointCoefficientMap k Q
      (NodeGeometricCompletionFiberResidue.quotientResidueAlgEquiv A B
        (algebraMap k (ResidueField B) a)) = algebraMap k C a
    rw [AlgEquiv.commutes]
    exact RingHom.congr_fun (pointCoefficient_base_triangle k Q) a

/-- The actual original Hensel point section, over the WHOLE same original base field. -/
def originalHenselSection : ResidueField B →ₐ[k] C where
  toRingHom := pointFieldSection A B
  commutes' := pointFieldSection_base A B

/-- EVERY original native residue has the SAME canonical completion image under the actual diagonal section. -/
theorem residue_originalDiagonalSection (a : ResidueField B) :
    residue C (originalDiagonalSection A B a) = originalResidueEquiv A B a := by
  change residue C (pointCoefficientMap k Q
    (NodeGeometricCompletionFiberResidue.quotientResidueAlgEquiv A B a)) = _
  rw [residue_pointCoefficientMap]
  rfl

/-- The WHOLE actual original diagonal and original Hensel coefficient sections coincide, without any supplied coefficient compatibility. -/
theorem originalDiagonalSection_eq_originalHenselSection :
    originalDiagonalSection A B = originalHenselSection A B := by
  let : Algebra.FormallyUnramified k (ResidueField B) :=
    Algebra.FormallyUnramified.of_isSeparable k (ResidueField B)
  apply Algebra.FormallyUnramified.ext_of_iInf
    (I := maximalIdeal C)
    (Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal C).ne_top)
  intro a
  change residue C (originalDiagonalSection A B a) = residue C (pointFieldSection A B a)
  rw [residue_originalDiagonalSection, residue_pointFieldSection]

/-- Every actual ORIGINAL point coefficient retains precisely the same original Hensel image. -/
theorem originalDiagonalSection_apply (a : ResidueField B) :
    pointCoefficientMap k Q
      (NodeGeometricCompletionFiberResidue.quotientResidueAlgEquiv A B a) = pointFieldSection A B a :=
  AlgHom.congr_fun (originalDiagonalSection_eq_originalHenselSection A B) a

end Hironaka.Algebra.NodeGeometricCompletionOriginalCoefficientAgreement
