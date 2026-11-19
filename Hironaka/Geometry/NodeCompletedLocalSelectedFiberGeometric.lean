import Hironaka.Geometry.NodeCompletedLocalSelectedFiberTensor
import Hironaka.Geometry.NodeCompletedLocalSelectedTensor
import Hironaka.Algebra.NodeGeometricCompletionFiberResidue
import Hironaka.Algebra.NodeGeometricCompletionDiagonalGeometric

/-! The actual original closed-fibre geometric point is the SAME prescribed original tensor-kernel point. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct IsLocalRing

namespace Hironaka.Geometry.NodeCompletedLocalSelectedFiberGeometric

open NodeCompletedLocalMap NodeCompletedLocalResiduePoint NodeCompletedLocalSelectedAffine
  NodeCompletedLocalSelectedFiberTensor NodeCompletedLocalSelectedTensor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000
set_option quotPrecheck false

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
  (L : Type u) [Field L] [Algebra (X.residueField x) L]

attribute [local instance] originalAlgebra baseFieldAlgebra originalBaseAlgebra
  originalFiberResidueAlgebra NodeCompletedLocalSelectedFiberTensor.baseResidueAlgebra
  NodeCompletedLocalSelectedFiberTensor.original_scalarTower
  Algebra.TensorProduct.rightAlgebra

local notation "A" => S.presheaf.stalk (f x)
local notation "B" => X.presheaf.stalk x
local notation "k" => S.residueField (f x)
local notation "Q" => OriginalFiberRing f x
local notation "F" => L ⊗[k] Q
local notation "D" => NodeCompletedLocalSelectedTensor.TensorRing f x L
local notation "p" => NodeCompletedLocalSelectedTensor.tensorPoint f x L

local instance nativeOriginalResidueEmbedding : Algebra (ResidueField B) L :=
  inferInstanceAs (Algebra (X.residueField x) L)

local instance originalLocalMap : IsLocalHom (algebraMap A B) :=
  inferInstanceAs (IsLocalHom (f.stalkMap x).hom)

local instance originalQuotientLocalRing : IsLocalRing Q := originalFiberLocalRing f x

/-- The SAME actual original selected embedding on the native closed-fibre residue field. -/
@[instance_reducible]
def selectedQuotientPointAlgebra : Algebra (ResidueField Q) L :=
  Algebra.NodeGeometricCompletionFiberResidue.quotientPointAlgebra A B L

/-- Its ENTIRE original base-residue action is the original selected geometric coefficient action. -/
theorem selectedQuotientPoint_scalarTower :
    letI := selectedQuotientPointAlgebra f x L
    IsScalarTower k (ResidueField Q) L := by
  let := selectedQuotientPointAlgebra f x L
  exact Algebra.NodeGeometricCompletionFiberResidue.quotientPoint_scalarTower A B L

/-- The actual original closed-fibre augmentation uses precisely the prescribed original residue embedding. -/
def quotientAugmentation : F →ₐ[L] L := by
  letI := selectedQuotientPointAlgebra f x L
  letI := selectedQuotientPoint_scalarTower f x L
  exact Algebra.NodeGeometricCompletionDiagonalGeometric.originalAugmentation k Q L

/-- EVERY original local germ has its SAME prescribed original residue image after taking the closed fibre. -/
theorem quotientAugmentation_tmul (l : L) (b : B) :
    quotientAugmentation f x L (l ⊗ₜ[k] Ideal.Quotient.mk (originalFiberIdeal f x) b) =
      l * algebraMap (X.residueField x) L ((X.residue x) b) := by
  let := selectedQuotientPointAlgebra f x L
  let := selectedQuotientPoint_scalarTower f x L
  change l * algebraMap (ResidueField Q) L
    (residue Q (Ideal.Quotient.mk (originalFiberIdeal f x) b)) = _
  exact congrArg (fun z : L => l * z)
    (Algebra.NodeGeometricCompletionFiberResidue.quotientPoint_original A B L b)

/-- The WHOLE actual closed-fibre tensor equivalence preserves the SAME original selected augmentation. -/
theorem augmentation_triangle :
    (NodeCompletedLocalSelectedTensor.augmentation f x L).comp
      (fiberTensorEquiv f x L).toAlgHom = quotientAugmentation f x L := by
  apply AlgHom.ext
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul l q =>
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
      change NodeCompletedLocalSelectedTensor.augmentation f x L
        (fiberTensorEquiv f x L (l ⊗ₜ[k] Ideal.Quotient.mk (originalFiberIdeal f x) b)) = _
      rw [fiberTensorEquiv_tmul, NodeCompletedLocalSelectedTensor.augmentation_tmul,
        quotientAugmentation_tmul]
  | add t s ht hs => simpa only [map_add] using congrArg₂ (· + ·) ht hs

/-- The literal ORIGINAL closed-fibre selected geometric point is its actual augmentation kernel. -/
def quotientPoint : Ideal F := RingHom.ker (quotientAugmentation f x L).toRingHom

/-- Its maximality is internally derived from the WHOLE external-field action. -/
theorem quotientPoint_isMaximal : (quotientPoint f x L).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (quotientAugmentation f x L) (by
    intro l
    exact ⟨algebraMap L F l, (quotientAugmentation f x L).commutes l⟩)

attribute [local instance] quotientPoint_isMaximal

/-- The ENTIRE actual tensor point contracts to precisely the SAME closed-fibre selected point. -/
theorem quotientPoint_comap :
    (p).asIdeal.comap (fiberTensorEquiv f x L).toRingHom = quotientPoint f x L := by
  rw [tensorPoint_asIdeal]
  change RingHom.ker ((NodeCompletedLocalSelectedTensor.augmentation f x L).comp
    (fiberTensorEquiv f x L).toAlgHom).toRingHom = _
  rw [augmentation_triangle]
  rfl

/-- All actual denominators are preserved, with NO replacement point. -/
theorem primeCompl_map :
    Submonoid.map (fiberTensorEquiv f x L) (quotientPoint f x L).primeCompl = (p).asIdeal.primeCompl := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    change fiberTensorEquiv f x L z ∉ (p).asIdeal
    change z ∉ quotientPoint f x L at hz
    rw [← quotientPoint_comap] at hz
    exact hz
  · intro hy
    change y ∉ (p).asIdeal at hy
    refine ⟨(fiberTensorEquiv f x L).symm y, ?_, (fiberTensorEquiv f x L).apply_symm_apply y⟩
    change (fiberTensorEquiv f x L).symm y ∉ quotientPoint f x L
    rw [← quotientPoint_comap]
    change fiberTensorEquiv f x L ((fiberTensorEquiv f x L).symm y) ∉ (p).asIdeal
    simpa only [AlgEquiv.apply_symm_apply] using hy

/-- The original closed-fibre selected geometric stalk, at its internally constructed SAME kernel point. -/
abbrev QuotientGeometricStalk := Localization.AtPrime (quotientPoint f x L)

/-- The WHOLE original closed-fibre geometric local ring is the SAME selected original tensor localization. -/
def stalkEquiv :
    QuotientGeometricStalk f x L ≃ₐ[L] Localization.AtPrime (p).asIdeal :=
  IsLocalization.algEquivOfAlgEquiv (QuotientGeometricStalk f x L)
    (Localization.AtPrime (p).asIdeal) (fiberTensorEquiv f x L) (primeCompl_map f x L)

/-- EVERY original local representative retains its literal tensor/localization image. -/
theorem stalkEquiv_original (l : L) (b : B) :
    stalkEquiv f x L
      (algebraMap F (QuotientGeometricStalk f x L)
        (l ⊗ₜ[k] Ideal.Quotient.mk (originalFiberIdeal f x) b)) =
      algebraMap D (Localization.AtPrime (p).asIdeal) (l ⊗ₜ[A] b) := by
  change IsLocalization.algEquivOfAlgEquiv (QuotientGeometricStalk f x L)
    (Localization.AtPrime (p).asIdeal) (fiberTensorEquiv f x L) (primeCompl_map f x L) _ = _
  rw [IsLocalization.algEquivOfAlgEquiv_eq, fiberTensorEquiv_tmul]

end Hironaka.Geometry.NodeCompletedLocalSelectedFiberGeometric
