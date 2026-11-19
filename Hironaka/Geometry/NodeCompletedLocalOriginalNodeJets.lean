import Hironaka.Geometry.NodeCompletedLocalSelectedFiberNode
import Hironaka.Geometry.SemistableSingularFinite
import Hironaka.Algebra.NodeGeometricCompletionOriginalGeometricJets
import Hironaka.Algebra.NodeGeometricCompletionFiberFiniteType
import Hironaka.Algebra.NoetherianCompletion
import Hironaka.Algebra.NodeFieldFormalUVLocal

/-! The genuine original singular-point completion supplies ALL geometric node jets internally. -/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing TensorProduct

namespace Hironaka.Geometry.NodeCompletedLocalOriginalNodeJets

open NodeCompletedLocalMap NodeCompletedLocalResiduePoint
  NodeCompletedLocalSelectedFiberGeometric NodeCompletedLocalSelectedFiberNode
  Algebra.NodeGeometricCompletionDiagonalCoefficients

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000
set_option quotPrecheck false

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsSemistableCurve f]
  (z : (Algebra.NodeFittingOmegaGluing.idealSheaf f 1).subscheme)

local notation "I" => Algebra.NodeFittingOmegaGluing.idealSheaf f 1
local notation "x" => (I).subschemeι z
local notation "A" => S.presheaf.stalk (f x)
local notation "B" => X.presheaf.stalk x
local notation "k" => S.residueField (f x)
local notation "Q" => OriginalFiberRing f x
local notation "κ" => ResidueField Q
local notation "C" => Algebra.CompletionRegularityBasics.Completion Q

attribute [local instance] originalAlgebra originalFiberResidueAlgebra

local instance originalLocalMap : IsLocalHom (algebraMap A B) :=
  inferInstanceAs (IsLocalHom (f.stalkMap x).hom)

local instance originalQuotientLocalRing : IsLocalRing Q := originalFiberLocalRing f x

local instance originalStalkEssFiniteType : Algebra.EssFiniteType A B :=
  originalAlgebra_essFiniteType f x

/-- Native original closed-fibre essential finite type is derived from the SAME original scheme stalk map. -/
theorem originalFiber_essFiniteType : Algebra.EssFiniteType k Q :=
  Algebra.NodeGeometricCompletionFiberFiniteType.fiber_essFiniteType A B

attribute [local instance] originalFiber_essFiniteType

/-- Noetherianity of the original closed fibre follows internally, without a Noetherian-base assumption. -/
theorem originalFiber_isNoetherianRing : IsNoetherianRing Q :=
  Algebra.NodeGeometricCompletionFiberFiniteType.fiber_isNoetherianRing A B

attribute [local instance] originalFiber_isNoetherianRing

/-- The ORIGINAL point residue extension is finite separable by the actual proved source 2.21. -/
theorem originalResidue_finite_separable :
    FiniteDimensional (ResidueField A) (ResidueField B) ∧
      Algebra.IsSeparable (ResidueField A) (ResidueField B) :=
by
  have hmap : algebraMap (ResidueField A) (ResidueField B) = (f.residueFieldMap x).hom := by
    apply RingHom.ext
    intro a
    obtain ⟨r, rfl⟩ := residue_surjective a
    rw [ResidueField.algebraMap_residue]
    rfl
  let eA : (S.residueField (f x)) ≃+* ResidueField A := RingEquiv.refl _
  let eB : (X.residueField x) ≃+* ResidueField B := RingEquiv.refl _
  have he : (algebraMap (ResidueField A) (ResidueField B)).comp eA.toRingHom =
      eB.toRingHom.comp (f.residueFieldMap x).hom := by
    apply RingHom.ext
    intro a
    exact RingHom.congr_fun hmap a
  have hs := SemistableCurve.originalSingularResidue_finite_separable f z
  constructor
  · exact @Module.Finite.of_equiv_equiv
      (S.residueField (f x)) (X.residueField x) (ResidueField A) (ResidueField B)
      _ _ _ _ (f.residueFieldMap x).hom.toAlgebra inferInstance eA eB he hs.1
  · exact @Algebra.IsSeparable.of_equiv_equiv
      (S.residueField (f x)) (X.residueField x) (ResidueField A) (ResidueField B)
      _ _ _ _ (f.residueFieldMap x).hom.toAlgebra inferInstance eA eB he hs.2

local instance originalResidueFinite : FiniteDimensional (ResidueField A) (ResidueField B) :=
  (originalResidue_finite_separable f z).1
local instance originalResidueSeparable : Algebra.IsSeparable (ResidueField A) (ResidueField B) :=
  (originalResidue_finite_separable f z).2

/-- The SAME actual closed-fibre native residue extension is internally finite. -/
theorem originalFiberResidue_finite : FiniteDimensional k κ :=
  Algebra.NodeGeometricCompletionFiberResidue.quotientResidue_finite A B

/-- The SAME actual closed-fibre native residue extension is internally separable. -/
theorem originalFiberResidue_separable : Algebra.IsSeparable k κ :=
  Algebra.NodeGeometricCompletionFiberResidue.quotientResidue_separable A B

attribute [local instance] originalFiberResidue_finite originalFiberResidue_separable

/-- The actual ORIGINAL singular point belongs to the support of its SAME original whole Fitting ideal. -/
theorem singular_mem_support : x ∈ (I).support := by
  change x ∈ ((I).support : Set X)
  rw [← (I).range_subschemeι]
  exact ⟨z, rfl⟩

/-- The SAME original closed-fibre completion is internally Noetherian. -/
theorem originalCompletion_isNoetherianRing : IsNoetherianRing C := by infer_instance

/-- The SAME original closed-fibre completion is complete for its ACTUAL native maximal ideal. -/
theorem originalCompletion_isAdicComplete : IsAdicComplete (maximalIdeal C) C := by infer_instance

/-- Actual point-field coefficients on the SAME original closed-fibre completion, obtained from its actual diagonal neighbourhood. -/
@[instance_reducible]
def originalPointAlgebra : Algebra κ C := pointCoefficientAlgebra k Q

/-- EVERY original closed-fibre residue coefficient retains its SAME canonical native completion residue. -/
theorem originalPoint_residue (a : κ) :
    letI := originalPointAlgebra f z
    residue C (algebraMap κ C a) = Algebra.CompletionRegularityBasics.residueFieldEquiv Q a := by
  let := originalPointAlgebra f z
  exact residue_pointCoefficientMap k Q a

/-- The forward native original-point coefficient map has its ACTUAL canonical residue identity and is bijective on residues. -/
theorem originalPoint_residue_bijective :
    letI := originalPointAlgebra f z
    Function.Bijective ((residue C).comp (algebraMap κ C)) := by
  let := originalPointAlgebra f z
  exact pointCoefficient_residue_bijective k Q

variable (L : Type u) [Field L] [IsAlgClosed L]
  [Algebra (X.residueField ((Algebra.NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z)) L]

attribute [local instance] originalBaseAlgebra selectedQuotientPointAlgebra
  selectedQuotientPoint_scalarTower Algebra.TensorProduct.rightAlgebra
  Algebra.NodeGeometricCompletionTensorLocalization.localizedPoint_isMaximal
  Algebra.NodeGeometricCompletionDiagonalCompletedJets.selectedStalk_isNoetherianRing

local notation "G" => Algebra.NodeGeometricCompletionDiagonalGeometric.DiagonalGeometricStalk k Q L
local notation "U" => Algebra.NodeGeometricCompletionFormalUV.FormalUV L

/-- EVERY actual original completed finite jet, scalar extended only AFTER quotient, is the literal native uv node jet. -/
def nodeJetEquiv (n : ℕ) :
    letI := originalPointAlgebra f z
    (L ⊗[κ] (C ⧸ maximalIdeal C ^ n)) ≃ₐ[L] (U ⧸ maximalIdeal U ^ n) := by
  letI := originalPointAlgebra f z
  let e := diagonalNodeModel f x L (singular_mem_support f z)
  exact (Algebra.NodeGeometricCompletionOriginalGeometricJets.jetEquiv k Q L n).trans
    (Ideal.quotientEquivAlg (maximalIdeal (Algebra.CompletionRegularityBasics.Completion G) ^ n)
      (maximalIdeal U ^ n) e (by
        symm
        change (maximalIdeal (Algebra.CompletionRegularityBasics.Completion G) ^ n).map e.toRingEquiv.toRingHom = _
        rw [Ideal.map_pow]
        exact congrArg (fun J : Ideal U => J ^ n) (map_ringEquiv_maximalIdeal e.toRingEquiv)))

end Hironaka.Geometry.NodeCompletedLocalOriginalNodeJets
