import DeJongAlterations.Algebra.NodeFittingOmegaLocalization
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-! # Whole intrinsic differential Fitting ideals on every affine chart over an affine base -/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace DeJongAlterations.Algebra.NodeFittingOmegaAffine

open NodeFittingModule NodeFittingOmega

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The actual original coefficient map on a source open, from the same original morphism. -/
@[instance_reducible]
def sectionsAlgebra (U : X.Opens) : Algebra Γ(Y, ⊤) Γ(X, U) :=
  (f.appLE ⊤ U le_top).hom.toAlgebra

/-- Native naturality retains the entire original coefficient triangle on each basic open. -/
theorem sectionsAlgebra_basicOpen_tower (U : X.Opens) (s : Γ(X, U)) :
    letI := sectionsAlgebra f U
    letI := sectionsAlgebra f (X.basicOpen s)
    IsScalarTower Γ(Y, ⊤) Γ(X, U) Γ(X, X.basicOpen s) := by
  let := sectionsAlgebra f U
  let := sectionsAlgebra f (X.basicOpen s)
  apply IsScalarTower.of_algebraMap_eq'
  change (f.appLE ⊤ (X.basicOpen s) le_top).hom =
    (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom.comp (f.appLE ⊤ U le_top).hom
  exact congrArg CommRingCat.Hom.hom (f.appLE_map le_top
    (homOfLE (X.basicOpen_le s)).op).symm

variable [IsAffine Y] [LocallyOfFinitePresentation f]

/-- Local finite presentation applies to the actual original affine chart coefficient map. -/
theorem sections_finitePresentation (U : X.affineOpens) :
    letI := sectionsAlgebra f U.1
    Algebra.FinitePresentation Γ(Y, ⊤) Γ(X, U) := by
  let := sectionsAlgebra f U.1
  exact f.finitePresentation_appLE (isAffineOpen_top Y) U.2 le_top

/-- The actual original differential module on each affine chart is natively finitely presented. -/
theorem differential_finitePresentation (U : X.affineOpens) :
    letI := sectionsAlgebra f U.1
    Module.FinitePresentation Γ(X, U) (KaehlerDifferential Γ(Y, ⊤) Γ(X, U)) := by
  let := sectionsAlgebra f U.1
  let := sections_finitePresentation f U
  infer_instance

/-- The actual entire intrinsic Fitting ideal of the original relative differential module. -/
def chartIdeal (i : ℕ) (U : X.affineOpens) : Ideal Γ(X, U) := by
  letI := sectionsAlgebra f U.1
  letI := differential_finitePresentation f U
  exact fittingIdeal (R := Γ(X, U)) (M := KaehlerDifferential Γ(Y, ⊤) Γ(X, U)) i

/-- Basic-open restriction is an equality of whole ideals under the original restriction map. -/
theorem chartIdeal_basicOpen (i : ℕ) (U : X.affineOpens) (s : Γ(X, U)) :
    (chartIdeal f i U).map (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom =
      chartIdeal f i (X.affineBasicOpen s) := by
  let := sectionsAlgebra f U.1
  let := sectionsAlgebra f (X.basicOpen s)
  let := sectionsAlgebra_basicOpen_tower f U.1 s
  let := differential_finitePresentation f U
  let := differential_finitePresentation f (X.affineBasicOpen s)
  let := U.2.isLocalization_basicOpen s
  exact fittingIdeal_localization Γ(Y, ⊤) Γ(X, U) Γ(X, X.basicOpen s)
    (Submonoid.powers s) i

/-- Native ideal sheaf data with the exact intrinsic original differential ideal on EVERY affine open. -/
def idealSheaf (i : ℕ) : X.IdealSheafData where
  ideal := chartIdeal f i
  map_ideal_basicOpen := chartIdeal_basicOpen f i

/-- Every affine component is exactly the assigned original intrinsic whole ideal. -/
@[simp]
theorem idealSheaf_ideal (i : ℕ) (U : X.affineOpens) :
    (idealSheaf f i).ideal U = chartIdeal f i U := rfl

/-- All affine-open restriction identities follow for the same actual native ideal sheaf. -/
theorem chartIdeal_restrict (i : ℕ) {U V : X.affineOpens} (h : V ≤ U) :
    (chartIdeal f i U).map (X.presheaf.map (homOfLE h).op).hom = chartIdeal f i V :=
  (idealSheaf f i).map_ideal h

end DeJongAlterations.Algebra.NodeFittingOmegaAffine
