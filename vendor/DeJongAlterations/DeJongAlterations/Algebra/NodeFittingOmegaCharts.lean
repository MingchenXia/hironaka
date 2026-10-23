import DeJongAlterations.Algebra.NodeFittingOmegaLocalization
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Whole intrinsic original differential ideals on arbitrary affine source--base charts -/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace DeJongAlterations.Algebra.NodeFittingOmegaCharts

open NodeFittingModule

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- An actual affine source--base chart of the same original morphism. -/
structure Chart where
  source : X.affineOpens
  base : Y.affineOpens
  le_preimage : source.1 ≤ f ⁻¹ᵁ base.1

/-- The actual original coefficient map, with no coordinate or differential model supplied. -/
@[instance_reducible]
def Chart.algebra (C : Chart f) : Algebra Γ(Y, C.base) Γ(X, C.source) :=
  (f.appLE C.base.1 C.source.1 C.le_preimage).hom.toAlgebra

variable [LocallyOfFinitePresentation f]

/-- Local finite presentation gives the native finite presentation of the actual original map. -/
theorem Chart.finitePresentation (C : Chart f) :
    letI := C.algebra f
    Algebra.FinitePresentation Γ(Y, C.base) Γ(X, C.source) := by
  let := C.algebra f
  exact f.finitePresentation_appLE C.base.2 C.source.2 C.le_preimage

/-- Its actual native relative differential module is internally finitely presented. -/
theorem Chart.differentialFinitePresentation (C : Chart f) :
    letI := C.algebra f
    Module.FinitePresentation Γ(X, C.source)
      (KaehlerDifferential Γ(Y, C.base) Γ(X, C.source)) := by
  let := C.algebra f
  let := C.finitePresentation f
  infer_instance

/-- The original entire intrinsic differential Fitting ideal on this original affine chart. -/
def Chart.ideal (C : Chart f) (i : ℕ) : Ideal Γ(X, C.source) := by
  letI := C.algebra f
  letI := C.differentialFinitePresentation f
  exact fittingIdeal (R := Γ(X, C.source))
    (M := KaehlerDifferential Γ(Y, C.base) Γ(X, C.source)) i

/-- Every actual nested source--base chart has EXACTLY the extended original whole ideal. -/
theorem Chart.ideal_restrict (C D : Chart f) (hs : D.source ≤ C.source)
    (hb : D.base ≤ C.base) (i : ℕ) :
    (C.ideal f i).map (X.presheaf.map (homOfLE (show D.source.1 ≤ C.source.1 from hs)).op).hom = D.ideal f i := by
  let R := Γ(Y, C.base)
  let R' := Γ(Y, D.base)
  let A := Γ(X, C.source)
  let B := Γ(X, D.source)
  let : Algebra R A := C.algebra f
  let : Algebra R' B := D.algebra f
  let : Algebra R R' := (Y.presheaf.map (homOfLE (show D.base.1 ≤ C.base.1 from hb)).op).hom.toAlgebra
  let : Algebra A B := (X.presheaf.map (homOfLE (show D.source.1 ≤ C.source.1 from hs)).op).hom.toAlgebra
  let : Algebra R B := (f.appLE C.base.1 D.source.1 ((show D.source.1 ≤ C.source.1 from hs).trans C.le_preimage)).hom.toAlgebra
  let : IsScalarTower R A B := by
    apply IsScalarTower.of_algebraMap_eq'
    exact congrArg CommRingCat.Hom.hom
      (f.appLE_map C.le_preimage (homOfLE (show D.source.1 ≤ C.source.1 from hs)).op).symm
  let : IsScalarTower R R' B := by
    apply IsScalarTower.of_algebraMap_eq'
    exact congrArg CommRingCat.Hom.hom
      (f.map_appLE D.le_preimage (homOfLE (show D.base.1 ≤ C.base.1 from hb)).op).symm
  let : Algebra.Etale A B := by
    change (X.presheaf.map (homOfLE (show D.source.1 ≤ C.source.1 from hs)).op).hom.Etale
    simpa [Scheme.Hom.appLE] using
      Scheme.Hom.etale_appLE (𝟙 X) C.source.2 D.source.2 hs
  let : Algebra.FormallyUnramified R R' := by
    change (Y.presheaf.map (homOfLE (show D.base.1 ≤ C.base.1 from hb)).op).hom.FormallyUnramified
    simpa [Scheme.Hom.appLE] using
      Scheme.Hom.formallyUnramified_appLE (𝟙 Y) C.base.2 D.base.2 hb
  let : Module.FinitePresentation A (KaehlerDifferential R A) :=
    C.differentialFinitePresentation f
  let : Module.FinitePresentation B (KaehlerDifferential R' B) :=
    D.differentialFinitePresentation f
  let : Module.FinitePresentation B (KaehlerDifferential R B) :=
    NodeFittingOmega.finitePresentation_of_formallyEtale R A B
  exact (NodeFittingOmega.fittingIdeal_formallyEtale R A B i).trans
    (NodeFittingOmega.fittingIdeal_changeBase R R' B i)

end DeJongAlterations.Algebra.NodeFittingOmegaCharts
