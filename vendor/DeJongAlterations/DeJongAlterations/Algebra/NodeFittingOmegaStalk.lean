import DeJongAlterations.Algebra.NodeFittingOmegaCharts
import DeJongAlterations.Algebra.NodeFittingIdealSheafStalks

/-! # The entire original affine differential Fitting ideal at the SAME original stalk -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Algebra.NodeFittingOmegaStalk

open NodeFittingModule NodeFittingOmegaCharts

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The original native stalk map is the actual original local-ring coefficient action. -/
@[instance_reducible]
def stalkAlgebra (x : X) : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
  (f.stalkMap x).hom.toAlgebra

/-- The exact whole coefficient square at the original point, with no auxiliary map. -/
theorem chart_stalk_triangle (C : Chart f) {x : X} (hx : x ∈ C.source.1) :
    Y.presheaf.germ C.base.1 (f x) (C.le_preimage hx) ≫ f.stalkMap x =
      f.appLE C.base.1 C.source.1 C.le_preimage ≫ X.presheaf.germ C.source.1 x hx := by
  rw [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res, f.germ_stalkMap]

/-- The SAME actual coefficient action from the original affine base into the original source stalk. -/
@[instance_reducible]
def chartStalkAlgebra (C : Chart f) {x : X} (hx : x ∈ C.source.1) :
    Algebra Γ(Y, C.base) (X.presheaf.stalk x) :=
  ((X.presheaf.germ C.source.1 x hx).hom.comp
    (f.appLE C.base.1 C.source.1 C.le_preimage).hom).toAlgebra

/-- The actual source germ followed by the actual source stalk is the original chart coefficient map. -/
theorem chart_source_tower (C : Chart f) {x : X} (hx : x ∈ C.source.1) :
    letI := C.algebra f
    letI := X.presheaf.algebra_section_stalk ⟨x, hx⟩
    letI := chartStalkAlgebra f C hx
    IsScalarTower Γ(Y, C.base) Γ(X, C.source) (X.presheaf.stalk x) := by
  let := C.algebra f
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  let := chartStalkAlgebra f C hx
  exact IsScalarTower.of_algebraMap_eq' rfl

/-- The actual base germ and native original stalk map give that SAME original action. -/
theorem chart_base_tower (C : Chart f) {x : X} (hx : x ∈ C.source.1) :
    letI := Y.presheaf.algebra_section_stalk ⟨f x, C.le_preimage hx⟩
    letI := stalkAlgebra f x
    letI := chartStalkAlgebra f C hx
    IsScalarTower Γ(Y, C.base) (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
  let := Y.presheaf.algebra_section_stalk ⟨f x, C.le_preimage hx⟩
  let := stalkAlgebra f x
  let := chartStalkAlgebra f C hx
  apply IsScalarTower.of_algebraMap_eq'
  exact congrArg CommRingCat.Hom.hom (chart_stalk_triangle f C hx).symm

variable [LocallyOfFinitePresentation f]

/-- Native finite presentation at the original local rings is internally produced from any actual chart. -/
theorem differentialFinitePresentation_of_chart (C : Chart f) {x : X}
    (hx : x ∈ C.source.1) :
    letI := stalkAlgebra f x
    Module.FinitePresentation (X.presheaf.stalk x)
      (KaehlerDifferential (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) := by
  let := C.algebra f
  let := C.differentialFinitePresentation f
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  let := Y.presheaf.algebra_section_stalk ⟨f x, C.le_preimage hx⟩
  let := stalkAlgebra f x
  let := chartStalkAlgebra f C hx
  let := chart_source_tower f C hx
  let := chart_base_tower f C hx
  let := C.source.2.isLocalization_stalk ⟨x, hx⟩
  let := C.base.2.isLocalization_stalk ⟨f x, C.le_preimage hx⟩
  exact NodeFittingOmega.finitePresentation_doubleLocalization Γ(Y, C.base) Γ(X, C.source)
    (X.presheaf.stalk x) (Y.presheaf.stalk (f x))
    (C.source.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (C.base.2.primeIdealOf ⟨f x, C.le_preimage hx⟩).asIdeal.primeCompl

omit [LocallyOfFinitePresentation f] in
/-- Every original point admits an actual source--base affine chart through the same original map. -/
theorem exists_chart_mem (x : X) : ∃ C : Chart f, x ∈ C.source.1 := by
  obtain ⟨V, hv⟩ := NodeFittingIdealSheaf.exists_affineOpens_mem (f x)
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    hv (f ⁻¹ᵁ V.1).2
  exact ⟨⟨⟨U, hU⟩, V, hUV⟩, hx⟩

/-- Native finite presentation of the actual original local differential module, with no chart hypothesis. -/
theorem differentialFinitePresentation (x : X) :
    letI := stalkAlgebra f x
    Module.FinitePresentation (X.presheaf.stalk x)
      (KaehlerDifferential (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) := by
  obtain ⟨C, hx⟩ := exists_chart_mem f x
  exact differentialFinitePresentation_of_chart f C hx

/-- The original intrinsic whole Fitting ideal at the actual original local coefficient map. -/
def ideal (i : ℕ) (x : X) : Ideal (X.presheaf.stalk x) := by
  letI := stalkAlgebra f x
  letI := differentialFinitePresentation f x
  exact fittingIdeal (R := X.presheaf.stalk x)
    (M := KaehlerDifferential (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) i

/-- Every original affine chart computes the EXACT SAME whole intrinsic ideal in the SAME actual stalk. -/
theorem chart_ideal_stalk (C : Chart f) (i : ℕ) {x : X} (hx : x ∈ C.source.1) :
    (C.ideal f i).map (X.presheaf.germ C.source.1 x hx).hom = ideal f i x := by
  let := C.algebra f
  let := C.differentialFinitePresentation f
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  let := Y.presheaf.algebra_section_stalk ⟨f x, C.le_preimage hx⟩
  let := stalkAlgebra f x
  let := chartStalkAlgebra f C hx
  let := chart_source_tower f C hx
  let := chart_base_tower f C hx
  let := C.source.2.isLocalization_stalk ⟨x, hx⟩
  let := C.base.2.isLocalization_stalk ⟨f x, C.le_preimage hx⟩
  let := differentialFinitePresentation f x
  exact NodeFittingOmega.fittingIdeal_doubleLocalization Γ(Y, C.base) Γ(X, C.source)
    (X.presheaf.stalk x) (Y.presheaf.stalk (f x))
    (C.source.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (C.base.2.primeIdealOf ⟨f x, C.le_preimage hx⟩).asIdeal.primeCompl i

end DeJongAlterations.Algebra.NodeFittingOmegaStalk
