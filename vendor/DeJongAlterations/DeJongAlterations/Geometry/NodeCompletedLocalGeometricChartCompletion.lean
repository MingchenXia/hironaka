import DeJongAlterations.Geometry.NodeCompletedLocalGeometricChart
import DeJongAlterations.Geometry.NodeCompletedLocalOpenCompletion
import DeJongAlterations.Geometry.NodeCompletedLocalAffineGerm

/-! Natural ORIGINAL section coefficients and canonical completions at the ACTUAL
geometric affine chart. Both original-ring and field equivalences use the SAME native
open-immersion stalk map; neither action is defined by pulling back through its inverse. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

namespace DeJongAlterations.Geometry.NodeCompletedLocalGeometricChartCompletion

open Algebra.NodeFittingOmegaCharts NodeCompletedLocalAffineBaseChangeUV
  NodeCompletedLocalGeometricChart

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000
set_option quotPrecheck false

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) (C : Chart f)
  (s : S) (hs : s ∈ C.base.1) (K : Type u) [Field K] [Algebra (S.residueField s) K]

local instance originalChartAlgebra : Algebra Γ(S, C.base.1) Γ(X, C.source.1) := C.algebra f

/-- The SAME actual affine geometric chart, recording its ORIGINAL field coefficient map. -/
abbrev ChartScheme : Scheme.{u} := by
  letI := chartFieldAlgebra f C s hs K
  exact ActualBaseChange Γ(S, C.base.1) Γ(X, C.source.1) K

/-- The whole ORIGINAL section spectrum projection of the actual affine geometric chart. -/
def chartOriginalProjection : ChartScheme f C s hs K ⟶ Spec Γ(X, C.source.1) := by
  letI := chartFieldAlgebra f C s hs K
  exact NodeCompletedLocalActualAffineUV.originalProjection Γ(S, C.base.1) Γ(X, C.source.1) K

/-- The whole actual geometric-field projection of this same affine geometric chart. -/
def chartFieldProjection : ChartScheme f C s hs K ⟶ Spec (.of K) := by
  letI := chartFieldAlgebra f C s hs K
  exact NodeCompletedLocalActualAffineUV.fieldProjection Γ(S, C.base.1) Γ(X, C.source.1) K

local instance actualChartOpen : IsOpenImmersion (chartMap f C s hs K) :=
  chartMap_isOpenImmersion f C s hs K

local notation "Z" => ChartScheme f C s hs K
local notation "Y" => OriginalGeometricScheme f s K
local notation "j" => chartMap f C s hs K
local notation "π" => pullback.fst f (originalFieldMap s K)
local notation "q" => pullback.snd f (originalFieldMap s K)

/-- The ACTUAL original-source point of every actual chart point lies in the ORIGINAL open. -/
theorem originalPoint_mem (z : Z) : π (j z) ∈ C.source.1 := by
  have hz : j z ∈ Set.range j := ⟨z, rfl⟩
  rw [chartMap_range] at hz
  exact hz

/-- The natural ENTIRE original section coefficient map, via its ORIGINAL germ and the
ACTUAL original-source projection, before using any chart stalk equivalence. -/
def originalCoefficient (z : Z) : Γ(X, C.source.1) ⟶ (Y).presheaf.stalk (j z) :=
  X.presheaf.germ C.source.1 (π (j z)) (originalPoint_mem f C s hs K z) ≫ (π).stalkMap (j z)

/-- The ACTUAL open-chart stalk map preserves the WHOLE natural original section map. -/
theorem originalCoefficient_stalkMap (z : Z) :
    originalCoefficient f C s hs K z ≫ (j).stalkMap z =
      Scheme.baseToStalk (chartOriginalProjection f C s hs K) z := by
  unfold originalCoefficient
  rw [Category.assoc, ← Scheme.Hom.stalkMap_comp]
  exact NodeCompletedLocalAffineGerm.affine_germ_stalkMap_over C.source.2
    (chartOriginalProjection f C s hs K)
    (j ≫ π) (chartMap_source f C s hs K) z (originalPoint_mem f C s hs K z)

/-- The native original-section action at the ACTUAL geometric point is defined by its
original germ and projection, rather than by the inverse chart isomorphism. -/
@[instance_reducible]
def originalStalkAlgebra (z : Z) : Algebra Γ(X, C.source.1) ((Y).presheaf.stalk (j z)) :=
  (originalCoefficient f C s hs K z).hom.toAlgebra

/-- Its natural extension to the SAME ACTUAL completed geometric local ring. -/
@[instance_reducible]
def originalCompletedAlgebra (z : Z) : Algebra Γ(X, C.source.1) ((Y).completedLocalRing (j z)) := by
  letI := originalStalkAlgebra f C s hs K z
  infer_instance

/-- The ACTUAL open-chart stalk equivalence is over the WHOLE natural original section ring. -/
def stalkOriginalEquiv (z : Z) :
    letI := originalStalkAlgebra f C s hs K z
    letI := Scheme.stalkAlgebra (chartOriginalProjection f C s hs K) z
    (Y).presheaf.stalk (j z) ≃ₐ[Γ(X, C.source.1)] (Z).presheaf.stalk z := by
  letI := originalStalkAlgebra f C s hs K z
  letI := Scheme.stalkAlgebra (chartOriginalProjection f C s hs K) z
  refine AlgEquiv.ofRingEquiv (f := (asIso ((j).stalkMap z)).commRingCatIsoToRingEquiv) ?_
  intro r
  exact ConcreteCategory.congr_hom (originalCoefficient_stalkMap f C s hs K z) r

/-- The SAME canonical open-chart completion map is an algebra equivalence for the
natural ORIGINAL section action on the ACTUAL geometric local ring. -/
def completedOriginalEquiv (z : Z) :
    letI := originalCompletedAlgebra f C s hs K z
    letI := Scheme.completedLocalRingAlgebra (chartOriginalProjection f C s hs K) z
    (Y).completedLocalRing (j z) ≃ₐ[Γ(X, C.source.1)] (Z).completedLocalRing z := by
  letI := originalStalkAlgebra f C s hs K z
  letI := originalCompletedAlgebra f C s hs K z
  letI := Scheme.stalkAlgebra (chartOriginalProjection f C s hs K) z
  letI := Scheme.completedLocalRingAlgebra (chartOriginalProjection f C s hs K) z
  refine AlgEquiv.ofRingEquiv
    (f := Algebra.CompletionLocalMap.completionEquiv (asIso ((j).stalkMap z)).commRingCatIsoToRingEquiv) ?_
  intro r
  change Algebra.CompletionLocalMap.completionMap ((j).stalkMap z).hom
      (algebraMap ((Y).presheaf.stalk (j z)) ((Y).completedLocalRing (j z))
        (originalCoefficient f C s hs K z r)) =
    algebraMap ((Z).presheaf.stalk z) ((Z).completedLocalRing z)
      (Scheme.baseToStalk (chartOriginalProjection f C s hs K) z r)
  rw [Algebra.CompletionLocalMap.completionMap_algebraMap]
  exact congrArg (algebraMap ((Z).presheaf.stalk z) ((Z).completedLocalRing z))
    (ConcreteCategory.congr_hom (originalCoefficient_stalkMap f C s hs K z) r)

/-- Its WHOLE ring map is literally the actual induced map of the SAME geometric chart. -/
theorem completedOriginalEquiv_toRingHom (z : Z) :
    letI := originalCompletedAlgebra f C s hs K z
    letI := Scheme.completedLocalRingAlgebra (chartOriginalProjection f C s hs K) z
    (completedOriginalEquiv f C s hs K z).toRingHom = NodeCompletedLocalMap.completedMap j z := by
  rfl

/-- The field-coefficient completion equivalence uses this SAME original open-chart map. -/
def completedFieldEquiv (z : Z) :
    letI := Scheme.completedLocalRingAlgebra q (j z)
    letI := Scheme.completedLocalRingAlgebra (chartFieldProjection f C s hs K) z
    (Y).completedLocalRing (j z) ≃ₐ[K] (Z).completedLocalRing z :=
  NodeCompletedLocalOpenCompletion.completedEquivOver K j q z
    (chartFieldProjection f C s hs K)
    (chartMap_field f C s hs K)

/-- BOTH original-section and geometric-field algebra equivalences have the SAME whole map. -/
theorem completedOriginalEquiv_eq_completedFieldEquiv (z : Z) :
    letI := originalCompletedAlgebra f C s hs K z
    letI := Scheme.completedLocalRingAlgebra (chartOriginalProjection f C s hs K) z
    letI := Scheme.completedLocalRingAlgebra q (j z)
    letI := Scheme.completedLocalRingAlgebra (chartFieldProjection f C s hs K) z
    (completedOriginalEquiv f C s hs K z).toRingEquiv =
      (completedFieldEquiv f C s hs K z).toRingEquiv := by
  apply RingEquiv.toRingHom_injective
  exact (completedOriginalEquiv_toRingHom f C s hs K z).trans
    (NodeCompletedLocalOpenCompletion.completedEquivOver_toRingHom K j q z
      (chartFieldProjection f C s hs K)
      (chartMap_field f C s hs K)).symm

/-- Every ORIGINAL geometric stalk element retains precisely its actual open-chart image. -/
theorem completedOriginalEquiv_original (z : Z) (a : (Y).presheaf.stalk (j z)) :
    letI := originalCompletedAlgebra f C s hs K z
    letI := Scheme.completedLocalRingAlgebra (chartOriginalProjection f C s hs K) z
    completedOriginalEquiv f C s hs K z ((Y).toCompletedLocalRing (j z) a) =
      (Z).toCompletedLocalRing z ((j).stalkMap z a) := by
  exact Algebra.CompletionLocalMap.completionMap_algebraMap ((j).stalkMap z).hom a

/-- The SAME field-coefficient map retains the ENTIRE natural original section action. -/
theorem completedFieldEquiv_originalCoefficient (z : Z) (r : Γ(X, C.source.1)) :
    letI := originalCompletedAlgebra f C s hs K z
    letI := Scheme.completedLocalRingAlgebra (chartOriginalProjection f C s hs K) z
    letI := Scheme.completedLocalRingAlgebra q (j z)
    letI := Scheme.completedLocalRingAlgebra (chartFieldProjection f C s hs K) z
    completedFieldEquiv f C s hs K z
      (algebraMap Γ(X, C.source.1) ((Y).completedLocalRing (j z)) r) =
      algebraMap Γ(X, C.source.1) ((Z).completedLocalRing z) r := by
  let := originalCompletedAlgebra f C s hs K z
  let := Scheme.completedLocalRingAlgebra (chartOriginalProjection f C s hs K) z
  let := Scheme.completedLocalRingAlgebra q (j z)
  let := Scheme.completedLocalRingAlgebra (chartFieldProjection f C s hs K) z
  change (completedFieldEquiv f C s hs K z).toRingEquiv _ = _
  rw [← completedOriginalEquiv_eq_completedFieldEquiv]
  exact (completedOriginalEquiv f C s hs K z).commutes r

/-- Every original geometric stalk germ is retained also by the SAME field algebra map. -/
theorem completedFieldEquiv_original (z : Z) (a : (Y).presheaf.stalk (j z)) :
    letI := Scheme.completedLocalRingAlgebra q (j z)
    letI := Scheme.completedLocalRingAlgebra (chartFieldProjection f C s hs K) z
    completedFieldEquiv f C s hs K z ((Y).toCompletedLocalRing (j z) a) =
      (Z).toCompletedLocalRing z ((j).stalkMap z a) := by
  let := originalCompletedAlgebra f C s hs K z
  let := Scheme.completedLocalRingAlgebra (chartOriginalProjection f C s hs K) z
  let := Scheme.completedLocalRingAlgebra q (j z)
  let := Scheme.completedLocalRingAlgebra (chartFieldProjection f C s hs K) z
  change (completedFieldEquiv f C s hs K z).toRingEquiv _ = _
  rw [← completedOriginalEquiv_eq_completedFieldEquiv]
  exact completedOriginalEquiv_original f C s hs K z a

end DeJongAlterations.Geometry.NodeCompletedLocalGeometricChartCompletion
