import Hironaka.Resolution.HironakaActualCoherentWeightedCoefficientMarked
import Hironaka.Resolution.HironakaActualAnalyticSubspaceOpenRestriction
import Hironaka.Resolution.HironakaChowPureTransformBaseChange

/-! The SAME actual full-minor sections define a coherent analytic ideal on
precisely the literal ORIGINAL open, with the entire native ideal dictionary.
Blueprint FIRST: `hironaka-g10-coherent-original-minor-ideal.tex`. -/

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite TopologicalSpace Set Filter AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaChowCoherentOriginalMinorIdeal

open Hironaka.HolomorphicIdealSheaves
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualWholeStalkHolomorphicPullback
  HironakaActualCoherentWeightedCoefficientMarked HironakaChowDeterminantalImage
  HironakaChowPureTransformBaseChange HironakaHolomorphicJetRankLoci

variable {n : ℕ} {Y : Type} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- The ENTIRE native ideal of the existing finite-function ideal is the ORIGINAL span. -/
theorem actualWholeStalk_finiteFunctionIdeal {ι : Type} [Fintype ι]
    (c : ι → Y → ℂ) (y : Y) (hc : ∀ i, HolomorphicAt n (c i) y) :
    actualWholeSheafStalkIdeal (finiteFunctionIdeal (n := n) c) y =
      Ideal.span (Set.range fun i => actualOriginalFunctionGerm y (c i) (hc i)) := by
  let e := Fintype.equivFin ι
  let G (j : Fin (Fintype.card ι)) := c (e.symm j)
  have hr : Set.range G = Set.range c := by
    ext g
    constructor
    · rintro ⟨j,rfl⟩
      exact ⟨e.symm j,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨e i,by simp only [G,e.symm_apply_apply]⟩
  have hgen (g : Y → ℂ) : (finiteFunctionIdeal (n := n) c).mem y g ↔
      IsInSpanAt (n := n) (· ∈ Set.range G) y g := by
    change IsInSpanAt (n := n) (· ∈ Set.range c) y g ↔ _
    rw [hr]
  rw [actualWholeSheafStalkIdeal_eq_map_chart,
    wholeChartStalkIdeal_eq_actual_generator_span _ y G (fun j => hc (e.symm j)) hgen,
    Ideal.map_span,← Set.range_comp]
  apply congrArg Ideal.span
  ext z
  constructor
  · rintro ⟨j,rfl⟩
    refine ⟨e.symm j,?_⟩
    change actualOriginalFunctionGerm y (c (e.symm j)) (hc (e.symm j)) =
      (actualStalkChartEquiv (n := n) y).symm
        (chartTranslatedGerm y y (mem_chart_source _ y) (G j) (hc (e.symm j)))
    apply (actualStalkChartEquiv (n := n) y).injective
    rw [actualOriginalFunctionGerm_chart, RingEquiv.apply_symm_apply]
  · rintro ⟨i,rfl⟩
    refine ⟨e i,?_⟩
    change (actualStalkChartEquiv (n := n) y).symm
      (chartTranslatedGerm y y (mem_chart_source _ y) (G (e i)) (hc (e.symm (e i)))) =
        actualOriginalFunctionGerm y (c i) (hc i)
    apply (actualStalkChartEquiv (n := n) y).injective
    rw [RingEquiv.apply_symm_apply,actualOriginalFunctionGerm_chart]
    simp only [G,e.symm_apply_apply]

/-- The ACTUAL original open-inclusion stalk map retains the SAME section function. -/
theorem openInclusion_stalkMap_section (U : Opens Y) (y : U)
    (a : actualComplexSection (n := n) U) :
    (ChartedSpace.locallyRingedSpaceMap (IM := 𝓘(ℂ,ComplexModel n))
      (IN := 𝓘(ℂ,ComplexModel n)) (Subtype.val : U → Y) contMDiff_subtype_val).stalkMap y
      (TopCat.Presheaf.germ (actualComplexStructureSheaf (n := n) Y).obj U y.val y.property a) =
      actualOriginalFunctionGerm y (a : U → ℂ)
        (Eventually.of_forall fun z => ((smoothSheaf.contMDiff_section a) z).mdifferentiableAt (by simp)) := by
  let F := ChartedSpace.locallyRingedSpaceMap (IM := 𝓘(ℂ,ComplexModel n))
      (IN := 𝓘(ℂ,ComplexModel n)) (Subtype.val : U → Y) contMDiff_subtype_val
  let V : Opens U := (Opens.map F.base).obj U
  have hyV : y ∈ V := y.property
  let t : actualComplexSection (n := n) V := F.toHom.c.app (op U) a
  calc
    _ = TopCat.Presheaf.germ (actualComplexStructureSheaf (n := n) U).obj V y hyV t :=
      PresheafedSpace.stalkMap_germ_apply F.toHom U y y.property a
    _ = _ := by
      symm
      apply actualOriginalFunctionGerm_eq_section (M := U) V y hyV t
      filter_upwards [V.isOpen.mem_nhds hyV] with z hz
      rw [sectionExtension_apply V t z hz]
      rfl

/-- The analytic ideal of THESE SAME actual original sections, only on their literal open. -/
def sectionFamilyIdeal {ι : Type} (U : Opens Y) (a : ι → actualComplexSection (n := n) U) :
    GermIdeal n U := finiteFunctionIdeal (fun i => (a i : U → ℂ))

omit [IsComplexManifold n Y] in
/-- Existing finite-function coherence applies to the SAME actual section family. -/
theorem sectionFamilyIdeal_isCoherent {ι : Type} [Fintype ι] (U : Opens Y)
    (a : ι → actualComplexSection (n := n) U) : (sectionFamilyIdeal U a).IsCoherent := by
  exact isCoherent_finiteFunctionIdeal _
    (fun i => (smoothSheaf.contMDiff_section (a i)).mdifferentiable (by simp))

/-- BOTH entire original ideal directions follow from native original section germs. -/
theorem sectionFamilyIdeal_wholeStalk {ι : Type} [Fintype ι] (U : Opens Y)
    (a : ι → actualComplexSection (n := n) U) (y : U) :
    actualWholeSheafStalkIdeal (sectionFamilyIdeal U a) y =
      Ideal.map ((ChartedSpace.locallyRingedSpaceMap (IM := 𝓘(ℂ,ComplexModel n))
        (IN := 𝓘(ℂ,ComplexModel n)) (Subtype.val : U → Y) contMDiff_subtype_val).stalkMap y).hom
        (Ideal.span (Set.range fun i => TopCat.Presheaf.germ
          (actualComplexStructureSheaf (n := n) Y).obj U y.val y.property (a i))) := by
  rw [sectionFamilyIdeal,actualWholeStalk_finiteFunctionIdeal _ y
    (fun i => Eventually.of_forall fun z =>
      ((smoothSheaf.contMDiff_section (a i)) z).mdifferentiableAt (by simp)),
    Ideal.map_span,← Set.range_comp]
  apply congrArg Ideal.span
  congr 1
  funext i
  exact (openInclusion_stalkMap_section U y (a i)).symm

/-- The SAME full minor SECTIONS, with their ORIGINAL finite row/column-map indices. -/
def minorSectionIdeal {p q : ℕ} (U : Opens Y)
    (B : Matrix (Fin p) (Fin q) (actualComplexSection (n := n) U)) (r : ℕ) : GermIdeal n U :=
  sectionFamilyIdeal U (fun ij : (Fin r → Fin p) × (Fin r → Fin q) =>
    (B.submatrix ij.1 ij.2).det)

omit [IsComplexManifold n Y] in
/-- The SAME full minor ideal is genuinely coherent on the literal ORIGINAL open. -/
theorem minorSectionIdeal_isCoherent {p q : ℕ} (U : Opens Y)
    (B : Matrix (Fin p) (Fin q) (actualComplexSection (n := n) U)) (r : ℕ) :
    (minorSectionIdeal U B r).IsCoherent := sectionFamilyIdeal_isCoherent U _

/-- The ENTIRE native analytic ideal is the actual original stalk image of the SAME full ideal. -/
theorem minorSectionIdeal_wholeStalk {p q : ℕ} (U : Opens Y)
    (B : Matrix (Fin p) (Fin q) (actualComplexSection (n := n) U)) (r : ℕ) (y : U) :
    actualWholeSheafStalkIdeal (minorSectionIdeal U B r) y =
      Ideal.map ((ChartedSpace.locallyRingedSpaceMap (IM := 𝓘(ℂ,ComplexModel n))
        (IN := 𝓘(ℂ,ComplexModel n)) (Subtype.val : U → Y) contMDiff_subtype_val).stalkMap y).hom
        (minorIdeal (B.map (TopCat.Presheaf.germ
          (actualComplexStructureSheaf (n := n) Y).obj U y.val y.property).hom) r) := by
  rw [minorSectionIdeal,sectionFamilyIdeal_wholeStalk]
  congr 1
  rw [minorIdeal_map]
  change Ideal.span _ = Ideal.map _ (Ideal.span _)
  rw [Ideal.map_span,← Set.range_comp]
  rfl

end Hironaka.HironakaChowCoherentOriginalMinorIdeal
