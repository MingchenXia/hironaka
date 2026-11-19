import Hironaka.Analytic.Unibranch.HironakaG10OpenChartHelpers
import Hironaka.Analytic.Unibranch.HironakaG10CoherentProjectionFlatOpen
import Hironaka.Resolution.HironakaActualOpenIntrinsicHS
import Hironaka.Coherence.CartanLocalReduction

/-! Actual coherent quotient projection on an open Euclidean ambient.
The ideal is never extended across the open boundary. -/

set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10OpenCoherentProjectionFlatOpen
noncomputable section
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HolGerm OkaRelationSheaf OkaGermBridge
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaHolomorphicJetRankLoci
  HironakaActualWholeStalkHolomorphicPullback HironakaRelativeNormalIdeal
  HironakaNonreducedAnalyticQuotientModel HironakaActualAnalyticSubspaceOpenRestriction
  HironakaActualProjectionIntrinsicHS HironakaActualOpenIntrinsicHS HironakaActualBiholomorphicWholeStalkHS
  HironakaG10HirChartFlattener HironakaG10CoherentProjectionFlatOpen

def projection (d t : ℕ) (O : Opens (ComplexModel (d + t)))
    (I : GermIdeal (d + t) O) (hI : I.IsCoherent) : quotientLocallyRingedSpace I hI ⟶
      ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel d) (ComplexModel d) :=
  quotientInclusion I hI ≫ ChartedSpace.locallyRingedSpaceMap
    (fun x : O => tangentProjection d t x.val)
    ((tangentProjection d t).contDiff.contMDiff.comp contMDiff_subtype_val)

theorem tangent_on_open_germ (d t : ℕ) (O : Opens (ComplexModel (d + t))) (p : O) :
    actualHolomorphicGermPullback
      ((tangentProjection d t).contDiff.contMDiff.comp (contMDiff_subtype_val :
        ContMDiff 𝓘(ℂ, ComplexModel (d + t)) 𝓘(ℂ, ComplexModel (d + t)) ∞
          (Subtype.val : O → ComplexModel (d + t)))) p = tangentPullback d t := by
  have h := actualHolomorphicGermPullback_comp (f := tangentProjection d t)
    (g := (Subtype.val : O → ComplexModel (d + t)))
    (tangentProjection d t).contDiff.contMDiff contMDiff_subtype_val p
  rw [actualHolomorphicGermPullback_val, actualHolomorphicGermPullback_tangentProjection] at h
  simpa only [AlgHom.id_comp] using h

private theorem chart_inclusion {n : ℕ} (O : Opens (ComplexModel n))
    (I : GermIdeal n O) (hI : I.IsCoherent) (x : I.zeroLocus)
    (r : actualComplexStructureStalk (n := n) x.val) :
    quotientStalkChartEquiv I hI x ((quotientInclusion I hI).stalkMap x r) =
      Ideal.Quotient.mk (wholeChartStalkIdeal I x.val x.val (mem_chart_source _ x.val))
        (actualStalkChartEquiv (n := n) x.val r) := by
  simp only [quotientStalkChartEquiv, RingEquiv.trans_apply, quotientInclusion_stalk]
  rfl

theorem projection_stalk_square (d t : ℕ) (O : Opens (ComplexModel (d + t)))
    (I : GermIdeal (d + t) O) (hI : I.IsCoherent) (x : I.zeroLocus)
    (a : HolGerm (ComplexModel d)) :
    quotientStalkChartEquiv I hI x ((projection d t O I hI).stalkMap x
      ((actualStalkChartEquiv (n := d) (tangentProjection d t x.val.val)).symm a)) =
      Ideal.Quotient.mk (wholeChartStalkIdeal I x.val x.val (mem_chart_source _ x.val))
        (tangentPullback d t a) := by
  change quotientStalkChartEquiv I hI x
    ((quotientInclusion I hI ≫ ChartedSpace.locallyRingedSpaceMap
      (fun p : O => tangentProjection d t p.val)
      ((tangentProjection d t).contDiff.contMDiff.comp contMDiff_subtype_val)).stalkMap x
        ((actualStalkChartEquiv (n := d) (tangentProjection d t x.val.val)).symm a)) = _
  rw [LocallyRingedSpace.stalkMap_comp]
  change quotientStalkChartEquiv I hI x ((quotientInclusion I hI).stalkMap x
    ((ChartedSpace.locallyRingedSpaceMap (fun p : O => tangentProjection d t p.val)
      ((tangentProjection d t).contDiff.contMDiff.comp contMDiff_subtype_val)).stalkMap x.val
        ((actualStalkChartEquiv (n := d) (tangentProjection d t x.val.val)).symm a))) = _
  rw [chart_inclusion, actualNativeStalk_chart_pullback, RingEquiv.apply_symm_apply,
    tangent_on_open_germ]

theorem projection_flat_iff_chartMap (d t : ℕ) (O : Opens (ComplexModel (d + t)))
    (I : GermIdeal (d + t) O) (hI : I.IsCoherent) (x : I.zeroLocus) :
    ((projection d t O I hI).stalkMap x).hom.Flat ↔
      (chartMap d t (wholeChartStalkIdeal I x.val x.val (mem_chart_source _ x.val))).Flat := by
  let eS := quotientStalkChartEquiv I hI x
  let eB := actualStalkChartEquiv (n := d) (tangentProjection d t x.val.val)
  have he : eS.toRingHom.comp (((projection d t O I hI).stalkMap x).hom.comp eB.symm.toRingHom) =
      chartMap d t (wholeChartStalkIdeal I x.val x.val (mem_chart_source _ x.val)) := by
    ext a
    exact projection_stalk_square d t O I hI x a
  calc
    _ ↔ (((projection d t O I hI).stalkMap x).hom.comp eB.symm.toRingHom).Flat :=
      (RingHom.Flat.comp_iff_of_bijective_right eB.symm.bijective).symm
    _ ↔ (eS.toRingHom.comp
        (((projection d t O I hI).stalkMap x).hom.comp eB.symm.toRingHom)).Flat :=
      (RingHom.Flat.comp_iff_of_bijective_left eS.bijective).symm
    _ ↔ _ := Iff.of_eq (congrArg RingHom.Flat he)

theorem whole_ideal_eq_open_germ_span {n r : ℕ} (O : Opens (ComplexModel n))
    (I : GermIdeal n O) (x y : O) (g : Fin r → O → ℂ)
    (hg : ∀ j, HolomorphicAt n (g j) y)
    (hgen : ∀ f, I.mem y f ↔ IsInSpanAt (n := n) (· ∈ Set.range g) y f) :
    wholeChartStalkIdeal I y y (mem_chart_source _ y) =
      Ideal.span (Set.range fun j => germAt y.val
        (fun z => g j ((chartAt (ComplexModel n) x).symm z))) := by
  rw [wholeChartStalkIdeal_eq_actual_generator_span I y g hg hgen]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext j
  exact chartTranslatedGerm_open_eq_germAt O x y (g j) (hg j)

theorem exists_generator_window {n : ℕ} (O : Opens (ComplexModel n))
    (I : GermIdeal n O) (hI : I.IsCoherent) (x : O) :
    ∃ (V : Set (ComplexModel n)), IsOpen V ∧ x.val ∈ V ∧ V ⊆ O ∧
      ∃ (r : ℕ) (H : Fin r → ComplexModel n → ℂ),
        (∀ j, DifferentiableOn ℂ (H j) V) ∧ ∀ (y : O), y.val ∈ V →
          wholeChartStalkIdeal I y y (mem_chart_source _ y) =
            Ideal.span (Set.range fun j => germAt y.val (H j)) := by
  obtain ⟨W, hW, hxW, r, g, hg, hgen⟩ := hI x
  let e := chartAt (ComplexModel n) x
  let H : Fin r → ComplexModel n → ℂ := fun j z => g j (e.symm z)
  let V : Set (ComplexModel n) := e '' W
  have hV : IsOpen V := e.isOpen_image_of_subset_source hW (by
    rw [show e.source = Set.univ from open_chart_source O x]
    exact Set.subset_univ W)
  refine ⟨V, hV, ⟨x, hxW, rfl⟩, ?_, r, H, ?_, ?_⟩
  · rintro _ ⟨y, _, rfl⟩
    exact y.property
  · intro j w hw
    obtain ⟨y, hy, rfl⟩ := hw
    have hys : y ∈ e.source := by rw [open_chart_source]; trivial
    exact (CartanLocalReduction.holAt_comp_chart_symm hys
      (InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hW (hg j) hy)).self_of_nhds.differentiableWithinAt
  · intro y hyV
    have hyW : y ∈ W := by
      obtain ⟨z, hz, heq⟩ := hyV
      have hzy : z = y := Subtype.ext heq
      exact hzy ▸ hz
    exact whole_ideal_eq_open_germ_span O I x y g
      (fun j => InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hW (hg j) hyW)
      (hgen y hyW)

theorem isOpen_flatLocus_projection (d t : ℕ) (O : Opens (ComplexModel (d + t)))
    (I : GermIdeal (d + t) O) (hI : I.IsCoherent) :
    IsOpen {x : I.zeroLocus | ((projection d t O I hI).stalkMap x).hom.Flat} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨V, hV, hxV, _, r, H, hH, hwhole⟩ := exists_generator_window O I hI x.val
  have hopen := (isOpen_native_row_flat_locus d t H hV hH).preimage
    ((continuous_subtype_val : Continuous (Subtype.val : O → ComplexModel (d + t))).comp
      (continuous_subtype_val : Continuous (Subtype.val : I.zeroLocus → O)))
  have hxrow := (chartMap_flat_congr_ideal d t (hwhole x.val hxV)).mp
    ((projection_flat_iff_chartMap d t O I hI x).mp hx)
  refine mem_of_superset (hopen.mem_nhds ⟨hxV, hxrow⟩) ?_
  rintro y ⟨hyV, hyrow⟩
  exact (projection_flat_iff_chartMap d t O I hI y).mpr
    ((chartMap_flat_congr_ideal d t (hwhole y.val hyV)).mpr hyrow)

end
end Hironaka.Analytic.Unibranch.HironakaG10OpenCoherentProjectionFlatOpen
