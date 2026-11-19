import Hironaka.Analytic.Unibranch.HironakaG10SmoothBaseFlatOpen
import Hironaka.Resolution.HironakaNonreducedAnalyticQuotientModel
import Hironaka.Resolution.HironakaActualProjectionIntrinsicHS
import Hironaka.Resolution.HironakaActualAnalyticSubspaceOpenRestriction

/-! The actual flat locus of a coherent analytic quotient projected to a
smooth coordinate base, retaining its whole possibly nonradical ideal. -/

set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10CoherentProjectionFlatOpen
noncomputable section
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HolGerm OkaRelationSheaf OkaGermBridge
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaHolomorphicJetRankLoci
  HironakaActualWholeStalkHolomorphicPullback HironakaRelativeNormalIdeal
  HironakaNonreducedAnalyticQuotientModel HironakaActualAnalyticSubspaceOpenRestriction
  HironakaActualProjectionIntrinsicHS HironakaG10HirChartFlattener
  HironakaG10SmoothBaseFlatOpen

def projection (d t : ℕ) (I : GermIdeal (d + t) (ComplexModel (d + t)))
    (hI : I.IsCoherent) : quotientLocallyRingedSpace I hI ⟶
      ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel d) (ComplexModel d) :=
  quotientInclusion I hI ≫ ChartedSpace.locallyRingedSpaceMap (tangentProjection d t)
    (tangentProjection d t).contDiff.contMDiff

private theorem chart_inclusion {n : ℕ} (I : GermIdeal n (ComplexModel n)) (hI : I.IsCoherent)
    (x : I.zeroLocus) (r : actualComplexStructureStalk (n := n) x.val) :
    quotientStalkChartEquiv I hI x ((quotientInclusion I hI).stalkMap x r) =
      Ideal.Quotient.mk (wholeChartStalkIdeal I x.val x.val (mem_chart_source _ x.val))
        (actualStalkChartEquiv (n := n) x.val r) := by
  simp only [quotientStalkChartEquiv, RingEquiv.trans_apply, quotientInclusion_stalk]
  rfl

theorem projection_stalk_square (d t : ℕ)
    (I : GermIdeal (d + t) (ComplexModel (d + t))) (hI : I.IsCoherent) (x : I.zeroLocus)
    (a : HolGerm (ComplexModel d)) :
    quotientStalkChartEquiv I hI x
      ((projection d t I hI).stalkMap x
        ((actualStalkChartEquiv (n := d) (tangentProjection d t x.val)).symm a)) =
      Ideal.Quotient.mk (wholeChartStalkIdeal I x.val x.val (mem_chart_source _ x.val))
        (tangentPullback d t a) := by
  change quotientStalkChartEquiv I hI x
    ((quotientInclusion I hI ≫ ChartedSpace.locallyRingedSpaceMap (tangentProjection d t)
      (tangentProjection d t).contDiff.contMDiff).stalkMap x
        ((actualStalkChartEquiv (n := d) (tangentProjection d t x.val)).symm a)) = _
  rw [LocallyRingedSpace.stalkMap_comp]
  change quotientStalkChartEquiv I hI x ((quotientInclusion I hI).stalkMap x
    ((ChartedSpace.locallyRingedSpaceMap (tangentProjection d t)
      (tangentProjection d t).contDiff.contMDiff).stalkMap x.val
        ((actualStalkChartEquiv (n := d) (tangentProjection d t x.val)).symm a))) = _
  rw [chart_inclusion, actualNativeStalk_chart_pullback, RingEquiv.apply_symm_apply,
    actualHolomorphicGermPullback_tangentProjection]

theorem projection_flat_iff_chartMap (d t : ℕ)
    (I : GermIdeal (d + t) (ComplexModel (d + t))) (hI : I.IsCoherent) (x : I.zeroLocus) :
    ((projection d t I hI).stalkMap x).hom.Flat ↔
      (chartMap d t (wholeChartStalkIdeal I x.val x.val (mem_chart_source _ x.val))).Flat := by
  let eS := quotientStalkChartEquiv I hI x
  let eB := actualStalkChartEquiv (n := d) (tangentProjection d t x.val)
  have he : eS.toRingHom.comp (((projection d t I hI).stalkMap x).hom.comp eB.symm.toRingHom) =
      chartMap d t (wholeChartStalkIdeal I x.val x.val (mem_chart_source _ x.val)) := by
    ext a
    exact projection_stalk_square d t I hI x a
  calc
    _ ↔ (((projection d t I hI).stalkMap x).hom.comp eB.symm.toRingHom).Flat :=
      (RingHom.Flat.comp_iff_of_bijective_right eB.symm.bijective).symm
    _ ↔ (eS.toRingHom.comp
        (((projection d t I hI).stalkMap x).hom.comp eB.symm.toRingHom)).Flat :=
      (RingHom.Flat.comp_iff_of_bijective_left eS.bijective).symm
    _ ↔ _ := Iff.of_eq (congrArg RingHom.Flat he)

theorem chartTranslatedGerm_eq_germAt {n : ℕ} (p : ComplexModel n)
    (f : ComplexModel n → ℂ) (hf : HolomorphicAt n f p) :
    chartTranslatedGerm p p (mem_chart_source _ p) f hf = germAt p f := by
  have hfc : HolAt f p := hf.mono fun _ h => h.differentiableAt
  unfold chartTranslatedGerm translatedGerm
  rw [germAt_of_holAt hfc]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z => by
    simp [chartAt_self_eq, add_comm]

theorem whole_ideal_eq_germ_span {n : ℕ} (I : GermIdeal n (ComplexModel n)) (p : ComplexModel n)
    {r : ℕ} (g : Fin r → ComplexModel n → ℂ) (hg : ∀ j, HolomorphicAt n (g j) p)
    (hgen : ∀ f, I.mem p f ↔ IsInSpanAt (n := n) (· ∈ Set.range g) p f) :
    wholeChartStalkIdeal I p p (mem_chart_source _ p) =
      Ideal.span (Set.range fun j => germAt p (g j)) := by
  rw [wholeChartStalkIdeal_eq_actual_generator_span I p g hg hgen]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext j
  exact chartTranslatedGerm_eq_germAt p (g j) (hg j)

theorem chartMap_flat_congr_ideal (d t : ℕ)
    {I J : Ideal (HolGerm (ComplexModel (d + t)))} (h : I = J) :
    (chartMap d t I).Flat ↔ (chartMap d t J).Flat := by
  subst J
  rfl

def productRow {r : ℕ} (d t : ℕ) (g : Fin r → ComplexModel (d + t) → ℂ) :
    Fin 1 → Fin r → ComplexModel d × ComplexModel t → ℂ :=
  fun _ j q => g j ((splitModel d t).symm q)

theorem holAt_productRow {r : ℕ} (d t : ℕ) (g : Fin r → ComplexModel (d + t) → ℂ)
    (w : ComplexModel (d + t)) (hg : ∀ j, HolAt (g j) w) :
    ∀ i j, HolAt (productRow d t g i j) (splitModel d t w) := by
  intro i j
  have h : HolAt (g j) ((splitModel d t).symm (splitModel d t w)) := by
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact hg j
  exact h.comp (splitModel d t).symm.continuous (fun _ => (splitModel d t).symm.differentiableAt)

theorem centred_productRow_entryIdeal {r : ℕ} (d t : ℕ)
    (g : Fin r → ComplexModel (d + t) → ℂ) (w : ComplexModel (d + t))
    (hg : ∀ j, HolAt (g j) w) :
    HironakaG10LinearCurveMatrixPullback.entryIdeal d t
      (centredMatrix d t (productRow d t g) (splitModel d t w)) =
        Ideal.span (Set.range fun j => germAt w (g j)) := by
  unfold HironakaG10LinearCurveMatrixPullback.entryIdeal
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext j
  rw [germAt_of_holAt
      (holAt_centredMatrix d t (productRow d t g) (splitModel d t w)
        (holAt_productRow d t g w hg) 0 j), germAt_of_holAt (hg j)]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z => by
    change g j ((splitModel d t).symm (splitModel d t w + splitModel d t (0 + z))) = g j (w + z)
    rw [zero_add, map_add, ContinuousLinearEquiv.symm_apply_apply,
      ContinuousLinearEquiv.symm_apply_apply]

theorem rowFlat_iff_productStalkFlat {r : ℕ} (d t : ℕ)
    (g : Fin r → ComplexModel (d + t) → ℂ) (w : ComplexModel (d + t))
    (hg : ∀ j, HolAt (g j) w) :
    (chartMap d t (Ideal.span (Set.range fun j => germAt w (g j)))).Flat ↔
      StalkFlatAt d t (productRow d t g) (splitModel d t w) :=
  (chartMap_flat_congr_ideal d t (centred_productRow_entryIdeal d t g w hg)).symm.trans
    (native_flat_iff_stalkFlatAt d t (productRow d t g) (splitModel d t w)
      (holAt_productRow d t g w hg))

theorem isOpen_native_row_flat_locus {r : ℕ} (d t : ℕ)
    (g : Fin r → ComplexModel (d + t) → ℂ) {W : Set (ComplexModel (d + t))}
    (hW : IsOpen W) (hg : ∀ j, DifferentiableOn ℂ (g j) W) :
    IsOpen {w | w ∈ W ∧ (chartMap d t (Ideal.span (Set.range fun j => germAt w (g j)))).Flat} := by
  let V : Set (ComplexModel d × ComplexModel t) := (splitModel d t).symm ⁻¹' W
  have hV : IsOpen V := hW.preimage (splitModel d t).symm.continuous
  have hF : ∀ i j, DifferentiableOn ℂ (productRow d t g i j) V :=
    fun _ j => (hg j).comp (splitModel d t).symm.differentiable.differentiableOn (fun _ h => h)
  have hSet : {w | w ∈ W ∧ (chartMap d t (Ideal.span (Set.range fun j => germAt w (g j)))).Flat} =
      (splitModel d t) ⁻¹' {q | q ∈ V ∧ StalkFlatAt d t (productRow d t g) q} := by
    ext w
    constructor
    · rintro ⟨hw, hflat⟩
      exact ⟨by simpa only [V, mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hw,
        (rowFlat_iff_productStalkFlat d t g w
          (fun j => holAt_of_differentiableOn hW (hg j) hw)).mp hflat⟩
    · rintro ⟨hw, hflat⟩
      have hw' : w ∈ W := by
        simpa only [V, mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hw
      exact ⟨hw', (rowFlat_iff_productStalkFlat d t g w
        (fun j => holAt_of_differentiableOn hW (hg j) hw')).mpr hflat⟩
  rw [hSet]
  exact (isOpen_stalkFlatLocus d t (productRow d t g) hV hF).preimage (splitModel d t).continuous

/-- Openness for the actual coherent quotient projection, with one uniform
generator window chosen internally and with the whole nonradical ideal retained. -/
theorem isOpen_flatLocus_projection (d t : ℕ)
    (I : GermIdeal (d + t) (ComplexModel (d + t))) (hI : I.IsCoherent) :
    IsOpen {x : I.zeroLocus | ((projection d t I hI).stalkMap x).hom.Flat} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨W, hW, hxW, r, g, hg, hgen⟩ := hI x.val
  have hgc : ∀ j, DifferentiableOn ℂ (g j) W :=
    fun j w hw => (hg j w hw).differentiableWithinAt
  have hwhole (w : ComplexModel (d + t)) (hw : w ∈ W) :
      wholeChartStalkIdeal I w w (mem_chart_source _ w) =
        Ideal.span (Set.range fun j => germAt w (g j)) :=
    whole_ideal_eq_germ_span I w g
      (fun j => InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hW (hg j) hw)
      (hgen w hw)
  have hopen := (isOpen_native_row_flat_locus d t g hW hgc).preimage
    (continuous_subtype_val : Continuous (Subtype.val : I.zeroLocus → ComplexModel (d + t)))
  have hxrow := (chartMap_flat_congr_ideal d t (hwhole x.val hxW)).mp
    ((projection_flat_iff_chartMap d t I hI x).mp hx)
  refine mem_of_superset (hopen.mem_nhds ⟨hxW, hxrow⟩) ?_
  rintro y ⟨hyW, hyrow⟩
  exact (projection_flat_iff_chartMap d t I hI y).mpr
    ((chartMap_flat_congr_ideal d t (hwhole y.val hyW)).mpr hyrow)

end
end Hironaka.Analytic.Unibranch.HironakaG10CoherentProjectionFlatOpen
