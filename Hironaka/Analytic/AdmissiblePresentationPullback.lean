import Hironaka.Analytic.NumericalRestrictedVolume
import Hironaka.Analytic.ClosedFormPullback
import Hironaka.Blowup.BlowupBigPullback
import Hironaka.Analytic.PotentialTheory.LocalPotentials

set_option autoImplicit false

/-!
# Pulling back admissible presentations along a blowup

Source: CT22, Lemma 4.3 (first inequality); blueprint `ana:rv-birational-blowup`.

Let `g : Z → Y` be the blowup of a complex manifold along a smooth centre, `ω`, `ω_Z`
Kähler forms with `-g^*ω + cω_Z ≥ 0`, and `T = θ' + ddᶜu` an `ε`-admissible presentation
of `α = {θ}` along `W`.  Then `g^*θ' + ddᶜ(u ∘ g)` is a `cε`-admissible presentation of
`g^*α = {g^*θ}` along any subvariety `W̃ ⊆ Z` not contained in `g⁻¹ P(u)`:

* `g^*θ' + cεω_Z + ddᶜ(u ∘ g) = g^*(θ' + εω + ddᶜu) + ε(-g^*ω + cω_Z) ≥ 0`
  (holomorphic pullback of theta-PSH functions and adding a semipositive form);
* `u ∘ g` is not `-∞` on any open set, because an open set of `Z` contains a point off
  `g⁻¹ C`, near which `g` is open;
* `u ∘ g` has smooth analytic singularities: locally `u = c log ∑|f_j|² + b` with `b`
  smooth, and composing with the holomorphic chart expression of `g` preserves this form;
* `g^*θ'` represents `g^*α`, since pullback respects Bott--Chern equivalence
  (`θ' = θ + ddᶜh` gives `g^*θ' = g^*θ + ddᶜ(h ∘ g)`).
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.AdmissiblePresentationPullback

open Hironaka.PositiveClasses Hironaka.BlowupSequences
  Hironaka.NumericalRestrictedVolumeScaffold Hironaka.NumericalRestrictedVolume

noncomputable section

variable {n : ℕ}
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

/-- Smooth analytic singularities pull back along holomorphic maps. -/
theorem hasManifoldSmoothAnalyticSingularities_comp {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g) {v : Y → EReal}
    (hv : HasManifoldSmoothAnalyticSingularities (n := n) v) :
    HasManifoldSmoothAnalyticSingularities (n := n) (fun z => v (g z)) := by
  intro e z hz
  set d := complexChartAt (n := n) (g (e.val.symm z))
  set F := HolomorphicMaps.coordinateMap g e d
  have hzd : z ∈ HolomorphicMaps.coordinateDomain g e d := ⟨hz, mem_complexChartAt_source _⟩
  have hD := HolomorphicMaps.coordinateDomain_isOpen hg e d
  have hFc : ContDiffOn ℂ ∞ F (HolomorphicMaps.coordinateDomain g e d) :=
    HolomorphicMaps.coordinateMap_contDiffOn hg e d
  have hFz : ContinuousAt F z :=
    (HolomorphicMaps.coordinateMap_contDiffAt hg e d hzd).continuousAt
  obtain ⟨c, m, f, hc, ⟨U, hU, hwU, hfU⟩, b, hb, heq⟩ :=
    hv d (F z) (HolomorphicMaps.coordinateMap_mem_target hzd)
  refine ⟨c, m, fun j y => f j (F y), hc, ⟨HolomorphicMaps.coordinateDomain g e d ∩ F ⁻¹' U,
    hFc.continuousOn.isOpen_inter_preimage hD hU, ⟨hzd, hwU⟩, fun j => ?_⟩,
    fun y => b (F y), ?_, ?_⟩
  · exact (hfU j).comp ((hFc.differentiableOn (by simp)).mono inter_subset_left)
      (fun y hy => hy.2)
  · filter_upwards [hD.mem_nhds hzd, hFz.eventually hb] with y hy hby
    exact hby.comp y (HolomorphicMaps.coordinateMap_contDiffAt_real hg e d hy)
  · filter_upwards [hD.mem_nhds hzd, hFz.eventually heq] with y hy hey
    have hleft : chartFunction (fun z => v (g z)) e y = chartFunction v d (F y) := by
      show v (g (e.val.symm y)) = v (d.val.symm (d.val (g (e.val.symm y))))
      rw [d.val.left_inv hy.2]
    rw [hleft, hey]
    rfl

/-- **Analytic singularities in the `I-0489` convention pull back along a holomorphic map.**
The generators pull back, so the pole set pulls back and `generatorNormSq` is unchanged; the
remainder `b ∘ F` is bounded because `F` is continuous, and smooth wherever `b` is. -/
theorem hasManifoldAnalyticSingularitiesSmoothOffPole_comp {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g) {v : Y → EReal}
    (hv : HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) v) :
    HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) (fun z => v (g z)) := by
  intro e z hz
  set d := complexChartAt (n := n) (g (e.val.symm z))
  set F := HolomorphicMaps.coordinateMap g e d
  have hzd : z ∈ HolomorphicMaps.coordinateDomain g e d := ⟨hz, mem_complexChartAt_source _⟩
  have hD := HolomorphicMaps.coordinateDomain_isOpen hg e d
  have hFc : ContDiffOn ℂ ∞ F (HolomorphicMaps.coordinateDomain g e d) :=
    HolomorphicMaps.coordinateMap_contDiffOn hg e d
  have hFz : ContinuousAt F z :=
    (HolomorphicMaps.coordinateMap_contDiffAt hg e d hzd).continuousAt
  obtain ⟨c, m, f, hc, ⟨U, hU, hwU, hfU⟩, b, hbdd, hb, heq⟩ :=
    hv d (F z) (HolomorphicMaps.coordinateMap_mem_target hzd)
  refine ⟨c, m, fun j y => f j (F y), hc, ⟨HolomorphicMaps.coordinateDomain g e d ∩ F ⁻¹' U,
    hFc.continuousOn.isOpen_inter_preimage hD hU, ⟨hzd, hwU⟩, fun j => ?_⟩,
    fun y => b (F y), hbdd.comp_continuousAt hFz, ?_, ?_⟩
  · exact (hfU j).comp ((hFc.differentiableOn (by simp)).mono inter_subset_left)
      (fun y hy => hy.2)
  · filter_upwards [hD.mem_nhds hzd, hFz.eventually hb] with y hy hby hne
    have hne' : generatorNormSq f (F y) ≠ 0 := hne
    exact (hby hne').comp y (HolomorphicMaps.coordinateMap_contDiffAt_real hg e d hy)
  · filter_upwards [hD.mem_nhds hzd, hFz.eventually heq] with y hy hey
    have hleft : chartFunction (fun z => v (g z)) e y = chartFunction v d (F y) := by
      show v (g (e.val.symm y)) = v (d.val.symm (d.val (g (e.val.symm y))))
      rw [d.val.left_inv hy.2]
    rw [hleft, hey]
    rfl

/-- Chart-smooth functions pull back to chart-smooth functions along holomorphic maps. -/
theorem chartSmooth_comp {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g) {h : Y → ℝ}
    (hh : ChartSmooth (n := n) h) : ChartSmooth (n := n) (fun z => h (g z)) := by
  intro e u hu
  set d := complexChartAt (n := n) (g (e.val.symm u))
  have hud : u ∈ HolomorphicMaps.coordinateDomain g e d := ⟨hu, mem_complexChartAt_source _⟩
  have h1 := HolomorphicMaps.coordinateMap_contDiffAt_real hg e d hud
  have h2 := (hh d).contDiffAt
    (d.val.open_target.mem_nhds (HolomorphicMaps.coordinateMap_mem_target hud))
  have h3 := ContDiffAt.comp (g := fun z => h (d.val.symm z)) u h2 h1
  refine (h3.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [(HolomorphicMaps.coordinateDomain_isOpen hg e d).mem_nhds hud] with u' hu'
  show h (g (e.val.symm u')) = h (d.val.symm (d.val (g (e.val.symm u'))))
  rw [d.val.left_inv hu'.2]

/-- Pullback of closed real `(1,1)`-forms respects Bott--Chern equivalence. -/
theorem ofRepresentative_pullback_congr {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    {θ θ' : ClosedRealOneOneForm n Y}
    (h : RealBottChern.ofRepresentative θ' = RealBottChern.ofRepresentative θ) :
    RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hg θ') =
      RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hg θ) := by
  obtain ⟨h, hh, heq⟩ := (RealBottChern.ofRepresentative_eq_iff _ _).mp h
  refine (RealBottChern.ofRepresentative_eq_iff _ _).mpr
    ⟨fun z => h (g z), chartSmooth_comp hg hh, fun e z hz => ?_⟩
  set d := complexChartAt (n := n) (g (e.val.symm z))
  have hzd : z ∈ HolomorphicMaps.coordinateDomain g e d := ⟨hz, mem_complexChartAt_source _⟩
  have hD := HolomorphicMaps.coordinateDomain_isOpen hg e d
  have hddc : smoothDDC (fun y => h (g (e.val.symm y))) z =
      (smoothDDC (fun w => h (d.val.symm w)) (HolomorphicMaps.coordinateMap g e d z)).compContinuousLinearMap
        (fderiv ℝ (HolomorphicMaps.coordinateMap g e d) z) := by
    rw [← HolomorphicDDC.smoothDDC_comp hD d.val.open_target
      (HolomorphicMaps.coordinateMap_contDiffOn hg e d) (hh d)
      (fun _ hy => HolomorphicMaps.coordinateMap_mem_target hy) hzd]
    apply smoothDDC_congr
    filter_upwards [hD.mem_nhds hzd] with y hy
    show h (g (e.val.symm y)) = h (d.val.symm (d.val (g (e.val.symm y))))
    rw [d.val.left_inv hy.2]
  rw [ClosedRealOneOneForm.pullback_val, ClosedRealOneOneForm.pullback_val,
    SmoothRealForm.pullback_coeff hg _ e d hzd, SmoothRealForm.pullback_coeff hg _ e d hzd,
    hddc, heq d _ (HolomorphicMaps.coordinateMap_mem_target hzd)]
  ext v
  simp

variable {omega : KahlerBackground n Y} {omegaZ : KahlerBackground n Z}
  {θ : ClosedRealOneOneForm n Y} {W : ClosedIrreducibleAnalyticSubvariety n Y}
  {ε : PositiveError} {C : Set Y} {g : Z → Y}

/-- The pullback of an `ε`-admissible presentation is `cε`-admissible along any
subvariety not contained in the preimage of the polar set. -/
def pullbackPresentation (hg : IsBlowupAlong n C g) {c : ℝ} (hc : 0 < c)
    (hD : (-(ClosedRealOneOneForm.pullback hg.contMDiff omega.form) +
      c • omegaZ.form).val.IsSemipositive)
    (p : AdmissibleRestrictedCurrentPresentation omega (RealBottChern.ofRepresentative θ) W ε)
    (Wt : ClosedIrreducibleAnalyticSubvariety n Z)
    (hWt : ¬ Wt.carrier ⊆ g ⁻¹' poleSet p.potential) :
    AdmissibleRestrictedCurrentPresentation omegaZ
      (RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hg.contMDiff θ)) Wt
      ⟨c * ε, mul_pos hc ε.2⟩ where
  representative := ClosedRealOneOneForm.pullback hg.contMDiff p.representative
  represents := ofRepresentative_pullback_congr hg.contMDiff p.represents
  potential := fun z => p.potential (g z)
  potential_psh := by
    refine ⟨?_, ?_⟩
    · have hpull : ThetaPlurisubharmonic
          (ClosedRealOneOneForm.pullback hg.contMDiff p.representative +
            (ε : ℝ) • ClosedRealOneOneForm.pullback hg.contMDiff omega.form).val
          (fun z => p.potential (g z)) := by
        refine BlowupBigPullback.thetaPlurisubharmonic_of_geometricallyEq ?_
          (GlobalPotentialPullback.thetaPlurisubharmonic_comp hg.contMDiff p.potential_psh.1)
        intro e z hz
        set d := complexChartAt (n := n) (g (e.val.symm z))
        have hzd : z ∈ HolomorphicMaps.coordinateDomain g e d :=
          ⟨hz, mem_complexChartAt_source _⟩
        change (ClosedRealOneOneForm.pullback hg.contMDiff
          (p.representative + (ε : ℝ) • omega.form)).val.coeff e z = _
        simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
          ClosedRealOneOneForm.pullback_val, SmoothRealForm.pullback_coeff hg.contMDiff _ e d hzd]
        ext v
        simp
      have hsemi : ((ε : ℝ) • (-(ClosedRealOneOneForm.pullback hg.contMDiff omega.form) +
          c • omegaZ.form)).val.IsSemipositive := by
        intro e z hz v
        rw [ClosedRealOneOneForm.coeff_smul, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
        exact mul_nonneg ε.2.le (hD e z hz v)
      have hsum := Hironaka.LocalPotentials.thetaPlurisubharmonic_add_of_semipositive hpull hsemi
      have hform : ClosedRealOneOneForm.pullback hg.contMDiff p.representative +
          (ε : ℝ) • ClosedRealOneOneForm.pullback hg.contMDiff omega.form +
          (ε : ℝ) • (-(ClosedRealOneOneForm.pullback hg.contMDiff omega.form) + c • omegaZ.form) =
          ClosedRealOneOneForm.pullback hg.contMDiff p.representative +
            (c * ε : ℝ) • omegaZ.form := by
        rw [smul_add, smul_neg, smul_smul, mul_comm]
        abel
      rw [hform] at hsum
      exact hsum
    · intro x U hU hxU
      have hnot : ¬ U ⊆ g ⁻¹' C := fun hsub => by
        have hx := interior_maximal hsub hU hxU
        rw [ExceptionalFibres.interior_preimage_eq_empty hg] at hx
        exact hx
      obtain ⟨z₀, hz₀U, hz₀C⟩ := not_subset.mp hnot
      have hz₀E : z₀ ∉ exceptionalLocus n g := fun hE =>
        hz₀C (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hg hE)
      have himg : g '' U ∈ 𝓝 (g z₀) := by
        rw [← StrictTransformComposition.map_nhds_eq_of_not_mem_exceptionalLocus
          hg.contMDiff hz₀E]
        exact image_mem_map (hU.mem_nhds hz₀U)
      obtain ⟨y, hyi, hy⟩ := p.potential_psh.2 (g z₀) _ isOpen_interior
        (mem_interior_iff_mem_nhds.mpr himg)
      obtain ⟨z, hzU, rfl⟩ := interior_subset hyi
      exact ⟨z, hzU, hy⟩
  smoothAnalyticSingularities :=
    hasManifoldAnalyticSingularitiesSmoothOffPole_comp hg.contMDiff p.smoothAnalyticSingularities
  not_carrier_subset_poleSet := hWt

@[simp] theorem pullbackPresentation_potential (hg : IsBlowupAlong n C g) {c : ℝ} (hc : 0 < c)
    (hD : (-(ClosedRealOneOneForm.pullback hg.contMDiff omega.form) +
      c • omegaZ.form).val.IsSemipositive)
    (p : AdmissibleRestrictedCurrentPresentation omega (RealBottChern.ofRepresentative θ) W ε)
    (Wt : ClosedIrreducibleAnalyticSubvariety n Z)
    (hWt : ¬ Wt.carrier ⊆ g ⁻¹' poleSet p.potential) (z : Z) :
    (pullbackPresentation hg hc hD p Wt hWt).potential z = p.potential (g z) := rfl

/-- The coordinate form of the pulled-back presentation: the pullback of the coordinate
data of `θ' + εω`, the `ddᶜ` of the composed potential, and the semipositive correction
`ε(-g^*ω + cω_Z)`. -/
theorem coordinateCurrentForm_pullbackPresentation (hg : IsBlowupAlong n C g) {c : ℝ}
    (hc : 0 < c)
    (hD : (-(ClosedRealOneOneForm.pullback hg.contMDiff omega.form) +
      c • omegaZ.form).val.IsSemipositive)
    (p : AdmissibleRestrictedCurrentPresentation omega (RealBottChern.ofRepresentative θ) W ε)
    (Wt : ClosedIrreducibleAnalyticSubvariety n Z)
    (hWt : ¬ Wt.carrier ⊆ g ⁻¹' poleSet p.potential)
    (e : ComplexChart n Z) {z : ComplexModel n} (hz : z ∈ e.val.target) :
    coordinateCurrentForm (pullbackPresentation hg hc hD p Wt hWt) e z =
      (ClosedRealOneOneForm.pullback hg.contMDiff (perturbedRepresentative p)).val.coeff e z +
        smoothDDC (fun y => (p.potential (g (e.val.symm y))).toReal) z +
        (ε : ℝ) • (-(ClosedRealOneOneForm.pullback hg.contMDiff omega.form) +
          c • omegaZ.form).val.coeff e z := by
  set d := complexChartAt (n := n) (g (e.val.symm z))
  have hzd : z ∈ HolomorphicMaps.coordinateDomain g e d := ⟨hz, mem_complexChartAt_source _⟩
  simp only [coordinateCurrentForm, perturbedRepresentative, pullbackPresentation,
    ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
    ClosedRealOneOneForm.coeff_neg, ClosedRealOneOneForm.pullback_val,
    SmoothRealForm.pullback_coeff hg.contMDiff _ e d hzd]
  ext v
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.neg_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    smul_eq_mul]
  ring

end

end Hironaka.AdmissiblePresentationPullback
