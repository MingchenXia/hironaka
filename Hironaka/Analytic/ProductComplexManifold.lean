import Hironaka.Manifold.ComplexManifold
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Hironaka.Analytic.ClosedFormPullback
import Hironaka.Analytic.PositiveClasses
import Hironaka.Analytic.KahlerPerturbation
import Hironaka.Blowup.BlowupSequences

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The product of two complex manifolds, modelled on `ℂⁿ⁺ᵐ`

Source: Boucksom, *On the volume of a line bundle*, proof of Theorem 4.8
(`bou02-volume:4.8`, `references/bou02-volume/source/volume.tex:737-760`), and Demailly--Păun,
Theorem 2.12 (`dp04-kahler-cone:2.12`): the bigness criterion is proved on the product
`X × X`, with the classes `p₁^*α + p₂^*α` and the diagonal `Δ`.  This module supplies the
product as a complex manifold in this project's sense (phase TN.4, plan
`.archon-horizon/scratch/tn4-plan-0133.md`, step B1).

mathlib's `prodChartedSpace` models `X × Y` on `ComplexModel n × ComplexModel m`; every complex
manifold of the project is modelled on some `ComplexModel k = EuclideanSpace ℂ (Fin k)`.  The two
are identified by the linear equivalence `prodModelEquiv n m` (`EuclideanSpace.finAddEquivProd`).

## Main results

* `chartedSpace` — `X × Y` charted on `ComplexModel (n + m)`, the chart at `p` being the
  product chart at `(p.1, p.2)` followed by `prodModelEquiv` (`chartAt_prod`).  A scoped
  instance (`open scoped ProductComplexManifold`): it is not global because `X × Y` already
  carries mathlib's product structure on a different model.
* `isComplexManifold` — with it, `X × Y` is an `IsComplexManifold (n + m)` (scoped instance).
* `contMDiff_fst`, `contMDiff_snd` — the projections are holomorphic;
  `contMDiff_prodMk` — a pair of holomorphic maps is holomorphic into the product;
  `contMDiff_prodMap`, `contMDiff_diag` — products of holomorphic maps and the diagonal map.
* `prodForm_isKahler`, `prodKahlerBackground` — `p₁^*ω₁ + p₂^*ω₂` is a Kähler form on `X × Y`
  (`eq_zero_of_fderiv_coordinateMap_fst`/`_snd`: a tangent vector killed by both projections is 0;
  `pullback_coeff_pos`: the strict half of the pullback of a Hermitian form, pointwise).
* `regularAtDim_diagonal`, `isClosedConnectedSubmanifold_diagonal` — the diagonal of a connected
  `X` is a closed connected submanifold of `X × X` of dimension `n`, flattened in the product chart
  at `(p, p)` by the affine change `diagFlatten : L(u, u') ↦ L(u - u₀, u' - u)`.

No consumer yet: this is infrastructure for the product argument of Boucksom 4.8 (B3/B4 of the plan:
the mass concentration on the diagonal and the support statement on `Δ`).
-/

open Set
open scoped Manifold ContDiff

namespace Hironaka.ProductComplexManifold



noncomputable section

/-- The linear identification `ℂⁿ × ℂᵐ ≃ ℂⁿ⁺ᵐ`. -/
def prodModelEquiv (n m : ℕ) : (ComplexModel n × ComplexModel m) ≃L[ℂ] ComplexModel (n + m) :=
  EuclideanSpace.finAddEquivProd.symm

variable {n m : ℕ} {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y]

/-- The product chart, followed by the identification `ℂⁿ × ℂᵐ ≃ ℂⁿ⁺ᵐ`. -/
def prodChart (e : OpenPartialHomeomorph X (ComplexModel n))
    (e' : OpenPartialHomeomorph Y (ComplexModel m)) :
    OpenPartialHomeomorph (X × Y) (ComplexModel (n + m)) :=
  (e.prod e').trans (prodModelEquiv n m).toHomeomorph.toOpenPartialHomeomorph

@[simp] theorem prodChart_apply (e : OpenPartialHomeomorph X (ComplexModel n))
    (e' : OpenPartialHomeomorph Y (ComplexModel m)) (p : X × Y) :
    prodChart e e' p = prodModelEquiv n m (e p.1, e' p.2) := rfl

@[simp] theorem prodChart_symm_apply (e : OpenPartialHomeomorph X (ComplexModel n))
    (e' : OpenPartialHomeomorph Y (ComplexModel m)) (z : ComplexModel (n + m)) :
    (prodChart e e').symm z =
      (e.symm ((prodModelEquiv n m).symm z).1, e'.symm ((prodModelEquiv n m).symm z).2) := rfl

@[simp] theorem prodChart_source (e : OpenPartialHomeomorph X (ComplexModel n))
    (e' : OpenPartialHomeomorph Y (ComplexModel m)) :
    (prodChart e e').source = e.source ×ˢ e'.source := by
  simp [prodChart]

@[simp] theorem prodChart_target (e : OpenPartialHomeomorph X (ComplexModel n))
    (e' : OpenPartialHomeomorph Y (ComplexModel m)) :
    (prodChart e e').target = (prodModelEquiv n m).symm ⁻¹' (e.target ×ˢ e'.target) := by
  ext z
  simp [prodChart]

variable [ChartedSpace (ComplexModel n) X] [ChartedSpace (ComplexModel m) Y]

/-- `X × Y` modelled on `ℂⁿ⁺ᵐ`.  Not a global instance: `X × Y` already carries mathlib's
product structure modelled on `ℂⁿ × ℂᵐ`; see `open scoped ProductComplexManifold`. -/
@[instance_reducible]
def chartedSpace : ChartedSpace (ComplexModel (n + m)) (X × Y) where
  atlas := image2 prodChart (atlas (ComplexModel n) X) (atlas (ComplexModel m) Y)
  chartAt p := prodChart (chartAt (ComplexModel n) p.1) (chartAt (ComplexModel m) p.2)
  mem_chart_source p := by simp
  chart_mem_atlas p := mem_image2_of_mem (chart_mem_atlas _ _) (chart_mem_atlas _ _)

attribute [scoped instance] chartedSpace

@[simp] theorem chartAt_prod (p : X × Y) :
    chartAt (ComplexModel (n + m)) p =
      prodChart (chartAt (ComplexModel n) p.1) (chartAt (ComplexModel m) p.2) := rfl

/-- The chart transitions of the product atlas are holomorphic. -/
theorem contDiffOn_transition [IsComplexManifold n X] [IsComplexManifold m Y]
    {a a' : OpenPartialHomeomorph X (ComplexModel n)} {b b' : OpenPartialHomeomorph Y (ComplexModel m)}
    (ha : a ∈ atlas (ComplexModel n) X) (ha' : a' ∈ atlas (ComplexModel n) X)
    (hb : b ∈ atlas (ComplexModel m) Y) (hb' : b' ∈ atlas (ComplexModel m) Y) :
    ContDiffOn ℂ ∞ ((prodChart a b).symm ≫ₕ prodChart a' b')
      ((prodChart a b).symm ≫ₕ prodChart a' b').source := by
  set L := prodModelEquiv n m
  have hA : ContDiffOn ℂ ∞ (a.symm ≫ₕ a') (a.symm ≫ₕ a').source := by
    have h := (HasGroupoid.compatible (G := contDiffGroupoid ∞ 𝓘(ℂ, ComplexModel n)) ha ha').1
    simpa [contDiffPregroupoid] using h
  have hB : ContDiffOn ℂ ∞ (b.symm ≫ₕ b') (b.symm ≫ₕ b').source := by
    have h := (HasGroupoid.compatible (G := contDiffGroupoid ∞ 𝓘(ℂ, ComplexModel m)) hb hb').1
    simpa [contDiffPregroupoid] using h
  have hAB := hA.prodMap hB
  have hmaps : MapsTo L.symm ((prodChart a b).symm ≫ₕ prodChart a' b').source
      ((a.symm ≫ₕ a').source ×ˢ (b.symm ≫ₕ b').source) := by
    intro z hz
    simp only [OpenPartialHomeomorph.trans_source, prodChart_target, prodChart_symm_apply,
      prodChart_source, mem_inter_iff, mem_preimage, mem_prod, OpenPartialHomeomorph.symm_source] at hz
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source, mem_prod,
      mem_inter_iff, mem_preimage]
    exact ⟨⟨hz.1.1, hz.2.1⟩, ⟨hz.1.2, hz.2.2⟩⟩
  have hcomp := (L.contDiff.comp_contDiffOn (hAB.comp L.symm.contDiff.contDiffOn hmaps))
  refine hcomp.congr ?_
  intro z hz
  rfl

/-- The product of two complex manifolds is a complex manifold of the summed dimension. -/
scoped instance isComplexManifold [IsComplexManifold n X] [IsComplexManifold m Y] :
    IsComplexManifold (n + m) (X × Y) where
  toIsManifold := isManifold_of_contDiffOn _ _ _ (by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
    simpa using contDiffOn_transition ha ha' hb hb')

variable [IsComplexManifold n X] [IsComplexManifold m Y]

/-- The first projection is holomorphic. -/
theorem contMDiff_fst :
    ContMDiff 𝓘(ℂ, ComplexModel (n + m)) 𝓘(ℂ, ComplexModel n) ∞ (Prod.fst : X × Y → X) := by
  rw [contMDiff_iff]
  refine ⟨continuous_fst, fun p y => ?_⟩
  set L := prodModelEquiv n m
  set a := chartAt (ComplexModel n) p.1
  set c := chartAt (ComplexModel n) y
  have hA : ContDiffOn ℂ ∞ (a.symm ≫ₕ c) (a.symm ≫ₕ c).source := by
    have h := (HasGroupoid.compatible (G := contDiffGroupoid ∞ 𝓘(ℂ, ComplexModel n))
      (chart_mem_atlas _ p.1) (chart_mem_atlas _ y)).1
    simpa [contDiffPregroupoid] using h
  have hlin : ContDiff ℂ ∞ (fun z : ComplexModel (n + m) => (L.symm z).1) :=
    (ContinuousLinearMap.fst ℂ _ _).contDiff.comp L.symm.contDiff
  refine (hA.comp hlin.contDiffOn ?_).congr ?_
  · intro z hz
    simp only [extChartAt, OpenPartialHomeomorph.extend, mem_inter_iff, mem_preimage] at hz
    simp_all [a, c, L]
  · intro z hz
    simp [extChartAt, OpenPartialHomeomorph.extend, a, c, L]

/-- The second projection is holomorphic. -/
theorem contMDiff_snd :
    ContMDiff 𝓘(ℂ, ComplexModel (n + m)) 𝓘(ℂ, ComplexModel m) ∞ (Prod.snd : X × Y → Y) := by
  rw [contMDiff_iff]
  refine ⟨continuous_snd, fun p y => ?_⟩
  set L := prodModelEquiv n m
  set b := chartAt (ComplexModel m) p.2
  set c := chartAt (ComplexModel m) y
  have hB : ContDiffOn ℂ ∞ (b.symm ≫ₕ c) (b.symm ≫ₕ c).source := by
    have h := (HasGroupoid.compatible (G := contDiffGroupoid ∞ 𝓘(ℂ, ComplexModel m))
      (chart_mem_atlas _ p.2) (chart_mem_atlas _ y)).1
    simpa [contDiffPregroupoid] using h
  have hlin : ContDiff ℂ ∞ (fun z : ComplexModel (n + m) => (L.symm z).2) :=
    (ContinuousLinearMap.snd ℂ _ _).contDiff.comp L.symm.contDiff
  refine (hB.comp hlin.contDiffOn ?_).congr ?_
  · intro z hz
    simp only [extChartAt, OpenPartialHomeomorph.extend, mem_inter_iff, mem_preimage] at hz
    simp_all [b, c, L]
  · intro z hz
    simp [extChartAt, OpenPartialHomeomorph.extend, b, c, L]

/-- A pair of holomorphic maps is holomorphic into the product. -/
theorem contMDiff_prodMk {k : ℕ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z]
    [IsComplexManifold k Z] {f : Z → X} {g : Z → Y}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel m) ∞ g) :
    ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel (n + m)) ∞ (fun z => (f z, g z)) := by
  rw [contMDiff_iff_target] at hf hg ⊢
  refine ⟨hf.1.prodMk hg.1, fun p => ?_⟩
  have h1 := hf.2 p.1
  have h2 := hg.2 p.2
  have hsub1 : (fun z => (f z, g z)) ⁻¹' (extChartAt 𝓘(ℂ, ComplexModel (n + m)) p).source ⊆
      f ⁻¹' (extChartAt 𝓘(ℂ, ComplexModel n) p.1).source := by
    intro z hz
    simp only [extChartAt, OpenPartialHomeomorph.extend, mem_preimage] at hz ⊢
    simp_all
  have hsub2 : (fun z => (f z, g z)) ⁻¹' (extChartAt 𝓘(ℂ, ComplexModel (n + m)) p).source ⊆
      g ⁻¹' (extChartAt 𝓘(ℂ, ComplexModel m) p.2).source := by
    intro z hz
    simp only [extChartAt, OpenPartialHomeomorph.extend, mem_preimage] at hz ⊢
    simp_all
  have hpair := (h1.mono hsub1).prodMk_space (h2.mono hsub2)
  refine ((prodModelEquiv n m : (ComplexModel n × ComplexModel m) →L[ℂ] ComplexModel (n + m)).contMDiff.comp_contMDiffOn hpair).congr ?_
  intro z hz
  simp [extChartAt, OpenPartialHomeomorph.extend]

/-- The product of two holomorphic maps is holomorphic. -/
theorem contMDiff_prodMap {n' m' : ℕ} {X' : Type*} [TopologicalSpace X']
    [ChartedSpace (ComplexModel n') X'] [IsComplexManifold n' X'] {Y' : Type*} [TopologicalSpace Y']
    [ChartedSpace (ComplexModel m') Y'] [IsComplexManifold m' Y'] {f : X → X'} {g : Y → Y'}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n') ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m') ∞ g) :
    ContMDiff 𝓘(ℂ, ComplexModel (n + m)) 𝓘(ℂ, ComplexModel (n' + m')) ∞ (Prod.map f g) :=
  contMDiff_prodMk (hf.comp contMDiff_fst) (hg.comp contMDiff_snd)

/-- The diagonal map `x ↦ (x, x)` is holomorphic. -/
theorem contMDiff_diag :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (n + n)) ∞ (fun x : X => (x, x)) :=
  contMDiff_prodMk contMDiff_id contMDiff_id

/-! ### The product Kähler form `p₁^*ω₁ + p₂^*ω₂` -/

section Kahler

open HolomorphicMaps PositiveClasses

/-- On the product atlas, the coordinate representative of the first projection is a chart
transition of `X` after the linear projection `ℂⁿ⁺ᵐ → ℂⁿ`; so its differential kills `v` only if
the first component of `v` vanishes. -/
theorem eq_zero_of_fderiv_coordinateMap_fst {e : ComplexChart (n + m) (X × Y)}
    {z : ComplexModel (n + m)} (hz : z ∈ e.val.target) {v : ComplexModel (n + m)}
    (hv : fderiv ℝ (coordinateMap Prod.fst e (complexChartAt (n := n) (e.val.symm z).1)) z v = 0) :
    ((prodModelEquiv n m).symm v).1 = 0 := by
  obtain ⟨a, ha, b, hb, hab⟩ := e.property
  set d := complexChartAt (n := n) (e.val.symm z).1
  set a' : ComplexChart n X := ⟨a, ha⟩
  set L := prodModelEquiv n m
  set P : ComplexModel (n + m) →L[ℝ] ComplexModel n :=
    ((ContinuousLinearMap.fst ℂ (ComplexModel n) (ComplexModel m)).comp
      (L.symm : ComplexModel (n + m) →L[ℂ] ComplexModel n × ComplexModel m)).restrictScalars ℝ
  have hfun : coordinateMap Prod.fst e d = chartTransition a' d ∘ P := by
    funext w
    simp [coordinateMap, chartTransition, ← hab, a', P, L]
  have hz' : z ∈ (prodChart a b).target := hab ▸ hz
  rw [prodChart_target] at hz'
  have hsymm : (e.val.symm z).1 = a.symm (L.symm z).1 := by rw [← hab]; rfl
  have hu : P z ∈ (chartTransition a' d).source := by
    refine ⟨hz'.1, ?_⟩
    show a.symm (L.symm z).1 ∈ d.val.source
    rw [← hsymm]
    exact mem_complexChartAt_source _
  have hT := (chartTransition_contDiffAt_real a' d hu).differentiableAt (by simp)
  rw [hfun, fderiv_comp z hT P.differentiableAt, P.fderiv] at hv
  exact KahlerPerturbation.chartTransitionDerivative_injective a' d hu
    (hv.trans (map_zero _).symm)

/-- The second-projection analogue of `eq_zero_of_fderiv_coordinateMap_fst`. -/
theorem eq_zero_of_fderiv_coordinateMap_snd {e : ComplexChart (n + m) (X × Y)}
    {z : ComplexModel (n + m)} (hz : z ∈ e.val.target) {v : ComplexModel (n + m)}
    (hv : fderiv ℝ (coordinateMap Prod.snd e (complexChartAt (n := m) (e.val.symm z).2)) z v = 0) :
    ((prodModelEquiv n m).symm v).2 = 0 := by
  obtain ⟨a, ha, b, hb, hab⟩ := e.property
  set d := complexChartAt (n := m) (e.val.symm z).2
  set b' : ComplexChart m Y := ⟨b, hb⟩
  set L := prodModelEquiv n m
  set P : ComplexModel (n + m) →L[ℝ] ComplexModel m :=
    ((ContinuousLinearMap.snd ℂ (ComplexModel n) (ComplexModel m)).comp
      (L.symm : ComplexModel (n + m) →L[ℂ] ComplexModel n × ComplexModel m)).restrictScalars ℝ
  have hfun : coordinateMap Prod.snd e d = chartTransition b' d ∘ P := by
    funext w
    simp [coordinateMap, chartTransition, ← hab, b', P, L]
  have hz' : z ∈ (prodChart a b).target := hab ▸ hz
  rw [prodChart_target] at hz'
  have hsymm : (e.val.symm z).2 = b.symm (L.symm z).2 := by rw [← hab]; rfl
  have hu : P z ∈ (chartTransition b' d).source := by
    refine ⟨hz'.2, ?_⟩
    show b.symm (L.symm z).2 ∈ d.val.source
    rw [← hsymm]
    exact mem_complexChartAt_source _
  have hT := (chartTransition_contDiffAt_real b' d hu).differentiableAt (by simp)
  rw [hfun, fderiv_comp z hT P.differentiableAt, P.fderiv] at hv
  exact KahlerPerturbation.chartTransitionDerivative_injective b' d hu
    (hv.trans (map_zero _).symm)

/-- A pulled-back Hermitian form is strictly positive on every vector that the differential of the
coordinate representative does not kill (the strict half of
`SmoothRealForm.IsHermitian.pullback_of_injective`, pointwise). -/
theorem pullback_coeff_pos {k k' : ℕ} {V M : Type*} [TopologicalSpace V]
    [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V] [TopologicalSpace M]
    [ChartedSpace (ComplexModel k') M] [IsComplexManifold k' M] {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k') ∞ f)
    {a : SmoothRealForm k' M 2} (ha : a.IsHermitian) (e : ComplexChart k V)
    {z : ComplexModel k} (hz : z ∈ e.val.target) {v : ComplexModel k}
    (hv : fderiv ℝ (coordinateMap f e (complexChartAt (n := k') (f (e.val.symm z)))) z v ≠ 0) :
    0 < (SmoothRealForm.pullback hf a).coeff e z ![v, Complex.I • v] := by
  let d := complexChartAt (n := k') (f (e.val.symm z))
  have hzd : z ∈ coordinateDomain f e d := ⟨hz, mem_complexChartAt_source _⟩
  rw [SmoothRealForm.pullback_coeff hf a e d hzd]
  let L := fderiv ℝ (coordinateMap f e d) z
  have hvec : L ∘ ![v, Complex.I • v] = ![L v, Complex.I • L v] := by
    funext i
    fin_cases i
    · rfl
    · exact coordinateMap_fderiv_map_smul_complex hf e d hzd Complex.I v
  change 0 < a.coeff d (coordinateMap f e d z) (L ∘ ![v, Complex.I • v])
  rw [hvec]
  exact (ha d _ (coordinateMap_mem_target hzd)).2 (L v) hv

/-- `p₁^*a + p₂^*b` on `X × Y`. -/
def prodForm (a : ClosedRealOneOneForm n X) (b : ClosedRealOneOneForm m Y) :
    ClosedRealOneOneForm (n + m) (X × Y) :=
  ClosedRealOneOneForm.pullback contMDiff_fst a + ClosedRealOneOneForm.pullback contMDiff_snd b

/-- **The product of two Kähler forms is Kähler**: `p₁^*ω₁ + p₂^*ω₂` is closed of type `(1,1)`
and strictly positive, since a tangent vector killed by both projections is zero. -/
theorem prodForm_isKahler {a : ClosedRealOneOneForm n X} {b : ClosedRealOneOneForm m Y}
    (ha : a.val.IsKahler) (hb : b.val.IsKahler) : (prodForm a b).val.IsKahler := by
  refine ⟨fun e z hz => ⟨?_, ?_⟩, (prodForm a b).property.1⟩
  · intro u w
    have h1 := (ClosedRealOneOneForm.pullback contMDiff_fst a).property.2 e z hz u w
    have h2 := (ClosedRealOneOneForm.pullback contMDiff_snd b).property.2 e z hz u w
    simp only [prodForm, ClosedRealOneOneForm.coeff_add, ContinuousAlternatingMap.add_apply]
    rw [h1, h2]
  · intro v hv
    simp only [prodForm, ClosedRealOneOneForm.coeff_add, ContinuousAlternatingMap.add_apply,
      ClosedRealOneOneForm.pullback_val]
    have hs1 := (SmoothRealForm.IsSemipositive.pullback contMDiff_fst
      (KahlerBackground.isSemipositive ⟨a, ha⟩)) e z hz v
    have hs2 := (SmoothRealForm.IsSemipositive.pullback contMDiff_snd
      (KahlerBackground.isSemipositive ⟨b, hb⟩)) e z hz v
    by_cases h1 : fderiv ℝ (coordinateMap Prod.fst e
        (complexChartAt (n := n) (e.val.symm z).1)) z v = 0
    · have h2 : fderiv ℝ (coordinateMap Prod.snd e
          (complexChartAt (n := m) (e.val.symm z).2)) z v ≠ 0 := by
        intro h2
        apply hv
        have hL : (prodModelEquiv n m).symm v = 0 :=
          Prod.ext (eq_zero_of_fderiv_coordinateMap_fst hz h1)
            (eq_zero_of_fderiv_coordinateMap_snd hz h2)
        simpa using hL
      exact add_pos_of_nonneg_of_pos hs1 (pullback_coeff_pos contMDiff_snd hb.1 e hz h2)
    · exact add_pos_of_pos_of_nonneg (pullback_coeff_pos contMDiff_fst ha.1 e hz h1) hs2

/-- The product Kähler background `p₁^*ω₁ + p₂^*ω₂`. -/
def prodKahlerBackground (ω₁ : KahlerBackground n X) (ω₂ : KahlerBackground m Y) :
    KahlerBackground (n + m) (X × Y) :=
  ⟨prodForm ω₁.form ω₂.form, prodForm_isKahler ω₁.isKahler ω₂.isKahler⟩

@[simp] theorem prodKahlerBackground_form (ω₁ : KahlerBackground n X) (ω₂ : KahlerBackground m Y) :
    (prodKahlerBackground ω₁ ω₂).form = prodForm ω₁.form ω₂.form := rfl

end Kahler

/-! ### The diagonal is a closed connected submanifold -/

section Diagonal

/-- Product coordinates `L(x, z)` lie in the coordinate plane `ℂⁿ × 0` exactly when `z = 0`. -/
theorem prodModelEquiv_mem_complexCoordinatePlane_iff (x : ComplexModel n) (z : ComplexModel m) :
    prodModelEquiv n m (x, z) ∈ complexCoordinatePlane (n + m) n ↔ z = 0 := by
  constructor
  · intro h
    ext j
    have := h (Fin.natAdd n j) (by simp)
    simpa [prodModelEquiv] using this
  · rintro rfl i hi
    obtain ⟨j, rfl⟩ : ∃ j : Fin m, i = Fin.natAdd n j :=
      ⟨⟨i - n, by omega⟩, by ext; simp; omega⟩
    simp [prodModelEquiv]

/-- The affine change of coordinates `L(u, u') ↦ L(u - u₀, u' - u)` flattening the diagonal. -/
def diagFlatten (u₀ : ComplexModel n) (w : ComplexModel (n + n)) : ComplexModel (n + n) :=
  prodModelEquiv n n (((prodModelEquiv n n).symm w).1 - u₀,
    ((prodModelEquiv n n).symm w).2 - ((prodModelEquiv n n).symm w).1)

/-- The inverse of `diagFlatten`: `L(s, t) ↦ L(s + u₀, t + s + u₀)`. -/
def diagUnflatten (u₀ : ComplexModel n) (w : ComplexModel (n + n)) : ComplexModel (n + n) :=
  prodModelEquiv n n (((prodModelEquiv n n).symm w).1 + u₀,
    ((prodModelEquiv n n).symm w).2 + ((prodModelEquiv n n).symm w).1 + u₀)

theorem diagUnflatten_diagFlatten (u₀ : ComplexModel n) (w : ComplexModel (n + n)) :
    diagUnflatten u₀ (diagFlatten u₀ w) = w := by
  simp only [diagUnflatten, diagFlatten, ContinuousLinearEquiv.symm_apply_apply]
  rw [← (prodModelEquiv n n).apply_symm_apply w]
  congr 1
  ext <;> simp

theorem diagFlatten_diagUnflatten (u₀ : ComplexModel n) (w : ComplexModel (n + n)) :
    diagFlatten u₀ (diagUnflatten u₀ w) = w := by
  simp only [diagUnflatten, diagFlatten, ContinuousLinearEquiv.symm_apply_apply]
  rw [← (prodModelEquiv n n).apply_symm_apply w]
  congr 1
  ext <;> simp

theorem differentiable_diagFlatten (u₀ : ComplexModel n) :
    Differentiable ℂ (diagFlatten u₀) := by
  unfold diagFlatten
  fun_prop

theorem differentiable_diagUnflatten (u₀ : ComplexModel n) :
    Differentiable ℂ (diagUnflatten u₀) := by
  unfold diagUnflatten
  fun_prop

/-- In the product chart at `(p, p)`, the diagonal is the coordinate plane `ℂⁿ × 0` after the affine
change `diagFlatten`. -/
theorem regularAtDim_diagonal (p : X) :
    RegularAtDim (n := n + n) (Set.diagonal X) (p, p) n := by
  set c := complexChartAt (n := n + n) ((p, p) : X × X)
  set a := chartAt (ComplexModel n) p
  have hc : c.val = prodChart a a := rfl
  set u₀ := a p
  refine ⟨Nat.le_add_right n n, Set.mem_diagonal p, ?_⟩
  refine ⟨{ source := c.val.target
            target := diagUnflatten u₀ ⁻¹' c.val.target
            isOpen_source := c.val.open_target
            isOpen_target := c.val.open_target.preimage (differentiable_diagUnflatten u₀).continuous
            center_mem_source := c.val.map_source (mem_complexChartAt_source _)
            toFun := diagFlatten u₀
            invFun := diagUnflatten u₀
            toFun_holomorphic := (differentiable_diagFlatten u₀).differentiableOn
            invFun_holomorphic := (differentiable_diagUnflatten u₀).differentiableOn
            mapsTo_toFun := fun w hw => by
              show diagUnflatten u₀ (diagFlatten u₀ w) ∈ c.val.target
              rwa [diagUnflatten_diagFlatten]
            mapsTo_invFun := fun w hw => hw
            left_inv := fun w _ => diagUnflatten_diagFlatten u₀ w
            right_inv := fun w _ => diagFlatten_diagUnflatten u₀ w }, subset_rfl, ?_, ?_⟩
  · show diagFlatten u₀ (c.val (p, p)) = 0
    rw [hc]
    simp [diagFlatten, u₀]
  · intro y hy _
    rw [hc] at hy
    rw [prodChart_source] at hy
    show y ∈ Set.diagonal X ↔ diagFlatten u₀ (c.val y) ∈ complexCoordinatePlane (n + n) n
    rw [hc]
    simp only [diagFlatten, prodChart_apply, ContinuousLinearEquiv.symm_apply_apply]
    rw [prodModelEquiv_mem_complexCoordinatePlane_iff, sub_eq_zero, Set.mem_diagonal_iff]
    exact ⟨fun h => by rw [h], fun h => (a.injOn hy.1 hy.2 h.symm)⟩

/-- **The diagonal of a connected complex manifold is a closed connected submanifold of `X × X`
of dimension `n`.** -/
theorem isClosedConnectedSubmanifold_diagonal [ConnectedSpace X] [Nonempty X] :
    BlowupSequences.IsClosedConnectedSubmanifold (n + n) (Set.diagonal X) n := by
  refine ⟨isClosed_diagonal, ?_, ?_⟩
  · rw [← Set.range_diag]
    exact isConnected_range (continuous_id.prodMk continuous_id)
  · rintro ⟨p, q⟩ (h : p = q)
    subst h
    exact regularAtDim_diagonal p

end Diagonal

end

end Hironaka.ProductComplexManifold
