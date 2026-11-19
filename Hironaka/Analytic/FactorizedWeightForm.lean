import Hironaka.Analytic.LocalPotentialForm
import Hironaka.Analytic.LogWeightFactorization
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The form `ddᶜ log U` extended across the zeros of a factorized weight

Let `U ≥ 0` be a function on a complex manifold which vanishes on no nonempty open set and is
locally of the form `|hₓ|² Uₓ'` with `hₓ` holomorphic and `Uₓ'` smooth and positive.  The local
potentials `log Uₓ'` have pluriharmonic differences
(`LogWeightFactorization.smoothDDC_log_eq_of_normSq_mul_eq`), so they glue to a closed real
`(1,1)`-form (`WeightFactorization.closedForm`), equal to `ddᶜ log U` off the zeros of `U`.
For `U = ∑ |sᵢ|²` built from generators of an ideal this is the curvature form of the
associated line bundle metric.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.FactorizedWeightForm

open LocalPotentialForm

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem differentiableAt_comp_chart_symm {g : M → ℂ} (e : ComplexChart n M) {u : ComplexModel n}
    (hu : u ∈ e.val.target) (hg : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g (e.val.symm u)) :
    DifferentiableAt ℂ (fun u' => g (e.val.symm u')) u :=
  mdifferentiableAt_iff_differentiableAt.mp
    (hg.comp u (mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel n)) e.property hu))

variable (n) in
/-- Local factorizations `U = |hₓ|² Uₓ'` of a weight. -/
structure WeightFactorization (U : M → ℝ) where
  domain : M → Set M
  isOpen_domain : ∀ x, IsOpen (domain x)
  mem_domain : ∀ x, x ∈ domain x
  gen : M → M → ℂ
  smoothPart : M → M → ℝ
  gen_mdifferentiable : ∀ x, ∀ y ∈ domain x,
    MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (gen x) y
  smooth : ∀ (x : M) (e : ComplexChart n M),
    ContDiffOn ℝ ∞ (fun u => smoothPart x (e.val.symm u)) (e.val.target ∩ e.val.symm ⁻¹' domain x)
  pos : ∀ x, ∀ y ∈ domain x, 0 < smoothPart x y
  factor : ∀ x, ∀ y ∈ domain x, U y = Complex.normSq (gen x y) * smoothPart x y
  nowhereZero : ∀ W : Set M, IsOpen W → W.Nonempty → ∃ y ∈ W, U y ≠ 0

namespace WeightFactorization

variable {U : M → ℝ} (F : WeightFactorization n U)

theorem gen_ne_zero_of {x y : M} (hy : y ∈ F.domain x) (hU : U y ≠ 0) : F.gen x y ≠ 0 := by
  intro h0; apply hU; rw [F.factor x y hy, h0]; simp

theorem smoothDDC_log_eq (x y : M) (e : ComplexChart n M) {u : ComplexModel n}
    (hu : u ∈ e.val.target) (hx : e.val.symm u ∈ F.domain x) (hy : e.val.symm u ∈ F.domain y) :
    smoothDDC (fun u' => Real.log (F.smoothPart x (e.val.symm u'))) u =
      smoothDDC (fun u' => Real.log (F.smoothPart y (e.val.symm u'))) u := by
  set S := e.val.target ∩ e.val.symm ⁻¹' (F.domain x ∩ F.domain y) with hS_def
  have hS : IsOpen S := e.val.isOpen_inter_preimage_symm ((F.isOpen_domain x).inter (F.isOpen_domain y))
  have hSx : S ⊆ e.val.target ∩ e.val.symm ⁻¹' F.domain x := fun v hv => ⟨hv.1, hv.2.1⟩
  have hSy : S ⊆ e.val.target ∩ e.val.symm ⁻¹' F.domain y := fun v hv => ⟨hv.1, hv.2.2⟩
  have hhol : ∀ z, DifferentiableOn ℂ (fun u' => F.gen z (e.val.symm u'))
      (e.val.target ∩ e.val.symm ⁻¹' F.domain z) := fun z v hv =>
    (differentiableAt_comp_chart_symm e hv.1 (F.gen_mdifferentiable z _ hv.2)).differentiableWithinAt
  refine LogWeightFactorization.smoothDDC_log_eq_of_normSq_mul_eq hS ((F.smooth x e).mono hSx)
    ((F.smooth y e).mono hSy) (fun v hv => F.pos x _ hv.2.1) (fun v hv => F.pos y _ hv.2.2)
    ((hhol x).mono hSx) ((hhol y).mono hSy)
    (fun v hv => by rw [← F.factor x _ hv.2.1, ← F.factor y _ hv.2.2]) ?_ ⟨hu, hx, hy⟩
  intro v hv
  rw [mem_closure_iff]
  intro o ho hvo
  have hopen : IsOpen (e.val.symm '' (o ∩ S)) :=
    e.val.symm.isOpen_image_of_subset_source (ho.inter hS) fun w hw => hw.2.1
  obtain ⟨_, ⟨w, hw, rfl⟩, hU⟩ := F.nowhereZero _ hopen ⟨_, ⟨v, ⟨hvo, hv⟩, rfl⟩⟩
  exact ⟨w, hw.1, hw.2, F.gen_ne_zero_of hw.2.2.1 hU⟩

/-- The local `ddᶜ`-data `log Uₓ'`. -/
def toLocalDDCData : LocalDDCData n M where
  domain := F.domain
  isOpen_domain := F.isOpen_domain
  mem_domain := F.mem_domain
  potential x y := Real.log (F.smoothPart x y)
  smooth x e := (F.smooth x e).log fun u hu => (F.pos x _ hu.2).ne'
  pluriharmonic x y e u hu hx hy := by
    set S := e.val.target ∩ e.val.symm ⁻¹' (F.domain x ∩ F.domain y)
    have hS : IsOpen S :=
      e.val.isOpen_inter_preimage_symm ((F.isOpen_domain x).inter (F.isOpen_domain y))
    rw [PositiveClasses.smoothDDC_sub hS
      (((F.smooth x e).log fun u hu => (F.pos x _ hu.2).ne').mono fun v hv => ⟨hv.1, hv.2.1⟩)
      (((F.smooth y e).log fun u hu => (F.pos y _ hu.2).ne').mono fun v hv => ⟨hv.1, hv.2.2⟩)
      ⟨hu, hx, hy⟩, F.smoothDDC_log_eq x y e hu hx hy, sub_self]

/-- **The glued form**, `ddᶜ log U` extended across the zeros of `U`. -/
def closedForm : ClosedRealOneOneForm n M := F.toLocalDDCData.closedForm

theorem closedForm_coeff_eventuallyEq (x : M) (e : ComplexChart n M) {u : ComplexModel n}
    (hu : u ∈ e.val.target) (hx : e.val.symm u ∈ F.domain x) :
    F.closedForm.val.coeff e =ᶠ[𝓝 u]
      smoothDDC (fun u' => Real.log (F.smoothPart x (e.val.symm u'))) :=
  F.toLocalDDCData.form_coeff_eventuallyEq x e hu hx

end WeightFactorization

end

end Hironaka.FactorizedWeightForm
