import Hironaka.Resolution.HironakaSmoothSubmersionMonomialChartPullback

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionMonomialOpenCharts
open BlowupMonomialCharts BlowupTowers HironakaSmoothSubmersionMonomialChartPullback
noncomputable section

private theorem opens_chart_apply {d : ℕ} (V : TopologicalSpace.Opens (ComplexModel d))
    (x z : V) : chartAt (ComplexModel d) x z = z.val := by
  simp only [TopologicalSpace.Opens.chartAt_eq,chartAt_self_eq,
    OpenPartialHomeomorph.subtypeRestr_coe,OpenPartialHomeomorph.refl_apply]
  rfl

private theorem opens_chart_source {d : ℕ} (V : TopologicalSpace.Opens (ComplexModel d))
    (x : V) : (chartAt (ComplexModel d) x).source = univ := by
  simp only [TopologicalSpace.Opens.chartAt_eq,chartAt_self_eq,
    OpenPartialHomeomorph.subtypeRestr_source,OpenPartialHomeomorph.refl_source,preimage_univ]

/-- Genuine pointwise maximal charts produce the SAME-fibre submersion on the literal source chart open. -/
theorem isSubmersionOfComplement_liftedOpenProjection (r n k : ℕ) (j : Fin n)
    (R : TopologicalSpace.Opens (ComplexModel r)) (S : TopologicalSpace.Opens (ComplexModel n)) :
    Manifold.IsSubmersionOfComplement (ComplexModel r)
      𝓘(ℂ, ComplexModel (r+n)) 𝓘(ℂ, ComplexModel n) ∞ (liftedOpenProjection r n k j R S) := by
  intro x
  let g := liftedOpenProjection r n k j R S
  let a := chartAt (ComplexModel (r+n)) x
  let b := chartAt (ComplexModel n) (g x)
  apply Manifold.IsSubmersionAtOfComplement.mk_of_charts
    ((splitCoordinates r n).trans (ContinuousLinearEquiv.prodComm ℂ (ComplexModel r) (ComplexModel n)))
    a b (mem_chart_source _ x) (mem_chart_source _ (g x))
    (IsManifold.chart_mem_maximalAtlas _) (IsManifold.chart_mem_maximalAtlas _)
  · intro z hz
    change g z ∈ b.source
    rw [opens_chart_source]
    exact mem_univ _
  · intro z hz
    have hz' : z ∈ a.target := by simpa using hz
    have hsymm : (a.symm z).val = z := by
      have he := a.right_inv hz'
      change chartAt (ComplexModel (r+n)) x (a.symm z) = z at he
      rw [opens_chart_apply] at he
      exact he
    change b (g (a.symm z)) = blockProjection r n z
    rw [opens_chart_apply]
    change blockProjection r n (a.symm z).val = blockProjection r n z
    rw [hsymm]

theorem isSubmersion_liftedOpenProjection (r n k : ℕ) (j : Fin n)
    (R : TopologicalSpace.Opens (ComplexModel r)) (S : TopologicalSpace.Opens (ComplexModel n)) :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (r+n)) 𝓘(ℂ, ComplexModel n) ∞
      (liftedOpenProjection r n k j R S) :=
  (isSubmersionOfComplement_liftedOpenProjection r n k j R S).isSubmersion

/-- The SAME genuine literal chart maps simultaneously give true smoothness, square and ALL-cone universality. -/
theorem actual_smooth_cartesian_chart_square (r n k : ℕ) (j : Fin n)
    (R : TopologicalSpace.Opens (ComplexModel r)) (S : TopologicalSpace.Opens (ComplexModel n)) :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (r+n)) 𝓘(ℂ, ComplexModel n) ∞
      (liftedOpenProjection r n k j R S) ∧
    baseOpenProjection r n R S ∘ sourceOpenProjection r n k j R S =
      targetOpenProjection k j S ∘ liftedOpenProjection r n k j R S ∧
    ∀ (ℓ : ℕ) (P : CMfd.{u} ℓ)
      (a : P → baseProductOpen r n R S) (b : P → targetChartOpen k j S),
      ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel (r+n)) ∞ a →
      ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel n) ∞ b →
      baseOpenProjection r n R S ∘ a = targetOpenProjection k j S ∘ b →
      ∃! w : P → sourceChartOpen r n k j R S,
        ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel (r+n)) ∞ w ∧
        sourceOpenProjection r n k j R S ∘ w = a ∧
        liftedOpenProjection r n k j R S ∘ w = b := by
  refine ⟨isSubmersion_liftedOpenProjection r n k j R S,?_,?_⟩
  · funext w
    exact Subtype.ext (blockProjection_monomial r n k j w.val)
  · intro ℓ P a b ha hb hc
    exact existsUnique_open_monomial_lift r n k j R S a b ha hb hc

end
end Hironaka.HironakaSmoothSubmersionMonomialOpenCharts
