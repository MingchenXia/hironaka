import Hironaka.Analytic.Unibranch.ComplexSpaceFormPullbackPotentials
import Hironaka.Analytic.ExteriorDerivative

/-! Actual closed and real(1,1) preservation of the SAME original form
pullback between arbitrary singular complex spaces.
Blueprint: complex-space-form-pullback-closed.tex. -/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology ContDiff
open Hironaka
namespace Hironaka.Analytic.Unibranch.SpaceForm

/-- Genuine original closedness survives the actual singular-space
morphism pullback, with all ambient source data manufactured. -/
theorem IsClosed.pullback {X Y : SourceReducedComplexSpace} {k : ℕ}
    {θ : SpaceForm X k} (hθ : θ.IsClosed) (f : Y ⟶ X) : (pullback θ f).IsClosed := by
  intro y
  obtain ⟨e,he,v,hv,hclosed,hres⟩ := hθ (f.hom.left.base y)
  obtain ⟨A,hA⟩ := morphismChartLift_cover f e y he
  refine ⟨A.source,hA,pullbackForm A.lift v,?_,?_,
    pullback_restrictsTo_of_lift θ f hres A.source A.holomorphic A.maps A.factor⟩
  · apply SmoothRealForm.contDiffOn_compContinuousLinearMap
    · exact hv.comp (A.holomorphic.restrict_scalars ℝ) A.maps
    · exact (A.holomorphic.restrict_scalars ℝ).fderiv_of_isOpen A.source.ambient.isOpen (by simp)
  · intro z hz
    have hdiff := (hv.contDiffAt (e.ambient.isOpen.mem_nhds (A.maps hz))).differentiableAt (by simp)
    have hnat := extDeriv_pullback hdiff
      ((A.holomorphic.restrict_scalars ℝ).contDiffAt (A.source.ambient.isOpen.mem_nhds hz))
      (by simpa using ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    change extDeriv (fun w => (v (A.lift w)).compContinuousLinearMap (fderiv ℝ A.lift w)) z = 0
    rw [hnat,hclosed _ (A.maps hz)]
    ext w
    rfl

/-- Holomorphic ambient derivatives preserve the genuine original real
(1,1) type, retaining both actual possibly singular complex spaces. -/
theorem IsOneOne.pullback {X Y : SourceReducedComplexSpace}
    {θ : SpaceForm X 2} (hθ : θ.IsOneOne) (f : Y ⟶ X) : (pullback θ f).IsOneOne := by
  intro y
  obtain ⟨e,he,v,hv,htype,hres⟩ := hθ (f.hom.left.base y)
  obtain ⟨A,hA⟩ := morphismChartLift_cover f e y he
  refine ⟨A.source,hA,pullbackForm A.lift v,?_,?_,
    pullback_restrictsTo_of_lift θ f hres A.source A.holomorphic A.maps A.factor⟩
  · apply SmoothRealForm.contDiffOn_compContinuousLinearMap
    · exact hv.comp (A.holomorphic.restrict_scalars ℝ) A.maps
    · exact (A.holomorphic.restrict_scalars ℝ).fderiv_of_isOpen A.source.ambient.isOpen (by simp)
  · intro z hz a b
    have hd := (A.holomorphic.differentiableOn (by simp)).differentiableAt
      (A.source.ambient.isOpen.mem_nhds hz)
    have hlin (w : ComplexModel A.source.dim) :
        fderiv ℝ A.lift z (Complex.I • w) = Complex.I • fderiv ℝ A.lift z w := by
      rw [hd.fderiv_restrictScalars ℝ]
      exact (fderiv ℂ A.lift z).map_smul Complex.I w
    change v (A.lift z) ((fderiv ℝ A.lift z) ∘ ![Complex.I • a,Complex.I • b]) =
      v (A.lift z) ((fderiv ℝ A.lift z) ∘ ![a,b])
    have hvec : ((fderiv ℝ A.lift z) ∘ ![Complex.I • a,Complex.I • b]) =
        ![Complex.I • fderiv ℝ A.lift z a,Complex.I • fderiv ℝ A.lift z b] := by
      funext i
      fin_cases i <;> simp [hlin]
    have hvec' : ((fderiv ℝ A.lift z) ∘ ![a,b]) =
        ![fderiv ℝ A.lift z a,fderiv ℝ A.lift z b] := by
      funext i
      fin_cases i <;> rfl
    rw [hvec,hvec']
    exact htype (A.lift z) (A.maps hz) (fderiv ℝ A.lift z a) (fderiv ℝ A.lift z b)

end Hironaka.Analytic.Unibranch.SpaceForm
