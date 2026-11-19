import Hironaka.Analytic.Unibranch.ComplexSpaceFormLiftCompatibility

/-! The ACTUAL pullback of the ORIGINAL SpaceForm along an ORIGINAL
morphism between arbitrary reduced complex spaces. Both source and target
may be singular. Every cover, ambient lift, smooth tensor and original
VanishesOn compatibility field is manufactured. No PSH/resolution theorem
or desired form certificate is input. Blueprint: complex-space-form-pullback.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology ContDiff
open Hironaka
open Hironaka.HironakaReducedComplexAnalyticSpaces
namespace Hironaka.Analytic.Unibranch.SpaceForm
variable {X Y : SourceReducedComplexSpace} {k : ℕ}
  (θ : SpaceForm X k) (f : Y ⟶ X)

/-- Primitive genuine ambient coordinates of the SAME original morphism
on an actual source analytic chart, without pullback conclusions. -/
structure PullbackChart where
  source : LocalEmbedding Y
  chart : θ.ι
  lift : ComplexModel source.dim → ComplexModel (θ.chart chart).dim
  holomorphic : ContDiffOn ℂ ∞ lift source.ambient
  maps : MapsTo lift source.ambient (θ.chart chart).ambient
  factor : ∀ c : source.carrier, ∃ a : (θ.chart chart).carrier,
    a.val.val = lift c.val.val ∧ (θ.chart chart).toPoint a = f.hom.left.base (source.toPoint c)

/-- The actual source LRS morphism and existing analytic chart restriction
produce a genuine covering family of primitive lift charts. -/
theorem pullbackChart_cover (y : Y.obj.left) :
    ∃ A : PullbackChart θ f, y ∈ range A.source.toPoint := by
  let e := LocalEmbedding.ofPoint Y y
  obtain ⟨c,hcy⟩ := LocalEmbedding.mem_range_ofPoint Y y
  obtain ⟨i,hi⟩ := θ.covers (f.hom.left.base y)
  have hover : (e.map ≫ f.hom.left) ≫ X.obj.hom = (modelOver e.ambient e.carrier).hom := by
    rw [Category.assoc,Over.w f.hom,e.overPoint]
  have hcx : (e.map ≫ f.hom.left).base c ∈ range (θ.chart i).toPoint := by
    change f.hom.left.base (e.toPoint c) ∈ _
    rw [hcy]
    exact hi
  obtain ⟨W,hW,hcW,hWU,G,hG,hmaps,hfac⟩ :=
    LocalEmbedding.exists_contDiffOn_factor (e.map ≫ f.hom.left) hover (θ.chart i) c hcx
  let T : Opens (ComplexModel e.dim) := ⟨W,hW⟩
  let A : PullbackChart θ f := {
    source := e.restrict T hWU
    chart := i
    lift := G
    holomorphic := hG
    maps := hmaps
    factor := by
      intro z
      let z' : e.carrier := ⟨⟨z.val.val,hWU z.val.property⟩,z.property⟩
      obtain ⟨a,ha,hpa⟩ := hfac z' z.val.property
      refine ⟨a,ha,?_⟩
      exact hpa }
  refine ⟨A,?_,?_⟩
  · exact ⟨⟨c.val.val,hcW⟩,c.property⟩
  · change (e.restrict T hWU).toPoint _ = y
    rw [LocalEmbedding.restrict_toPoint]
    exact hcy

/-- Actual original form pullback, as an object of the EXISTING SpaceForm
on the ORIGINAL possibly singular source. -/
def pullback : SpaceForm Y k where
  ι := PullbackChart θ f
  chart A := A.source
  covers := pullbackChart_cover θ f
  rep A := pullbackForm A.lift (θ.rep A.chart)
  smooth A := by
    apply SmoothRealForm.contDiffOn_compContinuousLinearMap
    · exact (θ.smooth A.chart).comp (A.holomorphic.restrict_scalars ℝ) A.maps
    · exact (A.holomorphic.restrict_scalars ℝ).fderiv_of_isOpen A.source.ambient.isOpen (by simp)
  compatible A B W H hH := by
    intro m D h hD hd hm z hz
    rw [pullbackForm_sub,Pi.sub_apply,sub_eq_zero]
    have hmapA : MapsTo h D A.source.ambient := fun w hw => hH.2.1 (hm w hw).1
    have hmapB : MapsTo (H ∘ h) D B.source.ambient := fun w hw => hH.2.2.2.1 (hm w hw).1
    have hHh : DifferentiableOn ℂ (H ∘ h) D :=
      hH.2.2.1.comp hd (fun w hw => (hm w hw).1)
    have hG1 : DifferentiableOn ℂ (A.lift ∘ h) D :=
      (A.holomorphic.differentiableOn (by simp)).comp hd hmapA
    have hG2 : DifferentiableOn ℂ (B.lift ∘ H ∘ h) D :=
      (B.holomorphic.differentiableOn (by simp)).comp hHh hmapB
    have hpoints : ∀ w ∈ D, ∃ (a : (θ.chart A.chart).carrier) (b : (θ.chart B.chart).carrier),
        a.val.val = (A.lift ∘ h) w ∧ b.val.val = (B.lift ∘ H ∘ h) w ∧
        (θ.chart A.chart).toPoint a = (θ.chart B.chart).toPoint b := by
      intro w hw
      obtain ⟨aY,haY⟩ := (hm w hw).2
      obtain ⟨bY,hbY,hbYaY⟩ := hH.2.2.2.2 aY (by rw [haY]; exact (hm w hw).1)
      obtain ⟨aX,haX,hpaX⟩ := A.factor aY
      obtain ⟨bX,hbX,hpbX⟩ := B.factor bY
      refine ⟨aX,bX,?_,?_,?_⟩
      · simpa only [haY,Function.comp_apply] using haX
      · simpa only [hbY,haY,Function.comp_apply] using hbX
      · exact hpaX.trans ((congrArg (fun q => f.hom.left.base q) hbYaY).symm.trans hpbX.symm)
    have hcore := pullback_eq_of_compatible_points θ A.chart B.chart hD hG1 hG2 hpoints hz
    have hr : DifferentiableAt ℝ h z := (hd.differentiableAt (hD.mem_nhds hz)).restrictScalars ℝ
    have hHr : DifferentiableAt ℝ H (h z) :=
      (hH.2.2.1.differentiableAt (hH.1.mem_nhds (hm z hz).1)).restrictScalars ℝ
    have hAr : DifferentiableAt ℝ A.lift (h z) :=
      ((A.holomorphic.differentiableOn (by simp)).differentiableAt
        (A.source.ambient.isOpen.mem_nhds (hmapA hz))).restrictScalars ℝ
    have hBr : DifferentiableAt ℝ B.lift (H (h z)) :=
      ((B.holomorphic.differentiableOn (by simp)).differentiableAt
        (B.source.ambient.isOpen.mem_nhds (hmapB hz))).restrictScalars ℝ
    have hleft := pullbackForm_comp hr hAr (θ.rep A.chart)
    have hright := (pullbackForm_comp hr hHr (pullbackForm B.lift (θ.rep B.chart))).trans
      (pullbackForm_comp (hHr.comp z hr) hBr (θ.rep B.chart))
    exact hleft.trans (hcore.trans hright.symm)

/-- Literal original restriction readback on EVERY actual constructed
source chart, with the actual ambient tensor. -/
theorem pullback_restrictsTo (A : PullbackChart θ f) :
    (pullback θ f).RestrictsTo A.source (pullbackForm A.lift (θ.rep A.chart)) := by
  intro B W G hG
  exact (pullback θ f).compatible A B W G hG

end Hironaka.Analytic.Unibranch.SpaceForm
