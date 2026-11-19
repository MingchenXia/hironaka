import Hironaka.Analytic.Unibranch.ComplexSpaceFormPullback

/-! Genuine arbitrary-chart restriction and ddc-potential readback for the
SAME actual singular-space form pullback. Blueprint:
complex-space-form-pullback-potentials.tex. No output PSH/descent certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology ContDiff
open Hironaka
open Hironaka.HironakaReducedComplexAnalyticSpaces
namespace Hironaka.Analytic.Unibranch
namespace SpaceForm

private theorem pullback_germ_eq {m N k : ℕ}
    {F G : ComplexModel m → ComplexModel N} {z : ComplexModel m}
    (h : F =ᶠ[𝓝 z] G) (v : AmbientForm N k) :
    pullbackForm F v z = pullbackForm G v z := by
  simp only [pullbackForm,h.self_of_nhds,h.fderiv_eq]

/-- The ORIGINAL restriction predicate, together with actual holomorphic
point coherence, manufactures the target-probe tensor identity. -/
theorem pullback_eq_of_restrictsTo {X : SourceReducedComplexSpace} {k m : ℕ}
    (θ : SpaceForm X k) {e : LocalEmbedding X} {v : AmbientForm e.dim k}
    (hv : θ.RestrictsTo e v) (j : θ.ι) {D : Set (ComplexModel m)} (hD : IsOpen D)
    {G : ComplexModel m → ComplexModel e.dim}
    {H : ComplexModel m → ComplexModel (θ.chart j).dim}
    (hG : DifferentiableOn ℂ G D) (_hH : DifferentiableOn ℂ H D)
    (hpoints : ∀ z ∈ D, ∃ (a : e.carrier) (b : (θ.chart j).carrier),
      a.val.val = G z ∧ b.val.val = H z ∧ e.toPoint a = (θ.chart j).toPoint b)
    {z : ComplexModel m} (hz : z ∈ D) :
    pullbackForm G v z = pullbackForm H (θ.rep j) z := by
  obtain ⟨a,b,ha,hb,hab⟩ := hpoints z hz
  obtain ⟨W,T,haW,hT⟩ := e.exists_isTransition (θ.chart j) a ⟨b,hab.symm⟩
  let E : Set (ComplexModel m) := D ∩ G ⁻¹' W
  have hE : IsOpen E := hG.continuousOn.isOpen_inter_preimage hD hT.1
  have hzE : z ∈ E := ⟨hz,by change G z ∈ W; rw [← ha]; exact haW⟩
  have hmaps : ∀ w ∈ E, G w ∈ W ∧ ∃ a : e.carrier, a.val.val = G w := by
    intro w hw
    obtain ⟨a',-,ha',-⟩ := hpoints w hw.1
    exact ⟨hw.2,a',ha'⟩
  have hvan := hv j W T hT m E G hE (hG.mono inter_subset_left) hmaps z hzE
  rw [pullbackForm_sub,Pi.sub_apply,sub_eq_zero] at hvan
  have heq : (T ∘ G) =ᶠ[𝓝 z] H := by
    filter_upwards [hE.mem_nhds hzE] with w hw
    obtain ⟨a',b',ha',hb',hab'⟩ := hpoints w hw.1
    obtain ⟨c,hc,hpc⟩ := hT.2.2.2.2 a' (by rw [ha']; exact hw.2)
    have hcb : c = b' := (θ.chart j).toPoint_injective (hpc.trans hab')
    change T (G w) = H w
    rw [← ha',← hc,hcb,hb']
  have hGr : DifferentiableAt ℝ G z := (hG.differentiableAt (hD.mem_nhds hz)).restrictScalars ℝ
  have hTr : DifferentiableAt ℝ T (G z) :=
    (hT.2.2.1.differentiableAt (hT.1.mem_nhds hzE.2)).restrictScalars ℝ
  exact hvan.trans ((pullbackForm_comp hGr hTr (θ.rep j)).trans (pullback_germ_eq heq _))

/-- Literal restriction readback along ANY actual lift into ANY original
target embedding representing theta, not just the selected form cover. -/
theorem pullback_restrictsTo_of_lift {X Y : SourceReducedComplexSpace} {k : ℕ}
    (θ : SpaceForm X k) (f : Y ⟶ X) {e : LocalEmbedding X}
    {v : AmbientForm e.dim k} (hv : θ.RestrictsTo e v) (a : LocalEmbedding Y)
    {G : ComplexModel a.dim → ComplexModel e.dim}
    (hG : ContDiffOn ℂ ∞ G a.ambient) (_hGmaps : MapsTo G a.ambient e.ambient)
    (hfac : ∀ c : a.carrier, ∃ b : e.carrier,
      b.val.val = G c.val.val ∧ e.toPoint b = f.hom.left.base (a.toPoint c)) :
    (pullback θ f).RestrictsTo a (pullbackForm G v) := by
  intro B W H hH
  dsimp only [pullback] at H hH
  change a.IsTransition B.source W H at hH
  change a.VanishesOn W (pullbackForm G v - pullbackForm H (pullbackForm B.lift (θ.rep B.chart)))
  intro m D h hD hd hm z hz
  rw [pullbackForm_sub,Pi.sub_apply,sub_eq_zero]
  have hmapA : MapsTo h D a.ambient := fun w hw => hH.2.1 (hm w hw).1
  have hmapB : MapsTo (H ∘ h) D B.source.ambient := fun w hw => hH.2.2.2.1 (hm w hw).1
  have hHh : DifferentiableOn ℂ (H ∘ h) D := hH.2.2.1.comp hd (fun w hw => (hm w hw).1)
  have hG1 : DifferentiableOn ℂ (G ∘ h) D := (hG.differentiableOn (by simp)).comp hd hmapA
  have hG2 : DifferentiableOn ℂ (B.lift ∘ H ∘ h) D :=
    (B.holomorphic.differentiableOn (by simp)).comp hHh hmapB
  have hpoints : ∀ w ∈ D, ∃ (aX : e.carrier) (bX : (θ.chart B.chart).carrier),
      aX.val.val = (G ∘ h) w ∧ bX.val.val = (B.lift ∘ H ∘ h) w ∧
      e.toPoint aX = (θ.chart B.chart).toPoint bX := by
    intro w hw
    obtain ⟨aY,haY⟩ := (hm w hw).2
    obtain ⟨bY,hbY,hbYaY⟩ := hH.2.2.2.2 aY (by rw [haY]; exact (hm w hw).1)
    obtain ⟨aX,haX,hpaX⟩ := hfac aY
    obtain ⟨bX,hbX,hpbX⟩ := B.factor bY
    refine ⟨aX,bX,?_,?_,?_⟩
    · simpa only [haY,Function.comp_apply] using haX
    · simpa only [hbY,haY,Function.comp_apply] using hbX
    · exact hpaX.trans ((congrArg (fun q => f.hom.left.base q) hbYaY).symm.trans hpbX.symm)
  have hcore := pullback_eq_of_restrictsTo θ hv B.chart hD hG1 hG2 hpoints hz
  have hr : DifferentiableAt ℝ h z := (hd.differentiableAt (hD.mem_nhds hz)).restrictScalars ℝ
  have hHr : DifferentiableAt ℝ H (h z) :=
    (hH.2.2.1.differentiableAt (hH.1.mem_nhds (hm z hz).1)).restrictScalars ℝ
  have hAr : DifferentiableAt ℝ G (h z) :=
    ((hG.differentiableOn (by simp)).differentiableAt (a.ambient.isOpen.mem_nhds (hmapA hz))).restrictScalars ℝ
  have hBr : DifferentiableAt ℝ B.lift (H (h z)) :=
    ((B.holomorphic.differentiableOn (by simp)).differentiableAt
      (B.source.ambient.isOpen.mem_nhds (hmapB hz))).restrictScalars ℝ
  have hleft := pullbackForm_comp hr hAr v
  have hright := (pullbackForm_comp hr hHr (pullbackForm B.lift (θ.rep B.chart))).trans
    (pullbackForm_comp (hHr.comp z hr) hBr (θ.rep B.chart))
  exact hleft.trans (hcore.trans hright.symm)

/-- Equality of actual ambient coefficient fields preserves the ORIGINAL
restriction predicate. No quotient-form equality certificate is introduced. -/
theorem restrictsTo_congr {X : SourceReducedComplexSpace} {k : ℕ}
    {θ : SpaceForm X k} {e : LocalEmbedding X} {v w : AmbientForm e.dim k}
    (hv : θ.RestrictsTo e v) (hvw : ∀ z ∈ e.ambient, v z = w z) : θ.RestrictsTo e w := by
  intro i W G hG m D h hD hd hm z hz
  have hzero := hv i W G hG m D h hD hd hm z hz
  change ((w (h z) - pullbackForm G (θ.rep i) (h z)).compContinuousLinearMap (fderiv ℝ h z)) = 0
  rw [← hvw (h z) (hG.2.1 (hm z hz).1)]
  exact hzero

/-- Actual holomorphic ddc chain rule supplies a local potential of the
SAME original singular-space pullback form. -/
theorem pullback_restrictsTo_ddc {X Y : SourceReducedComplexSpace}
    (θ : SpaceForm X 2) (f : Y ⟶ X) {e : LocalEmbedding X} {g : ComplexModel e.dim → ℝ}
    (hg : ContDiffOn ℝ ∞ g e.ambient) (hv : θ.RestrictsTo e (smoothDDC g))
    (a : LocalEmbedding Y) {G : ComplexModel a.dim → ComplexModel e.dim}
    (hG : ContDiffOn ℂ ∞ G a.ambient) (hGmaps : MapsTo G a.ambient e.ambient)
    (hfac : ∀ c : a.carrier, ∃ b : e.carrier,
      b.val.val = G c.val.val ∧ e.toPoint b = f.hom.left.base (a.toPoint c)) :
    (pullback θ f).RestrictsTo a (smoothDDC (g ∘ G)) := by
  apply restrictsTo_congr (pullback_restrictsTo_of_lift θ f hv a hG hGmaps hfac)
  intro z hz
  exact (HolomorphicDDC.smoothDDC_comp a.ambient.isOpen e.ambient.isOpen hG hg hGmaps hz).symm

/-- Primitive original morphism lift into a prescribed actual target chart. -/
structure MorphismChartLift {X Y : SourceReducedComplexSpace} (f : Y ⟶ X) (e : LocalEmbedding X) where
  source : LocalEmbedding Y
  lift : ComplexModel source.dim → ComplexModel e.dim
  holomorphic : ContDiffOn ℂ ∞ lift source.ambient
  maps : MapsTo lift source.ambient e.ambient
  factor : ∀ c : source.carrier, ∃ b : e.carrier,
    b.val.val = lift c.val.val ∧ e.toPoint b = f.hom.left.base (source.toPoint c)

/-- Actual original morphism factorization manufactures the source chart
and primitive lift into the PRESCRIBED target chart. -/
theorem morphismChartLift_cover {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (e : LocalEmbedding X) (y : Y.obj.left) (hy : f.hom.left.base y ∈ range e.toPoint) :
    ∃ A : MorphismChartLift f e, y ∈ range A.source.toPoint := by
  let a := LocalEmbedding.ofPoint Y y
  obtain ⟨c,hcy⟩ := LocalEmbedding.mem_range_ofPoint Y y
  have hover : (a.map ≫ f.hom.left) ≫ X.obj.hom = (modelOver a.ambient a.carrier).hom := by
    rw [Category.assoc,Over.w f.hom,a.overPoint]
  have hcx : (a.map ≫ f.hom.left).base c ∈ range e.toPoint := by
    change f.hom.left.base (a.toPoint c) ∈ _
    rwa [hcy]
  obtain ⟨W,hW,hcW,hWU,G,hG,hmaps,hfac⟩ :=
    LocalEmbedding.exists_contDiffOn_factor (a.map ≫ f.hom.left) hover e c hcx
  let T : Opens (ComplexModel a.dim) := ⟨W,hW⟩
  let A : MorphismChartLift f e := {
    source := a.restrict T hWU
    lift := G
    holomorphic := hG
    maps := hmaps
    factor := by
      intro z
      let z' : a.carrier := ⟨⟨z.val.val,hWU z.val.property⟩,z.property⟩
      obtain ⟨b,hb,hpb⟩ := hfac z' z.val.property
      exact ⟨b,hb,hpb⟩ }
  refine ⟨A,?_,?_⟩
  · exact ⟨⟨c.val.val,hcW⟩,c.property⟩
  · change (a.restrict T hWU).toPoint _ = y
    rw [LocalEmbedding.restrict_toPoint]
    exact hcy

/-- Actual local potential on the ORIGINAL singular source is produced
from the original morphism and target local potential; no output chart,
lift, gauge or desired restriction certificate is input. -/
theorem exists_pullback_local_potential {X Y : SourceReducedComplexSpace}
    (θ : SpaceForm X 2) (f : Y ⟶ X) {e : LocalEmbedding X} {g : ComplexModel e.dim → ℝ}
    (hg : ContDiffOn ℝ ∞ g e.ambient) (hv : θ.RestrictsTo e (smoothDDC g))
    (y : Y.obj.left) (hy : f.hom.left.base y ∈ range e.toPoint) :
    ∃ a : LocalEmbedding Y, y ∈ range a.toPoint ∧
      ∃ h : ComplexModel a.dim → ℝ, ContDiffOn ℝ ∞ h a.ambient ∧
        (pullback θ f).RestrictsTo a (smoothDDC h) := by
  obtain ⟨A,hA⟩ := morphismChartLift_cover f e y hy
  exact ⟨A.source,hA,g ∘ A.lift,hg.comp (A.holomorphic.restrict_scalars ℝ) A.maps,
    pullback_restrictsTo_ddc θ f hg hv A.source A.holomorphic A.maps A.factor⟩

end SpaceForm
namespace SourceReducedComplexSpace

/-- The ORIGINAL theta-PSH predicate internally supplies actual local
potentials of the SAME pulled-back form at EVERY singular source point.
The remaining PSH/component-descent assertion is not assumed or claimed. -/
theorem IsThetaPSH.pullback_local_potentials {X Y : SourceReducedComplexSpace}
    {θ : SpaceForm X 2} {φ : X.obj.left → EReal} (hφ : X.IsThetaPSH θ φ) (f : Y ⟶ X)
    (y : Y.obj.left) :
    ∃ a : LocalEmbedding Y, y ∈ range a.toPoint ∧
      ∃ h : ComplexModel a.dim → ℝ, ContDiffOn ℝ ∞ h a.ambient ∧
        (SpaceForm.pullback θ f).RestrictsTo a (smoothDDC h) := by
  obtain ⟨e,he,-,g,hg,hres,-⟩ := hφ (f.hom.left.base y)
  exact SpaceForm.exists_pullback_local_potential θ f hg hres y he

end SourceReducedComplexSpace
end Hironaka.Analytic.Unibranch
