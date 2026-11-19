import Hironaka.Analytic.Unibranch.ComplexSpaceFormPullbackClosed
import Hironaka.Analytic.Unibranch.ComplexSpacePSHPullbackFinite

/-! Genuine finite theta-PSH pullback for the SAME original singular
complex spaces and SpaceForm pullback. Blueprint:
complex-space-theta-psh-finite.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open Hironaka
open Hironaka.HironakaReducedComplexAnalyticSpaces
open Hironaka.HironakaActualAnalyticSubspaceMaps
namespace Hironaka.Analytic.Unibranch
namespace SourceReducedComplexSpace

/-- The genuine actual analytic-model morphism induced by an ambient
holomorphic map, retaining both original possibly singular carriers. -/
def analyticModelMorphism {n m : ℕ} {U : Opens (ComplexModel n)}
    {V : Opens (ComplexModel m)} {C : Set U} {D : Set V}
    (hC : IsComplexAnalyticSubset C) (hD : IsComplexAnalyticSubset D)
    (G : ComplexModel n → ComplexModel m) (hG : ContDiffOn ℂ ∞ G U)
    (hmaps : MapsTo G U V)
    (hcarrier : ∀ c : C,(⟨G c.val.val,hmaps c.val.property⟩ : V) ∈ D) :
    sourceReducedComplexSpaceModel U C hC ⟶ sourceReducedComplexSpaceModel V D hD := by
  let g : U → V := fun z => ⟨G z.val,hmaps z.property⟩
  have hg : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ g := by
    apply (ContMDiff.subtypeVal_comp_iff V g).mp
    exact hG.contMDiffOn.comp_contMDiff contMDiff_subtype_val (fun z => z.property)
  exact ObjectProperty.homMk (Over.homMk (actualSubspaceMap hg (fun c hc => hcarrier ⟨c,hc⟩))
    (actualSubspaceMap_point hg _))

@[simp] theorem analyticModelMorphism_apply {n m : ℕ} {U : Opens (ComplexModel n)}
    {V : Opens (ComplexModel m)} {C : Set U} {D : Set V}
    (hC : IsComplexAnalyticSubset C) (hD : IsComplexAnalyticSubset D)
    (G : ComplexModel n → ComplexModel m) (hG : ContDiffOn ℂ ∞ G U)
    (hmaps : MapsTo G U V)
    (hcarrier : ∀ c : C,(⟨G c.val.val,hmaps c.val.property⟩ : V) ∈ D) (c : C) :
    (analyticModelMorphism hC hD G hG hmaps hcarrier).hom.left.base c =
      ⟨⟨G c.val.val,hmaps c.val.property⟩,hcarrier c⟩ := rfl

end SourceReducedComplexSpace
namespace SpaceForm

/-- An actual connected ambient source lift is produced internally. -/
theorem morphismChartLift_connected_cover {X Y : SourceReducedComplexSpace}
    (f : Y ⟶ X) (e : LocalEmbedding X) (y : Y.obj.left)
    (hy : f.hom.left.base y ∈ range e.toPoint) :
    ∃ A : MorphismChartLift f e, y ∈ range A.source.toPoint ∧
      IsConnected (A.source.ambient : Set (ComplexModel A.source.dim)) := by
  obtain ⟨B,⟨c,hc⟩⟩ := morphismChartLift_cover f e y hy
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp B.source.ambient.isOpen c.val.val c.val.property
  let T : Opens (ComplexModel B.source.dim) := ⟨Metric.ball c.val.val r,Metric.isOpen_ball⟩
  let A : MorphismChartLift f e := {
    source := B.source.restrict T hball
    lift := B.lift
    holomorphic := B.holomorphic.mono hball
    maps := B.maps.mono_left hball
    factor := fun z => B.factor ⟨⟨z.val.val,hball z.val.property⟩,z.property⟩ }
  refine ⟨A,?_,?_⟩
  · refine ⟨⟨⟨c.val.val,Metric.mem_ball_self hr⟩,c.property⟩,?_⟩
    change (B.source.restrict T hball).toPoint _ = y
    rw [LocalEmbedding.restrict_toPoint]
    exact hc
  · exact convex_ball _ _ |>.isConnected ⟨c.val.val,Metric.mem_ball_self hr⟩

end SpaceForm
namespace SourceReducedComplexSpace

/-- Actual finite theta-PSH pullback, with original form, local PSH models
and every original component nondegeneracy field manufactured internally. -/
theorem IsThetaPSH.pullback_of_finite {X Y : SourceReducedComplexSpace}
    {θ : SpaceForm X 2} {φ : X.obj.left → EReal} (hφ : X.IsThetaPSH θ φ)
    (hfinite : ∀ x : X.obj.left,φ x ≠ ⊥) (f : Y ⟶ X) :
    Y.IsThetaPSH (SpaceForm.pullback θ f) (fun y => φ (f.hom.left.base y)) := by
  intro y
  obtain ⟨e,he,-,g,hg,hres,hpsh⟩ := hφ (f.hom.left.base y)
  obtain ⟨A,hA,hconn⟩ := SpaceForm.morphismChartLift_connected_cover f e y he
  let hc : ∀ c : A.source.carrier,
      (⟨A.lift c.val.val,A.maps c.val.property⟩ : e.ambient) ∈ e.carrier := by
    intro c
    obtain ⟨b,hb,-⟩ := A.factor c
    have hval : (⟨A.lift c.val.val,A.maps c.val.property⟩ : e.ambient) = b.val :=
      Subtype.ext hb.symm
    rw [hval]
    exact b.property
  let F := analyticModelMorphism A.source.analytic e.analytic A.lift A.holomorphic A.maps hc
  have hfiniteCorrected (b : e.carrier) :
      (g b.val.val : EReal) + φ (e.toPoint b) ≠ ⊥ := by
    exact EReal.add_ne_bot_iff.mpr ⟨EReal.coe_ne_bot _,hfinite _⟩
  have hsource := hpsh.pullback_of_finite hfiniteCorrected F
  refine ⟨A.source,hA,hconn,g ∘ A.lift,
    hg.comp (A.holomorphic.restrict_scalars ℝ) A.maps,
    SpaceForm.pullback_restrictsTo_ddc θ f hg hres A.source A.holomorphic A.maps A.factor,?_⟩
  have heq : (fun c : A.source.carrier =>
      (g ((F.hom.left.base c).val.val) : EReal) + φ (e.toPoint (F.hom.left.base c))) =
      (fun c : A.source.carrier =>
        ((g ∘ A.lift) c.val.val : EReal) + φ (f.hom.left.base (A.source.toPoint c))) := by
    funext c
    obtain ⟨b,hb,hpb⟩ := A.factor c
    have hFb : F.hom.left.base c = b := by
      apply Subtype.ext
      apply Subtype.ext
      exact hb.symm
    rw [hFb,hb,hpb]
    rfl
  rw [← heq]
  exact hsource

end SourceReducedComplexSpace
end Hironaka.Analytic.Unibranch
