import Hironaka.Analytic.Unibranch.ComplexSpacePSH

/-! Actual original local PSH pullback at finite points, and genuine
component nondegeneracy for finite PSH on arbitrary singular spaces.
Blueprint: complex-space-psh-pullback-finite.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology ContDiff
open Hironaka
open Hironaka.HironakaReducedComplexAnalyticSpaces
namespace Hironaka.Analytic.Unibranch.SourceReducedComplexSpace

/-- At an actual non-pole point, an actual morphism pulls back the ORIGINAL
local ambient PSH property. No desired source representative is supplied. -/
theorem IsLocallyAmbientPSHAt.pullback_of_ne_bot
    {X Y : SourceReducedComplexSpace} {φ : X.obj.left → EReal}
    (f : Y ⟶ X) (y : Y.obj.left)
    (hφ : X.IsLocallyAmbientPSHAt φ (f.hom.left.base y))
    (hy : φ (f.hom.left.base y) ≠ ⊥) :
    Y.IsLocallyAmbientPSHAt (fun z => φ (f.hom.left.base z)) y := by
  obtain ⟨e,he,-,ψ,hψ,hrep⟩ := hφ
  let a := LocalEmbedding.ofPoint Y y
  obtain ⟨c,hcy⟩ := LocalEmbedding.mem_range_ofPoint Y y
  have hover : (a.map ≫ f.hom.left) ≫ X.obj.hom = (modelOver a.ambient a.carrier).hom := by
    rw [Category.assoc,Over.w f.hom,a.overPoint]
  have hc : (a.map ≫ f.hom.left).base c ∈ range e.toPoint := by
    change f.hom.left.base (a.toPoint c) ∈ _
    rwa [hcy]
  obtain ⟨W,hW,hcW,hWU,G,hG,hmaps,hfac⟩ :=
    LocalEmbedding.exists_differentiableOn_factor (a.map ≫ f.hom.left) hover e c hc
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hW c.val.val hcW
  let T : Opens (ComplexModel a.dim) := ⟨Metric.ball c.val.val r,Metric.isOpen_ball⟩
  have hT : T ≤ a.ambient := fun z hz => hWU (hball hz)
  have hcomp := Hironaka.Analytic.PotentialTheory.discPshOn_comp_holomorphic hW e.ambient.isOpen hG hmaps hψ
  have hvalue (z : a.carrier) (hz : z.val.val ∈ W) :
      φ (f.hom.left.base (a.toPoint z)) = ψ (G z.val.val) := by
    obtain ⟨b,hb,hpb⟩ := hfac z hz
    change e.toPoint b = f.hom.left.base (a.toPoint z) at hpb
    rw [← hpb,hrep b,hb]
  refine ⟨a.restrict T hT,?_,?_,fun z => ψ (G z),⟨hcomp.mono hball,?_⟩,?_⟩
  · refine ⟨⟨⟨c.val.val,Metric.mem_ball_self hr⟩,c.property⟩,?_⟩
    rw [LocalEmbedding.restrict_toPoint]
    exact hcy
  · exact convex_ball _ _ |>.isConnected ⟨c.val.val,Metric.mem_ball_self hr⟩
  · refine ⟨c.val.val,Metric.mem_ball_self hr,?_⟩
    rw [← hvalue c hcW,hcy]
    exact hy
  · intro z
    rw [LocalEmbedding.restrict_toPoint]
    exact hvalue _ (hball z.val.property)

/-- A finite original PSH function pulls back to the ORIGINAL PSH predicate
on arbitrary actual singular reduced complex spaces. Component nondegeneracy
is produced from actual nonempty irreducible components and finite values. -/
theorem IsPSH.pullback_of_finite {X Y : SourceReducedComplexSpace}
    {φ : X.obj.left → EReal} (hφ : X.IsPSH φ)
    (hfinite : ∀ x : X.obj.left,φ x ≠ ⊥) (f : Y ⟶ X) :
    Y.IsPSH (fun y => φ (f.hom.left.base y)) := by
  refine ⟨?_,?_⟩
  · intro Z hZ
    obtain ⟨z,hz⟩ := hZ.1.2.1
    exact ⟨z,hz,hfinite _⟩
  · intro y
    exact (hφ.2 _).pullback_of_ne_bot f y (hfinite _)

end Hironaka.Analytic.Unibranch.SourceReducedComplexSpace
