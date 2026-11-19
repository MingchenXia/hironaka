import Hironaka.Analytic.Unibranch.ComplexSpaceLocalEmbedding
import Hironaka.Resolution.HironakaActualAnalyticSubspaceLocalFunctions
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.HironakaG10ReducedLocalMapSquare
noncomputable section
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka
  HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps HironakaActualAnalyticSubspaceLocalFunctions
  HironakaActualAnalyticSubspaceOpenRestriction
  SourceReducedComplexSpace

/-- A morphism of reduced complex spaces has one actual ambient holomorphic
representative on a common neighborhood, compatible with both literal
local-embedding sheaf maps, including a possibly singular target carrier. -/
theorem exists_reduced_local_map_square {X Y : SourceReducedComplexSpace}
    (p : Y ⟶ X) (eX : LocalEmbedding X) (eY : LocalEmbedding Y) (c : eY.carrier)
    (hc : p.hom.left.base (eY.toPoint c) ∈ range eX.toPoint) :
    ∃ (U : Opens (ComplexModel eY.dim)) (hUV : U ≤ eY.ambient),
      c.val.val ∈ U ∧
      ∃ (f : U → eX.ambient)
        (hf : ContMDiff 𝓘(ℂ, ComplexModel eY.dim) 𝓘(ℂ, ComplexModel eX.dim) ∞ f)
        (hCD : ∀ z ∈ (eY.restrict U hUV).carrier, f z ∈ eX.carrier),
        actualSubspaceMap hf hCD ≫ eX.map = (eY.restrict U hUV).map ≫ p.hom.left := by
  let _ : LocallyRingedSpace.IsOpenImmersion eX.map := eX.isOpenImmersion
  let F := eY.map ≫ p.hom.left
  have hF : F ≫ X.obj.hom = (modelOver eY.ambient eY.carrier).hom := by
    dsimp only [F]
    rw [Category.assoc, Over.w p.hom]
    exact eY.overPoint
  obtain ⟨W, hW, hcW, hWU, G, hG, hGV, hfac⟩ :=
    LocalEmbedding.exists_contDiffOn_factor F hF eX c hc
  let U : Opens (ComplexModel eY.dim) := ⟨W, hW⟩
  have hUV : U ≤ eY.ambient := hWU
  let e := eY.restrict U hUV
  let _ : LocallyRingedSpace.IsOpenImmersion e.map := e.isOpenImmersion
  let f : U → eX.ambient := fun z => ⟨G z.val, hGV z.property⟩
  have hf : ContMDiff 𝓘(ℂ, ComplexModel eY.dim) 𝓘(ℂ, ComplexModel eX.dim) ∞ f := by
    apply (ContMDiff.subtypeVal_comp_iff eX.ambient f).mp
    intro z
    exact contMDiffAt_subtype_iff.mpr ((hG.contDiffAt (hW.mem_nhds z.property)).contMDiffAt)
  have hCD : ∀ z ∈ e.carrier, f z ∈ eX.carrier := by
    intro z hz
    let w : eY.carrier := ⟨Opens.inclusion hUV z, hz⟩
    obtain ⟨a, ha, _⟩ := hfac w z.property
    have heq : a.val = f z := Subtype.ext ha
    exact heq ▸ a.property
  let g := actualSubspaceMap hf hCD
  have hbase (z : e.carrier) : eX.toPoint (g.base z) = p.hom.left.base (e.toPoint z) := by
    let w : eY.carrier := ⟨Opens.inclusion hUV z.val, z.property⟩
    obtain ⟨a, ha, hpa⟩ := hfac w z.val.property
    have hga : g.base z = a := by
      apply Subtype.ext
      apply Subtype.ext
      exact ha.symm
    rw [hga, hpa]
    rfl
  let R := e.map ≫ p.hom.left
  have hrange : range R.base ⊆ range eX.map.base := by
    rintro _ ⟨z, rfl⟩
    exact ⟨g.base z, hbase z⟩
  let H := LocallyRingedSpace.IsOpenImmersion.lift eX.map R hrange
  have hHfac : H ≫ eX.map = R := LocallyRingedSpace.IsOpenImmersion.lift_fac eX.map R hrange
  have hHp : H ≫ subspacePointMap (n := eX.dim) eX.carrier =
      subspacePointMap (n := e.dim) e.carrier := by
    calc
      _ = H ≫ (eX.map ≫ X.obj.hom) := congrArg (H ≫ ·) eX.overPoint.symm
      _ = R ≫ X.obj.hom := by rw [← Category.assoc, hHfac]
      _ = _ := by
        dsimp only [R]
        rw [Category.assoc, Over.w p.hom]
        exact e.overPoint
  have hgH : g = H := by
    apply actualSubspaceMap_eq_of_base_eq g H
    · exact actualSubspaceMap_point hf _
    · exact hHp
    · ext z
      apply eX.toPoint_injective
      have hh := congrArg (fun k => k.base z) hHfac
      exact (hbase z).trans hh.symm
  refine ⟨U,hUV,hcW,f,hf,hCD,?_⟩
  change g ≫ eX.map = R
  rw [hgH]
  exact hHfac
end
end Hironaka.Analytic.Unibranch.HironakaG10ReducedLocalMapSquare
