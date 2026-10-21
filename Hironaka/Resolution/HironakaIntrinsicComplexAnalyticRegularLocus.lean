/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualAnalyticSubspaceRegularityConverse

/-!
# The actual intrinsic regular locus is open and dense

Intrinsic regularity means existence of a genuine over-complex-point native
manifold open chart. Both actual chart/whole-ideal directions identify it
with original embedded RegularAtDim. Ordinary analytic model charts and
actual original regular-point density imply density on every object of the
constructed reduced complex analytic category, without resolution data.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaIntrinsicComplexAnalyticRegularLocus
noncomputable section
open Hironaka.HolomorphicIdealSheaves
  HironakaActualAnalyticSubspace HironakaReducedComplexAnalyticSpaces
  HironakaActualAnalyticSubspaceManifoldCharts HironakaActualAnalyticSubspaceRegularityConverse

/-- Actual intrinsic regularity uses ordinary native manifold open charts over the SAME complex point. -/
def intrinsicRegularAtDim (A : Over complexPoint) (x : A.left) (d : ℕ) : Prop :=
  ∃ (O : Opens (ComplexModel d))
    (i : ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel d) O ⟶ A.left),
    LocallyRingedSpace.IsOpenImmersion i ∧ i ≫ A.hom = ambientPointMap d O ∧ x ∈ range i.base

/-- The actual intrinsic regular locus permits the genuine local dimension to vary. -/
def intrinsicRegularLocus (A : Over complexPoint) : Set A.left :=
  {x | ∃ d : ℕ,intrinsicRegularAtDim A x d}

/-- The genuine intrinsic singular locus is the actual complement of native regular points. -/
def intrinsicSingularLocus (A : Over complexPoint) : Set A.left := (intrinsicRegularLocus A)ᶜ

/-- The native chart predicate equals EXISTING original regularity of the SAME embedded subset. -/
theorem intrinsicRegularAtDim_model_iff {n d : ℕ} {U : Opens (ComplexModel n)}
    (C : Set U) (x : C) :
    intrinsicRegularAtDim (modelOver U C) x d ↔ RegularAtDim (n := n) C x.val d := by
  constructor
  · rintro ⟨O,i,hi,hpoint,y,hy⟩
    let : LocallyRingedSpace.IsOpenImmersion i := hi
    have hr := regularAtDim_of_native_manifold_chart i hpoint y
    have hp : (i.base y : C).val = x.val := congrArg (fun z : C => z.val) hy
    exact hp ▸ hr
  · intro hreg
    obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hreg.1
    obtain ⟨O,i,hi,hpoint,hcover⟩ := exists_actual_regular_subspace_manifold_chart C x.val hreg
    exact ⟨O,i,hi,hpoint,hcover⟩

/-- Each fixed-dimension actual intrinsic regular locus is genuinely open. -/
theorem isOpen_intrinsicRegularAtDim (A : Over complexPoint) (d : ℕ) :
    IsOpen {x : A.left | intrinsicRegularAtDim A x d} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨O,i,hi,hpoint,hcover⟩ := hx
  exact Filter.mem_of_superset (hi.base_open.isOpen_range.mem_nhds hcover)
    (fun y hy => ⟨O,i,hi,hpoint,hy⟩)

/-- The whole intrinsic regular locus is open; its actual singular complement is closed. -/
theorem isOpen_intrinsicRegularLocus (A : Over complexPoint) : IsOpen (intrinsicRegularLocus A) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨d,hd⟩
  exact Filter.mem_of_superset ((isOpen_intrinsicRegularAtDim A d).mem_nhds hd)
    (fun y hy => ⟨d,hy⟩)

/-- The actual intrinsic singular locus is closed in the true underlying space. -/
theorem isClosed_intrinsicSingularLocus (A : Over complexPoint) : IsClosed (intrinsicSingularLocus A) :=
  (isOpen_intrinsicRegularLocus A).isClosed_compl

/-- Every actual neighbourhood in ANY abstract analytic object contains a genuine intrinsic regular point. -/
theorem exists_intrinsicRegularAtDim_mem_nhds (A : ReducedComplexAnalyticSpace)
    (x : A.obj.left) {W : Set A.obj.left} (hW : W ∈ nhds x) :
    ∃ y ∈ W,∃ d : ℕ,intrinsicRegularAtDim A.obj y d := by
  obtain ⟨n,U,C,hC,i,hi,hpoint,c,hcx⟩ := A.property.2.2 x
  have hW' : W ∈ nhds (i.base c) := by rw [hcx];exact hW
  have hpre : i.base ⁻¹' W ∈ nhds c := i.base.hom.continuous.continuousAt.preimage_mem_nhds hW'
  obtain ⟨Q,hQsub,hQ,hcQ⟩ := mem_nhds_iff.mp hpre
  obtain ⟨T,hT,hTQ⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hQ
  have hcT : c.val ∈ T := by
    change c ∈ (Subtype.val : C → U) ⁻¹' T
    rw [hTQ]
    exact hcQ
  obtain ⟨y,hyT,d,hreg⟩ := RegularLocusDense.exists_regularAtDim_mem_nhds hC c.property
    (hT.mem_nhds hcT)
  let z : C := ⟨y,hreg.2.1⟩
  have hzQ : z ∈ Q := by
    rw [← hTQ]
    exact hyT
  have hzW : i.base z ∈ W := hQsub hzQ
  obtain ⟨O,j,hj,hjp,v,hv⟩ := (intrinsicRegularAtDim_model_iff C z).mpr hreg
  let : LocallyRingedSpace.IsOpenImmersion i := hi
  let : LocallyRingedSpace.IsOpenImmersion j := hj
  refine ⟨i.base z,hzW,d,O,j ≫ i,inferInstance,?_,v,?_⟩
  · rw [Category.assoc,hpoint]
    exact hjp
  · change i.base (j.base v) = i.base z
    rw [hv]

/-- Every actual reduced complex analytic space has a dense intrinsic regular locus. -/
theorem dense_intrinsicRegularLocus (A : ReducedComplexAnalyticSpace) :
    Dense (intrinsicRegularLocus A.obj) := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro x
  rw [mem_closure_iff_nhds]
  intro W hW
  obtain ⟨y,hy,d,hd⟩ := exists_intrinsicRegularAtDim_mem_nhds A x hW
  exact ⟨y,hy,d,hd⟩

end
end Hironaka.HironakaIntrinsicComplexAnalyticRegularLocus
