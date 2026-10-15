/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Manifold.ComplexManifold
import Mathlib.Topology.Gluing
import Mathlib.Topology.Bases
/-! Genuine separation, countability and lifted charts for a terminal atlas.
Complete three-node mathematics preceded proofs. Saturated actual projection
ranges, not a global separation/countability certificate, supply the geometry. -/
set_option autoImplicit false
open Set TopologicalSpace Topology
open scoped Manifold ContDiff
universe u v w
namespace Hironaka.HironakaTerminalAtlasTopology
noncomputable section

variable {J : Type u} {F : J → Type v} {X G : Type w}
  [TopologicalSpace X] [TopologicalSpace G] [∀ i, TopologicalSpace (F i)]

theorem t2Space_of_actual_saturated_projection_atlas [T2Space X] [∀ i, T2Space (F i)]
    (p : G → X) (hp : Continuous p) (U : J → Opens X)
    (hcover : ∀ x : X, ∃ i, x ∈ U i) (ι : ∀ i, F i → G)
    (hι : ∀ i, IsOpenEmbedding (ι i)) (hrange : ∀ i, range (ι i)=p ⁻¹' (U i : Set X)) :
    T2Space G where
  t2 a b hab := by
    by_cases he : p a=p b
    · obtain ⟨i,hi⟩ := hcover (p a)
      have ha : a ∈ range (ι i) := by rw [hrange i]; exact hi
      have hb : b ∈ range (ι i) := by
        rw [hrange i]
        change p b ∈ U i
        rw [← he]
        exact hi
      obtain ⟨a',rfl⟩ := ha
      obtain ⟨b',rfl⟩ := hb
      have hne : a'≠b' := fun h => hab (congrArg (ι i) h)
      obtain ⟨A,B,hA,hB,ha',hb',hd⟩ := t2_separation hne
      refine ⟨ι i '' A,ι i '' B,(hι i).isOpenMap _ hA,(hι i).isOpenMap _ hB,
        mem_image_of_mem _ ha',mem_image_of_mem _ hb',?_⟩
      apply disjoint_left.mpr
      rintro _ ⟨x,hx,rfl⟩ ⟨y,hy,heq⟩
      have hxy : y=x := (hι i).injective heq
      subst y
      exact disjoint_left.mp hd hx hy
    · obtain ⟨A,B,hA,hB,ha,hb,hd⟩ := t2_separation he
      refine ⟨p ⁻¹' A,p ⁻¹' B,hA.preimage hp,hB.preimage hp,ha,hb,?_⟩
      exact hd.preimage p

theorem secondCountable_of_actual_saturated_projection_atlas
    [SecondCountableTopology X] [∀ i, SecondCountableTopology (F i)]
    (p : G → X) (U : J → Opens X) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (ι : ∀ i, F i → G) (hι : ∀ i, IsOpenEmbedding (ι i))
    (hrange : ∀ i, range (ι i)=p ⁻¹' (U i : Set X)) : SecondCountableTopology G := by
  obtain ⟨S,hS,hunion⟩ := isOpen_iUnion_countable (fun i => (U i : Set X)) (fun i => (U i).isOpen)
  have hu : (⋃ i ∈ S, (U i : Set X))=univ := hunion.trans (by
    apply eq_univ_iff_forall.mpr
    intro x
    obtain ⟨i,hi⟩ := hcover x
    exact mem_iUnion.mpr ⟨i,hi⟩)
  let : Countable S := hS.to_subtype
  let R : S → Set G := fun i => range (ι i.val)
  let : ∀ i : S, SecondCountableTopology (R i) := fun i =>
    (hι i.val).isEmbedding.toHomeomorph.symm.secondCountableTopology
  apply secondCountableTopology_of_countable_cover (U := R) (fun i => (hι i.val).isOpen_range)
  apply eq_univ_iff_forall.mpr
  intro z
  have hz : p z ∈ ⋃ i ∈ S, (U i : Set X) := hu.symm ▸ mem_univ _
  obtain ⟨i,his⟩ := mem_iUnion.mp hz
  obtain ⟨hiS,hiz⟩ := mem_iUnion.mp his
  refine mem_iUnion.mpr ⟨⟨i,hiS⟩,?_⟩
  change z ∈ range (ι i)
  rw [hrange i]
  exact hiz

variable (n : ℕ) [∀ i, ChartedSpace (ComplexModel n) (F i)]

@[instance_reducible]
def actualLiftedTerminalChartedSpace (ι : ∀ i, F i → G)
    (hι : ∀ i, IsOpenEmbedding (ι i)) (hcover : ∀ z : G, ∃ i y, ι i y=z) :
    ChartedSpace (ComplexModel n) G where
  atlas := {a | ∃ (i : J) (e : OpenPartialHomeomorph (F i) (ComplexModel n)),
    e ∈ atlas (ComplexModel n) (F i) ∧ a=e.lift_openEmbedding (hι i)}
  chartAt z := (chartAt (ComplexModel n) (hcover z).choose_spec.choose).lift_openEmbedding
    (hι (hcover z).choose)
  mem_chart_source z := by
    change z ∈ ι (hcover z).choose '' (chartAt (ComplexModel n) (hcover z).choose_spec.choose).source
    exact ⟨(hcover z).choose_spec.choose,mem_chart_source (ComplexModel n) _,
      (hcover z).choose_spec.choose_spec⟩
  chart_mem_atlas z := ⟨(hcover z).choose,chartAt (ComplexModel n) (hcover z).choose_spec.choose,
    chart_mem_atlas (ComplexModel n) _,rfl⟩

end
end Hironaka.HironakaTerminalAtlasTopology
