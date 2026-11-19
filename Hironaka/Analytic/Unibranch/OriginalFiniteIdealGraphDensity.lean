import Hironaka.Analytic.Unibranch.OriginalFiniteIdealGraphChart
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Explicit original generic nonvanishing gives actual graph density

Only the ORIGINAL global unit-stalk-image locus is assumed dense. Both
current graph ideals and the actual graph are constructed from native finite
type by the frozen source producer; no current dictionary/density is input.
Zero-on-components ideals are not claimed to satisfy this hypothesis.
Blueprint: `original-finite-ideal-graph-density.tex`.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.OriginalFiniteIdealGraphDensity

open Hironaka
  Hironaka.HolomorphicIdealSheaves Hironaka
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaReducedComplexAnalyticSpaces HironakaNativePulledIdealSheaf
  HironakaSingularModuleSheafStalk HironakaFiniteSectionProductGraph
  SourceReducedComplexSpace OriginalFiniteIdealGraphChart

open scoped ProductComplexManifold

noncomputable section

private theorem local_map_ideal_eq_top_iff {R S : Type} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (f : R →+* S) [IsLocalHom f] (I : Ideal R) :
    Ideal.map f I = ⊤ ↔ I = ⊤ := by
  constructor
  · intro h
    by_contra hI
    have hlt : Ideal.map f I < ⊤ :=
      (Ideal.map_mono (IsLocalRing.le_maximalIdeal hI)).trans_lt
        (IsLocalRing.map_maximalIdeal_lt_top f)
    exact hlt.ne h
  · rintro rfl
    exact Ideal.map_top f

/-- A native WHOLE pulled ideal is the unit ideal precisely on the SAME
original unit-stalk-image locus; this uses actual local stalk homomorphisms. -/
theorem nativePulledIdealStalkIdeal_eq_top_iff {A X : LocallyRingedSpace}
    (F : A ⟶ X) (B : SheafOfModules.{0} (forgetRing X.toSheafedSpace.sheaf))
    (b : B ⟶ SheafOfModules.unit (forgetRing X.toSheafedSpace.sheaf)) (x : A) :
    nativePulledIdealStalkIdeal F B b x = ⊤ ↔
      LinearMap.range (stalkInclusionLinearMap X.toSheafedSpace.sheaf B b (F.base x)) = ⊤ :=
  local_map_ideal_eq_top_iff (F.stalkMap x).hom _

/-- The ENTIRE actual vanishing ideal of a genuine closed subset is the
unit ideal exactly off that SAME original subset. -/
theorem actualWholeVanishing_eq_top_iff {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (C : Set M) (hC : IsClosed C) (p : M) :
    actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) p = ⊤ ↔ p ∉ C := by
  constructor
  · intro h hp
    have hk := RingHom.ker_ne_top ((actualSubspaceInclusion (n := n) C).stalkMap (⟨p,hp⟩ : C)).hom
    exact hk ((actualSubspaceInclusion_stalk_kernel (n := n) C (⟨p,hp⟩ : C)).trans h)
  · intro hp
    have hf : (vanishingIdeal (n := n) C).mem p (fun _ : M => (1 : ℂ)) := by
      refine ⟨holomorphicAt_const 1,?_⟩
      filter_upwards [hC.isOpen_compl.mem_nhds hp] with q hq hqC
      exact False.elim (hq hqC)
    have hg : actualOriginalFunctionGerm (n := n) p (fun _ : M => (1 : ℂ)) (holomorphicAt_const 1) = 1 := by
      apply (actualStalkChartEquiv (n := n) p).injective
      rw [actualOriginalFunctionGerm_chart,map_one]
      rfl
    refine (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) p).eq_top_of_isUnit_mem ?_ isUnit_one
    rw [← hg]
    exact Ideal.subset_span ⟨(fun _ : M => (1 : ℂ)),holomorphicAt_const 1,hf,rfl⟩

variable {X : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf))

private theorem graph_density (e : LocalEmbedding X) (O : Opens e.ambient) {r : ℕ}
    (G : O → ComplexModel r)
    (hG : ContMDiff 𝓘(ℂ,ComplexModel e.dim) 𝓘(ℂ,ComplexModel r) ∞ G)
    (hDense : Dense {x : X.obj.left |
      LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊤})
    (hJ : ∀ z : productGraph ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G,
      Ideal.map ((actualSubspaceInclusion (n := e.dim+r)
        (productGraph ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G)).stalkMap z).hom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := e.dim+r)
            {q : O × ComplexModel r | q.2 = 0}) z.val) =
        nativePulledIdealStalkIdeal (chartGraphMap e O G hG) B b z) :
    productGraph ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G ⊆
      closure (productGraph ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G \
        {q : O × ComplexModel r | q.2 = 0}) := by
  let Γ := productGraph ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G
  have hC : IsClosed {q : O × ComplexModel r | q.2 = 0} :=
    isClosed_singleton.preimage continuous_snd
  have hiff (z : Γ) : z.val.2 ≠ 0 ↔
      LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b
        ((chartGraphMap e O G hG).base z)) = ⊤ := by
    calc
      _ ↔ actualWholeSheafStalkIdeal (vanishingIdeal (n := e.dim+r)
          {q : O × ComplexModel r | q.2 = 0}) z.val = ⊤ :=
        (actualWholeVanishing_eq_top_iff _ hC z.val).symm
      _ ↔ Ideal.map ((actualSubspaceInclusion (n := e.dim+r) Γ).stalkMap z).hom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := e.dim+r)
            {q : O × ComplexModel r | q.2 = 0}) z.val) = ⊤ :=
        (local_map_ideal_eq_top_iff ((actualSubspaceInclusion (n := e.dim+r) Γ).stalkMap z).hom _).symm
      _ ↔ nativePulledIdealStalkIdeal (chartGraphMap e O G hG) B b z = ⊤ :=
        iff_of_eq (congrArg (fun I => I = ⊤) (hJ z))
      _ ↔ _ := nativePulledIdealStalkIdeal_eq_top_iff (chartGraphMap e O G hG) B b z
  have hd := hDense.preimage
    (chartGraphMap_isOpenImmersion e O G hG).base_open.isOpenMap
  have hset : {z : Γ | LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b
        ((chartGraphMap e O G hG).base z)) = ⊤} = {z : Γ | z.val.2 ≠ 0} :=
    Set.ext fun z => (hiff z).symm
  change Dense {z : Γ | LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b
    ((chartGraphMap e O G hG).base z)) = ⊤} at hd
  rw [hset] at hd
  have himage : (Subtype.val : Γ → O × ComplexModel r) '' {z : Γ | z.val.2 ≠ 0} =
      Γ \ {q : O × ComplexModel r | q.2 = 0} := by
    ext q
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨z.property,hz⟩
    · rintro ⟨hq,hq0⟩
      exact ⟨⟨q,hq⟩,hq0,rfl⟩
  intro q hq
  have hqcl : (⟨q,hq⟩ : Γ) ∈ closure {z : Γ | z.val.2 ≠ 0} := by
    rw [hd.closure_eq]
    trivial
  have ha := mem_closure_image continuous_subtype_val.continuousAt hqcl
  rw [himage] at ha
  exact ha

/-- Standard FT and EXPLICIT dense original unit-stalk-image locus internally
produce actual original graph charts with honest off-plane density and positive
generator length. No current graph/dictionary/density packet is supplied. -/
theorem exists_dense_graph_chart [B.IsFiniteType]
    (hDense : Dense {x : X.obj.left |
      LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊤})
    (x : X.obj.left) :
    ∃ (e : LocalEmbedding X) (O : Opens e.ambient) (r : ℕ)
      (G : O → ComplexModel r)
      (hG : ContMDiff 𝓘(ℂ,ComplexModel e.dim) 𝓘(ℂ,ComplexModel r) ∞ G)
      (_hΓ : IsComplexAnalyticSubset (n := e.dim+r)
        (productGraph ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G)),
      (∀ z : productGraph ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G,
        Ideal.map ((actualSubspaceInclusion (n := e.dim+r)
          (productGraph ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G)).stalkMap z).hom
            (actualWholeSheafStalkIdeal (vanishingIdeal (n := e.dim+r)
              {q : O × ComplexModel r | q.2 = 0}) z.val) =
          nativePulledIdealStalkIdeal (chartGraphMap e O G hG) B b z) ∧
      (productGraph ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G ⊆
        closure (productGraph ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G \
          {q : O × ComplexModel r | q.2 = 0})) ∧ 0 < r ∧
      ∃ z : productGraph ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G,
        (chartGraphMap e O G hG).base z = x := by
  obtain ⟨e,O,r,G,hG,hΓ,_hparam,hJ,z,hz⟩ := exists_graph_chart B b x
  have hd := graph_density B b e O G hG hDense hJ
  have hr : 0 < r := by
    by_contra h
    have hr0 : r = 0 := by omega
    have hsub : Subsingleton (ComplexModel r) := hr0.symm ▸ inferInstance
    have hzero (q : O × ComplexModel r) : q.2 = 0 :=
      @Subsingleton.elim (ComplexModel r) hsub q.2 0
    have he : productGraph ((Subtype.val : O → e.ambient) ⁻¹' e.carrier) G \
        {q : O × ComplexModel r | q.2 = 0} = ∅ := by
      ext q
      simp only [Set.mem_sdiff,Set.mem_ofPred_eq,hzero,
        not_true_eq_false,and_false,Set.mem_empty_iff_false]
    have hc := hd z.property
    rw [he,closure_empty] at hc
    exact hc
  exact ⟨e,O,r,G,hG,hΓ,hJ,hd,hr,z,hz⟩

end
end Hironaka.Analytic.Unibranch.OriginalFiniteIdealGraphDensity
