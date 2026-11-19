import Hironaka.Resolution.HironakaIntrinsicMorphismGluing
import Hironaka.Resolution.HironakaResolutionSpaceComplex
import Hironaka.Resolution.HironakaActualAnalyticSubspaceLocalFunctions

/-!
# Original analytic sources on genuine open overlaps

The existing analytic-chart property passes through an actual scalar-compatible
open immersion. On any original source with this property, scalar-compatible
maps into an actual reduced quotient-subspace model are determined by their
original point maps, including the ENTIRE structure-sheaf morphisms.

Blueprint: `hironaka-intrinsic-morphism-gluing-analytic.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace Topology CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaIntrinsicMorphismGluingAnalytic

noncomputable section

open HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps HironakaActualAnalyticSubspaceOpenRestriction
  HironakaActualAnalyticSubspaceLocalFunctions HironakaResolutionSpaceComplex

/-- An ORIGINAL scalar-compatible open immersion inherits actual analytic
charts on the SAME original locally ringed source. -/
theorem hasAnalyticCharts_of_openImmersion {H T : LocallyRingedSpace}
    (σH : H ⟶ complexPoint) (σT : T ⟶ complexPoint)
    (hT : hasAnalyticCharts (Over.mk σT))
    (j : H ⟶ T) [hj : LocallyRingedSpace.IsOpenImmersion j]
    (hjp : j ≫ σT = σH) : hasAnalyticCharts (Over.mk σH) := by
  let : T2Space T.toPresheafedSpace := hT.1
  let : SecondCountableTopology T.toPresheafedSpace := hT.2.1
  refine ⟨hj.base_open.isEmbedding.t2Space,
    hj.base_open.isEmbedding.secondCountableTopology, ?_⟩
  intro x
  obtain ⟨n, V, C, hC, i, hi, hip, c, hcx⟩ := hT.2.2 (j.base x)
  change i ≫ σT = subspacePointMap (n := n) C at hip
  let : LocallyRingedSpace.IsOpenImmersion i := hi
  let Q : Opens (TopCat.of C) :=
    ⟨i.base ⁻¹' range j.base, hj.base_open.isOpen_range.preimage i.base.hom.continuous⟩
  obtain ⟨O, hO, hOQ⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp Q.isOpen
  let A : Opens V := ⟨O, hO⟩
  have hcA : c.val ∈ A := by
    change c ∈ Subtype.val ⁻¹' O
    rw [hOQ]
    change i.base c ∈ range j.base
    rw [hcx]
    exact ⟨x, rfl⟩
  let C' : Set A := (Subtype.val : A → V) ⁻¹' C
  let R := actualOpenSubspaceMap (n := n) C A ≫ i
  have : LocallyRingedSpace.IsOpenImmersion R := by
    dsimp [R]
    infer_instance
  have hR : range R.base ⊆ range j.base := by
    rintro _ ⟨y, rfl⟩
    have hy : (⟨y.val.val, y.property⟩ : C) ∈ Q := by
      change (⟨y.val.val, y.property⟩ : C) ∈ (Q : Set C)
      rw [← hOQ]
      exact y.val.property
    exact hy
  let L := LocallyRingedSpace.IsOpenImmersion.lift j R hR
  have hfac : L ≫ j = R := LocallyRingedSpace.IsOpenImmersion.lift_fac j R hR
  have : LocallyRingedSpace.IsOpenImmersion L := by
    let : IsIso (pullback.snd j R) :=
      LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset j R hR
    dsimp [L, LocallyRingedSpace.IsOpenImmersion.lift]
    infer_instance
  have hLp : L ≫ σH = subspacePointMap (n := n) C' := by
    rw [← hjp, ← Category.assoc, hfac]
    dsimp [R]
    rw [Category.assoc, hip]
    exact actualSubspaceMap_point contMDiff_subtype_val (fun _ hy => hy)
  let c' : C' := ⟨⟨c.val, hcA⟩, c.property⟩
  have hLc : L.base c' = x := by
    apply hj.base_open.injective
    calc
      j.base (L.base c') = R.base c' := congrArg (fun f => f.base c') hfac
      _ = j.base x := hcx
  have hC' : IsComplexAnalyticSubset (n := n) C' :=
    AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hC A
  obtain ⟨V', D, hD, k, hk, hkp, z, hzc⟩ := exists_model_chart hC' c'
  let : LocallyRingedSpace.IsOpenImmersion k := hk
  refine ⟨n, V', D, hD, k ≫ L, inferInstance, ?_, z, ?_⟩
  · change (k ≫ L) ≫ σH = (modelOver V' D).hom
    rw [Category.assoc, hLp]
    exact hkp
  · change L.base (k.base z) = x
    rw [hzc, hLc]

/-- On an arbitrary ORIGINAL source with actual analytic charts, original
scalar-compatible maps into an actual quotient model are determined by their
base maps as FULL morphisms. The target subset W is arbitrary. -/
theorem morphism_eq_of_base_eq {T : LocallyRingedSpace}
    (σT : T ⟶ complexPoint) (hT : hasAnalyticCharts (Over.mk σT))
    {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {W : Set M}
    (F G : T ⟶ actualSubspaceLocallyRingedSpace (n := n) W)
    (hF : F ≫ subspacePointMap (n := n) W = σT)
    (hG : G ≫ subspacePointMap (n := n) W = σT)
    (hbase : F.base = G.base) : F = G := by
  classical
  choose d V C hC i hi hip hc using hT.2.2
  let : ∀ x, LocallyRingedSpace.IsOpenImmersion (i x) := hi
  have hcover : ∀ x : T, ∃ (a : T) (c : C a), (i a).base c = x :=
    fun x => ⟨x, hc x⟩
  apply HironakaIntrinsicMorphismGluing.hom_ext (fun x => (modelOver (V x) (C x)).left)
    i hcover F G
  intro x
  apply actualSubspaceMap_eq_of_base_eq (i x ≫ F) (i x ≫ G)
  · rw [Category.assoc, hF]
    exact hip x
  · rw [Category.assoc, hG]
    exact hip x
  · simp only [LocallyRingedSpace.comp_base, hbase]

end

end Hironaka.HironakaIntrinsicMorphismGluingAnalytic
