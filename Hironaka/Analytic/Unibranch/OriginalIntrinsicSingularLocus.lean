import Hironaka.Analytic.Unibranch.Resolution
import Hironaka.Resolution.HironakaIntrinsicComplexAnalyticRegularLocus

/-!
# Intrinsic singular loci on arbitrary original reduced complex spaces

Every original local embedding identifies the existing native intrinsic
regular-point predicate with embedded regularity, in every dimension.
The SAME intrinsic singular locus is analytic, with dense regular complement.
No global second countability, purity, compactness or Kahler premise is used
for these local assertions. Compactness is only a final ordinary consequence.

Blueprint FIRST: `original-intrinsic-singular-locus.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.OriginalIntrinsicSingularLocus

open Hironaka Hironaka
  HironakaActualAnalyticSubspace HironakaReducedComplexAnalyticSpaces
  HironakaIntrinsicComplexAnalyticRegularLocus
  HironakaActualAnalyticSubspaceRegularityConverse HironakaEmbeddedAnalytic
  SourceReducedComplexSpace

noncomputable section

-- Native open-immersion lifting is held infrastructure, with zero extra credit.
private theorem openImmersion_lift {A B T : LocallyRingedSpace}
    (f : A ⟶ T) (g : B ⟶ T)
    [LocallyRingedSpace.IsOpenImmersion f] [LocallyRingedSpace.IsOpenImmersion g]
    (hr : range g.base ⊆ range f.base) :
    LocallyRingedSpace.IsOpenImmersion (LocallyRingedSpace.IsOpenImmersion.lift f g hr) := by
  let : IsIso (pullback.snd f g) :=
    LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset f g hr
  dsimp only [LocallyRingedSpace.IsOpenImmersion.lift]
  infer_instance

private theorem native_inclusion_point {d : ℕ} (O : Opens (ComplexModel d)) :
    ChartedSpace.locallyRingedSpaceMap (Subtype.val : O → ComplexModel d)
      (contMDiff_subtype_val (I := 𝓘(ℂ, ComplexModel d))) ≫
      ambientPointMap d (ComplexModel d) = ambientPointMap d O :=
  (ChartedSpace.locallyRingedSpace_comp (IM := 𝓘(ℂ, ComplexModel d))
    (IN := 𝓘(ℂ, ComplexModel d)) (IP := 𝓘(ℂ, ComplexModel 0))
    contMDiff_subtype_val
    (show ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel 0) ∞
      (fun _ : ComplexModel d => (0 : ComplexModel 0)) from contMDiff_const)).symm

/-- EVERY actual original chart identifies the existing intrinsic regularity
with embedded regularity of its SAME analytic carrier and SAME dimension. -/
theorem intrinsicRegularAtDim_localEmbedding_iff
    (X : SourceReducedComplexSpace) (e : LocalEmbedding X) (c : e.carrier) (d : ℕ) :
    intrinsicRegularAtDim X.obj (e.toPoint c) d ↔
      RegularAtDim (n := e.dim) e.carrier c.val d := by
  constructor
  · rintro ⟨O, i, hi, hip, v, hv⟩
    let : LocallyRingedSpace.IsOpenImmersion i := hi
    let : LocallyRingedSpace.IsOpenImmersion e.map := e.isOpenImmersion
    let j : actualSubspaceLocallyRingedSpace (n := e.dim) e.carrier ⟶ X.obj.left := e.map
    let : LocallyRingedSpace.IsOpenImmersion j := e.isOpenImmersion
    have hjp : j ≫ X.obj.hom = subspacePointMap (n := e.dim) e.carrier := e.overPoint
    let P : Opens O := ⟨i.base ⁻¹' range e.map.base,
      e.isOpenImmersion.base_open.isOpen_range.preimage i.base.hom.continuous⟩
    have hvP : v ∈ P := by
      change i.base v ∈ range e.map.base
      exact ⟨c, hv.symm⟩
    let V : Opens (ComplexModel d) :=
      ⟨(Subtype.val : O → ComplexModel d) '' (P : Set O),
        O.isOpen.isOpenMap_subtype_val _ P.isOpen⟩
    let a := ChartedSpace.locallyRingedSpaceMap (Subtype.val : O → ComplexModel d)
      (contMDiff_subtype_val (I := 𝓘(ℂ, ComplexModel d)))
    let b := ChartedSpace.locallyRingedSpaceMap (Subtype.val : V → ComplexModel d)
      (contMDiff_subtype_val (I := 𝓘(ℂ, ComplexModel d)))
    have hab : range b.base ⊆ range a.base := by
      rintro _ ⟨z, rfl⟩
      obtain ⟨u, _hu, huz⟩ := z.property
      exact ⟨u, huz⟩
    let k := LocallyRingedSpace.IsOpenImmersion.lift a b hab
    let : LocallyRingedSpace.IsOpenImmersion k := openImmersion_lift a b hab
    have hka : k ≫ a = b := LocallyRingedSpace.IsOpenImmersion.lift_fac a b hab
    have hkP (z : V) : k.base z ∈ P := by
      obtain ⟨u, hu, huz⟩ := z.property
      have hkz : (k.base z).val = z.val := congrArg (fun f => f.base z) hka
      have hku : k.base z = u := Subtype.ext (hkz.trans huz.symm)
      exact hku.symm ▸ hu
    have hkp : k ≫ ambientPointMap d O = ambientPointMap d V := by
      rw [← native_inclusion_point O, ← Category.assoc, hka]
      exact native_inclusion_point V
    let g := k ≫ i
    have hgp : g ≫ X.obj.hom = ambientPointMap d V := by
      dsimp only [g]
      rw [Category.assoc, hip, hkp]
    have hge : range g.base ⊆ range e.map.base := by
      rintro _ ⟨z, rfl⟩
      exact hkP z
    let H := LocallyRingedSpace.IsOpenImmersion.lift j g hge
    let : LocallyRingedSpace.IsOpenImmersion H := openImmersion_lift j g hge
    have hHe : H ≫ j = g := LocallyRingedSpace.IsOpenImmersion.lift_fac j g hge
    have hHp : H ≫ subspacePointMap (n := e.dim) e.carrier = ambientPointMap d V := by
      rw [← hjp, ← Category.assoc, hHe, hgp]
    let z : V := ⟨v.val, ⟨v, hvP, rfl⟩⟩
    have hkv : k.base z = v := by
      apply Subtype.ext
      exact congrArg (fun f => f.base z) hka
    have hHc : H.base z = c := by
      apply e.toPoint_injective
      change j.base (H.base z) = j.base c
      have hh := congrArg (fun f => f.base z) hHe
      change j.base (H.base z) = i.base (k.base z) at hh
      rw [hkv] at hh
      exact hh.trans hv
    have hreg := regularAtDim_of_native_manifold_chart H hHp z
    simpa only [hHc] using hreg
  · intro hreg
    obtain ⟨O, i, hi, hip, v, hv⟩ := (intrinsicRegularAtDim_model_iff e.carrier c).mpr hreg
    let : LocallyRingedSpace.IsOpenImmersion i := hi
    let : LocallyRingedSpace.IsOpenImmersion e.map := e.isOpenImmersion
    refine ⟨O, i ≫ e.map, inferInstance, ?_, v, ?_⟩
    · rw [Category.assoc, e.overPoint]
      exact hip
    · change e.map.base (i.base v) = e.map.base c
      rw [hv]

/-- The original intrinsic singular set has the EXACT embedded singular trace
in EVERY local embedding, including unequal ambient dimensions. -/
theorem intrinsicSingularLocus_localEmbedding_preimage
    (X : SourceReducedComplexSpace) (e : LocalEmbedding X) :
    e.toPoint ⁻¹' intrinsicSingularLocus X.obj =
      (Subtype.val : e.carrier → e.ambient) ⁻¹' singularSet (n := e.dim) e.carrier := by
  ext c
  change (¬ ∃ d : ℕ, intrinsicRegularAtDim X.obj (e.toPoint c) d) ↔
    c.val ∈ singularSet (n := e.dim) e.carrier
  rw [mem_singularSet_iff]
  simp only [c.property, true_and, not_exists]
  exact forall_congr' fun d => not_congr (intrinsicRegularAtDim_localEmbedding_iff X e c d)

/-- ONLY the original local-model property internally proves analyticity of
the SAME existing intrinsic singular locus. -/
theorem isAnalyticSubset_intrinsicSingularLocus (X : SourceReducedComplexSpace) :
    X.IsAnalyticSubset (intrinsicSingularLocus X.obj) := by
  intro x
  let e := LocalEmbedding.ofPoint X x
  refine ⟨e, LocalEmbedding.mem_range_ofPoint X x, singularSet (n := e.dim) e.carrier,
    HironakaResolutionSpaceSingular.isComplexAnalyticSubset_singularSet e.analytic, ?_⟩
  exact intrinsicSingularLocus_localEmbedding_preimage X e

/-- Original smoothness is precisely emptiness of the actual intrinsic
singular complement, with the native varying-dimension chart definition. -/
theorem isSmooth_iff_intrinsicSingularLocus_eq_empty (X : SourceReducedComplexSpace) :
    X.IsSmooth ↔ intrinsicSingularLocus X.obj = ∅ := by
  constructor
  · intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hx (h x)
  · intro h x
    by_contra hn
    have hx : x ∈ intrinsicSingularLocus X.obj := hn
    simp only [h, mem_empty_iff_false] at hx

/-- Compactness is a consequence only when the ORIGINAL space is compact. -/
theorem isCompact_intrinsicSingularLocus (X : SourceReducedComplexSpace)
    [CompactSpace X.obj.left] : IsCompact (intrinsicSingularLocus X.obj) :=
  (HironakaIntrinsicComplexAnalyticRegularLocus.isClosed_intrinsicSingularLocus X.obj).isCompact

theorem intrinsicSingularLocus_nonempty_of_not_isSmooth (X : SourceReducedComplexSpace)
    (h : ¬ X.IsSmooth) : (intrinsicSingularLocus X.obj).Nonempty := by
  apply Set.nonempty_iff_ne_empty.mpr
  exact fun he => h ((isSmooth_iff_intrinsicSingularLocus_eq_empty X).mpr he)

private theorem exists_original_regular_mem_nhds (X : SourceReducedComplexSpace)
    (x : X.obj.left) {W : Set X.obj.left} (hW : W ∈ nhds x) :
    ∃ y ∈ W, ∃ d : ℕ, intrinsicRegularAtDim X.obj y d := by
  let e := LocalEmbedding.ofPoint X x
  obtain ⟨c, hcx⟩ := LocalEmbedding.mem_range_ofPoint X x
  have hW' : W ∈ nhds (e.toPoint c) := by rw [hcx]; exact hW
  have hpre : e.toPoint ⁻¹' W ∈ nhds c :=
    e.isOpenEmbedding_toPoint.continuous.continuousAt.preimage_mem_nhds hW'
  obtain ⟨Q, hQsub, hQ, hcQ⟩ := mem_nhds_iff.mp hpre
  obtain ⟨T, hT, hTQ⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hQ
  have hcT : c.val ∈ T := by
    change c ∈ (Subtype.val : e.carrier → e.ambient) ⁻¹' T
    rw [hTQ]
    exact hcQ
  obtain ⟨y, hyT, d, hreg⟩ := RegularLocusDense.exists_regularAtDim_mem_nhds e.analytic c.property
    (hT.mem_nhds hcT)
  let z : e.carrier := ⟨y, hreg.2.1⟩
  have hzQ : z ∈ Q := by rw [← hTQ]; exact hyT
  exact ⟨e.toPoint z, hQsub hzQ, d,
    (intrinsicRegularAtDim_localEmbedding_iff X e z d).mpr hreg⟩

/-- Density for the ORIGINAL paracompact category, without imposing global
second countability or a supplied regular-locus dictionary. -/
theorem dense_intrinsicRegularLocus (X : SourceReducedComplexSpace) :
    Dense (intrinsicRegularLocus X.obj) := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro x
  rw [mem_closure_iff_nhds]
  intro W hW
  obtain ⟨y, hy, d, hd⟩ := exists_original_regular_mem_nhds X x hW
  exact ⟨y, hy, d, hd⟩

/-- The SAME actual intrinsic singular locus has empty interior. -/
theorem interior_intrinsicSingularLocus_eq_empty (X : SourceReducedComplexSpace) :
    interior (intrinsicSingularLocus X.obj) = ∅ := by
  apply interior_eq_empty_iff_dense_compl.mpr
  simpa only [intrinsicSingularLocus, compl_compl] using dense_intrinsicRegularLocus X

end
end Hironaka.Analytic.Unibranch.OriginalIntrinsicSingularLocus
