import Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningOpenReduction
import Hironaka.Analytic.Unibranch.HironakaG10ChowSingularTowerDomination
import Hironaka.Analytic.Unibranch.ComplexSpaceLocalEmbedding
import Hironaka.Resolution.HironakaG10ChowFlatModelOpen

/-!
# Flat morphisms of complex spaces are open

Blueprint `hironaka-g10-chowside-flat-open-native.tex` (nodes `g10c:flat-open`,
`g10c:chow-manifold-one-input`).

The named classical input `FlatMorphismsAreOpen` of `HironakaG10ChowFlatBimeromorphicIso`
(Douady 1966) is PROVED here (`flatMorphismsAreOpen`): a morphism `p : Y ⟶ X` of reduced complex
spaces whose stalk maps are all flat is an open map.

Proof: near `y` choose local embeddings `(U_Y, C) → Y` (with image in a prescribed neighbourhood
of `y`) and `(U_X, D) → X` at `p y`.  The model-level factorization theorems
(`exists_actual_model_chart_factor`, `exists_actualSubspaceMap_local_holomorphic_lift`) write
`p` near `y` as the model morphism of a holomorphic map `f` with `f(C) ⊆ D`.  Its stalk map is
the stalk map of `p` up to the stalk isomorphisms of open immersions, hence flat, and
`HironakaG10ChowFlatModelOpen.eventually_mem_image_of_stalk_flat` shows that `f(C)` contains a
neighbourhood of `f c` in `D`; the open embedding `D → X` carries it to a neighbourhood of `p y`
inside `p(N)`.

Consequences:
* goal G10a from Hironaka's flattening theorem alone
  (`hironakaChowLemmaManifold_of_hironakaFlattening`);
* a flat proper bimeromorphic morphism is a homeomorphism, so its fibres are single points
  (`isHomeomorph_of_isProperBimeromorphic_of_flat`, `subsingleton_fibre_of_isProperBimeromorphic_of_flat`;
  no named input);
* `chow:flat-bimeromorphic-iso` and the singular-base tower domination now use only the finite
  mapping theorem, resp. flattening and the finite mapping theorem
  (`isIso_of_isProperBimeromorphic_of_flat_of_finiteMapping`,
  `exists_nativeBlowupTower_domination_of_flattening_of_finiteMapping`).

Sorry-free.
-/

set_option autoImplicit false

open Set Filter Topology TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10ChowFlatOpen

open Hironaka
  Hironaka.HironakaReducedComplexAnalyticSpaces
  Hironaka.HironakaActualAnalyticSubspace
  Hironaka.HironakaActualAnalyticSubspaceMaps
  Hironaka.HironakaActualAnalyticSubspaceOpenRestriction
  Hironaka.HironakaActualAnalyticSubspaceIntrinsicLifting
  Hironaka.HironakaReducedComplexAnalyticMorphismCharts
  Hironaka.HironakaChowLemma
  HironakaG10ChowFlatBimeromorphicIso HironakaG10ChowFlatteningReduction
  HironakaG10ChowFlatteningOpenReduction HironakaG10ChowNativeIsoCriterion
  HironakaG10ChowSingularTowerDomination HironakaG10ChowTowerDomination SourceReducedComplexSpace

noncomputable section

/-! ### Flat stalk maps of locally ringed spaces -/

section StalkFlat

variable {X Y Z : LocallyRingedSpace}

/-- Stalk flatness along a composite. -/
theorem flat_stalkMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    (hg : (g.stalkMap (f.base x)).hom.Flat) (hf : (f.stalkMap x).hom.Flat) :
    ((f ≫ g).stalkMap x).hom.Flat := by
  rw [LocallyRingedSpace.stalkMap_comp]
  exact RingHom.Flat.comp hg hf

/-- An isomorphism of stalks is flat. -/
theorem flat_of_isIso {A B : CommRingCat} (φ : A ⟶ B) [IsIso φ] : φ.hom.Flat :=
  RingHom.Flat.of_bijective ((ConcreteCategory.isIso_iff_bijective φ).mp inferInstance)

/-- Stalk flatness is a property of the morphism. -/
theorem flat_stalkMap_of_eq {f g : X ⟶ Y} (h : f = g) (x : X)
    (hg : (g.stalkMap x).hom.Flat) : (f.stalkMap x).hom.Flat := by
  subst h
  exact hg

/-- Cancelling a morphism with isomorphic stalk maps. -/
theorem flat_stalkMap_of_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) (hiso : IsIso (g.stalkMap (f.base x)))
    (h : ((f ≫ g).stalkMap x).hom.Flat) : (f.stalkMap x).hom.Flat := by
  rw [LocallyRingedSpace.stalkMap_comp] at h
  have heq : f.stalkMap x = inv (g.stalkMap (f.base x)) ≫
      (g.stalkMap (f.base x) ≫ f.stalkMap x) := by
    rw [IsIso.inv_hom_id_assoc]
  rw [heq]
  exact RingHom.Flat.comp (flat_of_isIso _) h

end StalkFlat

/-! ### Flat morphisms are open -/

/-- **Openness at a point.**  For a flat morphism `p : Y ⟶ X` of reduced complex spaces, the
image of every neighbourhood of `y` is a neighbourhood of `p y`. -/
theorem image_mem_nhds_of_isFlatMorphism {X Y : SourceReducedComplexSpace} (p : Y ⟶ X)
    (hp : IsFlatMorphism p) (y : Y.obj.left) {N : Set Y.obj.left} (hN : N ∈ 𝓝 y) :
    p.hom.left.base '' N ∈ 𝓝 (p.hom.left.base y) := by
  classical
  set x := p.hom.left.base y with hxdef
  -- a local embedding of `X` at `x`
  let eX := LocalEmbedding.ofPoint X x
  have : LocallyRingedSpace.IsOpenImmersion eX.map := eX.isOpenImmersion
  obtain ⟨d, hd⟩ := LocalEmbedding.mem_range_ofPoint X x
  -- a local embedding of `Y` at `y` with image in `N` and over the image of `eX`
  have hN' : IsOpen (interior N ∩ p.hom.left.base ⁻¹' range eX.toPoint) :=
    isOpen_interior.inter (eX.isOpen_range_toPoint.preimage p.hom.left.base.hom.continuous)
  have hyN' : y ∈ interior N ∩ p.hom.left.base ⁻¹' range eX.toPoint :=
    ⟨mem_interior_iff_mem_nhds.mpr hN, d, hd⟩
  obtain ⟨eY, ⟨c, hc⟩, heYN, -⟩ := LocalEmbedding.exists_domain y hN' hyN'
  have : LocallyRingedSpace.IsOpenImmersion eY.map := eY.isOpenImmersion
  -- the model morphism of `p`
  have hF : (eY.map ≫ p.hom.left) ≫ X.obj.hom = (modelOver eY.ambient eY.carrier).hom := by
    rw [Category.assoc, Over.w p.hom]
    exact eY.overPoint
  have hFc : (eY.map ≫ p.hom.left).base c ∈ range eX.map.base := by
    refine ⟨d, ?_⟩
    change eX.toPoint d = p.hom.left.base (eY.map.base c)
    rw [hd]
    change x = p.hom.left.base (eY.toPoint c)
    rw [hc]
  obtain ⟨T, hcT, H, hHp, hHfac⟩ := exists_actual_model_chart_factor (n := eY.dim) X.obj
    (eY.map ≫ p.hom.left) hF eX.map eX.overPoint c hFc
  let c₁ : ((Subtype.val : T → eY.ambient) ⁻¹' eY.carrier) := ⟨⟨c.val, hcT⟩, c.property⟩
  obtain ⟨O, hcO, f, hf, hCD, hfH⟩ := exists_actualSubspaceMap_local_holomorphic_lift H hHp c₁
  let C₂ : Set O := (Subtype.val : O → T) ⁻¹' ((Subtype.val : T → eY.ambient) ⁻¹' eY.carrier)
  let c₂ : C₂ := ⟨⟨c₁.val, hcO⟩, c₁.property⟩
  -- flatness of the model stalk map
  have hiY := LocallyRingedSpace.IsOpenImmersion.stalk_iso eY.map
    ((actualOpenSubspaceMap (n := eY.dim) eY.carrier T).base c₁)
  have hiX := LocallyRingedSpace.IsOpenImmersion.stalk_iso eX.map (H.base c₁)
  have hF1 : ((eY.map ≫ p.hom.left).stalkMap
      ((actualOpenSubspaceMap (n := eY.dim) eY.carrier T).base c₁)).hom.Flat :=
    flat_stalkMap_comp eY.map p.hom.left _ (hp _) (flat_of_isIso _)
  have hF2 : ((actualOpenSubspaceMap (n := eY.dim) eY.carrier T ≫ (eY.map ≫ p.hom.left)).stalkMap
      c₁).hom.Flat :=
    flat_stalkMap_comp (actualOpenSubspaceMap (n := eY.dim) eY.carrier T) (eY.map ≫ p.hom.left) c₁
      hF1 (flat_of_isIso _)
  have hH1 : ((H ≫ eX.map).stalkMap c₁).hom.Flat := flat_stalkMap_of_eq hHfac c₁ hF2
  have hH2 : (H.stalkMap c₁).hom.Flat := flat_stalkMap_of_comp H eX.map c₁ hiX hH1
  have hA1 : ((actualOpenSubspaceMap (n := eY.dim) ((Subtype.val : T → eY.ambient) ⁻¹' eY.carrier) O ≫
      H).stalkMap c₂).hom.Flat :=
    flat_stalkMap_comp (actualOpenSubspaceMap (n := eY.dim)
      ((Subtype.val : T → eY.ambient) ⁻¹' eY.carrier) O) H c₂ hH2 (flat_of_isIso _)
  have hflatA : ((actualSubspaceMap hf hCD).stalkMap c₂).hom.Flat := flat_stalkMap_of_eq hfH c₂ hA1
  -- base points
  have hb1 : ∀ z : C₂, (actualSubspaceMap hf hCD).base z =
      H.base ((actualOpenSubspaceMap (n := eY.dim)
        ((Subtype.val : T → eY.ambient) ⁻¹' eY.carrier) O).base z) := by
    intro z
    have h := congrArg (fun k => k.base z) hfH
    simp only [LocallyRingedSpace.comp_base, TopCat.comp_app] at h
    exact h
  have hb2 : ∀ w : ((Subtype.val : T → eY.ambient) ⁻¹' eY.carrier), eX.map.base (H.base w) =
      p.hom.left.base (eY.map.base ((actualOpenSubspaceMap (n := eY.dim) eY.carrier T).base w)) := by
    intro w
    have h := congrArg (fun k => k.base w) hHfac
    simp only [LocallyRingedSpace.comp_base, TopCat.comp_app] at h
    exact h
  have hbase : ∀ z : C₂, eX.map.base ((actualSubspaceMap hf hCD).base z) =
      p.hom.left.base (eY.map.base ((actualOpenSubspaceMap (n := eY.dim) eY.carrier T).base
        ((actualOpenSubspaceMap (n := eY.dim)
          ((Subtype.val : T → eY.ambient) ⁻¹' eY.carrier) O).base z))) := by
    intro z
    rw [hb1, hb2]
  have hRN : ∀ w : eY.carrier, eY.map.base w ∈ N := by
    intro w
    have : eY.map.base w ∈ range eY.toPoint := ⟨w, rfl⟩
    exact interior_subset (heYN this).1
  -- the model is analytic
  have hC₁ : IsComplexAnalyticSubset (n := eY.dim)
      ((Subtype.val : T → eY.ambient) ⁻¹' eY.carrier) :=
    Hironaka.AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val
      eY.analytic T
  have hC₂ : IsComplexAnalyticSubset (n := eY.dim) C₂ :=
    Hironaka.AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hC₁ O
  -- the model-level openness
  have hev :=
    Hironaka.HironakaG10ChowFlatModelOpen.eventually_mem_image_of_stalk_flat
      hf hC₂ hCD c₂ hflatA (W := univ) univ_mem
  -- transport to `X`
  have hD : {w : eX.carrier | w.val ∈ f '' (C₂ ∩ univ)} ∈
      𝓝 ((actualSubspaceMap hf hCD).base c₂) := by
    have h1 : (Subtype.val : eX.carrier → eX.ambient) ⁻¹'
        {w | w ∈ eX.carrier → w ∈ f '' (C₂ ∩ univ)} ∈ 𝓝 ((actualSubspaceMap hf hCD).base c₂) :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds hev
    filter_upwards [h1] with w hw
    exact hw w.property
  have himg := eX.isOpenEmbedding_toPoint.image_mem_nhds.mpr hD
  have hpt : eX.toPoint ((actualSubspaceMap hf hCD).base c₂) = x := by
    change eX.map.base ((actualSubspaceMap hf hCD).base c₂) = x
    rw [hbase]
    change p.hom.left.base (eY.toPoint c) = x
    rw [hc]
  rw [hpt] at himg
  refine mem_of_superset himg ?_
  rintro _ ⟨w, ⟨c', hc', hfc'⟩, rfl⟩
  let z : C₂ := ⟨c', hc'.1⟩
  refine ⟨eY.map.base ((actualOpenSubspaceMap (n := eY.dim) eY.carrier T).base
    ((actualOpenSubspaceMap (n := eY.dim) ((Subtype.val : T → eY.ambient) ⁻¹' eY.carrier) O).base z)),
    hRN _, ?_⟩
  rw [← hbase z]
  change eX.map.base ((actualSubspaceMap hf hCD).base z) = eX.map.base w
  congr 1
  exact Subtype.ext hfc'

/-- **Flat morphisms of reduced complex spaces are open** (the named input of
`HironakaG10ChowFlatBimeromorphicIso`, Douady 1966, now proved). -/
theorem flatMorphismsAreOpen : FlatMorphismsAreOpen := by
  intro X Y p hp
  refine IsOpenMap.of_nhds_le fun y => ?_
  intro s hs
  exact mem_of_superset (image_mem_nhds_of_isFlatMorphism p hp y hs) (image_preimage_subset _ _)

/-- **Goal G10a from Hironaka's flattening theorem alone.**  Hironaka's Chow lemma for compact
complex manifolds follows from the flattening statement `HironakaFlattening`; the openness of
flat maps is now proved. -/
theorem hironakaChowLemmaManifold_of_hironakaFlattening (H₀ : HironakaFlattening) :
    HironakaChowLemmaManifold.{0} :=
  hironakaChowLemmaManifold_of_flattening_of_open H₀ flatMorphismsAreOpen

/-! ### Consequences -/

/-- **A flat proper bimeromorphic morphism is a homeomorphism** (no named input). -/
theorem isHomeomorph_of_isProperBimeromorphic_of_flat {X Y : SourceReducedComplexSpace}
    {p : Y ⟶ X} (hp : IsProperBimeromorphic p) (hflat : IsFlatMorphism p) :
    IsHomeomorph p.hom.left.base :=
  isHomeomorph_of_isProperBimeromorphic_of_isOpenMap hp (flatMorphismsAreOpen X Y p hflat)

/-- **The fibres of a flat proper bimeromorphic morphism are single points**: in particular they
are finite (zero-dimensional), with the dense generic isomorphism locus retained. -/
theorem subsingleton_fibre_of_isProperBimeromorphic_of_flat {X Y : SourceReducedComplexSpace}
    {p : Y ⟶ X} (hp : IsProperBimeromorphic p) (hflat : IsFlatMorphism p) (x : X.obj.left) :
    (p.hom.left.base ⁻¹' {x}).Subsingleton := fun _ ha _ hb =>
  (isHomeomorph_of_isProperBimeromorphic_of_flat hp hflat).injective (ha.trans hb.symm)

/-- `chow:flat-bimeromorphic-iso` with the finite mapping theorem as the only named input. -/
theorem isIso_of_isProperBimeromorphic_of_flat_of_finiteMapping (H₂ : FiniteMappingTheorem)
    {X Y : SourceReducedComplexSpace} {p : Y ⟶ X} (hp : IsProperBimeromorphic p)
    (hflat : IsFlatMorphism p) : IsIso p :=
  isIso_of_isProperBimeromorphic_of_flat flatMorphismsAreOpen H₂ hp hflat

/-- Domination of a proper bimeromorphic morphism to a compact reduced space by a tower of native
blowups, from flattening and the finite mapping theorem only. -/
theorem exists_nativeBlowupTower_domination_of_flattening_of_finiteMapping
    (H₀ : HironakaFlattening) (H₂ : FiniteMappingTheorem) {X Y : SourceReducedComplexSpace}
    (hX : CompactSpace X.obj.left) {f : Y ⟶ X} (hf : IsProperBimeromorphic f) :
    ∃ (X' : SourceReducedComplexSpace) (σ : X' ⟶ X) (β : X' ⟶ Y),
      IsNativeBlowupTower X X' σ ∧ β ≫ f = σ :=
  exists_nativeBlowupTower_domination_of_flattening H₀ flatMorphismsAreOpen H₂ hX hf

end

end Hironaka.Analytic.Unibranch.HironakaG10ChowFlatOpen
