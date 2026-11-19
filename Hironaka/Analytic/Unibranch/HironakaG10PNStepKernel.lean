import Hironaka.Analytic.Unibranch.HironakaG10PNFibreKernel
import Hironaka.Analytic.Unibranch.HironakaG10ChowFibreSurjective
import Hironaka.Analytic.Unibranch.HironakaG10ChowPairInjective
import Hironaka.Resolution.HironakaG10PNBlowupKernel

/-!
# One-step coherence of the fibres of the strict transform (lane G10P, run 0080 r5)

The last input `StepKernelCoherent` of the coherence of the fibre kernels of the flattening chain
(`HironakaG10PNFibreKernel.isLocallyFinitelyGenerated_fibreKernel`) is proved for every stage of the
algorithm (`stage_stepKernelCoherent`): for every point `x'` of the next base, the ideal in `Y` of the
fibre of the strict transform `Y' = Bl_{f*B} Y` over `x'` is locally finitely generated.  Hence G10C's
hypothesis `hfg` holds unconditionally (`isLocallyFinitelyGenerated_fibreKernel_stage`) and the
flattening reduction loses one input (`exists_flattening_of_closed_of_fibreDecreases`).

Route (no direct-image theorem):
* generic transport: `exists_sub_mem_pullFamily_of_openSquare` (fibre-algebra surjectivity through a
  chart), `exists_sub_mem_kerFamily_inclusion` (to the ambient manifold),
  `isLocallyFinitelyGeneratedAt_kerFamily_of_not_mem` (away from the image of the fibre, by
  properness), `isLocallyFinitelyGenerated_kerFamily_of_openImmersionOn` (fibres where the strict
  transform is an open immersion);
* `isLocallyFinitelyGenerated_kerFamily_model`: for the glued geometric blowup of a finite-type ideal
  (arbitrary local model data) and a coherent family `K` supported on a closed set over the nonunit
  locus, on which the projection is injective with surjective fibre algebras, the kernel family is
  coherent: in a chart it is the restriction of the kernel family of the manifold blowup, coherent
  by `HironakaG10PNBlowupKernel.isLocallyFinitelyGeneratedAt_kerFamily_blowup`;
* the strict transform: `K = 𝔪_{x'} 𝒪_{Y'}`, pair-injectivity (G10C's `strict_pairInjective`), N6
  (G10C's `strict_fibreSurjective`); over the unit locus `q` is an open immersion on the fibre.
-/

set_option autoImplicit false

open Set TopologicalSpace Topology CategoryTheory Opposite AlgebraicGeometry IsLocalRing
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10PNStepKernel

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps HironakaReducedComplexAnalyticSpaces
  HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf HironakaNativePulledIdealFiniteType
  SourceReducedComplexSpace EmbeddedIdealBlowupNonunitLocus BlowupStrictSubmanifold
  HironakaG10ChowOneStepStrictTransform HironakaG10ChowFlatteningDriver HironakaG10ChowFibreChain
  HironakaG10ChowFibreAlgebra HironakaG10PNIdealFamily HironakaG10PNPointIdeal
  HironakaG10PNKernelFamily HironakaG10PNKernelSquare HironakaG10PNIdealNoetherModel
  HironakaG10PNFibreKernel

noncomputable section

/-! ### Generic transport -/

section Generic

universe u

variable {X Y X' Y' : LocallyRingedSpace.{u}}

/-- **Fibre-algebra surjectivity through a chart.**  For a square `k ≫ q = Q ≫ J` with `k` an open
immersion, surjectivity modulo `K` at `k z` gives surjectivity modulo the restricted family at `z`. -/
theorem exists_sub_mem_pullFamily_of_openSquare (q : Y' ⟶ Y) (J : X ⟶ Y) (k : X' ⟶ Y')
    (Q : X' ⟶ X) (hsq : k ≫ q = Q ≫ J) [LocallyRingedSpace.IsOpenImmersion k]
    (K : ∀ y : Y', Ideal (Y'.presheaf.stalk y)) (z : X')
    (h : ∀ β : Y'.presheaf.stalk (k.base z), ∃ a : Y.presheaf.stalk (q.base (k.base z)),
      β - (q.stalkMap (k.base z)).hom a ∈ K (k.base z)) :
    ∀ β₀ : X'.presheaf.stalk z, ∃ a₀ : X.presheaf.stalk (Q.base z),
      β₀ - (Q.stalkMap z).hom a₀ ∈ pullFamily k K z := by
  intro β₀
  obtain ⟨β, rfl⟩ := (stalkMap_bijective_of_openImmersion k z).2 β₀
  obtain ⟨a, ha⟩ := h β
  obtain ⟨sp, hsp⟩ : ∃ sp, (k ≫ q).stalkMap z = sp ≫ (Q ≫ J).stalkMap z :=
    ⟨_, LocallyRingedSpace.stalkMap_congr_hom (k ≫ q) (Q ≫ J) hsq z⟩
  refine ⟨(J.stalkMap (Q.base z)).hom (sp.hom a), ?_⟩
  have h1 := congrArg (fun φ => CommRingCat.Hom.hom φ a) (LocallyRingedSpace.stalkMap_comp k q z)
  have h2 := congrArg (fun φ => CommRingCat.Hom.hom φ a) hsp
  have h3 := congrArg (fun φ => CommRingCat.Hom.hom φ (sp.hom a))
    (LocallyRingedSpace.stalkMap_comp Q J z)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h1 h2 h3
  have e : (k.stalkMap z).hom ((q.stalkMap (k.base z)).hom a) =
      (Q.stalkMap z).hom ((J.stalkMap (Q.base z)).hom (sp.hom a)) :=
    h1.symm.trans (h2.trans h3)
  rw [← e, ← map_sub]
  exact Ideal.mem_map_of_mem _ ha

/-- **Away from the image of the support, the kernel family is the unit ideal** near the point
(the projection is a closed map). -/
theorem isLocallyFinitelyGeneratedAt_kerFamily_of_not_mem (q : Y' ⟶ Y)
    (hq : IsClosedMap q.base) (K : ∀ y : Y', Ideal (Y'.presheaf.stalk y))
    (hK : IsLocallyFinitelyGenerated Y' K) (y : Y)
    (hy : ¬ ∃ y' : Y', K y' ≠ ⊤ ∧ q.base y' = y) :
    IsLocallyFinitelyGeneratedAt Y (kerFamily q K) y := by
  have hF : IsClosed {y' : Y' | K y' ≠ ⊤} := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro y' hy'
    have hy'' : K y' = ⊤ := not_not.mp hy'
    obtain ⟨O, hO, hO'⟩ := exists_nhds_eq_top_of_isLocallyFinitelyGenerated hK y' hy''
    exact ⟨O, fun z hz => not_not.mpr (hO' z hz), O.isOpen, hO⟩
  have hZ : IsClosed (q.base '' {y' : Y' | K y' ≠ ⊤}) := hq _ hF
  refine isLocallyFinitelyGeneratedAt_of_eq_top ⟨_, hZ.isOpen_compl⟩
    (fun ⟨y', h1, h2⟩ => hy ⟨y', h1, h2⟩) fun x hx => kerFamily_eq_top fun y' hy' => ?_
  by_contra h
  exact hx ⟨y', h, hy'⟩

/-- **Where the projection is an open immersion on the support**, the kernel family is coherent. -/
theorem isLocallyFinitelyGenerated_kerFamily_of_openImmersionOn {V : LocallyRingedSpace.{u}}
    (q : Y' ⟶ Y) (hq : IsClosedMap q.base) (K : ∀ y : Y', Ideal (Y'.presheaf.stalk y))
    (hK : IsLocallyFinitelyGenerated Y' K) (j : V ⟶ Y') (hjo : LocallyRingedSpace.IsOpenImmersion j)
    (hjq : LocallyRingedSpace.IsOpenImmersion (j ≫ q))
    (hj : ∀ y', K y' ≠ ⊤ → y' ∈ Set.range j.base) :
    IsLocallyFinitelyGenerated Y (kerFamily q K) := by
  intro y
  by_cases hy : ∃ y' : Y', K y' ≠ ⊤ ∧ q.base y' = y
  · obtain ⟨y', hy'K, rfl⟩ := hy
    obtain ⟨v, rfl⟩ := hj y' hy'K
    have h := pullFamily_kerFamily_of_openSquare q (j ≫ q) j (𝟙 V) (Category.id_comp _).symm K
      (fun y'' h _ => hj y'' h)
    rw [kerFamily_id] at h
    have h2 : IsLocallyFinitelyGeneratedAt Y (kerFamily q K) ((j ≫ q).base v) := by
      apply IsLocallyFinitelyGeneratedAt.of_openImmersion (j ≫ q)
      rw [h]
      exact IsLocallyFinitelyGeneratedAt.pull j (hK (j.base v))
    exact h2
  · exact isLocallyFinitelyGeneratedAt_kerFamily_of_not_mem q hq K hK y hy

end Generic

/-! ### Embedded models -/

section Ambient

variable {n : ℕ} {M Z : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

/-- The geometric strict transform of an analytic set is analytic. -/
theorem geoStrictTransform_analytic {C W : Set M} {π : Z → M} (hπ : IsBlowupAlong n C π)
    (hW : IsComplexAnalyticSubset (n := n) W) :
    IsComplexAnalyticSubset (n := n) (geoStrictTransform π C W) := by
  have hC := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hπ.1
  simpa only [geoStrictTransform, preimage_sdiff] using
    ClosureDifferenceAnalytic.isComplexAnalyticSubset_closure_diff
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hπ.contMDiff hW)
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hπ.contMDiff hC)

/-- **Fibre-algebra surjectivity to the ambient manifolds**: for a holomorphic `π` mapping `S` into
`W`, surjectivity of the subspace map modulo `K` at `s` gives surjectivity of `π` modulo the push
`kerFamily ι_S K` at `s`. -/
theorem exists_sub_mem_kerFamily_inclusion {π : Z → M}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π) {S : Set Z} {W : Set M}
    (hSW : ∀ x ∈ S, π x ∈ W)
    (K : ∀ s : actualSubspaceLocallyRingedSpace (n := n) S,
      Ideal ((actualSubspaceLocallyRingedSpace (n := n) S).presheaf.stalk s)) (s : S)
    (h : ∀ β : (actualSubspaceLocallyRingedSpace (n := n) S).presheaf.stalk s,
      ∃ a : (actualSubspaceLocallyRingedSpace (n := n) W).presheaf.stalk
          ((actualSubspaceMap hπ hSW).base s),
        β - ((actualSubspaceMap hπ hSW).stalkMap s).hom a ∈ K s) :
    ∀ β : (ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) Z).presheaf.stalk s.val,
      ∃ a : (ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M).presheaf.stalk (π s.val),
        β - ((ChartedSpace.locallyRingedSpaceMap π hπ).stalkMap s.val).hom a ∈
          kerFamily (actualSubspaceInclusion (n := n) S) K s.val := by
  intro β
  have hk := kerFamily_apply_of_injective (actualSubspaceInclusion (n := n) S)
    Subtype.val_injective K s
  obtain ⟨aW, haW⟩ := h (((actualSubspaceInclusion (n := n) S).stalkMap s).hom β)
  obtain ⟨a, ha⟩ := actualSubspaceInclusionRingedHom_stalk_surjective (n := n) W
    ((actualSubspaceMap hπ hSW).base s) aW
  refine ⟨a, ?_⟩
  change _ ∈ kerFamily (actualSubspaceInclusion (n := n) S) K
    ((actualSubspaceInclusion (n := n) S).base s)
  rw [hk, Ideal.mem_comap, map_sub]
  have sq := ConcreteCategory.congr_hom (actualSubspaceRingedMap_stalk_square hπ hSW s) a
  simp only [ConcreteCategory.comp_apply] at sq
  have e : ((actualSubspaceInclusion (n := n) S).stalkMap s).hom
      (((ChartedSpace.locallyRingedSpaceMap π hπ).stalkMap s.val).hom a) =
        ((actualSubspaceMap hπ hSW).stalkMap s).hom aW := by
    rw [← ha]
    exact sq.symm
  rw [e]
  exact haW

end Ambient

/-! ### The glued geometric blowup of a finite-type ideal -/

section Model

variable {Y : SourceReducedComplexSpace}
  (𝔍 : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  (b' : 𝔍 ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  {ι : Type} {n : ι → ℕ} {M Z : ι → Type} [∀ j, TopologicalSpace (M j)]
  [∀ j, TopologicalSpace (Z j)]
  [∀ j, ChartedSpace (ComplexModel (n j)) (M j)] [∀ j, IsComplexManifold (n j) (M j)]
  [∀ j, ChartedSpace (ComplexModel (n j)) (Z j)] [∀ j, IsComplexManifold (n j) (Z j)]
  {C W : ∀ j, Set (M j)} {π : ∀ j, Z j → M j}
  (hW : ∀ j, IsComplexAnalyticSubset (n := n j) (W j))
  (hπ : ∀ j, IsBlowupAlong (n j) (C j) (π j))
  (J : ∀ j, ofClosedAnalytic (W j) (hW j) ⟶ Y)
  [hJopen : ∀ j, LocallyRingedSpace.IsOpenImmersion (J j).hom.left]
  (hJ : ∀ j (y : W j),
    Ideal.map ((actualSubspaceInclusion (n := n j) (W j)).stalkMap y).hom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n j) (C j)) y.val) =
        nativePulledIdealStalkIdeal (J j).hom.left 𝔍 b' y)
  (hcover : ∀ y : Y.obj.left, ∃ (j : ι) (w : W j), (J j).hom.left.base w = y)

include hJ hJopen in
/-- **Coherence of the image ideal of a fibre of a glued geometric blowup.**  Let `K` be a coherent
ideal family on the glued geometric blowup of a finite-type ideal (arbitrary local model data) whose
support lies over the nonunit locus, such that the projection is injective on the support and the
fibre algebras are quotients of those of the base modulo `K`.  Then the kernel family of `K` along
the projection is coherent. -/
theorem isLocallyFinitelyGenerated_kerFamily_model
    (K : ∀ y' : (EmbeddedGeometricIdealOriginalObject.sourceObject hW hπ J 𝔍 b' hJ hcover).obj.left,
      Ideal ((EmbeddedGeometricIdealOriginalObject.sourceObject hW hπ J 𝔍 b' hJ
        hcover).obj.left.presheaf.stalk y'))
    (hK : IsLocallyFinitelyGenerated _ K)
    (hinj : ∀ a c, K a ≠ ⊤ → K c ≠ ⊤ →
      (EmbeddedGeometricIdealOriginalObject.projectionMorphism hW hπ J 𝔍 b' hJ
        hcover).hom.left.base a =
      (EmbeddedGeometricIdealOriginalObject.projectionMorphism hW hπ J 𝔍 b' hJ
        hcover).hom.left.base c → a = c)
    (hnu : ∀ y', K y' ≠ ⊤ →
      (EmbeddedGeometricIdealOriginalObject.projectionMorphism hW hπ J 𝔍 b' hJ
        hcover).hom.left.base y' ∈ nonunitLocus 𝔍 b')
    (hsurj : ∀ y', K y' ≠ ⊤ →
      ∀ β : (EmbeddedGeometricIdealOriginalObject.sourceObject hW hπ J 𝔍 b' hJ
        hcover).obj.left.presheaf.stalk y',
      ∃ a : Y.obj.left.presheaf.stalk ((EmbeddedGeometricIdealOriginalObject.projectionMorphism hW
          hπ J 𝔍 b' hJ hcover).hom.left.base y'),
        β - ((EmbeddedGeometricIdealOriginalObject.projectionMorphism hW hπ J 𝔍 b' hJ
          hcover).hom.left.stalkMap y').hom a ∈ K y') :
    IsLocallyFinitelyGenerated Y.obj.left
      (kerFamily (EmbeddedGeometricIdealOriginalObject.projectionMorphism hW hπ J 𝔍 b' hJ
        hcover).hom.left K) := by
  classical
  set qg := EmbeddedGeometricIdealObjectGluing.projection hW hπ J 𝔍 b' hJ with hqg
  have hclosed : IsClosedMap qg.base :=
    (EmbeddedGeometricIdealOriginalObject.projection_isProperMap hW hπ J 𝔍 b' hJ
      hcover).isClosedMap
  intro y
  by_cases hy : ∃ y', K y' ≠ ⊤ ∧ qg.base y' = y
  swap
  · exact isLocallyFinitelyGeneratedAt_kerFamily_of_not_mem qg hclosed K hK y hy
  obtain ⟨y', hy'K, rfl⟩ := hy
  obtain ⟨j, z₁, rfl⟩ :=
    EmbeddedGeometricIdealObjectGluing.inclusion_jointly_surjective hW hπ J 𝔍 b' hJ y'
  obtain ⟨z, rfl⟩ : ∃ z : geoStrictTransform (π j) (C j) (W j), z = z₁ := ⟨z₁, rfl⟩
  set k : actualSubspaceLocallyRingedSpace (n := n j) (geoStrictTransform (π j) (C j) (W j)) ⟶
      EmbeddedGeometricIdealObjectGluing.glued hW hπ J 𝔍 b' hJ :=
    EmbeddedGeometricIdealObjectGluing.inclusion hW hπ J 𝔍 b' hJ j with hk
  set gp := EmbeddedGeometricBlowup.geometricProjection (hπ j) (hW j).isClosed with hgp
  have hsq : k ≫ qg = gp ≫ (J j).hom.left :=
    EmbeddedGeometricIdealObjectGluing.inclusion_projection hW hπ J 𝔍 b' hJ j
  have hpt : qg.base (k.base z) = (J j).hom.left.base (gp.base z) :=
    congrArg (fun H => H.base z) hsq
  have hko : LocallyRingedSpace.IsOpenImmersion k :=
    EmbeddedGeometricIdealObjectGluing.inclusion_isOpenImmersion hW hπ J 𝔍 b' hJ j
  -- the point is over the centre
  have hC : π j z.val ∈ C j :=
    (chart_mem_nonunitLocus 𝔍 b' hW hπ J hJ j (gp.base z)).mpr (by rw [← hpt]; exact hnu _ hy'K)
  -- the ambient family on the blowup manifold
  have hKS : IsLocallyFinitelyGenerated _ (pullFamily k K) := isLocallyFinitelyGenerated_pull k hK
  have h𝒜 : IsLocallyFinitelyGenerated _
      (kerFamily (actualSubspaceInclusion (n := n j) (geoStrictTransform (π j) (C j) (W j)))
        (pullFamily k K)) := by
    rw [kerFamily_actualSubspaceInclusion]
    exact pushFamily_isLocallyFinitelyGenerated (geoStrictTransform_analytic (hπ j) (hW j)) _ hKS
  have hFc : IsClosed {y'' | K y'' ≠ ⊤} := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro y'' hy''
    have hy3 : K y'' = ⊤ := not_not.mp hy''
    obtain ⟨O, hO, hO'⟩ := exists_nhds_eq_top_of_isLocallyFinitelyGenerated hK y'' hy3
    exact ⟨O, fun x hx => not_not.mpr (hO' x hx), O.isOpen, hO⟩
  -- localization near `z` by properness and injectivity on the support
  have hloc : ∀ V : Set (Z j), IsOpen V → z.val ∈ V → ∃ U : Set (M j), IsOpen U ∧ π j z.val ∈ U ∧
      ∀ z' : Z j, kerFamily (actualSubspaceInclusion (n := n j)
        (geoStrictTransform (π j) (C j) (W j))) (pullFamily k K) z' ≠ ⊤ → π j z' ∈ U → z' ∈ V := by
    intro V hV hzV
    set VS := k.base '' {s | s.val ∈ V} with hVSdef
    have hVS : IsOpen VS := hko.base_open.isOpenMap _ (hV.preimage continuous_subtype_val)
    set T := qg.base '' ({y'' | K y'' ≠ ⊤} \ VS) with hTdef
    have hT : IsClosed T := hclosed _ (hFc.sdiff hVS)
    have hyT : qg.base (k.base z) ∉ T := by
      rintro ⟨a, ⟨haK, haV⟩, ha⟩
      have := hinj a (k.base z) haK hy'K ha
      exact haV (this ▸ ⟨z, hzV, rfl⟩)
    have hU₀ : IsOpen ((J j).hom.left.base ⁻¹' Tᶜ : Set (W j)) :=
      hT.isOpen_compl.preimage (J j).hom.left.base.hom.continuous
    obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.mp hU₀
    refine ⟨U, hU, ?_, ?_⟩
    · have h1 : gp.base z ∈ (J j).hom.left.base ⁻¹' Tᶜ := by
        show (J j).hom.left.base (gp.base z) ∈ Tᶜ
        rw [← hpt]
        exact hyT
      exact (Set.ext_iff.mp hUeq (gp.base z)).mpr h1
    · intro z' hz'𝒜 hz'U
      by_cases hz'S : z' ∈ geoStrictTransform (π j) (C j) (W j)
      · let s : geoStrictTransform (π j) (C j) (W j) := ⟨z', hz'S⟩
        have hKs : K (k.base s) ≠ ⊤ := by
          intro htop
          apply hz'𝒜
          have h1 := kerFamily_apply_of_injective
            (actualSubspaceInclusion (n := n j) (geoStrictTransform (π j) (C j) (W j)))
            Subtype.val_injective (pullFamily k K) s
          change kerFamily _ _ ((actualSubspaceInclusion (n := n j)
            (geoStrictTransform (π j) (C j) (W j))).base s) = ⊤
          have h4 : pullFamily k K s = ⊤ := by
            unfold pullFamily
            rw [htop, Ideal.map_top]
          rw [h1, h4, Ideal.comap_top]
        have hgs₀ : gp.base s ∈ ((↑) : W j → M j) ⁻¹' U := hz'U
        have hgs : gp.base s ∈ (J j).hom.left.base ⁻¹' Tᶜ := (Set.ext_iff.mp hUeq (gp.base s)).mp hgs₀
        have hqs : qg.base (k.base s) ∈ Tᶜ := by
          have h2 : qg.base (k.base s) = (J j).hom.left.base (gp.base s) :=
            congrArg (fun H => H.base s) hsq
          rw [h2]
          exact hgs
        by_contra hz'V
        apply hqs
        refine ⟨k.base s, ⟨hKs, ?_⟩, rfl⟩
        rintro ⟨s', hs'V, hs'⟩
        have h3 := hko.base_open.injective hs'
        have h4 : s.val ∈ V := h3 ▸ hs'V
        exact hz'V h4
      · exact absurd (kerFamily_of_not_mem_range _ _ (by
          rintro ⟨s, rfl⟩
          exact hz'S s.property)) hz'𝒜
  -- surjective fibre algebras on the ambient blowup at `z`
  have hsurjS := exists_sub_mem_pullFamily_of_openSquare qg (J j).hom.left k gp hsq K z
    (hsurj _ hy'K)
  have hsurjZ := exists_sub_mem_kerFamily_inclusion (hπ j).contMDiff
    (fun _ hy => geoStrictTransform_subset_preimage (hπ j).contMDiff.continuous (hW j).isClosed hy)
    (pullFamily k K) z hsurjS
  -- the manifold-level theorem
  have hB := HironakaG10PNBlowupKernel.isLocallyFinitelyGeneratedAt_kerFamily_blowup (hπ j) _ h𝒜
    z.val hC hloc hsurjZ
  have hpull := IsLocallyFinitelyGeneratedAt.pull (actualSubspaceInclusion (n := n j) (W j))
    (y := gp.base z) hB
  rw [pullFamily_kerFamily_of_closedSquare
    (actualSubspaceInclusion (n := n j) (geoStrictTransform (π j) (C j) (W j)))
    (ChartedSpace.locallyRingedSpaceMap (π j) (hπ j).contMDiff) gp
    (actualSubspaceInclusion (n := n j) (W j))
    (actualSubspaceMap_inclusion (hπ j).contMDiff _) Subtype.val_injective
    (fun w => actualSubspaceInclusionRingedHom_stalk_surjective (n := n j) (W j) w)
    (pullFamily k K)] at hpull
  have hEq := pullFamily_kerFamily_of_openSquare qg (J j).hom.left k gp hsq K (fun y'' _ h =>
    (Set.ext_iff.mp (EmbeddedGeometricIdealObjectGluing.preimage_chart_range hW hπ J 𝔍 b' hJ j)
      y'').mp h)
  have hfin := IsLocallyFinitelyGeneratedAt.of_openImmersion (J j).hom.left (y := gp.base z)
    (by rw [hEq]; exact hpull)
  rw [← hpt] at hfin
  exact hfin

end Model

/-! ### The one-step strict transform -/

section Strict

variable {X Y : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf))
  [B.IsFiniteType] (f : Y ⟶ X)

local instance pulled_isFiniteType_pn : (nativePulledIdealModule f.hom.left B b).IsFiniteType :=
  nativePulledIdealModule_isFiniteType f.hom.left B b

/-- The model theorem for the strict transform `q : Y' = Bl_{f*B} Y ⟶ Y`. -/
theorem isLocallyFinitelyGenerated_kerFamily_strictQ
    (K : ∀ y' : (strictSource B b f).obj.left,
      Ideal ((strictSource B b f).obj.left.presheaf.stalk y'))
    (hK : IsLocallyFinitelyGenerated _ K)
    (hinj : ∀ a c, K a ≠ ⊤ → K c ≠ ⊤ →
      (strictQ B b f).hom.left.base a = (strictQ B b f).hom.left.base c → a = c)
    (hnu : ∀ y', K y' ≠ ⊤ → (strictQ B b f).hom.left.base y' ∈
      nonunitLocus (nativePulledIdealModule f.hom.left B b)
        (nativePulledIdealInclusion f.hom.left B b))
    (hsurj : ∀ y', K y' ≠ ⊤ → ∀ β : (strictSource B b f).obj.left.presheaf.stalk y',
      ∃ a : Y.obj.left.presheaf.stalk ((strictQ B b f).hom.left.base y'),
        β - ((strictQ B b f).hom.left.stalkMap y').hom a ∈ K y') :
    IsLocallyFinitelyGenerated Y.obj.left (kerFamily (strictQ B b f).hom.left K) := by
  revert K
  unfold strictQ strictSource OriginalFiniteIdealGeometricBlowup.projectionMorphism
    OriginalFiniteIdealGeometricBlowup.sourceObject
  intro K hK hinj hnu hsurj
  exact isLocallyFinitelyGenerated_kerFamily_model _ _ _ _ _ _ _ K hK hinj hnu hsurj

end Strict

/-! ### Every stage of the algorithm -/

section Driver

variable (rule : ∀ s : Stage, AdmissibleCentre s.f)

/-- **One-step coherence holds for every stage**: for every point `x'` of the next base, the ideal
in `Y` of the fibre of the strict transform over `x'` is locally finitely generated. -/
theorem stage_stepKernelCoherent (s : Stage) : StepKernelCoherent rule s := by
  intro x'
  have hT1 := t1Space (Stage.next rule s).X
  have hK : IsLocallyFinitelyGenerated _ (pullFamily (Stage.next rule s).f.hom.left
      (pointFamily (Stage.next rule s).X.obj.left x')) :=
    isLocallyFinitelyGenerated_fibreFamily (HironakaG10PNSourceNoether.hasAnalyticModelCharts _) _ _
  have hne : ∀ y', pullFamily (Stage.next rule s).f.hom.left
      (pointFamily (Stage.next rule s).X.obj.left x') y' ≠ ⊤ →
        (Stage.next rule s).f.hom.left.base y' = x' := by
    intro y' h
    by_contra h'
    exact h (pullFamily_pointFamily_of_ne _ h')
  have hsurj : ∀ y', pullFamily (Stage.next rule s).f.hom.left
      (pointFamily (Stage.next rule s).X.obj.left x') y' ≠ ⊤ →
      ∀ β : (Stage.next rule s).Y.obj.left.presheaf.stalk y',
        ∃ a : s.Y.obj.left.presheaf.stalk ((Stage.q rule s).hom.left.base y'),
          β - ((Stage.q rule s).hom.left.stalkMap y').hom a ∈ pullFamily
            (Stage.next rule s).f.hom.left (pointFamily (Stage.next rule s).X.obj.left x') y' := by
    intro y' hy' β
    obtain ⟨a, ha⟩ := HironakaG10ChowFibreSurjective.stage_stepFibreSurjective rule s y' β
    refine ⟨a, ?_⟩
    rw [← hne y' hy', pullFamily_pointFamily_self]
    exact ha
  have hinj : ∀ a c, pullFamily (Stage.next rule s).f.hom.left
      (pointFamily (Stage.next rule s).X.obj.left x') a ≠ ⊤ →
      pullFamily (Stage.next rule s).f.hom.left
        (pointFamily (Stage.next rule s).X.obj.left x') c ≠ ⊤ →
      (Stage.q rule s).hom.left.base a = (Stage.q rule s).hom.left.base c → a = c :=
    fun a c ha hc hq => HironakaG10ChowPairInjective.stage_pairInjective rule s a c
      ((hne a ha).trans (hne c hc).symm) hq
  have hclosed : IsClosedMap (Stage.q rule s).hom.left.base := (stepQ_isProperMap rule s).isClosedMap
  let c := rule s
  let _ := c.finiteType
  by_cases hE : (Stage.σ rule s).hom.left.base x' ∈ nonunitLocus c.B c.b
  · -- over the centre: the chart theorem
    refine isLocallyFinitelyGenerated_kerFamily_strictQ c.B c.b s.f _ hK hinj ?_ hsurj
    intro y' hy'
    by_contra h
    apply (mem_pulledUnitLocus_iff c.B c.b s.f _).mp h
    have hp : (strictP c.B c.b c.dense s.f).hom.left.base y' = x' := hne y' hy'
    rw [← strictP_comp_apply c.B c.b c.dense s.f y', hp]
    exact hE
  · -- over the unit locus: `q` is an open immersion near the fibre
    obtain ⟨V, jV, hjV, hrange, hjVQ⟩ := strict_openImmersionOn c.B c.b c.dense s.f
    refine isLocallyFinitelyGenerated_kerFamily_of_openImmersionOn _ hclosed _ hK jV hjV hjVQ ?_
    intro y' hy'
    have hp : (strictP c.B c.b c.dense s.f).hom.left.base y' = x' := hne y' hy'
    have h5 : y' ∈ (strictP c.B c.b c.dense s.f).hom.left.base ⁻¹'
        (stepExcep c.B c.b c.dense)ᶜ := by
      show (stepProj c.B c.b c.dense).hom.left.base
        ((strictP c.B c.b c.dense s.f).hom.left.base y') ∉ nonunitLocus c.B c.b
      rw [hp]
      exact hE
    exact (Set.ext_iff.mp hrange y').mpr h5

variable (s₀ : Stage)

/-- **`hfg` holds unconditionally**: every fibre kernel of the flattening chain is locally finitely
generated (coherence of the ideal of the image in `Y_0` of every fibre of every stage). -/
theorem isLocallyFinitelyGenerated_fibreKernel_stage :
    ∀ (z : ∀ n, (stage rule s₀ n).X.obj.left) n,
      IsLocallyFinitelyGenerated (stage rule s₀ 0).Y.obj.left (fibreKernel rule s₀ z n) :=
  isLocallyFinitelyGenerated_fibreKernel
    (fun n => HironakaG10ChowFibreSurjective.stage_stepFibreSurjective rule (stage rule s₀ n))
    (fun n => stage_stepKernelCoherent rule (stage rule s₀ n))

/-- **Flattening from closed non-flat images and strict fibre decrease**: for compact `X` and
proper `f`, the conclusion of `HironakaFlattening` for `f` follows from (4.1) `hclosed` and
Lemma 1.18 under (RR) `hdec` only (N6, the Noether property and the coherence of the fibre kernels
are discharged). -/
theorem exists_flattening_of_closed_of_fibreDecreases (hX : CompactSpace s₀.X.obj.left)
    (hf : IsProperMap s₀.f.hom.left.base)
    (hclosed : ∀ n, IsClosed (HironakaG10ChowStrictFlatLocus.nonflatImage (stage rule s₀ n).f))
    (hdec : ∀ n, ∀ x' ∈ HironakaG10ChowStrictFlatLocus.nonflatImage (stage rule s₀ (n + 1)).f,
      StepFibreDecreasesAt rule (stage rule s₀ n) x') :
    ∃ (X' : SourceReducedComplexSpace) (σ : X' ⟶ s₀.X) (E : Set X'.obj.left),
      HironakaG10ChowTowerDomination.IsNativeBlowupTower s₀.X X' σ ∧ IsClosed E ∧
        interior E = ∅ ∧ HironakaG10ChowFlatteningReduction.IsOpenImmersionOn σ Eᶜ ∧
      ∃ (Y' : SourceReducedComplexSpace) (p : Y' ⟶ X') (q : Y' ⟶ s₀.Y),
        HironakaG10ChowFlatteningReduction.IsStrictTransform s₀.f σ E p q ∧
          HironakaG10ChowFlatBimeromorphicIso.IsFlatMorphism p :=
  exists_flattening_of_fibreDecreases_of_stepKernel hX hf hclosed
    (fun n => HironakaG10ChowFibreSurjective.stage_stepFibreSurjective rule (stage rule s₀ n))
    (fun n => stage_stepKernelCoherent rule (stage rule s₀ n)) hdec

end Driver

end

end Hironaka.Analytic.Unibranch.HironakaG10PNStepKernel
