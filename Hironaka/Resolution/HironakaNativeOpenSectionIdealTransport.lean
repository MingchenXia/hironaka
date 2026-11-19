import Hironaka.Resolution.HironakaActualAnalyticSubspaceOpenRestriction

/-!
# Native open-section scalars and whole vanishing ideals

The actual open inclusion constructs all section and stalk comparisons.
Every subset is allowed. No ambient extension, ideal-comparison certificate,
prime condition or support-module epimorphism is assumed.
Blueprint FIRST: `hironaka-g10-native-open-section-ideal-transport.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaNativeOpenSectionIdealTransport

noncomputable section

open Hironaka.HolomorphicIdealSheaves
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaSmoothCentreRealDomainActualIdealPresheaf
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceOpenRestriction
  HironakaActualVanishingIntrinsicHSTransport

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private abbrev openInclusion (D : Opens M) :
    ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) D ⟶
      ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M :=
  ChartedSpace.locallyRingedSpaceMap (IM := 𝓘(ℂ, ComplexModel n))
    (IN := 𝓘(ℂ, ComplexModel n)) (Subtype.val : D → M) contMDiff_subtype_val

/-- The genuine image-open under the original holomorphic open inclusion. -/
def actualOpenImage (D : Opens M) (V : Opens D) : Opens M :=
  (TopologicalSpace.Opens.isOpenEmbedding (X := TopCat.of M) D).functor.obj V

omit [IsComplexManifold n M] in
private theorem image_preimage (D : Opens M) (V : Opens D) :
    (Opens.map (openInclusion (n := n) D).base).obj (actualOpenImage D V) = V := by
  ext x
  change (∃ a ∈ V, a.val = x.val) ↔ x ∈ V
  constructor
  · rintro ⟨a, ha, hax⟩
    have h : a = x := Subtype.ext hax
    exact h ▸ ha
  · intro hx
    exact ⟨x, hx, rfl⟩

omit [IsComplexManifold n M] in
private theorem section_cast_apply {P Q : Opens M} (h : P = Q)
    (s : actualComplexSection (n := n) P) (x : Q) :
    (actualComplexStructureSheaf (n := n) M).presheaf.map (eqToHom h.symm).op s x =
      s ⟨x.val, h.symm ▸ x.property⟩ := by
  subst Q
  rfl

/-- Pullback on the actual image-open, with its genuine inverse. -/
def actualOpenSectionRingEquiv (D : Opens M) (V : Opens D) :
    actualComplexSection (n := n) (actualOpenImage D V) ≃+*
      actualComplexSection (n := n) V := by
  let f := openInclusion (n := n) D
  have h : IsIso (f.c.app (op (actualOpenImage D V))) := by
    exact (inferInstance : LocallyRingedSpace.IsOpenImmersion f).c_iso V
  exact ((asIso (f.c.app (op (actualOpenImage D V)))) ≪≫
    (actualComplexStructureSheaf (n := n) D).presheaf.mapIso
      (eqToIso (image_preimage (n := n) D V).symm).op).commRingCatIsoToRingEquiv

omit [IsComplexManifold n M] in
/-- EVERY original section retains its value at the actual corresponding point. -/
theorem actualOpenSectionRingEquiv_apply (D : Opens M) (V : Opens D)
    (s : actualComplexSection (n := n) (actualOpenImage D V)) (y : V) :
    actualOpenSectionRingEquiv (n := n) D V s y =
      s ⟨y.val.val, ⟨y.val, y.property, rfl⟩⟩ := by
  change (actualComplexStructureSheaf (n := n) D).presheaf.map
    (eqToHom (image_preimage (n := n) D V).symm).op
      ((openInclusion (n := n) D).c.app (op (actualOpenImage D V)) s) y = _
  exact section_cast_apply (n := n) (M := D) (image_preimage (n := n) D V)
    ((openInclusion (n := n) D).c.app (op (actualOpenImage D V)) s) y

omit [IsComplexManifold n M] in
/-- The actual inverse section equivalence has the inverse point formula. -/
theorem actualOpenSectionRingEquiv_symm_apply (D : Opens M) (V : Opens D)
    (s : actualComplexSection (n := n) V) (y : V) :
    (actualOpenSectionRingEquiv (n := n) D V).symm s
        ⟨y.val.val, ⟨y.val, y.property, rfl⟩⟩ = s y := by
  have h := actualOpenSectionRingEquiv_apply (n := n) D V
    ((actualOpenSectionRingEquiv (n := n) D V).symm s) y
  exact h.symm.trans (congrArg (fun t => t y)
    ((actualOpenSectionRingEquiv (n := n) D V).apply_symm_apply s))

omit [IsComplexManifold n M] in
/-- Every actual original open restriction commutes with this section comparison. -/
theorem actualOpenSectionRingEquiv_naturality (D : Opens M) (V T : Opens D)
    (hTV : T ≤ V) (s : actualComplexSection (n := n) (actualOpenImage D V)) :
    (actualComplexStructureSheaf (n := n) D).presheaf.map (homOfLE hTV).op
        (actualOpenSectionRingEquiv (n := n) D V s) =
      actualOpenSectionRingEquiv (n := n) D T
        ((actualComplexStructureSheaf (n := n) M).presheaf.map
          (((TopologicalSpace.Opens.isOpenEmbedding (X := TopCat.of M) D).functor.map
            (homOfLE hTV))).op s) := by
  apply Subtype.ext
  funext y
  change actualOpenSectionRingEquiv (n := n) D V s ⟨y.val, hTV y.property⟩ = _
  exact (actualOpenSectionRingEquiv_apply (n := n) D V s ⟨y.val, hTV y.property⟩).trans
    (actualOpenSectionRingEquiv_apply (n := n) D T
      ((actualComplexStructureSheaf (n := n) M).presheaf.map
        ((TopologicalSpace.Opens.isOpenEmbedding (X := TopCat.of M) D).functor.map
          (homOfLE hTV)).op s) y).symm

/-- The SAME original restricted ring sheaf, on the actual open carrier. -/
abbrev actualLiteralStructureSheaf (D : Opens M) : (TopCat.of D).Sheaf CommRingCat :=
  ((ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M).restrict
    (TopologicalSpace.Opens.isOpenEmbedding (X := TopCat.of M) D)).𝒪

/-- All section comparisons form one genuine same-site scalar-ring isomorphism. -/
def actualLiteralStructureRingIso (D : Opens M) :
    actualLiteralStructureSheaf (n := n) D ≅ actualComplexStructureSheaf (n := n) D := by
  apply (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology (TopCat.of D))
    CommRingCat).preimageIso
  refine NatIso.ofComponents (fun V =>
    (actualOpenSectionRingEquiv (n := n) D V.unop).toCommRingCatIso) ?_
  intro V T k
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  exact (actualOpenSectionRingEquiv_naturality (n := n) D V.unop T.unop
    (leOfHom k.unop) s).symm

omit [IsComplexManifold n M] in
/-- The exact scalar-ring component is the independently constructed section map. -/
theorem actualLiteralStructureRingIso_app (D : Opens M) (V : Opens D)
    (s : actualComplexSection (n := n) (actualOpenImage D V)) :
    (actualLiteralStructureRingIso (n := n) D).hom.hom.app (op V) s =
      actualOpenSectionRingEquiv (n := n) D V s := rfl

/-- The genuine native open inclusion supplies the entire stalk equivalence. -/
def actualOpenStalkRingEquiv (D : Opens M) (y : D) :
    actualComplexStructureStalk (n := n) y.val ≃+*
      actualComplexStructureStalk (n := n) y :=
  (asIso ((openInclusion (n := n) D).stalkMap y)).commRingCatIsoToRingEquiv

omit [IsComplexManifold n M] in
/-- Every actual section numerator retains its original germ under the native map. -/
theorem actualOpenStalkRingEquiv_germ (D : Opens M) (V : Opens D)
    (y : D) (hy : y ∈ V) (s : actualComplexSection (n := n) (actualOpenImage D V)) :
    actualOpenStalkRingEquiv (n := n) D y
        ((actualComplexStructureSheaf (n := n) M).presheaf.germ
          (actualOpenImage D V) y.val ⟨y, hy, rfl⟩ s) =
      (actualComplexStructureSheaf (n := n) D).presheaf.germ V y hy
        (actualOpenSectionRingEquiv (n := n) D V s) := by
  exact (LocallyRingedSpace.stalkMap_germ_apply (openInclusion (n := n) D)
    (actualOpenImage D V) y ⟨y, hy, rfl⟩ s).trans
      ((actualComplexStructureSheaf (n := n) D).presheaf.germ_res_apply
        (eqToHom (image_preimage (n := n) D V).symm) y hy
        ((openInclusion (n := n) D).c.app (op (actualOpenImage D V)) s)).symm

/-- The stalk map of the genuine same-site scalar comparison. -/
def actualLiteralStructureStalkEquiv (D : Opens M) (y : D) :
    ↑((actualLiteralStructureSheaf (n := n) D).presheaf.stalk y) ≃+*
      actualComplexStructureStalk (n := n) (M := D) y :=
  ((TopCat.Presheaf.stalkFunctor (X := TopCat.of D) CommRingCat y).mapIso
    ((sheafToPresheaf (Opens.grothendieckTopology (TopCat.of D)) CommRingCat).mapIso
      (actualLiteralStructureRingIso (n := n) D))).commRingCatIsoToRingEquiv

private abbrev originalRestriction (D : Opens M) :=
  (ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M).ofRestrict
    (TopologicalSpace.Opens.isOpenEmbedding (X := TopCat.of M) D)

/-- The original literal restriction map itself, with its native inverse on stalks. -/
def actualOriginalRestrictionStalkEquiv (D : Opens M) (y : D) :
    actualComplexStructureStalk (n := n) y.val ≃+*
      ↑((actualLiteralStructureSheaf (n := n) D).presheaf.stalk y) := by
  let X := PresheafedSpace.mk (TopCat.of M)
    (actualComplexStructureSheaf (n := n) M).presheaf
  let i : TopCat.of D ⟶ TopCat.of M :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have hi : Topology.IsOpenEmbedding i.hom := D.isOpenEmbedding'
  exact (PresheafedSpace.restrictStalkIso X (f := i) hi y).symm.commRingCatIsoToRingEquiv

omit [IsComplexManifold n M] in
/-- The constructed inverse is exactly the SAME original restriction stalk map. -/
theorem actualOriginalRestrictionStalkEquiv_apply (D : Opens M) (y : D)
    (r : actualComplexStructureStalk (n := n) y.val) :
    actualOriginalRestrictionStalkEquiv (n := n) D y r =
      (originalRestriction (n := n) D).stalkMap y r := by
  let X := PresheafedSpace.mk (TopCat.of M)
    (actualComplexStructureSheaf (n := n) M).presheaf
  let i : TopCat.of D ⟶ TopCat.of M :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have hi : Topology.IsOpenEmbedding i.hom := D.isOpenEmbedding'
  exact ConcreteCategory.congr_hom
    (PresheafedSpace.restrictStalkIso_inv_eq_ofRestrict X (f := i) hi y) r

omit [IsComplexManifold n M] in
private theorem section_original_square (D : Opens M) (O : Opens M)
    (s : actualComplexSection (n := n) O) :
    (actualLiteralStructureRingIso (n := n) D).hom.hom.app
        (op ((Opens.map (openInclusion (n := n) D).base).obj O))
          ((originalRestriction (n := n) D).c.app (op O) s) =
      (openInclusion (n := n) D).c.app (op O) s := by
  let T := (Opens.map (openInclusion (n := n) D).base).obj O
  let s₀ : actualComplexSection (n := n) (actualOpenImage D T) :=
    (originalRestriction (n := n) D).c.app (op O) s
  apply (actualLiteralStructureRingIso_app (n := n) D T s₀).trans
  apply Subtype.ext
  funext y
  exact actualOpenSectionRingEquiv_apply (n := n) D
    ((Opens.map (openInclusion (n := n) D).base).obj O)
      ((originalRestriction (n := n) D).c.app (op O) s) y

omit [IsComplexManifold n M] in
/-- Typed eta-star composed with the ORIGINAL restriction gamma is exactly beta. -/
theorem actualLiteralStructureStalkEquiv_original (D : Opens M) (y : D)
    (r : actualComplexStructureStalk (n := n) y.val) :
    actualLiteralStructureStalkEquiv (n := n) D y
        (actualOriginalRestrictionStalkEquiv (n := n) D y r) =
      actualOpenStalkRingEquiv (n := n) D y r := by
  obtain ⟨O, hy, s, rfl⟩ := (actualComplexStructureSheaf (n := n) M).presheaf.exists_germ_eq r
  rw [actualOriginalRestrictionStalkEquiv_apply]
  change actualLiteralStructureStalkEquiv (n := n) D y
    ((originalRestriction (n := n) D).stalkMap y
      ((actualComplexStructureSheaf (n := n) M).presheaf.germ O y.val hy s)) =
    (openInclusion (n := n) D).stalkMap y
      ((actualComplexStructureSheaf (n := n) M).presheaf.germ O y.val hy s)
  let T := (Opens.map (openInclusion (n := n) D).base).obj O
  calc
    _ = actualLiteralStructureStalkEquiv (n := n) D y
        ((actualLiteralStructureSheaf (n := n) D).presheaf.germ T y hy
          ((originalRestriction (n := n) D).c.app (op O) s)) :=
      congrArg (actualLiteralStructureStalkEquiv (n := n) D y)
        (LocallyRingedSpace.stalkMap_germ_apply (originalRestriction (n := n) D) O y hy s)
    _ = (actualComplexStructureSheaf (n := n) D).presheaf.germ T y hy
        ((actualLiteralStructureRingIso (n := n) D).hom.hom.app (op T)
          ((originalRestriction (n := n) D).c.app (op O) s)) :=
      TopCat.Presheaf.stalkFunctor_map_germ_apply T y hy
        (actualLiteralStructureRingIso (n := n) D).hom.hom _
    _ = (actualComplexStructureSheaf (n := n) D).presheaf.germ T y hy
        ((openInclusion (n := n) D).c.app (op O) s) :=
      congrArg ((actualComplexStructureSheaf (n := n) D).presheaf.germ T y hy)
        (section_original_square (n := n) D O s)
    _ = _ := (LocallyRingedSpace.stalkMap_germ_apply
      (openInclusion (n := n) D) O y hy s).symm

omit [IsComplexManifold n M] in
/-- The FULL original ambient section-map square, on every open at once. -/
theorem actualLiteralStructureRingIso_ambient (D : Opens M) :
    (originalRestriction (n := n) D).c ≫
        (Opens.map (openInclusion (n := n) D).base).op.whiskerLeft
          (actualLiteralStructureRingIso (n := n) D).hom.hom =
      (openInclusion (n := n) D).c := by
  apply NatTrans.ext
  funext O
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  exact section_original_square (n := n) D O.unop s

/-- The full identity-base presheafed map supplied by the inverse scalar comparison. -/
def actualLiteralComparisonPresheafHom (D : Opens M) :
    PresheafedSpace.mk (TopCat.of D) (actualLiteralStructureSheaf (n := n) D).presheaf ⟶
      PresheafedSpace.mk (TopCat.of D) (actualComplexStructureSheaf (n := n) D).presheaf :=
  ⟨𝟙 (TopCat.of D), (actualLiteralStructureRingIso (n := n) D).inv.hom⟩

omit [IsComplexManifold n M] in
/-- The scalar comparison is EXACTLY the genuine native manifold restriction map. -/
theorem actualLiteralStructureRingIso_native (D : Opens M) :
    actualLiteralComparisonPresheafHom (n := n) D =
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace).map
        (ChartedSpace.restrictLocallyRingedSpaceIso (IM := 𝓘(ℂ, ComplexModel n)) D).hom := by
  let F := LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace
  let i := openInclusion (n := n) D
  let j := originalRestriction (n := n) D
  let a := (ChartedSpace.restrictLocallyRingedSpaceIso (IM := 𝓘(ℂ, ComplexModel n)) D).hom
  let c : F.obj ((ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M).restrict
      (TopologicalSpace.Opens.isOpenEmbedding (X := TopCat.of M) D)) ⟶
      F.obj (ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) D) :=
    actualLiteralComparisonPresheafHom (n := n) D
  change c = F.map a
  let : PresheafedSpace.IsOpenImmersion (F.map i) := by
    change PresheafedSpace.IsOpenImmersion (openInclusion (n := n) D).toHom
    infer_instance
  apply (cancel_mono (F.map i)).mp
  have ha : F.map a ≫ F.map i = F.map j := by
    exact (F.map_comp a i).symm.trans
      (F.congr_map (LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ (by rfl)))
  rw [ha]
  have hb : (c ≫ F.map i).base = (F.map j).base := rfl
  refine PresheafedSpace.ext (c ≫ F.map i) (F.map j) hb ?_
  apply NatTrans.ext
  funext O
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  let T := (Opens.map (openInclusion (n := n) D).base).obj O.unop
  change (actualLiteralStructureRingIso (n := n) D).inv.hom.app (op T)
      ((openInclusion (n := n) D).c.app O s) =
    (originalRestriction (n := n) D).c.app O s
  apply (actualOpenSectionRingEquiv (n := n) D T).injective
  have he : (actualLiteralStructureRingIso (n := n) D).hom.hom.app (op T)
      ((actualLiteralStructureRingIso (n := n) D).inv.hom.app (op T)
        ((openInclusion (n := n) D).c.app O s)) =
        (openInclusion (n := n) D).c.app O s := by
    exact ConcreteCategory.congr_hom
      (congrArg (fun f => f.hom.app (op T))
        (actualLiteralStructureRingIso (n := n) D).inv_hom_id) _
  exact he.trans (section_original_square (n := n) D O.unop s).symm

/-- The ENTIRE vanishing section ideal is transported for ANY subset. -/
theorem map_actualOpenSectionIdeal (D : Opens M) (V : Opens D) (W : Set M) :
    Ideal.map (actualOpenSectionRingEquiv (n := n) D V).toRingHom
      (actualSectionIdeal (vanishingIdeal (n := n) W) (actualOpenImage D V)) =
        actualSectionIdeal (vanishingIdeal (n := n) ((Subtype.val : D → M) ⁻¹' W)) V := by
  have hm (s : actualComplexSection (n := n) (actualOpenImage D V)) :
      s ∈ actualSectionIdeal (vanishingIdeal (n := n) W) (actualOpenImage D V) ↔
        actualOpenSectionRingEquiv (n := n) D V s ∈
          actualSectionIdeal (vanishingIdeal (n := n) ((Subtype.val : D → M) ⁻¹' W)) V := by
    rw [actualSectionIdeal_vanishing_iff, actualSectionIdeal_vanishing_iff]
    constructor
    · intro hs y hy hyW
      rw [actualOpenSectionRingEquiv_apply]
      exact hs y.val ⟨y, hy, rfl⟩ hyW
    · intro hs x hx hxW
      obtain ⟨y, hy, hxy⟩ := hx
      change y.val = x at hxy
      subst x
      have hval := hs y hy hxW
      rw [actualOpenSectionRingEquiv_apply] at hval
      exact hval
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro s hs
    exact (hm s).mp hs
  · intro s hs
    obtain ⟨t, rfl⟩ := (actualOpenSectionRingEquiv (n := n) D V).surjective s
    exact Ideal.mem_map_of_mem _ ((hm t).mpr hs)

/-- The native original stalk map carries the ENTIRE vanishing ideal, for ANY subset. -/
theorem map_actualOpenWholeStalkIdeal (D : Opens M) (W : Set M) (y : D) :
    Ideal.map (actualOpenStalkRingEquiv (n := n) D y).toRingHom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) y.val) =
        actualWholeSheafStalkIdeal
          (vanishingIdeal (n := n) ((Subtype.val : D → M) ⁻¹' W)) y := by
  have hβ (r : actualComplexStructureStalk (n := n) y.val) :
      actualStalkChartEquiv (n := n) y (actualOpenStalkRingEquiv (n := n) D y r) =
        actualStalkChartEquiv (n := n) y.val r := by
    exact (actualNativeStalk_chart_pullback (f := (Subtype.val : D → M))
      contMDiff_subtype_val y r).trans
        (DFunLike.congr_fun (HironakaActualOpenIntrinsicHS.actualHolomorphicGermPullback_val D y)
          (actualStalkChartEquiv (n := n) y.val r))
  have hcomp : (actualOpenStalkRingEquiv (n := n) D y).toRingHom.comp
      (actualStalkChartEquiv (n := n) y.val).symm.toRingHom =
        (actualStalkChartEquiv (n := n) y).symm.toRingHom := by
    apply RingHom.ext
    intro r
    apply (actualStalkChartEquiv (n := n) y).injective
    exact (hβ _).trans (((actualStalkChartEquiv (n := n) y.val).apply_symm_apply r).trans
      ((actualStalkChartEquiv (n := n) y).apply_symm_apply r).symm)
  rw [actualWholeSheafStalkIdeal_eq_map_chart (vanishingIdeal (n := n) W) y.val,
    Ideal.map_map, hcomp]
  rw [← wholeChartStalkIdeal_vanishing_actual_open (n := n) D W y]
  exact (actualWholeSheafStalkIdeal_eq_map_chart
    (vanishingIdeal (n := n) ((Subtype.val : D → M) ⁻¹' W)) y).symm

end
end Hironaka.HironakaNativeOpenSectionIdealTransport
