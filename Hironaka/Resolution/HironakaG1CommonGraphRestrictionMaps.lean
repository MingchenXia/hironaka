import Hironaka.Resolution.HironakaActualNormalBlockCoordinateDictionary
import Hironaka.Resolution.HironakaActualIntrinsicIsoPairedWindows
import Hironaka.Resolution.HironakaBaseChange
import Hironaka.Resolution.HironakaG1FiniteSourceWeakClassGraphLift

/-! # The two actual ambient restrictions to a common coordinate graph -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1CommonGraphRestrictionMaps

noncomputable section

open HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualCentreJointJets HironakaRelativeNormalIdeal
  HironakaActualNormalBlockCoordinateDictionary HironakaActualIteratedRelativeNormalHistory
  HironakaActualLocalCommonGraphModel HironakaActualIntrinsicIsoPairedWindows
  HironakaReducedComplexAnalyticSpaces HironakaG1NormalGraphFlags
  HironakaG1FiniteSourceWeakClassGraphLift HironakaG1IteratedProperNormalNativeState
  HironakaBaseChange

variable {a b : ℕ} {U A : Opens (ComplexModel a)} {V B : Opens (ComplexModel b)}

private theorem common_le_first (hAU : A ≤ U) : commonDomain A B ≤ blockOpen U b :=
  fun _ hz => hAU hz.1

/-- The common ambient open in the first original block order. -/
def commonGraphFirstRestriction (hAU : A ≤ U) : commonDomain A B → blockOpen U b :=
  Opens.inclusion (common_le_first hAU)

/-- The common ambient open in the second original block order. -/
def commonGraphSecondRestriction (hBV : B ≤ V) : commonDomain A B → blockOpen V a :=
  fun z => ⟨blockSwap a b z.val, by
    change tangentProjection b a (blockSwap a b z.val) ∈ V
    rw [blockSwap_first]
    exact hBV z.property.2⟩

theorem commonGraphFirstRestriction_openEmbedding (hAU : A ≤ U) :
    Topology.IsOpenEmbedding (commonGraphFirstRestriction (B := B) hAU) :=
  Topology.IsOpenEmbedding.of_comp _ (blockOpen U b).isOpen.isOpenEmbedding_subtypeVal
    (commonDomain A B).isOpen.isOpenEmbedding_subtypeVal

theorem commonGraphSecondRestriction_openEmbedding (hBV : B ≤ V) :
    Topology.IsOpenEmbedding (commonGraphSecondRestriction (A := A) hBV) :=
  Topology.IsOpenEmbedding.of_comp _ (blockOpen V a).isOpen.isOpenEmbedding_subtypeVal
    ((blockSwap a b).toHomeomorph.isOpenEmbedding.comp
      (commonDomain A B).isOpen.isOpenEmbedding_subtypeVal)

theorem commonGraphFirstRestriction_contMDiff (hAU : A ≤ U) :
    ContMDiff 𝓘(ℂ, ComplexModel (a+b)) 𝓘(ℂ, ComplexModel (a+b)) ∞
      (commonGraphFirstRestriction (B := B) hAU) :=
  contMDiff_inclusion (common_le_first hAU)

theorem commonGraphSecondRestriction_contMDiff (hBV : B ≤ V) :
    ContMDiff 𝓘(ℂ, ComplexModel (a+b)) 𝓘(ℂ, ComplexModel (b+a)) ∞
      (commonGraphSecondRestriction (A := A) hBV) :=
  (ContMDiff.subtypeVal_comp_iff _ _).mp
    ((blockSwap a b).contMDiff.comp contMDiff_subtype_val)

@[simp] theorem commonGraphFirstRestriction_val (hAU : A ≤ U) (z : commonDomain A B) :
    (commonGraphFirstRestriction hAU z).val = z.val := rfl

@[simp] theorem commonGraphSecondRestriction_val (hBV : B ≤ V) (z : commonDomain A B) :
    (commonGraphSecondRestriction hBV z).val = blockSwap a b z.val := rfl

/-- The first restriction is an open holomorphic embedding in the
same ambient block coordinates. -/
theorem commonGraphFirstRestriction_isOpenHoloEmbedding (hAU : A ≤ U) :
    IsOpenHoloEmbedding (a + b) (commonGraphFirstRestriction (B := B) hAU) :=
  ⟨MaxLocusLocal.nestedOpens (blockOpen U b) (commonDomain A B),
    (MaxLocusLocal.nestedOpensDiffeo (n := a + b) (common_le_first hAU)).symm, fun _ => rfl⟩

/-- The switched restriction is a biholomorphism onto its open image,
expressed in the two actual coordinate orders. -/
theorem commonGraphSecondRestriction_openImage (hBV : B ≤ V) :
    ∃ (O : Opens (blockOpen V a))
      (Φ : commonDomain A B ≃ₘ⟮𝓘(ℂ, ComplexModel (a+b)), 𝓘(ℂ, ComplexModel (b+a))⟯ O),
        ∀ z, commonGraphSecondRestriction hBV z = (Φ z : blockOpen V a) := by
  let S := commonDomain A B
  let T := blockOpen V a
  let E := blockSwap a b
  let O : Opens T := ⟨(Subtype.val : T → ComplexModel (b+a)) ⁻¹'
      (E '' (S : Set (ComplexModel (a+b)))),
    (E.toHomeomorph.isOpenMap _ S.isOpen).preimage continuous_subtype_val⟩
  let f : S → O := fun z => ⟨commonGraphSecondRestriction hBV z, ⟨z.val, z.property, rfl⟩⟩
  have hInv (z : O) : E.symm z.val.val ∈ S := by
    obtain ⟨w, hw, he⟩ := z.property
    rw [← he, E.symm_apply_apply]
    exact hw
  let g : O → S := fun z => ⟨E.symm z.val.val, hInv z⟩
  have hf : ContMDiff 𝓘(ℂ, ComplexModel (a+b)) 𝓘(ℂ, ComplexModel (b+a)) ∞ f :=
    (ContMDiff.subtypeVal_comp_iff O f).mp (commonGraphSecondRestriction_contMDiff hBV)
  have hg : ContMDiff 𝓘(ℂ, ComplexModel (b+a)) 𝓘(ℂ, ComplexModel (a+b)) ∞ g :=
    (ContMDiff.subtypeVal_comp_iff S g).mp
      (E.symm.contMDiff.comp (contMDiff_subtype_val.comp contMDiff_subtype_val))
  refine ⟨O, ⟨⟨f, g, ?_, ?_⟩, hf, hg⟩, fun _ => rfl⟩
  · intro z
    exact Subtype.ext (E.symm_apply_apply z.val)
  · intro z
    exact Subtype.ext (Subtype.ext (E.apply_symm_apply z.val.val))

/-- Use the same underlying charted space after reindexing an equal
finite coordinate dimension. -/
@[instance_reducible]
def chartedSpaceReindex {d e : ℕ} {T : Type} [TopologicalSpace T]
    [ChartedSpace (ComplexModel e) T] (h : e = d) :
    ChartedSpace (ComplexModel d) T := h ▸ inferInstanceAs (ChartedSpace (ComplexModel e) T)

theorem isComplexManifoldReindex {d e : ℕ} {T : Type} [TopologicalSpace T]
    [ChartedSpace (ComplexModel e) T] [IsComplexManifold e T] (h : e = d) :
    letI := chartedSpaceReindex (T := T) h
    IsComplexManifold d T := by
  subst d
  infer_instance

private theorem reindex_openImage {d e : ℕ} {S T : Type} [TopologicalSpace S] [TopologicalSpace T]
    [ChartedSpace (ComplexModel d) S] [IsComplexManifold d S]
    [ChartedSpace (ComplexModel e) T] [IsComplexManifold e T] (h : e = d) (f : S → T)
    (O : Opens T) (Φ : S ≃ₘ⟮𝓘(ℂ, ComplexModel d), 𝓘(ℂ, ComplexModel e)⟯ O)
    (hΦ : ∀ z, f z = (Φ z : T)) :
    letI := chartedSpaceReindex (T := T) h
    letI := isComplexManifoldReindex (T := T) h
    IsOpenHoloEmbedding d f := by
  subst e
  exact ⟨O, Φ, hΦ⟩

/-- In equal dimension after the coordinate-order reindex, the second
restriction is an actual open holomorphic embedding. -/
theorem commonGraphSecondRestriction_isOpenHoloEmbedding (hBV : B ≤ V) :
    letI := chartedSpaceReindex (T := blockOpen V a) (Nat.add_comm b a)
    letI := isComplexManifoldReindex (T := blockOpen V a) (Nat.add_comm b a)
    IsOpenHoloEmbedding (a+b) (commonGraphSecondRestriction (A := A) hBV) := by
  obtain ⟨O, Φ, hΦ⟩ := commonGraphSecondRestriction_openImage (A := A) hBV
  exact reindex_openImage (Nat.add_comm b a) _ O Φ hΦ

/-- A coordinate graph in the original iterated ambient open. -/
def originalCoordinateGraph {d r : ℕ} (O : Opens (ComplexModel d))
    (W : Set (ComplexModel d)) (F : ComplexModel d → ComplexModel r) : Set (blockOpen O r) :=
  {z | tangentProjection d r z.val ∈ W ∧
    actualJointNormalProjection d r z.val = F (tangentProjection d r z.val)}

/-- The coordinate formula is the same carrier as the finite block record. -/
theorem originalCoordinateGraph_eq_blockGraph {d r : ℕ} (O : Opens (ComplexModel d))
    (W : Set O) (F : ComplexModel d → ComplexModel r) :
    originalCoordinateGraph O (coordinateCarrier W) F =
      blockGraph (fun x : O => F x.val) W := by
  ext z
  have hMem : tangentProjection d r z.val ∈ coordinateCarrier W ↔ blockProjection z ∈ W := by
    constructor
    · rintro ⟨x, hx, he⟩
      have hEq : x = blockProjection z := Subtype.ext he
      exact hEq ▸ hx
    · intro hz
      exact ⟨blockProjection z, hz, rfl⟩
  exact and_congr_left' hMem

/-- The literal common graph is the first original graph's preimage. -/
theorem commonGraph_first_preimage (hAU : A ≤ U)
    (W : Set (ComplexModel a)) (F : ComplexModel a → ComplexModel b) :
    commonGraphFirstRestriction (B := B) hAU ⁻¹' originalCoordinateGraph U W F =
      commonGraphSubset A B F (W ∩ (A : Set (ComplexModel a))) := by
  ext z
  change (tangentProjection a b z.val ∈ W ∧ _) ↔
    ((tangentProjection a b z.val ∈ W ∧ tangentProjection a b z.val ∈ A) ∧ _)
  exact ⟨fun h => ⟨⟨h.1, z.property.1⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩

/-- The reversed original graph pulls back to that same literal common graph.
Only the identities on the actual coordinate carriers enter the proof. -/
theorem commonGraph_second_preimage (hBV : B ≤ V)
    (W : Set (ComplexModel a)) (T : Set (ComplexModel b))
    (F : ComplexModel a → ComplexModel b) (G : ComplexModel b → ComplexModel a)
    (hFT : ∀ x ∈ W ∩ (A : Set (ComplexModel a)), F x ∈ T ∩ (B : Set (ComplexModel b)))
    (hGW : ∀ y ∈ T ∩ (B : Set (ComplexModel b)), G y ∈ W ∩ (A : Set (ComplexModel a)))
    (hGF : ∀ x ∈ W ∩ (A : Set (ComplexModel a)), G (F x) = x)
    (hFG : ∀ y ∈ T ∩ (B : Set (ComplexModel b)), F (G y) = y) :
    commonGraphSecondRestriction (A := A) hBV ⁻¹' originalCoordinateGraph V T G =
      commonGraphSubset A B F (W ∩ (A : Set (ComplexModel a))) := by
  ext z
  change (tangentProjection b a (blockSwap a b z.val) ∈ T ∧
    actualJointNormalProjection b a (blockSwap a b z.val) =
      G (tangentProjection b a (blockSwap a b z.val))) ↔
    (tangentProjection a b z.val ∈ W ∩ (A : Set (ComplexModel a)) ∧
      actualJointNormalProjection a b z.val = F (tangentProjection a b z.val))
  rw [blockSwap_first, blockSwap_second]
  constructor
  · rintro ⟨hy, he⟩
    have hy' : actualJointNormalProjection a b z.val ∈ T ∩ (B : Set (ComplexModel b)) :=
      ⟨hy, z.property.2⟩
    exact ⟨he.symm ▸ hGW _ hy', he.symm ▸ (hFG _ hy').symm⟩
  · rintro ⟨hx, he⟩
    exact ⟨he.symm ▸ (hFT _ hx).1, he.symm ▸ (hGF _ hx).symm⟩

/-- Any intrinsic comparison of the independent originals supplies genuine
paired ambient restrictions with the same literal carrier-graph preimage. -/
theorem exists_actual_commonGraph_restrictions
    {C : Set U} {D : Set V}
    (e : actualSubspaceLocallyRingedSpace (n := a) C ≅ actualSubspaceLocallyRingedSpace (n := b) D)
    (he : e.hom ≫ subspacePointMap (n := b) D = subspacePointMap (n := a) C)
    (hC : IsComplexAnalyticSubset (n := a) C) (hD : IsComplexAnalyticSubset (n := b) D) (c : C) :
    ∃ (A : Opens (ComplexModel a)) (B : Opens (ComplexModel b))
      (F : ComplexModel a → ComplexModel b) (G : ComplexModel b → ComplexModel a)
      (hAU : A ≤ U) (hBV : B ≤ V),
      c.val.val ∈ A ∧ (e.hom.base c).val.val ∈ B ∧
      ContDiffOn ℂ ∞ F A ∧ ContDiffOn ℂ ∞ G B ∧
      (∀ x : C, x.val.val ∈ A → F x.val.val = (e.hom.base x).val.val) ∧
      (∀ y : D, y.val.val ∈ B → G y.val.val = (e.inv.base y).val.val) ∧
      let S := commonGraphSubset A B F (coordinateCarrier C ∩ (A : Set (ComplexModel a)))
      commonGraphFirstRestriction (B := B) hAU ⁻¹' originalCoordinateGraph U (coordinateCarrier C) F = S ∧
      commonGraphSecondRestriction (A := A) hBV ⁻¹' originalCoordinateGraph V (coordinateCarrier D) G = S := by
  obtain ⟨A,B,F,G,hAU,hBV,hcA,hdB,hF,hG,_hW,_hT,hFT,hGW,hGF,hFG,hFval,hGval⟩ :=
    exists_actual_intrinsic_iso_paired_windows e he hC hD c
  exact ⟨A,B,F,G,hAU,hBV,hcA,hdB,hF,hG,hFval,hGval,
    commonGraph_first_preimage hAU _ _,
    commonGraph_second_preimage hBV _ _ _ _ hFT hGW hGF hFG⟩

private theorem coordinateCarrier_inclusion_preimage {d : ℕ}
    {P O : Opens (ComplexModel d)} (hPO : P ≤ O) (C : Set O) :
    coordinateCarrier (Opens.inclusion hPO ⁻¹' C) =
      coordinateCarrier C ∩ (P : Set (ComplexModel d)) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨Opens.inclusion hPO x, hx, rfl⟩, x.property⟩
  · rintro ⟨⟨x, hx, rfl⟩, hz⟩
    exact ⟨⟨x.val, hz⟩, hx, rfl⟩

/-- On the genuine paired windows the two finite block source carriers
pull back to the same graph. Each graph anchor is holomorphic on its
entire source window. -/
theorem exists_actual_commonBlockGraph_restrictions
    {C : Set U} {D : Set V}
    (e : actualSubspaceLocallyRingedSpace (n := a) C ≅ actualSubspaceLocallyRingedSpace (n := b) D)
    (he : e.hom ≫ subspacePointMap (n := b) D = subspacePointMap (n := a) C)
    (hC : IsComplexAnalyticSubset (n := a) C) (hD : IsComplexAnalyticSubset (n := b) D) (c : C) :
    ∃ (A : Opens (ComplexModel a)) (B : Opens (ComplexModel b))
      (F : ComplexModel a → ComplexModel b) (G : ComplexModel b → ComplexModel a)
      (hAU : A ≤ U) (hBV : B ≤ V),
      c.val.val ∈ A ∧ (e.hom.base c).val.val ∈ B ∧
      ContDiffOn ℂ ∞ F A ∧ ContDiffOn ℂ ∞ G B ∧
      let W := Opens.inclusion hAU ⁻¹' C
      let T := Opens.inclusion hBV ⁻¹' D
      let S := commonGraphSubset A B F (coordinateCarrier C ∩ (A : Set (ComplexModel a)))
      commonGraphFirstRestriction (B := B) (le_refl A) ⁻¹'
          blockGraph (fun x : A => F x.val) W = S ∧
      commonGraphSecondRestriction (A := A) (le_refl B) ⁻¹'
          blockGraph (fun y : B => G y.val) T = S := by
  obtain ⟨A,B,F,G,hAU,hBV,hcA,hdB,hF,hG,_hW,_hT,hFT,hGW,hGF,hFG,_hFval,_hGval⟩ :=
    exists_actual_intrinsic_iso_paired_windows e he hC hD c
  have hWI := coordinateCarrier_inclusion_preimage hAU C
  have hTI := coordinateCarrier_inclusion_preimage hBV D
  refine ⟨A,B,F,G,hAU,hBV,hcA,hdB,hF,hG,?_⟩
  dsimp only
  rw [← originalCoordinateGraph_eq_blockGraph, ← originalCoordinateGraph_eq_blockGraph, hWI, hTI]
  have hW : coordinateCarrier C ∩ (A : Set (ComplexModel a)) ∩ (A : Set (ComplexModel a)) =
      coordinateCarrier C ∩ (A : Set (ComplexModel a)) := by rw [inter_assoc, inter_self]
  have hT : coordinateCarrier D ∩ (B : Set (ComplexModel b)) ∩ (B : Set (ComplexModel b)) =
      coordinateCarrier D ∩ (B : Set (ComplexModel b)) := by rw [inter_assoc, inter_self]
  constructor
  · rw [commonGraph_first_preimage, hW]
  · rw [commonGraph_second_preimage (A := A) (le_refl B)
      (coordinateCarrier C ∩ (A : Set (ComplexModel a))) _ F G]
    · rw [hW]
    · simpa only [hW, hT] using hFT
    · simpa only [hW, hT] using hGW
    · simpa only [hW] using hGF
    · simpa only [hT] using hFG

/-- Restriction to the first actual iterated original open. -/
def commonGraphFirstIteratedRestriction (hAU : A ≤ U) :
    commonDomain A B → iteratedNormalOpen U b :=
  iteratedNormalBlockEquiv U b ∘ commonGraphFirstRestriction hAU

/-- Restriction to the second actual iterated original open. -/
def commonGraphSecondIteratedRestriction (hBV : B ≤ V) :
    commonDomain A B → iteratedNormalOpen V a :=
  iteratedNormalBlockEquiv V a ∘ commonGraphSecondRestriction hBV

theorem commonGraphFirstIteratedRestriction_openEmbedding (hAU : A ≤ U) :
    Topology.IsOpenEmbedding (commonGraphFirstIteratedRestriction (B := B) hAU) :=
  (iteratedNormalBlockEquiv U b).toHomeomorph.isOpenEmbedding.comp
    (commonGraphFirstRestriction_openEmbedding hAU)

theorem commonGraphSecondIteratedRestriction_openEmbedding (hBV : B ≤ V) :
    Topology.IsOpenEmbedding (commonGraphSecondIteratedRestriction (A := A) hBV) :=
  (iteratedNormalBlockEquiv V a).toHomeomorph.isOpenEmbedding.comp
    (commonGraphSecondRestriction_openEmbedding hBV)

theorem commonGraphFirstIteratedRestriction_contMDiff (hAU : A ≤ U) :
    ContMDiff 𝓘(ℂ, ComplexModel (a+b)) 𝓘(ℂ, ComplexModel (a+b)) ∞
      (commonGraphFirstIteratedRestriction (B := B) hAU) :=
  (iteratedNormalBlockEquiv U b).contMDiff.comp (commonGraphFirstRestriction_contMDiff hAU)

theorem commonGraphSecondIteratedRestriction_contMDiff (hBV : B ≤ V) :
    ContMDiff 𝓘(ℂ, ComplexModel (a+b)) 𝓘(ℂ, ComplexModel (b+a)) ∞
      (commonGraphSecondIteratedRestriction (A := A) hBV) :=
  (iteratedNormalBlockEquiv V a).contMDiff.comp (commonGraphSecondRestriction_contMDiff hBV)

/-- Moving a finite block carrier into its literal iterated open preserves
its pullback along the first ambient restriction. -/
theorem commonGraphFirstIteratedRestriction_preimage (hAU : A ≤ U) (S : Set (blockOpen U b)) :
    commonGraphFirstIteratedRestriction (B := B) hAU ⁻¹' (iteratedNormalBlockEquiv U b '' S) =
      commonGraphFirstRestriction (B := B) hAU ⁻¹' S := by
  have hInj : Function.Injective (fun z : blockOpen U b => iteratedNormalBlockEquiv U b z) :=
    (iteratedNormalBlockEquiv U b).injective
  rw [commonGraphFirstIteratedRestriction, preimage_comp, preimage_image_eq _ hInj]

/-- The same comparison for the ambient restriction in exchanged block order. -/
theorem commonGraphSecondIteratedRestriction_preimage (hBV : B ≤ V) (S : Set (blockOpen V a)) :
    commonGraphSecondIteratedRestriction (A := A) hBV ⁻¹' (iteratedNormalBlockEquiv V a '' S) =
      commonGraphSecondRestriction (A := A) hBV ⁻¹' S := by
  have hInj : Function.Injective (fun z : blockOpen V a => iteratedNormalBlockEquiv V a z) :=
    (iteratedNormalBlockEquiv V a).injective
  rw [commonGraphSecondIteratedRestriction, preimage_comp, preimage_image_eq _ hInj]

end
end Hironaka.HironakaG1CommonGraphRestrictionMaps
