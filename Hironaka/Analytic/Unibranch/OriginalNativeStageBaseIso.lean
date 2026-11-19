import Hironaka.Analytic.Unibranch.HironakaG11PresReduction
import Hironaka.Analytic.Unibranch.HironakaG1NativeModificationIsoTransport
import Hironaka.Analytic.Unibranch.OriginalNativeHSThresholdIsomorphism

/-! Genuine common-base transport of the SAME actual ambient/native stage.
Blueprint FIRST: original-native-stage-base-iso.tex. Physical extraction
and its real extra empty-centre step are separate; no clocks are equated. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeStageBaseIso
noncomputable section
open Hironaka Hironaka.BlowupSequences
  Hironaka SourceReducedComplexSpace HironakaG11VanishingWindows
  HironakaG11VanishingPrincipalization HironakaG11StrictTransformTowers HironakaG11PresReduction
  HironakaG11CompatibleCanonicalTowers MarkedIdeals HironakaG11SingularCentreModification
  BlowupTowers ResolutionInvariantSeq
  HironakaG1NativeModificationIsoTransport OriginalIntrinsicHSSuperlevels

variable {B U : SourceReducedComplexSpace} {n : ℕ} {ι : Type}
  (w : ι → DimEmbedding B n) (α : U ≅ B)

private theorem inverse_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion α.inv.hom.left := by
  change LocallyRingedSpace.IsOpenImmersion (isoLeft α).inv
  infer_instance
private theorem forward_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion α.hom.hom.left := by
  change LocallyRingedSpace.IsOpenImmersion (isoLeft α).hom
  infer_instance

/-- The old ambient record/carrier stays literal; only its FULL native map changes. -/
def window (i : ι) : DimEmbedding U n where
  ambient := (w i).ambient
  carrier := (w i).carrier
  analytic := (w i).analytic
  map := (w i).map ≫ α.inv.hom.left
  isOpenImmersion := @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ _ (w i).isOpenImmersion _
    (inverse_isOpenImmersion α)
  overPoint := by rw [Category.assoc,Over.w α.inv.hom];exact (w i).overPoint

theorem window_point (i : ι) (c : (w i).carrier) :
    (window w α i).toLocalEmbedding.toPoint c=α.inv.hom.left.base ((w i).toLocalEmbedding.toPoint c) := rfl

theorem window_square (i : ι) :
    EmbeddedBlowupOverlap.chartMorphism (window w α i).toLocalEmbedding ≫ α.hom =
      EmbeddedBlowupOverlap.chartMorphism (w i).toLocalEmbedding := by
  apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
  intro c
  exact congrArg (fun f : B ⟶ B => f.hom.left.base ((w i).toLocalEmbedding.toPoint c)) α.inv_hom_id

theorem mapAdm_iff (i j : ι) (V : Opens (w i).ambient) (V' : Opens (w j).ambient)
    (Φ : CMfd.of (n := n) V' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V) :
    mapAdm (window w α) i j V V' Φ ↔ mapAdm w i j V V' Φ := by
  constructor
  · rintro ⟨hc,hp⟩
    refine ⟨hc,fun p hp' hq => ?_⟩
    exact (inverse_isOpenImmersion α).base_open.injective (hp p hp' hq)
  · rintro ⟨hc,hp⟩
    exact ⟨hc,fun p hp' hq => congrArg α.inv.hom.left.base (hp p hp' hq)⟩

theorem native_record (raw : ∀i,MarkedIdeal n (Amb w i)) (H : ℕ → ℕ)
    (hrec : ∀i,IsNativeWindowRecord (w i) (raw i) H) (i : ι) :
    IsNativeWindowRecord (window w α i) (raw i) H := hrec i

variable {k : ℕ} {Λ : Type} [LinearOrder Λ]
  (R : ResolutionInvariant.{0} n k Λ) (record : ∀i,MarkedIdeal n (Amb w i))

theorem recordsTransport (hTr : RecordsTransport R record (mapAdm w)) :
    RecordsTransport (w := window w α) R record (mapAdm (window w α)) := by
  intro i j V V' Φ hadm
  exact hTr i j V V' Φ ((mapAdm_iff w α i j V V' Φ).mp hadm)

/-- SAME whole ambient towers, canonical histories and old physical clock. -/
def stage {m : ℕ} (s : GStage R record (mapAdm w) m) :
    GStage (w := window w α) R record (mapAdm (window w α)) m where
  T := s.T
  length := s.length
  canonical := s.canonical
  compatible i j V V' Φ ha := s.compatible i j V V' Φ ((mapAdm_iff w α i j V V' Φ).mp ha)

variable {T : Towers w} (xs : XStage w T)

/-- The SAME actual endpoint/current windows over the exact common native base. -/
def nativeStage : XStage (window w α) T where
  Y := xs.Y
  q := xs.q ≫ α.inv
  isSingularCentreModification := by
    have hstep : IsSingularCentreStep α.inv := by
      refine ⟨emptyCentre U,emptyCentreInclusion U,isSmoothCentreBlowup_iso α.symm,?_⟩
      rw [emptyCentreInclusion_range]
      exact empty_subset _
    exact xs.isSingularCentreModification.comp hstep.isSingularCentreModification
  carrier := xs.carrier
  analytic := xs.analytic
  map := xs.map
  isOpenImmersion := xs.isOpenImmersion
  carrier_eq := xs.carrier_eq
  square i c hc := congrArg α.inv.hom.left.base (xs.square i c hc)
  range_map i := by
    rw [xs.range_map i]
    ext y
    constructor
    · rintro ⟨c,hc⟩
      exact ⟨c,congrArg α.inv.hom.left.base hc⟩
    · rintro ⟨c,hc⟩
      exact ⟨c,(inverse_isOpenImmersion α).base_open.injective hc⟩

theorem projection_formula : (nativeStage w α xs).q=xs.q ≫ α.inv := rfl

theorem projection_scalar : (nativeStage w α xs).q.hom.left ≫ U.obj.hom=xs.Y.obj.hom :=
  Over.w (nativeStage w α xs).q.hom

theorem projection_square : (nativeStage w α xs).q ≫ α.hom=xs.q := by simp [nativeStage]

theorem threshold_covered (H : ℕ → ℕ)
    (hCover : originalSingularHSThreshold B H ⊆ ⋃i,range (w i).toLocalEmbedding.toPoint) :
    originalSingularHSThreshold U H ⊆ ⋃i,range (window w α i).toLocalEmbedding.toPoint := by
  intro y hy
  have hb : α.hom.hom.left.base y ∈ originalSingularHSThreshold B H :=
    (Set.ext_iff.mp (OriginalNativeHSThresholdIsomorphism.threshold_preimage_openImmersion H
      α.hom (forward_isOpenImmersion α)) y).mpr hy
  obtain ⟨i,c,hc⟩ := Set.mem_iUnion.mp (hCover hb)
  refine Set.mem_iUnion.mpr ⟨i,c,?_⟩
  have hα : α.inv.hom.left.base (α.hom.hom.left.base y)=y :=
    congrArg (fun f : U ⟶ U => f.hom.left.base y) α.hom_inv_id
  exact (congrArg α.inv.hom.left.base hc).trans hα

theorem off_threshold (H : ℕ → ℕ) (hq : IsIsoOver xs.q (originalSingularHSThreshold B H)ᶜ) :
    IsIsoOver (nativeStage w α xs).q (originalSingularHSThreshold U H)ᶜ := by
  apply OriginalNativeHSThresholdIsomorphism.isIsoOver_open_square_threshold_compl H xs.q
    (nativeStage w α xs).q (𝟙 xs.Y) α.hom
  · change LocallyRingedSpace.IsOpenImmersion (𝟙 xs.Y.obj.left)
    infer_instance
  · exact forward_isOpenImmersion α
  · exact (projection_square w α xs).trans (Category.id_comp xs.q).symm
  · have hsurj : Function.Surjective α.hom.hom.left.base := by
      intro b
      exact ⟨α.inv.hom.left.base b,
        congrArg (fun f : B ⟶ B => f.hom.left.base b) α.inv_hom_id⟩
    simp only [show range α.hom.hom.left.base=univ from range_eq_univ.mpr hsurj,preimage_univ]
    exact Set.range_id
  · exact hq

theorem projection_proper : IsProperMap (nativeStage w α xs).q.hom.left.base :=
  (nativeStage w α xs).isSingularCentreModification.isProperMap

end
end Hironaka.Analytic.Unibranch.OriginalNativeStageBaseIso
