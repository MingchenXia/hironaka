import Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentOverlap
import Hironaka.Analytic.Unibranch.OriginalNativeHSUnequalSuccessor
import Hironaka.Analytic.Unibranch.OriginalNativePrescribedHistoryRefinement

/-! The actual skipped successor gives a genuine PAST overlap over one
literal original base. Blueprint FIRST: original-native-hs-skipped-current-overlap.tex.
No future-case supplier, final comparison or common physical clock. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSSkippedCurrentOverlap
noncomputable section
open Hironaka HironakaEmbeddedNativeMorphism SourceReducedComplexSpace
  OriginalNativeHSOuterHistory OriginalNativeHSShadowOuterState OriginalNativeHSCurrentOverlap
  OriginalRelativelyCompactRestriction

private theorem native_iso_of_same_range {A B C : SourceReducedComplexSpace}
    (a : A ⟶ C) (b : B ⟶ C)
    (ha : LocallyRingedSpace.IsOpenImmersion a.hom.left)
    (hb : LocallyRingedSpace.IsOpenImmersion b.hom.left)
    (hr : range a.hom.left.base = range b.hom.left.base) :
    ∃ e : A ≅ B, e.hom ≫ b = a := by
  let : LocallyRingedSpace.IsOpenImmersion a.hom.left := ha
  let : LocallyRingedSpace.IsOpenImmersion b.hom.left := hb
  let E := openImmersionIsoOfRangeEq a.hom.left b.hom.left hr
  have hf : E.hom ≫ b.hom.left = a.hom.left := openImmersionIsoOfRangeEq_hom_fac _ _ hr
  have hp : E.hom ≫ B.obj.hom = A.obj.hom := by
    rw [← Over.w b.hom,← Category.assoc,hf]
    exact Over.w a.hom
  refine ⟨ObjectProperty.isoMk sourceReducedComplexSpaceProperty (Over.isoMk E hp),?_⟩
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact hf

private theorem restrict_comparison {X Y₁ Y₂ A₁ A₂ Z₁ Z₂ : SourceReducedComplexSpace}
    (f : Y₁ ⟶ X) (g : Y₂ ⟶ X) (a : A₁ ⟶ Y₁) (b : A₂ ⟶ Y₂)
    (ha : LocallyRingedSpace.IsOpenImmersion a.hom.left)
    (hb : LocallyRingedSpace.IsOpenImmersion b.hom.left)
    (θ : A₁ ≅ A₂) (hθ : θ.hom ≫ b ≫ g = a ≫ f)
    (O V : Set X.obj.left) (hVO : V ⊆ O)
    (hra : range a.hom.left.base = f.hom.left.base ⁻¹' O)
    (hrb : range b.hom.left.base = g.hom.left.base ⁻¹' O)
    (l : Z₁ ⟶ Y₁) (r : Z₂ ⟶ Y₂)
    (hl : LocallyRingedSpace.IsOpenImmersion l.hom.left)
    (hr : LocallyRingedSpace.IsOpenImmersion r.hom.left)
    (hrl : range l.hom.left.base = f.hom.left.base ⁻¹' V)
    (hrr : range r.hom.left.base = g.hom.left.base ⁻¹' V) :
    ∃ η : Z₁ ≅ Z₂, η.hom ≫ r ≫ g = l ≫ f := by
  have hsub : range l.hom.left.base ⊆ range a.hom.left.base := by
    rw [hrl,hra]
    exact fun _ hy => hVO hy
  obtain ⟨k,hk,hka⟩ := OriginalNativeSmoothOpenLocality.exists_native_open_lift a l ha hl hsub
  have hθO : LocallyRingedSpace.IsOpenImmersion θ.hom.hom.left := by
    change LocallyRingedSpace.IsOpenImmersion (isoLeft θ).hom
    infer_instance
  let m := k ≫ θ.hom ≫ b
  have hm : LocallyRingedSpace.IsOpenImmersion m.hom.left :=
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ k.hom.left hk _
      (@LocallyRingedSpace.IsOpenImmersion.comp _ _ _ θ.hom.hom.left hθO b.hom.left hb)
  have hmg : m ≫ g = l ≫ f := by
    change (k ≫ θ.hom ≫ b) ≫ g = _
    rw [Category.assoc,Category.assoc,hθ,← Category.assoc,hka]
  have hmr : range m.hom.left.base = range r.hom.left.base := by
    rw [hrr]
    ext y
    constructor
    · rintro ⟨z,rfl⟩
      have hz : l.hom.left.base z ∈ f.hom.left.base ⁻¹' V := by
        rw [← hrl]
        exact ⟨z,rfl⟩
      have he := congrArg (fun p => p.hom.left.base z) hmg
      exact (congrArg (fun x : X.obj.left => x ∈ V) he).mpr hz
    · intro hy
      have hyb : y ∈ range b.hom.left.base := by rw [hrb];exact hVO hy
      obtain ⟨z,hz⟩ := hyb
      let u := θ.inv.hom.left.base z
      have hu : θ.hom.hom.left.base u = z :=
        congrArg (fun p => p.hom.left.base z) θ.inv_hom_id
      have he := congrArg (fun p => p.hom.left.base u) hθ
      change g.hom.left.base (b.hom.left.base (θ.hom.hom.left.base u)) =
        f.hom.left.base (a.hom.left.base u) at he
      rw [hu,hz] at he
      have hul : a.hom.left.base u ∈ range l.hom.left.base := by
        rw [hrl]
        exact (congrArg (fun x : X.obj.left => x ∈ V) he).mp hy
      obtain ⟨v,hv⟩ := hul
      have hku : k.hom.left.base v = u := ha.base_open.injective
        ((congrArg (fun p => p.hom.left.base v) hka).trans hv)
      refine ⟨v,?_⟩
      change b.hom.left.base (θ.hom.hom.left.base (k.hom.left.base v)) = y
      rw [hku,hu,hz]
  obtain ⟨η,hη⟩ := native_iso_of_same_range m r hm hr hmr
  exact ⟨η,(Category.assoc _ _ _).symm.trans ((congrArg (fun p => p ≫ g) hη).trans hmg)⟩

variable {X : SourceReducedComplexSpace} {K L : Set X.obj.left}
  (S : State X K) (hK : IsCompact K) (hne : (singularShadow S).Nonempty)
  (hL : IsCompact L) (hLK : L ⊆ K)
  (W : Opens X.obj.left) (hLW : L ⊆ W)

abbrev nextCompact : Set (OriginalNativeHSShadowOuterRun.next S hK hne).base.obj.left :=
  (OriginalNativeHSShadowOuterRun.next S hK hne).inclusion.hom.left.base ⁻¹' L

include hL hLK in
theorem nextCompact_isCompact : IsCompact (nextCompact S hK hne (L := L)) :=
  (OriginalNativeHSShadowOuterRun.next S hK hne).inclusion_isOpenImmersion.base_open.isEmbedding.isInducing.isCompact_preimage'
    hL (fun _ hx => (OriginalNativeHSShadowOuterRun.next S hK hne).contains (hLK hx))

local notation "S₊" => OriginalNativeHSShadowOuterRun.next S hK hne
local notation "A" => OriginalNativeHSOuterSuccessor.oldSource S.history (baseShadow S) (baseShadow_compact S hK) hne
local notation "N₀" => OriginalNativeHSOuterSuccessor.neighbourhood S.history (baseShadow S) (baseShadow_compact S hK) hne
local notation "H₀" => OriginalNativeHSOuterInitialBound.profile S.history (baseShadow S) (baseShadow_compact S hK) hne

variable (hEmpty : OriginalNativeHSAbsentOuterSuccessor.oldFibre S.history (baseShadow S)
    (baseShadow_compact S hK) hne (nextCompact S hK hne (L := L)) ∩
      OriginalIntrinsicHSSuperlevels.originalSingularHSThreshold
        (OriginalNativeHSOuterSuccessor.oldSource S.history (baseShadow S) (baseShadow_compact S hK) hne)
        (OriginalNativeHSOuterInitialBound.profile S.history (baseShadow S) (baseShadow_compact S hK) hne) = ∅)

local notation "hc" => nextCompact_isCompact S hK hne hL hLK
local notation "N" => OriginalNativeHSAbsentOuterSuccessor.neighbourhood S.history (baseShadow S)
  (baseShadow_compact S hK) hne (nextCompact S hK hne (L := L)) (hc) hEmpty

private def rawBaseMap : (N).source ⟶ X := (N).inclusion ≫ (S₊).inclusion

private theorem rawBaseMap_open : LocallyRingedSpace.IsOpenImmersion (rawBaseMap S hK hne hL hLK hEmpty).hom.left :=
  @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ (N).inclusion.hom.left (N).inclusion_isOpenImmersion
    (S₊).inclusion.hom.left (S₊).inclusion_isOpenImmersion

private theorem compact_in_raw : L ⊆ range (rawBaseMap S hK hne hL hLK hEmpty).hom.left.base := by
  intro x hx
  obtain ⟨b,hb⟩ := (S₊).contains (hLK hx)
  have hbL : b ∈ nextCompact S hK hne (L := L) := by change (S₊).inclusion.hom.left.base b ∈ L;exact hb.symm ▸ hx
  exact ⟨⟨b,(N).contains hbL⟩,hb⟩

def neighbourhood : OriginalNativePrecompactNeighbourhood.Neighbourhood X L
    (W ⊓ ⟨range (rawBaseMap S hK hne hL hLK hEmpty).hom.left.base,
      (rawBaseMap_open S hK hne hL hLK hEmpty).base_open.isOpen_range⟩) :=
  OriginalNativePrecompactNeighbourhood.neighbourhood X L hL _
    (fun _ hx => ⟨hLW hx,compact_in_raw S hK hne hL hLK hEmpty hx⟩)

private abbrev nextCut := OriginalNativeHSAbsentOuterSuccessor.nextSource S.history (baseShadow S)
  (baseShadow_compact S hK) hne (nextCompact S hK hne (L := L)) (hc) hEmpty
private abbrev oldCut := OriginalNativeHSAbsentOuterSuccessor.oldSource S.history (baseShadow S)
  (baseShadow_compact S hK) hne (nextCompact S hK hne (L := L)) (hc) hEmpty

private def nextCutMap : nextCut S hK hne hL hLK hEmpty ⟶ (S₊).source :=
  OriginalNativeHSAbsentOuterSuccessor.nextInclusion S.history (baseShadow S)
    (baseShadow_compact S hK) hne (nextCompact S hK hne (L := L)) (hc) hEmpty
private def oldCutMap : oldCut S hK hne hL hLK hEmpty ⟶ S.source :=
  OriginalNativeHSAbsentOuterSuccessor.oldInclusion S.history (baseShadow S)
    (baseShadow_compact S hK) hne (nextCompact S hK hne (L := L)) (hc) hEmpty ≫
      OriginalNativeHSOuterSuccessor.oldInclusion S.history (baseShadow S) (baseShadow_compact S hK) hne

private theorem nextCutMap_open : LocallyRingedSpace.IsOpenImmersion (nextCutMap S hK hne hL hLK hEmpty).hom.left :=
  inclusion_isOpenImmersion _ _ _
private theorem oldCutMap_open : LocallyRingedSpace.IsOpenImmersion (oldCutMap S hK hne hL hLK hEmpty).hom.left :=
  @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ _ (inclusion_isOpenImmersion _ _ _) _
    (inclusion_isOpenImmersion _ _ _)

private theorem nextCutMap_range : range (nextCutMap S hK hne hL hLK hEmpty).hom.left.base =
    ((S₊).history.projection ≫ (S₊).inclusion).hom.left.base ⁻¹'
      range (rawBaseMap S hK hne hL hLK hEmpty).hom.left.base := by
  change range (Subtype.val : preimageOpen (N).openSet (S₊).history.projection → (S₊).source.obj.left) = _
  rw [Subtype.range_coe]
  ext y
  constructor
  · intro hy
    exact ⟨⟨(S₊).history.projection.hom.left.base y,hy⟩,rfl⟩
  · rintro ⟨z,hz⟩
    have he : z.val = (S₊).history.projection.hom.left.base y :=
      (S₊).inclusion_isOpenImmersion.base_open.injective hz
    change (S₊).history.projection.hom.left.base y ∈ (N).openSet
    exact (congrArg (fun b : (S₊).base.obj.left => b ∈ (N).openSet) he).mp z.property

private theorem oldCutMap_range : range (oldCutMap S hK hne hL hLK hEmpty).hom.left.base =
    (S.history.projection ≫ S.inclusion).hom.left.base ⁻¹'
      range (rawBaseMap S hK hne hL hLK hEmpty).hom.left.base := by
  ext y
  constructor
  · rintro ⟨z,rfl⟩
    refine ⟨⟨(OriginalNativeHSAbsentOuterSuccessor.oldPrefix S.history (baseShadow S)
      (baseShadow_compact S hK) hne).projection.hom.left.base z.val,z.property⟩,?_⟩
    exact congrArg S.inclusion.hom.left.base
      (OriginalNativePhysicalHistoryRestriction.projection_point S.history (N₀).openSet (N₀).compactClosure z.val)
  · rintro ⟨z,hz⟩
    have hz' : z.val.val = S.history.projection.hom.left.base y :=
      S.inclusion_isOpenImmersion.base_open.injective hz
    have hy : S.history.projection.hom.left.base y ∈ (N₀).openSet := hz' ▸ z.val.property
    let a : (A).obj.left := ⟨y,hy⟩
    have ha : (OriginalNativeHSAbsentOuterSuccessor.oldPrefix S.history (baseShadow S)
        (baseShadow_compact S hK) hne).projection.hom.left.base a = z.val := by
      apply Subtype.ext
      exact (OriginalNativePhysicalHistoryRestriction.projection_point S.history
        (N₀).openSet (N₀).compactClosure a).trans hz'.symm
    refine ⟨⟨a,?_⟩,rfl⟩
    change (OriginalNativeHSAbsentOuterSuccessor.oldPrefix S.history (baseShadow S)
      (baseShadow_compact S hK) hne).projection.hom.left.base a ∈ (N).openSet
    rw [ha]
    exact z.property

private theorem raw_comparison_square :
    (OriginalNativeHSAbsentOuterSuccessor.comparison S.history (baseShadow S)
      (baseShadow_compact S hK) hne (nextCompact S hK hne (L := L)) (hc) hEmpty).hom ≫
      oldCutMap S hK hne hL hLK hEmpty ≫ S.history.projection ≫ S.inclusion =
    nextCutMap S hK hne hL hLK hEmpty ≫ (S₊).history.projection ≫ (S₊).inclusion := by
  have hs := OriginalNativeHSAbsentOuterSuccessor.comparison_original_source_square S.history (baseShadow S)
    (baseShadow_compact S hK) hne (nextCompact S hK hne (L := L)) (hc) hEmpty
  apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
  intro z
  have hsPoint := congrArg (fun p => p.hom.left.base z) hs
  have hn := congrArg (fun p => p.hom.left.base ((nextCutMap S hK hne hL hLK hEmpty).hom.left.base z))
    (OriginalNativeHSShadowOuterRun.next_projection_square S hK hne)
  exact (congrArg (fun y : S.source.obj.left => S.inclusion.hom.left.base
    (S.history.projection.hom.left.base y)) hsPoint).trans hn.symm

include hL hLK hLW hEmpty in
/-- A real skipped successor, on a computed common ORIGINAL open retaining ALL L. -/
theorem exists_context : ∃ c : Context (S₊) S L, c.openSet ≤ W := by
  let M := neighbourhood S hK hne hL hLK W hLW hEmpty
  have hRN : closure (M.openSet : Set X.obj.left) ⊆ range (S₊).inclusion.hom.left.base := by
    intro x hx
    obtain ⟨z,hz⟩ := (M.closure_subset hx).2
    exact ⟨z.val,hz⟩
  have hRS : closure (M.openSet : Set X.obj.left) ⊆ range S.inclusion.hom.left.base := by
    intro x hx
    obtain ⟨z,hz⟩ := (M.closure_subset hx).2
    exact ⟨z.val.val,hz⟩
  let l := inclusion (S₊) M.openSet M.compactClosure hRN
  let r := inclusion S M.openSet M.compactClosure hRS
  have hl : LocallyRingedSpace.IsOpenImmersion l.hom.left :=
    OriginalNativePrescribedOpenHistory.sourceInclusion_isOpenImmersion _ _ _ _ _ _
  have hr : LocallyRingedSpace.IsOpenImmersion r.hom.left :=
    OriginalNativePrescribedOpenHistory.sourceInclusion_isOpenImmersion _ _ _ _ _ _
  have hrl : range l.hom.left.base = ((S₊).history.projection ≫ (S₊).inclusion).hom.left.base ⁻¹'
      (M.openSet : Set X.obj.left) :=
    OriginalNativePrescribedHistoryRefinement.inclusion_range _ _ _ _ _ _
  have hrr : range r.hom.left.base = (S.history.projection ≫ S.inclusion).hom.left.base ⁻¹'
      (M.openSet : Set X.obj.left) :=
    OriginalNativePrescribedHistoryRefinement.inclusion_range _ _ _ _ _ _
  obtain ⟨η,hη⟩ := restrict_comparison ((S₊).history.projection ≫ (S₊).inclusion)
    (S.history.projection ≫ S.inclusion) (nextCutMap S hK hne hL hLK hEmpty)
    (oldCutMap S hK hne hL hLK hEmpty) (nextCutMap_open S hK hne hL hLK hEmpty)
    (oldCutMap_open S hK hne hL hLK hEmpty)
    (OriginalNativeHSAbsentOuterSuccessor.comparison S.history (baseShadow S)
      (baseShadow_compact S hK) hne (nextCompact S hK hne (L := L)) (hc) hEmpty)
    (raw_comparison_square S hK hne hL hLK hEmpty)
    (range (rawBaseMap S hK hne hL hLK hEmpty).hom.left.base) (M.openSet : Set X.obj.left)
    (fun _ hx => (M.closure_subset (subset_closure hx)).2)
    (nextCutMap_range S hK hne hL hLK hEmpty) (oldCutMap_range S hK hne hL hLK hEmpty)
    l r hl hr hrl hrr
  have hsq : η.hom ≫ (history S M.openSet M.compactClosure hRS).projection =
      (history (S₊) M.openSet M.compactClosure hRN).projection := by
    have hs : (η.hom ≫ (history S M.openSet M.compactClosure hRS).projection) ≫
        OriginalRelativelyCompactRestriction.inclusion X M.openSet M.compactClosure =
      (history (S₊) M.openSet M.compactClosure hRN).projection ≫
        OriginalRelativelyCompactRestriction.inclusion X M.openSet M.compactClosure := by
      have hso : (history S M.openSet M.compactClosure hRS).projection ≫
          OriginalRelativelyCompactRestriction.inclusion X M.openSet M.compactClosure =
          r ≫ S.history.projection ≫ S.inclusion :=
        OriginalNativePrescribedOpenHistory.projection_square _ _ _ _ _ _
      have hsn : (history (S₊) M.openSet M.compactClosure hRN).projection ≫
          OriginalRelativelyCompactRestriction.inclusion X M.openSet M.compactClosure =
          l ≫ (S₊).history.projection ≫ (S₊).inclusion :=
        OriginalNativePrescribedOpenHistory.projection_square _ _ _ _ _ _
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun p => η.hom ≫ p) hso).trans (hη.trans hsn.symm))
    apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
    intro z
    apply Subtype.ext
    exact congrArg (fun p => p.hom.left.base z) hs
  exact ⟨⟨M.openSet,M.compactClosure,M.contains,hRN,hRS,η,hsq⟩,
    fun _ hx => (M.closure_subset (subset_closure hx)).1⟩

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSSkippedCurrentOverlap
