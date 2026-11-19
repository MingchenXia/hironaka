import Hironaka.Analytic.Unibranch.EmbeddedBlowupComparison
import Hironaka.Analytic.Unibranch.EmbeddedBlowupOpenRestriction

/-!
# Actual original overlap transitions for local blowup OBJECTS

The chart inputs are existing `LocalEmbedding X`, with their SAME original
carrier, ambient and full open immersion over the complex point. No new space
category or transition/cocycle/global-space packet is introduced.
Blueprint: `embedded-blowup-overlap.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace Topology CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.EmbeddedBlowupOverlap

open Hironaka Hironaka.BlowupSequences
  Hironaka HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps HironakaActualAnalyticSubspaceOpenRestriction
  HironakaReducedComplexAnalyticSpaces HironakaResolutionSpaceComplex
  HironakaSingularSubspaceBlowupLift SourceReducedComplexSpace
  EmbeddedBlowup EmbeddedBlowupUniversal EmbeddedBlowupComparison EmbeddedBlowupOpenRestriction

noncomputable section

variable {X : SourceReducedComplexSpace}

/-- The existing local embedding is the SAME original morphism, including
its entire sheaf map. -/
def chartMorphism (e : LocalEmbedding X) : ofClosedAnalytic e.carrier e.analytic ⟶ X :=
  ObjectProperty.homMk (Over.homMk e.map e.overPoint)

instance chartMorphism_isOpenImmersion (e : LocalEmbedding X) :
    LocallyRingedSpace.IsOpenImmersion (chartMorphism e).hom.left := e.isOpenImmersion

/-- The literal original base overlap, not a replacement model. -/
def overlapOpen (e f : LocalEmbedding X) : Opens e.carrier :=
  ⟨e.toPoint ⁻¹' range f.toPoint,
    f.isOpen_range_toPoint.preimage e.map.base.hom.continuous⟩

private theorem chartOpen_range (e f : LocalEmbedding X) (O : Opens e.ambient)
    (hO : (Subtype.val : e.carrier → e.ambient) ⁻¹' (O : Set e.ambient) =
      (overlapOpen e f : Set e.carrier)) :
    range ((ambientOpenInclusion e.analytic O ≫ chartMorphism e).hom.left.base) =
      range e.toPoint ∩ range f.toPoint := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    let z : e.carrier := ⟨y.val.val, y.property⟩
    refine ⟨⟨z, rfl⟩, ?_⟩
    exact (Set.ext_iff.mp hO z).mp y.val.property
  · rintro ⟨⟨y, rfl⟩, hy⟩
    have hyO : y.val ∈ O := (Set.ext_iff.mp hO y).mpr hy
    exact ⟨⟨⟨y.val, hyO⟩, y.property⟩, rfl⟩

private theorem sourceOpenIso_exists (A B Z : SourceReducedComplexSpace)
    (f : A ⟶ Z) (g : B ⟶ Z)
    [LocallyRingedSpace.IsOpenImmersion f.hom.left]
    [LocallyRingedSpace.IsOpenImmersion g.hom.left]
    (hr : range f.hom.left.base = range g.hom.left.base) :
    ∃ E : A ≅ B, E.hom ≫ g = f := by
  let L := LocallyRingedSpace.IsOpenImmersion.lift g.hom.left f.hom.left hr.subset
  have hL : L ≫ g.hom.left = f.hom.left :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac g.hom.left f.hom.left hr.subset
  let : IsIso (pullback.snd g.hom.left f.hom.left) :=
    LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset
      g.hom.left f.hom.left hr.subset
  let : LocallyRingedSpace.IsOpenImmersion L := by
    dsimp only [L, LocallyRingedSpace.IsOpenImmersion.lift]
    infer_instance
  have hsurj : Function.Surjective L.base := by
    rw [← Set.range_eq_univ,
      LocallyRingedSpace.IsOpenImmersion.lift_range g.hom.left f.hom.left hr.subset, hr]
    exact Set.preimage_range g.hom.left.base
  let : Epi L.base := (TopCat.epi_iff_surjective L.base).mpr hsurj
  let : IsIso L := LocallyRingedSpace.IsOpenImmersion.to_iso L
  have hp : L ≫ B.obj.hom = A.obj.hom := by
    rw [← Over.w g.hom, ← Category.assoc, hL]
    exact Over.w f.hom
  let E : A ≅ B := ObjectProperty.isoMk sourceReducedComplexSpaceProperty
    (Over.isoMk (asIso L) hp)
  refine ⟨E, ?_⟩
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact hL

private theorem open_density {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {C W : Set M} (hd : W ⊆ closure (W \ C)) (O : Opens M) :
    (Subtype.val : O → M) ⁻¹' W ⊆
      closure (((Subtype.val : O → M) ⁻¹' W) \ ((Subtype.val : O → M) ⁻¹' C)) := by
  have h := preimage_mono (f := (Subtype.val : O → M)) hd
  rw [(HironakaBaseChange.isOpenHoloEmbedding_val (n := n) O).preimage_closure,
    preimage_sdiff] at h
  exact h

/-- Ordinary original chart geometry constructs BOTH ambient overlap opens
and a full ORIGINAL base-model iso, carrying the SAME contained centres. -/
theorem exists_base_overlap_iso (e f : LocalEmbedding X)
    {C : Set e.ambient} {D : Set f.ambient} {Z : Set X.obj.left}
    (hC : ∀ x : e.carrier, x.val ∈ C ↔ e.toPoint x ∈ Z)
    (hD : ∀ x : f.carrier, x.val ∈ D ↔ f.toPoint x ∈ Z) :
    ∃ (O : Opens e.ambient) (P : Opens f.ambient)
      (_hO : (Subtype.val : e.carrier → e.ambient) ⁻¹' (O : Set e.ambient) =
        (overlapOpen e f : Set e.carrier))
      (_hP : (Subtype.val : f.carrier → f.ambient) ⁻¹' (P : Set f.ambient) =
        (overlapOpen f e : Set f.carrier))
      (E : ofClosedAnalytic ((Subtype.val : O → e.ambient) ⁻¹' e.carrier)
          (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val e.analytic O) ≅
        ofClosedAnalytic ((Subtype.val : P → f.ambient) ⁻¹' f.carrier)
          (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val f.analytic P)),
      E.hom ≫ (ambientOpenInclusion f.analytic P ≫ chartMorphism f) =
          ambientOpenInclusion e.analytic O ≫ chartMorphism e ∧
        ∀ x : ((Subtype.val : O → e.ambient) ⁻¹' e.carrier),
          x.val ∈ ((Subtype.val : O → e.ambient) ⁻¹' C) ↔
            (E.hom.hom.left.base x).val ∈ ((Subtype.val : P → f.ambient) ⁻¹' D) := by
  obtain ⟨O, hO⟩ := exists_ambient_open e.carrier (overlapOpen e f)
  obtain ⟨P, hP⟩ := exists_ambient_open f.carrier (overlapOpen f e)
  let a := ambientOpenInclusion e.analytic O ≫ chartMorphism e
  let b := ambientOpenInclusion f.analytic P ≫ chartMorphism f
  let : LocallyRingedSpace.IsOpenImmersion a.hom.left := by
    change LocallyRingedSpace.IsOpenImmersion
      (actualOpenSubspaceMap (n := e.dim) e.carrier O ≫ e.map)
    let : LocallyRingedSpace.IsOpenImmersion e.map := e.isOpenImmersion
    infer_instance
  let : LocallyRingedSpace.IsOpenImmersion b.hom.left := by
    change LocallyRingedSpace.IsOpenImmersion
      (actualOpenSubspaceMap (n := f.dim) f.carrier P ≫ f.map)
    let : LocallyRingedSpace.IsOpenImmersion f.map := f.isOpenImmersion
    infer_instance
  have hr : range a.hom.left.base = range b.hom.left.base :=
    (chartOpen_range e f O hO).trans ((inter_comm _ _).trans (chartOpen_range f e P hP).symm)
  obtain ⟨E, hE⟩ := sourceOpenIso_exists _ _ X a b hr
  refine ⟨O, P, hO, hP, E, hE, ?_⟩
  intro x
  let x₀ : e.carrier := ⟨x.val.val, x.property⟩
  let x₁ : f.carrier := ⟨(E.hom.hom.left.base x).val.val,
    (E.hom.hom.left.base x).property⟩
  have hp : f.toPoint x₁ = e.toPoint x₀ :=
    congrArg (fun H => H.hom.left.base x) hE
  change x₀.val ∈ C ↔ x₁.val ∈ D
  exact (hC x₀).trans ((iff_of_eq (congrArg (fun y => y ∈ Z) hp).symm).trans (hD x₁).symm)

/-- The ORIGINAL source overlaps of given local blowup models acquire a full
transition isomorphism internally, over the SAME original common space X. -/
theorem exists_overlap_transition (e f : LocalEmbedding X)
    {Y₀ Y₁ : Type} [TopologicalSpace Y₀] [TopologicalSpace Y₁]
    [ChartedSpace (ComplexModel e.dim) Y₀] [IsComplexManifold e.dim Y₀]
    [ChartedSpace (ComplexModel f.dim) Y₁] [IsComplexManifold f.dim Y₁]
    {C : Set e.ambient} {D : Set f.ambient} {π₀ : Y₀ → e.ambient} {π₁ : Y₁ → f.ambient}
    (hπ₀ : IsBlowupAlong e.dim C π₀) (hπ₁ : IsBlowupAlong f.dim D π₁)
    (hCW : C ⊆ e.carrier) (hDW : D ⊆ f.carrier)
    (hd₀ : e.carrier ⊆ closure (e.carrier \ C))
    (hd₁ : f.carrier ⊆ closure (f.carrier \ D)) {Z : Set X.obj.left}
    (hC : ∀ x : e.carrier, x.val ∈ C ↔ e.toPoint x ∈ Z)
    (hD : ∀ x : f.carrier, x.val ∈ D ↔ f.toPoint x ∈ Z) :
    ∃ T : restrictedClosedAnalytic
          (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
            hπ₀ e.analytic) (projectionOpen hπ₀ e.analytic (overlapOpen e f)) ≅
        restrictedClosedAnalytic
          (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
            hπ₁ f.analytic) (projectionOpen hπ₁ f.analytic (overlapOpen f e)),
      T.hom ≫ restrictionInclusion
          (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
            hπ₁ f.analytic) (projectionOpen hπ₁ f.analytic (overlapOpen f e)) ≫
            strictTransformMorphism hπ₁ f.analytic ≫ chartMorphism f =
        restrictionInclusion
          (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
            hπ₀ e.analytic) (projectionOpen hπ₀ e.analytic (overlapOpen e f)) ≫
            strictTransformMorphism hπ₀ e.analytic ≫ chartMorphism e := by
  obtain ⟨O, P, hO, hP, B, hB, hcentres⟩ := exists_base_overlap_iso e f hC hD
  let hOπ := BlowupBiholomorphismLift.isBlowupAlong_restrictMap hπ₀ O
  let hPπ := BlowupBiholomorphismLift.isBlowupAlong_restrictMap hπ₁ P
  let hOW := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val e.analytic O
  let hPW := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val f.analytic P
  obtain ⟨K, hK, _⟩ := exists_unique_strictTransform_iso hOπ hPπ hOW hPW B
    (preimage_mono (f := (Subtype.val : O → e.ambient)) hCW)
    (preimage_mono (f := (Subtype.val : P → f.ambient)) hDW)
    (open_density (n := e.dim) hd₀ O) (open_density (n := f.dim) hd₁ P) hcentres
  let I₀ := strictTransformRestrictionIso hπ₀ e.analytic (overlapOpen e f) O hO
  let I₁ := strictTransformRestrictionIso hπ₁ f.analytic (overlapOpen f e) P hP
  let T := I₀.symm ≪≫ K ≪≫ I₁
  let r₀ := restrictionInclusion
    (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
      hπ₀ e.analytic) (projectionOpen hπ₀ e.analytic (overlapOpen e f))
  let r₁ := restrictionInclusion
    (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
      hπ₁ f.analytic) (projectionOpen hπ₁ f.analytic (overlapOpen f e))
  let p₀ := strictTransformMorphism hπ₀ e.analytic
  let p₁ := strictTransformMorphism hπ₁ f.analytic
  let pO := strictTransformMorphism hOπ hOW
  let pP := strictTransformMorphism hPπ hPW
  let a₀ := ambientOpenInclusion e.analytic O
  let a₁ := ambientOpenInclusion f.analytic P
  have hs₀ : I₀.hom ≫ r₀ ≫ p₀ = pO ≫ a₀ := by
    rw [← Category.assoc, strictTransformRestrictionIso_inclusion]
    exact strictTransformOpenInclusion_projection hπ₀ e.analytic O
  have hs₁ : I₁.hom ≫ r₁ ≫ p₁ = pP ≫ a₁ := by
    rw [← Category.assoc, strictTransformRestrictionIso_inclusion]
    exact strictTransformOpenInclusion_projection hπ₁ f.analytic P
  have hI : I₀.hom ≫ T.hom = K.hom ≫ I₁.hom := by
    simp only [T, Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
  refine ⟨T, ?_⟩
  apply (cancel_epi I₀.hom).mp
  change I₀.hom ≫ (T.hom ≫ r₁ ≫ p₁ ≫ chartMorphism f) =
    I₀.hom ≫ (r₀ ≫ p₀ ≫ chartMorphism e)
  calc
    _ = (I₀.hom ≫ T.hom) ≫ r₁ ≫ p₁ ≫ chartMorphism f :=
      (Category.assoc _ _ _).symm
    _ = (K.hom ≫ I₁.hom) ≫ r₁ ≫ p₁ ≫ chartMorphism f := by rw [hI]
    _ = K.hom ≫ (I₁.hom ≫ r₁ ≫ p₁) ≫ chartMorphism f := by simp only [Category.assoc]
    _ = K.hom ≫ (pP ≫ a₁) ≫ chartMorphism f := by rw [hs₁]
    _ = (K.hom ≫ pP) ≫ (a₁ ≫ chartMorphism f) := by simp only [Category.assoc]
    _ = (pO ≫ B.hom) ≫ (a₁ ≫ chartMorphism f) := by rw [hK]
    _ = pO ≫ (B.hom ≫ (a₁ ≫ chartMorphism f)) := Category.assoc _ _ _
    _ = pO ≫ (a₀ ≫ chartMorphism e) := by rw [hB]
    _ = (I₀.hom ≫ r₀ ≫ p₀) ≫ chartMorphism e := by
      rw [hs₀]
      exact (Category.assoc _ _ _).symm
    _ = _ := by simp only [Category.assoc]

end

end Hironaka.Analytic.Unibranch.EmbeddedBlowupOverlap
