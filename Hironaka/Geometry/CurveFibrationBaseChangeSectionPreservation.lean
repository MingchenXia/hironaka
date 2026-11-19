import Hironaka.Geometry.CurveFibrationBaseChangeBoundaryComparison
import Hironaka.Geometry.FiniteBirationalNormalBoundarySections

/-!
# Closed sections survive the literal whole reduction after reduced base change

The actual base-change map of each ORIGINAL closed section factors through
the SAME whole reduction by reducedness of the new base. Its section
identity and exact support-image coverage retain the original maps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.CurveFibrationBaseChange

open FiniteBirationalNormal

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X S Y : Scheme.{u}}

/-- The actual section of the original Cartesian product, with its ORIGINAL coordinates. -/
def originalSectionBaseChange (f : X ⟶ S) (g : Y ⟶ S) (σ : S ⟶ X)
    (hσ : σ ≫ f = 𝟙 S) : Y ⟶ pullback f g :=
  pullback.lift (g ≫ σ) (𝟙 Y) (by simp [Category.assoc, hσ])

@[reassoc (attr := simp)]
theorem originalSectionBaseChange_fst (f : X ⟶ S) (g : Y ⟶ S) (σ : S ⟶ X)
    (hσ : σ ≫ f = 𝟙 S) : originalSectionBaseChange f g σ hσ ≫ pullback.fst f g = g ≫ σ := by
  simp [originalSectionBaseChange]

@[reassoc (attr := simp)]
theorem originalSectionBaseChange_snd (f : X ⟶ S) (g : Y ⟶ S) (σ : S ⟶ X)
    (hσ : σ ≫ f = 𝟙 S) : originalSectionBaseChange f g σ hσ ≫ pullback.snd f g = 𝟙 Y := by
  simp [originalSectionBaseChange]

/-- The literal second projection of the original section's base change is internally an isomorphism. -/
theorem originalSectionPullbackSnd_isIso (f : X ⟶ S) (g : Y ⟶ S) (σ : S ⟶ X)
    (hσ : σ ≫ f = 𝟙 S) : IsIso (pullback.snd (σ ≫ f) g) := by
  let : IsIso (σ ≫ f) := by rw [hσ]; infer_instance
  infer_instance

/-- The actual original closed-section base change equals the canonical section with its native source. -/
theorem originalSectionBaseChange_comparison (f : X ⟶ S) (g : Y ⟶ S) (σ : S ⟶ X)
    (hσ : σ ≫ f = 𝟙 S) :
    pullback.snd (σ ≫ f) g ≫ originalSectionBaseChange f g σ hσ =
      boundaryBaseChange σ f g := by
  have hr : pullback.fst (σ ≫ f) g = pullback.snd (σ ≫ f) g ≫ g := by
    simpa only [hσ, Category.comp_id] using (pullback.condition (f := σ ≫ f) (g := g))
  apply pullback.hom_ext
  · simp only [Category.assoc, originalSectionBaseChange_fst, boundaryBaseChange_fst, hr]
  · simp only [Category.assoc, originalSectionBaseChange_snd, Category.comp_id,
      boundaryBaseChange_snd]

/-- The actual original base-changed section has precisely its original image inverse image. -/
theorem originalSectionBaseChange_range (f : X ⟶ S) (g : Y ⟶ S) (σ : S ⟶ X)
    (hσ : σ ≫ f = 𝟙 S) :
    Set.range (originalSectionBaseChange f g σ hσ) = (pullback.fst f g) ⁻¹' Set.range σ := by
  let : IsIso (pullback.snd (σ ≫ f) g) := originalSectionPullbackSnd_isIso f g σ hσ
  rw [← boundaryBaseChange_range σ f g, ← originalSectionBaseChange_comparison f g σ hσ]
  change Set.range (originalSectionBaseChange f g σ hσ) =
    Set.range (originalSectionBaseChange f g σ hσ ∘ pullback.snd (σ ≫ f) g)
  rw [Set.range_comp, (pullback.snd (σ ≫ f) g).surjective.range_eq, Set.image_univ]

/-- Actual original section closedness survives on the SAME original Cartesian product. -/
theorem originalSectionBaseChange_isClosedImmersion (f : X ⟶ S) (g : Y ⟶ S) (σ : S ⟶ X)
    [IsClosedImmersion σ] (hσ : σ ≫ f = 𝟙 S) :
    IsClosedImmersion (originalSectionBaseChange f g σ hσ) := by
  let : IsIso (pullback.snd (σ ≫ f) g) := originalSectionPullbackSnd_isIso f g σ hσ
  have he : originalSectionBaseChange f g σ hσ =
      inv (pullback.snd (σ ≫ f) g) ≫ boundaryBaseChange σ f g := by
    apply (cancel_epi (pullback.snd (σ ≫ f) g)).1
    simp only [IsIso.hom_inv_id_assoc, originalSectionBaseChange_comparison]
  rw [he]
  infer_instance

/-- The actual original section factors through the SAME literal whole reduction, by new-base reducedness. -/
def reducedOriginalSection [IsReduced Y] (f : X ⟶ S) (g : Y ⟶ S) (σ : S ⟶ X)
    (hσ : σ ≫ f = 𝟙 S) : Y ⟶ reducedPullback f g :=
  IsClosedImmersion.lift (reductionι f g) (originalSectionBaseChange f g σ hσ)
    (kernel_le_of_reduced_range _ _ (by
      rw [(reductionι f g).surjective.range_eq]
      exact Set.subset_univ _))

@[reassoc (attr := simp)]
theorem reducedOriginalSection_fac [IsReduced Y] (f : X ⟶ S) (g : Y ⟶ S) (σ : S ⟶ X)
    (hσ : σ ≫ f = 𝟙 S) :
    reducedOriginalSection f g σ hσ ≫ reductionι f g = originalSectionBaseChange f g σ hσ :=
  IsClosedImmersion.lift_fac _ _ _

/-- The actual reduced section retains its ORIGINAL section identity. -/
theorem reducedOriginalSection_snd [IsReduced Y] (f : X ⟶ S) (g : Y ⟶ S) (σ : S ⟶ X)
    (hσ : σ ≫ f = 𝟙 S) :
    reducedOriginalSection f g σ hσ ≫ (reductionι f g ≫ pullback.snd f g) = 𝟙 Y := by
  rw [← Category.assoc, reducedOriginalSection_fac, originalSectionBaseChange_snd]

/-- The actual reduced section's image is exactly its ORIGINAL image inverse image. -/
theorem reducedOriginalSection_range [IsReduced Y] (f : X ⟶ S) (g : Y ⟶ S) (σ : S ⟶ X)
    (hσ : σ ≫ f = 𝟙 S) :
    Set.range (reducedOriginalSection f g σ hσ) =
      (reductionι f g ≫ pullback.fst f g) ⁻¹' Set.range σ := by
  have hr := originalSectionBaseChange_range f g σ hσ
  ext t
  constructor
  · rintro ⟨y, rfl⟩
    have h : originalSectionBaseChange f g σ hσ y ∈ Set.range (originalSectionBaseChange f g σ hσ) :=
      ⟨y, rfl⟩
    rw [hr] at h
    have hf := congrArg (fun m => m y) (reducedOriginalSection_fac f g σ hσ)
    change pullback.fst f g (reductionι f g (reducedOriginalSection f g σ hσ y)) ∈ Set.range σ
    simpa only [Scheme.Hom.comp_apply] using hf ▸ h
  · intro ht
    have ht' : reductionι f g t ∈ Set.range (originalSectionBaseChange f g σ hσ) := by
      rw [hr]
      exact ht
    obtain ⟨y, hy⟩ := ht'
    refine ⟨y, (reductionι f g).isEmbedding.injective ?_⟩
    have hf := congrArg (fun m => m y) (reducedOriginalSection_fac f g σ hσ)
    simpa only [Scheme.Hom.comp_apply] using hf.trans hy

/-- Original actual section closedness survives the SAME whole reduction. -/
theorem reducedOriginalSection_isClosedImmersion [IsReduced Y]
    (f : X ⟶ S) (g : Y ⟶ S) (σ : S ⟶ X) [IsClosedImmersion σ]
    (hσ : σ ≫ f = 𝟙 S) : IsClosedImmersion (reducedOriginalSection f g σ hσ) := by
  let : IsClosedImmersion (reducedOriginalSection f g σ hσ ≫ reductionι f g) := by
    rw [reducedOriginalSection_fac]
    exact originalSectionBaseChange_isClosedImmersion f g σ hσ
  exact IsClosedImmersion.of_comp _ (reductionι f g)

/-- Source4.16 final sentence: ALL original closed sections retain their complete support coverage. -/
theorem wholeReduction_preserves_boundary_sections [IsReduced Y]
    (f : X ⟶ S) (g : Y ⟶ S) (D : X.IdealSheafData)
    {ι : Type u} [Finite ι] (σ : ι → (S ⟶ X))
    (hσ : ∀ i, σ i ≫ f = 𝟙 S) [∀ i, IsClosedImmersion (σ i)]
    (hcover : ⋃ i, Set.range (σ i) = (D.support : Set X)) :
    ∃ τ : ι → (Y ⟶ reducedPullback f g),
      (∀ i, τ i ≫ (reductionι f g ≫ pullback.snd f g) = 𝟙 Y ∧ IsClosedImmersion (τ i)) ∧
      ⋃ i, Set.range (τ i) =
        ((D.comap (reductionι f g ≫ pullback.fst f g)).support : Set (reducedPullback f g)) := by
  let τ : ι → (Y ⟶ reducedPullback f g) := fun i => reducedOriginalSection f g (σ i) (hσ i)
  refine ⟨τ, fun i => ⟨reducedOriginalSection_snd f g (σ i) (hσ i),
    reducedOriginalSection_isClosedImmersion f g (σ i) (hσ i)⟩, ?_⟩
  simp only [τ, reducedOriginalSection_range, ← Set.preimage_iUnion, hcover,
    Scheme.IdealSheafData.support_comap, Closeds.coe_preimage]

end Hironaka.Geometry.CurveFibrationBaseChange
