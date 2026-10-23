import DeJongAlterations.Projective
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! A genuinely finite relative graph internally produces the required actual affine open restriction. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace DeJongAlterations.StableModificationBridge.RelativeAffineNeighbourhood

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem finite_morphismRestrict_of_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U V : Y.Opens} (h : U ≤ V) (hf : IsFinite (f ∣_ V)) : IsFinite (f ∣_ U) := by
  have outer : IsPullback (f ∣_ U)
      (X.homOfLE (f.preimage_mono h) ≫ (f ⁻¹ᵁ V).ι)
      (Y.homOfLE h ≫ V.ι) f := by
    simpa only [Scheme.homOfLE_ι] using isPullback_morphismRestrict f U
  exact MorphismProperty.of_isPullback
    (outer.of_bot (morphismRestrict_homOfLE f U V h) (isPullback_morphismRestrict f V)).flip hf

/-- Actual finiteness of the relative graph INTERNALLY produces a genuine original-base
neighborhood and an actual open source on which the ORIGINAL projective map is affine. -/
theorem exists_affine_neighbourhood {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (β : X ⟶ Y) (p : Y ⟶ Spec (.of R)) (O : Y.Opens) {y : Y} (hyO : y ∈ O)
    {N : ℕ} (h : (β ⁻¹ᵁ O).toScheme ⟶ projectiveSpace R N)
    (hh : h ≫ projectiveSpaceStructure R N = (β ∣_ O) ≫ O.ι ≫ p)
    (E : O.toScheme.Opens) (hyE : (⟨y, hyO⟩ : O) ∈ E)
    (hfin : IsFinite ((pullback.lift (β ∣_ O) h hh.symm) ∣_
      ((pullback.fst (O.ι ≫ p) (projectiveSpaceStructure R N)) ⁻¹ᵁ E))) :
    ∃ W : Y.Opens, y ∈ W ∧ ∃ (Z : Scheme.{u}) (k : Z ⟶ (β ⁻¹ᵁ O).toScheme),
      IsOpenImmersion (k ≫ (β ⁻¹ᵁ O).ι) ∧
      Set.range (k ≫ (β ⁻¹ᵁ O).ι) = β ⁻¹' (W : Set Y) ∧ IsAffineHom (k ≫ h) := by
  obtain ⟨F, hF, hyF, hFE⟩ := exists_isAffineOpen_mem_and_subset
    (X := O.toScheme) (x := (⟨y, hyO⟩ : O)) (U := E) hyE
  let W := O.ι ''ᵁ F
  let pO := O.ι ≫ p
  let Ψ := pullback.lift (β ∣_ O) h hh.symm
  let π₁ := pullback.fst pO (projectiveSpaceStructure R N)
  let π₂ := pullback.snd pO (projectiveSpaceStructure R N)
  let V := π₁ ⁻¹ᵁ F
  let Z := (Ψ ⁻¹ᵁ V).toScheme
  let k : Z ⟶ (β ⁻¹ᵁ O).toScheme := (Ψ ⁻¹ᵁ V).ι
  have hΨβ : Ψ ≫ π₁ = β ∣_ O := pullback.lift_fst _ _ _
  have hΨh : Ψ ≫ π₂ = h := pullback.lift_snd _ _ _
  have hfinite : IsFinite (Ψ ∣_ V) :=
    finite_morphismRestrict_of_le Ψ (π₁.preimage_mono hFE) hfin
  let : IsFinite (Ψ ∣_ V) := hfinite
  let : IsAffine F.toScheme := hF
  let : IsAffineHom (F.ι ≫ pO) := inferInstance
  have H : IsPullback (π₁ ∣_ F) (V.ι ≫ π₂) (F.ι ≫ pO)
      (projectiveSpaceStructure R N) :=
    (isPullback_morphismRestrict π₁ F).paste_vert (IsPullback.of_hasPullback pO _)
  let : IsAffineHom (V.ι ≫ π₂) := MorphismProperty.of_isPullback H inferInstance
  have hcomp : (Ψ ∣_ V) ≫ (V.ι ≫ π₂) = k ≫ h := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hΨh]
  have haff : IsAffineHom (k ≫ h) := by rw [← hcomp]; infer_instance
  have hpre : Ψ ⁻¹' (V : Set _) =
      (β ∣_ O) ⁻¹' (F : Set O) := by
    ext x
    change π₁ (Ψ x) ∈ F ↔ (β ∣_ O) x ∈ F
    have ht := congrArg (fun f : (β ⁻¹ᵁ O).toScheme ⟶ O => f x) hΨβ
    change π₁ (Ψ x) = (β ∣_ O) x at ht
    rw [ht]
  refine ⟨W, ⟨⟨y, hyO⟩, hyF, rfl⟩, Z, k, inferInstance, ?_, haff⟩
  change Set.range ((β ⁻¹ᵁ O).ι ∘ k) = β ⁻¹' (W : Set Y)
  rw [Set.range_comp, Scheme.Opens.range_ι]
  change (β ⁻¹ᵁ O).ι '' (Ψ ⁻¹' (V : Set _)) = β ⁻¹' (W : Set Y)
  rw [hpre]
  exact Scheme.image_preimage_eq_of_isPullback (isPullback_morphismRestrict β O) (F : Set O)

end DeJongAlterations.StableModificationBridge.RelativeAffineNeighbourhood
