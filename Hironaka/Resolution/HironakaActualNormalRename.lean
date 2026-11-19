import Hironaka.Resolution.HironakaActualRelativeStandardnessPointRename

/-! Genuine normal-chart naturality under a coordinate permutation preserving
the selected normal set. All equalities concern the entire substitution and
the whole strict ideal. The final adapted-chart consumer supplies the set
preservation condition internally; this lower lemma does not assert that an
arbitrary permutation preserves a degree-lex diagram. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualNormalRename
noncomputable section
open HironakaRelativeNormalMonomialBasis HironakaActualOriginalFormalHSTransfer
  HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
  HironakaActualFormalStrictGenerators HironakaActualRelativeStandardnessPivotPriority
  HironakaActualPointChartTransition
variable {n : ℕ}

private theorem map_coordinateIdeal_rename
    (p : Fin (n + 1) ≃ Fin (n + 1)) (A : Set (Fin (n + 1)))
    (hA : ∀ i, p i ∈ A ↔ i ∈ A) :
    Ideal.map (MvPowerSeries.rename p).toRingHom (actualFormalCoordinateIdeal (n + 1) A) =
      actualFormalCoordinateIdeal (n + 1) A := by
  apply le_antisymm
  · rw [actualFormalCoordinateIdeal, Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro F ⟨G, ⟨i, hi, rfl⟩, rfl⟩
    change MvPowerSeries.rename p (MvPowerSeries.X i) ∈ _
    rw [MvPowerSeries.rename_X]
    exact Ideal.subset_span ⟨p i, (hA i).mpr hi, rfl⟩
  · apply Ideal.span_le.mpr
    rintro F ⟨i, hi, rfl⟩
    have hpi : p.symm i ∈ A := (hA (p.symm i)).mp (by simpa only [p.apply_symm_apply] using hi)
    have hm := Ideal.mem_map_of_mem (MvPowerSeries.rename p).toRingHom
      (Ideal.subset_span (show MvPowerSeries.X (p.symm i) ∈
        (MvPowerSeries.X : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) ℂ) '' A from
          ⟨p.symm i, hpi, rfl⟩))
    change MvPowerSeries.rename p (MvPowerSeries.X (p.symm i)) ∈ _ at hm
    change MvPowerSeries.X i ∈ Ideal.map (MvPowerSeries.rename p).toRingHom
      (actualFormalCoordinateIdeal (n + 1) A)
    simpa only [actualFormalCoordinateIdeal, MvPowerSeries.rename_X, p.apply_symm_apply] using hm

/-- The genuine inverse rename reflects every entire selected-coordinate power. -/
theorem mem_coordinate_power_iff_rename
    (p : Fin (n + 1) ≃ Fin (n + 1)) (A : Set (Fin (n + 1)))
    (hA : ∀ i, p i ∈ A ↔ i ∈ A) (μ : ℕ)
    (F : MvPowerSeries (Fin (n + 1)) ℂ) :
    MvPowerSeries.rename p F ∈ actualFormalCoordinateIdeal (n + 1) A ^ μ ↔
      F ∈ actualFormalCoordinateIdeal (n + 1) A ^ μ := by
  have hmap : Ideal.map (MvPowerSeries.rename p).toRingHom
      (actualFormalCoordinateIdeal (n + 1) A ^ μ) =
        actualFormalCoordinateIdeal (n + 1) A ^ μ := by
    rw [Ideal.map_pow, map_coordinateIdeal_rename p A hA]
  constructor
  · intro h
    rw [← hmap] at h
    obtain ⟨G, hG, hGF⟩ := (Ideal.mem_map_iff_of_surjective (MvPowerSeries.rename p).toRingHom
      (MvPowerSeries.renameEquiv ℂ p).surjective).mp h
    have heq : G = F := (MvPowerSeries.renameEquiv ℂ p).injective hGF
    rwa [heq] at hG
  · intro h
    have hm := Ideal.mem_map_of_mem (MvPowerSeries.rename p).toRingHom h
    rwa [hmap] at hm

private theorem normal_coordinate_rename
    (p : Fin (n + 1) ≃ Fin (n + 1)) (A : Set (Fin (n + 1)))
    (hA : ∀ i, p i ∈ A ↔ i ∈ A) (e : Fin (n + 1))
    (b : Fin (n + 1) → ℂ) (i : Fin (n + 1)) :
    MvPowerSeries.rename p (actualFormalBlowupCoordinates A e b i) =
      actualFormalBlowupCoordinates A (p e) (fun j => b (p.symm j)) (p i) := by
  by_cases hi : i ∈ A
  · have hpi := (hA i).mpr hi
    by_cases hie : i = e
    · subst i
      simp only [actualFormalBlowupCoordinates, if_pos hi, if_pos hpi, if_true,
        MvPowerSeries.rename_X]
    · have hpie : p i ≠ p e := fun h => hie (p.injective h)
      simp only [actualFormalBlowupCoordinates, if_pos hi, if_pos hpi, if_neg hie,
        if_neg hpie, map_mul, map_add, MvPowerSeries.rename_C, MvPowerSeries.rename_X,
        p.symm_apply_apply]
  · have hpi : p i ∉ A := fun h => hi ((hA i).mp h)
    simp only [actualFormalBlowupCoordinates, if_neg hi, if_neg hpi, MvPowerSeries.rename_X]

/-- Literal coordinate equality is extended to ALL formal series by the true
whole substitution-composition theorem. -/
theorem rename_actual_normal_blowup
    (p : Fin (n + 1) ≃ Fin (n + 1)) (A : Set (Fin (n + 1)))
    (hA : ∀ i, p i ∈ A ↔ i ∈ A) (e : Fin (n + 1))
    (b : Fin (n + 1) → ℂ) (F : MvPowerSeries (Fin (n + 1)) ℂ) :
    MvPowerSeries.rename p (actualFormalBlowup A e b F) =
      actualFormalBlowup A (p e) (fun j => b (p.symm j)) (MvPowerSeries.rename p F) := by
  let c := actualFormalBlowupCoordinates A e b
  let d := actualFormalBlowupCoordinates A (p e) (fun j => b (p.symm j))
  have hc := MvPowerSeries.hasSubst_of_constantCoeff_zero
    (actualFormalBlowupCoordinates_constant_zero A e b)
  have hd := MvPowerSeries.hasSubst_of_constantCoeff_zero
    (actualFormalBlowupCoordinates_constant_zero A (p e) (fun j => b (p.symm j)))
  have hp := MvPowerSeries.HasSubst.X_comp (R := ℂ) p
  have hcoords : (fun i : Fin (n + 1) => MvPowerSeries.subst
        ((MvPowerSeries.X : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) ℂ) ∘ p) (c i)) =
      (fun i : Fin (n + 1) => MvPowerSeries.subst d
        (MvPowerSeries.X (p i) : MvPowerSeries (Fin (n + 1)) ℂ)) := by
    funext i
    rw [← MvPowerSeries.rename_eq_subst, MvPowerSeries.subst_X hd]
    exact normal_coordinate_rename p A hA e b i
  simp only [actualFormalBlowup, MvPowerSeries.substAlgHom_apply]
  change MvPowerSeries.rename p (MvPowerSeries.subst c F) =
    MvPowerSeries.subst d (MvPowerSeries.rename p F)
  rw [MvPowerSeries.rename_eq_subst, MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply hc hp, MvPowerSeries.subst_comp_subst_apply hp hd, hcoords]
  rfl

/-- The unchanged exceptional product identifies the SAME renamed numerator's
actual normalized member, with its unchanged mark. -/
theorem rename_actual_normal_normalized_member
    (p : Fin (n + 1) ≃ Fin (n + 1)) (A : Set (Fin (n + 1)))
    (hA : ∀ i, p i ∈ A ↔ i ∈ A) (e : Fin (n + 1)) (he : e ∈ A)
    (b : Fin (n + 1) → ℂ) (μ : ℕ) (F : MvPowerSeries (Fin (n + 1)) ℂ)
    (hF : F ∈ actualFormalCoordinateIdeal (n + 1) A ^ μ) :
    MvPowerSeries.rename p (actualNormalizedFormalMember A e he b μ F hF) =
      actualNormalizedFormalMember A (p e) ((hA e).mpr he) (fun j => b (p.symm j)) μ
        (MvPowerSeries.rename p F) ((mem_coordinate_power_iff_rename p A hA μ F).mpr hF) := by
  apply actualNormalizedFormalMember_unique
  calc
    _ = MvPowerSeries.rename p ((MvPowerSeries.X e) ^ μ *
        actualNormalizedFormalMember A e he b μ F hF) := by
      rw [map_mul, map_pow, MvPowerSeries.rename_X]
    _ = MvPowerSeries.rename p (actualFormalBlowup A e b F) := by
      rw [actualNormalizedFormalMember_spec]
    _ = _ := rename_actual_normal_blowup p A hA e b F

/-- Both WHOLE strict-ideal inclusions use all normalized original members and
genuine inverse source preimages with reflected coordinate powers. -/
theorem map_actual_normal_strict_rename
    (K : Ideal (MvPowerSeries (Fin (n + 1)) ℂ))
    (p : Fin (n + 1) ≃ Fin (n + 1)) (A : Set (Fin (n + 1)))
    (hA : ∀ i, p i ∈ A ↔ i ∈ A) (e : Fin (n + 1)) (he : e ∈ A)
    (b : Fin (n + 1) → ℂ) :
    Ideal.map (MvPowerSeries.rename p).toRingHom (actualFormalStrictTransform K A e he b) =
      actualFormalStrictTransform (Ideal.map (MvPowerSeries.rename p).toRingHom K)
        A (p e) ((hA e).mpr he) (fun j => b (p.symm j)) := by
  rw [actualFormalStrictTransform_eq_normalizedOriginalMemberIdeal,
    actualFormalStrictTransform_eq_normalizedOriginalMemberIdeal]
  apply le_antisymm
  · rw [actualNormalizedOriginalMemberIdeal, Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro G ⟨H, ⟨μ, F, hFK, hF, rfl⟩, rfl⟩
    change MvPowerSeries.rename p (actualNormalizedFormalMember A e he b μ F hF) ∈ _
    rw [rename_actual_normal_normalized_member p A hA e he b μ F hF]
    exact Ideal.subset_span ⟨μ, MvPowerSeries.rename p F, Ideal.mem_map_of_mem _ hFK,
      (mem_coordinate_power_iff_rename p A hA μ F).mpr hF, rfl⟩
  · rw [actualNormalizedOriginalMemberIdeal]
    apply Ideal.span_le.mpr
    rintro G ⟨μ, H, hHK, hH, rfl⟩
    obtain ⟨F, hFK, rfl⟩ := (Ideal.mem_map_iff_of_surjective (MvPowerSeries.rename p).toRingHom
      (MvPowerSeries.renameEquiv ℂ p).surjective).mp hHK
    have hF := (mem_coordinate_power_iff_rename p A hA μ F).mp hH
    change actualNormalizedFormalMember A (p e) ((hA e).mpr he) (fun j => b (p.symm j)) μ
      (MvPowerSeries.rename p F) ((mem_coordinate_power_iff_rename p A hA μ F).mpr hF) ∈ _
    rw [← rename_actual_normal_normalized_member p A hA e he b μ F hF]
    exact Ideal.mem_map_of_mem (MvPowerSeries.rename p).toRingHom
      (Ideal.subset_span ⟨μ, F, hFK, hF, rfl⟩)

/-- The original genuine closed-point equality produces the renamed one. No
new-chart numerical or jet certificate is a hypothesis. -/
theorem normal_strict_hs_eq_rename
    (K : Ideal (MvPowerSeries (Fin (n + 1)) ℂ))
    (p : Fin (n + 1) ≃ Fin (n + 1)) (A : Set (Fin (n + 1)))
    (hA : ∀ i, p i ∈ A ↔ i ∈ A) (e : Fin (n + 1)) (he : e ∈ A)
    (b : Fin (n + 1) → ℂ)
    (hHS : ∀ ℓ, genuineFormalHilbertSamuelValue (n + 1)
      (actualFormalStrictTransform K A e he b) ℓ = genuineFormalHilbertSamuelValue (n + 1) K ℓ) :
    ∀ ℓ, genuineFormalHilbertSamuelValue (n + 1)
      (actualFormalStrictTransform (Ideal.map (MvPowerSeries.rename p).toRingHom K)
        A (p e) ((hA e).mpr he) (fun j => b (p.symm j))) ℓ =
      genuineFormalHilbertSamuelValue (n + 1) (Ideal.map (MvPowerSeries.rename p).toRingHom K) ℓ := by
  intro ℓ
  calc
    _ = genuineFormalHilbertSamuelValue (n + 1)
        (Ideal.map (MvPowerSeries.rename p).toRingHom (actualFormalStrictTransform K A e he b)) ℓ := by
      rw [map_actual_normal_strict_rename K p A hA e he b]
    _ = genuineFormalHilbertSamuelValue (n + 1) (actualFormalStrictTransform K A e he b) ℓ :=
      (genuineFormalHilbertSamuelValue_map_formalAlgEquiv (MvPowerSeries.renameEquiv ℂ p)
        (map_genuineFormalVariables_rename p) _ ℓ).symm
    _ = genuineFormalHilbertSamuelValue (n + 1) K ℓ := hHS ℓ
    _ = _ := genuineFormalHilbertSamuelValue_map_formalAlgEquiv (MvPowerSeries.renameEquiv ℂ p)
      (map_genuineFormalVariables_rename p) K ℓ

end
end Hironaka.HironakaActualNormalRename
