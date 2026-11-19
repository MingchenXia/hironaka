import Hironaka.Resolution.HironakaActualRelativeStandardnessPivotPriority
import Hironaka.Resolution.HironakaActualFormalStrictGenerators

/-!
# Actual whole point-chart transport under stable pivot renaming

These are identities of the actual substitution, actual normalized members,
and actual entire strict ideals. The promoted HS equality is derived from the
original one through genuine variable-ideal-preserving algebra equivalences.
-/

set_option autoImplicit false
open Set Classical

namespace Hironaka.HironakaActualRelativeStandardnessPointRename

noncomputable section

open HironakaRelativeNormalMonomialBasis HironakaActualOriginalFormalHSTransfer
  HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
  HironakaActualFormalStrictGenerators HironakaActualPointChartTransition
  HironakaActualRelativeStandardnessPivotPriority

variable {n : ℕ}

private theorem pivot_at_zero (f : Fin (n + 1)) : pivotFirstEquiv f f = 0 := by
  simp only [pivotFirstEquiv, Equiv.trans_apply, finSuccEquiv'_at, finSuccEquiv_symm_none]

private theorem point_ideal_eq_variables :
    actualFormalCoordinateIdeal (n + 1) Set.univ = genuineFormalVariables (n + 1) := by
  simp only [actualFormalCoordinateIdeal, Set.image_univ, genuineFormalVariables]

private theorem point_power_map (f : Fin (n + 1)) (μ : ℕ) :
    Ideal.map (pivotFirstRename f).toRingHom (actualFormalCoordinateIdeal (n + 1) Set.univ ^ μ) =
      actualFormalCoordinateIdeal (n + 1) Set.univ ^ μ := by
  rw [point_ideal_eq_variables, Ideal.map_pow]
  exact congrArg (fun I : Ideal (MvPowerSeries (Fin (n + 1)) ℂ) => I ^ μ)
    (map_genuineFormalVariables_rename (pivotFirstEquiv f))

/-- Both entire point-power directions follow from the genuine rename equivalence. -/
theorem mem_point_power_iff_pivotFirstRename (f : Fin (n + 1)) (μ : ℕ)
    (F : MvPowerSeries (Fin (n + 1)) ℂ) :
    pivotFirstRename f F ∈ actualFormalCoordinateIdeal (n + 1) Set.univ ^ μ ↔
      F ∈ actualFormalCoordinateIdeal (n + 1) Set.univ ^ μ := by
  constructor
  · intro h
    rw [← point_power_map f μ] at h
    obtain ⟨G, hG, hGF⟩ := (Ideal.mem_map_iff_of_surjective (pivotFirstRename f).toRingHom
      (MvPowerSeries.renameEquiv ℂ (pivotFirstEquiv f)).surjective).mp h
    have heq : G = F := (MvPowerSeries.renameEquiv ℂ (pivotFirstEquiv f)).injective hGF
    rwa [heq] at hG
  · intro h
    have h' := Ideal.mem_map_of_mem (pivotFirstRename f).toRingHom h
    rwa [point_power_map f μ] at h'

private theorem point_coordinate_rename (f i : Fin (n + 1)) :
    pivotFirstRename f (actualFormalBlowupCoordinates Set.univ f (fun _ => 0) i) =
      actualFormalBlowupCoordinates Set.univ 0 (fun _ => 0) (pivotFirstEquiv f i) := by
  by_cases hi : i = f
  · subst i
    simp only [actualFormalBlowupCoordinates, Set.mem_univ, if_true,
      pivotFirstRename, MvPowerSeries.rename_X, pivot_at_zero]
  · have hpi : pivotFirstEquiv f i ≠ 0 := by
      intro h
      exact hi ((pivotFirstEquiv f).injective (h.trans (pivot_at_zero f).symm))
    simp only [actualFormalBlowupCoordinates, Set.mem_univ, if_true, if_neg hi,
      if_neg hpi, map_zero, zero_add, map_mul, pivotFirstRename,
      MvPowerSeries.rename_X, pivot_at_zero]

/-- The two actual whole substitutions commute, by their genuine substitution
composition theorem and literal coordinate images. -/
theorem pivotFirstRename_point_blowup (f : Fin (n + 1))
    (F : MvPowerSeries (Fin (n + 1)) ℂ) :
    pivotFirstRename f (actualFormalBlowup Set.univ f (fun _ => 0) F) =
      actualFormalBlowup Set.univ 0 (fun _ => 0) (pivotFirstRename f F) := by
  let p := pivotFirstEquiv f
  let af := actualFormalBlowupCoordinates Set.univ f (fun _ => 0)
  let a0 := actualFormalBlowupCoordinates Set.univ (0 : Fin (n + 1)) (fun _ => 0)
  have hf := MvPowerSeries.hasSubst_of_constantCoeff_zero
    (actualFormalBlowupCoordinates_constant_zero Set.univ f (fun _ => 0))
  have h0 := MvPowerSeries.hasSubst_of_constantCoeff_zero
    (actualFormalBlowupCoordinates_constant_zero Set.univ (0 : Fin (n + 1)) (fun _ => 0))
  have hp := MvPowerSeries.HasSubst.X_comp (R := ℂ) p
  have hcoords : (fun i : Fin (n + 1) => MvPowerSeries.subst
        ((MvPowerSeries.X : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) ℂ) ∘ p) (af i)) =
      (fun i : Fin (n + 1) => MvPowerSeries.subst a0
        (MvPowerSeries.X (p i) : MvPowerSeries (Fin (n + 1)) ℂ)) := by
    funext i
    rw [← MvPowerSeries.rename_eq_subst, MvPowerSeries.subst_X h0]
    exact point_coordinate_rename f i
  simp only [pivotFirstRename, actualFormalBlowup, MvPowerSeries.substAlgHom_apply]
  change MvPowerSeries.rename p (MvPowerSeries.subst af F) =
    MvPowerSeries.subst a0 (MvPowerSeries.rename p F)
  rw [MvPowerSeries.rename_eq_subst, MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply hf hp, MvPowerSeries.subst_comp_subst_apply hp h0, hcoords]
  rfl

/-- Renaming the true exceptional identity gives the SAME actual normalized
member with its unchanged normalization degree. -/
theorem pivotFirstRename_normalized_member (f : Fin (n + 1)) (μ : ℕ)
    (F : MvPowerSeries (Fin (n + 1)) ℂ)
    (hF : F ∈ actualFormalCoordinateIdeal (n + 1) Set.univ ^ μ) :
    pivotFirstRename f (actualNormalizedFormalMember Set.univ f (mem_univ f) (fun _ => 0) μ F hF) =
      actualNormalizedFormalMember Set.univ 0 (mem_univ 0) (fun _ => 0) μ (pivotFirstRename f F)
        ((mem_point_power_iff_pivotFirstRename f μ F).mpr hF) := by
  apply actualNormalizedFormalMember_unique
  calc
    _ = pivotFirstRename f ((MvPowerSeries.X f) ^ μ *
        actualNormalizedFormalMember Set.univ f (mem_univ f) (fun _ => 0) μ F hF) := by
      rw [map_mul, map_pow, pivotFirstRename, MvPowerSeries.rename_X, pivot_at_zero]
    _ = pivotFirstRename f (actualFormalBlowup Set.univ f (fun _ => 0) F) := by
      rw [actualNormalizedFormalMember_spec]
    _ = _ := pivotFirstRename_point_blowup f F

/-- Both whole strict-ideal inclusions use ALL genuine normalized original
members and actual surjectivity; no fixed presentation equality is assumed. -/
theorem map_point_strict_pivotFirst
    (K : Ideal (MvPowerSeries (Fin (n + 1)) ℂ)) (f : Fin (n + 1)) :
    Ideal.map (pivotFirstRename f).toRingHom
      (actualFormalStrictTransform K Set.univ f (mem_univ f) (fun _ => 0)) =
        actualFormalStrictTransform (Ideal.map (pivotFirstRename f).toRingHom K)
          Set.univ 0 (mem_univ 0) (fun _ => 0) := by
  rw [actualFormalStrictTransform_eq_normalizedOriginalMemberIdeal,
    actualFormalStrictTransform_eq_normalizedOriginalMemberIdeal]
  apply le_antisymm
  · rw [actualNormalizedOriginalMemberIdeal, Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro G ⟨H, ⟨μ, F, hFK, hF, rfl⟩, rfl⟩
    change pivotFirstRename f
      (actualNormalizedFormalMember Set.univ f (mem_univ f) (fun _ => 0) μ F hF) ∈ _
    rw [pivotFirstRename_normalized_member f μ F hF]
    exact Ideal.subset_span ⟨μ, pivotFirstRename f F, Ideal.mem_map_of_mem _ hFK,
      (mem_point_power_iff_pivotFirstRename f μ F).mpr hF, rfl⟩
  · rw [actualNormalizedOriginalMemberIdeal]
    apply Ideal.span_le.mpr
    rintro G ⟨μ, H, hHK, hH, rfl⟩
    obtain ⟨F, hFK, rfl⟩ := (Ideal.mem_map_iff_of_surjective (pivotFirstRename f).toRingHom
      (MvPowerSeries.renameEquiv ℂ (pivotFirstEquiv f)).surjective).mp hHK
    have hF := (mem_point_power_iff_pivotFirstRename f μ F).mp hH
    change actualNormalizedFormalMember Set.univ (0 : Fin (n + 1)) (mem_univ 0)
      (fun _ => 0) μ (pivotFirstRename f F)
        ((mem_point_power_iff_pivotFirstRename f μ F).mpr hF) ∈ _
    rw [← pivotFirstRename_normalized_member f μ F hF]
    exact Ideal.mem_map_of_mem (pivotFirstRename f).toRingHom
      (Ideal.subset_span ⟨μ, F, hFK, hF, rfl⟩)

/-- The promoted model's entire strict/source HS equality is produced from the
original model's equality and genuine whole ideal/jet transport. -/
theorem point_strict_hs_eq_after_pivotFirst
    (K : Ideal (MvPowerSeries (Fin (n + 1)) ℂ)) (f : Fin (n + 1))
    (hHS : ∀ q, genuineFormalHilbertSamuelValue (n + 1)
      (actualFormalStrictTransform K Set.univ f (mem_univ f) (fun _ => 0)) q =
        genuineFormalHilbertSamuelValue (n + 1) K q) :
    ∀ q, genuineFormalHilbertSamuelValue (n + 1)
      (actualFormalStrictTransform (Ideal.map (pivotFirstRename f).toRingHom K)
        Set.univ 0 (mem_univ 0) (fun _ => 0)) q =
          genuineFormalHilbertSamuelValue (n + 1) (Ideal.map (pivotFirstRename f).toRingHom K) q := by
  intro q
  calc
    _ = genuineFormalHilbertSamuelValue (n + 1) (Ideal.map (pivotFirstRename f).toRingHom
        (actualFormalStrictTransform K Set.univ f (mem_univ f) (fun _ => 0))) q := by
      rw [map_point_strict_pivotFirst]
    _ = genuineFormalHilbertSamuelValue (n + 1)
        (actualFormalStrictTransform K Set.univ f (mem_univ f) (fun _ => 0)) q :=
      (genuineFormalHilbertSamuelValue_map_formalAlgEquiv
        (MvPowerSeries.renameEquiv ℂ (pivotFirstEquiv f))
        (map_genuineFormalVariables_rename (pivotFirstEquiv f)) _ q).symm
    _ = genuineFormalHilbertSamuelValue (n + 1) K q := hHS q
    _ = _ := genuineFormalHilbertSamuelValue_map_formalAlgEquiv
      (MvPowerSeries.renameEquiv ℂ (pivotFirstEquiv f))
      (map_genuineFormalVariables_rename (pivotFirstEquiv f)) K q

end

end Hironaka.HironakaActualRelativeStandardnessPointRename
