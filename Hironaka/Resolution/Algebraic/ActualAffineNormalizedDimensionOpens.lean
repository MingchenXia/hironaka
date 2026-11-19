import Hironaka.Resolution.Algebraic.ActualGlobalSeparationAffineCharts
import Hironaka.Scheme.BlowUp.AffineBlowUp.Exceptional

/-!
# Actual normalized opens equal the frozen affine dimension group opens

Source-first proof: `actual-affine-normalized-dimension-opens-20261102.tex`.
The original actual degree-one charts compute every normalized ideal;
the real affine chart atlas then identifies the global piece restrictions.
Global purity and the genuine pure padded input remain separate consumers.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.IdealSheafData
universe u

namespace Hironaka.Resolution.Algebraic.ActualAffineNormalizedDimensionOpens

noncomputable section
open ActualDimensionGroupBlowup ActualGlobalDimensionIdealAffineComparison

section Affine
variable (R : Type u) [CommRing R] [IsReduced R]

private abbrev centre := dimensionSeparationIdeal R

private abbrev chartElement (e : dimensionIndex R) (a : complementIdeal R (dimensionGroupIdeal R) e) :
    centre R := ⟨a.val, (show complementIdeal R (dimensionGroupIdeal R) e ≤ centre R from
      le_iSup_of_le e le_rfl) a.property⟩

private abbrev chartRing (e : dimensionIndex R) (a : complementIdeal R (dimensionGroupIdeal R) e) :=
  affineBlowUpAlgebra (centre R) a.val

private abbrev groupChart (e : dimensionIndex R) (a : complementIdeal R (dimensionGroupIdeal R) e) :=
  affineBlowUp.chart (centre R) (chartElement R e a)

omit [IsReduced R] in
theorem complementImage_selected (e : dimensionIndex R)
    (a : complementIdeal R (dimensionGroupIdeal R) e) :
    (dimensionComplement R e.val).map (algebraMap R (chartRing R e a)) =
      Ideal.span {algebraMap R (chartRing R e a) a.val} := by
  have hI : (centre R).map (algebraMap R (chartRing R e a)) =
      Ideal.span {algebraMap R (chartRing R e a) a.val} :=
    affineBlowUpAlgebra.map_algebraMap_eq_span_singleton (chartElement R e a).property
  rw [dimensionComplement_eq_native]
  apply le_antisymm
  · have hle : complementIdeal R (dimensionGroupIdeal R) e ≤ centre R :=
      le_iSup_of_le e le_rfl
    exact (Ideal.map_mono hle).trans_eq hI
  · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_map_of_mem _ a.property))

theorem complementImage_other (e : dimensionIndex R)
    (a : complementIdeal R (dimensionGroupIdeal R) e) (d : WithBot ℕ∞) (hde : d ≠ e.val) :
    (dimensionComplement R d).map (algebraMap R (chartRing R e a)) = ⊥ := by
  apply eq_bot_iff.mpr
  apply Ideal.map_le_iff_le_comap.mpr
  intro x hx
  change algebraMap R (chartRing R e a) x = 0
  have hxgroup : x ∈ dimensionGroupIdeal R e := by
    apply Ideal.mem_iInf.mpr
    intro q
    apply Ideal.mem_iInf.mpr
    intro hq
    exact (Ideal.mem_iInf.mp ((Ideal.mem_iInf.mp hx) q))
      (fun hd => hde (hd.symm.trans hq))
  have hxa : x * a.val = 0 := by
    apply Ideal.mem_bot.mp
    rw [← (dimension_group_annihilation R).1 e]
    exact Ideal.mul_mem_mul hxgroup a.property
  apply Subtype.ext
  change algebraMap R (Localization.Away a.val) x = 0
  have hu : IsUnit (algebraMap R (Localization.Away a.val) a.val) :=
    IsLocalization.Away.algebraMap_isUnit a.val
  apply hu.mul_left_inj.mp
  rw [zero_mul, ← map_mul, hxa, map_zero]

def normalizedIdeal (d : WithBot ℕ∞) : (affineBlowUp (centre R)).IdealSheafData :=
  ((specIdealSheaf (dimensionComplement R d)).comap (affineBlowUp.π (centre R))).colon
    (affineBlowUp.exceptionalIdeal (centre R))

private theorem spectrumIdeal_comap {A B : Type u} [CommRing A] [CommRing B]
    (I : Ideal A) (f : A →+* B) :
    (specIdealSheaf I).comap (Spec.map (CommRingCat.ofHom f)) = specIdealSheaf (I.map f) :=
  Scheme.IdealSheafData.comap_ofIdealTop_Spec_map _ _

omit [IsReduced R] in
theorem normalizedIdeal_chart_selected (e : dimensionIndex R)
    (a : complementIdeal R (dimensionGroupIdeal R) e) :
    (normalizedIdeal R e.val).comap (groupChart R e a) = ⊤ := by
  rw [normalizedIdeal, colon_comap_of_flat _ _ (affineBlowUp.isInvertible_exceptionalIdeal _)]
  have hnum : ((specIdealSheaf (dimensionComplement R e.val)).comap
      (affineBlowUp.π (centre R))).comap (groupChart R e a) =
      (affineBlowUp.exceptionalIdeal (centre R)).comap (groupChart R e a) := by
    rw [← comap_comp, affineBlowUp.chart_π, spectrumIdeal_comap]
    change specIdealSheaf ((dimensionComplement R e.val).map (algebraMap R (chartRing R e a))) = _
    rw [complementImage_selected R e a]
    exact (affineBlowUp.comap_exceptionalIdeal_chart (centre R) (chartElement R e a)).symm
  rw [hnum]
  apply top_le_iff.mp
  rw [Scheme.IdealSheafData.le_colon_iff_mul_le, top_mul]

theorem normalizedIdeal_chart_other (e : dimensionIndex R)
    (a : complementIdeal R (dimensionGroupIdeal R) e) (d : WithBot ℕ∞) (hde : d ≠ e.val) :
    (normalizedIdeal R d).comap (groupChart R e a) = ⊥ := by
  rw [normalizedIdeal, colon_comap_of_flat _ _ (affineBlowUp.isInvertible_exceptionalIdeal _)]
  have hnum : ((specIdealSheaf (dimensionComplement R d)).comap
      (affineBlowUp.π (centre R))).comap (groupChart R e a) = ⊥ := by
    rw [← comap_comp, affineBlowUp.chart_π, spectrumIdeal_comap]
    change specIdealSheaf ((dimensionComplement R d).map (algebraMap R (chartRing R e a))) = _
    rw [complementImage_other R e a d hde]
    exact (Hironaka.Geometry.SpecIdealSheaf.specIdealSheafEquiv (chartRing R e a)).symm.map_bot
  rw [hnum]
  simpa only [pow_one] using colon_pow_bot_of_isInvertible
    ((affineBlowUp.isInvertible_exceptionalIdeal (centre R)).comap_of_flat (groupChart R e a)) 1

def normalizedOpen (d : WithBot ℕ∞) : (affineBlowUp (centre R)).Opens :=
  ⟨((normalizedIdeal R d).support : Set (affineBlowUp (centre R)))ᶜ,
    (normalizedIdeal R d).support.isClosed.isOpen_compl⟩

omit [IsReduced R] in
private theorem mem_native_part_iff (e : dimensionIndex R) (b : affineBlowUp (centre R)) :
    b ∈ dimensionPartOpen R e ↔
      ∃ (a : complementIdeal R (dimensionGroupIdeal R) e)
        (c : Spec (.of (chartRing R e a))), groupChart R e a c = b := by
  change b ∈ groupOpen R (dimensionGroupIdeal R) e ↔ _
  constructor
  · intro hb
    obtain ⟨a, ha⟩ := Opens.mem_iSup.mp hb
    have ha' : b ∈ (groupChart R e a).opensRange := by
      rw [affineBlowUp.opensRange_chart]
      exact ha
    change ∃ c, groupChart R e a c = b at ha'
    exact ⟨a, ha'⟩
  · rintro ⟨a, c, rfl⟩
    apply Opens.mem_iSup.mpr
    refine ⟨a, ?_⟩
    rw [← affineBlowUp.opensRange_chart]
    exact Set.mem_range_self c

theorem normalizedOpen_eq_native (d : dimensionIndex R) :
    normalizedOpen R d.val = dimensionPartOpen R d := by
  ext b
  constructor
  · intro hb
    change b ∉ (normalizedIdeal R d.val).support at hb
    have hcov : b ∈ (⨆ e : dimensionIndex R, dimensionPartOpen R e) := by
      rw [(dimension_group_clopen_partition R).1]
      trivial
    obtain ⟨e, he⟩ := Opens.mem_iSup.mp hcov
    by_cases hed : e = d
    · exact hed ▸ he
    exfalso
    obtain ⟨a, c, hc⟩ := (mem_native_part_iff R e b).mp he
    have hde : d.val ≠ e.val := fun h => hed (Subtype.ext h.symm)
    have hs : c ∈ ((normalizedIdeal R d.val).comap (groupChart R e a)).support := by
      rw [normalizedIdeal_chart_other R e a d.val hde, support_bot]
      trivial
    rw [support_comap] at hs
    change groupChart R e a c ∈ (normalizedIdeal R d.val).support at hs
    rw [hc] at hs
    exact hb hs
  · intro hb
    obtain ⟨a, c, hc⟩ := (mem_native_part_iff R d b).mp hb
    change b ∉ (normalizedIdeal R d.val).support
    intro hs
    have hsc : c ∈ ((normalizedIdeal R d.val).comap (groupChart R d a)).support := by
      rw [support_comap]
      change groupChart R d a c ∈ (normalizedIdeal R d.val).support
      rwa [hc]
    rw [normalizedIdeal_chart_selected, support_top] at hsc
    exact hsc

theorem normalizedOpen_eq_bot_of_absent (d : WithBot ℕ∞)
    (hd : d ∉ Set.range (componentDimension R)) : normalizedOpen R d = ⊥ := by
  apply eq_bot_iff.mpr
  intro b hb
  change b ∉ (normalizedIdeal R d).support at hb
  have hcov : b ∈ (⨆ e : dimensionIndex R, dimensionPartOpen R e) := by
    rw [(dimension_group_clopen_partition R).1]
    trivial
  obtain ⟨e, he⟩ := Opens.mem_iSup.mp hcov
  obtain ⟨a, c, hc⟩ := (mem_native_part_iff R e b).mp he
  have hde : d ≠ e.val := fun h => hd (h ▸ e.property)
  have hs : c ∈ ((normalizedIdeal R d).comap (groupChart R e a)).support := by
    rw [normalizedIdeal_chart_other R e a d hde, support_bot]
    trivial
  rw [support_comap] at hs
  change groupChart R e a c ∈ (normalizedIdeal R d).support at hs
  rw [hc] at hs
  exact hb hs
end Affine

section Global
variable {X : Scheme.{u}} [IsNoetherian X] [IsReduced X]
    {k : Type u} [Field k] (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]

theorem globalPartOpen_chart (U : X.affineOpens)
    (d : ActualIntrinsicComponentDimensions.dimensionIndex X)
    (e : dimensionIndex Γ(X, U)) (he : e.val = d.val) :
    ActualGlobalSeparationAffineCharts.chartMap p U ⁻¹ᵁ
        ActualGlobalDimensionClopenPartition.dimensionPartOpen X d = dimensionPartOpen Γ(X, U) e := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  rw [ActualGlobalSeparationAffineCharts.dimensionPartOpen_chart]
  change normalizedOpen Γ(X, U) d.val = _
  rw [← he, normalizedOpen_eq_native]

theorem globalPartOpen_chart_absent (U : X.affineOpens)
    (d : ActualIntrinsicComponentDimensions.dimensionIndex X)
    (hd : d.val ∉ Set.range (componentDimension Γ(X, U))) :
    ActualGlobalSeparationAffineCharts.chartMap p U ⁻¹ᵁ
        ActualGlobalDimensionClopenPartition.dimensionPartOpen X d = ⊥ := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  rw [ActualGlobalSeparationAffineCharts.dimensionPartOpen_chart]
  change normalizedOpen Γ(X, U) d.val = _
  exact normalizedOpen_eq_bot_of_absent Γ(X, U) d.val hd
end Global

end
end Hironaka.Resolution.Algebraic.ActualAffineNormalizedDimensionOpens
