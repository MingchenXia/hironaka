import Hironaka.Resolution.HironakaActualAnalyticNormalTargetTransition
import Hironaka.Resolution.HironakaActualAnalyticAdaptedCurrentFamily
import Hironaka.Resolution.HironakaActualNormalCoordinateReindex

/-! Actual SOURCE shears and coordinate permutations transport the ENTIRE
independently named normalized-member ideals. Actual quotient products retain
each literal source mark; genuine inverse source preimages give both inclusions.
No diagram, target span or ideal comparison is supplied. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualAnalyticSourceNormalizedTransport
noncomputable section
open HolGerm HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetChartInvariance
 HironakaActualCoefficientPresentationCentrePower HironakaActualAnalyticBlowupTaylor
 HironakaActualAnalyticDirectionRemovalQuotient HironakaActualAnalyticSourceShearTaylor
 HironakaActualNormalZeroAnalyticSaturation HironakaActualFormalBlowupAllDirections
 HironakaActualFormalCoordinatePowerDivision HironakaActualAnalyticStrictGenerators
 HironakaActualNormalCoordinateReindex HironakaActualAnalyticNormalTargetTransition
 HironakaActualFixedInheritedSelectorPermutation HironakaActualAnalyticFormalNormalPowers
 HironakaActualAnalyticAdaptedCurrentFamily HironakaActualNormalMarkedDirection
 HironakaActualRelativeStandardnessNormalPivotPriority
 HironakaActualRelativeStandardnessNormalPointBridge HironakaActualNormalCentreChartTransition
variable {n : ℕ}

private theorem equiv_mem_map_iff
    (E : HolGerm (ComplexModel n)≃ₐ[ℂ]HolGerm (ComplexModel n))
    (J : Ideal (HolGerm (ComplexModel n))) (g : HolGerm (ComplexModel n)) :
    E g∈Ideal.map E.toRingEquiv.toRingHom J ↔ g∈J := by
  constructor
  · intro h
    obtain ⟨f,hf,he⟩:=(Ideal.mem_map_iff_of_surjective E.toRingEquiv.toRingHom E.surjective).mp h
    exact E.injective he ▸ hf
  · exact Ideal.mem_map_of_mem E.toRingEquiv.toRingHom

private theorem shear_power_map (A : Set (Fin n)) (e : Fin n) (he : e∈A)
    (b : Fin n → ℂ) (μ : ℕ) :
    Ideal.map (actualAnalyticDirectionShearGermEquiv A e b).toRingEquiv.toRingHom
        (actualAnalyticCoordinateIdeal A^μ)=actualAnalyticCoordinateIdeal A^μ := by
  apply actualUnshifted_ideal_extension_injective n
  rw [map_actualTaylor_analytic_source_shear A e he b]
  simp only [Ideal.map_pow,map_actualAnalyticCoordinateIdeal_taylor]
  rw [map_coordinateIdeal_centerShear A e he b]

/-- The source shear removes a direction while leaving each actual normalized
quotient germ unchanged, for the WHOLE independent source ideal. -/
theorem analytic_normalized_ideal_source_shear
    (I : Ideal (HolGerm (ComplexModel n))) (A : Set (Fin n))
    (e : Fin n) (he : e∈A) (b : Fin n → ℂ) :
    actualAnalyticNormalizedMemberIdeal I A e b=
      actualAnalyticNormalizedMemberIdeal
        (Ideal.map (actualAnalyticDirectionShearGermEquiv A e b).toRingEquiv.toRingHom I)
        A e (fun _=>0) := by
  let S:=actualAnalyticDirectionShearGermEquiv A e b
  have hp (μ : ℕ) (g : HolGerm (ComplexModel n)) :
      S g∈actualAnalyticCoordinateIdeal A^μ ↔ g∈actualAnalyticCoordinateIdeal A^μ := by
    have h:=equiv_mem_map_iff S (actualAnalyticCoordinateIdeal A^μ) g
    simpa only [S,shear_power_map A e he b μ] using h
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro H ⟨μ,g,hg,hgP,hH⟩
    apply Ideal.subset_span
    exact ⟨μ,S g,Ideal.mem_map_of_mem _ hg,(hp μ g).mpr hgP,
      hH.trans (actualAnalyticBlowupPullback_direction_shear A e b g)⟩
  · apply Ideal.span_le.mpr
    rintro H ⟨μ,g,hg,hgP,hH⟩
    obtain ⟨g0,hg0,rfl⟩:=(Ideal.mem_map_iff_of_surjective S.toRingEquiv.toRingHom S.surjective).mp hg
    apply Ideal.subset_span
    exact ⟨μ,g0,hg0,(hp μ g0).mp hgP,
      hH.trans (actualAnalyticBlowupPullback_direction_shear A e b g0).symm⟩

/-- A genuine analytic coordinate permutation transports every literal source
power and exceptional product, hence BOTH WHOLE normalized-member ideal spans. -/
theorem analytic_normalized_ideal_coordinate_permutation
    (r : Fin n ≃ Fin n) (I : Ideal (HolGerm (ComplexModel n)))
    (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    Ideal.map (coordinateGermEquiv r).toRingEquiv.toRingHom
      (actualAnalyticNormalizedMemberIdeal I A e b)=
      actualAnalyticNormalizedMemberIdeal (Ideal.map (coordinateGermEquiv r).toRingEquiv.toRingHom I)
        (r '' A) (r e) (b ∘ r.symm) := by
  let P:=coordinateGermEquiv r
  have hPower (μ : ℕ) : Ideal.map P.toRingEquiv.toRingHom (actualAnalyticCoordinateIdeal A^μ)=
      actualAnalyticCoordinateIdeal (r '' A)^μ := by
    rw [Ideal.map_pow,map_analyticCoordinateIdeal_coordinateGermEquiv]
  have hp (μ : ℕ) (g : HolGerm (ComplexModel n)) :
      P g∈actualAnalyticCoordinateIdeal (r '' A)^μ ↔ g∈actualAnalyticCoordinateIdeal A^μ := by
    rw [←hPower]
    exact equiv_mem_map_iff P _ g
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro H ⟨μ,g,hg,hgP,hH⟩
    change P H∈actualAnalyticNormalizedMemberIdeal (Ideal.map P.toRingEquiv.toRingHom I)
      (r '' A) (r e) (b ∘ r.symm)
    apply Ideal.subset_span
    refine ⟨μ,P g,Ideal.mem_map_of_mem _ hg,(hp μ g).mpr hgP,?_⟩
    have h:=congrArg P hH
    rw [map_mul,map_pow,coordinateGermEquiv_coordinate,coordinateGermEquiv_actualAnalyticBlowupPullback] at h
    exact h
  · apply Ideal.span_le.mpr
    rintro H ⟨μ,g,hg,hgP,hH⟩
    obtain ⟨g0,hg0,rfl⟩:=(Ideal.mem_map_iff_of_surjective P.toRingEquiv.toRingHom P.surjective).mp hg
    have hProd : coordinateGerm e^μ*P.symm H=actualAnalyticBlowupPullback A e b g0 := by
      apply P.injective
      rw [map_mul,map_pow,coordinateGermEquiv_coordinate,AlgEquiv.apply_symm_apply,
        coordinateGermEquiv_actualAnalyticBlowupPullback]
      exact hH
    have hMem : P.symm H∈actualAnalyticNormalizedMemberIdeal I A e b :=
      Ideal.subset_span ⟨μ,g0,hg0,(hp μ g0).mp hgP,hProd⟩
    have hm:=Ideal.mem_map_of_mem P.toRingEquiv.toRingHom hMem
    change P (P.symm H)∈Ideal.map P.toRingEquiv.toRingHom (actualAnalyticNormalizedMemberIdeal I A e b) at hm
    change H∈Ideal.map P.toRingEquiv.toRingHom (actualAnalyticNormalizedMemberIdeal I A e b)
    simpa only [AlgEquiv.apply_symm_apply] using hm

private theorem coordinateEquiv_eq_actualPermutation (r : Fin n ≃ Fin n) :
    coordinateGermEquiv r=actualPermutationGermEquiv r := by
  apply AlgEquiv.ext
  intro g
  apply actualUnshiftedTaylorAlgHom_injective n
  have h : actualUnshiftedTaylorAlgHom n (coordinateGermEquiv r g)=
      MvPowerSeries.rename r (actualUnshiftedTaylorAlgHom n g) :=
    DFunLike.congr_fun (actualTaylor_coordinateGermEquiv r) g
  rw [h,actualTaylor_actualPermutationGermEquiv]

private theorem inverse_map_of_map_eq
    (E : HolGerm (ComplexModel n)≃ₐ[ℂ]HolGerm (ComplexModel n))
    (J K : Ideal (HolGerm (ComplexModel n))) (h : Ideal.map E.toRingEquiv.toRingHom J=K) :
    Ideal.map E.symm.toRingEquiv.toRingHom K=J := by
  rw [←h,Ideal.map_map]
  have he : E.symm.toRingEquiv.toRingHom.comp E.toRingEquiv.toRingHom=RingHom.id _ := by
    apply RingHom.ext
    intro g
    exact E.symm_apply_apply g
  rw [he,Ideal.map_id]

private theorem normal_pivot_preserves_tail {m : ℕ} (q f : Fin (m+1)) (hqf : q≤f)
    (i : Fin (m+1)) : normalPivotEquiv q f i∈Set.Ici q ↔ i∈Set.Ici q := by
  constructor
  · intro hi
    by_contra h
    have ht:=normalPivotEquiv_tangent q f hqf i (lt_of_not_ge h)
    rw [ht] at hi
    exact h hi
  · intro hi
    by_contra h
    have hpi : normalPivotEquiv q f i<q:=lt_of_not_ge h
    have hfix:=normalPivotEquiv_tangent q f hqf (normalPivotEquiv q f i) hpi
    have heq : normalPivotEquiv q f i=i:=(normalPivotEquiv q f).injective hfix
    rw [heq] at hpi
    exact (not_lt_of_ge hi) hpi

private theorem normal_pivot_tail_image {m : ℕ} (q f : Fin (m+1)) (hqf : q≤f) :
    normalPivotEquiv q f '' Set.Ici q=Set.Ici q := by
  ext i
  constructor
  · rintro ⟨j,hj,rfl⟩
    exact (normal_pivot_preserves_tail q f hqf j).mpr hj
  · intro hi
    refine ⟨(normalPivotEquiv q f).symm i,?_,by simp⟩
    exact (normal_pivot_preserves_tail q f hqf _).mp (by simpa using hi)

private theorem actual_pullback_eq_normal_direction (A : Set (Fin n))
    (e : Fin n) (b : Fin n → ℂ) :
    actualAnalyticBlowupPullback A e b=
      actualAnalyticBlowupPullback A e (actualNormalMarkedDirection A e b) := by
  have hMap : actualAnalyticBlowupMap A e b=
      actualAnalyticBlowupMap A e (actualNormalMarkedDirection A e b) := by
    funext z
    ext i
    by_cases hi : i∈A <;> by_cases hie : i=e <;>
      simp [actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate,
        actualNormalMarkedDirection,actualNormalPointDirection,hi,hie]
  apply AlgHom.ext
  intro g
  obtain ⟨H,hH,rfl⟩:=HolGerm.exists_eq_mk g
  unfold actualAnalyticBlowupPullback
  rw [compAlgHom_mk,compAlgHom_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Filter.Eventually.of_forall fun z=>congrArg H (congrFun hMap z)

/-- ONE actual analytic target equivalence, constructed before the source
ideal, identifies its original arbitrary-direction whole normalized ideal with
the independently defined zero-chart ideal of the actual analytic source
adaptation. No current ideal equality or analytic inverse is supplied. -/
theorem exists_actual_original_to_adapted_normalized_ideal_transport {m : ℕ}
    (q e f : Fin (m+1)) (hqe : q≤e) (hqf : q≤f) (b : Fin (m+1) → ℂ)
    (hvf : actualNormalMarkedDirection (Set.Ici q) e b f≠0) :
    ∃C : HolGerm (ComplexModel (m+1))≃ₐ[ℂ]HolGerm (ComplexModel (m+1)),
      ∀I : Ideal (HolGerm (ComplexModel (m+1))),
        Ideal.map C.toRingEquiv.toRingHom (actualAnalyticNormalizedMemberIdeal I (Set.Ici q) e b)=
          actualAnalyticNormalizedMemberIdeal (actualAnalyticNormalAdaptedSourceIdeal I q e f b)
            (Set.Ici q) q (fun _=>0) := by
  let A:=Set.Ici q
  let v:=actualNormalMarkedDirection A e b
  let w:=actualNormalChartNormalizedDirection f v
  let p:=normalPivotEquiv q f
  let P:=actualPermutationGermEquiv p
  let S:=actualAnalyticDirectionShearGermEquiv A f w
  have hve : v e=1:=by simp [v,actualNormalMarkedDirection]
  obtain ⟨E,_hCoord,_hTaylor,_hUnit,_hMember,hNorm⟩:=
    exists_actual_analytic_normal_target_transport A e f hqe hqf v hve hvf
  let C:=E.symm.trans P
  refine ⟨C,?_⟩
  intro I
  have hNb : actualAnalyticNormalizedMemberIdeal I A e b=
      actualAnalyticNormalizedMemberIdeal I A e v := by
    simp only [actualAnalyticNormalizedMemberIdeal,actual_pullback_eq_normal_direction A e b]
    rfl
  have hInv : Ideal.map E.symm.toRingEquiv.toRingHom (actualAnalyticNormalizedMemberIdeal I A e b)=
      actualAnalyticNormalizedMemberIdeal I A f w := by
    rw [hNb]
    exact inverse_map_of_map_eq E _ _ (hNorm I)
  have hPerm := analytic_normalized_ideal_coordinate_permutation p (Ideal.map S.toRingEquiv.toRingHom I)
    A f (fun _=>0)
  have hImage : p '' A=A:=normal_pivot_tail_image q f hqf
  have hpf : p f=q:=normalPivotEquiv_pivot q f hqf
  rw [hImage,hpf,coordinateEquiv_eq_actualPermutation] at hPerm
  have hS : actualAnalyticNormalizedMemberIdeal I A f w=
      actualAnalyticNormalizedMemberIdeal (Ideal.map S.toRingEquiv.toRingHom I) A f (fun _=>0) :=
    analytic_normalized_ideal_source_shear I A f hqf w
  have hMap : C.toRingEquiv.toRingHom=P.toRingEquiv.toRingHom.comp E.symm.toRingEquiv.toRingHom:=rfl
  rw [hMap,←Ideal.map_map,hInv,hS]
  exact hPerm

end
end Hironaka.HironakaActualAnalyticSourceNormalizedTransport
