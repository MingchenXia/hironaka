import Hironaka.Resolution.HironakaActualHistoricalNormalizedWeakPresentation
import Hironaka.Resolution.HironakaG8WeightOneTwoGeneratorChange
import Hironaka.Resolution.HironakaActualHistoricalMovingPrefixSupport

/-! Full degree-prefix support, rather than canonical reducedness, is enough
to recover the aligned weighted cusp germ. -/
set_option autoImplicit false
open Set
open scoped MonomialOrder
namespace Hironaka.HironakaG8CuspPrefixSupportCompression
noncomputable section
open HolGerm HironakaRelativeNormalIdeal
  HironakaActualCoefficientPresentationCentrePower HironakaActualZeroSectionFormalBasis
  HironakaActualTaylorCoordinateNaturality HironakaActualAnalyticFormalNormalPowers
  HironakaActualRelativeTaylorCoefficients
  HironakaActualFormalCoordinatePowerDivision HironakaRelativeNormalMonomialBasis
  HironakaG8SameHSCuspContact HironakaActualZeroSectionStabilization
  HironakaG8WeightOneTwoGeneratorChange

private theorem normal_zero_derivative_part
    (a : Fin 3 →₀ ℕ) (h : a (2 : Fin 3) = 0) :
    Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables 2 1)) a = 0 := by
  have hN : actualNormalExponent (d := 2) (t := 1) a = 0 := by
    apply Finsupp.ext
    intro j
    have hj := Subsingleton.elim j (0 : Fin 1)
    subst j
    exact h
  have ha := actualJoinedExponent_split (d := 2) (t := 1) a
  rw [← ha, actualJoinedExponent_normal_weight, hN]
  simp [normalExponentDegree]

/-- A genuine analytic germ with no coefficient supported in the normal
cone is exactly the lift of its literal analytic plane trace. -/
theorem tangentPullback_planeTrace_of_no_normal_coefficients
    (f : HolGerm (ComplexModel 3))
    (hf : ∀ a : Fin 3 →₀ ℕ, a (2 : Fin 3) ≠ 0 →
      MvPowerSeries.coeff a (actualUnshiftedTaylorAlgHom 3 f) = 0) :
    tangentPullback 2 1 (planeTrace 2 1 f) = f := by
  let g := f - tangentPullback 2 1 (planeTrace 2 1 f)
  have hg : g ∈ normalIdeal 2 1 := by
    rw [normalIdeal_eq_ker_planeTrace]
    change planeTrace 2 1 g = 0
    dsimp [g]
    rw [map_sub, planeTrace_tangentPullback, sub_self]
  apply Eq.symm
  apply sub_eq_zero.mp
  apply actualUnshiftedTaylorAlgHom_injective 3
  rw [map_zero]
  apply MvPowerSeries.ext
  intro a
  rw [map_zero]
  by_cases ha : a (2 : Fin 3) = 0
  · have hTG : actualUnshiftedTaylorAlgHom 3 g ∈
        actualFormalCoordinateIdeal 3 (actualTangentCentreVariables 2 1) := by
      rw [← map_normalIdeal_originalTaylor 2 1]
      exact Ideal.mem_map_of_mem _ hg
    rw [← pow_one (actualFormalCoordinateIdeal 3 (actualTangentCentreVariables 2 1))] at hTG
    exact (mem_actualFormalCoordinateIdeal_pow_iff _ _ _).mp hTG a
      (by rw [normal_zero_derivative_part a ha]; decide)
  · have ht : actualUnshiftedTaylorAlgHom 3 (tangentPullback 2 1 (planeTrace 2 1 f)) =
        MvPowerSeries.rename (Fin.castAdd 1) (actualUnshiftedTaylorAlgHom 2 (planeTrace 2 1 f)) :=
      DFunLike.congr_fun (actualUnshiftedTaylor_tangentPullback 2 1) _
    change MvPowerSeries.coeff a (actualUnshiftedTaylorAlgHom 3
      (f - tangentPullback 2 1 (planeTrace 2 1 f))) = _
    have hNot : a ∉ range (Finsupp.mapDomain (Fin.castAdd 1 : Fin 2 → Fin 3)) := by
      rintro ⟨b,hb⟩
      have hn := congrArg (fun a : Fin 3 →₀ ℕ => a (2 : Fin 3)) hb
      let e : Fin 2 ↪ Fin 3 := Fin.castAddEmb 1
      change Finsupp.mapDomain e b 2 = a 2 at hn
      rw [← Finsupp.embDomain_eq_mapDomain] at hn
      have hh : (2 : Fin 3) ∉ range e := by
        rintro ⟨j,hj⟩
        have he := congrArg Fin.val hj
        exact (Nat.ne_of_lt j.isLt) he
      exact ha (hn.symm.trans (Finsupp.embDomain_of_notMem_range e b 2 hh))
    rw [map_sub, ht, map_sub, hf a ha, MvPowerSeries.coeff_rename_eq_zero _ _ hNot, sub_zero]


private theorem embedded_cusp_unweighted_span (p : ℕ) :
    embeddedCuspIdeal p =
      Ideal.span {normalCoordinate 2 1 0, tangentPullback 2 1 (cuspGerm p)} := by
  have hNormal : range (normalCoordinate 2 1) = {normalCoordinate 2 1 0} := by
    ext g
    simp only [mem_range, mem_singleton_iff]
    constructor
    · rintro ⟨a,rfl⟩
      rw [Subsingleton.elim a 0]
    · rintro rfl
      exact ⟨0,rfl⟩
  rw [embeddedCuspIdeal, actualZeroSectionIdeal, Ideal.map_span, Set.image_singleton,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, normalIdeal, hNormal, ← Ideal.span_union]
  congr 1
  ext g
  simp

/-- The exact historic orders and absence of the degree-one normal cone in
the degree-two member suffice for the genuine compressed ideal. -/
theorem cusp_compression_of_native_prefix_support (p : ℕ)
    (a b : HolGerm (ComplexModel 3))
    (hSpan : Ideal.span {a,b} = embeddedCuspIdeal p)
    (hA : a ∉ IsLocalRing.maximalIdeal (HolGerm (ComplexModel 3)) ^ 2)
    (hB : b ∉ IsLocalRing.maximalIdeal (HolGerm (ComplexModel 3)) ^ 3)
    (hF : tangentPullback 2 1 (cuspGerm p) ∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel 3)) ^ 2)
    (hPrefix : ∀ c : Fin 3 →₀ ℕ, c (2 : Fin 3) ≠ 0 →
      MvPowerSeries.coeff c (actualUnshiftedTaylorAlgHom 3 b) = 0) :
    Ideal.span {a^2,b} =
      Ideal.span {(normalCoordinate 2 1 0)^2, tangentPullback 2 1 (cuspGerm p)} := by
  let R := HolGerm (ComplexModel 3)
  let m := IsLocalRing.maximalIdeal R
  let z := normalCoordinate 2 1 0
  let f := tangentPullback 2 1 (cuspGerm p)
  have hz : z ∈ m :=
    HironakaSmoothSubmersionProjectionIdealColon.normalIdeal_le_actual_maximalIdeal 2 1
      (Ideal.subset_span ⟨0,rfl⟩)
  have ha : a ∈ Ideal.span ({z,f} : Set R) := by
    rw [← embedded_cusp_unweighted_span p, ← hSpan]
    exact Ideal.subset_span (by simp)
  have hb : b ∈ Ideal.span ({z,f} : Set R) := by
    rw [← embedded_cusp_unweighted_span p, ← hSpan]
    exact Ideal.subset_span (by simp)
  obtain ⟨u,v,hAeq⟩ := Ideal.mem_span_pair.mp ha
  obtain ⟨c,d,hBeq⟩ := Ideal.mem_span_pair.mp hb
  let t := tangentPullback 2 1 (planeTrace 2 1 d)
  have hB' : b = t * f := by
    rw [← tangentPullback_planeTrace_of_no_normal_coefficients b hPrefix, ← hBeq]
    change tangentPullback 2 1 (planeTrace 2 1 (c*z+d*f)) = t*f
    simp only [z,f,map_add,map_mul,planeTrace_normalCoordinate, mul_zero,zero_add,
      planeTrace_tangentPullback,t]
  have hu : IsUnit u := by
    apply Classical.byContradiction
    intro hn
    have hu : u ∈ m := by
      change u ∈ IsLocalRing.maximalIdeal R
      exact (IsLocalRing.mem_maximalIdeal _).mpr hn
    apply hA
    rw [← hAeq, pow_two]
    exact (m*m).add_mem (Ideal.mul_mem_mul hu hz) ((m*m).mul_mem_left v (by simpa only [← pow_two] using hF))
  have ht : IsUnit t := by
    apply Classical.byContradiction
    intro hn
    have ht : t ∈ m := by
      change t ∈ IsLocalRing.maximalIdeal R
      exact (IsLocalRing.mem_maximalIdeal _).mpr hn
    apply hB
    rw [hB', pow_succ']
    exact Ideal.mul_mem_mul ht hF
  have hf : f ∈ m := by
    simpa only [pow_one] using Ideal.pow_le_pow_right (show 1 ≤ 2 by decide) hF
  rw [← hAeq, hB']
  simpa only [zero_mul, zero_add] using
    (span_weight_one_two_of_adapted_change (c := 0) hf hz hu ht)


open HironakaG8NativeCuspDiagram HironakaActualHistoricalNormalizedWeakPresentation
  HironakaActualHistoricalMovingPrefixSupport HironakaActualHistoricalCentreFilteredDivision
  HironakaActualOriginalFormalHSTransfer HironakaActualFixedInheritedSelector
  HironakaActualFormalInitialDiagram HironakaActualNormalZeroAnalyticSaturation
  HironakaActualWeightedCoefficientCompression HironakaActualCauchyMonomialDivision

private theorem embedded_cusp_high_generator_order (p : ℕ) (hp : 2 < p) :
    tangentPullback 2 1 (cuspGerm p) ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel 3)) ^ 2 := by
  apply (actual_maximal_power_iff_formal_coefficients_zero 3 2 _).mpr
  intro a ha
  have hTaylor : actualUnshiftedTaylorAlgHom 3 (tangentPullback 2 1 (cuspGerm p)) =
      (MvPowerSeries.X (1 : Fin 3))^2 - (MvPowerSeries.X (0 : Fin 3))^p := by
    have ht : actualUnshiftedTaylorAlgHom 3 (tangentPullback 2 1 (cuspGerm p)) =
        MvPowerSeries.rename (Fin.castAdd 1) (actualUnshiftedTaylorAlgHom 2 (cuspGerm p)) :=
      DFunLike.congr_fun (actualUnshiftedTaylor_tangentPullback 2 1) _
    rw [ht, cusp_actual_taylor,
      cuspSeries, map_sub, map_pow, map_pow, MvPowerSeries.rename_X, MvPowerSeries.rename_X]
    rfl
  have hDegree (j : Fin 3) (k : ℕ) : normalExponentDegree (Finsupp.single j k) = k := by
    simp [normalExponentDegree, Finsupp.single_apply]
  have h1 : a ≠ Finsupp.single (1 : Fin 3) 2 := fun h => (Nat.ne_of_lt ha) (h ▸ hDegree 1 2)
  have h0 : a ≠ Finsupp.single (0 : Fin 3) p := fun h =>
    (Nat.ne_of_lt (ha.trans hp)) (h ▸ hDegree 0 p)
  simp [hTaylor, MvPowerSeries.coeff_X_pow, h1, h0]

/-- The existing historical point laws already suffice for the prescribed
compression once the adapted whole ideal and the retained labels are aligned
with the displayed geometric cusp. No reduced-basis guard is needed. -/
theorem cusp_compression_of_aligned_historical_point_laws (p : ℕ) (hp : 2 < p)
    (k : ℕ)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex
      (analyticZeroTaylorIdeal 3 (embeddedCuspIdeal p))))
    (e : Fin k ≃ actualInitialVertices MonomialOrder.degLex
      (analyticZeroTaylorIdeal 3 (embeddedCuspIdeal p)))
    (w : Fin k → CoordinateWord 3)
    (hWords : ∀ i, wordExponent (w i) = (e i).val)
    (Γ : actualInitialVertices MonomialOrder.degLex
      (analyticZeroTaylorIdeal 3 (embeddedCuspIdeal p)) → HolGerm (ComplexModel 3))
    (hFive : ActualHistoricalFivePointLaws S e w Γ)
    (hSpan : Ideal.span (range (fun i => Γ (e i))) = embeddedCuspIdeal p) :
    weightedCompression (fun u => normalExponentDegree u.val) Γ =
      Ideal.span {(normalCoordinate 2 1 0)^2, tangentPullback 2 1 (cuspGerm p)} := by
  classical
  let V := actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal 3 (embeddedCuspIdeal p))
  have hLift : actualJoinedExponent cuspVertex (0 : Fin 1 →₀ ℕ) =
      Finsupp.single (1 : Fin 3) 2 := by
    ext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [show actualJoinedExponent cuspVertex (0 : Fin 1 →₀ ℕ) (i.castAdd 1) = cuspVertex i by
        simp [actualJoinedExponent]]
      fin_cases i <;> simp
    · rw [show actualJoinedExponent cuspVertex (0 : Fin 1 →₀ ℕ) (i.natAdd 2) = 0 by
        simp [actualJoinedExponent]]
      fin_cases i; simp
  have hV : V = {Finsupp.single (1 : Fin 3) 2, Finsupp.single (2 : Fin 3) 1} := by
    change actualInitialVertices MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom 3).toRingHom (embeddedCuspIdeal p)) = _
    rw [embedded_cusp_vertices p hp, hLift]
  let v₁ : V := ⟨Finsupp.single 2 1, by simp [hV]⟩
  let v₂ : V := ⟨Finsupp.single 1 2, by simp [hV]⟩
  have h1 : normalExponentDegree v₁.val = 1 := by simp [v₁, normalExponentDegree, Finsupp.single_apply]
  have h2 : normalExponentDegree v₂.val = 2 := by simp [v₂, normalExponentDegree, Finsupp.single_apply]
  have hCases (u : V) : u = v₁ ∨ u = v₂ := by
    have h : u.val ∈ ({Finsupp.single (1 : Fin 3) 2, Finsupp.single (2 : Fin 3) 1} : Finset _) :=
      hV ▸ u.property
    rcases Finset.mem_insert.mp h with h | h
    · exact Or.inr (Subtype.ext h)
    · exact Or.inl (Subtype.ext (Finset.mem_singleton.mp h))
  have hSpan' : Ideal.span {Γ v₁,Γ v₂} = embeddedCuspIdeal p := by
    rw [← hSpan]
    congr 1
    ext f
    constructor
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (rfl | rfl)
      · exact ⟨e.symm v₁, by simp⟩
      · exact ⟨e.symm v₂, by simp⟩
    · rintro ⟨i,rfl⟩
      rcases hCases (e i) with h | h <;> simp [h]
  have hOrder (u : V) : Γ u ∉
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel 3)) ^ (normalExponentDegree u.val+1) := by
    have h := (hFive.1 (e.symm u)).2
    rw [hWords,e.apply_symm_apply] at h
    intro he
    exact h ((mem_genuineFormalVariables_pow_iff_coefficients_zero _ _ _).mpr
      ((actual_maximal_power_iff_formal_coefficients_zero _ _ _).mp he))
  have hA := hOrder v₁
  have hB := hOrder v₂
  rw [h1] at hA
  rw [h2] at hB
  have hPrefix : ∀ c : Fin 3 →₀ ℕ, c (2 : Fin 3) ≠ 0 →
      MvPowerSeries.coeff c (actualUnshiftedTaylorAlgHom 3 (Γ v₂)) = 0 := by
    intro c hc
    apply hFive.2.2.2.2.2 1 v₂ (by rw [h2]; decide) v₁ h1.le c
    intro j
    change Finsupp.single (2 : Fin 3) 1 j ≤ c j
    by_cases h : j = 2
    · subst j
      simp only [Finsupp.single_eq_same]
      omega
    · simp [Finsupp.single_eq_of_ne h]
  have hMark := embedded_cusp_native_mark p hp
  have hCompression : weightedCompression (fun u : V => normalExponentDegree u.val) Γ =
      Ideal.span {Γ v₁ ^ 2, Γ v₂} := by
    unfold weightedCompression
    change weightedCommonMark (fun u : V => normalExponentDegree u.val) = 2 at hMark
    rw [hMark]
    congr 1
    ext f
    constructor
    · rintro ⟨u,rfl⟩
      rcases hCases u with rfl | rfl <;> simp [h1,h2]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (rfl | rfl)
      · exact ⟨v₁, by simp [h1]⟩
      · exact ⟨v₂, by simp [h2]⟩
  exact hCompression.trans (cusp_compression_of_native_prefix_support p (Γ v₁) (Γ v₂)
    hSpan' hA hB (embedded_cusp_high_generator_order p hp) hPrefix)

end
end Hironaka.HironakaG8CuspPrefixSupportCompression
