import Hironaka.Resolution.HironakaG8NativeResidualWeightCriterion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG8NativeUnpoweredWeightObstruction
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  BlowupTowers GermIdealOrder OrderTaylor IdealWeightPowers MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaActualFixedInheritedSelector HironakaActualCauchyMonomialDivision
  HironakaRelativeNormalMonomialBasis HironakaActualWeightedCoefficientCompression
  HironakaSmoothSubmersionGermIdealColon HironakaActualHistoricalNativeStageStep
  HironakaActualNativeBornWeightedExponents HironakaActualWeightedHSNativeOrder
  HironakaActualCoefficientPresentationCentrePower HironakaActualFormalInitialDiagram
  HironakaActualRelativeNormalJetDivision HironakaActualOriginalFormalHSTransfer HironakaActualNormalZeroAnalyticSaturation
  HironakaActualWeightedHSNormalInput HironakaActualHistoricalNativeOrdinaryOrder
  HironakaActualHistoricalNormalizedWeakPresentation

/-- A second weight greater than one forces the common product mark strictly
above the first weight. -/
theorem weight_lt_commonMark_of_other_weight
    {ι : Type*} [Fintype ι] (w : ι → ℕ) (hw : ∀ i, 0 < w i)
    {i j : ι} (hij : j ≠ i) (hj : 1 < w j) :
    w i < weightedCommonMark w := by
  classical
  have hPos : 0 < ∏ t ∈ (Finset.univ : Finset ι).erase i, w t :=
    Finset.prod_pos fun t _ => hw t
  have hDiv := Finset.dvd_prod_of_mem w
    (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ j⟩)
  have hLe := Nat.le_of_dvd hPos hDiv
  unfold weightedCommonMark
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  exact lt_of_lt_of_le (by simpa using Nat.mul_lt_mul_of_pos_right hj (hw i))
    (Nat.mul_le_mul_right (w i) hLe)

/-- Equal weights greater than one across two or more labels cannot
produce an unpowered native compression with the actual common mark. -/
theorem equal_top_weights_force_power
    {ι : Type*} [Fintype ι] (w : ι → ℕ) {o : ℕ} (ho : 1 < o)
    (hEq : ∀ i, w i = o) {i j : ι} (hij : j ≠ i) :
    1 < weightedCommonMark w / w i := by
  have hw : ∀ i, 0 < w i := fun i => hEq i ▸ (by omega : 0 < o)
  have hlt := weight_lt_commonMark_of_other_weight w hw hij (by simpa [hEq] using ho)
  have he := weight_mul_compressionExponent w i
  by_contra h
  have hf : weightedCommonMark w / w i ≤ 1 := by omega
  have hle := Nat.mul_le_mul_left (w i) hf
  rw [he, Nat.mul_one] at hle
  omega

set_option maxHeartbeats 1200000 in
/-- At an actual native cut point, a label with weight below the common
mark witnesses that the weighted adapted stalk is nonradical. -/
theorem actual_native_point_nonradical_of_smaller_weight
    {n k : ℕ} {X : CMfd.{0} n} {V : Finset (Fin n →₀ ℕ)}
    (S : ActualFixedInheritedSelector V) (a : Fin k ≃ V) (w : Fin k → CoordinateWord n)
    (hw : ∀ i, wordExponent (w i) = (a i).val)
    (W : Set X) (Q : MarkedIdeal n X) (hN : Q.N = univ) (hQ : Q.ideal.IsCoherent)
    (hAtMark : Q.d = weightedCommonMark (fun v : V => normalExponentDegree v.val))
    (x : X) (hx : x ∈ Q.cosupp)
    (hAt : ActualHistoricalNativePointPresentation S a w W Q x)
    (v : V) (hv : normalExponentDegree v.val < Q.d) :
    ∃ (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
      (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0),
      ¬ (adaptedIdeal Q.ideal x Φ h0).IsRadical := by
  obtain ⟨Φ,hΦsrc,h0,Γ,hFive,_,hCompression⟩ := hAt
  refine ⟨Φ,h0,?_⟩
  intro hRad
  let μ := fun v : V => normalExponentDegree v.val
  have hGt : (Γ v) ^ (weightedCommonMark μ / μ v) ∈ adaptedIdeal Q.ideal x Φ h0 := by
    rw [hCompression]
    exact Ideal.subset_span ⟨v,rfl⟩
  have hMember : Γ v ∈ adaptedIdeal Q.ideal x Φ h0 := hRad (show Γ v ∈ (adaptedIdeal Q.ideal x Φ h0).radical from ⟨_, hGt⟩)
  obtain ⟨F,hF,hFΓ⟩ := exists_original_adapted_representative x Φ h0 (Γ v)
  have hFQ : Q.ideal.mem x F := (mem_adaptedIdeal_iff Q.ideal hQ x Φ h0 F hF).mp (hFΓ.symm ▸ hMember)
  change μ v < Q.d at hv
  have hLow : (idealPow (pointIdeal n x) (μ v+1)).mem x F := by
    change x ∈ cosupport n Q.N Q.ideal Q.d at hx
    rw [hN] at hx
    exact mem_idealPow_of_vanishesToOrderOn_univ
      (VanishesToOrderOn.mono (by omega : μ v + 1 ≤ Q.d) (hx.2 _ hFQ))
  have hGerm := adaptedGerm_point_power x Φ hΦsrc h0 F hF hLow
  rw [hFΓ] at hGerm
  have hTaylor : actualUnshiftedTaylorAlgHom n (Γ v) ∈ genuineFormalVariables n ^ (μ v+1) := by
    rw [← map_actualUnshifted_maximal_pow n (μ v+1)]
    exact Ideal.mem_map_of_mem _ hGerm
  let i := a.symm v
  have hai : a i = v := a.apply_symm_apply v
  have hDegree : normalExponentDegree (wordExponent (w i)) = μ v := by rw [hw,hai]
  have hHigh := (hFive.1 i).2
  rw [hDegree,hai] at hHigh
  exact hHigh hTaylor

/-- A genuine active native point with at least two positive-weight labels
and raw mark greater than one obstructs identification with the reduced
vanishing ideal of the original analytic set, on any window containing it. -/
theorem actual_native_ideal_ne_reduced_of_two_labels
    {n k : ℕ} {X : CMfd.{0} n} {V : Finset (Fin n →₀ ℕ)}
    (S : ActualFixedInheritedSelector V) (a : Fin k ≃ V) (w : Fin k → CoordinateWord n)
    (hw : ∀ i, wordExponent (w i) = (a i).val)
    (hPositive : ∀ v : V, 0 < normalExponentDegree v.val)
    (hLabels : ∀ i : V, ∃ j : V, j ≠ i)
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (Q : MarkedIdeal n X) (hN : Q.N = univ) (hQ : Q.ideal.IsCoherent)
    (hAtMark : Q.d = weightedCommonMark (fun v : V => normalExponentDegree v.val))
    (hMark : 1 < Q.d) (x : X) (hx : x ∈ Q.cosupp)
    (hAt : ActualHistoricalNativePointPresentation S a w W Q x) :
    Q.ideal ≠ vanishingIdeal (n := n) W := by
  let μ := fun v : V => normalExponentDegree v.val
  have hLarge : ∃ j : V, 1 < μ j := by
    by_contra hNone
    have hOne (j : V) : μ j = 1 := by
      have hp : 0 < μ j := hPositive j
      have hu : ¬ 1 < μ j := fun hj => hNone ⟨j,hj⟩
      omega
    have hProduct : weightedCommonMark μ = 1 := by simp [weightedCommonMark,hOne]
    have hMarkOne : Q.d = 1 := hAtMark.trans hProduct
    omega
  obtain ⟨j,hj⟩ := hLarge
  obtain ⟨i,hi⟩ := hLabels j
  have hLt : μ i < Q.d :=
    (weight_lt_commonMark_of_other_weight μ hPositive (Ne.symm hi) hj).trans_eq hAtMark.symm
  obtain ⟨Φ,h0,hNot⟩ := actual_native_point_nonradical_of_smaller_weight S a w hw W Q hN hQ
    hAtMark x hx hAt i hLt
  intro hEq
  apply hNot
  rw [hEq]
  exact adapted_vanishingIdeal_isRadical W (CartanIrreducible.cartanCoherence W hW) x Φ h0

end
end Hironaka.HironakaG8NativeUnpoweredWeightObstruction
