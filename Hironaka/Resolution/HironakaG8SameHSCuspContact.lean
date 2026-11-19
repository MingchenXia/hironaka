import Hironaka.Resolution.HironakaActualPrincipalHSFormula
import Hironaka.Resolution.HironakaActualOriginalFormalTaylor
import Hironaka.Resolution.HironakaActualZeroSectionStabilization
import Hironaka.Resolution.HironakaSmoothSubmersionProjectionIdealColon

/-! Actual analytic cusp jets and the trace to their common tangent line. -/
set_option autoImplicit false
open Set

namespace Hironaka.HironakaG8SameHSCuspContact

noncomputable section

open HolGerm HironakaHolomorphicPointJets
  HironakaActualPrincipalHSFormula HironakaActualPrincipalJetMultiplication
  HironakaActualOriginalFormalTaylor HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaHolomorphicJetMonomialSpan HironakaActualZeroSectionStabilization HironakaHolomorphicJetChartInvariance

private abbrev t : HolGerm (ComplexModel 1) := normalCoordinate 0 1 0
private abbrev x : HolGerm (ComplexModel 2) := tangentPullback 1 1 t
private abbrev y : HolGerm (ComplexModel 2) := normalCoordinate 1 1 0

/-- The actual germ of the plane cusp with exponent `p`. -/
def cuspGerm (p : ℕ) : HolGerm (ComplexModel 2) := y ^ 2 - x ^ p

private theorem x_eq_chart_coordinate : x = normalCoordinate 0 2 0 := by
  unfold x t tangentPullback normalCoordinate coordinateGerm
  rw [compAlgHom_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Filter.Eventually.of_forall fun _ => rfl

private theorem cusp_taylor (p : ℕ) :
    originalTaylorAlgHom 2 (cuspGerm p) =
      (MvPowerSeries.X (1 : Fin 2)) ^ 2 - (MvPowerSeries.X (0 : Fin 2)) ^ p := by
  rw [cuspGerm, map_sub, map_pow, map_pow, x_eq_chart_coordinate,
    show y = normalCoordinate 0 2 1 from rfl,
    originalTaylorAlgHom_coordinate, originalTaylorAlgHom_coordinate]

private theorem cusp_order_two (p : ℕ) (hp : 2 < p) :
    let m := IsLocalRing.maximalIdeal (HolGerm (ComplexModel 2))
    cuspGerm p ∈ m ^ 2 ∧ cuspGerm p ∉ m ^ 3 := by
  have hDegree (i : Fin 2) (k : ℕ) : normalExponentDegree (Finsupp.single i k) = k := by
    simp [normalExponentDegree, Finsupp.single_apply]
  constructor
  · apply (mem_original_maximal_pow_iff_formal_coefficients_zero 2 2 _).mpr
    intro α hα
    rw [cusp_taylor, map_sub, MvPowerSeries.coeff_X_pow, MvPowerSeries.coeff_X_pow]
    have hy : α ≠ Finsupp.single 1 2 := fun h => (Nat.ne_of_lt hα) (h ▸ hDegree 1 2)
    have hx : α ≠ Finsupp.single 0 p := fun h => (Nat.ne_of_lt (hα.trans hp)) (h ▸ hDegree 0 p)
    simp only [if_neg hy, if_neg hx, sub_zero]
  · intro h
    have hZero := (mem_original_maximal_pow_iff_formal_coefficients_zero 2 3 _).mp h
      (Finsupp.single (1 : Fin 2) 2) (by rw [hDegree]; decide)
    have hNe : Finsupp.single (1 : Fin 2) 2 ≠ Finsupp.single 0 p := fun h =>
      (Nat.ne_of_lt hp) ((hDegree 1 2).symm.trans ((congrArg normalExponentDegree h).trans (hDegree 0 p)))
    rw [cusp_taylor, map_sub, MvPowerSeries.coeff_X_pow, MvPowerSeries.coeff_X_pow,
      if_pos rfl, if_neg hNe, sub_zero] at hZero
    exact one_ne_zero hZero

/-- All the actual whole plane-cusp Hilbert–Samuel values coincide for
exponents strictly above two. -/
theorem cusp_hilbertSamuel_eq (p q : ℕ) (hp : 2 < p) (hq : 2 < q) (l : ℕ) :
    hilbertSamuelValue (Ideal.span {cuspGerm p}) l =
      hilbertSamuelValue (Ideal.span {cuspGerm q}) l := by
  rw [hilbertSamuelValue_actual_principal _ 2 (cusp_order_two p hp).1 (cusp_order_two p hp).2,
    hilbertSamuelValue_actual_principal _ 2 (cusp_order_two q hq).1 (cusp_order_two q hq).2]

/-- The same cusp as an actual analytic ideal in a threefold, with its
ambient normal coordinate adjoined to the whole tangential ideal. -/
def embeddedCuspIdeal (p : ℕ) : Ideal (HolGerm (ComplexModel 3)) :=
  actualZeroSectionIdeal 2 1 (Ideal.span {cuspGerm p})

/-- Both embedded ideals have exact ambient ordinary order one. -/
theorem embeddedCusp_ordinary_order_one (p : ℕ) (hp : 2 < p) :
    let m := IsLocalRing.maximalIdeal (HolGerm (ComplexModel 3))
    embeddedCuspIdeal p ≤ m ∧ ¬ embeddedCuspIdeal p ≤ m ^ 2 := by

  have hBase : Ideal.span {cuspGerm p} ≤ IsLocalRing.maximalIdeal (HolGerm (ComplexModel 2)) := by
    apply Ideal.span_le.mpr
    rintro f (rfl : f = cuspGerm p)
    change cuspGerm p ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel 2))
    simpa only [pow_one] using
      Ideal.pow_le_pow_right (by decide : 1 ≤ 2) (cusp_order_two p hp).1
  constructor
  · rw [embeddedCuspIdeal, ← comap_planeTrace_eq_actualZeroSectionIdeal]
    apply (Ideal.comap_mono hBase).trans
    have h := comap_planeTrace_sup_maximalIdeal_pow 2 1 ⊥ 1
    rw [bot_sup_eq, pow_one, pow_one, show actualZeroSectionIdeal 2 1 ⊥ = normalIdeal 2 1 by
      simp [actualZeroSectionIdeal], sup_eq_right.mpr
        (HironakaSmoothSubmersionProjectionIdealColon.normalIdeal_le_actual_maximalIdeal 2 1)] at h
    exact h.le
  · intro hle
    have hMem : normalCoordinate 2 1 0 ∈ embeddedCuspIdeal p :=
      Ideal.mem_sup_right (Ideal.subset_span ⟨0, rfl⟩)
    have hZ := (mem_original_maximal_pow_iff_formal_coefficients_zero 3 2 _).mp
      (hle hMem) (Finsupp.single (2 : Fin 3) 1)
      (by simp [normalExponentDegree, Finsupp.single_apply])
    rw [show normalCoordinate 2 1 0 = normalCoordinate 0 3 2 from rfl,
      originalTaylorAlgHom_coordinate, MvPowerSeries.coeff_X, if_pos rfl] at hZ
    exact one_ne_zero hZ

/-- The actual threefold embeddings have the same entire original profile. -/
theorem embeddedCusp_hilbertSamuel_eq (p q : ℕ) (hp : 2 < p) (hq : 2 < q) (l : ℕ) :
    hilbertSamuelValue (embeddedCuspIdeal p) l = hilbertSamuelValue (embeddedCuspIdeal q) l := by
  exact (hilbertSamuelValue_actualZeroSectionIdeal 2 1 _ l).trans
    ((cusp_hilbertSamuel_eq p q hp hq l).trans (hilbertSamuelValue_actualZeroSectionIdeal 2 1 _ l).symm)

/-- The actual first trace from the threefold to its common linear contact
plane recovers its whole plane cusp ideal. -/
theorem embeddedCusp_plane_trace (p : ℕ) :
    Ideal.map (planeTrace 2 1).toRingHom (embeddedCuspIdeal p) = Ideal.span {cuspGerm p} :=
  map_actualZeroSectionIdeal_planeTrace 2 1 _

/-- The embedded cusp ideal is genuinely nonprincipal. The first jet
would require a principal generator of order one, whose next jet has
the wrong dimension. -/
theorem embeddedCusp_not_principal (p : ℕ) (hp : 2 < p) :
    ¬ ∃ f : HolGerm (ComplexModel 3), embeddedCuspIdeal p = Ideal.span {f} := by
  intro h
  obtain ⟨f, hf⟩ := h
  have hProfile (l : ℕ) : hilbertSamuelValue (embeddedCuspIdeal p) l =
      Nat.choose (2+l) 2 - (if 2 ≤ l then Nat.choose (2+(l-2)) 2 else 0) :=
    (hilbertSamuelValue_actualZeroSectionIdeal 2 1 _ l).trans
      (hilbertSamuelValue_actual_principal _ 2 (cusp_order_two p hp).1 (cusp_order_two p hp).2 l)
  have hF0 : f ≠ 0 := by
    intro h0
    have h := hProfile 1
    rw [hf, h0, Ideal.span_singleton_zero, hilbertSamuelValue] at h
    rw [bot_sup_eq, HironakaRelativeNormalActualBaseJetDimension.actualBaseJetDimension 3 1] at h
    norm_num at h
  have hGen (l : ℕ) := hilbertSamuelValue_actual_principal_order f hF0 l
  rw [← hf] at hGen
  have hOrder : actualGermOrder f hF0 = 1 := by
    have h₁ := (hGen 1).symm.trans (hProfile 1)
    cases he : actualGermOrder f hF0 with
    | zero => norm_num [he] at h₁
    | succ a =>
      cases a with
      | zero => rfl
      | succ b =>
        have hz : ¬ b.succ.succ ≤ 1 := by omega
        norm_num [he, hz] at h₁
  have h₂ := (hGen 2).symm.trans (hProfile 2)
  norm_num [hOrder] at h₂
  exact (by decide : ¬ Nat.choose 5 3 - 4 = Nat.choose 4 2 - 1) h₂

/-- The exact entire analytic trace to the common tangent line. -/
theorem cusp_tangent_trace (p : ℕ) : planeTrace 1 1 (cuspGerm p) = -(t ^ p) := by
  rw [cuspGerm, map_sub, map_pow, map_pow, planeTrace_normalCoordinate,
    planeTrace_tangentPullback, zero_pow (by decide : 2 ≠ 0), zero_sub]

/-- The tangent trace first fails the `(p+1)`st ambient maximal power.
This is a strict distinction on actual original analytic contact germs. -/
theorem cusp_tangent_trace_order (p : ℕ) :
    let m := IsLocalRing.maximalIdeal (HolGerm (ComplexModel 1))
    planeTrace 1 1 (cuspGerm p) ∈ m ^ p ∧ planeTrace 1 1 (cuspGerm p) ∉ m ^ (p+1) := by
  have hDegree : normalExponentDegree (Finsupp.single (0 : Fin 1) p) = p := by
    simp [normalExponentDegree, Finsupp.single_apply]
  have hTaylor : originalTaylorAlgHom 1 (planeTrace 1 1 (cuspGerm p)) =
      -((MvPowerSeries.X (0 : Fin 1)) ^ p) := by
    rw [cusp_tangent_trace, map_neg, map_pow, originalTaylorAlgHom_coordinate]
  constructor
  · apply (mem_original_maximal_pow_iff_formal_coefficients_zero 1 p _).mpr
    intro α hα
    have hNe : α ≠ Finsupp.single 0 p := fun h => (Nat.ne_of_lt hα) (h ▸ hDegree)
    rw [hTaylor, map_neg, MvPowerSeries.coeff_X_pow, if_neg hNe, neg_zero]
  · intro h
    have hZero := (mem_original_maximal_pow_iff_formal_coefficients_zero 1 (p+1) _).mp h
      (Finsupp.single (0 : Fin 1) p) (by rw [hDegree]; omega)
    rw [hTaylor, map_neg, MvPowerSeries.coeff_X_pow, if_pos rfl] at hZero
    exact one_ne_zero (neg_eq_zero.mp hZero)

end
end Hironaka.HironakaG8SameHSCuspContact
