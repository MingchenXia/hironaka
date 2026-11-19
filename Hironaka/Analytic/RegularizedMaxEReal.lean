import Hironaka.Analytic.ScaledSmoothMax
import Hironaka.Analytic.QuasiPshSingularities

set_option autoImplicit false

/-!
# A regularized maximum for extended-real potentials

`ScaledSmoothMax.scaledSmoothMax` is deliberately real-valued.  This file
extends its *pointwise algebra* to the extended-real values used by singular
potentials.  It preserves poles exactly: a pole in one input is discarded by
the maximum, while two common poles remain a pole.  The only invocation of the
real regularized maximum is on the finite branch; positive infinity is dealt
with separately and never sent through `EReal.toReal`.

There is intentionally no assertion here about plurisubharmonicity,
upper-semicontinuity, or closure across a pole locus.  Those are analytic and
topological questions beyond this algebraic interface.
-/

namespace Hironaka.RegularizedMaxEReal

open ScaledSmoothMax

noncomputable section

/-- The real-valued scale-`δ` regularized maximum, viewed as a binary scalar
operation.  Keeping this abbreviation makes explicit that the finite branch
of `eregularizedMax` uses the existing real construction. -/
def realRegularizedMax (δ a b : ℝ) : ℝ :=
  scaledSmoothMax δ (fun _ : Unit => a) (fun _ : Unit => b) ()

/-- The algebraic extended-real regularized maximum.

The `⊥` cases are handled first, so a common pole remains `⊥`.  The `⊤`
cases are handled before taking `toReal`; actual quasi-PSH applications supply
the stronger hypothesis that neither input is `⊤`. -/
def eregularizedMax (δ : ℝ) (u v : EReal) : EReal :=
  if _hu : u = ⊥ then v else
  if _hv : v = ⊥ then u else
  if _hu : u = ⊤ then ⊤ else
  if _hv : v = ⊤ then ⊤ else
  (realRegularizedMax δ u.toReal v.toReal : EReal)

@[simp]
theorem realRegularizedMax_apply (δ a b : ℝ) :
    realRegularizedMax δ a b =
      b + δ * SmoothMax.posPart ((a - b) / δ) := by
  simp [realRegularizedMax, scaledSmoothMax_apply]

@[simp]
theorem eregularizedMax_bot_left (δ : ℝ) (v : EReal) :
    eregularizedMax δ ⊥ v = v := by
  simp [eregularizedMax]

@[simp]
theorem eregularizedMax_bot_right (δ : ℝ) (u : EReal) :
    eregularizedMax δ u ⊥ = u := by
  by_cases hu : u = ⊥
  · subst u
    simp
  · simp [eregularizedMax, hu]

@[simp]
theorem eregularizedMax_top_left (δ : ℝ) (v : EReal) :
    eregularizedMax δ ⊤ v = ⊤ := by
  by_cases hv : v = ⊥
  · subst v
    simp
  · simp [eregularizedMax, hv]

@[simp]
theorem eregularizedMax_top_right (δ : ℝ) (u : EReal) :
    eregularizedMax δ u ⊤ = ⊤ := by
  by_cases hu : u = ⊥
  · subst u
    simp
  · simp [eregularizedMax, hu]

/-- The regularized maximum has a pole precisely at a common pole. -/
theorem eregularizedMax_eq_bot_iff (δ : ℝ) (u v : EReal) :
    eregularizedMax δ u v = ⊥ ↔ u = ⊥ ∧ v = ⊥ := by
  by_cases hu : u = ⊥
  · subst u
    simp
  · by_cases hv : v = ⊥
    · subst v
      simp [hu]
    · by_cases hu_top : u = ⊤
      · simp [eregularizedMax, hv, hu_top]
      · by_cases hv_top : v = ⊤
        · simp [eregularizedMax, hu, hu_top, hv_top]
        · rw [eregularizedMax]
          simp only [dif_neg hu, dif_neg hv, dif_neg hu_top, dif_neg hv_top]
          constructor
          · intro h
            exact (EReal.coe_ne_bot _ h).elim
          · rintro ⟨hu', _⟩
            exact (hu hu').elim

/-- No positive infinity can be produced from inputs which are not positive
infinity. -/
theorem eregularizedMax_ne_top {δ : ℝ} {u v : EReal}
    (hu : u ≠ ⊤) (hv : v ≠ ⊤) : eregularizedMax δ u v ≠ ⊤ := by
  by_cases hu_bot : u = ⊥
  · simp [eregularizedMax, hu_bot, hv]
  by_cases hv_bot : v = ⊥
  · simp [eregularizedMax, hu_bot, hv_bot, hu]
  rw [eregularizedMax]
  simp only [dif_neg hu_bot, dif_neg hv_bot, dif_neg hu, dif_neg hv]
  exact EReal.coe_ne_top _

/-- On the finite branch, `eregularizedMax` is exactly the real
regularized maximum, embedded into `EReal`. -/
theorem eregularizedMax_eq_coe_realRegularizedMax {δ : ℝ} {u v : EReal}
    (hu_top : u ≠ ⊤) (hu_bot : u ≠ ⊥) (hv_top : v ≠ ⊤) (hv_bot : v ≠ ⊥) :
    eregularizedMax δ u v = (realRegularizedMax δ u.toReal v.toReal : EReal) := by
  simp [eregularizedMax, hu_bot, hv_bot, hu_top, hv_top]

/-- The explicit finite formula, stated only when neither `toReal` can hide an
infinite value. -/
theorem eregularizedMax_eq_coe_formula {δ : ℝ} {u v : EReal}
    (hu_top : u ≠ ⊤) (hu_bot : u ≠ ⊥) (hv_top : v ≠ ⊤) (hv_bot : v ≠ ⊥) :
    eregularizedMax δ u v =
      (v.toReal + δ * SmoothMax.posPart ((u.toReal - v.toReal) / δ) : ℝ) := by
  rw [eregularizedMax_eq_coe_realRegularizedMax hu_top hu_bot hv_top hv_bot,
    realRegularizedMax_apply]

private theorem max_coe_toReal_eq {u v : EReal}
    (hu_top : u ≠ ⊤) (hu_bot : u ≠ ⊥) (hv_top : v ≠ ⊤) (hv_bot : v ≠ ⊥) :
    max u v = (max u.toReal v.toReal : ℝ) := by
  rw [← EReal.coe_toReal hu_top hu_bot, ← EReal.coe_toReal hv_top hv_bot]
  norm_cast

private theorem eregularizedMax_bounds_finite {δ : ℝ} (hδ : 0 < δ) {u v : EReal}
    (hu_top : u ≠ ⊤) (hu_bot : u ≠ ⊥) (hv_top : v ≠ ⊤) (hv_bot : v ≠ ⊥) :
    max u v ≤ eregularizedMax δ u v ∧
      eregularizedMax δ u v ≤ max u v + (δ : EReal) := by
  rw [eregularizedMax_eq_coe_realRegularizedMax hu_top hu_bot hv_top hv_bot,
    max_coe_toReal_eq hu_top hu_bot hv_top hv_bot]
  constructor
  · norm_cast
    change max u.toReal v.toReal ≤
      scaledSmoothMax δ (fun _ : Unit => u.toReal) (fun _ : Unit => v.toReal) ()
    exact max_le_scaledSmoothMax hδ (fun _ : Unit => u.toReal) (fun _ : Unit => v.toReal) ()
  · rw [← EReal.coe_add]
    norm_cast
    change scaledSmoothMax δ (fun _ : Unit => u.toReal) (fun _ : Unit => v.toReal) () ≤
      max u.toReal v.toReal + δ
    exact scaledSmoothMax_le_max_add hδ
      (fun _ : Unit => u.toReal) (fun _ : Unit => v.toReal) ()

/-- The ordinary maximum lies below the regularized maximum whenever neither
input is `⊤`.  This remains true at one or two pole values. -/
theorem max_le_eregularizedMax {δ : ℝ} (hδ : 0 < δ) {u v : EReal}
    (hu_top : u ≠ ⊤) (hv_top : v ≠ ⊤) :
    max u v ≤ eregularizedMax δ u v := by
  by_cases hu_bot : u = ⊥
  · subst u
    simp
  by_cases hv_bot : v = ⊥
  · subst v
    simp
  exact (eregularizedMax_bounds_finite hδ hu_top hu_bot hv_top hv_bot).1

/-- The error over the ordinary maximum is at most the finite scale `δ`, in
the extended-real order.  This includes the pole cases and never uses
subtraction of extended-real values. -/
theorem eregularizedMax_le_max_add {δ : ℝ} (hδ : 0 < δ) {u v : EReal}
    (hu_top : u ≠ ⊤) (hv_top : v ≠ ⊤) :
    eregularizedMax δ u v ≤ max u v + (δ : EReal) := by
  have hδ' : (0 : EReal) ≤ (δ : EReal) := by exact_mod_cast hδ.le
  by_cases hu_bot : u = ⊥
  · subst u
    simpa using (le_add_of_nonneg_right hδ' : v ≤ v + (δ : EReal))
  by_cases hv_bot : v = ⊥
  · subst v
    simpa [hu_bot] using (le_add_of_nonneg_right hδ' : u ≤ u + (δ : EReal))
  exact (eregularizedMax_bounds_finite hδ hu_top hu_bot hv_top hv_bot).2

/-- The two-sided comparison with the ordinary maximum. -/
theorem max_le_eregularizedMax_le_max_add {δ : ℝ} (hδ : 0 < δ) {u v : EReal}
    (hu_top : u ≠ ⊤) (hv_top : v ≠ ⊤) :
    max u v ≤ eregularizedMax δ u v ∧
      eregularizedMax δ u v ≤ max u v + (δ : EReal) :=
  ⟨max_le_eregularizedMax hδ hu_top hv_top,
    eregularizedMax_le_max_add hδ hu_top hv_top⟩

/-- A pointwise finite-scale regularized maximum has the bounded additive
singularity type of the ordinary pointwise maximum. -/
theorem sameSingularityTypeOn_eregularizedMax_max {X : Type*} {δ : ℝ}
    (hδ : 0 < δ) (u v : X → EReal) (U : Set X)
    (h_top : ∀ x ∈ U, u x ≠ ⊤ ∧ v x ≠ ⊤) :
    SameSingularityTypeOn (fun x => eregularizedMax δ (u x) (v x))
      (fun x => max (u x) (v x)) U := by
  constructor
  · refine ⟨δ, fun x hx => ?_⟩
    exact eregularizedMax_le_max_add hδ (h_top x hx).1 (h_top x hx).2
  · exact MoreSingularOn.of_le fun x hx =>
      max_le_eregularizedMax hδ (h_top x hx).1 (h_top x hx).2

/-- If the two inputs have bounded additive difference, their regularized
maximum has the same bounded singularity type as the left input.  This is the
order-level consequence usable before any PSH closure theorem. -/
theorem sameSingularityTypeOn_eregularizedMax_left {X : Type*} {δ : ℝ}
    (hδ : 0 < δ) (u v : X → EReal) (U : Set X)
    (h_top : ∀ x ∈ U, u x ≠ ⊤ ∧ v x ≠ ⊤)
    (h_same : SameSingularityTypeOn u v U) :
    SameSingularityTypeOn (fun x => eregularizedMax δ (u x) (v x)) u U := by
  constructor
  · obtain ⟨C, hC⟩ := h_same.2
    refine ⟨max 0 C + δ, fun x hx => ?_⟩
    have hC0 : (0 : EReal) ≤ ((max 0 C : ℝ) : EReal) :=
      EReal.coe_nonneg.mpr (le_max_left 0 C)
    have hCC0 : (C : EReal) ≤ ((max 0 C : ℝ) : EReal) :=
      EReal.coe_le_coe_iff.mpr (le_max_right 0 C)
    have hmax : max (u x) (v x) ≤ u x + ((max 0 C : ℝ) : EReal) := by
      apply max_le
      · simpa using (le_add_of_nonneg_right hC0 :
          u x ≤ u x + ((max 0 C : ℝ) : EReal))
      · exact (hC x hx).trans (add_le_add_right hCC0 _)
    calc
      eregularizedMax δ (u x) (v x) ≤ max (u x) (v x) + (δ : EReal) :=
        eregularizedMax_le_max_add hδ (h_top x hx).1 (h_top x hx).2
      _ ≤ (u x + ((max 0 C : ℝ) : EReal)) + (δ : EReal) :=
        add_le_add_left hmax _
      _ = u x + ((max 0 C + δ : ℝ) : EReal) := by
        rw [EReal.coe_add, add_assoc]
  · exact MoreSingularOn.of_le fun x hx =>
      (le_max_left (u x) (v x)).trans
        (max_le_eregularizedMax hδ (h_top x hx).1 (h_top x hx).2)

/-- The corresponding right-input singularity-type statement. -/
theorem sameSingularityTypeOn_eregularizedMax_right {X : Type*} {δ : ℝ}
    (hδ : 0 < δ) (u v : X → EReal) (U : Set X)
    (h_top : ∀ x ∈ U, u x ≠ ⊤ ∧ v x ≠ ⊤)
    (h_same : SameSingularityTypeOn u v U) :
    SameSingularityTypeOn (fun x => eregularizedMax δ (u x) (v x)) v U := by
  exact (sameSingularityTypeOn_eregularizedMax_left hδ u v U h_top h_same).trans h_same

end

end Hironaka.RegularizedMaxEReal
