import Hironaka.Analytic.FlatteningTangentSpaceIndependence
import Hironaka.Analytic.SmoothPotentialDomination

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Step 6 of `prop:principalization` from ONE flattening

Source: Copy-4, Steps 4 and 6 of `prop:principalization`.

`Hironaka.ManifoldTubePositivity.exists_tube_forall_strictPosAt` and
`Hironaka.SmoothPotentialDomination.exists_tube_dominatesKahlerFormOn` ask for
strict positivity of `β` along `(dF)⁻¹(ℂᵏ × 0)` for **every** chart `f` and
**every** nondegenerate holomorphic flattening `F` of `W` in `f`.  Step 4 has to
hand that hypothesis over, and it can only ever produce *one* flattening per
point — the one regularity of `W` supplies.  That gap is the `hβ` obligation
recorded in I-0416/I-0417.

`Hironaka.FlatteningTangentSpaceIndependence.forall_admissible_flattening_of_exists`
closed the mathematical half: the subspace `(dF)⁻¹(ℂᵏ × 0)` does not depend on
`F`.  This module spends it, restating both conclusions with the hypothesis a
producer can actually meet:

* `PositiveOnOneFlattening W k β` — for each `w ∈ W`, *some* admissible
  flattening in the **preferred** chart at `w` has `β` strictly positive on its
  tangent directions.  Two quantifiers weaker than the original `hβ`: one
  flattening instead of all, and one chart instead of all.
* `exists_tube_dominatesKahlerFormOn_of_oneFlattening` and
  `exists_tube_forall_strictPosAt_of_oneFlattening` — the conclusions of the two
  theorems above, verbatim, from that hypothesis.
* `positiveOnOneFlattening_of_forall` — the original `hβ` implies it, so the two
  theorems here are strictly stronger than the ones they replace.  Nothing is
  restated in a weaker form and no statement elsewhere changes.

Everything here is sorry-free; the only nontrivial input is the independence
theorem.
-/

open Set Filter
open scoped Topology ContDiff

namespace Hironaka.TubePositivityOneFlattening

open Hironaka.PositiveClasses Hironaka.AnalyticGluingData
  PositivityPerturbation KahlerPerturbation GlobalTubeFunction ManifoldTubePositivity
  SmoothPotentialDomination FlatteningTangentSpaceIndependence

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-! ### The producible positivity hypothesis -/

/-- **`β` is strictly positive along `W` as a producer can state it.**  For every
`w ∈ W` there is *one* nondegenerate holomorphic flattening `F` of `W`, in the
*preferred* chart at `w`, with `β` strictly positive on the nonzero vectors that
`dF` sends into `ℂᵏ × 0`.

Compare the `hβ` of `ManifoldTubePositivity.exists_tube_forall_strictPosAt`,
which demands the same for every chart and every flattening. -/
def PositiveOnOneFlattening (W : Set M) (k : ℕ) (β : ClosedRealOneOneForm n M) :
    Prop :=
  ∀ w ∈ W, ∃ (F : ComplexModel n → ComplexModel n) (D : Set (ComplexModel n)),
    IsOpen D ∧ (complexChartAt (n := n) w).val w ∈ D ∧
      D ⊆ (complexChartAt (n := n) w).val.target ∧ ContDiffOn ℂ ∞ F D ∧
      Function.Injective (fderiv ℝ F ((complexChartAt (n := n) w).val w)) ∧
      (∀ z ∈ D, ((complexChartAt (n := n) w).val.symm z ∈ W ↔
        F z ∈ complexCoordinatePlane n k)) ∧
      ∀ v : ComplexModel n, v ≠ 0 →
        fderiv ℝ F ((complexChartAt (n := n) w).val w) v ∈
          complexCoordinatePlane n k →
        0 < quad (β.val.coeff (complexChartAt (n := n) w)
          ((complexChartAt (n := n) w).val w)) v

/-- **The canonical admissible flattening at a regular point**, read in the
preferred chart there.  `RegularAtDim` supplies the local biholomorphism `Φ`;
`GlobalTubeFunction.flatChartMap` packages it as a map of the ambient coordinate
space, and its differential is injective because it is a biholomorphism composed
with a chart transition.  This is the witness a producer of
`PositiveOnOneFlattening` has in hand. -/
theorem exists_admissible_flattening {W : Set M} {k : ℕ} {w : M}
    (hreg : RegularAtDim (n := n) W w k) :
    ∃ (F : ComplexModel n → ComplexModel n) (D : Set (ComplexModel n)),
      IsOpen D ∧ (complexChartAt (n := n) w).val w ∈ D ∧
        D ⊆ (complexChartAt (n := n) w).val.target ∧ ContDiffOn ℂ ∞ F D ∧
        Function.Injective (fderiv ℝ F ((complexChartAt (n := n) w).val w)) ∧
        ∀ z ∈ D, ((complexChartAt (n := n) w).val.symm z ∈ W ↔
          F z ∈ complexCoordinatePlane n k) := by
  obtain ⟨-, -, Φ, -, -, hΦflat⟩ := hreg
  have hwf : w ∈ (complexChartAt (n := n) w).val.source := mem_complexChartAt_source w
  have hsymm : (complexChartAt (n := n) w).val.symm ((complexChartAt (n := n) w).val w) = w :=
    (complexChartAt (n := n) w).val.left_inv hwf
  have hz₀ : (complexChartAt (n := n) w).val w ∈
      flatChartDomain (complexChartAt (n := n) w) (complexChartAt (n := n) w) Φ := by
    refine ⟨(complexChartAt (n := n) w).val.map_source hwf, ?_, ?_⟩
    · rw [hsymm]; exact mem_complexChartAt_source w
    · show (complexChartAt (n := n) w).val
        ((complexChartAt (n := n) w).val.symm ((complexChartAt (n := n) w).val w)) ∈ Φ.source
      rw [hsymm]; exact Φ.center_mem_source
  exact ⟨flatChartMap (complexChartAt (n := n) w) (complexChartAt (n := n) w) Φ,
    flatChartDomain (complexChartAt (n := n) w) (complexChartAt (n := n) w) Φ,
    isOpen_flatChartDomain _ _ _, hz₀, flatChartDomain_subset_target _ _ _,
    contDiffOn_flatChartMap _ _ _, fderiv_flatChartMap_injective _ _ _ hz₀,
    fun z hz => hΦflat hz.2.1 (Set.mem_preimage.mp hz.2.2)⟩

/-- The hypothesis of the two existing theorems implies the one used here: it is
the same statement with the chart and the flattening specialised. -/
theorem positiveOnOneFlattening_of_forall {W : Set M} {k : ℕ}
    (hWreg : ∀ x ∈ W, RegularAtDim (n := n) W x k)
    {β : ClosedRealOneOneForm n M}
    (hβ : ∀ (f : ComplexChart n M) (w : M), w ∈ W → w ∈ f.val.source →
      ∀ (F : ComplexModel n → ComplexModel n) (D : Set (ComplexModel n)),
        IsOpen D → f.val w ∈ D → D ⊆ f.val.target → ContDiffOn ℂ ∞ F D →
        Function.Injective (fderiv ℝ F (f.val w)) →
        (∀ z ∈ D, (f.val.symm z ∈ W ↔ F z ∈ complexCoordinatePlane n k)) →
        ∀ v : ComplexModel n, v ≠ 0 →
          fderiv ℝ F (f.val w) v ∈ complexCoordinatePlane n k →
          0 < quad (β.val.coeff f (f.val w)) v) :
    PositiveOnOneFlattening W k β := by
  intro w hw
  obtain ⟨F, D, hD, hzD, hDsub, hFc, hFinj, hFflat⟩ :=
    exists_admissible_flattening (W := W) (k := k) (hWreg w hw)
  exact ⟨F, D, hD, hzD, hDsub, hFc, hFinj, hFflat,
    hβ (complexChartAt (n := n) w) w hw (mem_complexChartAt_source w)
      F D hD hzD hDsub hFc hFinj hFflat⟩

/-! ### Transferring to every flattening -/

/-- **The `∃ → ∀` transfer, at the preferred chart.**  `PositiveOnOneFlattening`
already implies the positivity statement for *every* admissible flattening in
the preferred chart. -/
theorem forall_flattening_of_positiveOnOneFlattening {W : Set M} {k : ℕ}
    (hWreg : ∀ x ∈ W, RegularAtDim (n := n) W x k)
    {β : ClosedRealOneOneForm n M} (hβ : PositiveOnOneFlattening W k β) :
    ∀ w ∈ W, ∀ (F : ComplexModel n → ComplexModel n) (D : Set (ComplexModel n)),
      IsOpen D → (complexChartAt (n := n) w).val w ∈ D →
      D ⊆ (complexChartAt (n := n) w).val.target → ContDiffOn ℂ ∞ F D →
      Function.Injective (fderiv ℝ F ((complexChartAt (n := n) w).val w)) →
      (∀ z ∈ D, ((complexChartAt (n := n) w).val.symm z ∈ W ↔
        F z ∈ complexCoordinatePlane n k)) →
      ∀ v : ComplexModel n, v ≠ 0 →
        fderiv ℝ F ((complexChartAt (n := n) w).val w) v ∈
          complexCoordinatePlane n k →
        0 < quad (β.val.coeff (complexChartAt (n := n) w)
          ((complexChartAt (n := n) w).val w)) v := by
  intro w hw
  obtain ⟨F₀, D₀, hD₀, hz₀, hD₀sub, hF₀c, hF₀inj, hF₀flat, hF₀pos⟩ := hβ w hw
  have htr := forall_admissible_flattening_of_exists (W := W) (k := k) hw (hWreg w hw)
    (f := complexChartAt (n := n) w) (mem_complexChartAt_source w)
    (P := fun v => v ≠ 0 → 0 < quad (β.val.coeff (complexChartAt (n := n) w)
      ((complexChartAt (n := n) w).val w)) v)
    ⟨F₀, D₀, hD₀, hz₀, hD₀sub, hF₀c, hF₀inj, hF₀flat,
      fun v hmem hv => hF₀pos v hv hmem⟩
  intro F D hD hzD hDsub hFc hFinj hFflat v hv hmem
  exact htr F D hD hzD hDsub hFc hFinj hFflat v hmem hv

/-! ### The two conclusions, from one flattening -/

/-- **`ManifoldTubePositivity.exists_tube_forall_strictPosAt` from ONE
flattening.**  Conclusion verbatim; the `∀ chart, ∀ flattening` hypothesis is
replaced by `PositiveOnOneFlattening`. -/
theorem exists_tube_forall_strictPosAt_of_oneFlattening [CompactSpace M]
    {W : Set M} {k : ℕ}
    (hWclosed : IsClosed W) (hWreg : ∀ x ∈ W, RegularAtDim (n := n) W x k)
    (β : ClosedRealOneOneForm n M) (hβ : PositiveOnOneFlattening W k β) :
    ∃ (r : M → ℝ) (hr : ChartSmooth (n := n) r) (B : ℝ), 0 < B ∧
      (∀ y, 0 ≤ r y) ∧ (∀ w ∈ W, r w = 0) ∧
      ∃ U : Set M, IsOpen U ∧ W ⊆ U ∧
        ∀ y ∈ U, StrictPosAt (β + B • ddcClosedForm r hr).val y := by
  have hall := forall_flattening_of_positiveOnOneFlattening hWreg hβ
  obtain ⟨r, hr, hrnn, hrW, hlevi⟩ := exists_chartSmooth_tube hWclosed hWreg
  have hsemi : ∀ w ∈ W, ∀ v : ComplexModel n,
      0 ≤ leviForm (fun z => r ((complexChartAt (n := n) w).val.symm z))
        ((complexChartAt (n := n) w).val w) v := fun w hw v =>
    (hlevi (complexChartAt (n := n) w) w hw (mem_complexChartAt_source w)).1 v
  have hpos : ∀ w ∈ W, ∀ v : ComplexModel n, v ≠ 0 →
      leviForm (fun z => r ((complexChartAt (n := n) w).val.symm z))
        ((complexChartAt (n := n) w).val w) v = 0 →
      0 < quad (β.val.coeff (complexChartAt (n := n) w)
        ((complexChartAt (n := n) w).val w)) v := by
    intro w hw v hv hnull
    obtain ⟨-, F, D, hDopen, hzD, hDsub, hFholo, hFinj, hFflat, hker⟩ :=
      hlevi (complexChartAt (n := n) w) w hw (mem_complexChartAt_source w)
    exact hall w hw F D hDopen hzD hDsub hFholo hFinj hFflat v hv (hker v hnull)
  obtain ⟨B, hB, U, hU, hWU, hposU⟩ :=
    exists_pos_forall_strictPosAt_add_smul_ddc hWclosed.isCompact β hr hsemi hpos
  exact ⟨r, hr, B, hB, hrnn, hrW, U, hU, hWU, hposU⟩

/-- **Step 6 of `prop:principalization` from ONE flattening.**  The conclusion of
`SmoothPotentialDomination.exists_tube_dominatesKahlerFormOn`, verbatim, with the
`∀ chart, ∀ flattening` hypothesis replaced by `PositiveOnOneFlattening`. -/
theorem exists_tube_dominatesKahlerFormOn_of_oneFlattening [CompactSpace M]
    (omega : KahlerBackground n M) {W : Set M} {k : ℕ}
    (hWclosed : IsClosed W) (hWreg : ∀ x ∈ W, RegularAtDim (n := n) W x k)
    (β : ClosedRealOneOneForm n M) (hβ : PositiveOnOneFlattening W k β) :
    ∃ r : M → ℝ, ChartSmooth (n := n) r ∧ (∀ y, 0 ≤ r y) ∧ (∀ w ∈ W, r w = 0) ∧
      ∃ B : ℝ, 0 < B ∧ ∃ U : Set M, IsOpen U ∧ W ⊆ U ∧
        DominatesKahlerFormOn β (fun x => ((B * r x : ℝ) : EReal)) U := by
  have hall := forall_flattening_of_positiveOnOneFlattening hWreg hβ
  obtain ⟨r, hr, hrnn, hrW, hlevi⟩ := exists_chartSmooth_tube hWclosed hWreg
  refine ⟨r, hr, hrnn, hrW, ?_⟩
  refine exists_pos_dominatesKahlerFormOn_of_leviNull omega hWclosed.isCompact β hr
    (fun w hw v => (hlevi (complexChartAt (n := n) w) w hw
      (mem_complexChartAt_source w)).1 v) (fun w hw v hv hnull => ?_)
  obtain ⟨-, F, D, hDopen, hzD, hDsub, hFholo, hFinj, hFflat, hker⟩ :=
    hlevi (complexChartAt (n := n) w) w hw (mem_complexChartAt_source w)
  exact hall w hw F D hDopen hzD hDsub hFholo hFinj hFflat v hv (hker v hnull)

end

end Hironaka.TubePositivityOneFlattening
