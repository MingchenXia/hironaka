import Hironaka.Resolution.HironakaG11PresLineChart
import Hironaka.Resolution.HironakaOriginalSmoothSubmersionIntrinsicHS
import Hironaka.Resolution.HironakaOriginalCanonicalDimensionList

/-!
# Native line stability (goal G11, step (3a-lines)): PROVED

`HironakaG11PresLineState.NativeLineStability` was the first of the two named inputs of the G11 reduction
(`Hironaka HironakaG11PresReduction.compactSingularCentreResolution_of_nativeLineStability`). It is proved here: a marked ideal in
the native Hilbert–Samuel state for `(W, H)` gives, after the product with a line, a marked ideal in the native state for
`(W × ℂ, lineHS H)` (Bierstone–Milman 1997, Thm 9.4, test (ii)).

* `sum_normalExponentIndex_one`, **`hilbertSamuelAt_line`**: `HS(W × ℂ, (x, t)) = lineHS (HS(W, x))` (the convolution formula
  `HironakaOriginalSmoothSubmersionIntrinsicHS.hilbertSamuelAt_original_submersion_convolution` with one normal variable);
* `lineHS_eq_iff` (`lineHS` is injective), `lineHS_mono`;
* `isSingularHSValue_lineHS`: `(a₀, 0)` is a singular point of `W₀ × ℂ` with Hilbert–Samuel function `lineHS H`
  (`HironakaOriginalCanonicalDimensionList.singularSet_preimage_eq`);
* **`nativeLineStability : NativeLineStability`**: the native data are the lifted vertices, selector, enumeration and words
  (`HironakaG11PresLineFormal`), the point presentations are `HironakaG11PresLineChart.point_presentation_line`, the
  cosupport is `cosupp Q × ℂ` (`HironakaSmoothSubmersionRelativeOrder.cosupport_preimage_eq`).

Nothing here proves or assumes G11. Blueprint: `hironaka-g11-pres-line-state.tex`.
-/

set_option autoImplicit false

open Set Filter Classical
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG11PresLineStable

noncomputable section

open Hironaka.HolomorphicIdealSheaves BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaEmbeddedAnalytic HironakaHolomorphicJetChartInvariance HironakaRelativeNormalMonomialBasis HironakaActualCauchyMonomialDivision
  HironakaG11PresLineState HironakaG11PresLineFormal HironakaG11PresLineChart
open Hironaka.HironakaActualProjectionTestRecord (projectionTest projectionAmbient)
open scoped ProductComplexManifold

variable {n : ℕ}

/-! ### The Hilbert–Samuel function of `W × ℂ` -/

theorem sum_normalExponentIndex_one (f : ℕ → ℕ) (ℓ : ℕ) :
    let := normalExponentFintype 1 (ℓ + 1)
    ∑ α : normalExponentIndex 1 (ℓ + 1), f (ℓ - normalExponentDegree α.val) = lineHS f ℓ := by
  intro inst
  have hdeg : ∀ α : Fin 1 →₀ ℕ, normalExponentDegree α = α 0 := by
    intro α
    simp [normalExponentDegree]
  let e : normalExponentIndex 1 (ℓ + 1) ≃ Fin (ℓ + 1) :=
    { toFun := fun α => ⟨α.val 0, by have := α.property; rwa [hdeg] at this⟩
      invFun := fun j => ⟨Finsupp.single 0 j.val, by rw [hdeg, Finsupp.single_eq_same]; exact j.isLt⟩
      left_inv := fun α => Subtype.ext (Finsupp.ext fun i => by fin_cases i; simp)
      right_inv := fun j => Fin.ext (by simp) }
  rw [Fintype.sum_equiv e _ (fun j : Fin (ℓ + 1) => f (ℓ - j.val)) (fun α => by simp [e, hdeg]),
    Fin.sum_univ_eq_sum_range (fun j => f (ℓ - j)) (ℓ + 1)]
  have h := Finset.sum_range_reflect f (ℓ + 1)
  simp only [Nat.add_sub_cancel] at h
  rw [h]
  rfl

/-- **The Hilbert–Samuel function of `W × ℂ` at `(x, t)` is `lineHS` of that of `W` at `x`.** -/
theorem hilbertSamuelAt_line {X : CMfd.{0} n} (W : Set X) (hW : (vanishingIdeal (n := n) W).IsCoherent)
    (p : projectionAmbient X) :
    hilbertSamuelAt (vanishingIdeal (n := n+1) ((Prod.fst : projectionAmbient X → X) ⁻¹' W)) p =
      lineHS (hilbertSamuelAt (vanishingIdeal (n := n) W) p.1) := by
  funext ℓ
  rw [← vanishingIdeal_line,
    HironakaOriginalSmoothSubmersionIntrinsicHS.hilbertSamuelAt_original_submersion_convolution (r := 1)
      (ProductComplexManifold.contMDiff_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1)) _ hW p
      ((HironakaAuxiliaryGraphGeometry.isSubmersion_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1)).isSubmersionAt p)
      ℓ]
  exact sum_normalExponentIndex_one _ ℓ

theorem lineHS_succ (A : ℕ → ℕ) (ℓ : ℕ) : lineHS A (ℓ + 1) = lineHS A ℓ + A (ℓ + 1) :=
  Finset.sum_range_succ A (ℓ + 1)

/-- `lineHS` is injective. -/
theorem lineHS_eq_iff (A B : ℕ → ℕ) : (∀ ℓ, lineHS A ℓ = lineHS B ℓ) ↔ ∀ ℓ, A ℓ = B ℓ := by
  constructor
  · intro h ℓ
    cases ℓ with
    | zero => simpa [lineHS] using h 0
    | succ ℓ =>
      have h1 := h (ℓ + 1)
      rw [lineHS_succ, lineHS_succ, h ℓ] at h1
      omega
  · intro h ℓ
    unfold lineHS
    exact Finset.sum_congr rfl fun j _ => h j

/-- `lineHS` is monotone. -/
theorem lineHS_mono {A B : ℕ → ℕ} (h : ∀ ℓ, A ℓ ≤ B ℓ) (ℓ : ℕ) : lineHS A ℓ ≤ lineHS B ℓ :=
  Finset.sum_le_sum fun j _ => h j

/-- **`lineHS H` is a singular Hilbert–Samuel value** when `H` is: `(a₀, 0)` is a singular point of `W₀ × ℂ`. -/
theorem isSingularHSValue_lineHS {H : ℕ → ℕ} (h : IsSingularHSValue H) : IsSingularHSValue (lineHS H) := by
  obtain ⟨m, X₀, W₀, a₀, hW₀, ha₀, hH⟩ := h
  refine ⟨m + 1, projectionAmbient X₀, (Prod.fst : projectionAmbient X₀ → X₀) ⁻¹' W₀, (a₀, 0),
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
      (ProductComplexManifold.contMDiff_fst (n := m) (m := 1) (X := X₀) (Y := ComplexModel 1)) hW₀, ?_, ?_⟩
  · rw [HironakaOriginalCanonicalDimensionList.singularSet_preimage_eq (n := m) (m := m + 1) (X := X₀)
      (Y := projectionAmbient X₀) (b := Prod.fst)
      (HironakaAuxiliaryGraphGeometry.isSubmersion_fst (n := m) (m := 1) (X := X₀) (Y := ComplexModel 1)) W₀]
    exact ha₀
  · rw [hilbertSamuelAt_line W₀ (CartanIrreducible.cartanCoherence W₀ hW₀)]
    exact congrArg lineHS hH

/-! ### Native line stability -/

/-- **Native line stability (step (3a-lines)) holds**: the native Hilbert–Samuel state is stable under the product with a
line (BM97 Thm 9.4, test (ii)). -/
theorem nativeLineStability : NativeLineStability := by
  intro n X Q W H h
  obtain ⟨hH, hW, hQN, hQI, V, S, k, a, w, hw, hPos, hOwn, hMark, hCut, hUpper, hAt⟩ := h
  have hWc := CartanIrreducible.cartanCoherence W hW
  have hcos : (projectionTest Q).cosupp = (Prod.fst : projectionAmbient X → X) ⁻¹' Q.cosupp :=
    HironakaSmoothSubmersionRelativeOrder.cosupport_preimage_eq
      (HironakaAuxiliaryGraphGeometry.isSubmersion_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1)) hQI Q.N Q.d
  refine ⟨isSingularHSValue_lineHS hH,
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
      (ProductComplexManifold.contMDiff_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1)) hW, ?_,
    GermIdealPullbackCalculus.isCoherent_pullback (ProductComplexManifold.contMDiff_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1)) hQI,
    liftVertices V, liftSelector S, k, a.trans (liftVertexEquiv V), fun i => liftWord (w i), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (Prod.fst : projectionAmbient X → X) ⁻¹' Q.N = univ
    rw [hQN, preimage_univ]
  · intro i
    rw [wordExponent_liftWord, hw, Equiv.trans_apply, liftVertexEquiv_val]
  · intro v'
    rw [← liftVertexEquiv_symm_val v', normalExponentDegree_liftExp]
    exact hPos _
  · intro i
    rw [wordExponent_liftWord, historicalOwner_liftWord]
    exact hOwn i
  · change Q.d = _
    rw [hMark, weightedCommonMark_liftVertices]
  · rw [hcos, hCut]
    ext p
    simp only [mem_preimage, mem_ofPred_eq]
    rw [hilbertSamuelAt_line W hWc p, lineHS_eq_iff]
  · intro p ℓ
    rw [hilbertSamuelAt_line W hWc p]
    exact lineHS_mono (hUpper p.1) ℓ
  · intro p hp
    rw [hcos] at hp
    exact point_presentation_line S a w W hWc Q hQI p (hAt p.1 hp)

/-- **Native records for the same `(W, H)` are locally equivalent** (`s(i,ii)` with local blowings-up), unconditionally. -/
theorem locWPEquiv_native {X : CMfd.{0} n} {P Q : MarkedIdeal n X} {W : Set X} {H : ℕ → ℕ}
    (hP : NativeHSState P W H) (hQ : NativeHSState Q W H) (hE : Q.E = P.E) :
    HironakaG8LocalHistory.LocWPEquiv P Q :=
  locWPEquiv_of_nativeHSState nativeLineStability hP hQ hE

end

end Hironaka.HironakaG11PresLineStable
