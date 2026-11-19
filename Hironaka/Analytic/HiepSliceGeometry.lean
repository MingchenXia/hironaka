import Hironaka.Analytic.HiepSliceLemma
import Mathlib.MeasureTheory.Measure.Haar.Unique

set_option autoImplicit false

/-!
# Hiep's Lemma 2.1 for increasing sequences: polydiscs and slice coordinates

* `polydiscN p r`: the open polydisc in `ℂ^n`; openness, convexity, compact closure, and
  inclusion in a Euclidean ball;
* `splitCLE m : ℂ^{m+1} ≃L[ℂ] ℂ^m × ℂ`, whose inverse is `(w, u) ↦ sliceMap m u w`;
* `sliceMap_preimage_polydiscN`: the slice of a polydisc at a height inside its last disc
  is the polydisc of the remaining coordinates;
* `aemeasurable_lintegral_sliceMap_prod`: a finite integral over `S = L⁻¹(B × D)` gives a
  finite integral of `(w, u) ↦ G (w, u)` for the product of Lebesgue measures.  The two
  measures differ by a positive Haar scalar, which is never computed.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace Hironaka

noncomputable section



/-! ### Polydiscs in any dimension -/

/-- The open polydisc of centre `p` and radius `r` in `ℂ^n`. -/
def polydiscN {n : ℕ} (p : ComplexModel n) (r : ℝ) : Set (ComplexModel n) :=
  {z | ∀ i, ‖z i - p i‖ < r}

/-- The closed polydisc of centre `p` and radius `r` in `ℂ^n`. -/
def closedPolydiscN {n : ℕ} (p : ComplexModel n) (r : ℝ) : Set (ComplexModel n) :=
  {z | ∀ i, ‖z i - p i‖ ≤ r}

theorem openPolydisc_eq_polydiscN {m : ℕ} (p : ComplexModel (m + 1)) (r : ℝ) :
    openPolydisc p r = polydiscN p r := rfl

theorem isOpen_polydiscN {n : ℕ} (p : ComplexModel n) (r : ℝ) : IsOpen (polydiscN p r) := by
  have : polydiscN p r = ⋂ i, {z : ComplexModel n | ‖z i - p i‖ < r} := by
    ext z; simp [polydiscN]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_lt (by fun_prop) continuous_const

theorem isClosed_closedPolydiscN {n : ℕ} (p : ComplexModel n) (r : ℝ) :
    IsClosed (closedPolydiscN p r) := by
  have : closedPolydiscN p r = ⋂ i, {z : ComplexModel n | ‖z i - p i‖ ≤ r} := by
    ext z; simp [closedPolydiscN]
  rw [this]
  exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const

theorem convex_polydiscN {n : ℕ} (p : ComplexModel n) (r : ℝ) :
    Convex ℝ (polydiscN p r) := by
  have : polydiscN p r = ⋂ i, ((EuclideanSpace.proj (𝕜 := ℂ) i : ComplexModel n →L[ℂ] ℂ)
      : ComplexModel n →ₗ[ℂ] ℂ).restrictScalars ℝ ⁻¹' ball (p i) r := by
    ext z; simp [polydiscN, dist_eq_norm]
  rw [this]
  exact convex_iInter fun i => (convex_ball _ _).linear_preimage _

theorem norm_sub_le_sqrt_mul_of_mem_closedPolydiscN {n : ℕ} {p z : ComplexModel n} {r : ℝ}
    (hr : 0 ≤ r) (hz : z ∈ closedPolydiscN p r) : ‖z - p‖ ≤ Real.sqrt n * r := by
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i, ‖(z - p) i‖ ^ 2 ≤ n * r ^ 2 := by
    calc ∑ i, ‖(z - p) i‖ ^ 2 ≤ ∑ _i : Fin n, r ^ 2 :=
          Finset.sum_le_sum fun i _ => by
            simp only [PiLp.sub_apply]
            exact pow_le_pow_left₀ (norm_nonneg _) (hz i) 2
      _ = n * r ^ 2 := by simp
  calc Real.sqrt (∑ i, ‖(z - p) i‖ ^ 2) ≤ Real.sqrt (n * r ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt n * r := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hr]

theorem isCompact_closedPolydiscN {n : ℕ} (p : ComplexModel n) {r : ℝ} (hr : 0 ≤ r) :
    IsCompact (closedPolydiscN p r) :=
  (isCompact_closedBall p (Real.sqrt n * r)).of_isClosed_subset
    (isClosed_closedPolydiscN p r) fun z hz => by
      rw [mem_closedBall, dist_eq_norm]
      exact norm_sub_le_sqrt_mul_of_mem_closedPolydiscN hr hz

theorem polydiscN_subset_closedPolydiscN {n : ℕ} (p : ComplexModel n) (r : ℝ) :
    polydiscN p r ⊆ closedPolydiscN p r := fun _ hz i => (hz i).le

theorem closure_polydiscN_subset {n : ℕ} (p : ComplexModel n) (r : ℝ) :
    closure (polydiscN p r) ⊆ closedPolydiscN p r :=
  closure_minimal (polydiscN_subset_closedPolydiscN p r) (isClosed_closedPolydiscN p r)

theorem closedPolydiscN_subset_polydiscN {n : ℕ} (p : ComplexModel n) {r r' : ℝ}
    (hrr' : r < r') : closedPolydiscN p r ⊆ polydiscN p r' :=
  fun _ hz i => (hz i).trans_lt hrr'

theorem polydiscN_subset_ball {n : ℕ} (p : ComplexModel n) {r R : ℝ} (hr : 0 ≤ r)
    (hR : Real.sqrt n * r < R) : polydiscN p r ⊆ ball p R := fun z hz => by
  rw [mem_ball, dist_eq_norm]
  exact (norm_sub_le_sqrt_mul_of_mem_closedPolydiscN hr
    (polydiscN_subset_closedPolydiscN p r hz)).trans_lt hR

/-- A closed ball around a point of the closed polydisc of radius `s` lies in the closed
polydisc of radius `s + δ`. -/
theorem closedBall_subset_closedPolydiscN {n : ℕ} {p ζ : ComplexModel n} {s δ : ℝ}
    (hζ : ζ ∈ closedPolydiscN p s) : closedBall ζ δ ⊆ closedPolydiscN p (s + δ) := by
  intro x hx i
  rw [mem_closedBall, dist_eq_norm] at hx
  calc ‖x i - p i‖ = ‖(x i - ζ i) + (ζ i - p i)‖ := by ring_nf
    _ ≤ ‖x i - ζ i‖ + ‖ζ i - p i‖ := norm_add_le _ _
    _ ≤ δ + s := by
        refine add_le_add ?_ (hζ i)
        simpa using (PiLp.norm_apply_le (x - ζ) i).trans hx
    _ = s + δ := add_comm _ _

/-! ### Slice coordinates -/

/-- The first `m` coordinates of a point of `ℂ^{m+1}`. -/
def initCoords {m : ℕ} (x : ComplexModel (m + 1)) : ComplexModel m :=
  WithLp.toLp 2 fun i => x i.castSucc

@[simp] theorem initCoords_apply {m : ℕ} (x : ComplexModel (m + 1)) (i : Fin m) :
    initCoords x i = x i.castSucc := rfl

theorem sliceMap_initCoords {m : ℕ} (x : ComplexModel (m + 1)) :
    sliceMap m (x (Fin.last m)) (initCoords x) = x := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem initCoords_sliceMap {m : ℕ} (u : ℂ) (w : ComplexModel m) :
    initCoords (sliceMap m u w) = w := by
  ext i; simp

/-- The slice of a polydisc at a height inside its last disc is the polydisc of the
remaining coordinates. -/
theorem sliceMap_preimage_polydiscN {m : ℕ} (p : ComplexModel (m + 1)) {r : ℝ} {u : ℂ}
    (hu : ‖u - p (Fin.last m)‖ < r) :
    sliceMap m u ⁻¹' polydiscN p r = polydiscN (initCoords p) r := by
  ext w
  constructor
  · intro h i
    simpa using h i.castSucc
  · intro h i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hu
    · simpa using h j

/-- The splitting `ℂ^{m+1} ≃ ℂ^m × ℂ`. -/
def splitCLE (m : ℕ) : ComplexModel (m + 1) ≃L[ℂ] ComplexModel m × ℂ :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => (initCoords x, x (Fin.last m))
      invFun := fun q => sliceMap m q.2 q.1
      map_add' := fun x y => by
        ext i <;> simp
      map_smul' := fun a x => by
        ext i <;> simp
      left_inv := fun x => sliceMap_initCoords x
      right_inv := fun q => by
        ext i <;> simp [initCoords_sliceMap] }

@[simp] theorem splitCLE_apply {m : ℕ} (x : ComplexModel (m + 1)) :
    splitCLE m x = (initCoords x, x (Fin.last m)) := rfl

@[simp] theorem splitCLE_symm_apply {m : ℕ} (q : ComplexModel m × ℂ) :
    (splitCLE m).symm q = sliceMap m q.2 q.1 := rfl

theorem splitCLE_preimage_polydiscN {m : ℕ} (p : ComplexModel (m + 1)) (r : ℝ) :
    splitCLE m ⁻¹' (polydiscN (initCoords p) r ×ˢ ball (p (Fin.last m)) r) = polydiscN p r := by
  ext x
  simp only [mem_preimage, splitCLE_apply, mem_prod, polydiscN, Set.mem_ofPred_eq,
    initCoords_apply, mem_ball, dist_eq_norm, Fin.forall_fin_succ']

/-- A finite integral over a polydisc of `ℂ^{m+1}` is a finite integral in slice
coordinates, for the product of Lebesgue measures. -/
theorem aemeasurable_lintegral_sliceMap_prod {m : ℕ}
    [MeasurableSpace (ComplexModel (m + 1))] [BorelSpace (ComplexModel (m + 1))]
    [MeasurableSpace (ComplexModel m)] [BorelSpace (ComplexModel m)]
    (p : ComplexModel (m + 1)) (r : ℝ) {G : ComplexModel (m + 1) → ℝ≥0∞}
    (hG : AEMeasurable G (volume.restrict (polydiscN p r)))
    (hfin : ∫⁻ x in polydiscN p r, G x ≠ ⊤) :
    AEMeasurable (fun q : ComplexModel m × ℂ => G (sliceMap m q.2 q.1))
        ((volume.restrict (polydiscN (initCoords p) r)).prod
          (volume.restrict (ball (p (Fin.last m)) r))) ∧
      ∫⁻ q, G (sliceMap m q.2 q.1) ∂((volume.restrict (polydiscN (initCoords p) r)).prod
          (volume.restrict (ball (p (Fin.last m)) r))) ≠ ⊤ := by
  set e : ComplexModel (m + 1) ≃ᵐ ComplexModel m × ℂ :=
    (splitCLE m).toHomeomorph.toMeasurableEquiv with he
  set T : Set (ComplexModel m × ℂ) := polydiscN (initCoords p) r ×ˢ ball (p (Fin.last m)) r
  have hpre : e ⁻¹' T = polydiscN p r := splitCLE_preimage_polydiscN p r
  set μ' : Measure (ComplexModel m × ℂ) := volume.map e with hμ'
  have : μ'.IsAddHaarMeasure := (splitCLE m).isAddHaarMeasure_map volume
  set k := μ'.addHaarScalarFactor (volume.prod volume) with hk
  have hkpos : (k : ℝ≥0∞) ≠ 0 := by
    have := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ' (volume.prod volume)
    exact_mod_cast this.ne'
  have hsmul : μ' = k • (volume.prod volume) :=
    Measure.isAddLeftInvariant_eq_smul μ' (volume.prod volume)
  have hrestr : μ'.restrict T = (volume.restrict (polydiscN p r)).map e := by
    rw [hμ', e.restrict_map, hpre]
  have hprodres : μ'.restrict T = (k : ℝ≥0∞) •
      ((volume.restrict (polydiscN (initCoords p) r)).prod
        (volume.restrict (ball (p (Fin.last m)) r))) := by
    rw [hsmul, Measure.restrict_smul, Measure.prod_restrict]
    rfl
  have hGe : ∀ q, G (sliceMap m q.2 q.1) = G (e.symm q) := fun q => rfl
  constructor
  · rw [← aemeasurable_smul_measure_iff hkpos, ← hprodres, hrestr,
      aemeasurable_map_equiv_iff]
    refine hG.congr (Eventually.of_forall fun x => ?_)
    simp [hGe]
  · have hint : ∫⁻ q, G (e.symm q) ∂(μ'.restrict T) = ∫⁻ x in polydiscN p r, G x := by
      rw [hrestr, lintegral_map_equiv]
      simp
    rw [hprodres, lintegral_smul_measure] at hint
    intro htop
    simp only [hGe] at htop
    rw [htop, smul_eq_mul, ENNReal.mul_top hkpos] at hint
    exact hfin hint.symm

end

end Hironaka
