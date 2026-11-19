import Hironaka.Analytic.GAGA.CoreBRungeKernel
import Hironaka.Analytic.GAGA.CoreBCousin
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Polynomial approximation on compact convex product sets

Infrastructure of lane SERRE-CORE2 (Serre's GAGA, towards source `lma:GAGA`), step M2.2 of the
plan in `blueprint/src/claude-serre-core.tex` (see `blueprint/src/claude-serre-core2.tex`).
Source for the mathematics: the Oka--Weil theorem for compact convex product sets, in the
elementary form of an iterated Cauchy integral (Gunning--Rossi, *Analytic functions of several
complex variables*, I.F; Hörmander, *An introduction to complex analysis in several
variables*, Thm. 2.7.7 for the one-variable step).

**Theorem** (`exists_mvPolynomial_approx`). Let `C_k ⊆ ℂ` (`k < n`) be compact and convex and
`Q = {z ∈ ℂⁿ : z_k ∈ C_k ∀ k}`. Every function holomorphic on a neighbourhood of `Q` is a
uniform limit on `Q` of polynomials.

Proof, one coordinate at a time. Let `ψ` be a cutoff in the variable `z_k`, equal to `1` near
`C_k`. For `z` near `Q`, the Cauchy--Pompeiu formula in `z_k` (from `Hironaka`)
gives `a(z) = π⁻¹ ∫ ∂̄ψ(ζ) a(z^{k←ζ}) (z_k - ζ)⁻¹ dA(ζ)`, where `z^{k←ζ}` replaces the
coordinate `z_k` by `ζ` (`cauchy_pompeiu_cutoff`). The kernel is approximated on
`supp ∂̄ψ × C_k` by `∑_i χ_i(ζ) p_i(z_k)` (`exists_kernel_approx`), so
`a ≈ ∑_i p_i(z_k) c_i` on `Q` with `c_i(z) = π⁻¹ ∫ χ_i ∂̄ψ(ζ) a(z^{k←ζ}) dA(ζ)`. The `c_i` are
holomorphic near `Q` (differentiation under the integral, `differentiableOn_integral_rep`),
do not depend on `z_k`, and do not depend on the coordinates that `a` does not depend on
(`exists_slice_approx`). Iterating over the coordinates leaves coefficients independent of all
coordinates, i.e. constants.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter Metric MeasureTheory Complex
open Hironaka.CauchyGreen (dbarDir dbarDir_congr dbarDir_const
  dbarDir_ofReal_mul)
open scoped Topology ContDiff Real

namespace Hironaka.Analytic.GAGA.Core.Runge

noncomputable section

variable {n : ℕ}

/-! ### Replacing one coordinate -/

/-- The point `z` with its coordinate `k` replaced by `w`. -/
def rep (z : EuclideanSpace ℂ (Fin n)) (k : Fin n) (w : ℂ) : EuclideanSpace ℂ (Fin n) :=
  z + (w - z k) • EuclideanSpace.single k (1 : ℂ)

theorem rep_apply (z : EuclideanSpace ℂ (Fin n)) (k : Fin n) (w : ℂ) (l : Fin n) :
    rep z k w l = if l = k then w else z l := by
  by_cases h : l = k
  · subst h
    simp [rep]
  · simp [rep, h]

theorem rep_self (z : EuclideanSpace ℂ (Fin n)) (k : Fin n) : rep z k (z k) = z := by
  simp [rep]

theorem rep_rep_same (z : EuclideanSpace ℂ (Fin n)) (k : Fin n) (w w' : ℂ) :
    rep (rep z k w) k w' = rep z k w' := by
  ext l
  simp only [rep_apply]
  split_ifs <;> rfl

theorem rep_comm (z : EuclideanSpace ℂ (Fin n)) {k l : Fin n} (h : l ≠ k) (w ζ : ℂ) :
    rep (rep z l w) k ζ = rep (rep z k ζ) l w := by
  ext j
  simp only [rep_apply]
  by_cases hj : j = k
  · subst hj
    simp [h.symm]
  · by_cases hjl : j = l
    · subst hjl
      simp [hj]
    · simp [hj, hjl]

/-- The linear part `z ↦ z - z_k e_k` of `z ↦ z^{k←ζ}`. -/
def repLin (k : Fin n) : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  ContinuousLinearMap.id ℂ _ -
    (EuclideanSpace.proj k : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).smulRight
      (EuclideanSpace.single k (1 : ℂ))

theorem rep_eq_repLin (z : EuclideanSpace ℂ (Fin n)) (k : Fin n) (ζ : ℂ) :
    rep z k ζ = repLin k z + ζ • EuclideanSpace.single k (1 : ℂ) := by
  simp only [rep, repLin, FunLike.coe_sub, Pi.sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, sub_smul]
  rw [show (EuclideanSpace.proj k : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ) z = z k from rfl]
  abel

theorem hasFDerivAt_rep (z : EuclideanSpace ℂ (Fin n)) (k : Fin n) (ζ : ℂ) :
    HasFDerivAt (fun z => rep z k ζ) (repLin k) z := by
  have : (fun z => rep z k ζ) = fun z => repLin k z + ζ • EuclideanSpace.single k (1 : ℂ) :=
    funext fun z => rep_eq_repLin z k ζ
  rw [this]
  exact (repLin k).hasFDerivAt.add_const _

theorem continuous_rep (k : Fin n) :
    Continuous fun p : EuclideanSpace ℂ (Fin n) × ℂ => rep p.1 k p.2 := by
  have : (fun p : EuclideanSpace ℂ (Fin n) × ℂ => rep p.1 k p.2) =
      fun p => repLin k p.1 + p.2 • EuclideanSpace.single k (1 : ℂ) :=
    funext fun p => rep_eq_repLin p.1 k p.2
  rw [this]
  exact ((repLin k).continuous.comp continuous_fst).add (continuous_snd.smul continuous_const)

theorem continuous_rep_right (z : EuclideanSpace ℂ (Fin n)) (k : Fin n) :
    Continuous fun ζ : ℂ => rep z k ζ :=
  (continuous_rep k).comp (continuous_const.prodMk continuous_id)

theorem differentiable_rep_right (z : EuclideanSpace ℂ (Fin n)) (k : Fin n) :
    Differentiable ℂ fun ζ : ℂ => rep z k ζ := by
  have : (fun ζ : ℂ => rep z k ζ) = fun ζ => repLin k z + ζ • EuclideanSpace.single k (1 : ℂ) :=
    funext fun ζ => rep_eq_repLin z k ζ
  rw [this]
  exact (differentiable_id.smul_const _).const_add _

/-- `g` does not depend on the coordinate `l`. -/
def IndepCoord (g : EuclideanSpace ℂ (Fin n) → ℂ) (l : Fin n) : Prop :=
  ∀ z w, g (rep z l w) = g z

/-- A function independent of every coordinate is constant. -/
theorem eq_zero_of_indepCoord {g : EuclideanSpace ℂ (Fin n) → ℂ} (hg : ∀ l, IndepCoord g l)
    (z : EuclideanSpace ℂ (Fin n)) : g z = g 0 := by
  classical
  suffices h : ∀ T : Finset (Fin n), ∀ z : EuclideanSpace ℂ (Fin n), (∀ l ∉ T, z l = 0) →
      g z = g 0 from h Finset.univ z (fun l hl => absurd (Finset.mem_univ l) hl)
  intro T
  induction T using Finset.induction_on with
  | empty =>
      intro z hz
      congr 1
      ext l
      simpa using hz l (Finset.notMem_empty l)
  | insert l T hl ih =>
      intro z hz
      rw [← hg l z 0]
      refine ih _ fun j hj => ?_
      rw [rep_apply]
      split_ifs with hjl
      · rfl
      · exact hz j fun h => (Finset.mem_insert.1 h).elim hjl hj

/-! ### Continuity of products with cut-off functions -/

/-- A continuous function with support in an open set `U`, times a function continuous on `U`,
is continuous. -/
theorem continuous_smul_of_tsupport {α E : Type*} [TopologicalSpace α] [NormedAddCommGroup E]
    [NormedSpace ℂ E] {g : α → ℂ} {h : α → E} {U : Set α} (hU : IsOpen U)
    (hg : Continuous g) (hgU : tsupport g ⊆ U) (hh : ContinuousOn h U) :
    Continuous fun x => g x • h x := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  by_cases hx : x ∈ U
  · exact hg.continuousAt.smul (hh.continuousAt (hU.mem_nhds hx))
  · have hxs : x ∉ tsupport g := fun h' => hx (hgU h')
    have hev : (fun x => g x • h x) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isClosed_tsupport g).isOpen_compl.mem_nhds hxs] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
    exact continuousAt_const.congr hev.symm

theorem continuous_mul_of_tsupport {α : Type*} [TopologicalSpace α] {g h : α → ℂ}
    {U : Set α} (hU : IsOpen U) (hg : Continuous g) (hgU : tsupport g ⊆ U)
    (hh : ContinuousOn h U) : Continuous fun x => g x * h x :=
  continuous_smul_of_tsupport hU hg hgU hh


/-! ### Cauchy--Pompeiu with a cutoff -/

open Hironaka.CauchyGreen in
theorem dbar_eq_dbarDir (f : ℂ → ℂ) (w : ℂ) : dbar f w = dbarDir (1 : ℂ) f w := by
  simp [dbar, dbarDir]

open Hironaka.CauchyGreen in
/-- **Cauchy--Pompeiu formula with a cutoff.** Let `ψ` be a smooth compactly supported cutoff
with `ψ(w₀) = 1`, and let `φ` be holomorphic on an open set containing `tsupport ψ`. Then
`φ(w₀) = π⁻¹ ∫ ∂̄ψ(ζ) φ(ζ) (w₀ - ζ)⁻¹ dA(ζ)`. -/
theorem cauchy_pompeiu_cutoff {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    {V : Set ℂ} (hV : IsOpen V) (hψV : tsupport ψ ⊆ V) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ V) {w₀ : ℂ} (hw₀ : ψ w₀ = 1) :
    φ w₀ = (π : ℂ)⁻¹ * ∫ ζ : ℂ, dbar (fun w => (ψ w : ℂ)) ζ * φ ζ * (w₀ - ζ)⁻¹ := by
  set ψc : ℂ → ℂ := fun w => (ψ w : ℂ) with hψcdef
  set Φ : ℂ → ℂ := fun w => ψc w * φ w with hΦdef
  have hψcc : ContDiff ℝ ∞ ψc := ofRealCLM.contDiff.comp hψ
  have hφC : ∀ x ∈ V, ContDiffAt ℝ ∞ φ x := fun x hx =>
    Hironaka.contDiffAt_real_of_differentiableOn_complex hφ hV hx
  have hzero : ∀ x, x ∉ tsupport ψ → ψc =ᶠ[𝓝 x] fun _ => 0 := fun x hx => by
    filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hx] with y hy
    simp [ψc, image_eq_zero_of_notMem_tsupport hy]
  have hΦzero : ∀ x, x ∉ tsupport ψ → Φ =ᶠ[𝓝 x] fun _ => 0 := fun x hx =>
    (hzero x hx).mono fun y hy => by simp only [Φ, hy, zero_mul]
  have hΦ : ContDiff ℝ 1 Φ := by
    refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hx : x ∈ tsupport ψ
    · exact (hψcc.contDiffAt.mul (hφC x (hψV hx))).of_le (by simp)
    · exact contDiffAt_const.congr_of_eventuallyEq (hΦzero x hx)
  have hΦc : HasCompactSupport Φ := by
    refine HasCompactSupport.intro hψc fun x hx => ?_
    simp [Φ, ψc, image_eq_zero_of_notMem_tsupport hx]
  set Φt : ℂ → ℂ := fun w => Φ (w₀ + w) with hΦtdef
  have hΦt : ContDiff ℝ 1 Φt := hΦ.comp (contDiff_const.add contDiff_id)
  have hΦtc : HasCompactSupport Φt := hΦc.comp_homeomorph (Homeomorph.addLeft w₀)
  have hP := integral_inv_mul_dbar hΦt hΦtc
  -- the `∂̄` of the translate
  have hdbar : ∀ ζ, dbar Φ ζ = dbar ψc ζ * φ ζ := by
    intro ζ
    by_cases hζ : ζ ∈ tsupport ψ
    · have hφd : DifferentiableAt ℂ φ ζ := hφ.differentiableAt (hV.mem_nhds (hψV hζ))
      rw [dbar_eq_dbarDir, dbar_eq_dbarDir]
      have := dbarDir_ofReal_mul (v := (1 : ℂ)) (χ := ψ) (a := φ) (x := ζ)
        ((hψ.differentiable (by simp)) ζ) (hφd.restrictScalars ℝ)
      rw [show Φ = fun y => (ψ y : ℂ) * φ y from rfl, this,
        Hironaka.Analytic.GAGA.Core.Cousin.dbarDir_eq_zero_of_differentiableAt hφd, mul_zero, add_zero]
    · rw [dbar_eq_dbarDir, dbar_eq_dbarDir, dbarDir_congr (hΦzero ζ hζ),
        dbarDir_congr (hzero ζ hζ), dbarDir_const, zero_mul]
  have hdbart : ∀ w, dbar Φt w = dbar ψc (w₀ + w) * φ (w₀ + w) := by
    intro w
    rw [← hdbar]
    simp only [dbar, hΦtdef, fderiv_comp_add_left]
  simp_rw [hdbart] at hP
  have htrans : ∫ w : ℂ, w⁻¹ * (dbar ψc (w₀ + w) * φ (w₀ + w)) =
      ∫ ζ : ℂ, (ζ - w₀)⁻¹ * (dbar ψc ζ * φ ζ) := by
    have := integral_add_left_eq_self (μ := (volume : Measure ℂ))
      (fun ζ : ℂ => (ζ - w₀)⁻¹ * (dbar ψc ζ * φ ζ)) w₀
    simpa using this
  rw [htrans] at hP
  have hneg : ∫ ζ : ℂ, dbar ψc ζ * φ ζ * (w₀ - ζ)⁻¹ =
      -∫ ζ : ℂ, (ζ - w₀)⁻¹ * (dbar ψc ζ * φ ζ) := by
    rw [← integral_neg]
    congr 1
    funext ζ
    rw [show w₀ - ζ = -(ζ - w₀) by ring, inv_neg]
    ring
  rw [hneg, hP]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [hΦtdef, add_zero, hΦdef, hψcdef, hw₀, ofReal_one, one_mul]
  field_simp

/-! ### Holomorphy of integrals with a holomorphic parameter -/

/-- The integral `z ↦ ∫ κ(ζ) a(z^{k←ζ}) dA(ζ)` of a holomorphic function against a continuous
compactly supported weight is holomorphic. -/
theorem differentiableOn_integral_rep {κ : ℂ → ℂ} (hκ : Continuous κ) (hκc : HasCompactSupport κ)
    (k : Fin n) {W W' : Set (EuclideanSpace ℂ (Fin n))} (hW : IsOpen W) (hW' : IsOpen W')
    {a : EuclideanSpace ℂ (Fin n) → ℂ} (ha : DifferentiableOn ℂ a W)
    (hrep : ∀ z ∈ W', ∀ ζ ∈ tsupport κ, rep z k ζ ∈ W) :
    DifferentiableOn ℂ (fun z => ∫ ζ : ℂ, κ ζ * a (rep z k ζ)) W' := by
  intro z₀ hz₀
  obtain ⟨r₀, hr₀, hr₀W'⟩ := Metric.isOpen_iff.1 hW' z₀ hz₀
  set r : ℝ := r₀ / 2 with hr
  have hr0 : 0 < r := by positivity
  have hcb : closedBall z₀ r ⊆ W' :=
    (closedBall_subset_ball (by linarith)).trans hr₀W'
  set K := (fun p : EuclideanSpace ℂ (Fin n) × ℂ => rep p.1 k p.2) '' (closedBall z₀ r ×ˢ tsupport κ)
  have hKc : IsCompact K :=
    ((isCompact_closedBall z₀ r).prod hκc).image (continuous_rep k)
  have hKW : K ⊆ W := by
    rintro _ ⟨p, hp, rfl⟩
    exact hrep p.1 (hcb hp.1) p.2 hp.2
  have hda : ContinuousOn (fderiv ℂ a) W :=
    (Hironaka.contDiffOn_of_differentiableOn_complex ha hW).continuousOn_fderiv_of_isOpen hW (by simp)
  obtain ⟨Bd, hBd⟩ := hKc.exists_bound_of_continuousOn (hda.mono hKW)
  set F : EuclideanSpace ℂ (Fin n) → ℂ → ℂ := fun z ζ => κ ζ * a (rep z k ζ)
  set F' : EuclideanSpace ℂ (Fin n) → ℂ → (EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ) :=
    fun z ζ => κ ζ • (fderiv ℂ a (rep z k ζ)).comp (repLin k)
  have hU : ∀ z ∈ W', IsOpen {ζ : ℂ | rep z k ζ ∈ W} := fun z _ =>
    hW.preimage (continuous_rep_right z k)
  have hFc : ∀ z ∈ W', Continuous (F z) := fun z hz =>
    continuous_mul_of_tsupport (hU z hz) hκ (fun ζ hζ => hrep z hz ζ hζ)
      (ha.continuousOn.comp (continuous_rep_right z k).continuousOn fun ζ hζ => hζ)
  have hcon : ContinuousOn (fun ζ => (fderiv ℂ a (rep z₀ k ζ)).comp (repLin k))
      {ζ | rep z₀ k ζ ∈ W} :=
    (hda.comp (continuous_rep_right z₀ k).continuousOn fun ζ hζ => hζ).clm_comp
      continuousOn_const
  have hF'c : Continuous (F' z₀) := by
    show Continuous fun ζ => κ ζ • (fderiv ℂ a (rep z₀ k ζ)).comp (repLin k)
    exact continuous_smul_of_tsupport (hU z₀ hz₀) hκ (fun ζ hζ => hrep z₀ hz₀ ζ hζ) hcon
  have hderiv := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := (volume : Measure ℂ))
    (F := F) (F' := F') (x₀ := z₀) (s := ball z₀ r)
    (bound := fun ζ => ‖κ ζ‖ * (Bd * ‖repLin k‖)) (ball_mem_nhds z₀ hr0)
    (eventually_of_mem (ball_mem_nhds z₀ hr0) fun z hz =>
      (hFc z (hcb (ball_subset_closedBall hz))).aestronglyMeasurable)
    ((hFc z₀ hz₀).integrable_of_hasCompactSupport hκc.mul_right)
    hF'c.aestronglyMeasurable
    (Eventually.of_forall fun ζ z hz => by
      by_cases hζ : ζ ∈ tsupport κ
      · have hK : rep z k ζ ∈ K := ⟨(z, ζ), ⟨ball_subset_closedBall hz, hζ⟩, rfl⟩
        simp only [F', norm_smul]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_right (hBd _ hK) (norm_nonneg _))
      · simp [F', image_eq_zero_of_notMem_tsupport hζ])
    ((hκ.norm.integrable_of_hasCompactSupport hκc.norm).mul_const _)
    (Eventually.of_forall fun ζ z hz => by
      by_cases hζ : ζ ∈ tsupport κ
      · have hzW : rep z k ζ ∈ W := hrep z (hcb (ball_subset_closedBall hz)) ζ hζ
        have hd := ((ha.differentiableAt (hW.mem_nhds hzW)).hasFDerivAt.comp z
          (hasFDerivAt_rep z k ζ)).const_mul (κ ζ)
        exact hd
      · have h0 : κ ζ = 0 := image_eq_zero_of_notMem_tsupport hζ
        simp only [F, F', h0, zero_mul]
        rw [zero_smul ℂ ((fderiv ℂ a (rep z k ζ)).comp (repLin k))]
        exact hasFDerivAt_const (0 : ℂ) z)
  exact hderiv.differentiableAt.differentiableWithinAt


/-! ### A product neighbourhood -/

/-- An open set containing a compact product set contains a closed product neighbourhood. -/
theorem exists_cthickening_pi_subset {C : Fin n → Set ℂ} (hC : ∀ l, IsCompact (C l))
    {W : Set (EuclideanSpace ℂ (Fin n))} (hW : IsOpen W) (hQW : {z | ∀ l, z l ∈ C l} ⊆ W) :
    ∃ e > 0, {z : EuclideanSpace ℂ (Fin n) | ∀ l, z l ∈ cthickening e (C l)} ⊆ W := by
  let V : ℕ → Set (EuclideanSpace ℂ (Fin n)) := fun m =>
    {z | ∀ l, z l ∈ cthickening (1 / ((m : ℝ) + 1)) (C l)}
  have hVc : ∀ m, IsCompact (V m) := fun m =>
    Cousin.isCompact_coord_pi fun l => (hC l).cthickening
  have hVd : Directed (· ⊇ ·) V := by
    refine directed_of_isDirected_le fun m m' hmm' => ?_
    have hle : 1 / ((m' : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmm' 1)
    exact fun z hz l => cthickening_mono hle _ (hz l)
  have hVW : ∀ x ∈ ⋂ m, V m, W ∈ 𝓝 x := by
    intro x hx
    rw [mem_iInter] at hx
    refine hW.mem_nhds (hQW fun l => ?_)
    rw [← (hC l).isClosed.closure_eq, closure_eq_iInter_cthickening]
    simp only [mem_iInter]
    intro δ hδ
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    exact cthickening_mono hm.le _ (hx m l)
  obtain ⟨m, hmW⟩ := exists_subset_nhds_of_isCompact hVd hVc hVW
  exact ⟨1 / ((m : ℝ) + 1), by positivity, hmW⟩

/-! ### One coordinate -/

open Hironaka.CauchyGreen in
/-- **Approximation in one coordinate.** Let `C_l ⊆ ℂ` be compact, `C_k` convex, and `a`
holomorphic near `Q = ∏ C_l`. Then `a` is uniformly approximated on `Q` by
`∑_i c_i(z) p_i(z_k)` with polynomials `p_i` and functions `c_i` holomorphic near `Q` that do
not depend on `z_k`, nor on any coordinate that `a` does not depend on. -/
theorem exists_slice_approx {C : Fin n → Set ℂ} (hC : ∀ l, IsCompact (C l)) (k : Fin n)
    (hconv : Convex ℝ (C k)) {W : Set (EuclideanSpace ℂ (Fin n))} (hW : IsOpen W)
    (hQW : {z | ∀ l, z l ∈ C l} ⊆ W) {a : EuclideanSpace ℂ (Fin n) → ℂ}
    (ha : DifferentiableOn ℂ a W) {ε : ℝ} (hε : 0 < ε) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → EuclideanSpace ℂ (Fin n) → ℂ)
      (p : ι → Polynomial ℂ) (W' : Set (EuclideanSpace ℂ (Fin n))),
      IsOpen W' ∧ {z | ∀ l, z l ∈ C l} ⊆ W' ∧ (∀ i, DifferentiableOn ℂ (c i) W') ∧
      (∀ i, IndepCoord (c i) k) ∧ (∀ l, IndepCoord a l → ∀ i, IndepCoord (c i) l) ∧
      ∀ z, (∀ l, z l ∈ C l) → ‖a z - ∑ i, c i z * (p i).eval (z k)‖ < ε := by
  classical
  obtain ⟨e₀, he₀, hPW⟩ := exists_cthickening_pi_subset hC hW hQW
  set e : ℝ := e₀ / 2 with hedef
  have he : 0 < e := by positivity
  obtain ⟨ψ, hψ, hψc, -, hψ1, hψs⟩ := Cousin.exists_cutoff_between (hC k) he.le
    (by linarith : e < 2 * e)
  set ψc : ℂ → ℂ := fun w => (ψ w : ℂ) with hψcdef
  have hψcc : ContDiff ℝ ∞ ψc := ofRealCLM.contDiff.comp hψ
  set g : ℂ → ℂ := dbar ψc with hgdef
  have hgcont : Continuous g := by
    have hD := hψcc.continuous_fderiv (by simp)
    exact ((hD.clm_apply continuous_const).add
      (continuous_const.mul (hD.clm_apply continuous_const))).div_const _
  have hgzero : ∀ x, x ∉ tsupport ψ → g x = 0 := by
    intro x hx
    have hev : ψc =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hx] with y hy
      simp [ψc, image_eq_zero_of_notMem_tsupport hy]
    rw [hgdef, dbar_eq_dbarDir, dbarDir_congr hev, dbarDir_const]
  have hgc : HasCompactSupport g := HasCompactSupport.intro hψc hgzero
  have hgsupp : tsupport g ⊆ tsupport ψ :=
    closure_minimal (fun x hx => by_contra fun h => hx (hgzero x h)) (isClosed_tsupport ψ)
  have hdisj : Disjoint (tsupport g) (C k) := by
    refine Set.disjoint_left.2 fun ζ hζ hζC => ?_
    have hev : g =ᶠ[𝓝 ζ] 0 := by
      have hth : thickening e (C k) ∈ 𝓝 ζ :=
        isOpen_thickening.mem_nhds (self_subset_thickening he _ hζC)
      filter_upwards [hth] with y hy
      have hev1 : ψc =ᶠ[𝓝 y] fun _ => 1 := by
        filter_upwards [isOpen_thickening.mem_nhds hy] with x hx
        simp [ψc, hψ1 x hx]
      show dbar ψc y = 0
      rw [dbar_eq_dbarDir, dbarDir_congr hev1, dbarDir_const]
    exact (notMem_tsupport_iff_eventuallyEq.2 hev) hζ
  -- the compact product neighbourhood and the bound for `a`
  set P2 := {z : EuclideanSpace ℂ (Fin n) | ∀ l, z l ∈ cthickening (2 * e) (C l)} with hP2
  have hP2c : IsCompact P2 := Cousin.isCompact_coord_pi fun l => (hC l).cthickening
  have hP2W : P2 ⊆ W := fun z hz => hPW fun l => by
    have := hz l
    rwa [show 2 * e = e₀ by rw [hedef]; ring] at this
  obtain ⟨M₀, hM₀⟩ := hP2c.exists_bound_of_continuousOn (ha.continuousOn.mono hP2W)
  set M : ℝ := max M₀ 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM : ∀ y ∈ P2, ‖a y‖ ≤ M := fun y hy => (hM₀ y hy).trans (le_max_left _ _)
  set Ig : ℝ := ∫ ζ : ℂ, ‖g ζ‖ with hIg
  have hIg0 : 0 ≤ Ig := integral_nonneg fun _ => norm_nonneg _
  set ε' : ℝ := ε / (2 * (π⁻¹ * Ig * M + 1)) with hε'def
  have hε' : 0 < ε' := by positivity
  obtain ⟨ι, _, χ, p, hχc, hχ01, hK⟩ := exists_kernel_approx (hC k) hconv hgc hdisj hε'
  set W' := {z : EuclideanSpace ℂ (Fin n) | ∀ l, z l ∈ thickening e (C l)} with hW'def
  have hW'o : IsOpen W' := by
    simp only [hW'def, ofPred_forall]
    exact isOpen_iInter_of_finite fun l => isOpen_thickening.preimage (Cousin.continuous_coord l)
  have hQW' : {z : EuclideanSpace ℂ (Fin n) | ∀ l, z l ∈ C l} ⊆ W' := fun z hz l =>
    self_subset_thickening he _ (hz l)
  have hrepP2 : ∀ z ∈ W', ∀ ζ ∈ tsupport ψ, rep z k ζ ∈ P2 := by
    intro z hz ζ hζ l
    rw [rep_apply]
    split_ifs with hl
    · subst hl; exact hψs hζ
    · exact thickening_subset_cthickening _ _ (thickening_mono (by linarith) _ (hz l))
  -- the coefficients
  set c : ι → EuclideanSpace ℂ (Fin n) → ℂ := fun i z =>
    (π : ℂ)⁻¹ * ∫ ζ : ℂ, ((χ i ζ : ℂ) * g ζ) * a (rep z k ζ) with hcdef
  have hκc : ∀ i, Continuous fun ζ => (χ i ζ : ℂ) * g ζ := fun i =>
    (continuous_ofReal.comp (hχc i)).mul hgcont
  have hκs : ∀ i, HasCompactSupport fun ζ => (χ i ζ : ℂ) * g ζ := fun i => hgc.mul_left
  have hκsupp : ∀ i, tsupport (fun ζ => (χ i ζ : ℂ) * g ζ) ⊆ tsupport ψ := fun i =>
    (tsupport_mul_subset_right).trans hgsupp
  refine ⟨ι, inferInstance, c, p, W', hW'o, hQW', fun i => ?_, fun i z w => ?_,
    fun l hl i z w => ?_, fun z hz => ?_⟩
  · exact (differentiableOn_integral_rep (hκc i) (hκs i) k hW hW'o ha
      fun z hz ζ hζ => hP2W (hrepP2 z hz ζ (hκsupp i hζ))).const_mul _
  · simp only [hcdef, rep_rep_same]
  · by_cases hlk : l = k
    · subst hlk
      simp only [hcdef, rep_rep_same]
    · simp only [hcdef]
      congr 2
      funext ζ
      rw [rep_comm z hlk w ζ, hl]
  -- the error estimate
  have hzW' : z ∈ W' := hQW' hz
  set V := {w : ℂ | rep z k w ∈ W} with hVdef
  have hVo : IsOpen V := hW.preimage (continuous_rep_right z k)
  have hψV : tsupport ψ ⊆ V := fun ζ hζ => hP2W (hrepP2 z hzW' ζ hζ)
  have hφ : DifferentiableOn ℂ (fun w => a (rep z k w)) V :=
    ha.comp (differentiable_rep_right z k).differentiableOn fun w hw => hw
  have hrepr := cauchy_pompeiu_cutoff hψ hψc hVo hψV hφ
    (hψ1 (z k) (self_subset_thickening he _ (hz k)))
  rw [rep_self] at hrepr
  set G : ℂ → ℂ := fun ζ => g ζ * a (rep z k ζ) with hGdef
  have hGc : Continuous G := continuous_mul_of_tsupport hVo hgcont (hgsupp.trans hψV) hφ.continuousOn
  have hGs : HasCompactSupport G := hgc.mul_right
  have hGsupp : tsupport G ⊆ tsupport g := tsupport_mul_subset_left
  have hzk : z k ∉ tsupport g := fun h => Set.disjoint_left.1 hdisj h (hz k)
  have hGK : Continuous fun ζ => G ζ * (z k - ζ)⁻¹ := by
    refine continuous_mul_of_tsupport (U := {ζ | ζ ≠ z k}) isOpen_ne hGc
      (fun ζ hζ h => hzk (h ▸ hGsupp hζ)) ?_
    exact (continuousOn_const.sub continuousOn_id).inv₀ fun ζ hζ => sub_ne_zero.2 (Ne.symm hζ)
  have hGKi : Integrable fun ζ => G ζ * (z k - ζ)⁻¹ :=
    hGK.integrable_of_hasCompactSupport hGs.mul_right
  have hterm : ∀ i, Integrable fun ζ => ((χ i ζ : ℂ) * g ζ) * a (rep z k ζ) * (p i).eval (z k) := by
    intro i
    refine Continuous.integrable_of_hasCompactSupport ?_ ((hκs i).mul_right.mul_right)
    exact (continuous_mul_of_tsupport hVo (hκc i) ((hκsupp i).trans hψV) hφ.continuousOn).mul
      continuous_const
  have hdiff : a z - ∑ i, c i z * (p i).eval (z k) =
      (π : ℂ)⁻¹ * ∫ ζ : ℂ, G ζ * ((z k - ζ)⁻¹ - ∑ i, (χ i ζ : ℂ) * (p i).eval (z k)) := by
    have h1 : a z = (π : ℂ)⁻¹ * ∫ ζ : ℂ, G ζ * (z k - ζ)⁻¹ := by
      rw [hrepr]
    have h2 : ∑ i, c i z * (p i).eval (z k) = (π : ℂ)⁻¹ *
        ∫ ζ : ℂ, ∑ i, ((χ i ζ : ℂ) * g ζ) * a (rep z k ζ) * (p i).eval (z k) := by
      rw [integral_finsetSum _ fun i _ => hterm i, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcdef, integral_mul_const]
      ring
    rw [h1, h2, ← mul_sub, ← integral_sub hGKi (integrable_finsetSum _ fun i _ => hterm i)]
    congr 2
    funext ζ
    rw [hGdef, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hdiff, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have hbound : ∀ ζ, ‖G ζ * ((z k - ζ)⁻¹ - ∑ i, (χ i ζ : ℂ) * (p i).eval (z k))‖ ≤
      ‖g ζ‖ * M * ε' := by
    intro ζ
    by_cases hζ : ζ ∈ tsupport g
    · rw [norm_mul, hGdef, norm_mul]
      have h1 : ‖a (rep z k ζ)‖ ≤ M := hM _ (hrepP2 z hzW' ζ (hgsupp hζ))
      have h2 := hK ζ hζ (z k) (hz k)
      exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) h2 (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) hM0)
    · have : g ζ = 0 := image_eq_zero_of_notMem_tsupport hζ
      simp [hGdef, this]
  have hgi : Integrable (fun ζ : ℂ => ‖g ζ‖) (volume : Measure ℂ) :=
    hgcont.norm.integrable_of_hasCompactSupport hgc.norm
  have hint := norm_integral_le_of_norm_le ((hgi.mul_const M).mul_const ε')
    (Eventually.of_forall hbound)
  have hcomp : ∫ ζ : ℂ, ‖g ζ‖ * M * ε' = Ig * M * ε' := by
    rw [integral_mul_const, integral_mul_const]
  rw [hcomp] at hint
  have hfin : π⁻¹ * (Ig * M * ε') < ε := by
    have hden : 0 < 2 * (π⁻¹ * Ig * M + 1) := by positivity
    have : π⁻¹ * (Ig * M * ε') = ε * (π⁻¹ * Ig * M) / (2 * (π⁻¹ * Ig * M + 1)) := by
      rw [hε'def]; field_simp
    rw [this, div_lt_iff₀ hden]
    nlinarith [mul_nonneg (inv_nonneg.2 Real.pi_pos.le) (mul_nonneg hIg0 hM0)]
  calc π⁻¹ * ‖∫ ζ : ℂ, G ζ * ((z k - ζ)⁻¹ - ∑ i, (χ i ζ : ℂ) * (p i).eval (z k))‖
      ≤ π⁻¹ * (Ig * M * ε') := mul_le_mul_of_nonneg_left hint (inv_nonneg.2 Real.pi_pos.le)
    _ < ε := hfin


/-! ### All coordinates -/

theorem eval_aeval_X_mul (k : Fin n) (p : Polynomial ℂ) (q : MvPolynomial (Fin n) ℂ)
    (x : Fin n → ℂ) :
    MvPolynomial.eval x (Polynomial.aeval (MvPolynomial.X k) p * q) =
      p.eval (x k) * MvPolynomial.eval x q := by
  rw [map_mul]
  congr 1
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, MvPolynomial.eval_X]
  have : (MvPolynomial.eval x).comp (algebraMap ℂ (MvPolynomial (Fin n) ℂ)) = RingHom.id ℂ := by
    ext a
    simp [MvPolynomial.algebraMap_eq]
  rw [this]
  rfl

/-- **Polynomial approximation on compact convex product sets** (Oka--Weil for
`Q = ∏ C_k`). Let `C_k ⊆ ℂ` be compact and convex, and let `f` be holomorphic on an open set
containing `Q = {z : z_k ∈ C_k ∀ k}`. For every `ε > 0` there is a polynomial `q` with
`|f - q| < ε` on `Q`. -/
theorem exists_mvPolynomial_approx {C : Fin n → Set ℂ} (hC : ∀ l, IsCompact (C l))
    (hconv : ∀ l, Convex ℝ (C l)) {W : Set (EuclideanSpace ℂ (Fin n))} (hW : IsOpen W)
    (hQW : {z | ∀ l, z l ∈ C l} ⊆ W) {f : EuclideanSpace ℂ (Fin n) → ℂ}
    (hf : DifferentiableOn ℂ f W) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : MvPolynomial (Fin n) ℂ, ∀ z : EuclideanSpace ℂ (Fin n), (∀ l, z l ∈ C l) →
      ‖f z - MvPolynomial.eval (fun l => z l) q‖ < ε := by
  classical
  set Q := {z : EuclideanSpace ℂ (Fin n) | ∀ l, z l ∈ C l} with hQ
  have hQc : IsCompact Q := Cousin.isCompact_coord_pi hC
  have hevc : ∀ q : MvPolynomial (Fin n) ℂ,
      Continuous fun z : EuclideanSpace ℂ (Fin n) => MvPolynomial.eval (fun l => z l) q := by
    intro q
    exact (MvPolynomial.continuous_eval (p := q)).comp
      (continuous_pi fun l => Cousin.continuous_coord l)
  have key : ∀ S : Finset (Fin n), ∀ ε > 0, ∃ (ι : Type) (_ : Fintype ι)
      (b : ι → EuclideanSpace ℂ (Fin n) → ℂ) (q : ι → MvPolynomial (Fin n) ℂ)
      (W' : Set (EuclideanSpace ℂ (Fin n))), IsOpen W' ∧ Q ⊆ W' ∧
      (∀ i, DifferentiableOn ℂ (b i) W') ∧ (∀ i, ∀ l ∈ S, IndepCoord (b i) l) ∧
      ∀ z ∈ Q, ‖f z - ∑ i, b i z * MvPolynomial.eval (fun l => z l) (q i)‖ < ε := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        intro ε hε
        refine ⟨Unit, inferInstance, fun _ => f, fun _ => 1, W, hW, hQW, fun _ => hf,
          fun _ l hl => absurd hl (Finset.notMem_empty l), fun z _ => ?_⟩
        simpa using hε
    | insert k S hk ih =>
        intro ε hε
        obtain ⟨ι, _, b, q, W', hW'o, hQW', hb, hbS, happ⟩ := ih (ε / 2) (half_pos hε)
        have hMq : ∀ i, ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ Q,
            ‖MvPolynomial.eval (fun l => z l) (q i)‖ ≤ M := by
          intro i
          obtain ⟨M, hM⟩ := hQc.exists_bound_of_continuousOn (hevc (q i)).continuousOn
          exact ⟨max M 0, le_max_right _ _, fun z hz => (hM z hz).trans (le_max_left _ _)⟩
        choose Mq hMq0 hMq using hMq
        set δ : ι → ℝ := fun i => ε / (2 * (Fintype.card ι + 1) * (Mq i + 1)) with hδ
        have hδ0 : ∀ i, 0 < δ i := fun i => by
          have := hMq0 i
          positivity
        have hslice := fun i => exists_slice_approx hC k (hconv k) hW'o hQW' (hb i) (hδ0 i)
        choose ι' inst c p W'' hW''o hQW'' hc hck hcl happ' using hslice
        refine ⟨Σ i, ι' i, inferInstance, fun x => c x.1 x.2,
          fun x => Polynomial.aeval (MvPolynomial.X k) (p x.1 x.2) * q x.1,
          W' ∩ ⋂ i, W'' i, hW'o.inter (isOpen_iInter_of_finite hW''o),
          fun z hz => ⟨hQW' hz, mem_iInter.2 fun i => hQW'' i hz⟩,
          fun x => (hc x.1 x.2).mono (inter_subset_right.trans (iInter_subset _ x.1)),
          fun x l hl => ?_, fun z hz => ?_⟩
        · rcases Finset.mem_insert.1 hl with rfl | hl
          · exact hck x.1 x.2
          · exact hcl x.1 l (hbS x.1 l hl) x.2
        · have hsum : ∑ x : Σ i, ι' i, c x.1 x.2 z * MvPolynomial.eval (fun l => z l)
              (Polynomial.aeval (MvPolynomial.X k) (p x.1 x.2) * q x.1) =
              ∑ i, (∑ j, c i j z * (p i j).eval (z k)) *
                MvPolynomial.eval (fun l => z l) (q i) := by
            rw [Fintype.sum_sigma]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [eval_aeval_X_mul]
            ring
          rw [hsum]
          have hsplit : f z - ∑ i, (∑ j, c i j z * (p i j).eval (z k)) *
              MvPolynomial.eval (fun l => z l) (q i) =
              (f z - ∑ i, b i z * MvPolynomial.eval (fun l => z l) (q i)) +
              ∑ i, (b i z - ∑ j, c i j z * (p i j).eval (z k)) *
                MvPolynomial.eval (fun l => z l) (q i) := by
            simp only [sub_mul, Finset.sum_sub_distrib]
            ring
          rw [hsplit]
          have h1 := happ z hz
          have h2 : ‖∑ i, (b i z - ∑ j, c i j z * (p i j).eval (z k)) *
              MvPolynomial.eval (fun l => z l) (q i)‖ ≤
              ∑ _i : ι, ε / (2 * (Fintype.card ι + 1)) := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
            rw [norm_mul]
            have ha := (happ' i z hz).le
            have hq := hMq i z hz
            have hMi := hMq0 i
            calc ‖b i z - ∑ j, c i j z * (p i j).eval (z k)‖ *
                ‖MvPolynomial.eval (fun l => z l) (q i)‖ ≤ δ i * Mq i :=
                  mul_le_mul ha hq (norm_nonneg _) (hδ0 i).le
              _ ≤ δ i * (Mq i + 1) := by nlinarith [hδ0 i]
              _ = ε / (2 * (Fintype.card ι + 1)) := by
                  rw [hδ]; field_simp
          have h3 : ∑ _i : ι, ε / (2 * (Fintype.card ι + 1)) < ε / 2 := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by positivity)]
            nlinarith
          calc ‖(f z - ∑ i, b i z * MvPolynomial.eval (fun l => z l) (q i)) +
                ∑ i, (b i z - ∑ j, c i j z * (p i j).eval (z k)) *
                  MvPolynomial.eval (fun l => z l) (q i)‖
              ≤ ‖f z - ∑ i, b i z * MvPolynomial.eval (fun l => z l) (q i)‖ +
                ‖∑ i, (b i z - ∑ j, c i j z * (p i j).eval (z k)) *
                  MvPolynomial.eval (fun l => z l) (q i)‖ := norm_add_le _ _
            _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le h1 (h2.trans h3.le)
            _ = ε := add_halves ε
  obtain ⟨ι, _, b, q, _, -, -, -, hbS, happ⟩ := key Finset.univ ε hε
  refine ⟨∑ i, MvPolynomial.C (b i 0) * q i, fun z hz => ?_⟩
  have hconst : ∀ i, b i z = b i 0 := fun i =>
    eq_zero_of_indepCoord (fun l => hbS i l (Finset.mem_univ l)) z
  have := happ z hz
  simpa [map_sum, hconst] using this

end

end Hironaka.Analytic.GAGA.Core.Runge
