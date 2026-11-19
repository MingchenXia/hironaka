import Hironaka.Analytic.OhsawaTakegoshiSubspace
import Hironaka.Analytic.BergmanSupWeight
import Hironaka.Analytic.PotentialTheory.LocalPshDiscControl
import Hironaka.Analytic.PshConvexCone
import Mathlib.Analysis.Normed.Affine.MazurUlam

set_option autoImplicit false

/-!
# Subadditivity of weighted Bergman kernels

`bergmanSup_add_le`: on a bounded open convex domain `B ⊆ ℂ^d`, for a plurisubharmonic `P` and
exponents `c₁, c₂ > 0`, the Bergman kernels on the diagonal satisfy

  `K_{(c₁+c₂)P}(y) ≤ C · K_{c₁P}(y) · K_{c₂P}(y)`,

with `C` depending only on `d` and the radius of a ball containing `B`.  For `c₁ = c₂ = m` this is
Demailly's `K_{2m} ≤ C K_m²`, the inequality that makes his Bergman approximations
`φ_{2^k} + C 2^{1-k}` decrease (Demailly, *Regularization of closed positive currents and
intersection theory*, J. Alg. Geom. 1 (1992), proof of Prop. 3.7; *Analytic methods in algebraic
geometry*, proof of Thm. 13.21).  Programme step A7 of `TN.3.3.DEMPROVE`.

## Proof

Let `f` be holomorphic on `B` with `∫_B |f|² e^{-(c₁+c₂)P} ≤ 1`.  On
`Ω = {(z, u) ∈ ℂ^{d+d} : z ∈ B, z + u ∈ B}` (open, convex, bounded) the weight
`Φ(z, u) = c₁ P(z) + c₂ P(z + u)` is plurisubharmonic and restricts to `(c₁+c₂)P` on the slice
`u = 0`, which is `B`.  The Ohsawa--Takegoshi theorem from a coordinate subspace
(`OhsawaTakegoshiSubspace.exists_extension_from_subspace`) extends `f` to `F` on `Ω` with
`∫_Ω |F|² e^{-Φ} ≤ C`.  In the coordinates `(a, b) = (z, z + u)` of `B × B` (a volume-preserving
change of variables) `G(a, b) = F(a, b - a)` satisfies `G(y, y) = f(y)` and
`∫∫_{B×B} |G(a,b)|² e^{-c₁P(a)} e^{-c₂P(b)} ≤ C`, and the extremal property of the kernel,
applied first in `b` (for almost every `a`) and then in `a`, gives
`|G(y, y)|² ≤ C K_{c₁P}(y) K_{c₂P}(y)` (`normSq_le_mul_bergmanSup_mul`).
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace Hironaka.BergmanSubadditivity

noncomputable section

open BergmanSupWeight OhsawaTakegoshiSubspace

/-! ### `ℂ^{d+d}` as `ℂ^d × ℂ^d` -/

section Coordinates

variable (d : ℕ)

/-- The linear isometry `WithLp 2 (ℂ^d × ℂ^d) ≃ ℂ^{d+d}`. -/
def joinEquiv : WithLp 2 (ComplexModel d × ComplexModel d) ≃ₗᵢ[ℂ] ComplexModel (d + d) :=
  (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin d ⊕ Fin d => ℂ)).symm.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ finSumFinEquiv)

/-- `(a, b) ↦ (a, b)` as a continuous linear equivalence `ℂ^d × ℂ^d ≃ ℂ^{d+d}`. -/
def joinCLE : (ComplexModel d × ComplexModel d) ≃L[ℂ] ComplexModel (d + d) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ (ComplexModel d) (ComplexModel d)).symm.trans
    (joinEquiv d).toContinuousLinearEquiv

variable {d}

/-- The point `(a, b) ∈ ℂ^{d+d}`. -/
def join (a b : ComplexModel d) : ComplexModel (d + d) := joinCLE d (a, b)

theorem join_eq (a b : ComplexModel d) : join a b = joinEquiv d (WithLp.toLp 2 (a, b)) := rfl

@[simp] theorem join_castAdd (a b : ComplexModel d) (i : Fin d) :
    join a b (Fin.castAdd d i) = a i := by
  have h : finSumFinEquiv.symm (Fin.castAdd d i) = Sum.inl i :=
    finSumFinEquiv_symm_apply_castAdd i
  rw [join_eq]
  simp only [joinEquiv, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft'_apply, h]
  rfl

@[simp] theorem join_natAdd (a b : ComplexModel d) (i : Fin d) :
    join a b (Fin.natAdd d i) = b i := by
  have h : finSumFinEquiv.symm (Fin.natAdd d i) = Sum.inr i :=
    finSumFinEquiv_symm_apply_natAdd i
  rw [join_eq]
  simp only [joinEquiv, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft'_apply, h]
  rfl

/-- `‖(a, b)‖ ≤ ‖a‖ + ‖b‖`. -/
theorem norm_join_le (a b : ComplexModel d) : ‖join a b‖ ≤ ‖a‖ + ‖b‖ := by
  rw [join_eq, LinearIsometryEquiv.norm_map, WithLp.prod_norm_eq_of_L2]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd]
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [norm_nonneg a, norm_nonneg b]

variable (d) in
/-- The first `d` coordinates. -/
def fstCLM : ComplexModel (d + d) →L[ℂ] ComplexModel d :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 fun i => z (Fin.castAdd d i)
      map_add' := fun z z' => by ext i; simp
      map_smul' := fun c z => by ext i; simp }

variable (d) in
/-- The last `d` coordinates. -/
def sndCLM : ComplexModel (d + d) →L[ℂ] ComplexModel d :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 fun i => z (Fin.natAdd d i)
      map_add' := fun z z' => by ext i; simp
      map_smul' := fun c z => by ext i; simp }

@[simp] theorem fstCLM_apply (z : ComplexModel (d + d)) (i : Fin d) :
    fstCLM d z i = z (Fin.castAdd d i) := rfl

@[simp] theorem sndCLM_apply (z : ComplexModel (d + d)) (i : Fin d) :
    sndCLM d z i = z (Fin.natAdd d i) := rfl

@[simp] theorem fstCLM_join (a b : ComplexModel d) : fstCLM d (join a b) = a := by
  ext i; simp

@[simp] theorem sndCLM_join (a b : ComplexModel d) : sndCLM d (join a b) = b := by
  ext i; simp

theorem join_fst_snd (z : ComplexModel (d + d)) : join (fstCLM d z) (sndCLM d z) = z := by
  ext k
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · rw [join_castAdd, fstCLM_apply]
  · rw [join_natAdd, sndCLM_apply]

/-- The slice embedding of `OhsawaTakegoshiSubspace` is `w ↦ (w, 0)`. -/
theorem subspaceCLM_eq_join (w : ComplexModel d) : subspaceCLM d d w = join w 0 := by
  ext k
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · rw [join_castAdd, subspaceCLM_apply_castAdd]
  · rw [join_natAdd, subspaceCLM_apply_natAdd]
    rfl

/-- The shear `(a, b) ↦ (a, -a + b)`. -/
def shear : (ComplexModel d × ComplexModel d) ≃ₜ (ComplexModel d × ComplexModel d) where
  toFun p := (p.1, -p.1 + p.2)
  invFun p := (p.1, p.1 + p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

variable (d) in
/-- The change of variables `(a, b) ↦ (a, b - a) ∈ ℂ^{d+d}`. -/
def chartT : (ComplexModel d × ComplexModel d) ≃ₜ ComplexModel (d + d) :=
  shear.trans (joinCLE d).toHomeomorph

theorem chartT_apply (p : ComplexModel d × ComplexModel d) :
    chartT d p = join p.1 (-p.1 + p.2) := rfl

end Coordinates

/-! ### Weighted Bergman kernels: three small facts -/

section Bergman

variable {d : ℕ} [MeasurableSpace (ComplexModel d)] [BorelSpace (ComplexModel d)]

/-- The Bergman objects only see the weight on the domain. -/
theorem bergmanSup_congr_weight {D : Set (ComplexModel d)} (hD : MeasurableSet D)
    {w w' : ComplexModel d → ℝ≥0∞} (h : ∀ z ∈ D, w z = w' z) (y : ComplexModel d) :
    bergmanSup D w y = bergmanSup D w' y := by
  have hball : bergmanBall D w = bergmanBall D w' := by
    ext f
    change (DifferentiableOn ℂ f D ∧ ∫⁻ z in D, ENNReal.ofReal (‖f z‖ ^ 2) * w z ≤ 1) ↔
      (DifferentiableOn ℂ f D ∧ ∫⁻ z in D, ENNReal.ofReal (‖f z‖ ^ 2) * w' z ≤ 1)
    rw [setLIntegral_congr_fun hD fun z hz => by rw [h z hz]]
  simp only [bergmanSup, hball]

/-- Shrinking the domain increases the kernel. -/
theorem bergmanSup_le_of_subset {D D' : Set (ComplexModel d)} (hDD' : D' ⊆ D)
    (w : ComplexModel d → ℝ≥0∞) (y : ComplexModel d) :
    bergmanSup D w y ≤ bergmanSup D' w y :=
  bergmanSup_le fun _ hf => le_bergmanSup ⟨hf.1.mono hDD', (lintegral_mono_set hDD').trans hf.2⟩ y

/-- **The extremal property with a finite but possibly zero norm.** -/
theorem normSq_le_mul_bergmanSup {D : Set (ComplexModel d)} {w : ComplexModel d → ℝ≥0∞}
    {g : ComplexModel d → ℂ} (hg : DifferentiableOn ℂ g D) {A : ℝ≥0∞} (hA : A ≠ ⊤)
    (hint : ∫⁻ z in D, ENNReal.ofReal (‖g z‖ ^ 2) * w z ≤ A) {y : ComplexModel d}
    (hK : bergmanSup D w y ≠ ⊤) :
    ENNReal.ofReal (‖g y‖ ^ 2) ≤ A * bergmanSup D w y := by
  by_cases hA0 : A = 0
  · subst hA0
    rw [zero_mul]
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    rw [zero_add]
    by_cases hK0 : bergmanSup D w y = 0
    · have := bergmanSup_extremal hg one_ne_zero ENNReal.one_ne_top (hint.trans (by positivity)) y
      rw [hK0, mul_zero] at this
      exact this.trans (by positivity)
    · have hε0 : (ε : ℝ≥0∞) ≠ 0 := by exact_mod_cast hε.ne'
      have hA'0 : (ε : ℝ≥0∞) / bergmanSup D w y ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hε0, hK⟩
      have hA'top : (ε : ℝ≥0∞) / bergmanSup D w y ≠ ⊤ :=
        ENNReal.div_ne_top ENNReal.coe_ne_top hK0
      have := bergmanSup_extremal hg hA'0 hA'top (hint.trans (by positivity)) y
      rwa [ENNReal.div_mul_cancel hK0 hK] at this
  · exact bergmanSup_extremal hg hA0 hA hint y

/-- **The kernel of a psh weight is finite at interior points.**  The weight is bounded below
on a small closed ball around `y`, where `P` is bounded above, and shrinking the domain to that
ball only increases the kernel. -/
theorem bergmanSup_multiplierWeight_ne_top {B : Set (ComplexModel d)} (hB : IsOpen B)
    {P : ComplexModel d → EReal} (hP : PlurisubharmonicOn P B) {c : ℝ} (hc : 0 < c)
    {y : ComplexModel d} (hy : y ∈ B) :
    bergmanSup B (fun z => multiplierWeight c (P z)) y ≠ ⊤ := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hB y hy
  have hsub : closedBall y (r / 2) ⊆ B := (closedBall_subset_ball (by linarith)).trans hball
  obtain ⟨M, -, hM⟩ :=
    hP.exists_nonnegative_compact_upper_bound (isCompact_closedBall y (r / 2)) hsub
  refine ne_top_of_le_ne_top ?_ (bergmanSup_le_of_subset (ball_subset_closedBall.trans hsub) _ y)
  refine bergmanSup_ne_top_of_isOpen isOpen_ball (Real.exp_pos (-(c * M))) (fun z hz => ?_)
    (mem_ball_self (by linarith))
  rw [← multiplierWeight_coe]
  exact multiplierWeight_antitone hc.le (hM z (ball_subset_closedBall hz))

/-- **The product extremal bound.**  If `G` is holomorphic in each variable on `B × B`,
continuous there, and `∫∫_{B×B} |G(a,b)|² w₁(a) w₂(b) ≤ A < ⊤`, then
`|G(y, y)|² ≤ A K_{w₁}(y) K_{w₂}(y)` at every `y ∈ B` where both kernels are finite. -/
theorem normSq_le_mul_bergmanSup_mul {B : Set (ComplexModel d)} (hB : IsOpen B)
    {w₁ w₂ : ComplexModel d → ℝ≥0∞} (hw₁ : Measurable w₁) (hw₂ : Measurable w₂)
    (hw₁0 : ∀ z ∈ B, w₁ z ≠ 0)
    {G : ComplexModel d × ComplexModel d → ℂ}
    (hG₁ : ∀ b ∈ B, DifferentiableOn ℂ (fun a => G (a, b)) B)
    (hG₂ : ∀ a ∈ B, DifferentiableOn ℂ (fun b => G (a, b)) B)
    (hGc : ContinuousOn G (B ×ˢ B)) {A : ℝ≥0∞} (hA : A ≠ ⊤)
    (hint : ∫⁻ p in B ×ˢ B, ENNReal.ofReal (‖G p‖ ^ 2) * (w₁ p.1 * w₂ p.2)
      ∂(volume.prod volume) ≤ A)
    {y : ComplexModel d} (hy : y ∈ B)
    (hK₁ : bergmanSup B w₁ y ≠ ⊤) (hK₂ : bergmanSup B w₂ y ≠ ⊤) :
    ENNReal.ofReal (‖G (y, y)‖ ^ 2) ≤ A * bergmanSup B w₁ y * bergmanSup B w₂ y := by
  classical
  have hBm : MeasurableSet B := hB.measurableSet
  set K₁ := bergmanSup B w₁ y with hK₁def
  set K₂ := bergmanSup B w₂ y with hK₂def
  -- a measurable version of `G`
  set G' : ComplexModel d × ComplexModel d → ℂ := (B ×ˢ B).piecewise G 0 with hG'def
  have hG'm : Measurable G' :=
    hGc.measurable_piecewise continuousOn_const (hBm.prod hBm)
  have hG'eq : ∀ a ∈ B, ∀ b ∈ B, G' (a, b) = G (a, b) := fun a ha b hb =>
    Set.piecewise_eq_of_mem _ _ _ ⟨ha, hb⟩
  set f : ComplexModel d × ComplexModel d → ℝ≥0∞ :=
    fun p => ENNReal.ofReal (‖G' p‖ ^ 2) * (w₁ p.1 * w₂ p.2) with hfdef
  have hfm : Measurable f :=
    (ENNReal.measurable_ofReal.comp (hG'm.norm.pow_const 2)).mul
      ((hw₁.comp measurable_fst).mul (hw₂.comp measurable_snd))
  -- the inner integral in the second variable
  set I₂ : ComplexModel d → ℝ≥0∞ :=
    fun a => ∫⁻ b in B, ENNReal.ofReal (‖G' (a, b)‖ ^ 2) * w₂ b with hI₂def
  have hI₂m : Measurable I₂ := by
    have : Measurable fun p : ComplexModel d × ComplexModel d =>
        ENNReal.ofReal (‖G' p‖ ^ 2) * w₂ p.2 :=
      (ENNReal.measurable_ofReal.comp (hG'm.norm.pow_const 2)).mul (hw₂.comp measurable_snd)
    exact this.lintegral_prod_right'
  -- Tonelli
  have hiter : ∫⁻ a in B, I₂ a * w₁ a ≤ A := by
    have h1 : ∫⁻ a in B, I₂ a * w₁ a = ∫⁻ a in B, ∫⁻ b in B, f (a, b) := by
      refine lintegral_congr fun a => ?_
      have hmeas : Measurable fun b => ENNReal.ofReal (‖G' (a, b)‖ ^ 2) * w₂ b :=
        (ENNReal.measurable_ofReal.comp
          ((hG'm.comp measurable_prodMk_left).norm.pow_const 2)).mul hw₂
      simp only [hI₂def, hfdef]
      rw [← lintegral_mul_const (w₁ a) hmeas]
      refine lintegral_congr fun b => ?_
      ring
    have h2 : ∫⁻ a in B, ∫⁻ b in B, f (a, b)
        = ∫⁻ p, f p ∂((volume.restrict B).prod (volume.restrict B)) :=
      (lintegral_prod f hfm.aemeasurable).symm
    rw [h1, h2, Measure.prod_restrict]
    refine le_trans (le_of_eq ?_) hint
    refine setLIntegral_congr_fun (hBm.prod hBm) fun p hp => ?_
    simp only [hfdef, hG'def, Set.piecewise_eq_of_mem _ _ _ hp]
  -- `I₂ < ⊤` almost everywhere on `B`
  have hae : ∀ᵐ a ∂(volume.restrict B), I₂ a < ⊤ := by
    have h := ae_lt_top' (hI₂m.mul hw₁).aemeasurable (ne_top_of_le_ne_top hA hiter)
    filter_upwards [h, ae_restrict_mem hBm] with a ha haB
    change I₂ a * w₁ a < ⊤ at ha
    by_contra htop
    rw [not_lt, top_le_iff] at htop
    rw [htop, ENNReal.top_mul (hw₁0 a haB)] at ha
    exact lt_irrefl _ ha
  -- step 1: extremal in the second variable
  have hstep1 : ∀ᵐ a ∂(volume.restrict B),
      ENNReal.ofReal (‖G (a, y)‖ ^ 2) * w₁ a ≤ K₂ * (I₂ a * w₁ a) := by
    filter_upwards [hae, ae_restrict_mem hBm] with a ha haB
    have hint₂ : ∫⁻ b in B, ENNReal.ofReal (‖G (a, b)‖ ^ 2) * w₂ b ≤ I₂ a :=
      le_of_eq (setLIntegral_congr_fun hBm fun b hb => by rw [hG'eq a haB b hb])
    have := normSq_le_mul_bergmanSup (hG₂ a haB) ha.ne hint₂ hK₂
    calc ENNReal.ofReal (‖G (a, y)‖ ^ 2) * w₁ a ≤ I₂ a * K₂ * w₁ a := by gcongr
      _ = K₂ * (I₂ a * w₁ a) := by ring
  -- step 2: integrate in the first variable
  have hI₁ : ∫⁻ a in B, ENNReal.ofReal (‖G (a, y)‖ ^ 2) * w₁ a ≤ K₂ * A := by
    calc ∫⁻ a in B, ENNReal.ofReal (‖G (a, y)‖ ^ 2) * w₁ a
        ≤ ∫⁻ a in B, K₂ * (I₂ a * w₁ a) := lintegral_mono_ae hstep1
      _ = K₂ * ∫⁻ a in B, I₂ a * w₁ a := lintegral_const_mul' _ _ hK₂
      _ ≤ K₂ * A := by gcongr
  -- step 3: extremal in the first variable
  have := normSq_le_mul_bergmanSup (hG₁ y hy) (ENNReal.mul_ne_top hK₂ hA) hI₁ hK₁
  calc ENNReal.ofReal (‖G (y, y)‖ ^ 2) ≤ K₂ * A * K₁ := this
    _ = A * K₁ * K₂ := by ring

end Bergman

/-! ### The weights -/

section Weights

/-- `e^{-(c₁x + c₂y)} = e^{-c₁x} e^{-c₂y}` for extended reals below `+∞`. -/
theorem multiplierWeight_one_add {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) {x y : EReal}
    (hx : x ≠ ⊤) (hy : y ≠ ⊤) :
    multiplierWeight 1 ((c₁ : EReal) * x + (c₂ : EReal) * y) =
      multiplierWeight c₁ x * multiplierWeight c₂ y := by
  induction x using EReal.rec with
  | top => exact absurd rfl hx
  | bot =>
    rw [EReal.coe_mul_bot_of_pos hc₁, EReal.bot_add, multiplierWeight_bot one_pos,
      multiplierWeight_bot hc₁, ENNReal.top_mul]
    induction y using EReal.rec with
    | top => exact absurd rfl hy
    | bot => rw [multiplierWeight_bot hc₂]; exact ENNReal.top_ne_zero
    | coe y => rw [multiplierWeight_coe]; exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  | coe x =>
    induction y using EReal.rec with
    | top => exact absurd rfl hy
    | bot =>
      rw [EReal.coe_mul_bot_of_pos hc₂, EReal.add_bot, multiplierWeight_bot one_pos,
        multiplierWeight_bot hc₂, ENNReal.mul_top]
      rw [multiplierWeight_coe]; exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    | coe y =>
      rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, multiplierWeight_coe,
        multiplierWeight_coe, multiplierWeight_coe, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← Real.exp_add]
      congr 2
      ring

/-- `e^{-c₁x} e^{-c₂x} = e^{-(c₁+c₂)x}` for an extended real below `+∞`. -/
theorem multiplierWeight_mul_same {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) {x : EReal}
    (hx : x ≠ ⊤) :
    multiplierWeight c₁ x * multiplierWeight c₂ x = multiplierWeight (c₁ + c₂) x := by
  induction x using EReal.rec with
  | top => exact absurd rfl hx
  | bot =>
    rw [multiplierWeight_bot hc₁, multiplierWeight_bot hc₂,
      multiplierWeight_bot (add_pos hc₁ hc₂), ENNReal.top_mul_top]
  | coe x =>
    rw [multiplierWeight_coe, multiplierWeight_coe, multiplierWeight_coe,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring

/-- `e^{-cx} ≠ 0` below `+∞`. -/
theorem multiplierWeight_ne_zero {c : ℝ} (hc : 0 < c) {x : EReal} (hx : x ≠ ⊤) :
    multiplierWeight c x ≠ 0 := by
  induction x using EReal.rec with
  | top => exact absurd rfl hx
  | bot => rw [multiplierWeight_bot hc]; exact ENNReal.top_ne_zero
  | coe x => rw [multiplierWeight_coe]; exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'

open Classical in
/-- An upper semicontinuous function on an open set, extended by `+∞`, is measurable. -/
theorem measurable_extendTop {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {f : X → EReal} {U : Set X} (hf : UpperSemicontinuousOn f U)
    (hU : IsOpen U) : Measurable fun x => if x ∈ U then f x else ⊤ := by
  apply UpperSemicontinuous.measurable
  intro x c hxc
  by_cases hx : x ∈ U
  · have hfc : f x < c := by simpa [hx] using hxc
    have hlocal := hf x hx c hfc
    rw [hU.nhdsWithin_eq hx] at hlocal
    filter_upwards [hlocal, hU.mem_nhds hx] with y hy hyU
    simpa [hyU] using hy
  · simp [hx] at hxc

end Weights

/-! ### Subadditivity -/

open Classical in
/-- **Subadditivity of weighted Bergman kernels** (Demailly).  On a bounded open convex domain
`B ⊆ ℂ^d` inside the ball of radius `R`, for `P` plurisubharmonic on `B` and `c₁, c₂ > 0`,

  `K_{(c₁+c₂)P}(y) ≤ C K_{c₁P}(y) K_{c₂P}(y)`  for every `y ∈ B`,

with `C` depending only on `d` and `R`.  Stated, like
`BergmanSupWeight.exists_one_le_mul_bergmanSup`, for the Borel structure `borel (ℂ^d)`; see
`bergmanSup_add_le'` for any Borel structure. -/
theorem bergmanSup_add_le (d : ℕ) : by
    letI : MeasurableSpace (ComplexModel d) := borel _
    letI : BorelSpace (ComplexModel d) := ⟨rfl⟩
    exact ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
      ∀ B : Set (ComplexModel d), IsOpen B → Convex ℝ B → (∀ z ∈ B, ‖z‖ < R) →
      ∀ P : ComplexModel d → EReal, PlurisubharmonicOn P B →
      ∀ c₁ c₂ : ℝ, 0 < c₁ → 0 < c₂ → ∀ y ∈ B,
        bergmanSup B (fun z => multiplierWeight (c₁ + c₂) (P z)) y ≤
          ENNReal.ofReal C * bergmanSup B (fun z => multiplierWeight c₁ (P z)) y *
            bergmanSup B (fun z => multiplierWeight c₂ (P z)) y := by
  let _ : MeasurableSpace (ComplexModel d) := borel _
  have _ : BorelSpace (ComplexModel d) := ⟨rfl⟩
  let _ : MeasurableSpace (ComplexModel (d + d)) := borel _
  have _ : BorelSpace (ComplexModel (d + d)) := ⟨rfl⟩
  intro R hR
  obtain ⟨C, hC, hOT⟩ := exists_extension_from_subspace d d (3 * R) (by linarith)
  refine ⟨C, hC, fun B hB hconv hbd P hP c₁ c₂ hc₁ hc₂ y hy => ?_⟩
  have hBm : MeasurableSet B := hB.measurableSet
  have hPtop : ∀ z ∈ B, P z ≠ ⊤ := fun z hz => (hP z hz).ne_top
  -- the domain `Ω = {(z, u) : z ∈ B, z + u ∈ B}`
  set L : ComplexModel (d + d) →L[ℂ] ComplexModel d := fstCLM d + sndCLM d with hLdef
  have hL : ∀ a b : ComplexModel d, L (join a b) = a + b := fun a b => by
    simp only [hLdef, FunLike.coe_add, Pi.add_apply, fstCLM_join, sndCLM_join]
  set Ω : Set (ComplexModel (d + d)) := fstCLM d ⁻¹' B ∩ L ⁻¹' B with hΩdef
  have hΩo : IsOpen Ω := (hB.preimage (fstCLM d).continuous).inter (hB.preimage L.continuous)
  have hΩc : Convex ℝ Ω :=
    (hconv.linear_preimage ((fstCLM d).toLinearMap.restrictScalars ℝ)).inter
      (hconv.linear_preimage (L.toLinearMap.restrictScalars ℝ))
  have hΩb : ∀ z ∈ Ω, ‖z‖ < 3 * R := by
    intro z hz
    have h1 : ‖fstCLM d z‖ < R := hbd _ hz.1
    have h2 : ‖L z‖ < R := hbd _ hz.2
    have h3 : sndCLM d z = L z - fstCLM d z := by
      simp only [hLdef, FunLike.coe_add, Pi.add_apply, add_sub_cancel_left]
    have h4 : ‖sndCLM d z‖ < 2 * R := by
      rw [h3]
      calc ‖L z - fstCLM d z‖ ≤ ‖L z‖ + ‖fstCLM d z‖ := norm_sub_le _ _
        _ < 2 * R := by linarith
    rw [← join_fst_snd z]
    calc ‖join (fstCLM d z) (sndCLM d z)‖ ≤ ‖fstCLM d z‖ + ‖sndCLM d z‖ := norm_join_le _ _
      _ < 3 * R := by linarith
  -- the weight `Φ(z, u) = c₁ P(z) + c₂ P(z + u)`
  set φ : ComplexModel (d + d) → EReal :=
    fun z => (c₁ : EReal) * P (fstCLM d z) + (c₂ : EReal) * P (L z) with hφdef
  have hφ : PlurisubharmonicOn φ Ω :=
    PlurisubharmonicOn.add
      (PlurisubharmonicOn.mono
        (PlurisubharmonicOn.const_mul (hP.comp_continuousLinearMap (fstCLM d)) hc₁)
        inter_subset_left)
      (PlurisubharmonicOn.mono
        (PlurisubharmonicOn.const_mul (hP.comp_continuousLinearMap L) hc₂) inter_subset_right)
  -- the slice is `B`
  have hslice : subspaceCLM d d ⁻¹' Ω = B := by
    ext w
    simp only [hΩdef, mem_preimage, mem_inter_iff, subspaceCLM_eq_join, fstCLM_join, hL,
      add_zero, and_self]
  -- measurable versions of the weights
  set P' : ComplexModel d → EReal := fun z => if z ∈ B then P z else ⊤ with hP'def
  have hP'm : Measurable P' := measurable_extendTop hP.upperSemicontinuousOn hB
  have hP'eq : ∀ z ∈ B, P' z = P z := fun z hz => by simp only [hP'def, if_pos hz]
  have hw'm : ∀ c : ℝ, 0 < c → Measurable fun z => multiplierWeight c (P' z) := fun c hc =>
    (multiplierWeight_antitone hc.le).measurable.comp hP'm
  have hKeq : ∀ c : ℝ, bergmanSup B (fun z => multiplierWeight c (P' z)) y =
      bergmanSup B (fun z => multiplierWeight c (P z)) y := fun c =>
    bergmanSup_congr_weight hBm (fun z hz => by rw [hP'eq z hz]) y
  -- the estimate for one competitor
  refine bergmanSup_le fun f hf => ?_
  have hfB : DifferentiableOn ℂ f (subspaceCLM d d ⁻¹' Ω) := by rw [hslice]; exact hf.1
  obtain ⟨F, hFhol, hFext, hFint⟩ := hOT Ω hΩo hΩc hΩb φ hφ 1 one_pos f hfB
  have hsliceint : ∫⁻ w in subspaceCLM d d ⁻¹' Ω,
      multiplierDensity (fun w => φ (subspaceCLM d d w)) 1 f w ≤ 1 := by
    rw [hslice]
    refine le_trans (le_of_eq ?_) hf.2
    refine setLIntegral_congr_fun hBm fun w hw => ?_
    simp only [multiplierDensity, hφdef, subspaceCLM_eq_join, fstCLM_join, hL, add_zero]
    rw [multiplierWeight_one_add hc₁ hc₂ (hPtop w hw) (hPtop w hw),
      multiplierWeight_mul_same hc₁ hc₂ (hPtop w hw)]
  have hFint' : ∫⁻ z in Ω, multiplierDensity φ 1 F z ≤ ENNReal.ofReal C :=
    hFint.trans (by
      calc ENNReal.ofReal C * ∫⁻ w in subspaceCLM d d ⁻¹' Ω,
            multiplierDensity (fun w => φ (subspaceCLM d d w)) 1 f w
          ≤ ENNReal.ofReal C * 1 := by gcongr
        _ = ENNReal.ofReal C := mul_one _)
  -- `G(a, b) = F(a, b - a)` on `B × B`
  set G : ComplexModel d × ComplexModel d → ℂ := fun p => F (chartT d p) with hGdef
  have hmaps : ∀ a ∈ B, ∀ b ∈ B, chartT d (a, b) ∈ Ω := fun a ha b hb => by
    refine ⟨?_, ?_⟩
    · simp only [mem_preimage, chartT_apply, fstCLM_join]; exact ha
    · simp only [mem_preimage, chartT_apply, hL, add_neg_cancel_left]; exact hb
  have hG₁ : ∀ b ∈ B, DifferentiableOn ℂ (fun a => G (a, b)) B := fun b hb => by
    have hdiff : Differentiable ℂ fun a : ComplexModel d => chartT d (a, b) := by
      simp only [chartT_apply]
      exact (joinCLE d).differentiable.comp (differentiable_id.prodMk
        (differentiable_id.neg.add_const b))
    exact hFhol.comp hdiff.differentiableOn fun a ha => hmaps a ha b hb
  have hG₂ : ∀ a ∈ B, DifferentiableOn ℂ (fun b => G (a, b)) B := fun a ha => by
    have hdiff : Differentiable ℂ fun b : ComplexModel d => chartT d (a, b) := by
      simp only [chartT_apply]
      exact (joinCLE d).differentiable.comp ((differentiable_const a).prodMk
        ((differentiable_const (-a)).add differentiable_id))
    exact hFhol.comp hdiff.differentiableOn fun b hb => hmaps a ha b hb
  have hGc : ContinuousOn G (B ×ˢ B) :=
    hFhol.continuousOn.comp (chartT d).continuous.continuousOn fun p hp => hmaps p.1 hp.1 p.2 hp.2
  -- the change of variables
  have hpre : chartT d ⁻¹' Ω = B ×ˢ B := by
    ext ⟨a, b⟩
    simp only [hΩdef, mem_preimage, mem_inter_iff, chartT_apply, fstCLM_join, hL,
      add_neg_cancel_left, mem_prod]
  have hmp : MeasurePreserving (chartT d) (volume.prod volume) volume := by
    have hshear : MeasurePreserving (shear (d := d)) (volume.prod volume) (volume.prod volume) :=
      measurePreserving_prod_neg_add volume volume
    have hiso := (IsometryEquiv.toRealLinearIsometryEquivOfMapZero (joinEquiv d).toIsometryEquiv
      (by rw [LinearIsometryEquiv.coe_toIsometryEquiv]; exact map_zero _)).measurePreserving
    rw [IsometryEquiv.coe_toRealLinearIsometryEquivOfMapZero] at hiso
    have hjoin : MeasurePreserving (joinCLE d) (volume.prod volume) volume := by
      have := hiso.comp (WithLp.volume_preserving_toLp (ComplexModel d) (ComplexModel d))
      rw [← Measure.volume_eq_prod]
      exact this
    exact hjoin.comp hshear
  have hint : ∫⁻ p in B ×ˢ B, ENNReal.ofReal (‖G p‖ ^ 2) *
      (multiplierWeight c₁ (P' p.1) * multiplierWeight c₂ (P' p.2)) ∂(volume.prod volume) ≤
        ENNReal.ofReal C := by
    calc ∫⁻ p in B ×ˢ B, ENNReal.ofReal (‖G p‖ ^ 2) *
          (multiplierWeight c₁ (P' p.1) * multiplierWeight c₂ (P' p.2)) ∂(volume.prod volume)
        = ∫⁻ p in chartT d ⁻¹' Ω, multiplierDensity φ 1 F (chartT d p) ∂(volume.prod volume) := by
          rw [hpre]
          refine setLIntegral_congr_fun (hBm.prod hBm) fun p hp => ?_
          simp only [multiplierDensity, hGdef, hφdef, chartT_apply, fstCLM_join, hL,
            add_neg_cancel_left, hP'eq p.1 hp.1, hP'eq p.2 hp.2]
          rw [multiplierWeight_one_add hc₁ hc₂ (hPtop _ hp.1) (hPtop _ hp.2)]
      _ = ∫⁻ z in Ω, multiplierDensity φ 1 F z :=
          hmp.setLIntegral_comp_preimage_emb (chartT d).measurableEmbedding _ _
      _ ≤ ENNReal.ofReal C := hFint'
  have hK₁ : bergmanSup B (fun z => multiplierWeight c₁ (P' z)) y ≠ ⊤ := by
    rw [hKeq]; exact bergmanSup_multiplierWeight_ne_top hB hP hc₁ hy
  have hK₂ : bergmanSup B (fun z => multiplierWeight c₂ (P' z)) y ≠ ⊤ := by
    rw [hKeq]; exact bergmanSup_multiplierWeight_ne_top hB hP hc₂ hy
  have hcore := normSq_le_mul_bergmanSup_mul hB (hw'm c₁ hc₁) (hw'm c₂ hc₂)
    (fun z hz => multiplierWeight_ne_zero hc₁ (by rw [hP'eq z hz]; exact hPtop z hz))
    hG₁ hG₂ hGc ENNReal.ofReal_ne_top hint hy hK₁ hK₂
  have hGyy : G (y, y) = f y := by
    simp only [hGdef, chartT_apply, neg_add_cancel, ← subspaceCLM_eq_join]
    exact hFext y (by rw [hslice]; exact hy)
  rw [hGyy, hKeq, hKeq] at hcore
  exact hcore

/-- `bergmanSup_add_le` for any Borel structure on `ℂ^d`. -/
theorem bergmanSup_add_le' {d : ℕ} [i : MeasurableSpace (ComplexModel d)]
    [hi : BorelSpace (ComplexModel d)] {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧
      ∀ B : Set (ComplexModel d), IsOpen B → Convex ℝ B → (∀ z ∈ B, ‖z‖ < R) →
      ∀ P : ComplexModel d → EReal, PlurisubharmonicOn P B →
      ∀ c₁ c₂ : ℝ, 0 < c₁ → 0 < c₂ → ∀ y ∈ B,
        bergmanSup B (fun z => multiplierWeight (c₁ + c₂) (P z)) y ≤
          ENNReal.ofReal C * bergmanSup B (fun z => multiplierWeight c₁ (P z)) y *
            bergmanSup B (fun z => multiplierWeight c₂ (P z)) y := by
  obtain rfl : i = borel _ := hi.measurable_eq
  exact bergmanSup_add_le d R hR

/-- **Subadditivity of Bergman weights** (logarithmic form): with `C` from
`bergmanSup_add_le'`, `log K_{(c₁+c₂)P} ≤ log C + log K_{c₁P} + log K_{c₂P}`.  For
`c₁ = c₂ = m` and the normalisation `φ_m = m⁻¹ log K_{mP}` this is Demailly's
`φ_{2m} ≤ φ_m + (log C)/(2m)`. -/
theorem bergmanLog_add_le {d : ℕ} [MeasurableSpace (ComplexModel d)]
    [BorelSpace (ComplexModel d)] {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧
      ∀ B : Set (ComplexModel d), IsOpen B → Convex ℝ B → (∀ z ∈ B, ‖z‖ < R) →
      ∀ P : ComplexModel d → EReal, PlurisubharmonicOn P B →
      ∀ c₁ c₂ : ℝ, 0 < c₁ → 0 < c₂ → ∀ y ∈ B,
        bergmanLog B (fun z => multiplierWeight (c₁ + c₂) (P z)) y ≤
          (Real.log C : EReal) + bergmanLog B (fun z => multiplierWeight c₁ (P z)) y +
            bergmanLog B (fun z => multiplierWeight c₂ (P z)) y := by
  obtain ⟨C, hC, h⟩ := bergmanSup_add_le' (d := d) hR
  refine ⟨C, hC, fun B hB hconv hbd P hP c₁ c₂ hc₁ hc₂ y hy => ?_⟩
  have := ENNReal.log_monotone (h B hB hconv hbd P hP c₁ c₂ hc₁ hc₂ y hy)
  rwa [ENNReal.log_mul_add, ENNReal.log_mul_add, ENNReal.log_ofReal_of_pos hC] at this

end

end Hironaka.BergmanSubadditivity
