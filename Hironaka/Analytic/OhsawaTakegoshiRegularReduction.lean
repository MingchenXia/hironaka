import Hironaka.Analytic.WeightedL2ExtensionLimit
import Hironaka.Analytic.OhsawaTakegoshiInterface

set_option autoImplicit false

/-!
# The Ohsawa--Takegoshi theorem from its regular case

`OhsawaTakegoshiHyperplaneRegular` is the Ohsawa--Takegoshi extension theorem in the setting
where its L² proofs start: a *bounded* convex domain `Ω`, a weight `φ` which is smooth and
plurisubharmonic on a neighbourhood `U` of `closure Ω`, and data `f` holomorphic on the slice
of `U`.  This module derives the general interface `OhsawaTakegoshiHyperplane` from it.

For finite right-hand side `S`: exhaust `Ω` by bounded convex `K k` with
`closure (K k) ⊆ K (k + 1)`, truncate `φ` to `max (φ, -k)`, and regularize the truncation on
`K (k + 1)` by a decreasing sequence of smooth plurisubharmonic functions
(`HolomorphicPullback.exists_decreasingMollifierApproximation`).  The regular theorem gives
extensions on `K k` for each regularization, with the right-hand side at most `C S` because
the regularizations lie above `φ`.  Two applications of the weighted limit lemma
(`exists_differentiableOn_extension_of_weighted_bounds`) pass to the truncation on `K k`, and
then to `φ` on `⋃ K k = Ω`.
-/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal ContDiff

namespace Hironaka

noncomputable section

open Hironaka.MongeAmpere

variable {m : ℕ}

/-- The regular Ohsawa--Takegoshi extension property in dimension `m + 1` for the height bound
`R` and the constant `C`. -/
def RegularHyperplaneExtension (m : ℕ)
    [MeasurableSpace (ComplexModel m)] [BorelSpace (ComplexModel m)]
    [MeasurableSpace (ComplexModel (m + 1))] [BorelSpace (ComplexModel (m + 1))]
    (R C : ℝ) : Prop :=
  ∀ Ω : Set (ComplexModel (m + 1)), IsOpen Ω → Convex ℝ Ω → Bornology.IsBounded Ω →
    (∀ z ∈ Ω, ‖z (Fin.last m)‖ < R) →
    ∀ U : Set (ComplexModel (m + 1)), IsOpen U → closure Ω ⊆ U →
    ∀ φ : ComplexModel (m + 1) → ℝ, ContDiffOn ℝ ∞ φ U →
      PlurisubharmonicOn (fun z => (φ z : EReal)) U →
      ∀ c : ℝ, 0 < c → ∀ f : ComplexModel m → ℂ,
        DifferentiableOn ℂ f (hyperplaneEmbedding m ⁻¹' U) →
        ∃ F : ComplexModel (m + 1) → ℂ, DifferentiableOn ℂ F Ω ∧
          (∀ w ∈ hyperplaneEmbedding m ⁻¹' Ω, F (hyperplaneEmbedding m w) = f w) ∧
          (∫⁻ z in Ω, multiplierDensity (fun z => (φ z : EReal)) c F z) ≤
            ENNReal.ofReal C * ∫⁻ w in hyperplaneEmbedding m ⁻¹' Ω,
              multiplierDensity (fun w => (φ (hyperplaneEmbedding m w) : EReal)) c f w

/-- **The Ohsawa--Takegoshi theorem, regular case**: bounded convex domains whose last
coordinate is bounded by `R`, weights smooth and plurisubharmonic near the closure, data
holomorphic near the closure of the slice.  The constant depends only on `m` and `R`.

This definition is only the statement; it is proved as `ohsawaTakegoshiHyperplaneRegular_proved`
in `Hironaka.OhsawaTakegoshiRegularProof`. -/
def OhsawaTakegoshiHyperplaneRegular : Prop := by
  exact ∀ m : ℕ, by
    letI : MeasurableSpace (ComplexModel m) := borel _
    letI : BorelSpace (ComplexModel m) := ⟨rfl⟩
    letI : MeasurableSpace (ComplexModel (m + 1)) := borel _
    letI : BorelSpace (ComplexModel (m + 1)) := ⟨rfl⟩
    exact ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧ RegularHyperplaneExtension m R C

theorem multiplierWeight_coe_eq (c : ℝ) :
    (fun a : ℝ => multiplierWeight c (a : EReal)) =
      fun a => ENNReal.ofReal (Real.exp (-(c * a))) := by
  funext a
  exact multiplierWeight_coe c a

theorem continuous_multiplierWeight_coe (c : ℝ) :
    Continuous fun a : ℝ => multiplierWeight c (a : EReal) := by
  rw [multiplierWeight_coe_eq]
  exact ENNReal.continuous_ofReal.comp (by fun_prop)

/-- First limit: from the smooth regularizations of `max (φ, -k)` on `L` to the truncation
itself, on a bounded convex `K` with `closure K ⊆ L`. -/
theorem exists_extension_truncation_of_regular
    [MeasurableSpace (ComplexModel m)] [BorelSpace (ComplexModel m)]
    [MeasurableSpace (ComplexModel (m + 1))] [BorelSpace (ComplexModel (m + 1))]
    {R C : ℝ} (hreg : RegularHyperplaneExtension m R C)
    {Ω : TopologicalSpace.Opens (ComplexModel (m + 1))} {K L : Set (ComplexModel (m + 1))}
    (hKo : IsOpen K) (hKc : Convex ℝ K) (hKb : Bornology.IsBounded K)
    (hKR : ∀ z ∈ K, ‖z (Fin.last m)‖ < R)
    (hLo : IsOpen L) (hKL : closure K ⊆ L) (hLb : Bornology.IsBounded L)
    (hLΩ : closure L ⊆ Ω)
    {φ : ComplexModel (m + 1) → EReal} (hφ : PlurisubharmonicOn φ Ω) (k : ℕ)
    {c : ℝ} (hc : 0 < c) {f : ComplexModel m → ℂ}
    (hf : DifferentiableOn ℂ f (hyperplaneEmbedding m ⁻¹' Ω))
    {S : ℝ≥0∞} (hS : S ≠ ⊤)
    (hSle : ∫⁻ w in hyperplaneEmbedding m ⁻¹' Ω,
      multiplierDensity (fun w => φ (hyperplaneEmbedding m w)) c f w ≤ S) :
    ∃ G : ComplexModel (m + 1) → ℂ, DifferentiableOn ℂ G K ∧
      (∀ w ∈ hyperplaneEmbedding m ⁻¹' K, G (hyperplaneEmbedding m w) = f w) ∧
      ∫⁻ z in K, ENNReal.ofReal (‖G z‖ ^ 2) *
        multiplierWeight c (truncationReal φ k z : EReal) ≤ ENNReal.ofReal C * S := by
  set ι := hyperplaneEmbedding m with hι
  have hLΩ' : L ⊆ Ω := subset_closure.trans hLΩ
  have hKLs : K ⊆ L := subset_closure.trans hKL
  have hKΩ : K ⊆ Ω := hKLs.trans hLΩ'
  let A : TopologicalSpace.Opens (ComplexModel (m + 1)) := ⟨L, hLo⟩
  have hA : RelativelyCompactIn A Ω := ⟨hLb.isCompact_closure, hLΩ⟩
  obtain ⟨fs, hfs⟩ := HolomorphicPullback.exists_decreasingMollifierApproximation
    (truncationReal_isLocallyBoundedPshOn hφ k) hA
  have hge : ∀ j, ∀ z ∈ L, truncationReal φ k z ≤ fs j z := fun j z hz =>
    (hfs.2.1 z hz).le_of_tendsto (hfs.2.2 z hz) j
  have hφle : ∀ z ∈ Ω, φ z ≤ (truncationReal φ k z : EReal) := fun z hz => by
    rw [coe_truncationReal hφ k hz]
    exact le_max_left _ _
  have hext := fun j => hreg K hKo hKc hKb hKR L hLo hKL (fs j) (hfs.1 j).1 (hfs.1 j).2.1 c hc f
    (hf.mono (preimage_mono hLΩ'))
  choose F hFd hFext hFint using hext
  have hKmeas : MeasurableSet (ι ⁻¹' K) :=
    (hKo.preimage (hyperplaneCLM m).continuous).measurableSet
  have hbound : ∀ j, ∫⁻ z in K, ENNReal.ofReal (‖F j z‖ ^ 2) *
      multiplierWeight c (fs j z : EReal) ≤ ENNReal.ofReal C * S := by
    intro j
    refine (hFint j).trans (mul_le_mul_of_nonneg_left ?_ zero_le)
    calc ∫⁻ w in ι ⁻¹' K, multiplierDensity (fun w => (fs j (ι w) : EReal)) c f w
        ≤ ∫⁻ w in ι ⁻¹' K, multiplierDensity (fun w => φ (ι w)) c f w := by
          refine setLIntegral_mono' hKmeas fun w hw => ?_
          refine mul_le_mul_of_nonneg_left (multiplierWeight_antitone hc.le ?_) zero_le
          exact (hφle _ (hKΩ hw)).trans (EReal.coe_le_coe_iff.mpr (hge j _ (hKLs hw)))
      _ ≤ ∫⁻ w in ι ⁻¹' Ω, multiplierDensity (fun w => φ (ι w)) c f w :=
          lintegral_mono_set (preimage_mono hKΩ)
      _ ≤ S := hSle
  have hUK : (⋃ _ : ℕ, K) = K := iUnion_const K
  obtain ⟨G, hG, hGext, hGint⟩ :=
    exists_differentiableOn_extension_of_weighted_bounds (ι := ι) (g := f)
      (U := fun _ => K) (w := fun j z => multiplierWeight c (fs j z : EReal))
      (fun _ => hKo) monotone_const
      (fun x hx i j hij => by
        rw [hUK] at hx
        exact multiplierWeight_antitone hc.le
          (EReal.coe_le_coe_iff.mpr (hfs.2.1 x (hKLs hx) hij)))
      (fun j => by
        rw [hUK]
        exact ((continuous_multiplierWeight_coe c).comp_continuousOn
          ((hfs.1 j).1.continuousOn.mono hKLs)).aemeasurable hKo.measurableSet)
      (fun x hx => by
        rw [hUK] at hx
        have hcont : ContinuousAt (fs 0) x :=
          (hfs.1 0).1.continuousOn.continuousAt (hLo.mem_nhds (hKLs hx))
        obtain ⟨r, hr, hball⟩ := Metric.continuousAt_iff.mp hcont 1 one_pos
        refine ⟨r, hr, Real.exp (-(c * (fs 0 x + 1))), Real.exp_pos _, fun y hy => ?_⟩
        rw [multiplierWeight_coe]
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
        have h1 := hball (mem_ball.mp hy)
        rw [Real.dist_eq] at h1
        have h2 : fs 0 y ≤ fs 0 x + 1 := by linarith [le_abs_self (fs 0 y - fs 0 x)]
        nlinarith)
      hFd (fun i a ha => hFext i a ha) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS) hbound
  simp only [hUK] at hG hGext hGint
  refine ⟨G, hG, fun w hw => hGext w hw, le_trans ?_ hGint⟩
  refine setLIntegral_mono' hKo.measurableSet fun z hz => ?_
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  have ht : Tendsto (fun j => multiplierWeight c (fs j z : EReal)) atTop
      (𝓝 (multiplierWeight c (truncationReal φ k z : EReal))) :=
    ((continuous_multiplierWeight_coe c).tendsto _).comp (hfs.2.2 z (hKLs hz))
  exact le_of_tendsto' ht fun j => le_iSup (fun j => multiplierWeight c (fs j z : EReal)) j

/-- The truncations `max (φ, -k)` recover the weight `e^{-cφ}` as a supremum. -/
theorem multiplierWeight_le_iSup_truncationReal {n : ℕ} {Ω : TopologicalSpace.Opens (ComplexModel n)}
    {φ : ComplexModel n → EReal} (hφ : PlurisubharmonicOn φ Ω) {c : ℝ} (hc : 0 < c)
    {z : ComplexModel n} (hz : z ∈ Ω) :
    multiplierWeight c (φ z) ≤ ⨆ k : ℕ, multiplierWeight c (truncationReal φ k z : EReal) := by
  by_cases hbot : φ z = ⊥
  · rw [hbot, multiplierWeight_bot hc]
    refine top_le_iff.mpr (iSup_eq_top.mpr fun b hb => ?_)
    obtain ⟨k, hk⟩ := exists_nat_gt (b.toReal / c)
    refine ⟨k, ?_⟩
    rw [truncationReal_at_pole k hbot, multiplierWeight_coe,
      ENNReal.lt_ofReal_iff_toReal_lt hb.ne]
    have h1 : b.toReal < c * k := by
      rwa [div_lt_iff₀ hc, mul_comm] at hk
    have h2 := Real.add_one_le_exp (-(c * -(k : ℝ)))
    linarith
  · have htop : φ z ≠ ⊤ := (hφ z hz).ne_top
    obtain ⟨k, hk⟩ := exists_nat_ge (-(φ z).toReal)
    refine le_iSup_of_le k (le_of_eq ?_)
    congr 1
    rw [coe_truncationReal hφ k hz]
    refine (max_eq_left ?_).symm
    rw [← EReal.coe_toReal htop hbot]
    exact EReal.coe_le_coe_iff.mpr (by linarith)

/-- **Ohsawa--Takegoshi for finite right-hand side**, from the regular case and a bounded
convex exhaustion of the domain. -/
theorem exists_extension_of_regular_of_exhaustion
    [MeasurableSpace (ComplexModel m)] [BorelSpace (ComplexModel m)]
    [MeasurableSpace (ComplexModel (m + 1))] [BorelSpace (ComplexModel (m + 1))]
    {R C : ℝ} (hreg : RegularHyperplaneExtension m R C)
    {Ω : TopologicalSpace.Opens (ComplexModel (m + 1))}
    (hΩR : ∀ z ∈ Ω, ‖z (Fin.last m)‖ < R)
    {K : ℕ → Set (ComplexModel (m + 1))} (hKo : ∀ k, IsOpen (K k))
    (hKc : ∀ k, Convex ℝ (K k)) (hKb : ∀ k, Bornology.IsBounded (K k))
    (hKcl : ∀ k, closure (K k) ⊆ K (k + 1)) (hKΩ : ∀ k, K k ⊆ Ω) (hKU : (⋃ k, K k) = Ω)
    {φ : ComplexModel (m + 1) → EReal} (hφ : PlurisubharmonicOn φ Ω)
    {c : ℝ} (hc : 0 < c) {f : ComplexModel m → ℂ}
    (hf : DifferentiableOn ℂ f (hyperplaneEmbedding m ⁻¹' Ω))
    (hS : ∫⁻ w in hyperplaneEmbedding m ⁻¹' Ω,
      multiplierDensity (fun w => φ (hyperplaneEmbedding m w)) c f w ≠ ⊤) :
    ∃ F : ComplexModel (m + 1) → ℂ, DifferentiableOn ℂ F Ω ∧
      (∀ w ∈ hyperplaneEmbedding m ⁻¹' Ω, F (hyperplaneEmbedding m w) = f w) ∧
      (∫⁻ z in Ω, multiplierDensity φ c F z) ≤
        ENNReal.ofReal C * ∫⁻ w in hyperplaneEmbedding m ⁻¹' Ω,
          multiplierDensity (fun w => φ (hyperplaneEmbedding m w)) c f w := by
  set ι := hyperplaneEmbedding m with hι
  set S := ∫⁻ w in ι ⁻¹' Ω, multiplierDensity (fun w => φ (ι w)) c f w with hSdef
  have hΩo : IsOpen (Ω : Set (ComplexModel (m + 1))) := Ω.isOpen
  have hlev := fun k => exists_extension_truncation_of_regular hreg (Ω := Ω)
    (hKo k) (hKc k) (hKb k) (fun z hz => hΩR z (hKΩ k hz)) (hKo (k + 1)) (hKcl k)
    (hKb (k + 1)) ((hKcl (k + 1)).trans (hKΩ (k + 2))) hφ k hc hf hS le_rfl
  choose G hG hGext hGint using hlev
  have hKmono : Monotone K := monotone_nat_of_le_succ fun k => subset_closure.trans (hKcl k)
  obtain ⟨F, hF, hFext, hFint⟩ :=
    exists_differentiableOn_extension_of_weighted_bounds (ι := ι) (g := f) (U := K)
      (w := fun k z => multiplierWeight c (truncationReal φ k z : EReal))
      hKo hKmono
      (fun x hx i j hij => by
        rw [hKU] at hx
        exact multiplierWeight_antitone hc.le
          (EReal.coe_le_coe_iff.mpr (truncationReal_antitone hφ hx hij)))
      (fun k => by
        rw [hKU]
        have hq : QuasiPlurisubharmonicOn (fun z => (truncationReal φ k z : EReal)) Ω :=
          fun x hx => (truncationReal_plurisubharmonicOn hφ k x hx).quasiPlurisubharmonicAt
        have h := aemeasurable_multiplierDensity_restrict_of_quasiPlurisubharmonicOn
          (μ := volume) hΩo hq hc.ne' (f := fun _ => (1 : ℂ)) continuousOn_const
        refine h.congr (Eventually.of_forall fun z => ?_)
        simp [multiplierDensity])
      (fun x hx => by
        rw [hKU] at hx
        obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩo x hx
        obtain ⟨B, hB0, hB⟩ := hφ.exists_nonnegative_compact_upper_bound
          (isCompact_closedBall x (r / 2)) ((closedBall_subset_ball (by linarith)).trans hball)
        refine ⟨r / 2, by positivity, Real.exp (-(c * B)), Real.exp_pos _, fun y hy => ?_⟩
        have hyΩ : y ∈ Ω := hball (ball_subset_ball (by linarith) hy)
        have htr : truncationReal φ 0 y ≤ B := by
          apply EReal.coe_le_coe_iff.mp
          rw [coe_truncationReal hφ 0 hyΩ]
          refine max_le (hB y (ball_subset_closedBall hy)) ?_
          exact EReal.coe_le_coe_iff.mpr (by simpa using hB0)
        rw [multiplierWeight_coe]
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by nlinarith)))
      hG (fun i a ha => hGext i a ha) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS) hGint
  simp only [hKU] at hF hFext hFint
  refine ⟨F, hF, fun w hw => hFext w hw, le_trans ?_ hFint⟩
  refine setLIntegral_mono' hΩo.measurableSet fun z hz => ?_
  exact mul_le_mul_of_nonneg_left (multiplierWeight_le_iSup_truncationReal hφ hc hz) zero_le

end

end Hironaka
