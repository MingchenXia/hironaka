import Hironaka.Analytic.OhsawaTakegoshiPoint

set_option autoImplicit false

/-!
# L² extension from a coordinate subspace

`exists_extension_from_subspace`: on an open convex domain `Ω ⊆ ℂ^{k+d}` contained in the ball of
radius `R`, with a plurisubharmonic weight `φ` and an exponent `c > 0`, every holomorphic function
`f` on the slice `Ω ∩ (ℂ^k × {0})` extends to a holomorphic `F` on `Ω` with

  `∫_Ω |F|² e^{-cφ} ≤ C ∫_{Ω ∩ ℂ^k} |f|² e^{-cφ}`,

where `C` depends only on `k`, `d` and `R`.  This is the Ohsawa--Takegoshi theorem for a linear
subspace of codimension `d`; it follows from the hyperplane theorem
(`ohsawaTakegoshiHyperplane_of_regular`, proved in this workspace) by induction on the
codimension, exactly as `OhsawaTakegoshiPoint.exists_extension_from_zero` does for a point (the
case `k = 0`).

It is the extension input of Demailly's subadditivity of Bergman kernels
(`K_{2m} ≤ C K_m²`, extension from the diagonal of `B × B`, which after the linear change of
variables `(z, w) ↦ (z, w - z)` is a coordinate subspace), Demailly, *Regularization of closed
positive currents and intersection theory* (1992), Prop. 3.7 / *Analytic methods in algebraic
geometry*, Thm. 13.21; programme step A6 of `TN.3.3.DEMPROVE`.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace Hironaka.OhsawaTakegoshiSubspace

noncomputable section



/-- The linear isometric embedding `ℂ^k → ℂ^{k+d}`, `w ↦ (w, 0)`, as the composite of `d`
hyperplane embeddings. -/
def subspaceCLM (k : ℕ) : (d : ℕ) → ComplexModel k →L[ℂ] ComplexModel (k + d)
  | 0 => ContinuousLinearMap.id ℂ (ComplexModel k)
  | d + 1 => (hyperplaneCLM (k + d)).comp (subspaceCLM k d)

@[simp] theorem subspaceCLM_zero (k : ℕ) (w : ComplexModel k) : subspaceCLM k 0 w = w := rfl

theorem subspaceCLM_succ (k d : ℕ) (w : ComplexModel k) :
    subspaceCLM k (d + 1) w = hyperplaneEmbedding (k + d) (subspaceCLM k d w) := rfl

/-- The embedding is isometric. -/
theorem norm_subspaceCLM (k : ℕ) : ∀ (d : ℕ) (w : ComplexModel k), ‖subspaceCLM k d w‖ = ‖w‖
  | 0, w => rfl
  | d + 1, w => by rw [subspaceCLM_succ, norm_hyperplaneEmbedding, norm_subspaceCLM k d w]

/-- The first `k` coordinates of `(w, 0)` are those of `w`. -/
theorem subspaceCLM_apply_castAdd (k : ℕ) : ∀ (d : ℕ) (w : ComplexModel k) (i : Fin k),
    subspaceCLM k d w (Fin.castAdd d i) = w i
  | 0, w, i => rfl
  | d + 1, w, i => by
    rw [subspaceCLM_succ]
    have : (Fin.castAdd (d + 1) i : Fin (k + d + 1)) = (Fin.castAdd d i).castSucc := rfl
    rw [this, hyperplaneEmbedding_castSucc, subspaceCLM_apply_castAdd k d w i]

/-- The last `d` coordinates of `(w, 0)` vanish. -/
theorem subspaceCLM_apply_natAdd (k : ℕ) : ∀ (d : ℕ) (w : ComplexModel k) (i : Fin d),
    subspaceCLM k d w (Fin.natAdd k i) = 0
  | 0, _, i => i.elim0
  | d + 1, w, i => by
    rw [subspaceCLM_succ]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have : (Fin.natAdd k (Fin.last d) : Fin (k + d + 1)) = Fin.last (k + d) := rfl
      rw [this, hyperplaneEmbedding_last]
    · have : (Fin.natAdd k j.castSucc : Fin (k + d + 1)) = (Fin.natAdd k j).castSucc := rfl
      rw [this, hyperplaneEmbedding_castSucc, subspaceCLM_apply_natAdd k d w j]

/-- **L² extension from a coordinate subspace** (Ohsawa--Takegoshi in codimension `d`). On an
open convex domain `Ω ⊆ ℂ^{k+d}` inside the ball of radius `R`, with a plurisubharmonic weight
`φ` and `c > 0`, every holomorphic `f` on the slice `{w : (w, 0) ∈ Ω}` extends to a holomorphic
`F` on `Ω` with `∫_Ω |F|² e^{-cφ} ≤ C ∫_{slice} |f|² e^{-cφ(·, 0)}`, `C` depending only on
`k`, `d`, `R`. -/
theorem exists_extension_from_subspace (k d : ℕ) : by
    letI : MeasurableSpace (ComplexModel k) := borel _
    letI : BorelSpace (ComplexModel k) := ⟨rfl⟩
    letI : MeasurableSpace (ComplexModel (k + d)) := borel _
    letI : BorelSpace (ComplexModel (k + d)) := ⟨rfl⟩
    exact ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
      ∀ Ω : Set (ComplexModel (k + d)), IsOpen Ω → Convex ℝ Ω → (∀ z ∈ Ω, ‖z‖ < R) →
      ∀ φ : ComplexModel (k + d) → EReal, PlurisubharmonicOn φ Ω → ∀ c : ℝ, 0 < c →
      ∀ f : ComplexModel k → ℂ, DifferentiableOn ℂ f (subspaceCLM k d ⁻¹' Ω) →
      ∃ F : ComplexModel (k + d) → ℂ, DifferentiableOn ℂ F Ω ∧
        (∀ w ∈ subspaceCLM k d ⁻¹' Ω, F (subspaceCLM k d w) = f w) ∧
        (∫⁻ z in Ω, multiplierDensity φ c F z) ≤
          ENNReal.ofReal C *
            ∫⁻ w in subspaceCLM k d ⁻¹' Ω,
              multiplierDensity (fun w => φ (subspaceCLM k d w)) c f w := by
  induction d with
  | zero =>
    let _ : MeasurableSpace (ComplexModel k) := borel _
    have _ : BorelSpace (ComplexModel k) := ⟨rfl⟩
    intro R _
    refine ⟨1, one_pos, fun Ω _ _ _ φ _ c _ f hf => ⟨f, hf, fun _ _ => rfl, ?_⟩⟩
    simp only [ENNReal.ofReal_one, one_mul]
    exact le_rfl
  | succ d ih =>
    let _ : MeasurableSpace (ComplexModel k) := borel _
    have _ : BorelSpace (ComplexModel k) := ⟨rfl⟩
    let _ : MeasurableSpace (ComplexModel (k + d)) := borel _
    have _ : BorelSpace (ComplexModel (k + d)) := ⟨rfl⟩
    let _ : MeasurableSpace (ComplexModel (k + d + 1)) := borel _
    have _ : BorelSpace (ComplexModel (k + d + 1)) := ⟨rfl⟩
    intro R hR
    obtain ⟨Cd, hCd, hd⟩ := ih R hR
    obtain ⟨CT, hCT, hOT⟩ :=
      ohsawaTakegoshiHyperplane_of_regular ohsawaTakegoshiHyperplaneRegular (k + d) R hR
    refine ⟨CT * Cd, mul_pos hCT hCd, fun Ω hΩ hconv hbd φ hφ c hc f hf => ?_⟩
    set Ω' : Set (ComplexModel (k + d)) := hyperplaneEmbedding (k + d) ⁻¹' Ω with hΩ'
    have hΩ'open : IsOpen Ω' := hΩ.preimage (continuous_hyperplaneEmbedding (k + d))
    have hΩ'conv : Convex ℝ Ω' :=
      hconv.linear_preimage ((hyperplaneCLM (k + d)).toLinearMap.restrictScalars ℝ)
    have hbd' : ∀ w ∈ Ω', ‖w‖ < R := fun w hw => by
      simpa [norm_hyperplaneEmbedding] using hbd _ hw
    have hφ' : PlurisubharmonicOn (fun w => φ (hyperplaneEmbedding (k + d) w)) Ω' :=
      hφ.comp_continuousLinearMap (hyperplaneCLM (k + d))
    have hpre : subspaceCLM k d ⁻¹' Ω' = subspaceCLM k (d + 1) ⁻¹' Ω := rfl
    obtain ⟨G, hGhol, hGext, hGint⟩ := hd Ω' hΩ'open hΩ'conv hbd' _ hφ' c hc f (hpre ▸ hf)
    have hbdlast : ∀ z ∈ Ω, ‖z (Fin.last (k + d))‖ < R := fun z hz =>
      lt_of_le_of_lt (PiLp.norm_apply_le z _) (hbd z hz)
    obtain ⟨F, hFhol, hFext, hFint⟩ := hOT Ω hΩ hconv hbdlast φ hφ c hc G hGhol
    refine ⟨F, hFhol, fun w hw => ?_, ?_⟩
    · rw [subspaceCLM_succ]
      exact (hFext (subspaceCLM k d w) hw).trans (hGext w hw)
    · calc (∫⁻ z in Ω, multiplierDensity φ c F z)
          ≤ ENNReal.ofReal CT * ∫⁻ v in Ω',
              multiplierDensity (fun v => φ (hyperplaneEmbedding (k + d) v)) c G v := hFint
        _ ≤ ENNReal.ofReal CT * (ENNReal.ofReal Cd * ∫⁻ w in subspaceCLM k (d + 1) ⁻¹' Ω,
              multiplierDensity (fun w => φ (subspaceCLM k (d + 1) w)) c f w) := by
          gcongr
          exact hGint
        _ = ENNReal.ofReal (CT * Cd) * ∫⁻ w in subspaceCLM k (d + 1) ⁻¹' Ω,
              multiplierDensity (fun w => φ (subspaceCLM k (d + 1) w)) c f w := by
          rw [ENNReal.ofReal_mul hCT.le, mul_assoc]

end

end Hironaka.OhsawaTakegoshiSubspace
