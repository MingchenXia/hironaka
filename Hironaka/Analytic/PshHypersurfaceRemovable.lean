import Hironaka.Analytic.PshCodimTwoExtension

set_option autoImplicit false

/-!
# Reduction of hypersurface removability to transverse one-dimensional slices

Let `H = {z_i = 0}` in a complex coordinate domain `B`.  For a function `ψ`
which is locally bounded above off `H`, write `ψ̂` for the upper-semicontinuous
regularization of the function equal to `ψ` off `H` and `-∞` on `H`.

This file proves the analytic reduction which remains after the
Grauert--Remmert stratification: if every affine complex line transverse to
`H` carries the one-dimensional subharmonic extension of `ψ̂`, then `ψ̂` is
plurisubharmonic on `B`.  The proof is not a closure axiom.  It derives the
submean inequality on a tangent affine disc by tilting its direction into the
normal coordinate and passing to the limit with Fatou's lemma.

Thus the only analytic input left at a smooth hypersurface point is the
classical *one-dimensional* removable-singularity theorem on the transverse
punctured discs.  In particular, no global PSH conclusion is stored in the
slice hypothesis.
-/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace Hironaka.PshHypersurfaceRemovable

open Hironaka
open PshCodimTwoExtension

noncomputable section

variable {n : ℕ}

/-- The coordinate hyperplane `z_i = 0`. -/
def coordHyperplane (i : Fin n) : Set (ComplexModel n) := {z | z i = 0}

/-- The complex-linear direction used to parametrize an affine complex line. -/
def affineLine (v : ComplexModel n) : ℂ →L[ℂ] ComplexModel n :=
  (ContinuousLinearMap.id ℂ ℂ).smulRight v

@[simp] theorem affineLine_apply (v : ComplexModel n) (z : ℂ) : affineLine v z = z • v := rfl

/-- The actual one-dimensional residual obligation.  It asks for PSH only on
lines whose direction meets the coordinate hyperplane transversely.  It does
*not* state PSH on the ambient domain. -/
def HasTransverseLineSlices (i : Fin n) (F : ComplexModel n → EReal)
    (B : Set (ComplexModel n)) : Prop :=
  ∀ (x v : ComplexModel n), v i ≠ 0 →
    PlurisubharmonicOn (fun z => F (x + affineLine v z))
      ((fun z => x + affineLine v z) ⁻¹' B)

/-- A transverse affine line meets the coordinate hyperplane in precisely one
parameter value. -/
theorem preimage_coordHyperplane_eq_singleton {i : Fin n}
    {x v : ComplexModel n} (hv : v i ≠ 0) :
    (fun z : ℂ => x + affineLine v z) ⁻¹' coordHyperplane i = {-(x i) / v i} := by
  ext z
  change x i + z * v i = 0 ↔ z = -(x i) / v i
  constructor
  · intro hz
    apply (eq_div_iff hv).mpr
    calc z * v i = (x i + z * v i) - x i := by ring
      _ = -(x i) := by rw [hz]; ring
  · rintro rfl
    field_simp
    ring

/-- The already-given PSH branch restricts to a one-dimensional PSH function
on the transverse line with its single hyperplane-intersection point deleted.
This is the exact input to the classical punctured-disc removable theorem. -/
theorem plurisubharmonicOn_comp_transverseLine_off_coordHyperplane
    {i : Fin n} {B : Set (ComplexModel n)} {ψ : ComplexModel n → EReal}
    (hψ : PlurisubharmonicOn ψ (B \ coordHyperplane i))
    (x v : ComplexModel n) (hv : v i ≠ 0) :
    PlurisubharmonicOn (fun z => ψ (x + affineLine v z))
      ((fun z => x + affineLine v z) ⁻¹' B \ {-(x i) / v i}) := by
  rw [← preimage_coordHyperplane_eq_singleton hv]
  exact hψ.comp_affine (affineLine v) x

/-- Local boundedness above on a coordinate domain. -/
def LocallyBoundedAboveOn (F : ComplexModel n → EReal)
    (B : Set (ComplexModel n)) : Prop :=
  ∀ x ∈ B, ∃ U : Set (ComplexModel n), U ∈ 𝓝 x ∧
    ∃ C : ℝ, ∀ y ∈ U, F y ≤ (C : EReal)

/-- Local boundedness above of the branch before its `-∞` extension. -/
def LocallyBoundedAboveOff (A B : Set (ComplexModel n))
    (ψ : ComplexModel n → EReal) : Prop :=
  ∀ x ∈ B, ∃ U : Set (ComplexModel n), U ∈ 𝓝 x ∧
    ∃ C : ℝ, ∀ y ∈ U, y ∉ A → ψ y ≤ (C : EReal)

/-- The regularized branch inherits a genuine local upper bound from the
branch off the exceptional set. -/
theorem locallyBoundedAboveOn_extension
    {A B : Set (ComplexModel n)} {ψ : ComplexModel n → EReal}
    (hbound : LocallyBoundedAboveOff A B ψ) :
    LocallyBoundedAboveOn (extension A ψ) B := by
  classical
  intro x hx
  obtain ⟨U, hU, C, hC⟩ := hbound x hx
  obtain ⟨V, hVU, hVopen, hxV⟩ := _root_.mem_nhds_iff.mp hU
  refine ⟨V, hVopen.mem_nhds hxV, C, ?_⟩
  intro y hy
  refine (uscRegularization_le_localSup _ (hVopen.mem_nhds hy)).trans
    (iSup₂_le fun z hz => ?_)
  by_cases hzA : z ∈ A
  · simp [hzA]
  · simp only [if_neg hzA]
    exact hC z (hVU hz) hzA

/-- Every direction can be approximated by one transverse to the chosen
coordinate hyperplane. -/
theorem exists_transverse_direction (i : Fin n) (v : ComplexModel n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ w : ComplexModel n, ‖w - v‖ < ε ∧ w i ≠ 0 := by
  by_cases hv : v i = 0
  · refine ⟨v + ((ε / 2 : ℝ) : ℂ) • unitVec i, ?_, ?_⟩
    · have hdiff : v + ((ε / 2 : ℝ) : ℂ) • unitVec i - v =
          ((ε / 2 : ℝ) : ℂ) • unitVec i := by abel
      rw [hdiff, norm_smul, norm_unitVec]
      simpa [abs_of_pos hε] using (show ε / 2 < ε by linarith)
    · simp [hv, hε.ne']
  · exact ⟨v, by simpa using hε, hv⟩

/-- A transverse line slice supplies the disc submean inequality for every
closed affine disc in that line. -/
theorem transverse_circleDeficit_le
    {i : Fin n} {F : ComplexModel n → EReal} {B : Set (ComplexModel n)}
    (hslices : HasTransverseLineSlices i F B) {x v : ComplexModel n}
    (hv : v i ≠ 0) {r C : ℝ} (hr : 0 < r)
    (hD : affineClosedDisc x v r ⊆ B)
    (hC : ∀ y ∈ affineClosedDisc x v r, F y ≤ (C : EReal)) :
    circleDeficit F x v r C ≤
      ENNReal.ofReal (2 * Real.pi) * ((C : EReal) - F x).toENNReal := by
  let L : ℂ →L[ℂ] ComplexModel n := affineLine v
  have hD' : affineClosedDisc (0 : ℂ) 1 r ⊆ (fun z => x + L z) ⁻¹' B := by
    rintro z ⟨ζ, hζ, rfl⟩
    apply hD
    exact ⟨ζ, hζ, by simp [L]⟩
  have hC' : ∀ z ∈ affineClosedDisc (0 : ℂ) 1 r,
      F (x + L z) ≤ (C : EReal) := by
    rintro z ⟨ζ, hζ, rfl⟩
    apply hC
    exact ⟨ζ, hζ, by simp [L]⟩
  have hsub := (hslices x v hv).discPshOn.submean (0 : ℂ) 1 r hr hD' C hC'
  change circleDeficit (fun z => F (x + L z)) 0 1 r C ≤ _ at hsub
  rw [circleDeficit_comp_affine F L x] at hsub
  simpa [L] using hsub

/-- The approximate submean inequality at an arbitrary disc.  Its proof only
uses the submean inequalities on nearby transverse discs; upper
semicontinuity and Fatou transport their deficits to the limiting disc. -/
theorem circleDeficit_transverse_approximation
    {i : Fin n} {F : ComplexModel n → EReal} {B : Set (ComplexModel n)}
    (hB : IsOpen B) (husc : UpperSemicontinuous F)
    (hslices : HasTransverseLineSlices i F B)
    {x v : ComplexModel n} {r : ℝ} (hr : 0 < r)
    (hD : affineClosedDisc x v r ⊆ B)
    {C : ℝ} (hC : ∀ y ∈ affineClosedDisc x v r, F y ≤ (C : EReal))
    {η : ℝ} (hη : 0 < η) {b : ℝ} (hb : (b : EReal) < F x) :
    circleDeficit F x v r (C + η) ≤
      ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (C + η - b) := by
  choose w hwv hwi using fun k : ℕ =>
    exists_transverse_direction i v (by positivity : 0 < 1 / ((k : ℝ) + 1))
  have hw_tend : Tendsto w atTop (𝓝 v) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun k => (hwv k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  set O := B ∩ F ⁻¹' Iio ((C + η : ℝ) : EReal)
  have hO : IsOpen O := hB.inter (husc.isOpen_preimage _)
  have hDO : affineClosedDisc x v r ⊆ O := fun p hp =>
    ⟨hD hp, (hC p hp).trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith))⟩
  have hDc : IsCompact (affineClosedDisc x v r) :=
    (isCompact_closedBall (0 : ℂ) r).image (by fun_prop)
  obtain ⟨ρ, hρ, hρO⟩ := hDc.exists_thickening_subset_open hO hDO
  have hev : ∀ᶠ k : ℕ in atTop, affineClosedDisc x (w k) r ⊆ O := by
    have h1 : Tendsto (fun k : ℕ => r * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul r
    filter_upwards [h1.eventually (gt_mem_nhds hρ)] with k hk
    rintro _ ⟨ζ, hζ, rfl⟩
    rw [mem_closedBall, dist_zero_right] at hζ
    refine hρO (mem_thickening_iff.mpr ⟨x + ζ • v,
      ⟨ζ, by simpa using hζ, rfl⟩, ?_⟩)
    rw [dist_eq_norm]
    calc ‖x + ζ • w k - (x + ζ • v)‖ = ‖ζ • (w k - v)‖ := by
          congr 1
          simp only [smul_sub]
          abel
      _ ≤ ‖ζ‖ * ‖w k - v‖ := by rw [norm_smul]
      _ ≤ r * (1 / (k + 1)) := by gcongr; exact (hwv k).le
      _ = r * (1 / ((k : ℝ) + 1)) := by norm_num
      _ < ρ := hk
  have hsub : ∀ᶠ k : ℕ in atTop, circleDeficit F x (w k) r (C + η) ≤
      ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (C + η - b) := by
    filter_upwards [hev] with k hk
    have hdisc := transverse_circleDeficit_le hslices (hwi k) hr
      (fun p hp => (hk hp).1) (C := C + η) fun p hp => ((hk hp).2 : F p < _).le
    refine hdisc.trans (mul_le_mul_right ?_ _)
    rw [← EReal.real_coe_toENNReal (C + η - b)]
    exact EReal.toENNReal_le_toENNReal (by
      rw [EReal.coe_sub]
      exact EReal.sub_le_sub le_rfl hb.le)
  have hmeas : ∀ k : ℕ, AEMeasurable
      (fun t => deficit (C + η) (F (x + circleMap 0 r t • w k)))
      (volume.restrict (Ioc 0 (2 * Real.pi))) := fun k =>
    ((continuous_deficit _).measurable.comp
      (husc.measurable.comp (by fun_prop : Continuous fun t : ℝ =>
        x + circleMap 0 r t • w k).measurable)).aemeasurable
  have hpointwise : ∀ t : ℝ, deficit (C + η) (F (x + circleMap 0 r t • v)) ≤
      liminf (fun k => deficit (C + η) (F (x + circleMap 0 r t • w k))) atTop := fun t => by
    have hp : Tendsto (fun k => x + circleMap 0 r t • w k) atTop
        (𝓝 (x + circleMap 0 r t • v)) :=
      tendsto_const_nhds.add (hw_tend.const_smul _)
    have hls : limsup (fun k => F (x + circleMap 0 r t • w k)) atTop ≤
        F (x + circleMap 0 r t • v) :=
      (limsup_le_limsup_of_le hp (by isBoundedDefault) (by isBoundedDefault)).trans
        (upperSemicontinuousAt_iff_limsup_le.mp (husc _))
    calc deficit (C + η) (F (x + circleMap 0 r t • v))
        ≤ deficit (C + η) (limsup (fun k => F (x + circleMap 0 r t • w k)) atTop) :=
          antitone_deficit _ hls
      _ = liminf (fun k => deficit (C + η) (F (x + circleMap 0 r t • w k))) atTop :=
          (antitone_deficit _).map_limsup_of_continuousAt _
            (continuous_deficit _).continuousAt
  calc circleDeficit F x v r (C + η)
      = ∫⁻ t in Ioc 0 (2 * Real.pi), deficit (C + η) (F (x + circleMap 0 r t • v)) := rfl
    _ ≤ ∫⁻ t in Ioc 0 (2 * Real.pi),
          liminf (fun k => deficit (C + η) (F (x + circleMap 0 r t • w k))) atTop :=
        lintegral_mono hpointwise
    _ ≤ liminf (fun k => circleDeficit F x (w k) r (C + η)) atTop :=
        lintegral_liminf_le' hmeas
    _ ≤ _ := liminf_le_of_frequently_le' hsub.frequently

/-- The submean inequality on arbitrary affine discs follows from the
one-dimensional transverse slices.  This is the Fatou/tilting step in the
hypersurface removable-singularity argument. -/
theorem hasDiscSubmeanOn_of_transverseLineSlices
    {i : Fin n} {F : ComplexModel n → EReal} {B : Set (ComplexModel n)}
    (hB : IsOpen B) (husc : UpperSemicontinuous F) (hbound : LocallyBoundedAboveOn F B)
    (hslices : HasTransverseLineSlices i F B) :
    HasDiscSubmeanOn F B := by
  intro x v r hr hD C hC
  rcases eq_bot_or_bot_lt (F x) with hbot | hpos
  · rw [hbot]
    have : ((C : EReal) - ⊥).toENNReal = ⊤ := by simp
    rw [this, ENNReal.mul_top (by simp [Real.pi_pos])]
    exact le_top
  have hne_top : F x ≠ ⊤ := by
    have hxB : x ∈ B := hD
      (by simpa using mem_affineClosedDisc_of_norm_le x v (ζ := 0) (by simpa using hr.le))
    obtain ⟨U, hU, b, hb⟩ := hbound x hxB
    exact ne_top_of_le_ne_top (EReal.coe_ne_top b) (hb x (mem_of_mem_nhds hU))
  set a := (F x).toReal
  have ha : F x = (a : EReal) := (EReal.coe_toReal hne_top hpos.ne').symm
  have key : ∀ ε : ℝ, 0 < ε → circleDeficit F x v r C ≤
      ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (C - a + ε) := by
    intro ε hε
    have h := circleDeficit_transverse_approximation hB husc hslices hr hD hC
      (half_pos hε) (b := a - ε / 2) (by rw [ha]; exact EReal.coe_lt_coe_iff.mpr (by linarith))
    refine le_trans ?_ (h.trans_eq (by congr 2; ring))
    refine lintegral_mono fun t => EReal.toENNReal_le_toENNReal
      (EReal.sub_le_sub (EReal.coe_le_coe_iff.mpr (by linarith)) le_rfl)
  rw [ha, ← EReal.coe_sub, EReal.real_coe_toENNReal]
  have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (C - a + ε))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (C - a))) := by
    refine ENNReal.Tendsto.const_mul ?_ (Or.inr ENNReal.ofReal_ne_top)
    have : Tendsto (fun ε : ℝ => C - a + ε) (𝓝[>] 0) (𝓝 (C - a + 0)) :=
      (tendsto_const_nhds.add tendsto_id).mono_left nhdsWithin_le_nhds
    simpa using ENNReal.tendsto_ofReal this
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)

/-- A locally bounded upper-semicontinuous function which is subharmonic on
all transverse complex lines is plurisubharmonic. -/
theorem plurisubharmonicOn_of_transverseLineSlices
    {i : Fin n} {F : ComplexModel n → EReal} {B : Set (ComplexModel n)}
    (hB : IsOpen B) (husc : UpperSemicontinuous F)
    (hbound : LocallyBoundedAboveOn F B)
    (hslices : HasTransverseLineSlices i F B) :
    PlurisubharmonicOn F B := by
  apply DiscPshOn.plurisubharmonicOn
  refine ⟨?_, husc.upperSemicontinuousOn _,
    hasDiscSubmeanOn_of_transverseLineSlices hB husc hbound hslices⟩
  intro x hx
  obtain ⟨U, hU, C, hC⟩ := hbound x hx
  exact ne_top_of_le_ne_top (EReal.coe_ne_top C) (hC x (mem_of_mem_nhds hU))
  exact hB

/-- The exact smooth-hypersurface reduction for the upper regularization used
in the Grauert--Remmert step.  The sole remaining hypothesis is the
one-dimensional transverse-slice extension property. -/
theorem plurisubharmonicOn_extensionAcross_coordHyperplane_of_transverseSlices
    {i : Fin n} {B : Set (ComplexModel n)} {ψ : ComplexModel n → EReal}
    (hB : IsOpen B)
    (hbound : LocallyBoundedAboveOff (coordHyperplane i) B ψ)
    (hslices : HasTransverseLineSlices i (extension (coordHyperplane i) ψ) B) :
    PlurisubharmonicOn (extension (coordHyperplane i) ψ) B :=
  plurisubharmonicOn_of_transverseLineSlices hB
    (upperSemicontinuous_extension _ _) (locallyBoundedAboveOn_extension hbound) hslices

end

end Hironaka.PshHypersurfaceRemovable
