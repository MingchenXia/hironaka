import Hironaka.Analytic.PshDiscLocalGlobal
import Hironaka.Analytic.PshClosedDiscMaximum
import Hironaka.Analytic.PotentialTheory.EnvelopesBasic
import Hironaka.Analytic.PotentialTheory.PlurisubharmonicPullback
import Hironaka.Manifold.ComplexManifold

set_option autoImplicit false

/-!
# Plurisubharmonic functions extend across codimension-two sets

Source: Grauert–Remmert, *Plurisubharmonische Funktionen in komplexen Räumen* (1956), Satz 3;
Demailly, *Complex analytic and differential geometry*, I (5.24).

Let `B ⊆ ℂⁿ` be open and `A ⊆ B` with `B \ A` open and `A` contained in the coordinate plane
`{w_i = w_j = 0}`, `i ≠ j`.  Every plurisubharmonic function `ψ` on `B \ A` extends to a
plurisubharmonic function on `B`, namely the upper semicontinuous regularization of `ψ`
(extended by `-∞` on `A`).

* `exists_bound`: `ψ` is bounded above near every point of `B`.  Near a point of the plane,
  through `y ∉ A` one of the coordinate discs `y + t e_i`, `y + t e_j` misses `A`, and its
  boundary circle lies in a compact subset of `B \ A`; apply the maximum principle.
* `submean`: through a point `y ∉ A` near `x`, a slightly perturbed direction gives a disc missing
  `A`; the submean inequality on these discs passes to the limit by Fatou's lemma and upper
  semicontinuity.
-/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace Hironaka.PshCodimTwoExtension

open Hironaka

noncomputable section

variable {n : ℕ}

/-- The coordinate plane `{w_i = w_j = 0}`. -/
def coordPlane (i j : Fin n) : Set (ComplexModel n) := {w | w i = 0 ∧ w j = 0}

/-- The coordinate unit vector `e_d`. -/
def unitVec (d : Fin n) : ComplexModel n := EuclideanSpace.single d 1

@[simp] theorem unitVec_apply_self (d : Fin n) : unitVec d d = 1 := by simp [unitVec]

theorem unitVec_apply_ne {d d' : Fin n} (h : d' ≠ d) : unitVec d d' = 0 := by
  simp [unitVec, h]

@[simp] theorem norm_unitVec (d : Fin n) : ‖unitVec d‖ = 1 := by simp [unitVec]

/-- The complex line `t ↦ t • e_d`. -/
def lineMap (d : Fin n) : ℂ →L[ℂ] ComplexModel n :=
  (ContinuousLinearMap.id ℂ ℂ).smulRight (unitVec d)

@[simp] theorem lineMap_apply (d : Fin n) (t : ℂ) : lineMap d t = t • unitVec d := rfl

theorem norm_lineMap (d : Fin n) (t : ℂ) : ‖lineMap d t‖ = ‖t‖ := by
  simp [norm_smul]

variable {A B : Set (ComplexModel n)} {i j : Fin n}

/-- Through a point off `A` one of the two coordinate lines misses `A`. -/
theorem exists_coordLine_disjoint (hij : i ≠ j) (hA : A ⊆ coordPlane i j) {y : ComplexModel n}
    (hy : y ∉ A) : ∃ d : Fin n, (d = i ∨ d = j) ∧ ∀ t : ℂ, y + t • unitVec d ∉ A := by
  by_cases hc : y j = 0 ∧ y i ≠ 0
  · refine ⟨j, Or.inr rfl, fun t ht => hc.2 ?_⟩
    have := (hA ht).1
    simpa [unitVec_apply_ne hij] using this
  · refine ⟨i, Or.inl rfl, fun t ht => ?_⟩
    have h := hA ht
    have hi : y i + t = 0 := by simpa using h.1
    have hj : y j = 0 := by simpa [unitVec_apply_ne hij.symm] using h.2
    have hyi : y i = 0 := by by_contra h'; exact hc ⟨hj, h'⟩
    have ht0 : t = 0 := by simpa [hyi] using hi
    subst ht0
    simp at ht
    exact hy ht

/-- An upper semicontinuous function without `⊤` values is bounded above on a compact set. -/
theorem exists_bound_of_isCompact {K : Set (ComplexModel n)} (hK : IsCompact K)
    {ψ : ComplexModel n → EReal} (husc : UpperSemicontinuousOn ψ K) (hne : ∀ p ∈ K, ψ p ≠ ⊤) :
    ∃ M : ℝ, ∀ p ∈ K, ψ p ≤ M := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨0, fun p hp => hp.elim⟩
  obtain ⟨p₀, hp₀, hmax⟩ := husc.exists_isMaxOn hKne hK
  refine ⟨(ψ p₀).toReal, fun p hp => (hmax hp).trans ?_⟩
  induction h : ψ p₀ with
  | bot => exact bot_le
  | top => exact absurd h (hne p₀ hp₀)
  | coe a => simp

/-- **Local upper bound.** -/
theorem exists_bound (hij : i ≠ j) (hA : A ⊆ coordPlane i j)
    {ψ : ComplexModel n → EReal} (hψ : PlurisubharmonicOn ψ (B \ A)) {x₀ : ComplexModel n}
    (hx₀ : x₀ ∈ coordPlane i j) {R : ℝ} (hR : 0 < R) (hball : closedBall x₀ (3 * R) ⊆ B) :
    ∃ M : ℝ, ∀ y ∈ ball x₀ R, y ∉ A → ψ y ≤ M := by
  have hψd := hψ.discPshOn
  set K : Fin n → Set (ComplexModel n) := fun d => closedBall x₀ (3 * R) ∩ {p | R ≤ ‖p d‖}
  have hKsub : ∀ d, d = i ∨ d = j → K d ⊆ B \ A := by
    rintro d hd p ⟨hp, hpd⟩
    refine ⟨hball hp, fun hpA => ?_⟩
    have h0 : p d = 0 := by rcases hd with rfl | rfl <;> [exact (hA hpA).1; exact (hA hpA).2]
    change R ≤ ‖p d‖ at hpd
    rw [h0, norm_zero] at hpd
    linarith
  have hKc : ∀ d, IsCompact (K d) := fun d =>
    (isCompact_closedBall _ _).inter_right
      (isClosed_le continuous_const ((EuclideanSpace.proj d).continuous.norm))
  obtain ⟨Mi, hMi⟩ := exists_bound_of_isCompact (hKc i)
    (hψd.upperSemicontinuousOn.mono (hKsub i (Or.inl rfl)))
    fun p hp => hψd.ne_top p (hKsub i (Or.inl rfl) hp)
  obtain ⟨Mj, hMj⟩ := exists_bound_of_isCompact (hKc j)
    (hψd.upperSemicontinuousOn.mono (hKsub j (Or.inr rfl)))
    fun p hp => hψd.ne_top p (hKsub j (Or.inr rfl) hp)
  refine ⟨max Mi Mj, fun y hy hyA => ?_⟩
  obtain ⟨d, hd, hline⟩ := exists_coordLine_disjoint hij hA hyA
  have hKd : ∀ p ∈ K d, ψ p ≤ (max Mi Mj : ℝ) := fun p hp => by
    rcases hd with rfl | rfl
    · exact (hMi p hp).trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _))
    · exact (hMj p hp).trans (EReal.coe_le_coe_iff.mpr (le_max_right _ _))
  have hpsh := hψ.comp_affine (lineMap d) y
  have hdisc : closedBall (0 : ℂ) (2 * R) ⊆ (fun t => y + lineMap d t) ⁻¹' (B \ A) := by
    intro t ht
    refine ⟨hball ?_, hline t⟩
    rw [mem_closedBall, dist_eq_norm] at ht ⊢
    rw [mem_ball, dist_eq_norm] at hy
    calc ‖y + lineMap d t - x₀‖ ≤ ‖y - x₀‖ + ‖lineMap d t‖ := by
          rw [add_sub_right_comm]; exact norm_add_le _ _
      _ ≤ 3 * R := by rw [norm_lineMap]; simp only [sub_zero] at ht; linarith
  have hyd : ‖y d‖ < R := by
    have hx₀d : x₀ d = 0 := by rcases hd with rfl | rfl <;> [exact hx₀.1; exact hx₀.2]
    calc ‖y d‖ = ‖(y - x₀) d‖ := by simp [hx₀d]
      _ ≤ ‖y - x₀‖ := PiLp.norm_apply_le _ _
      _ < R := by rwa [mem_ball, dist_eq_norm] at hy
  have h := PlurisubharmonicOn.le_const_on_closedBall_of_le_on_sphere hpsh (by linarith) hdisc
    (C := max Mi Mj) (fun t ht => by
      refine hKd _ ⟨(hdisc (sphere_subset_closedBall ht)).1 |> fun _ => ?_, ?_⟩
      · have ht' := sphere_subset_closedBall ht
        rw [mem_closedBall, dist_eq_norm] at ht' ⊢
        rw [mem_ball, dist_eq_norm] at hy
        calc ‖y + lineMap d t - x₀‖ ≤ ‖y - x₀‖ + ‖lineMap d t‖ := by
              rw [add_sub_right_comm]; exact norm_add_le _ _
          _ ≤ 3 * R := by rw [norm_lineMap]; simp only [sub_zero] at ht'; linarith
      · rw [mem_sphere, dist_zero_right] at ht
        show R ≤ ‖(y + lineMap d t) d‖
        have : (y + lineMap d t) d = y d + t := by simp
        rw [this]
        have := norm_sub_norm_le t (-(y d))
        simp only [sub_neg_eq_add] at this
        rw [add_comm]
        have h2 : ‖-(y d)‖ = ‖y d‖ := norm_neg _
        linarith) 0 (mem_closedBall_self (by linarith))
  simpa using h

open scoped Classical in
/-- The extension: the upper semicontinuous regularization of `ψ` extended by `⊥` on `A`. -/
def extension (A : Set (ComplexModel n)) (ψ : ComplexModel n → EReal) : ComplexModel n → EReal :=
  uscRegularization (fun y => if y ∈ A then ⊥ else ψ y)

theorem upperSemicontinuous_extension (A : Set (ComplexModel n)) (ψ : ComplexModel n → EReal) :
    UpperSemicontinuous (extension A ψ) :=
  upperSemicontinuous_uscRegularization _

open scoped Classical in
theorem extension_eq_uscRegularization (A : Set (ComplexModel n)) (ψ : ComplexModel n → EReal) :
    extension A ψ = uscRegularization (fun y => if y ∈ A then ⊥ else ψ y) := rfl

theorem extension_eq {ψ : ComplexModel n → EReal} (hψ : PlurisubharmonicOn ψ (B \ A))
    (hBA : IsOpen (B \ A)) {y : ComplexModel n} (hy : y ∈ B \ A) : extension A ψ y = ψ y := by
  classical
  rw [extension_eq_uscRegularization]
  refine le_antisymm ?_ ?_
  · refine le_of_forall_gt fun c hc => ?_
    have husc : ∀ c' > ψ y, ∀ᶠ p in 𝓝 y, ψ p < c' := fun c' hc' => by
      have h := hψ.discPshOn.upperSemicontinuousOn y hy c' hc'
      rwa [nhdsWithin_eq_nhds.mpr (hBA.mem_nhds hy)] at h
    obtain ⟨c', hc', hc'c⟩ := exists_between hc
    have hev : {p | p ∈ B \ A ∧ ψ p < c'} ∈ 𝓝 y :=
      Filter.inter_mem (hBA.mem_nhds hy) (husc c' hc')
    refine lt_of_le_of_lt ?_ hc'c
    refine (uscRegularization_le_localSup _ hev).trans (iSup₂_le fun p hp => ?_)
    simp only [if_neg hp.1.2]
    exact hp.2.le
  · have := le_uscRegularization (fun y => if y ∈ A then ⊥ else ψ y) y
    simp only [if_neg hy.2] at this
    exact this

theorem extension_ne_top (hij : i ≠ j) (hA : A ⊆ coordPlane i j) (hB : IsOpen B)
    {ψ : ComplexModel n → EReal} (hψ : PlurisubharmonicOn ψ (B \ A)) (hBA : IsOpen (B \ A))
    {x : ComplexModel n} (hx : x ∈ B) : extension A ψ x ≠ ⊤ := by
  classical
  by_cases hxA : x ∈ A
  · obtain ⟨ρ, hρ, hρB⟩ := Metric.isOpen_iff.mp hB x hx
    have hR : 0 < ρ / 6 := by positivity
    obtain ⟨M, hM⟩ := exists_bound hij hA hψ (hA hxA) hR
      ((closedBall_subset_ball (by linarith)).trans hρB)
    refine ne_top_of_le_ne_top (EReal.coe_ne_top M) ?_
    rw [extension_eq_uscRegularization]
    refine (uscRegularization_le_localSup _ (ball_mem_nhds x hR)).trans (iSup₂_le fun p hp => ?_)
    by_cases hpA : p ∈ A
    · simp [hpA]
    · simp only [if_neg hpA]; exact hM p hp hpA
  · rw [extension_eq hψ hBA ⟨hx, hxA⟩]
    exact hψ.discPshOn.ne_top x ⟨hx, hxA⟩

/-- A direction can be perturbed so that the complex line through a point off `A` misses `A`. -/
theorem exists_direction_disjoint (hij : i ≠ j) (hA : A ⊆ coordPlane i j) {y : ComplexModel n}
    (hy : y ∉ A) (v : ComplexModel n) {ε : ℝ} (hε : 0 < ε) :
    ∃ v' : ComplexModel n, ‖v' - v‖ < ε ∧ ∀ ζ : ℂ, y + ζ • v' ∉ A := by
  -- two candidate perturbations along `e_d`; at most one of them is bad
  have key : ∀ (d : Fin n) (F : ℂ → ℂ), (∀ δ₁ δ₂ : ℝ, δ₁ ≠ δ₂ → F δ₁ = 0 → F δ₂ = 0 → False) →
      (∀ δ : ℝ, F δ ≠ 0 → ∀ ζ : ℂ, y + ζ • (v + (δ : ℂ) • unitVec d) ∉ A) →
      ∃ v' : ComplexModel n, ‖v' - v‖ < ε ∧ ∀ ζ : ℂ, y + ζ • v' ∉ A := by
    intro d F hF hgood
    have hnorm : ∀ δ : ℝ, 0 < δ → δ < ε → ‖(v + (δ : ℂ) • unitVec d) - v‖ < ε := fun δ h0 h1 => by
      simp [norm_smul, abs_of_pos h0, h1]
    by_cases h1 : F (ε / 2 : ℝ) = 0
    · have h2 : F (ε / 4 : ℝ) ≠ 0 := fun h2 => hF _ _ (by linarith) h1 h2
      exact ⟨_, hnorm _ (by positivity) (by linarith), hgood _ h2⟩
    · exact ⟨_, hnorm _ (by positivity) (by linarith), hgood _ h1⟩
  by_cases hyP : y ∈ coordPlane i j
  · -- make `v' i ≠ 0`; then the line meets the plane only at `y`
    refine key i (fun δ => v i + δ) (fun δ₁ δ₂ h h₁ h₂ => h ?_) fun δ hδ ζ hζ => ?_
    · have := h₁.trans h₂.symm
      exact_mod_cast add_left_cancel this
    · have h := (hA hζ).1
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, unitVec_apply_self, mul_one,
        hyP.1, zero_add] at h
      rcases mul_eq_zero.mp h with rfl | h'
      · simp at hζ; exact hy hζ
      · exact hδ h'
  · -- make the determinant `y_i v'_j - y_j v'_i` nonzero
    have hyij : y i ≠ 0 ∨ y j ≠ 0 := by
      by_contra h; push Not at h; exact hyP h
    have hdet : ∀ v' : ComplexModel n, y i * v' j - y j * v' i ≠ 0 → ∀ ζ : ℂ, y + ζ • v' ∉ A :=
      fun v' hv' ζ hζ => by
        have h : (y + ζ • v') i = 0 ∧ (y + ζ • v') j = 0 := hA hζ
        simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h
        apply hv'
        have hi : y i = -(ζ * v' i) := by linear_combination h.1
        have hj : y j = -(ζ * v' j) := by linear_combination h.2
        rw [hi, hj]; ring
    rcases hyij with hyi | hyj
    · refine key j (fun δ => y i * (v + (δ : ℂ) • unitVec j) j - y j * (v + (δ : ℂ) • unitVec j) i)
        (fun δ₁ δ₂ h h₁ h₂ => h ?_) fun δ hδ => hdet _ hδ
      · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, unitVec_apply_self,
          unitVec_apply_ne hij, mul_one, mul_zero, add_zero] at h₁ h₂
        have : y i * ((δ₁ : ℂ) - δ₂) = 0 := by linear_combination h₁ - h₂
        rcases mul_eq_zero.mp this with h0 | h0
        · exact absurd h0 hyi
        · exact Complex.ofReal_injective (sub_eq_zero.mp h0)
    · refine key i (fun δ => y i * (v + (δ : ℂ) • unitVec i) j - y j * (v + (δ : ℂ) • unitVec i) i)
        (fun δ₁ δ₂ h h₁ h₂ => h ?_) fun δ hδ => hdet _ hδ
      · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, unitVec_apply_self,
          unitVec_apply_ne hij.symm, mul_one, mul_zero, add_zero] at h₁ h₂
        have : y j * ((δ₂ : ℂ) - δ₁) = 0 := by linear_combination h₁ - h₂
        rcases mul_eq_zero.mp this with h0 | h0
        · exact absurd h0 hyj
        · exact Complex.ofReal_injective (sub_eq_zero.mp h0).symm


/-- The deficit `a ↦ (c - a)⁺`. -/
def deficit (c : ℝ) (a : EReal) : ℝ≥0∞ := ((c : EReal) - a).toENNReal

theorem continuous_deficit (c : ℝ) : Continuous (deficit c) := by
  refine EReal.continuous_toENNReal.comp ?_
  refine continuous_iff_continuousAt.mpr fun a => ?_
  have h : ContinuousAt ((fun p : EReal × EReal => p.1 + p.2) ∘ fun a : EReal => ((c : EReal), -a))
      a :=
    ContinuousAt.comp (EReal.continuousAt_add (p := ((c : EReal), -a)) (Or.inl (EReal.coe_ne_top c))
      (Or.inl (EReal.coe_ne_bot c))) (by fun_prop : Continuous fun a : EReal => ((c : EReal), -a)).continuousAt
  have hfun : (fun x : EReal => (c : EReal) - x) = fun x => (c : EReal) + -x :=
    funext fun x => sub_eq_add_neg _ _
  show ContinuousAt (fun x : EReal => (c : EReal) - x) a
  rw [hfun]
  exact h

theorem antitone_deficit (c : ℝ) : Antitone (deficit c) := fun _ _ h =>
  EReal.toENNReal_le_toENNReal (EReal.sub_le_sub le_rfl h)

theorem mem_affineClosedDisc_of_norm_le (x v : ComplexModel n) {r : ℝ} {ζ : ℂ} (hζ : ‖ζ‖ ≤ r) :
    x + ζ • v ∈ affineClosedDisc x v r :=
  ⟨ζ, by simpa using hζ, rfl⟩

theorem circleMap_mem_affineClosedDisc (x v : ComplexModel n) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    x + circleMap 0 r t • v ∈ affineClosedDisc x v r :=
  mem_affineClosedDisc_of_norm_le x v (by simp [abs_of_pos hr])

/-- **Approximate submean inequality** at a point where the extension exceeds `b`. -/
theorem circleDeficit_extension_le (hij : i ≠ j) (hA : A ⊆ coordPlane i j) (hB : IsOpen B)
    {ψ : ComplexModel n → EReal} (hψ : PlurisubharmonicOn ψ (B \ A)) (hBA : IsOpen (B \ A))
    {x v : ComplexModel n} {r : ℝ} (hr : 0 < r) (hD : affineClosedDisc x v r ⊆ B) {C : ℝ}
    (hC : ∀ y ∈ affineClosedDisc x v r, extension A ψ y ≤ (C : EReal)) {η : ℝ} (hη : 0 < η)
    {b : ℝ} (hb : (b : EReal) < extension A ψ x) :
    circleDeficit (extension A ψ) x v r (C + η) ≤
      ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (C + η - b) := by
  classical
  set u := extension A ψ with hu_def
  have husc : UpperSemicontinuous u := upperSemicontinuous_extension A ψ
  have hψd := hψ.discPshOn
  -- points `y k → x` off `A` with `ψ (y k) > b`
  have hpt : ∀ k : ℕ, ∃ y ∈ ball x (1 / (k + 1)), y ∉ A ∧ (b : EReal) < ψ y := fun k => by
    have h := hb.trans_le (uscRegularization_le_localSup
      (fun y => if y ∈ A then ⊥ else ψ y) (ball_mem_nhds x (by positivity : (0 : ℝ) < 1 / (k + 1))))
    obtain ⟨y, hy⟩ := lt_iSup_iff.mp h
    obtain ⟨hyb, hy⟩ := lt_iSup_iff.mp hy
    by_cases hyA : y ∈ A
    · simp [hyA] at hy
    · exact ⟨y, hyb, hyA, by simpa [hyA] using hy⟩
  choose y hyball hyA hyb using hpt
  have hdir : ∀ k : ℕ, ∃ w : ComplexModel n, ‖w - v‖ < 1 / (k + 1) ∧ ∀ ζ : ℂ, y k + ζ • w ∉ A :=
    fun k => exists_direction_disjoint hij hA (hyA k) v (by positivity)
  choose w hwv hwA using hdir
  have hy_tend : Tendsto y atTop (𝓝 x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ => dist_nonneg) (fun k => (mem_ball.mp (hyball k)).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hw_tend : Tendsto w atTop (𝓝 v) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun k => (hwv k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  -- the perturbed discs eventually lie in `B \ A` with `ψ ≤ C + η`
  set O := B ∩ u ⁻¹' Iio ((C + η : ℝ) : EReal)
  have hO : IsOpen O := hB.inter (husc.isOpen_preimage _)
  have hDO : affineClosedDisc x v r ⊆ O := fun p hp =>
    ⟨hD hp, (hC p hp).trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith))⟩
  have hDc : IsCompact (affineClosedDisc x v r) :=
    (isCompact_closedBall (0 : ℂ) r).image (by fun_prop)
  obtain ⟨ρ, hρ, hρO⟩ := hDc.exists_thickening_subset_open hO hDO
  have hev : ∀ᶠ k : ℕ in atTop, affineClosedDisc (y k) (w k) r ⊆ O := by
    have h1 : Tendsto (fun k : ℕ => (1 + r) * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 + r)
    filter_upwards [h1.eventually (gt_mem_nhds hρ)] with k hk
    rintro _ ⟨ζ, hζ, rfl⟩
    rw [mem_closedBall, dist_zero_right] at hζ
    refine hρO (mem_thickening_iff.mpr ⟨x + ζ • v, ⟨ζ, by simpa using hζ, rfl⟩, ?_⟩)
    rw [dist_eq_norm]
    calc ‖y k + ζ • w k - (x + ζ • v)‖ = ‖(y k - x) + ζ • (w k - v)‖ := by
          congr 1; simp only [smul_sub]; abel
      _ ≤ ‖y k - x‖ + ‖ζ‖ * ‖w k - v‖ := (norm_add_le _ _).trans (by rw [norm_smul])
      _ ≤ 1 / (k + 1) + r * (1 / (k + 1)) := by
          gcongr
          · exact (mem_ball_iff_norm.mp (hyball k)).le
          · exact (hwv k).le
      _ = (1 + r) * (1 / ((k : ℝ) + 1)) := by ring
      _ < ρ := hk
  -- the submean inequality on the perturbed discs
  have hbound : ∀ᶠ k : ℕ in atTop, circleDeficit u (y k) (w k) r (C + η) ≤
      ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (C + η - b) := by
    filter_upwards [hev] with k hk
    have hkBA : affineClosedDisc (y k) (w k) r ⊆ B \ A := by
      intro p hp
      refine ⟨(hk hp).1, ?_⟩
      obtain ⟨ζ, -, rfl⟩ := hp
      exact hwA k ζ
    have heq : ∀ p ∈ affineClosedDisc (y k) (w k) r, u p = ψ p := fun p hp =>
      extension_eq hψ hBA (hkBA hp)
    have hsub := hψd.submean (y k) (w k) r hr hkBA (C + η) fun p hp => by
      rw [← heq p hp]; exact ((hk hp).2 : u p < _).le
    have hcd : circleDeficit u (y k) (w k) r (C + η) = circleDeficit ψ (y k) (w k) r (C + η) := by
      unfold circleDeficit
      refine lintegral_congr fun t => ?_
      rw [heq _ (circleMap_mem_affineClosedDisc _ _ hr t)]
    rw [hcd]
    refine hsub.trans (mul_le_mul_right ?_ _)
    rw [← EReal.real_coe_toENNReal (C + η - b)]
    exact EReal.toENNReal_le_toENNReal (by
      rw [EReal.coe_sub]; exact EReal.sub_le_sub le_rfl (hyb k).le)
  -- Fatou
  have hmeas : ∀ k : ℕ, AEMeasurable
      (fun t => deficit (C + η) (u (y k + circleMap 0 r t • w k)))
      (volume.restrict (Ioc 0 (2 * Real.pi))) := fun k =>
    ((continuous_deficit _).measurable.comp
      (husc.measurable.comp (by fun_prop : Continuous fun t : ℝ =>
        y k + circleMap 0 r t • w k).measurable)).aemeasurable
  have hpointwise : ∀ t : ℝ, deficit (C + η) (u (x + circleMap 0 r t • v)) ≤
      liminf (fun k => deficit (C + η) (u (y k + circleMap 0 r t • w k))) atTop := fun t => by
    have hp : Tendsto (fun k => y k + circleMap 0 r t • w k) atTop
        (𝓝 (x + circleMap 0 r t • v)) :=
      hy_tend.add (hw_tend.const_smul _)
    have hls : limsup (fun k => u (y k + circleMap 0 r t • w k)) atTop ≤
        u (x + circleMap 0 r t • v) :=
      (limsup_le_limsup_of_le hp (by isBoundedDefault) (by isBoundedDefault)).trans
        (upperSemicontinuousAt_iff_limsup_le.mp (husc _))
    calc deficit (C + η) (u (x + circleMap 0 r t • v))
        ≤ deficit (C + η) (limsup (fun k => u (y k + circleMap 0 r t • w k)) atTop) :=
          antitone_deficit _ hls
      _ = liminf (fun k => deficit (C + η) (u (y k + circleMap 0 r t • w k))) atTop :=
          (antitone_deficit _).map_limsup_of_continuousAt _
            (continuous_deficit _).continuousAt
  calc circleDeficit u x v r (C + η)
      = ∫⁻ t in Ioc 0 (2 * Real.pi), deficit (C + η) (u (x + circleMap 0 r t • v)) := rfl
    _ ≤ ∫⁻ t in Ioc 0 (2 * Real.pi),
          liminf (fun k => deficit (C + η) (u (y k + circleMap 0 r t • w k))) atTop :=
        lintegral_mono hpointwise
    _ ≤ liminf (fun k => circleDeficit u (y k) (w k) r (C + η)) atTop :=
        lintegral_liminf_le' hmeas
    _ ≤ _ := liminf_le_of_frequently_le' hbound.frequently


theorem hasDiscSubmeanOn_extension (hij : i ≠ j) (hA : A ⊆ coordPlane i j) (hB : IsOpen B)
    {ψ : ComplexModel n → EReal} (hψ : PlurisubharmonicOn ψ (B \ A)) (hBA : IsOpen (B \ A)) :
    HasDiscSubmeanOn (extension A ψ) B := by
  intro x v r hr hD C hC
  have hxB : x ∈ B := hD (by simpa using mem_affineClosedDisc_of_norm_le x v (ζ := 0) (by simpa using hr.le))
  rcases eq_bot_or_bot_lt (extension A ψ x) with hbot | hpos
  · rw [hbot]
    have : ((C : EReal) - ⊥).toENNReal = ⊤ := by simp
    rw [this, ENNReal.mul_top (by simp [Real.pi_pos])]
    exact le_top
  have hne := extension_ne_top hij hA hB hψ hBA hxB
  set a := (extension A ψ x).toReal
  have ha : extension A ψ x = (a : EReal) := (EReal.coe_toReal hne hpos.ne').symm
  have key : ∀ ε : ℝ, 0 < ε → circleDeficit (extension A ψ) x v r C ≤
      ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (C - a + ε) := fun ε hε => by
    have h := circleDeficit_extension_le hij hA hB hψ hBA hr hD hC (half_pos hε)
      (b := a - ε / 2) (by rw [ha]; exact EReal.coe_lt_coe_iff.mpr (by linarith))
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

/-- **Grauert–Remmert extension.**  A plurisubharmonic function on `B \ A`, where `A` lies in a
coordinate plane of codimension two, extends to a plurisubharmonic function on `B`. -/
theorem plurisubharmonicOn_extension (hij : i ≠ j) (hA : A ⊆ coordPlane i j) (hB : IsOpen B)
    {ψ : ComplexModel n → EReal} (hψ : PlurisubharmonicOn ψ (B \ A)) (hBA : IsOpen (B \ A)) :
    PlurisubharmonicOn (extension A ψ) B ∧ EqOn (extension A ψ) ψ (B \ A) :=
  ⟨DiscPshOn.plurisubharmonicOn
    ⟨fun _ hx => extension_ne_top hij hA hB hψ hBA hx,
      (upperSemicontinuous_extension A ψ).upperSemicontinuousOn _,
      hasDiscSubmeanOn_extension hij hA hB hψ hBA⟩ hB,
    fun _ hy => extension_eq hψ hBA hy⟩

end

end Hironaka.PshCodimTwoExtension
