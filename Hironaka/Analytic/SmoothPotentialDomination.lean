import Hironaka.Analytic.ManifoldTubePositivity
import Hironaka.Analytic.PotentialTheory.LocalPotentials
import Hironaka.Blowup.BlowupBigPullback
import Hironaka.Analytic.AnalyticGluingData
import Hironaka.Analytic.KahlerCurrentPerturbation

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# A smooth potential of a strictly positive form dominates a Kähler form

Copy-4, step 6 of `prop:principalization`, ends with *"in particular `Ω_U`
dominates a Kähler form on `U`"*.  `Hironaka.ManifoldTubePositivity` produces the
strict positivity of `Ω_U = θ + ddᶜ(f̃ + B r_W²)` on a neighbourhood of `W`; this
file converts that into the form the gluing proposition consumes,
`Hironaka.AnalyticGluingData.DominatesKahlerFormOn`.

Two steps, both missing from the tree in the *relativised* form needed here.

* `plurisubharmonicOn_coe_of_smoothDDC_nonneg` generalises
  `Hironaka.plurisubharmonicOn_coe_of_smoothDDC_eq_zero` from `ddᶜh = 0` to
  `ddᶜh ≥ 0` on the diagonal.  Same proof: a global `C^∞` representative of the
  germ, then `plurisubharmonicOn_of_levi_nonneg`.  (The `eq_zero` statement lives
  in `FirstPass/`, which is human-only, so it is not restated in terms of this
  one; that would be the natural cleanup.)
* `thetaPlurisubharmonicOn_smooth_of_semipositive` is the *`On`* half of
  `Hironaka.thetaPlurisubharmonic_smooth_iff`.  The existing criterion tests
  semipositivity at every point of the manifold; step 6 has it only over an open
  `Ω`.  The local potential is simply restricted to the part of its domain lying
  over `Ω` (`Hironaka.IsSmoothLocalPotential.mono`), which is exactly what makes
  the relativised statement true and cheap.

The last theorem, `exists_pos_dominatesKahlerFormOn_of_forall_strictPosAt`, is
the quantitative step: strict positivity of `θ + ddᶜφ` on an open `U ⊇ K` with
`K` compact leaves room for one fixed Kähler background `ε ω`, on one open
`U' ⊆ U` still containing `K`.  As always with the tube, `ε` cannot be chosen
pointwise: the finite subcover fixes it on `K`, and openness of strict positivity
produces `U'`.
-/

open Set Filter
open scoped Topology ContDiff

namespace Hironaka.SmoothPotentialDomination

open Hironaka.PositiveClasses Hironaka.AnalyticGluingData
  PositivityPerturbation UniformTubePositivity KahlerPerturbation
  SmoothDDCForm ManifoldTubePositivity GlobalTubeFunction

noncomputable section

/-! ### Smooth functions with semipositive `ddᶜ` -/

variable {n : ℕ}

/-- **A smooth function with semipositive `ddᶜ` on an open set is PSH there.**
This is `Hironaka.plurisubharmonicOn_coe_of_smoothDDC_eq_zero` with the equation
`ddᶜh = 0` relaxed to the diagonal inequality. -/
theorem plurisubharmonicOn_coe_of_smoothDDC_nonneg
    {W : Set (ComplexModel n)} {h : ComplexModel n → ℝ}
    (hW : IsOpen W) (hh : ContDiffOn ℝ ∞ h W)
    (hnn : ∀ z ∈ W, ∀ v : ComplexModel n, 0 ≤ smoothDDC h z ![v, Complex.I • v]) :
    PlurisubharmonicOn (fun z => (h z : EReal)) W := by
  intro x hx
  obtain ⟨g, hg, heq⟩ := exists_contDiff_eventuallyEq_of_contDiffOn hW hh hx
  have hmem : {y | h y = g y} ∩ W ∈ 𝓝 x := inter_mem heq (hW.mem_nhds hx)
  obtain ⟨V, hVsub, hV, hxV⟩ := mem_nhds_iff.mp hmem
  have hVW : V ⊆ W := fun y hy => (hVsub hy).2
  have heqV : EqOn h g V := fun y hy => (hVsub hy).1
  have hg2 : ContDiff ℝ 2 g := hg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hlevi : ∀ y ∈ V, ∀ v : ComplexModel n, 0 ≤ leviForm g y v := by
    intro y hy v
    have hloc : h =ᶠ[𝓝 y] g := by
      filter_upwards [hV.mem_nhds hy] with t ht
      exact heqV ht
    have hdiag := smoothDDC_complexDiagonal_eq_leviForm (z := y) hg2.contDiffAt v
    rw [← smoothDDC_congr hloc] at hdiag
    have hbase := hnn y (hVW hy) v
    rw [hdiag] at hbase
    have hpi := Real.pi_pos
    have hmul := mul_nonneg hbase hpi.le
    rwa [div_mul_cancel₀ _ hpi.ne'] at hmul
  have hpshg : PlurisubharmonicOn (fun y => (g y : EReal)) V :=
    plurisubharmonicOn_of_levi_nonneg hg2 hV hlevi
  apply (hpshg x hxV).congr
  filter_upwards [hV.mem_nhds hxV] with y hy
  rw [heqV hy]

/-! ### The relativised smooth theta-PSH criterion -/

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **The `On` half of the smooth theta-PSH criterion.**  If `θ + ddᶜu` is
semipositive at every chart point lying over the open set `Ω`, then the smooth `u`
is theta-PSH over `Ω`.  The local potential of `θ` is restricted to the part of
its domain over `Ω`. -/
theorem thetaPlurisubharmonicOn_smooth_of_semipositive
    (a : ClosedRealOneOneForm n M) {u : M → ℝ} (hu : ChartSmooth (n := n) u)
    {Ω : Set M} (hΩ : IsOpen Ω)
    (hdiag : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      e.val.symm z ∈ Ω → ∀ v : ComplexModel n,
        0 ≤ a.val.coeff e z ![v, Complex.I • v] +
          smoothDDC (fun y => u (e.val.symm y)) z ![v, Complex.I • v]) :
    ThetaPlurisubharmonicOn a.val (fun x => (u x : EReal)) Ω := by
  intro e z hz hzΩ
  obtain ⟨W, ρ, hzW, hρ⟩ :=
    LocalPotentials.closedRealOneOne_hasLocalPotentials a e z hz
  set W' : Set (ComplexModel n) := W ∩ (e.val.target ∩ e.val.symm ⁻¹' Ω) with hW'
  have hW'open : IsOpen W' := hρ.1.inter (e.val.isOpen_inter_preimage_symm hΩ)
  have hW'sub : W' ⊆ W := inter_subset_left
  have hzW' : z ∈ W' := ⟨hzW, hz, hzΩ⟩
  refine ⟨W', ρ, hzW', hρ.mono hW'open hW'sub, ?_⟩
  set f : ComplexModel n → ℝ := fun y => u (e.val.symm y) + ρ y with hf
  have huchart : ContDiffOn ℝ ∞ (fun y => u (e.val.symm y)) W' :=
    (hu e).mono fun y hy => hy.2.1
  have hρW' : ContDiffOn ℝ ∞ ρ W' := hρ.2.2.1.mono hW'sub
  have hfsm : ContDiffOn ℝ ∞ f W' := huchart.add hρW'
  have hfpsh : PlurisubharmonicOn (fun y => (f y : EReal)) W' := by
    refine plurisubharmonicOn_coe_of_smoothDDC_nonneg hW'open hfsm ?_
    intro y hy v
    rw [hf, smoothDDC_add hW'open huchart hρW' hy, hρ.2.2.2 (hW'sub hy)]
    have := hdiag e y hy.2.1 hy.2.2 v
    simpa only [ContinuousAlternatingMap.add_apply, add_comm] using this
  simpa only [hf, chartFunction, EReal.coe_add] using hfpsh

/-- The `IsThetaPshPotentialOn` package: a real-valued potential is nowhere
`-∞`, so the nondegeneracy clause is automatic. -/
theorem isThetaPshPotentialOn_smooth_of_semipositive
    (a : ClosedRealOneOneForm n M) {u : M → ℝ} (hu : ChartSmooth (n := n) u)
    {Ω : Set M} (hΩ : IsOpen Ω)
    (hdiag : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      e.val.symm z ∈ Ω → ∀ v : ComplexModel n,
        0 ≤ a.val.coeff e z ![v, Complex.I • v] +
          smoothDDC (fun y => u (e.val.symm y)) z ![v, Complex.I • v]) :
    IsThetaPshPotentialOn a.val (fun x => (u x : EReal)) Ω :=
  ⟨thetaPlurisubharmonicOn_smooth_of_semipositive a hu hΩ hdiag,
    fun _ _ _ _ hxU => ⟨_, hxU, EReal.coe_ne_bot _⟩⟩

/-! ### From strict positivity near a compact set to Kähler domination -/

theorem quad_zero (b : ComplexModel n [⋀^Fin 2]→L[ℝ] ℝ) : quad b 0 = 0 := by
  have := quad_smul b 0 0
  simpa using this

theorem quad_sub (a b : ComplexModel n [⋀^Fin 2]→L[ℝ] ℝ) (v : ComplexModel n) :
    quad (a - b) v = quad a v - quad b v := rfl

/-- Subtracting a small enough multiple of a fixed form keeps strict
positivity. -/
theorem exists_pos_isStrictlyPositive_sub_smul
    {a b : ComplexModel n [⋀^Fin 2]→L[ℝ] ℝ} (ha : IsStrictlyPositive a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c : ℝ, 0 ≤ c → c < δ → IsStrictlyPositive (a - c • b) := by
  obtain ⟨m, hm, hmb⟩ := exists_pos_forall_le_quad ha
  refine ⟨m / (‖b‖ + 1), by positivity, fun c hc hcd => ?_⟩
  refine isStrictlyPositive_of_opNorm_sub_lt hmb ?_
  have hnorm : ‖a - c • b - a‖ = c * ‖b‖ := by
    rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  rw [hnorm]
  have hb : (0 : ℝ) ≤ ‖b‖ := norm_nonneg b
  have h1 : c * (‖b‖ + 1) < m :=
    (lt_div_iff₀ (by positivity : (0:ℝ) < ‖b‖ + 1)).mp hcd
  nlinarith

/-- **Kähler domination from strict positivity near a compact set.**  If
`θ + ddᶜφ` is strictly positive at every point of an open `U` containing the
compact `K`, then a smaller open set still containing `K` carries a genuine
Kähler-form domination with the smooth potential `φ`. -/
theorem exists_pos_dominatesKahlerFormOn_of_forall_strictPosAt
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {φ : M → ℝ} (hφ : ChartSmooth (n := n) φ)
    {K : Set M} (hK : IsCompact K) {U : Set M} (hU : IsOpen U) (hKU : K ⊆ U)
    (hpos : ∀ y ∈ U, StrictPosAt (θ + ddcClosedForm φ hφ).val y) :
    ∃ U' : Set M, IsOpen U' ∧ K ⊆ U' ∧ U' ⊆ U ∧
      DominatesKahlerFormOn θ (fun x => (φ x : EReal)) U' := by
  classical
  set γ : ClosedRealOneOneForm n M := ddcClosedForm φ hφ with hγ
  set P : ℝ → ClosedRealOneOneForm n M :=
    fun c => (θ + γ) - c • omega.form with hP
  have hPcoeff : ∀ (c : ℝ) (e : ComplexChart n M) (z : ComplexModel n)
      (v : ComplexModel n),
      (P c).val.coeff e z ![v, Complex.I • v] =
        (θ + γ).val.coeff e z ![v, Complex.I • v]
          - c * omega.form.val.coeff e z ![v, Complex.I • v] := by
    intro c e z v
    rw [hP]
    show quad (((θ + γ) - c • omega.form).val.coeff e z) v = _
    rw [BlowupBigPullback.coeff_sub, ClosedRealOneOneForm.coeff_smul, quad_sub,
      quad_smul_form]
    rfl
  -- decreasing the constant preserves strict positivity
  have hmono : ∀ (c c' : ℝ), c' ≤ c → ∀ y : M, StrictPosAt (P c).val y →
      StrictPosAt (P c').val y := by
    intro c c' hcc y hy v hv
    have hsemi := omega.isSemipositive (complexChartAt (n := n) y)
      ((complexChartAt (n := n) y).val y)
      ((complexChartAt (n := n) y).val.map_source (mem_complexChartAt_source y)) v
    have hbase : (P c).val.coeff (complexChartAt (n := n) y)
        ((complexChartAt (n := n) y).val y) ![v, Complex.I • v] > 0 := hy v hv
    show (P c').val.coeff (complexChartAt (n := n) y)
      ((complexChartAt (n := n) y).val y) ![v, Complex.I • v] > 0
    rw [hPcoeff] at hbase ⊢
    nlinarith
  -- the cover of `K` by the sets where a fixed small constant works
  set N : ℕ → Set M :=
    fun j => U ∩ {y : M | StrictPosAt (P (1 / ((j : ℝ) + 1))).val y} with hN
  have hNopen : ∀ j, IsOpen (N j) := fun j =>
    hU.inter (isOpen_setOf_strictPosAt _)
  have hcover : K ⊆ ⋃ j : ℕ, N j := by
    intro y hy
    obtain ⟨δ, hδ, hδpos⟩ :=
      exists_pos_isStrictlyPositive_sub_smul
        (b := omega.form.val.coeff (complexChartAt (n := n) y)
          ((complexChartAt (n := n) y).val y))
        (hpos y (hKU hy))
    obtain ⟨j, hj⟩ := exists_nat_gt (1 / δ)
    have hjpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hlt : 1 / ((j : ℝ) + 1) < δ := by
      rw [div_lt_iff₀ hjpos]
      have h1 : 1 / δ < (j : ℝ) + 1 := by linarith
      rw [div_lt_iff₀ hδ] at h1
      linarith
    refine mem_iUnion.2 ⟨j, hKU hy, ?_⟩
    intro v hv
    show (P (1 / ((j : ℝ) + 1))).val.coeff (complexChartAt (n := n) y)
      ((complexChartAt (n := n) y).val y) ![v, Complex.I • v] > 0
    rw [hPcoeff]
    have hstrict := hδpos (1 / ((j : ℝ) + 1)) (by positivity) hlt v hv
    have hshow : ((θ + γ).val.coeff (complexChartAt (n := n) y)
          ((complexChartAt (n := n) y).val y)
        - (1 / ((j : ℝ) + 1)) • omega.form.val.coeff (complexChartAt (n := n) y)
          ((complexChartAt (n := n) y).val y)) ![v, Complex.I • v]
        = (θ + γ).val.coeff (complexChartAt (n := n) y)
            ((complexChartAt (n := n) y).val y) ![v, Complex.I • v]
          - 1 / ((j : ℝ) + 1) * omega.form.val.coeff (complexChartAt (n := n) y)
            ((complexChartAt (n := n) y).val y) ![v, Complex.I • v] := by
      show quad ((θ + γ).val.coeff (complexChartAt (n := n) y)
          ((complexChartAt (n := n) y).val y)
        - (1 / ((j : ℝ) + 1)) • omega.form.val.coeff (complexChartAt (n := n) y)
          ((complexChartAt (n := n) y).val y)) v = _
      rw [quad_sub, quad_smul_form]
      rfl
    have hstrict2 : 0 < ((θ + γ).val.coeff (complexChartAt (n := n) y)
        ((complexChartAt (n := n) y).val y)
        - (1 / ((j : ℝ) + 1)) • omega.form.val.coeff (complexChartAt (n := n) y)
          ((complexChartAt (n := n) y).val y)) ![v, Complex.I • v] := hstrict
    rw [hshow] at hstrict2
    exact hstrict2
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover N hNopen hcover
  set ε : ℝ := 1 / (((t.sup id : ℕ) : ℝ) + 1) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hKsub : K ⊆ U ∩ {y : M | StrictPosAt (P ε).val y} := by
    intro y hy
    obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.mp (ht hy)
    refine ⟨hyj.1, ?_⟩
    have hjs : (j : ℕ) ≤ t.sup id := Finset.le_sup (f := id) hj
    have hle : ε ≤ 1 / ((j : ℝ) + 1) := by
      rw [hε]
      apply one_div_le_one_div_of_le (by positivity)
      have : (j : ℝ) ≤ ((t.sup id : ℕ) : ℝ) := Nat.cast_le.mpr hjs
      linarith
    exact hmono _ _ hle y hyj.2
  refine ⟨U ∩ {y : M | StrictPosAt (P ε).val y},
    hU.inter (isOpen_setOf_strictPosAt _), hKsub, inter_subset_left, ?_⟩
  refine ⟨Hironaka.PositiveClasses.KahlerBackground.smul hεpos omega, ?_⟩
  refine isThetaPshPotentialOn_smooth_of_semipositive _ hφ
    (hU.inter (isOpen_setOf_strictPosAt _)) ?_
  intro e z hz hzΩ v
  have hstrict : IsStrictlyPositive ((P ε).val.coeff e z) := by
    have h := hzΩ.2
    have hmem : e.val.symm z ∈ e.val.source := e.val.map_target hz
    have hb := h.isStrictlyPositive e hmem
    rwa [e.val.right_inv hz] at hb
  have hq : 0 ≤ (P ε).val.coeff e z ![v, Complex.I • v] := by
    rcases eq_or_ne v 0 with rfl | hv
    · exact le_of_eq (quad_zero ((P ε).val.coeff e z)).symm
    · exact (hstrict v hv).le
  rw [hPcoeff] at hq
  have hγcoeff : γ.val.coeff e z = smoothDDC (fun y => φ (e.val.symm y)) z := rfl
  have hsum : (θ + γ).val.coeff e z ![v, Complex.I • v]
      = θ.val.coeff e z ![v, Complex.I • v]
        + smoothDDC (fun y => φ (e.val.symm y)) z ![v, Complex.I • v] := by
    rw [ClosedRealOneOneForm.coeff_add, hγcoeff]; rfl
  rw [hsum] at hq
  have hgoal : (θ - (Hironaka.PositiveClasses.KahlerBackground.smul hεpos omega).form).val.coeff e z
      ![v, Complex.I • v]
      = θ.val.coeff e z ![v, Complex.I • v]
        - ε * omega.form.val.coeff e z ![v, Complex.I • v] := by
    rw [BlowupBigPullback.coeff_sub,
      Hironaka.PositiveClasses.KahlerBackground.smul_form,
      ClosedRealOneOneForm.coeff_smul]
    show quad (θ.val.coeff e z - ε • omega.form.val.coeff e z) v = _
    rw [quad_sub, quad_smul_form]
    rfl
  rw [hgoal]
  linarith

/-! ### Step 6 of `prop:principalization`, assembled -/

/-- Scaling a chart-smooth function scales its `ddᶜ`. -/
theorem ddcClosedForm_const_mul_coeff {ψ : M → ℝ} (hψ : ChartSmooth (n := n) ψ)
    (B : ℝ) (hBψ : ChartSmooth (n := n) fun x => B * ψ x) (e : ComplexChart n M)
    {z : ComplexModel n} (hz : z ∈ e.val.target) (v : ComplexModel n) :
    (ddcClosedForm (fun x => B * ψ x) hBψ).val.coeff e z ![v, Complex.I • v]
      = B * (ddcClosedForm ψ hψ).val.coeff e z ![v, Complex.I • v] := by
  show smoothDDC (fun w => B * ψ (e.val.symm w)) z ![v, Complex.I • v]
    = B * smoothDDC (fun w => ψ (e.val.symm w)) z ![v, Complex.I • v]
  rw [show (fun w => B * ψ (e.val.symm w)) = fun w => B • ψ (e.val.symm w) from rfl,
    smoothDDC_smul e.val.open_target (hψ e) B hz]
  rfl

/-- **The usable entry point: Kähler domination from the Levi data of a tube.**
No flattening occurs in the hypotheses — only the Levi form of `r` at the points
of the compact `W`, in the preferred chart there.  This is what
`Hironaka.GlobalTubeFunction.exists_chartSmooth_tube` hands back directly, so a
consumer needs no independence statement about tangent spaces (I-0356). -/
theorem exists_pos_dominatesKahlerFormOn_of_leviNull [CompactSpace M]
    (omega : KahlerBackground n M) {W : Set M} (hW : IsCompact W)
    (β : ClosedRealOneOneForm n M) {r : M → ℝ} (hr : ChartSmooth (n := n) r)
    (hsemi : ∀ w ∈ W, ∀ v : ComplexModel n,
      0 ≤ leviForm (fun z => r ((complexChartAt (n := n) w).val.symm z))
        ((complexChartAt (n := n) w).val w) v)
    (hposβ : ∀ w ∈ W, ∀ v : ComplexModel n, v ≠ 0 →
      leviForm (fun z => r ((complexChartAt (n := n) w).val.symm z))
        ((complexChartAt (n := n) w).val w) v = 0 →
      0 < quad (β.val.coeff (complexChartAt (n := n) w)
        ((complexChartAt (n := n) w).val w)) v) :
    ∃ B : ℝ, 0 < B ∧ ∃ U : Set M, IsOpen U ∧ W ⊆ U ∧
      DominatesKahlerFormOn β (fun x => ((B * r x : ℝ) : EReal)) U := by
  obtain ⟨B, hB, U₀, hU₀, hWU₀, hstrict⟩ :=
    ManifoldTubePositivity.exists_pos_forall_strictPosAt_add_smul_ddc hW β hr
      hsemi hposβ
  have hBr : ChartSmooth (n := n) fun x => B * r x := fun e => (hr e).const_smul B
  have hsame : ∀ y ∈ U₀, StrictPosAt (β + ddcClosedForm (fun x => B * r x) hBr).val y := by
    intro y hy v hv
    have hbase := hstrict y hy v hv
    have hmem : (complexChartAt (n := n) y).val y ∈ (complexChartAt (n := n) y).val.target :=
      (complexChartAt (n := n) y).val.map_source (mem_complexChartAt_source y)
    have hb : 0 < (β + B • ddcClosedForm r hr).val.coeff (complexChartAt (n := n) y)
        ((complexChartAt (n := n) y).val y) ![v, Complex.I • v] := hbase
    rw [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
      ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply] at hb
    show 0 < (β + ddcClosedForm (fun x => B * r x) hBr).val.coeff
      (complexChartAt (n := n) y) ((complexChartAt (n := n) y).val y) ![v, Complex.I • v]
    rw [ClosedRealOneOneForm.coeff_add, ContinuousAlternatingMap.add_apply,
      ddcClosedForm_const_mul_coeff hr B hBr _ hmem v]
    simpa using hb
  obtain ⟨U, hUopen, hWU, hUsub, hdom⟩ :=
    exists_pos_dominatesKahlerFormOn_of_forall_strictPosAt omega β hBr hW hU₀ hWU₀ hsame
  exact ⟨B, hB, U, hUopen, hWU, hdom⟩

/-- **Step 6 of `prop:principalization`, assembled.**  On a compact Kähler
manifold, let `W` be a closed set all of whose points are regular of dimension
`k`, and let `β` be a closed real `(1,1)`-form strictly positive along the tangent
directions of `W` (through any nondegenerate holomorphic flattening).  Then there
are the tube `r ≥ 0` vanishing on `W`, a constant `B > 0` and an open `U ⊇ W` on
which `β + ddᶜ(B r)` genuinely dominates a Kähler form — Copy-4's

> `Ω_U := θ_Y - Θ_D - ½δ₀ π^*ω + ddᶜ(f̃ + B r_W²) > 0` … *in particular `Ω_U`
> dominates a Kähler form on `U`*.

Here `β` carries the manuscript's `θ_Y - Θ_D - ½δ₀ π^*ω + ddᶜ f̃`; the smooth
extension `f̃` is absorbed into `β` because it is smooth, so nothing is lost and
the statement is about the tube alone. -/
theorem exists_tube_dominatesKahlerFormOn [CompactSpace M]
    (omega : KahlerBackground n M) {W : Set M} {k : ℕ}
    (hWclosed : IsClosed W) (hWreg : ∀ x ∈ W, RegularAtDim (n := n) W x k)
    (β : ClosedRealOneOneForm n M)
    (hβ : ∀ (f : ComplexChart n M) (w : M), w ∈ W → w ∈ f.val.source →
      ∀ (F : ComplexModel n → ComplexModel n) (D : Set (ComplexModel n)),
        IsOpen D → f.val w ∈ D → D ⊆ f.val.target → ContDiffOn ℂ ∞ F D →
        Function.Injective (fderiv ℝ F (f.val w)) →
        (∀ z ∈ D, (f.val.symm z ∈ W ↔ F z ∈ complexCoordinatePlane n k)) →
        ∀ v : ComplexModel n, v ≠ 0 →
          fderiv ℝ F (f.val w) v ∈ complexCoordinatePlane n k →
          0 < quad (β.val.coeff f (f.val w)) v) :
    ∃ r : M → ℝ, ChartSmooth (n := n) r ∧ (∀ y, 0 ≤ r y) ∧ (∀ w ∈ W, r w = 0) ∧
      ∃ B : ℝ, 0 < B ∧ ∃ U : Set M, IsOpen U ∧ W ⊆ U ∧
        DominatesKahlerFormOn β (fun x => ((B * r x : ℝ) : EReal)) U := by
  obtain ⟨r, hr, hrnn, hrW, hlevi⟩ :=
    GlobalTubeFunction.exists_chartSmooth_tube hWclosed hWreg
  refine ⟨r, hr, hrnn, hrW, ?_⟩
  refine exists_pos_dominatesKahlerFormOn_of_leviNull omega hWclosed.isCompact β hr
    (fun w hw v => (hlevi (complexChartAt (n := n) w) w hw
      (mem_complexChartAt_source w)).1 v) (fun w hw v hv hnull => ?_)
  obtain ⟨-, F, D, hDopen, hzD, hDsub, hFholo, hFinj, hFflat, hker⟩ :=
    hlevi (complexChartAt (n := n) w) w hw (mem_complexChartAt_source w)
  exact hβ (complexChartAt (n := n) w) w hw (mem_complexChartAt_source w)
    F D hDopen hzD hDsub hFholo hFinj hFflat v hv (hker v hnull)

end

end Hironaka.SmoothPotentialDomination
