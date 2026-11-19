import Hironaka.Analytic.PshHypersurfaceRemovableIntegration
import Hironaka.Analytic.PotentialTheory.AnalyticSingularities
import Hironaka.Analytic.PshSupremumRegularization
import Hironaka.Analytic.PshDiscLocalGlobal
import Hironaka.Analytic.UscRegularizationLocality
import Hironaka.Analytic.RegularPatchNeighborhood
import Hironaka.Analytic.PotentialTheory.PlurisubharmonicLimits
import Hironaka.Analytic.PotentialTheory.LocalPotentials

set_option autoImplicit false

/-!
# Removable singularities of (quasi-)PSH functions across analytic sets

Source: Demailly, *Complex Analytic and Differential Geometry*, Chapter I, Theorems (5.23)
and (5.24) (`demailly-cadg:I.5.24`): a plurisubharmonic function on `Ω \ A`, `A` a closed
pluripolar set, which is locally bounded above near `A`, extends to a plurisubharmonic function
on `Ω`, namely its upper semicontinuous regularization.  For a complex analytic set `A`, locally
`A = {g₁ = ⋯ = g_N = 0}`, and `w = log ∑ |gᵢ|²` is a plurisubharmonic function which is `-∞`
exactly on `A` (Demailly's (5.22)).

## The proof (Demailly's argument for (5.23), in the plurisubharmonic setting)

Near a point `x₀`, bound `w < c` on a ball `Ω₀` and put, for `ε_k = 1/(k+1)`,
`v_k = ψ + ε_k (w - c)` off `A` and `v_k = -∞` on `A`.

* `v_k` is PSH on `Ω₀`: off `A` it is a sum of PSH functions; at a point of `A` it tends to
  `-∞` (`ψ` is bounded above there and `w → -∞`), so each truncation `max(v_k, -M)` is the
  constant `-M` near `A` and is PSH germwise on `Ω₀`; the local-to-global disc theorem
  (`PlurisubharmonicOn.discPshOn`) makes it disc-PSH on all of `Ω₀`, and the decreasing limit
  over `M` (`DiscPshOn.iInf_of_antitone`) is `v_k`.
* `v_k ≤ ψ` off `A`, so the family is locally uniformly bounded above, and its regularized
  supremum is PSH (`Hironaka.plurisubharmonicOn_uscRegularization_sSup`, the Choquet--Lelong
  envelope theorem).
* The supremum is exactly `ψ` off `A` (there `w` is finite and `ε_k (w - c) ↑ 0`) and `-∞` on
  `A`, so its regularization is the prescribed extension `(ψ on Ω \ A, -∞ on A)^*`.

No stratification of `A`, no Grauert--Remmert input and no measure theory is used.

## Main results

* `plurisubharmonicOn_extension_of_zeroLocus` — the local theorem in a coordinate domain.
* `thetaPshLocalClosure_of_isComplexAnalyticSubset` — its `θ`-PSH manifold form, in every chart.
* `analyticRemovableThetaPsh` — the proposition `PshAnalyticSetExtension.AnalyticRemovableThetaPsh`,
  for every form with smooth local potentials, and `analyticRemovableThetaPsh_of_closed` for every
  closed real `(1,1)`-form.  This discharges the named input
  `PshRemovableSingularity.demaillyCadgI524_analyticRemovableThetaPsh`.
-/

open Set Filter Metric
open scoped Topology

namespace Hironaka.PshAnalyticRemovable

open Hironaka PshCodimTwoExtension PshAnalyticSetExtension ThetaPshCodimTwoExtension
  PshExtensionEquivariance PshHypersurfaceRemovableIntegration

noncomputable section

/-! ### Two facts about extended reals -/

/-- Truncating from below at `-M` and letting `M → ∞` recovers the value. -/
theorem iInf_max_neg_nat (a : EReal) : ⨅ M : ℕ, max a (((-(M : ℝ) : ℝ)) : EReal) = a := by
  refine le_antisymm ?_ (le_iInf fun M => le_max_left _ _)
  induction a using EReal.rec with
  | bot =>
      refine le_of_eq ((EReal.eq_bot_iff_forall_lt _).mpr fun y => ?_)
      obtain ⟨M, hM⟩ := exists_nat_gt (-y)
      refine (iInf_le _ M).trans_lt ?_
      rw [max_eq_right bot_le]
      exact EReal.coe_lt_coe_iff.mpr (by linarith)
  | coe b =>
      obtain ⟨M, hM⟩ := exists_nat_ge (-b)
      refine (iInf_le _ M).trans ?_
      rw [max_eq_left (EReal.coe_le_coe_iff.mpr (by linarith))]
  | top => exact le_top

/-- The weights `ε_k = 1/(k+1)`. -/
def eps (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

theorem eps_pos (k : ℕ) : 0 < eps k := by
  unfold eps
  positivity

/-! ### The local theorem -/

variable {n : ℕ}

/-- **Removable singularities across a local analytic set** (Demailly, CADG I.5.23--5.24).  Let
`A ∩ Ω` be the common zero set of finitely many holomorphic functions on the open set `Ω`.  If
`ψ` is PSH on `Ω \ A` and locally bounded above near every point of `Ω` (off `A`), then the upper
regularization of (`ψ` off `A`, `-∞` on `A`) is PSH on `Ω`. -/
theorem plurisubharmonicOn_extension_of_zeroLocus {Ω A : Set (ComplexModel n)} (hΩ : IsOpen Ω)
    {ψ : ComplexModel n → EReal} (hψ : PlurisubharmonicOn ψ (Ω \ A))
    (hbound : PshHypersurfaceRemovable.LocallyBoundedAboveOff A Ω ψ)
    {N : ℕ} {g : Fin N → ComplexModel n → ℂ} (hg : ∀ i, DifferentiableOn ℂ (g i) Ω)
    (hgA : ∀ y ∈ Ω, y ∈ A ↔ ∀ i, g i y = 0) :
    PlurisubharmonicOn (extension A ψ) Ω := by
  classical
  set w : ComplexModel n → EReal := generatorLog g with hw
  -- `w = log ∑ |gᵢ|²` and its positive multiples are PSH on `Ω`
  have hwc : ∀ {c : ℝ}, 0 < c → PlurisubharmonicOn (fun y => (c : EReal) * w y) Ω :=
    fun hc y hy => Hironaka.plurisubharmonicAt_scaled_generatorLog ⟨Ω, hΩ, hy, hg⟩ hc
  have hw1 : PlurisubharmonicOn w Ω := by
    have h := hwc (c := 1) one_pos
    simpa only [EReal.coe_one, one_mul] using h
  have hwbot : ∀ y ∈ Ω, (w y = ⊥ ↔ y ∈ A) := fun y hy => by
    rw [hw, generatorLog_eq_bot_iff, hgA y hy]
  -- `Ω \ A` is open
  have hΩA : IsOpen (Ω \ A) := by
    have hset : Ω \ A = ⋃ i, Ω ∩ g i ⁻¹' {0}ᶜ := by
      ext y
      simp only [Set.mem_sdiff, mem_iUnion, mem_inter_iff, mem_preimage, mem_compl_iff,
        mem_singleton_iff]
      constructor
      · rintro ⟨hyΩ, hyA⟩
        have h : ¬ ∀ i, g i y = 0 := fun h => hyA ((hgA y hyΩ).mpr h)
        obtain ⟨i, hi⟩ := not_forall.mp h
        exact ⟨i, hyΩ, hi⟩
      · rintro ⟨i, hyΩ, hi⟩
        exact ⟨hyΩ, fun hyA => hi ((hgA y hyΩ).mp hyA i)⟩
    rw [hset]
    exact isOpen_iUnion fun i =>
      (hg i).continuousOn.isOpen_inter_preimage hΩ isOpen_compl_singleton
  intro x₀ hx₀
  -- a ball `Ω₀` around `x₀` on which `w < c`
  obtain ⟨c, hc⟩ : ∃ c : ℝ, w x₀ < c := by
    obtain ⟨c, hc, -⟩ :=
      EReal.lt_iff_exists_real_btwn.mp (lt_top_iff_ne_top.mpr (generatorLog_ne_top g x₀))
    exact ⟨c, hc⟩
  have hnhd : {y | y ∈ Ω ∧ w y < c} ∈ 𝓝 x₀ :=
    inter_mem (hΩ.mem_nhds hx₀) ((hw1 x₀ hx₀).upperSemicontinuousAt c hc)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnhd
  set Ω₀ := ball x₀ r with hΩ₀
  have hΩ₀open : IsOpen Ω₀ := isOpen_ball
  have hΩ₀Ω : Ω₀ ⊆ Ω := fun y hy => (hball hy).1
  have hwc₀ : ∀ y ∈ Ω₀, w y < c := fun y hy => (hball hy).2
  -- the correction terms `ε_k (w - c) ≤ 0` on `Ω₀`
  set t : ℕ → ComplexModel n → EReal := fun k y =>
    ((eps k : ℝ) : EReal) * w y + ((-(eps k * c) : ℝ) : EReal) with ht_def
  have ht : ∀ k, ∀ y ∈ Ω₀, t k y ≤ 0 := by
    intro k y hy
    have h1 : ((eps k : ℝ) : EReal) * w y ≤ ((eps k : ℝ) : EReal) * (c : EReal) :=
      mul_le_mul_of_nonneg_left (hwc₀ y hy).le (EReal.coe_nonneg.mpr (eps_pos k).le)
    calc t k y ≤ ((eps k : ℝ) : EReal) * (c : EReal) + ((-(eps k * c) : ℝ) : EReal) :=
          add_le_add_left h1 _
      _ = 0 := by
        rw [← EReal.coe_mul, ← EReal.coe_add]
        simp
  -- the family `v_k`
  set v : ℕ → ComplexModel n → EReal := fun k y => if y ∈ A then ⊥ else ψ y + t k y
    with hv_def
  have hvoff : ∀ k, PlurisubharmonicOn (fun y => ψ y + t k y) (Ω \ A) := fun k =>
    hψ.add (((hwc (eps_pos k)).mono sdiff_subset).add
      (fun y _ => plurisubharmonicAt_const _ (EReal.coe_ne_top _) y))
  have hvAt_off : ∀ k, ∀ y ∈ Ω \ A, PlurisubharmonicAt (v k) y := by
    intro k y hy
    refine (hvoff k y hy).congr ?_
    filter_upwards [hΩA.mem_nhds hy] with z hz
    simp only [hv_def, if_neg hz.2]
  -- at a point of `A`, `v_k → -∞`
  have hvbot : ∀ k, ∀ a ∈ A, a ∈ Ω → ∀ M : ℝ, ∀ᶠ y in 𝓝 a, v k y < M := by
    intro k a haA haΩ M
    obtain ⟨U, hU, C, hC⟩ := hbound a haΩ
    have hwa : w a = ⊥ := (hwbot a haΩ).mpr haA
    have he := eps_pos k
    set m : ℝ := (M - C) / eps k + c - 1 with hm
    have hwm : ∀ᶠ y in 𝓝 a, w y < m :=
      (hw1 a haΩ).upperSemicontinuousAt m (by
        show w a < (m : EReal)
        rw [hwa]
        exact EReal.bot_lt_coe m)
    filter_upwards [hU, hwm] with y hyU hym
    by_cases hyA : y ∈ A
    · simp only [hv_def, if_pos hyA]
      exact EReal.bot_lt_coe M
    · simp only [hv_def, if_neg hyA]
      have h1 : ((eps k : ℝ) : EReal) * w y ≤ ((eps k : ℝ) : EReal) * (m : EReal) :=
        mul_le_mul_of_nonneg_left hym.le (EReal.coe_nonneg.mpr he.le)
      calc ψ y + t k y ≤ (C : EReal) +
            (((eps k : ℝ) : EReal) * (m : EReal) + ((-(eps k * c) : ℝ) : EReal)) :=
            add_le_add (hC y hyU hyA) (add_le_add_left h1 _)
        _ = ((C + (eps k * m + -(eps k * c)) : ℝ) : EReal) := by
            rw [← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_add]
        _ < M := by
            refine EReal.coe_lt_coe_iff.mpr ?_
            have hem : eps k * m = M - C + eps k * c - eps k := by
              rw [hm]
              field_simp
            linarith
  -- each `v_k` is PSH on `Ω₀`: truncate, go local-to-global, and take the decreasing limit
  have hvpsh : ∀ k, PlurisubharmonicOn (v k) Ω₀ := by
    intro k
    set f : ℕ → ComplexModel n → EReal := fun M y => max (v k y) (((-(M : ℝ) : ℝ)) : EReal)
      with hf_def
    have hf : ∀ M, PlurisubharmonicOn (f M) Ω₀ := by
      intro M y hy
      by_cases hyA : y ∈ A
      · refine (plurisubharmonicAt_const (((-(M : ℝ) : ℝ)) : EReal) (EReal.coe_ne_top _)
          y).congr ?_
        filter_upwards [hvbot k y hyA (hΩ₀Ω hy) (-(M : ℝ))] with z hz
        exact (max_eq_right hz.le).symm
      · exact (hvAt_off k y ⟨hΩ₀Ω hy, hyA⟩).max
          (plurisubharmonicAt_const _ (EReal.coe_ne_top _) y)
    have hanti : ∀ y ∈ Ω₀, Antitone (fun M => f M y) := by
      intro y _ M M' hMM'
      refine max_le_max le_rfl (EReal.coe_le_coe_iff.mpr ?_)
      have : (M : ℝ) ≤ M' := by exact_mod_cast hMM'
      linarith
    have hinf : DiscPshOn (fun y => ⨅ M, f M y) Ω₀ :=
      DiscPshOn.iInf_of_antitone (fun M => (hf M).discPshOn) hanti
    have heq : EqOn (fun y => ⨅ M, f M y) (v k) Ω₀ := fun y _ => iInf_max_neg_nat (v k y)
    exact (hinf.congr heq).plurisubharmonicOn hΩ₀open
  -- the family is locally uniformly bounded above
  have hvle : ∀ k, ∀ y ∈ Ω₀, y ∉ A → v k y ≤ ψ y := by
    intro k y hy hyA
    simp only [hv_def, if_neg hyA]
    exact add_le_of_nonpos_right (ht k y hy)
  have hunif : LocallyUniformlyBoundedAbove (range v) Ω₀ := by
    intro x hx
    obtain ⟨U, hU, C, hC⟩ := hbound x (hΩ₀Ω hx)
    refine ⟨U, mem_nhdsWithin_of_mem_nhds hU, C, ?_⟩
    rintro _ ⟨k, rfl⟩ y ⟨hyU, hyΩ₀⟩
    by_cases hyA : y ∈ A
    · simp only [hv_def, if_pos hyA]
      exact bot_le
    · exact (hvle k y hyΩ₀ hyA).trans (hC y hyU hyA)
  -- its regularized supremum is PSH
  have hφ : PlurisubharmonicOn (uscRegularization (sSup (range v))) Ω₀ :=
    Hironaka.plurisubharmonicOn_uscRegularization_sSup hΩ₀open (range_nonempty v)
      (by rintro _ ⟨k, rfl⟩; exact hvpsh k) hunif
  -- and the supremum is the prescribed raw function on `Ω₀`
  have hsup : ∀ y ∈ Ω₀, sSup (range v) y = (fun y => if y ∈ A then (⊥ : EReal) else ψ y) y := by
    intro y hy
    rw [sSup_range, iSup_apply]
    show (⨆ k, v k y) = if y ∈ A then ⊥ else ψ y
    by_cases hyA : y ∈ A
    · rw [if_pos hyA]
      simp only [hv_def, if_pos hyA, iSup_const]
    · rw [if_neg hyA]
      refine le_antisymm (iSup_le fun k => hvle k y hy hyA) ?_
      have hyΩ : y ∈ Ω := hΩ₀Ω hy
      by_contra hlt
      replace hlt := not_le.mp hlt
      obtain ⟨s, hs1, hs2⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
      -- `ψ y` and `w y` are finite reals
      have hψtop : ψ y ≠ ⊤ := (hψ y ⟨hyΩ, hyA⟩).ne_top
      have hψbot : ψ y ≠ ⊥ := ne_of_gt ((EReal.bot_lt_coe s).trans hs2)
      have hwtop : w y ≠ ⊤ := generatorLog_ne_top g y
      have hwbot' : w y ≠ ⊥ := fun h => hyA ((hwbot y hyΩ).mp h)
      set a := (ψ y).toReal with ha
      set b := (w y).toReal with hb
      have hψa : ψ y = (a : EReal) := (EReal.coe_toReal hψtop hψbot).symm
      have hwb : w y = (b : EReal) := (EReal.coe_toReal hwtop hwbot').symm
      have hbc : b < c := by
        have := hwc₀ y hy
        rw [hwb] at this
        exact EReal.coe_lt_coe_iff.mp this
      have hsa : s < a := by
        rw [hψa] at hs2
        exact EReal.coe_lt_coe_iff.mp hs2
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (div_pos (sub_pos.mpr hsa) (sub_pos.mpr hbc))
      have hvk : v k y = ((a + (eps k * b + -(eps k * c))) : ℝ) := by
        simp only [hv_def, ht_def, if_neg hyA, hψa, hwb]
        rw [← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_add]
      have hkey : s < a + (eps k * b + -(eps k * c)) := by
        have hek : eps k * (c - b) < a - s := by
          have h := (mul_lt_mul_of_pos_right hk (sub_pos.mpr hbc))
          rw [div_mul_cancel₀ _ (sub_pos.mpr hbc).ne'] at h
          simpa [eps] using h
        nlinarith
      have h1 : ((s : ℝ) : EReal) < v k y := by
        rw [hvk]
        exact EReal.coe_lt_coe_iff.mpr hkey
      exact lt_irrefl _ ((h1.trans_le (le_iSup (fun k => v k y) k)).trans hs1)
  -- conclusion at `x₀`
  have hEq : EqOn (uscRegularization (sSup (range v))) (extension A ψ) Ω₀ := by
    intro y hy
    rw [extension_eq_uscRegularization]
    refine uscRegularization_congr_of_eventuallyEq ?_
    filter_upwards [hΩ₀open.mem_nhds hy] with z hz
    exact hsup z hz
  refine (hφ x₀ (mem_ball_self hr)).congr ?_
  filter_upwards [hΩ₀open.mem_nhds (mem_ball_self hr)] with z hz
  exact hEq hz

/-! ### The `θ`-PSH form on a manifold -/

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **Removable singularities across an analytic set, `θ`-PSH form.**  If `θ` has smooth local
potentials, `A` is a complex analytic subset, `u` is `θ`-PSH off `A` and locally bounded above
there, then the upper regularization of (`u` off `A`, `-∞` on `A`) is `θ`-PSH near every point of
`A`, in every chart. -/
theorem thetaPshLocalClosure_of_isComplexAnalyticSubset {theta : SmoothRealForm n M 2}
    (htheta : HasSmoothLocalPotentials theta) {A : Set M} {u : M → EReal}
    (hA : IsComplexAnalyticSubset (n := n) A) (hoff : ThetaPshOff theta A u)
    (hbound : PshAnalyticSetExtension.LocallyBoundedAboveOff A u) :
    ThetaPshLocalClosure theta A u := by
  intro e z hz _
  obtain ⟨W, rho, hzW, hrho⟩ := htheta e z hz
  obtain ⟨P⟩ := hA (e.val.symm z)
  set c := complexChartAt (n := n) (e.val.symm z) with hc
  set T := chartTransition e c with hT
  have hTsrc : T.source = e.val.target ∩ e.val.symm ⁻¹' c.val.source := by
    simp [hT, chartTransition]
  have hTapp : ∀ y, T y = c.val (e.val.symm y) := fun y => rfl
  set S : Set (ComplexModel n) := e.val.symm ⁻¹' A with hS
  set Ω : Set (ComplexModel n) := W ∩ (T.source ∩ T ⁻¹' P.coordinateNeighborhood) with hΩ
  have hΩopen : IsOpen Ω :=
    hrho.1.inter (T.continuousOn.isOpen_inter_preimage T.open_source
      P.isOpen_coordinateNeighborhood)
  have hzT : z ∈ T.source := by
    rw [hTsrc]
    exact ⟨hz, mem_complexChartAt_source _⟩
  have hzΩ : z ∈ Ω := by
    refine ⟨hzW, hzT, ?_⟩
    change T z ∈ P.coordinateNeighborhood
    rw [hTapp]
    exact P.center_mem_coordinateNeighborhood
  -- the generators in the coordinates of `e`
  set g : Fin P.generatorCount → ComplexModel n → ℂ := fun i y => P.generator i (T y) with hg
  have hgd : ∀ i, DifferentiableOn ℂ (g i) Ω := fun i =>
    (P.generator_holomorphic i).comp
      ((RegularPatchNeighborhood.differentiableOn_chartTransition e c).mono
        (fun y hy => hy.2.1))
      (fun y hy => hy.2.2)
  have hgA : ∀ y ∈ Ω, y ∈ S ↔ ∀ i, g i y = 0 := by
    intro y hy
    have hysrc : e.val.symm y ∈ c.val.source := by
      have := hy.2.1
      rw [hTsrc] at this
      exact this.2
    have hyN : c.val (e.val.symm y) ∈ P.coordinateNeighborhood := hy.2.2
    exact P.zeroLocus hysrc hyN
  -- the branch with the fixed local potential
  set f : ComplexModel n → EReal := fun y => chartFunction u e y + (rho y : EReal) with hf
  have hpsh : PlurisubharmonicOn f (Ω \ S) :=
    (plurisubharmonicOn_chartFunction_add_fixedPotential_off hoff hrho).mono
      (Set.sdiff_subset_sdiff_left inter_subset_left)
  have hbd : PshHypersurfaceRemovable.LocallyBoundedAboveOff S Ω f := fun y hy =>
    locallyBoundedAboveOff_chartFunction_add_fixedPotential hbound hrho y hy.1
  have hext : PlurisubharmonicOn (extension S f) Ω :=
    plurisubharmonicOn_extension_of_zeroLocus hΩopen hpsh hbd hgd hgA
  refine ⟨Ω, rho, hzΩ, hrho.mono hΩopen inter_subset_left, ?_⟩
  intro y hy
  apply (hext y hy).congr
  filter_upwards [hΩopen.mem_nhds hy] with y hy'
  have hyt : y ∈ e.val.target := hrho.2.1 hy'.1
  have hrhoc : ContinuousAt rho y :=
    (hrho.2.2.1.continuousOn y hy'.1).continuousAt (hrho.1.mem_nhds hy'.1)
  have hchart := chartFunction_extensionAcross_eq_extension_preimage (K := A) (v := u) hyt
  have hadd := extension_add_coe_continuousAt_apply S (chartFunction u e) hrhoc
  change extension S (fun w => chartFunction u e w + (rho w : EReal)) y = _
  rw [hadd, ← hchart]

/-- **Demailly, CADG I.5.24, for analytic sets, as the project's proposition.**  For every form
with smooth local potentials, every set `A` and every `u`, `AnalyticRemovableThetaPsh θ A u`
holds.  Neither connectedness nor properness of `A` is needed for the local closure statement. -/
theorem analyticRemovableThetaPsh {theta : SmoothRealForm n M 2}
    (htheta : HasSmoothLocalPotentials theta) (A : Set M) (u : M → EReal) :
    AnalyticRemovableThetaPsh theta A u :=
  fun hA _ hoff hbound => thetaPshLocalClosure_of_isComplexAnalyticSubset htheta hA hoff hbound

/-- **For closed real `(1,1)`-forms no hypothesis is left**: they have smooth local potentials
(`LocalPotentials.closedRealOneOne_hasLocalPotentials`, the local `ddᶜ`-lemma), so
`AnalyticRemovableThetaPsh a A u` holds outright. -/
theorem analyticRemovableThetaPsh_of_closed (a : ClosedRealOneOneForm n M) (A : Set M)
    (u : M → EReal) : AnalyticRemovableThetaPsh a.val A u :=
  analyticRemovableThetaPsh (LocalPotentials.closedRealOneOne_hasLocalPotentials a) A u

end

end Hironaka.PshAnalyticRemovable
