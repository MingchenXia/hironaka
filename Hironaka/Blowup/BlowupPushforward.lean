import Hironaka.Blowup.BlowupNonKahlerLocus
import Hironaka.Analytic.ThetaPshPushforward
import Hironaka.Analytic.NonNefLocusKahlerIndependence
import Hironaka.Analytic.PotentialTheory.ManifoldPluripolar
import Hironaka.Analytic.ThetaPshComparison
import Hironaka.Analytic.KahlerCurrentPerturbation

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Pushing a Kähler current down a blowup

Let `π : Z → Y` be the blowup of a compact Kähler manifold `(Y, ω)` along `C`, `C₂ = π(Exc π)` its
exceptional centre with Blanchard weight `U`, factorization `U ∘ π = |h|² U'` and glued form `Θ`,
and `ε > 0` with `L = π^* ω + ε Θ` Kähler.  Let `S = θ_S + ddᶜ u ≥ K` be a Kähler current in
`π^* {θ}`, and write `π^* θ = θ_S + ddᶜ h_Z`.

`exists_pushforward`: there are `δ > 0` and a `(θ - δ ω)`-PSH potential `ψ` on `Y` with
`u - h_Z = ψ ∘ π + δ ε log (U ∘ π)` on all of `Z`.

* `K ≥ δ L`, so `w = u - h_Z` is `(π^* θ - δ L)`-PSH;
* off `Exc π`, `-δ ε log (U ∘ π)` is a local potential of `(π^* θ - δ L) - π^*(θ - δ ω) = -δ ε Θ`,
  so `(w - δ ε log (U ∘ π)) ∘ s` is `(θ - δ ω)`-PSH off `C₂` (`ThetaPshPushforward`), `s` a section;
* `ψ` is its extension across `C₂` (`ThetaPshCodimTwoExtension`);
* both sides of the identity are `(π^*(θ - δ ω) - δ ε Θ)`-PSH and agree off the pluripolar set
  `Exc π = {log (U ∘ π) = -∞}` (`ThetaPlurisubharmonic.le_of_quasiEverywhere_le`).
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BlowupPushforward

open Hironaka.PositiveClasses Hironaka.NonKahlerLocus Hironaka.BlowupSequences
  Hironaka.HolomorphicMaps BlanchardWeight FactorizedWeightForm FactorizedWeightPsh
  BlowupExceptionalCentre ThetaPshCodimTwoExtension

noncomputable section

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

section Forms

variable {k : ℕ} {V M : Type*}
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Pullback commutes with scalar multiplication, coefficientwise. -/
theorem pullback_smul_geometricallyEq {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (c : ℝ) (a : ClosedRealOneOneForm n M) :
    (ClosedRealOneOneForm.pullback hf (c • a)).val.GeometricallyEq
      (c • ClosedRealOneOneForm.pullback hf a).val := by
  intro e z hz
  let d := complexChartAt (n := n) (f (e.val.symm z))
  have hzd : z ∈ coordinateDomain f e d := ⟨hz, mem_complexChartAt_source _⟩
  rw [ClosedRealOneOneForm.coeff_smul, ClosedRealOneOneForm.pullback_val,
    ClosedRealOneOneForm.pullback_val, SmoothRealForm.pullback_coeff hf _ e d hzd,
    SmoothRealForm.pullback_coeff hf _ e d hzd, ClosedRealOneOneForm.coeff_smul]
  ext v
  simp

/-- Pullback commutes with subtraction (restated). -/
theorem pullback_sub_geometricallyEq' {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (a b : ClosedRealOneOneForm n M) :
    (ClosedRealOneOneForm.pullback hf (a - b)).val.GeometricallyEq
      (ClosedRealOneOneForm.pullback hf a - ClosedRealOneOneForm.pullback hf b).val :=
  BlowupBigPullback.pullback_sub_geometricallyEq hf a b

end Forms

/-- **`-c log U` is a local potential of `-c Θ` off the zeros of `U`.** -/
theorem isSmoothLocalPotential_neg_log {U : Z → ℝ} (hU : ChartSmooth (n := n) U)
    (F : WeightFactorization n U) (c : ℝ) {z : Z} (hz : 0 < U z) (e : ComplexChart n Z)
    (hze : z ∈ e.val.source) :
    ∃ W : Set (ComplexModel n), e.val z ∈ W ∧
      IsSmoothLocalPotential (-(c • F.closedForm)).val e W
        (fun ζ => -(c * Real.log (U (e.val.symm ζ)))) := by
  have hUc : Continuous U := KahlerCurrentMax.continuous_of_chartSmooth hU
  set W := e.val.target ∩ e.val.symm ⁻¹' (F.domain z ∩ {y | 0 < U y})
  have hW : IsOpen W :=
    e.val.isOpen_inter_preimage_symm ((F.isOpen_domain z).inter (isOpen_lt continuous_const hUc))
  have hzW : e.val z ∈ W := ⟨e.val.map_source hze, by
    rw [mem_preimage, e.val.left_inv hze]; exact ⟨F.mem_domain z, hz⟩⟩
  have hUs : ContDiffOn ℝ ∞ (fun ζ => U (e.val.symm ζ)) W := (hU e).mono inter_subset_left
  have hlog : ContDiffOn ℝ ∞ (fun ζ => Real.log (U (e.val.symm ζ))) W :=
    hUs.log fun ζ hζ => hζ.2.2.ne'
  refine ⟨W, hzW, hW, inter_subset_left, (hlog.const_smul c).neg, fun ζ hζ => ?_⟩
  have hsp : ContDiffOn ℝ ∞ (fun ζ => F.smoothPart z (e.val.symm ζ)) W :=
    (F.smooth z e).mono fun ζ' hζ' => ⟨hζ'.1, hζ'.2.1⟩
  have hgen : DifferentiableOn ℂ (fun ζ => F.gen z (e.val.symm ζ)) W := fun ζ' hζ' =>
    (differentiableAt_comp_chart_symm e hζ'.1 (F.gen_mdifferentiable z _ hζ'.2.1)).differentiableWithinAt
  have hlogeq := LogWeightFactorization.smoothDDC_log_eq_of_normSq_mul_eq hW hUs hsp
    (fun ζ' hζ' => hζ'.2.2) (fun ζ' hζ' => F.pos z _ hζ'.2.1)
    (h₁ := fun _ => 1) (differentiableOn_const 1) hgen
    (fun ζ' hζ' => by simp only [map_one, one_mul]; exact F.factor z _ hζ'.2.1)
    (fun ζ' hζ' => subset_closure ⟨hζ', one_ne_zero⟩) hζ
  change smoothDDC (fun ζ => -(c • Real.log (U (e.val.symm ζ)))) ζ = _
  rw [smoothDDC_neg hW (hlog.const_smul c) hζ, smoothDDC_smul hW hlog c hζ, hlogeq,
    ClosedRealOneOneForm.coeff_neg, ClosedRealOneOneForm.coeff_smul,
    (F.closedForm_coeff_eventuallyEq z e hζ.1 hζ.2.1).self_of_nhds]


/-- **Pushing a Kähler current down a blowup.** -/
theorem exists_pushforward [CompactSpace Y] (omega : KahlerBackground n Y)
    (θ : ClosedRealOneOneForm n Y) {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g)
    (D : BlanchardData n (exceptionalCentre n g))
    (F : WeightFactorization n (fun z => D.weight (g z)))
    {ε : ℝ} (hε : 0 < ε)
    (hK : (ClosedRealOneOneForm.pullback hg.contMDiff omega.form + ε • F.closedForm).val.IsKahler)
    (S : KahlerCurrent (RealBottChern.ofRepresentative
      (ClosedRealOneOneForm.pullback hg.contMDiff θ))) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ ψ : Y → EReal,
      IsThetaPshPotential (θ - δ • omega.form).val ψ ∧ ∃ hZ : Z → ℝ, ChartSmooth (n := n) hZ ∧
        ∀ z, S.potential z - (hZ z : EReal) =
          ψ (g z) + ((δ * ε : ℝ) : EReal) *
            logWeight (fun z => D.weight (g z)) z := by
  classical
  have := BlowupCompact.compactSpace_of_isBlowupAlong hg
  have hC₂ : IsClosed (exceptionalCentre n g) := isClosed_exceptionalCentre hg
  have hC₂C : (exceptionalCentre n g) ⊆ C := exceptionalCentre_subset hg
  have hE : ∀ z, g z ∉ (exceptionalCentre n g) → z ∉ exceptionalLocus n g := fun z h hE => h ⟨z, hE, rfl⟩
  -- a section of `g`
  have hsurj := StrictTransformComposition.surjective_of_isBlowupAlong hg
  set sec : Y → Z := fun y => Classical.choose (hsurj y)
  have hgs : ∀ y, g (sec y) = y := fun y => Classical.choose_spec (hsurj y)
  have hsg : ∀ z, g z ∉ (exceptionalCentre n g) → sec (g z) = z := fun z hz =>
    ExceptionalFibres.eq_of_apply_eq_of_not_mem_exceptionalLocus hg (hE z hz) (hgs (g z))
  -- `K ≥ δ L`
  set L : KahlerBackground n Z := ⟨_, hK⟩
  obtain ⟨δ, hδ, K', hK'⟩ :=
    NonNefLocusKahlerIndependence.exists_pos_kahlerBackground_eq_smul_sub_smul S.lowerBound L
      one_pos
  obtain ⟨hZ, hhZ, heqZ⟩ := (RealBottChern.ofRepresentative_eq_iff _ _).mp S.represents
  set w : Z → EReal := fun z => S.potential z - (hZ z : EReal)
  have hw₀ : IsThetaPshPotential ((ClosedRealOneOneForm.pullback hg.contMDiff θ) - S.lowerBound.form).val w := by
    refine thetaPshPotential_sub_smooth hhZ (fun e z hz => ?_) S.strictlyPsh
    rw [BlowupBigPullback.coeff_sub, BlowupBigPullback.coeff_sub, heqZ e z hz]
    abel
  have hw : ThetaPlurisubharmonic ((ClosedRealOneOneForm.pullback hg.contMDiff θ) - δ • L.form).val w := by
    have h := Hironaka.LocalPotentials.thetaPlurisubharmonic_add_of_semipositive hw₀.1
      K'.isSemipositive
    have hform : (ClosedRealOneOneForm.pullback hg.contMDiff θ) - S.lowerBound.form + K'.form = (ClosedRealOneOneForm.pullback hg.contMDiff θ) - δ • L.form := by
      rw [hK', one_smul]; abel
    rwa [hform] at h
  -- the forms
  have hgeom₁ : (((ClosedRealOneOneForm.pullback hg.contMDiff θ) - δ • L.form) - ClosedRealOneOneForm.pullback hg.contMDiff (θ - δ • omega.form)).val.GeometricallyEq
      (-((δ * ε) • F.closedForm)).val := by
    intro e z hz
    have h1 := pullback_sub_geometricallyEq' hg.contMDiff θ (δ • omega.form) e hz
    have h2 := pullback_smul_geometricallyEq hg.contMDiff δ omega.form e hz
    simp only [BlowupBigPullback.coeff_sub, ClosedRealOneOneForm.coeff_smul,
      ClosedRealOneOneForm.coeff_neg] at h1 h2 ⊢
    rw [h1, h2]
    show (ClosedRealOneOneForm.pullback hg.contMDiff θ).val.coeff e z - δ • ((ClosedRealOneOneForm.pullback hg.contMDiff omega.form).val.coeff e z +
      ε • F.closedForm.val.coeff e z) - ((ClosedRealOneOneForm.pullback hg.contMDiff θ).val.coeff e z - δ • (ClosedRealOneOneForm.pullback hg.contMDiff
        omega.form).val.coeff e z) = -((δ * ε) • F.closedForm.val.coeff e z)
    rw [smul_add, mul_smul]; abel
  have hgeom₂ : ((ClosedRealOneOneForm.pullback hg.contMDiff θ) - δ • L.form).val.GeometricallyEq
      (ClosedRealOneOneForm.pullback hg.contMDiff (θ - δ • omega.form) + -((δ * ε) • F.closedForm)).val := by
    intro e z hz
    have h := hgeom₁ e hz
    simp only [BlowupBigPullback.coeff_sub, ClosedRealOneOneForm.coeff_add] at h ⊢
    rw [← h]; abel
  -- the pushed-forward function off `(exceptionalCentre n g)`
  have hUs : ChartSmooth (n := n) fun z => D.weight (g z) := fun e =>
    BlanchardForm.contDiffOn_chartSmooth_comp hg.contMDiff D.chartSmooth_weight e
  set r : Z → ℝ := fun z => -((δ * ε) * Real.log (D.weight (g z)))
  have hr : ∀ z, g z ∉ (exceptionalCentre n g) → ∀ eZ : ComplexChart n Z, z ∈ eZ.val.source →
      ∃ W : Set (ComplexModel n), eZ.val z ∈ W ∧
        IsSmoothLocalPotential (((ClosedRealOneOneForm.pullback hg.contMDiff θ) - δ • L.form) - ClosedRealOneOneForm.pullback hg.contMDiff (θ - δ • omega.form)).val eZ W
          (fun ζ => r (eZ.val.symm ζ)) := fun z hz eZ hze => by
    obtain ⟨W, hzW, hpot⟩ := isSmoothLocalPotential_neg_log hUs F (δ * ε)
      (D.weight_pos_of_notMem hz) eZ hze
    exact ⟨W, hzW, (hgeom₁.localPotential_iff eZ W _).mpr hpot⟩
  set v : Y → EReal := fun y => w (sec y) + (r (sec y) : EReal)
  have hv : ThetaPshOff (θ - δ • omega.form).val (exceptionalCentre n g) v :=
    ThetaPshPushforward.thetaPshOff_comp_section hg.contMDiff hC₂ hE hsg (fun y _ => hgs y) hw hr
  have hflat₂ : HasCodimTwoFlattenings (n := n) (exceptionalCentre n g) := fun p hp => by
    obtain ⟨k, hk, Φ, hsrc, -, hflat, -⟩ := exists_flat_exceptionalCentre hg hp
    exact ⟨k, hk, Φ, hsrc, fun y hy hyC => (hflat hy.1 hy.2).mp (hC₂C hyC)⟩
  set ψ := extensionAcross (exceptionalCentre n g) v
  have hψ : ThetaPlurisubharmonic (θ - δ • omega.form).val ψ :=
    thetaPlurisubharmonic_extensionAcross hC₂ hflat₂
      (Hironaka.LocalPotentials.closedRealOneOne_hasLocalPotentials (θ - δ • omega.form)) hv
  have hψv : ∀ y ∉ (exceptionalCentre n g), ψ y = v y := fun y hy => extensionAcross_eq_of_notMem hC₂ hv hy
  -- the identity off the exceptional locus
  have hoff : ∀ z, g z ∉ (exceptionalCentre n g) → w z = ψ (g z) + ((δ * ε : ℝ) : EReal) * logWeight (fun z => D.weight (g z)) z := fun z hz => by
    have hpos : 0 < D.weight (g z) := D.weight_pos_of_notMem hz
    rw [hψv _ hz, logWeight_of_pos (U := fun z => D.weight (g z)) hpos]
    simp only [v, hsg z hz, r]
    rw [add_assoc, ← EReal.coe_mul, ← EReal.coe_add]
    simp
  -- comparison on all of `Z`
  set G : Z → EReal := fun z => ψ (g z) + ((δ * ε : ℝ) : EReal) * logWeight (fun z => D.weight (g z)) z
  have hG : ThetaPlurisubharmonic
      (ClosedRealOneOneForm.pullback hg.contMDiff (θ - δ • omega.form) + -((δ * ε) • F.closedForm)).val G :=
    Hironaka.LocalPotentials.thetaPlurisubharmonic_add
      (GlobalPotentialPullback.thetaPlurisubharmonic_comp hg.contMDiff hψ)
      (thetaPlurisubharmonic_logWeight F (mul_pos hδ hε))
  have hw' : ThetaPlurisubharmonic
      (ClosedRealOneOneForm.pullback hg.contMDiff (θ - δ • omega.form) + -((δ * ε) • F.closedForm)).val w :=
    BlowupBigPullback.thetaPlurisubharmonic_of_geometricallyEq hgeom₂ hw
  have hlogpsh : IsGlobalQuasiPshPotential (n := n) (logWeight (fun z => D.weight (g z))) := by
    refine ⟨?_, fun x O hO hxO => ?_⟩
    · have h := (thetaPlurisubharmonic_logWeight F one_pos).quasiPlurisubharmonic
      simpa using h
    · obtain ⟨y, hyO, hy⟩ := F.nowhereZero O hO ⟨x, hxO⟩
      exact ⟨y, hyO, logWeight_ne_bot_of_pos (lt_of_le_of_ne (D.weight_nonneg _) (Ne.symm hy))⟩
  have hpolar := Hironaka.quasiPsh_poles_manifoldLocallyPluripolar hlogpsh
  have hqe : ∀ P : Z → Prop, (∀ z, g z ∉ (exceptionalCentre n g) → P z) → QuasiEverywhere (n := n) P := fun P hP => by
    refine hpolar.mono fun z hz => ?_
    by_contra hlog
    refine hz (hP z fun hzC => hlog ?_)
    have h0 : D.weight (g z) = 0 := D.weight_eq_zero_of_mem hzC
    simp [logWeight, h0]
  have hle₁ : w ≤ G := hw'.le_of_quasiEverywhere_le hG (hqe _ fun z hz => (hoff z hz).le)
  have hle₂ : G ≤ w := hG.le_of_quasiEverywhere_le hw' (hqe _ fun z hz => (hoff z hz).ge)
  -- nondegeneracy of `ψ`
  have hnd : LocallyNondegenerate ψ := by
    intro x O hO hxO
    have hExcint : interior (exceptionalLocus n g) = ∅ :=
      Set.eq_empty_of_subset_empty ((interior_mono
        (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hg)).trans
        (ExceptionalFibres.interior_preimage_eq_empty hg).le)
    have hO' : IsOpen (g ⁻¹' O) := hO.preimage hg.contMDiff.continuous
    have hnot : ¬ g ⁻¹' O ⊆ exceptionalLocus n g := fun hsub => by
      have := interior_maximal hsub hO'
      rw [hExcint] at this
      exact this (show sec x ∈ g ⁻¹' O by rw [mem_preimage, hgs]; exact hxO)
    obtain ⟨z₀, hz₀O, hz₀E⟩ := not_subset.mp hnot
    have hopen : IsOpen (g ⁻¹' O ∩ (exceptionalLocus n g)ᶜ) :=
      hO'.inter (StrictTransformComposition.isOpen_compl_exceptionalLocus hg.contMDiff)
    obtain ⟨z₁, ⟨hz₁O, hz₁E⟩, hz₁⟩ := hw₀.2 z₀ _ hopen ⟨hz₀O, hz₀E⟩
    have hz₁C : g z₁ ∉ (exceptionalCentre n g) := fun h => hz₁E (by rw [← preimage_exceptionalCentre hg]; exact h)
    refine ⟨g z₁, hz₁O, ?_⟩
    rw [hψv _ hz₁C]
    simp only [v, hsg z₁ hz₁C]
    exact EReal.add_ne_bot_iff.mpr ⟨hz₁, EReal.coe_ne_bot _⟩
  exact ⟨δ, hδ, ψ, ⟨hψ, hnd⟩, hZ, hhZ, fun z => le_antisymm (hle₁ z) (hle₂ z)⟩

end

end Hironaka.BlowupPushforward
