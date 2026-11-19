import Hironaka.Blowup.BlowupPushforward
import Hironaka.Analytic.MeteredDivisorSmoothOffSupport

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-!
# CT22 Lemma 4.3, step 2: pushing the exceptionally corrected current across the centre

Let `g : Z → Y` be a blowup along `C`, `E` a metered effective `ℚ`-divisor supported in
`Exc g`, and `ω̃ = g^*ω - Θ_E` the exceptional correction of the Kähler background.  Let
`T' = θ_Z + ddᶜ u` be an `ε₀`-admissible presentation upstairs of the pullback class, so
that `T' + ε₀ω̃ ≥ 0`.

CT22 forms `S = T' - ε₀Θ_E` and pushes it forward.  Since

    `S + ε₀ g^*ω = T' + ε₀ω̃ ≥ 0`,

the pushforward `T = g_*S` should be a current of `{θ}` with `T + εω ≥ 0`; in potentials
that says the `(g^*θ + ε₀ω̃)`-PSH function `u - h_Z` is `ψ ∘ g + ε₀ψ_E` for a
`(θ + ε₀ω)`-PSH `ψ` downstairs.  That is exactly what is proved here:

`exists_thetaPshPotential_pushforward` produces `ψ`, and the identity holds at every point
off `Exc g` — which is every point the density comparison of CT22's step 3 looks at.

The three ingredients are all available.  Off `Exc g` the divisor weight `ψ_E` is a smooth
local potential of `-Θ_E` (`Hironaka.MeteredDivisorSmoothOffSupport`), so `u - h_Z + ε₀ψ_E`
is `g^*(θ + ε₀ω)`-PSH there; `Hironaka.ThetaPshPushforward.thetaPshOff_comp_section` moves
it down along a section of `g`; and `Hironaka.ThetaPshCodimTwoExtension` extends the result
across the exceptional centre.  Nondegeneracy downstairs comes from nondegeneracy
upstairs, because `Exc g` has empty interior.

Nothing here regularizes: `ψ` has no analytic singularities, and turning it into a
sequence of admissible presentations is the remaining analytic input of
`Hironaka.ExceptionalPushforwardFatouReduction`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.ExceptionalPushforwardPotential

open Hironaka.PositiveClasses Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka.NumericalRestrictedVolumeScaffold
  Hironaka.HolomorphicMaps
  BlowupExceptionalCentre ThetaPshCodimTwoExtension

noncomputable section

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

section Forms

variable {k : ℕ} {V M : Type*}
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Pullback commutes with addition, coefficientwise. -/
theorem pullback_add_geometricallyEq {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (a b : ClosedRealOneOneForm n M) :
    (ClosedRealOneOneForm.pullback hf (a + b)).val.GeometricallyEq
      (ClosedRealOneOneForm.pullback hf a + ClosedRealOneOneForm.pullback hf b).val := by
  intro e z hz
  let d := complexChartAt (n := n) (f (e.val.symm z))
  have hzd : z ∈ coordinateDomain f e d := ⟨hz, mem_complexChartAt_source _⟩
  simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.pullback_val,
    SmoothRealForm.pullback_coeff hf _ e d hzd]
  ext v
  simp

end Forms

/-- **Pushing an exceptionally corrected admissible presentation across the centre.**
`u` is a potential of an `ε₀`-admissible presentation upstairs for the corrected Kähler
background `ω̃ = g^*ω - Θ_E`; `ψ` is a `(θ + ε₀ω)`-PSH potential downstairs with

    `ψ ∘ g = u - h_Z + ε₀ ψ_E`   off `Exc g`,

where `θ_Z = g^*θ + ddᶜ h_Z` compares the chosen representative with the pullback. -/
theorem exists_thetaPshPotential_pushforward [CompactSpace Y]
    (θ : ClosedRealOneOneForm n Y)
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g)
    (omega : KahlerBackground n Y)
    (E : MeteredEffectiveQDivisor n Z) (hE : E.support ⊆ exceptionalLocus n g)
    (omegaTilde : KahlerBackground n Z)
    (hcorr : omegaTilde.form =
      ClosedRealOneOneForm.pullback hg.contMDiff omega.form - E.curvature)
    {ε₀ : ℝ}
    (rep : ClosedRealOneOneForm n Z)
    (hrep : RealBottChern.ofRepresentative rep =
      RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hg.contMDiff θ))
    (u : Z → EReal)
    (hu : IsThetaPshPotential (rep + ε₀ • omegaTilde.form).val u) :
    ∃ ψ : Y → EReal,
      IsThetaPshPotential (θ + ε₀ • omega.form).val ψ ∧
      ∃ hZ : Z → ℝ, ChartSmooth (n := n) hZ ∧
        (∀ (e : ComplexChart n Z) (z : ComplexModel n), z ∈ e.val.target →
          (ClosedRealOneOneForm.pullback hg.contMDiff θ).val.coeff e z =
            rep.val.coeff e z + smoothDDC (fun y => hZ (e.val.symm y)) z) ∧
        ∀ z ∉ exceptionalLocus n g,
          ψ (g z) = u z - (hZ z : EReal) + ((ε₀ * (E.weight z).toReal : ℝ) : EReal) := by
  classical
  have hC₂ : IsClosed (exceptionalCentre n g) := isClosed_exceptionalCentre hg
  have hC₂C : exceptionalCentre n g ⊆ C := exceptionalCentre_subset hg
  have hEx : ∀ z, g z ∉ exceptionalCentre n g → z ∉ exceptionalLocus n g :=
    fun z hz hzE => hz ⟨z, hzE, rfl⟩
  -- a section of `g`
  have hsurj := StrictTransformComposition.surjective_of_isBlowupAlong hg
  set sec : Y → Z := fun y => Classical.choose (hsurj y) with hsecdef
  have hgs : ∀ y, g (sec y) = y := fun y => Classical.choose_spec (hsurj y)
  have hsg : ∀ z, g z ∉ exceptionalCentre n g → sec (g z) = z := fun z hz =>
    ExceptionalFibres.eq_of_apply_eq_of_not_mem_exceptionalLocus hg (hEx z hz) (hgs (g z))
  -- move to the pullback representative
  obtain ⟨hZ, hhZ, heqZ⟩ := (RealBottChern.ofRepresentative_eq_iff _ _).mp hrep
  set A : ClosedRealOneOneForm n Z :=
    ClosedRealOneOneForm.pullback hg.contMDiff θ + ε₀ • omegaTilde.form with hA
  set w : Z → EReal := fun z => u z - (hZ z : EReal) with hw
  have hwpsh : IsThetaPshPotential A.val w := by
    refine thetaPshPotential_sub_smooth hhZ (fun e z hz => ?_) hu
    rw [hA, ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_add, heqZ e z hz]
    abel
  -- the discrepancy form and its potential
  set B : ClosedRealOneOneForm n Y := θ + ε₀ • omega.form with hB
  have hgeom : (A - ClosedRealOneOneForm.pullback hg.contMDiff B).val.GeometricallyEq
      (ε₀ • (-E.curvature)).val := by
    intro e z hz
    have h1 := pullback_add_geometricallyEq hg.contMDiff θ (ε₀ • omega.form) e hz
    have h2 := BlowupPushforward.pullback_smul_geometricallyEq hg.contMDiff ε₀ omega.form e hz
    simp only [hA, hB, hcorr, BlowupBigPullback.coeff_sub, ClosedRealOneOneForm.coeff_add,
      ClosedRealOneOneForm.coeff_smul, ClosedRealOneOneForm.coeff_neg] at h1 h2 ⊢
    rw [h1, h2]
    ext v
    simp
    ring
  set r : Z → ℝ := fun z => ε₀ * (E.weight z).toReal with hr
  have hrpot : ∀ z, g z ∉ exceptionalCentre n g → ∀ eZ : ComplexChart n Z,
      z ∈ eZ.val.source → ∃ W : Set (ComplexModel n), eZ.val z ∈ W ∧
        IsSmoothLocalPotential (A - ClosedRealOneOneForm.pullback hg.contMDiff B).val eZ W
          (fun ζ => r (eZ.val.symm ζ)) := by
    intro z hz eZ hze
    have hzsupp : z ∉ E.support := fun hmem => hEx z hz (hE hmem)
    obtain ⟨W, hzW, hpot⟩ :=
      MeteredDivisorSmoothOffSupport.exists_isSmoothLocalPotential_neg_curvature E hzsupp eZ hze
    refine ⟨W, hzW, (hgeom.localPotential_iff eZ W _).mpr ?_⟩
    have := Hironaka.LocalPotentials.localPotential_smul hpot ε₀
    simpa [hr, smul_eq_mul] using this
  -- push down off the centre and extend across it
  set v : Y → EReal := fun y => w (sec y) + (r (sec y) : EReal) with hv
  have hvoff : ThetaPshOff B.val (exceptionalCentre n g) v :=
    ThetaPshPushforward.thetaPshOff_comp_section hg.contMDiff hC₂ hEx hsg
      (fun y _ => hgs y) hwpsh.1 hrpot
  have hflat₂ : HasCodimTwoFlattenings (n := n) (exceptionalCentre n g) := fun p hp => by
    obtain ⟨k, hk, Φ, hsrc, -, hflat, -⟩ := exists_flat_exceptionalCentre hg hp
    exact ⟨k, hk, Φ, hsrc, fun y hy hyC => (hflat hy.1 hy.2).mp (hC₂C hyC)⟩
  set ψ := extensionAcross (exceptionalCentre n g) v with hψdef
  have hψ : ThetaPlurisubharmonic B.val ψ :=
    thetaPlurisubharmonic_extensionAcross hC₂ hflat₂
      (Hironaka.LocalPotentials.closedRealOneOne_hasLocalPotentials B) hvoff
  have hψv : ∀ y ∉ exceptionalCentre n g, ψ y = v y := fun y hy =>
    extensionAcross_eq_of_notMem hC₂ hvoff hy
  -- nondegeneracy, from nondegeneracy upstairs and the empty interior of `Exc g`
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
    obtain ⟨z₁, ⟨hz₁O, hz₁E⟩, hz₁⟩ := hwpsh.2 z₀ _ hopen ⟨hz₀O, hz₀E⟩
    have hz₁C : g z₁ ∉ exceptionalCentre n g := fun h => hz₁E (by
      rw [← preimage_exceptionalCentre hg]; exact h)
    refine ⟨g z₁, hz₁O, ?_⟩
    rw [hψv _ hz₁C]
    simp only [hv, hsg z₁ hz₁C]
    exact EReal.add_ne_bot_iff.mpr ⟨hz₁, EReal.coe_ne_bot _⟩
  refine ⟨ψ, ⟨hψ, hnd⟩, hZ, hhZ, heqZ, fun z hz => ?_⟩
  have hzC : g z ∉ exceptionalCentre n g := fun h => hz (by
    rw [← preimage_exceptionalCentre hg]; exact h)
  rw [hψv _ hzC]
  simp only [hv, hsg z hzC, hw, hr]

end

end Hironaka.ExceptionalPushforwardPotential
