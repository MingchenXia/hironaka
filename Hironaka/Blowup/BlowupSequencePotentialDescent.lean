import Hironaka.Blowup.ExceptionalPushforwardPotential
import Hironaka.Analytic.GlobalPotentialPullback
import Hironaka.Analytic.HolomorphicZeroSetNull
import Hironaka.Analytic.ThetaPshDecreasingLimit
import Hironaka.Blowup.BlowupSequenceTotalTransform
import Hironaka.Analytic.PotentialTheory.PlurisubharmonicAE

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Descent of potentials along blowup sequences (Xia Hironaka Prop. 1.5.3)

Source: Xia, *Singularities in global pluripotential theory*, Prop. 1.5.3 (pullback of potentials
along a modification is a bijection), in the form used by Copy-4 `lem:domination` Step 3
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex`, "By
[Xia, Prop 1.5.3], the pullback of potentials is a bijection ... hence `s̃_j = s_j ∘ ρ_j`").
Piece of the positive-current programme (`TN.2.3.PCI`) assigned by TN23-ENVELOPES (I-0773
C-0006); needed under every answer to D2 of I-0764.

* `exists_descent_of_isBlowupSequence` — TN23's exact target: for a blowup sequence
  `π : Y → X` (`Hironaka.BlowupSequences.IsBlowupSequence`) of a COMPACT complex manifold `X` and
  a closed real `(1,1)`-form `θ` on `X`, every `π^*θ`-psh potential `w` on `Y` is `s ∘ π` for a
  `θ`-psh potential `s` on `X`, with `s (π y) = w y` at EVERY point `y`.
* `exists_descent_of_isBlowupAlong` — the same for one blowup;
  `exists_thetaPshPotential_eq_off_of_isBlowupAlong` — its first half, the identity off `Exc g`.
* `eq_of_eq_off_exceptionalLocus` — two `θ`-psh functions on a blowup that agree off the
  exceptional locus agree everywhere.

## Proof

One blowup `g : Z → Y` along `C` (`Y` compact): off the exceptional centre `g(Exc g)` the map `g`
has a section and is a local biholomorphism, so `w ∘ g⁻¹` is `θ`-psh there
(`ThetaPshPushforward.thetaPshOff_comp_section`); it extends across the centre, which has
codimension-`≥ 2` flattenings (`BlowupExceptionalCentre.exists_flat_exceptionalCentre`,
`ThetaPshCodimTwoExtension`); nondegeneracy comes down from `Z` because `Exc g` has empty interior.
This is `ExceptionalPushforwardPotential.exists_thetaPshPotential_pushforward` with no exceptional
correction.  For the identity everywhere: `ψ ∘ g` and `w` are both `g^*θ`-psh
(`GlobalPotentialPullback.thetaPlurisubharmonic_comp`); in a chart, after adding one local potential
(any local potential works, `ThetaPshDecreasingLimit.plurisubharmonicOn_corrected_of_thetaPlurisubharmonic`)
both are psh, and they agree off `Exc g`, which near each point lies in the zero set of the local
generator of the invertible ideal `g^* 𝓘_C`; that zero set is null
(`HolomorphicZeroSetNull.measure_inter_preimage_zero_eq_zero`), and psh functions equal almost
everywhere are equal (`PlurisubharmonicOn.eqOn_of_ae_eq`).  Sequences: induction on
`IsBlowupSequence`, the intermediate manifolds being compact
(`StrictTransformComposition.IsBlowupSequence.compactSpace_surjective`) and
`(f ∘ g)^*θ = g^*(f^*θ)` (`SmoothRealForm.pullback_comp_geometricallyEq`).

Sorry-free.  No existing statement is changed.
-/

open Set Filter MeasureTheory Metric
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BlowupSequencePotentialDescent

open Hironaka.PositiveClasses Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences BlowupExceptionalCentre ThetaPshCodimTwoExtension

noncomputable section

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

/-! ### One blowup, off the exceptional locus -/

/-- **Descent along one blowup, off the exceptional locus.**  A `g^*θ`-psh potential `w` on the
blowup `Z` of a compact `Y` is `ψ ∘ g` off `Exc g` for a `θ`-psh potential `ψ` on `Y`: push it down
along a section of `g` off the exceptional centre and extend across the centre (codimension
`≥ 2`).  This is `ExceptionalPushforwardPotential.exists_thetaPshPotential_pushforward` without the
exceptional correction. -/
theorem exists_thetaPshPotential_eq_off_of_isBlowupAlong [CompactSpace Y]
    (θ : ClosedRealOneOneForm n Y) {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g)
    {w : Z → EReal}
    (hw : IsThetaPshPotential (ClosedRealOneOneForm.pullback hg.contMDiff θ).val w) :
    ∃ ψ : Y → EReal, IsThetaPshPotential θ.val ψ ∧
      ∀ z ∉ exceptionalLocus n g, ψ (g z) = w z := by
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
  -- push down off the centre (zero correction) and extend across it
  set θZ : ClosedRealOneOneForm n Z := ClosedRealOneOneForm.pullback hg.contMDiff θ with hθZ
  have hrpot : ∀ z, g z ∉ exceptionalCentre n g → ∀ eZ : ComplexChart n Z,
      z ∈ eZ.val.source → ∃ W : Set (ComplexModel n), eZ.val z ∈ W ∧
        IsSmoothLocalPotential (θZ - ClosedRealOneOneForm.pullback hg.contMDiff θ).val eZ W
          (fun ζ => (fun _ : Z => (0 : ℝ)) (eZ.val.symm ζ)) := by
    intro z _ eZ hze
    refine ⟨eZ.val.target, eZ.val.map_source hze, ?_⟩
    rw [hθZ, sub_self]
    exact LocalPotentials.localPotential_zero eZ eZ.val.open_target subset_rfl
  set v : Y → EReal := fun y => w (sec y) + (((fun _ : Z => (0 : ℝ)) (sec y) : ℝ) : EReal)
    with hv
  have hvoff : ThetaPshOff θ.val (exceptionalCentre n g) v :=
    ThetaPshPushforward.thetaPshOff_comp_section (θY := θ) (θZ := θZ)
      (r := fun _ : Z => (0 : ℝ)) hg.contMDiff hC₂ hEx hsg (fun y _ => hgs y) hw.1 hrpot
  have hflat₂ : HasCodimTwoFlattenings (n := n) (exceptionalCentre n g) := fun p hp => by
    obtain ⟨k, hk, Φ, hsrc, -, hflat, -⟩ := exists_flat_exceptionalCentre hg hp
    exact ⟨k, hk, Φ, hsrc, fun y hy hyC => (hflat hy.1 hy.2).mp (hC₂C hyC)⟩
  set ψ := extensionAcross (exceptionalCentre n g) v with hψdef
  have hψ : ThetaPlurisubharmonic θ.val ψ :=
    thetaPlurisubharmonic_extensionAcross hC₂ hflat₂
      (Hironaka.LocalPotentials.closedRealOneOne_hasLocalPotentials θ) hvoff
  have hψv : ∀ y ∉ exceptionalCentre n g, ψ y = v y := fun y hy =>
    extensionAcross_eq_of_notMem hC₂ hvoff hy
  have hvsec : ∀ y, v y = w (sec y) := fun y => by simp [hv]
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
    obtain ⟨z₁, ⟨hz₁O, hz₁E⟩, hz₁⟩ := hw.2 z₀ _ hopen ⟨hz₀O, hz₀E⟩
    have hz₁C : g z₁ ∉ exceptionalCentre n g := fun h => hz₁E (by
      rw [← preimage_exceptionalCentre hg]; exact h)
    refine ⟨g z₁, hz₁O, ?_⟩
    rw [hψv _ hz₁C, hvsec, hsg z₁ hz₁C]
    exact hz₁
  refine ⟨ψ, ⟨hψ, hnd⟩, fun z hz => ?_⟩
  have hzC : g z ∉ exceptionalCentre n g := fun h => hz (by
    rw [← preimage_exceptionalCentre hg]; exact h)
  rw [hψv _ hzC, hvsec, hsg z hzC]

/-! ### Equality across the exceptional locus -/

/-- Near every point of the blowup, `Exc g` lies in the zero set of a local generator `h` of the
invertible ideal `g^* 𝓘_C`, and `h` vanishes identically on no nonempty open set. -/
theorem exists_generator_exceptionalLocus_subset_zero {C : Set Y} {g : Z → Y}
    (hg : IsBlowupAlong n C g) (z : Z) :
    ∃ U : Set Z, IsOpen U ∧ z ∈ U ∧ ∃ h : Z → ℂ,
      MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) h U ∧
      (∀ W : Set Z, IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, h y ≠ 0) ∧
      ∀ y ∈ U, y ∈ exceptionalLocus n g → h y = 0 := by
  obtain ⟨U, hU, hzU, h, hhol, hnv, hgen⟩ := hg.2.2.2.1 z
  refine ⟨U, hU, hzU, h, hhol, hnv, fun y hyU hyE => ?_⟩
  have hgyC : g y ∈ C := BlowupIsomorphismOff.exceptionalLocus_subset_preimage hg hyE
  have hhy : HolomorphicAt n h y := by
    filter_upwards [hU.mem_nhds hyU] with y' hy'
    exact (hhol y' hy').mdifferentiableAt (hU.mem_nhds hy')
  have hmem : (GermIdeal.pullback (m := n) g (vanishingIdeal (n := n) C)).mem y h :=
    (hgen y hyU h).mpr (isInSpanAt_of_eq_mul rfl hhy (holomorphicAt_const 1) (by simp))
  obtain ⟨-, N, s, c, hs, -, heq⟩ := hmem
  have hsy : ∀ i, s i y = 0 := fun i => by
    obtain ⟨a, ⟨-, ha⟩, hsa⟩ := hs i
    rw [hsa]
    exact ha.self_of_nhds hgyC
  rw [heq.self_of_nhds]
  simp [hsy]

/-- **A `θ`-psh function on a blowup is determined off the exceptional locus.**  Two functions
satisfying `ThetaPlurisubharmonic θ` on the blowup `Z` that agree off `Exc g` agree everywhere: in a
chart both are psh after adding one local potential, they agree off the zero set of the local
generator of `g^* 𝓘_C`, which is null, and psh functions equal almost everywhere are equal. -/
theorem eq_of_eq_off_exceptionalLocus {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g)
    {θ : SmoothRealForm n Z 2} {u v : Z → EReal} (hu : ThetaPlurisubharmonic θ u)
    (hv : ThetaPlurisubharmonic θ v) (huv : ∀ z ∉ exceptionalLocus n g, u z = v z) (z : Z) :
    u z = v z := by
  set e := complexChartAt (n := n) z with he
  have hze : e.val z ∈ e.val.target := e.val.map_source (mem_complexChartAt_source z)
  obtain ⟨W, ρ, hzW, hρ, hpu⟩ := hu e (e.val z) hze
  have hpv := ThetaPshDecreasingLimit.plurisubharmonicOn_corrected_of_thetaPlurisubharmonic hv e hρ
  obtain ⟨U, hU, hzU, h, hhol, hnv, hzero⟩ := exists_generator_exceptionalLocus_subset_zero hg z
  have hUopen : IsOpen (e.val.target ∩ e.val.symm ⁻¹' U) := e.val.isOpen_inter_preimage_symm hU
  have hzU' : e.val z ∈ e.val.target ∩ e.val.symm ⁻¹' U := by
    refine ⟨hze, ?_⟩
    simpa [e.val.left_inv (mem_complexChartAt_source z)] using hzU
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp (hρ.1.inter hUopen) _ ⟨hzW, hzU'⟩
  set B := ball (e.val z) r with hB
  have hBW : B ⊆ W := fun ζ hζ => (hrsub hζ).1
  have hBU : B ⊆ e.val.target ∩ e.val.symm ⁻¹' U := fun ζ hζ => (hrsub hζ).2
  -- the generator in the chart is holomorphic on `B` and nonzero somewhere in `B`
  have hH : DifferentiableOn ℂ (fun ζ => h (e.val.symm ζ)) B :=
    (differentiableOn_comp_chartSymm z hhol).mono hBU
  have hOopen : IsOpen (e.val.source ∩ e.val ⁻¹' B) :=
    e.val.isOpen_inter_preimage isOpen_ball
  have hOU : e.val.source ∩ e.val ⁻¹' B ⊆ U := fun y hy => by
    have := (hBU hy.2).2
    rwa [mem_preimage, e.val.left_inv hy.1] at this
  obtain ⟨y₁, hy₁, hy₁h⟩ := hnv _ hOopen hOU
    ⟨z, mem_complexChartAt_source z, mem_ball_self hr⟩
  have hnull : volume (B ∩ (fun ζ => h (e.val.symm ζ)) ⁻¹' {0}) = 0 :=
    HolomorphicZeroSetNull.measure_inter_preimage_zero_eq_zero volume isOpen_ball
      (convex_ball _ _) hH hy₁.2 (by simpa [e.val.left_inv hy₁.1] using hy₁h)
  -- the two corrected functions agree almost everywhere on `B`
  have hae : (fun ζ => chartFunction u e ζ + (ρ ζ : EReal)) =ᵐ[volume.restrict B]
      (fun ζ => chartFunction v e ζ + (ρ ζ : EReal)) := by
    have hcompl : ∀ᵐ ζ ∂(volume.restrict B),
        ζ ∉ B ∩ (fun ζ => h (e.val.symm ζ)) ⁻¹' {0} := by
      refine measure_eq_zero_iff_ae_notMem.mp ?_
      exact le_antisymm ((Measure.restrict_apply_le _ _).trans_eq hnull) bot_le
    filter_upwards [hcompl, ae_restrict_mem isOpen_ball.measurableSet] with ζ hζ hζB
    have hne : h (e.val.symm ζ) ≠ 0 := fun h0 => hζ ⟨hζB, h0⟩
    have hnotE : e.val.symm ζ ∉ exceptionalLocus n g := fun hE =>
      hne (hzero _ (hBU hζB).2 hE)
    simp only [chartFunction, huv _ hnotE]
  have hEq := PlurisubharmonicOn.eqOn_of_ae_eq (fun ζ hζ => hpu ζ (hBW hζ))
    (fun ζ hζ => hpv ζ (hBW hζ)) isOpen_ball volume hae (mem_ball_self hr)
  have hleft : e.val.symm (e.val z) = z := e.val.left_inv (mem_complexChartAt_source z)
  simp only [chartFunction, hleft] at hEq
  have := congrArg (fun a => a - ((ρ (e.val z) : ℝ) : EReal)) hEq
  simpa [EReal.add_sub_cancel_right] using this

/-! ### One blowup, everywhere -/

/-- **Descent along one blowup** (Xia Hironaka Prop. 1.5.3 for a single blowup of a compact manifold):
every `g^*θ`-psh potential on the blowup is `ψ ∘ g` for a `θ`-psh potential `ψ` downstairs, the
identity holding at every point. -/
theorem exists_descent_of_isBlowupAlong [CompactSpace Y] (θ : ClosedRealOneOneForm n Y)
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g) {w : Z → EReal}
    (hw : IsThetaPshPotential (ClosedRealOneOneForm.pullback hg.contMDiff θ).val w) :
    ∃ ψ : Y → EReal, IsThetaPshPotential θ.val ψ ∧ ∀ z, ψ (g z) = w z := by
  obtain ⟨ψ, hψ, hoff⟩ := exists_thetaPshPotential_eq_off_of_isBlowupAlong θ hg hw
  refine ⟨ψ, hψ, eq_of_eq_off_exceptionalLocus hg (θ := (ClosedRealOneOneForm.pullback
    hg.contMDiff θ).val) (u := fun z => ψ (g z)) ?_ hw.1 hoff⟩
  exact GlobalPotentialPullback.thetaPlurisubharmonic_comp hg.contMDiff hψ.1

/-! ### Blowup sequences -/

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- The induction behind `exists_descent_of_isBlowupSequence`, with the holomorphy proof of the
sequence left free. -/
theorem exists_descent_of_isBlowupSequence_aux [CompactSpace X] (θ : ClosedRealOneOneForm n X)
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {π : Y → X} (hπ : IsBlowupSequence n X Y π) :
    ∀ (hc : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π) {w : Y → EReal},
      IsThetaPshPotential (ClosedRealOneOneForm.pullback hc θ).val w →
        ∃ s : X → EReal, IsThetaPshPotential θ.val s ∧ ∀ y, s (π y) = w y := by
  induction hπ with
  | refl =>
    intro hc w hw
    refine ⟨w, ?_, fun _ => rfl⟩
    exact ((SmoothRealForm.pullback_id_geometricallyEq θ.val).thetaPshPotential_iff w).mp hw
  | step f C g hf hg ih =>
    intro hc w hw
    have := (StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hf).1
    have hw' : IsThetaPshPotential (ClosedRealOneOneForm.pullback hg.contMDiff
        (ClosedRealOneOneForm.pullback hf.contMDiff θ)).val w :=
      ((SmoothRealForm.pullback_comp_geometricallyEq hf.contMDiff hg.contMDiff
        θ.val).thetaPshPotential_iff w).mp hw
    obtain ⟨ψ, hψ, hψw⟩ := exists_descent_of_isBlowupAlong _ hg hw'
    obtain ⟨s, hs, hsψ⟩ := ih hf.contMDiff hψ
    exact ⟨s, hs, fun z => (hsψ (g z)).trans (hψw z)⟩

/-- **Xia Hironaka Prop. 1.5.3 for blowup sequences** (the descent step of Copy-4 `lem:domination`
Step 3): if `π : Y → X` is a finite sequence of blowups with smooth centres of a compact complex
manifold `X`, every `π^*θ`-psh potential `w` on `Y` is `s ∘ π` for a `θ`-psh potential `s` on `X`,
the identity `s (π y) = w y` holding at every point. -/
theorem exists_descent_of_isBlowupSequence [CompactSpace X]
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {π : Y → X} (hπ : IsBlowupSequence n X Y π) (θ : ClosedRealOneOneForm n X) {w : Y → EReal}
    (hw : IsThetaPshPotential (ClosedRealOneOneForm.pullback hπ.contMDiff θ).val w) :
    ∃ s : X → EReal, IsThetaPshPotential θ.val s ∧ ∀ y, s (π y) = w y :=
  exists_descent_of_isBlowupSequence_aux θ hπ hπ.contMDiff hw

end

end Hironaka.BlowupSequencePotentialDescent
