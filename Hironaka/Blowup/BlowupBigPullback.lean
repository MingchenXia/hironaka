import Hironaka.Blowup.BlowupKahler
import Hironaka.Analytic.FactorizedWeightPsh
import Hironaka.Analytic.GlobalPotentialPullback
import Hironaka.Blowup.ExceptionalFibres
import Hironaka.Analytic.PotentialTheory.LocalPotentialsBasic
import Hironaka.Analytic.GlobalPotentialTransforms

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The pullback of a big class under a blowup is big

Source: CT22, Section 4; Boucksom, *Divisorial Zariski decompositions*, Prop. 2.3.

Let `π : Z → M` be the blowup of a compact complex manifold along a nowhere dense closed
submanifold `C`, and let `T = θ_T + ddᶜ u ≥ ω'` be a Kähler current in the class of `θ`.

* Write `θ = θ_T + ddᶜ h` (Bott–Chern), so `u - h` is `(θ - ω')`-PSH.
* `(u - h) ∘ π` is `(π^* θ - π^* ω')`-PSH (holomorphic pullback).
* For the Blanchard form `Θ` of `C` and `ε > 0` with `ω_Z := π^* ω' + ε Θ` Kähler
  (`BlowupKahler.exists_isKahler_pullback_add`), `ε log (U ∘ π)` is `(-εΘ)`-PSH
  (`FactorizedWeightPsh`), where `U` is the Blanchard weight.
* Hence `v := (u - h) ∘ π + ε log (U ∘ π)` is `(π^* θ - ω_Z)`-PSH, i.e.
  `π^* θ + ddᶜ v ≥ ω_Z`.  It is not `-∞` on any open set: an open set of `Z` contains a point
  off `π⁻¹ C`, where `π` is open, so it contains a point where `u ∘ π` and `U ∘ π` are finite.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BlowupBigPullback

open Hironaka.PositiveClasses Hironaka.BlowupSequences
  Hironaka.HolomorphicMaps FactorizedWeightForm FactorizedWeightPsh

noncomputable section

section Forms

variable {k n : ℕ} {V M : Type*}
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem coeff_sub {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] (a b : ClosedRealOneOneForm n M) (e : ComplexChart n M)
    (z : ComplexModel n) : (a - b).val.coeff e z = a.val.coeff e z - b.val.coeff e z := by
  rw [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_neg,
    sub_eq_add_neg]

/-- Pullback commutes with subtraction, coefficientwise. -/
theorem pullback_sub_geometricallyEq {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (a b : ClosedRealOneOneForm n M) :
    (ClosedRealOneOneForm.pullback hf (a - b)).val.GeometricallyEq
      (ClosedRealOneOneForm.pullback hf a - ClosedRealOneOneForm.pullback hf b).val := by
  intro e z hz
  let d := complexChartAt (n := n) (f (e.val.symm z))
  have hzd : z ∈ coordinateDomain f e d := ⟨hz, mem_complexChartAt_source _⟩
  rw [coeff_sub, ClosedRealOneOneForm.pullback_val, ClosedRealOneOneForm.pullback_val,
    ClosedRealOneOneForm.pullback_val, SmoothRealForm.pullback_coeff hf _ e d hzd,
    SmoothRealForm.pullback_coeff hf _ e d hzd, SmoothRealForm.pullback_coeff hf _ e d hzd,
    coeff_sub]
  ext v
  simp

end Forms

theorem thetaPlurisubharmonic_of_geometricallyEq {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {θ η : SmoothRealForm n M 2}
    (h : θ.GeometricallyEq η) {u : M → EReal} (hu : ThetaPlurisubharmonic θ u) :
    ThetaPlurisubharmonic η u := by
  intro e z hz
  obtain ⟨W, ρ, hzW, hρ, hp⟩ := hu e z hz
  exact ⟨W, ρ, hzW, (h.localPotential_iff e W ρ).mp hρ, hp⟩

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

/-- **The pulled-back Kähler current.**  If `T = θ_T + ddᶜ u ≥ ω'` is a Kähler current in `{θ}`
with `θ = θ_T + ddᶜ h`, `U ≥ 0` is a weight positive off `C` with `U ∘ π = |h_z|² U'_z` locally,
and `π^* ω' + ε Θ` is Kähler (`Θ` the glued form of the factorization), then
`π^* θ + ddᶜ ((u - h) ∘ π + ε log (U ∘ π)) ≥ π^* ω' + ε Θ`. -/
def pullbackCurrent {θ : ClosedRealOneOneForm n Y} (T : KahlerCurrent (RealBottChern.ofRepresentative θ))
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g) {h : Y → ℝ} (hh : ChartSmooth (n := n) h)
    (heq : ∀ (e : ComplexChart n Y) (z : ComplexModel n), z ∈ e.val.target →
      θ.val.coeff e z = T.representative.val.coeff e z + smoothDDC (fun y => h (e.val.symm y)) z)
    {U : Y → ℝ} (hU : ∀ y ∉ C, 0 < U y) (F : WeightFactorization n (fun z => U (g z)))
    {ε : ℝ} (hε : 0 < ε)
    (hK : (ClosedRealOneOneForm.pullback hg.contMDiff T.lowerBound.form +
      ε • F.closedForm).val.IsKahler) :
    KahlerCurrent (RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hg.contMDiff θ)) :=
  have hu₁ : ThetaPlurisubharmonic (θ - T.lowerBound.form).val
      (fun y => T.potential y - (h y : EReal)) := by
    refine GlobalPotentialTransforms.thetaPlurisubharmonic_sub_smooth hh (fun e z hz => ?_)
      T.strictlyPsh.1
    rw [coeff_sub, coeff_sub, heq e z hz]
    abel
  have hpull : ThetaPlurisubharmonic
      (ClosedRealOneOneForm.pullback hg.contMDiff θ -
        ClosedRealOneOneForm.pullback hg.contMDiff T.lowerBound.form).val
      (fun z => T.potential (g z) - (h (g z) : EReal)) :=
    thetaPlurisubharmonic_of_geometricallyEq (pullback_sub_geometricallyEq hg.contMDiff _ _)
      (GlobalPotentialPullback.thetaPlurisubharmonic_comp hg.contMDiff hu₁)
  { representative := ClosedRealOneOneForm.pullback hg.contMDiff θ
    represents := rfl
    potential := fun z => (T.potential (g z) - (h (g z) : EReal)) +
      (ε : EReal) * logWeight (fun z => U (g z)) z
    lowerBound := ⟨_, hK⟩
    strictlyPsh := by
      refine ⟨?_, ?_⟩
      · change ThetaPlurisubharmonic (ClosedRealOneOneForm.pullback hg.contMDiff θ -
          (ClosedRealOneOneForm.pullback hg.contMDiff T.lowerBound.form + ε • F.closedForm)).val _
        have hform : ClosedRealOneOneForm.pullback hg.contMDiff θ -
            (ClosedRealOneOneForm.pullback hg.contMDiff T.lowerBound.form + ε • F.closedForm) =
            (ClosedRealOneOneForm.pullback hg.contMDiff θ -
              ClosedRealOneOneForm.pullback hg.contMDiff T.lowerBound.form) +
              -(ε • F.closedForm) := by abel
        rw [hform]
        exact LocalPotentials.thetaPlurisubharmonic_add hpull (thetaPlurisubharmonic_logWeight F hε)
      · intro x W hW hxW
        have hnot : ¬ W ⊆ g ⁻¹' C := fun hsub => by
          have hx := interior_maximal hsub hW hxW
          rw [ExceptionalFibres.interior_preimage_eq_empty hg] at hx
          exact hx
        obtain ⟨z₀, hz₀W, hz₀C⟩ := not_subset.mp hnot
        have hz₀E : z₀ ∉ exceptionalLocus n g := fun hE =>
          hz₀C (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hg hE)
        have himg : g '' W ∈ 𝓝 (g z₀) := by
          rw [← StrictTransformComposition.map_nhds_eq_of_not_mem_exceptionalLocus hg.contMDiff
            hz₀E]
          exact image_mem_map (hW.mem_nhds hz₀W)
        have hO : IsOpen (interior (g '' W) ∩ Cᶜ) := isOpen_interior.inter hg.1.1.isOpen_compl
        obtain ⟨y, ⟨hyi, hyC⟩, hy⟩ := T.strictlyPsh.2 (g z₀) _ hO
          ⟨mem_interior_iff_mem_nhds.mpr himg, hz₀C⟩
        obtain ⟨z, hzW, rfl⟩ := interior_subset hyi
        refine ⟨z, hzW, ?_⟩
        have hpos : 0 < U (g z) := hU _ hyC
        change (T.potential (g z) - (h (g z) : EReal)) +
          (ε : EReal) * logWeight (fun z => U (g z)) z ≠ ⊥
        rw [logWeight_of_pos (U := fun z => U (g z)) hpos, ← EReal.coe_mul]
        refine EReal.add_ne_bot_iff.mpr ⟨?_, EReal.coe_ne_bot _⟩
        rw [sub_eq_add_neg, ← EReal.coe_neg]
        exact EReal.add_ne_bot_iff.mpr ⟨hy, EReal.coe_ne_bot _⟩ }

theorem pullbackCurrent_potential {θ : ClosedRealOneOneForm n Y}
    (T : KahlerCurrent (RealBottChern.ofRepresentative θ))
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g) {h : Y → ℝ} (hh : ChartSmooth (n := n) h)
    (heq : ∀ (e : ComplexChart n Y) (z : ComplexModel n), z ∈ e.val.target →
      θ.val.coeff e z = T.representative.val.coeff e z + smoothDDC (fun y => h (e.val.symm y)) z)
    {U : Y → ℝ} (hU : ∀ y ∉ C, 0 < U y) (F : WeightFactorization n (fun z => U (g z)))
    {ε : ℝ} (hε : 0 < ε)
    (hK : (ClosedRealOneOneForm.pullback hg.contMDiff T.lowerBound.form +
      ε • F.closedForm).val.IsKahler) (z : Z) :
    (pullbackCurrent T hg hh heq hU F hε hK).potential z =
      (T.potential (g z) - (h (g z) : EReal)) + (ε : EReal) * logWeight (fun z => U (g z)) z :=
  rfl

/-- **The pullback of a big class under one blowup is big.** -/
theorem isBigClass_pullback_of_isBlowupAlong [CompactSpace Y]
    (θ : ClosedRealOneOneForm n Y)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g) :
    IsBigClass (RealBottChern.ofRepresentative
      (ClosedRealOneOneForm.pullback hg.contMDiff θ)) := by
  obtain ⟨T⟩ := hbig
  have := BlowupCompact.compactSpace_of_isBlowupAlong hg
  obtain ⟨D⟩ := BlanchardWeight.exists_blanchardData hg.1
  obtain ⟨F, ε, hε, hK⟩ := BlowupKahler.exists_isKahler_pullback_add T.lowerBound hg D
  obtain ⟨h, hh, heq⟩ := (RealBottChern.ofRepresentative_eq_iff _ _).mp T.represents
  exact ⟨pullbackCurrent T hg hh heq (fun y hy => D.weight_pos_of_notMem hy) F hε hK⟩

end

end Hironaka.BlowupBigPullback
