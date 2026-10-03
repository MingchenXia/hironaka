/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.Blowup.BlowupIsomorphismOff
import Hironaka.Invariant.IdealOrderArithmetic
import Hironaka.MarkedIdeal.CodimOneSupport
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.HadamardBridge
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.MarkedIdeal.RestrictedIdealExtension
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The transform of a marked ideal away from the centre

Source: Wlodarczyk 2005 (`wlodarczyk05-hironaka`), §2.1 (the blowup is an isomorphism off the centre, and the
controlled transform is the pullback there) and Proposition `pr:resol` (3)(b) (off the centre the invariants do not
change); Bierstone--Milman 2008, Definition 2.2.

Let `π : Y → X` be the blowup along `C` and `𝔪 = (X, N, E, 𝔞, d)` a marked ideal with `N` closed
and `𝔞` an ideal of holomorphic germs; `𝔪' = 𝔪.geoTransform C π` is the corrected transform.

* `eventually_mem_geoStrictTransform_iff`: off `π⁻¹ C`, `N' = π⁻¹ N` near every point.
* `mem_cosupp_geoTransform_iff` (**the transform away from the centre**): if `π z ∉ C`, then
  `z ∈ cosupp 𝔪' ↔ π z ∈ cosupp 𝔪`.  Forward: the exceptional ideal contains the unit at `z`, so a
  germ of `𝔞'` is a combination along `N'` of pullbacks `a ∘ π`, `a ∈ 𝔞`, and `a = h` on `N` with
  `h ∈ 𝔪^d` gives `a ∘ π = h ∘ π` on `N' ⊆ π⁻¹ N` with `h ∘ π ∈ 𝔪^d`.  Backward: `a ∘ π ∈ 𝔞'`, and
  the holomorphic section `s` of `π` over `X \ C` (`BlowupIsomorphismOff.exists_section_compl`)
  carries `a ∘ π = h` on `N'` back to `a = h ∘ s` on `N`, with `h ∘ s ∈ 𝔪^d` (extended by zero off
  `X \ C`).
* Step 1ba, completed: blowing up the codimension-one part `R` of the support `S` of a marked ideal of maximal
  order, the new support lies over `S \ R`, which has dimension `≤ n - 2` (with `CodimOneSupport`).
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.TransformOffCentre

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder IdealWeightPowers RestrictedIdealExtension RestrictedIdealQuotient InvertibleIdealQuotient BlowupStrictSubmanifold HadamardBridge IdealOrderArithmetic RelativePrincipalizationSpan BlowupControlledTransform

noncomputable section

universe u

/-- **Restricted spans of germs vanishing to order `μ` along `W` vanish to order `μ` along `W`.** -/
theorem IsInSpanOnAt.vanishesToOrderOn {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {W : Set M}
    {S : (M → ℂ) → Prop} {z : M} {g : M → ℂ} {μ : ℕ} (hg : IsInSpanOnAt (n := n) W S z g)
    (hS : ∀ s, S s → VanishesToOrderOn n W z μ s) : VanishesToOrderOn n W z μ g := by
  obtain ⟨K, s, c, hs, hc, hsum⟩ := hg
  obtain ⟨h, hh, hgh⟩ := vanishesToOrderOn_sum_mul (N := W) hc fun k => hS _ (hs k)
  exact ⟨h, hh, by filter_upwards [hsum, hgh] with p hp hp' hpW; rw [hp hpW, hp' hpW]⟩

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- **Off the exceptional divisor the strict transform is the preimage**: if `N` is closed and
`π z ∉ C`, then near `z`, `y ∈ closure (π⁻¹ (N \ C)) ↔ π y ∈ N`. -/
theorem eventually_mem_geoStrictTransform_iff {N : Set X} (hN : IsClosed N) (hC : IsClosed C)
    (hπc : Continuous π) {z : Y} (hz : π z ∉ C) :
    ∀ᶠ y in 𝓝 z, y ∈ geoStrictTransform π C N ↔ π y ∈ N := by
  filter_upwards [(hC.isOpen_compl.preimage hπc).mem_nhds hz] with y hy
  refine ⟨fun h => ?_, fun h => subset_closure ⟨h, hy⟩⟩
  exact closure_minimal (preimage_mono sdiff_subset) (hN.preimage hπc) h

/-- **Forward half**: a point of the cosupport of `𝔪` off the centre lifts to the cosupport of the
transform. -/
theorem mem_cosupp_geoTransform_of_mem_cosupp (𝔪 : MarkedIdeal n X) (hN : IsClosed 𝔪.N)
    (hπ : IsBlowupAlong n C π) {z : Y} (hz : π z ∉ C) (hx : π z ∈ 𝔪.cosupp) :
    z ∈ (𝔪.geoTransform C π).cosupp := by
  have hπc : Continuous π := hπ.contMDiff.continuous
  have hNe := eventually_mem_geoStrictTransform_iff hN hπ.1.1 hπc hz (N := 𝔪.N)
  refine ⟨hNe.self_of_nhds.mpr hx.1, fun f hf => ?_⟩
  have h1 := one_mem_idealPow (n := n) (one_mem_pullback_vanishingIdeal (n := n) (π := π) hz hπ.1.1)
    𝔪.d
  have hres := hf.2 _ h1
  have hres' : IsInSpanOnAt (n := n) (geoStrictTransform π C 𝔪.N)
      ((GermIdeal.pullback (m := n) π 𝔪.ideal).mem z) z f := by
    obtain ⟨K, s, c, hs, hc, hsum⟩ := hres.2
    exact ⟨K, s, c, hs, hc, by filter_upwards [hsum] with y hy hyN; simpa using hy hyN⟩
  refine IsInSpanOnAt.vanishesToOrderOn hres' fun b hb =>
    IsInSpanAt.vanishesToOrderOn (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hb) ?_
  rintro s ⟨a, ha, rfl⟩
  obtain ⟨h, hh, hah⟩ := hx.2 a ha
  refine ⟨h ∘ π, comp_mem_idealPow_pointIdeal
    (Eventually.of_forall fun w => (hπ.contMDiff w).mdifferentiableAt (by simp)) 𝔪.d hh, ?_⟩
  filter_upwards [(hπc.tendsto z).eventually hah, hNe] with y hy hyN hyN'
  exact hy (hyN.mp hyN')

/-- **Backward half**: a point of the cosupport of the transform off the exceptional divisor lies
over the cosupport of `𝔪`. -/
theorem mem_cosupp_of_mem_cosupp_geoTransform (𝔪 : MarkedIdeal n X) (hN : IsClosed 𝔪.N)
    (h𝔞 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x) (hπ : IsBlowupAlong n C π) {z : Y}
    (hz : π z ∉ C) (hz' : z ∈ (𝔪.geoTransform C π).cosupp) : π z ∈ 𝔪.cosupp := by
  have hπc : Continuous π := hπ.contMDiff.continuous
  have hNe := eventually_mem_geoStrictTransform_iff hN hπ.1.1 hπc hz (N := 𝔪.N)
  refine ⟨hNe.self_of_nhds.mp hz'.1, fun a ha => ?_⟩
  have hπat : ∀ᶠ w in 𝓝 z, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π w :=
    Eventually.of_forall fun w => (hπ.contMDiff w).mdifferentiableAt (by simp)
  have haπhol : HolomorphicAt n (a ∘ π) z := holomorphicAt_comp_map hπat (h𝔞 _ _ ha)
  have haπ : (GermIdeal.pullback (m := n) π 𝔪.ideal).mem z (a ∘ π) :=
    isInSpanAt_self (S := fun s => ∃ a', 𝔪.ideal.mem (π z) a' ∧ s = a' ∘ π) ⟨a, ha, rfl⟩ haπhol
  -- `a ∘ π` is a germ of the transformed ideal at `z`
  have hmem : (𝔪.geoTransform C π).ideal.mem z (a ∘ π) := by
    refine ⟨haπhol, fun g hg => ⟨(holomorphicAt_of_mem_idealPow hg).mul haπhol, ?_⟩⟩
    exact ⟨1, fun _ => a ∘ π, fun _ => g, fun _ => haπ, fun _ => holomorphicAt_of_mem_idealPow hg,
      Eventually.of_forall fun y _ => by simp⟩
  obtain ⟨h, hh, hah⟩ := hz'.2 _ hmem
  -- carry `a ∘ π = h` back along the section of `π` over `X \ C`
  obtain ⟨s, hs, hsπ, hsec⟩ := BlowupIsomorphismOff.exists_section_compl hπ
  have hsu : s ⟨π z, hz⟩ = z := hsec z hz
  have hsd : ∀ᶠ w in 𝓝 (⟨π z, hz⟩ : (⟨Cᶜ, hπ.1.1.isOpen_compl⟩ : Opens X)),
      MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) s w :=
    Eventually.of_forall fun w => (hs w).mdifferentiableAt (by simp)
  have h1 : (idealPow (pointIdeal n (s ⟨π z, hz⟩)) 𝔪.d).mem (s ⟨π z, hz⟩) h := by
    rw [hsu]
    exact hh
  have h2 := comp_mem_idealPow_pointIdeal hsd 𝔪.d h1
  have h3 := MarkedIdealRestrictOpen.mem_idealPow_pointIdeal_extendOpens
    (O := (⟨Cᶜ, hπ.1.1.isOpen_compl⟩ : Opens X)) 𝔪.d h2
  refine ⟨extendOpens (⟨Cᶜ, hπ.1.1.isOpen_compl⟩ : Opens X) (h ∘ s), h3, ?_⟩
  have hev : ∀ᶠ w in 𝓝 (⟨π z, hz⟩ : (⟨Cᶜ, hπ.1.1.isOpen_compl⟩ : Opens X)),
      (s w ∈ geoStrictTransform π C 𝔪.N → (a ∘ π) (s w) = h (s w)) ∧
      (s w ∈ geoStrictTransform π C 𝔪.N ↔ π (s w) ∈ 𝔪.N) := by
    have hcont : Filter.Tendsto s (𝓝 ⟨π z, hz⟩) (𝓝 z) := by
      have := hs.continuous.tendsto (⟨π z, hz⟩ : (⟨Cᶜ, hπ.1.1.isOpen_compl⟩ : Opens X))
      rwa [hsu] at this
    exact hcont.eventually (hah.and hNe)
  refine (eventually_nhds_val_iff (⟨Cᶜ, hπ.1.1.isOpen_compl⟩ : Opens X)
    (x := ⟨π z, hz⟩)).mpr ?_
  filter_upwards [hev] with w hw hwN
  have hπs : π (s w) = w.1 := congrFun hsπ w
  have hsN : s w ∈ geoStrictTransform π C 𝔪.N := hw.2.mpr (by rw [hπs]; exact hwN)
  have := hw.1 hsN
  simp only [Function.comp_apply, hπs] at this
  rw [extendOpens_val, Function.comp_apply]
  exact this

/-- **The transform away from the centre**: if `π z ∉ C`, then `z` lies in the cosupport of the
transform if and only if `π z` lies in the cosupport of `𝔪`. -/
theorem mem_cosupp_geoTransform_iff (𝔪 : MarkedIdeal n X) (hN : IsClosed 𝔪.N)
    (h𝔞 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x) (hπ : IsBlowupAlong n C π) {z : Y}
    (hz : π z ∉ C) : z ∈ (𝔪.geoTransform C π).cosupp ↔ π z ∈ 𝔪.cosupp :=
  ⟨mem_cosupp_of_mem_cosupp_geoTransform 𝔪 hN h𝔞 hπ hz,
    mem_cosupp_geoTransform_of_mem_cosupp 𝔪 hN hπ hz⟩

/-- **The cosupport of the transform lies over the cosupport** when the centre lies in it. -/
theorem cosupp_geoTransform_subset_preimage (𝔪 : MarkedIdeal n X) (hN : IsClosed 𝔪.N)
    (h𝔞 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x) (hπ : IsBlowupAlong n C π)
    (hC : C ⊆ 𝔪.cosupp) : (𝔪.geoTransform C π).cosupp ⊆ π ⁻¹' 𝔪.cosupp := by
  intro z hz'
  by_cases hz : π z ∈ C
  · exact hC hz
  · exact mem_cosupp_of_mem_cosupp_geoTransform 𝔪 hN h𝔞 hπ hz hz'

/-- **Along a multiple test blow-up the cosupports lie over the original cosupport** (`N` a closed
submanifold, `𝔞` coherent). -/
theorem cosupp_geoTransformAlong_subset {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower 𝔪 T →
      (geoTransformAlong 𝔪 T).cosupp ⊆ T.proj ⁻¹' 𝔪.cosupp
  | _, .refl, _ => by simp
  | _, .step T C π hπ, hT => by
      obtain ⟨hTT, hC⟩ := hT
      obtain ⟨hNT, hcT⟩ :=
        MarkedIdealRestrictOpen.isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hTT
      have ih := cosupp_geoTransformAlong_subset 𝔪 hN h𝔞 T hTT
      rw [geoTransformAlong_step, BlowupTower.proj_step]
      intro z hz
      exact ih (cosupp_geoTransform_subset_preimage _ hNT.1
        (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcT hg) hπ hC.2.1 hz)

end

end Hironaka.TransformOffCentre
