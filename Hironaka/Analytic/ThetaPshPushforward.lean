import Hironaka.Analytic.HolomorphicLocalInverse
import Hironaka.Analytic.ThetaPshCodimTwoExtension
import Hironaka.Analytic.LocalPotentialPullback
import Hironaka.Analytic.PotentialTheory.LocalPotentialsBasic
import Hironaka.Analytic.ClosedFormPullback
import Hironaka.Analytic.PotentialTheory.LocalPotentials

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Pushing theta-plurisubharmonic functions forward along an unramified map

Let `g : Z → Y` be holomorphic, `E ⊆ Y` a set with `g z ∉ E → z ∉ Exc g`, and `s : Y → Z` with
`s (g z) = z` whenever `g z ∉ E`.  Let `w` be `θ_Z`-plurisubharmonic on `Z` and `r : Z → ℝ` a local
potential of `θ_Z - g^* θ_Y` near every point off `g⁻¹ E`.  Then `(w + r) ∘ s` is
`θ_Y`-plurisubharmonic off `E` (`thetaPshOff_comp_section`).

Near `y ∉ E` take a holomorphic local inverse `σ` of `g` at `s y`.  In a chart of `Z`,
`w + ρ_Y ∘ g + r` is plurisubharmonic (`ρ_Y ∘ g + r` is a local potential of `θ_Z`), and composing
with the coordinate expression of `σ` gives `(w + r) ∘ σ + ρ_Y` in the chart of `Y`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.ThetaPshPushforward

open Hironaka Hironaka.HolomorphicMaps Hironaka.BlowupSequences ThetaPshCodimTwoExtension
  HolomorphicLocalInverse

noncomputable section

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

/-- **Pushforward of a theta-PSH function along an unramified map.** -/
theorem thetaPshOff_comp_section {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g) {E : Set Y} (hEc : IsClosed E)
    (hE : ∀ z, g z ∉ E → z ∉ exceptionalLocus n g) {s : Y → Z}
    (hsg : ∀ z, g z ∉ E → s (g z) = z) (hgs : ∀ y ∉ E, g (s y) = y)
    {θY : ClosedRealOneOneForm n Y} {θZ : ClosedRealOneOneForm n Z} {w : Z → EReal}
    (hw : ThetaPlurisubharmonic θZ.val w) {r : Z → ℝ}
    (hr : ∀ z, g z ∉ E → ∀ eZ : ComplexChart n Z, z ∈ eZ.val.source →
      ∃ W : Set (ComplexModel n), eZ.val z ∈ W ∧
        IsSmoothLocalPotential (θZ - ClosedRealOneOneForm.pullback hg θY).val eZ W
          (fun ζ => r (eZ.val.symm ζ))) :
    ThetaPshOff θY.val E (fun y => w (s y) + (r (s y) : EReal)) := by
  intro e b hb hbE
  set y := e.val.symm b
  set z := s y
  have hgz : g z = y := hgs y hbE
  have hzE : g z ∉ E := by rw [hgz]; exact hbE
  have hzexc := hE z hzE
  obtain ⟨V, σ, hV, hgzV, hσz, hgσ, hσs, -⟩ := exists_localInverse hg hzexc
  rw [hgz] at hgzV hσz
  set eZ := complexChartAt (n := n) z
  have hzeZ : z ∈ eZ.val.source := mem_complexChartAt_source z
  -- a local potential of `θ_Y` at `b`
  obtain ⟨WY, ρ, hbWY, hρ⟩ := (LocalPotentials.closedRealOneOne_hasLocalPotentials θY) e b hb
  -- the potential `ρ ∘ g + r` of `θ_Z` near `eZ z`
  have hgzt : g (eZ.val.symm (eZ.val z)) ∈ e.val.source := by
    rw [eZ.val.left_inv hzeZ, hgz]; exact e.val.map_target hb
  have hzdom : eZ.val z ∈ coordinateDomain g eZ e := ⟨eZ.val.map_source hzeZ, hgzt⟩
  have hρpull := LocalPotentialPullback.isSmoothLocalPotential_pullback hg eZ hρ
  have hcoord : coordinateMap g eZ e (eZ.val z) = b := by
    show e.val (g (eZ.val.symm (eZ.val z))) = b
    rw [eZ.val.left_inv hzeZ, hgz]; exact e.val.right_inv hb
  obtain ⟨Wr, hzWr, hrpot⟩ := hr z hzE eZ hzeZ
  -- the potential `ρ ∘ g + r` of `θ_Z` and the plurisubharmonic germ of `w` in `eZ`
  set W₁ := LocalPotentialPullback.potentialDomain g eZ e WY ∩ Wr
  have hW₁ : IsOpen W₁ := hρpull.1.inter hrpot.1
  have hzW₁ : eZ.val z ∈ W₁ := ⟨⟨hzdom, by rw [mem_preimage, hcoord]; exact hbWY⟩, hzWr⟩
  have hρZ : IsSmoothLocalPotential θZ.val eZ W₁
      (fun ζ => (ρ ∘ coordinateMap g eZ e) ζ + r (eZ.val.symm ζ)) := by
    have h := Hironaka.LocalPotentials.localPotential_add
      (a := ClosedRealOneOneForm.pullback hg θY) (b := θZ - ClosedRealOneOneForm.pullback hg θY)
      (hρpull.mono hW₁ inter_subset_left) (hrpot.mono hW₁ inter_subset_right)
    rwa [add_sub_cancel] at h
  obtain ⟨W₂, σ₂, hzW₂, hσ₂, hpsh₂⟩ := hw eZ (eZ.val z) (eZ.val.map_source hzeZ)
  set W₃ := W₁ ∩ W₂
  have hW₃ : IsOpen W₃ := hW₁.inter hσ₂.1
  have hP : PlurisubharmonicOn (fun ζ => chartFunction w eZ ζ +
      (((ρ ∘ coordinateMap g eZ e) ζ + r (eZ.val.symm ζ) : ℝ) : EReal)) W₃ :=
    (_root_.Hironaka.PotentialTheory.GlobalPotentials.smoothLocalPotential_psh_iff θZ.val eZ W₃ σ₂ _ (hσ₂.mono hW₃ inter_subset_right)
      (hρZ.mono hW₃ inter_subset_left) (chartFunction w eZ)).1 (hpsh₂.mono inter_subset_right)
  -- the coordinate expression of the local inverse
  have hσc : ContinuousOn σ V := fun y' hy' => (hσs y' hy').continuousAt.continuousWithinAt
  set N₀ := e.val.target ∩ e.val.symm ⁻¹' ((V ∩ σ ⁻¹' eZ.val.source) ∩ Eᶜ)
  have hN₀ : IsOpen N₀ :=
    e.val.isOpen_inter_preimage_symm ((hσc.isOpen_inter_preimage hV eZ.val.open_source).inter
      hEc.isOpen_compl)
  set Gc : ComplexModel n → ComplexModel n := fun ζ => eZ.val (σ (e.val.symm ζ))
  have hGcd : ∀ ζ ∈ N₀, DifferentiableAt ℂ Gc ζ := fun ζ hζ => by
    have h1 : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.val.symm ζ :=
      contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas e.property) hζ.1
    have h3 : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ eZ.val (σ (e.val.symm ζ)) :=
      (contMDiffOn_chart (n := ∞)).contMDiffAt (eZ.val.open_source.mem_nhds hζ.2.1.2)
    have h := h3.comp ζ ((hσs _ hζ.2.1.1).comp ζ h1)
    exact (contMDiffAt_iff_contDiffAt.mp h).differentiableAt (by simp)
  have hGcc : ContinuousOn Gc N₀ := fun ζ hζ => (hGcd ζ hζ).continuousAt.continuousWithinAt
  set N := N₀ ∩ Gc ⁻¹' W₃
  have hN : IsOpen N := hGcc.isOpen_inter_preimage hN₀ hW₃
  have hbN : b ∈ N := by
    refine ⟨⟨hb, ⟨hgzV, ?_⟩, hbE⟩, ?_⟩
    · show σ y ∈ eZ.val.source; rw [hσz]; exact hzeZ
    · show eZ.val (σ y) ∈ W₃; rw [hσz]; exact ⟨hzW₁, hzW₂⟩
  have hcomp : PlurisubharmonicOn (fun ζ => chartFunction w eZ (Gc ζ) +
      (((ρ ∘ coordinateMap g eZ e) (Gc ζ) + r (eZ.val.symm (Gc ζ)) : ℝ) : EReal)) N :=
    HolomorphicPullback.plurisubharmonicOn_comp_holomorphic hN
      (fun ζ hζ => (hGcd ζ hζ.1).differentiableWithinAt) (fun ζ hζ => hζ.2) hP
  set W := N ∩ WY
  have hW : IsOpen W := hN.inter hρ.1
  refine ⟨W, ρ, ⟨hbN, hbWY⟩, hρ.mono hW inter_subset_right, fun ζ hζ => ?_⟩
  refine (hcomp ζ hζ.1).congr ?_
  filter_upwards [hW.mem_nhds hζ] with ζ' hζ'
  obtain ⟨⟨⟨hζt, ⟨hζV, hζs⟩, hζE⟩, -⟩, -⟩ := hζ'
  set z' := σ (e.val.symm ζ')
  have hsymm : eZ.val.symm (Gc ζ') = z' := eZ.val.left_inv hζs
  have hgz' : g z' = e.val.symm ζ' := hgσ _ hζV
  have hco : coordinateMap g eZ e (Gc ζ') = ζ' := by
    show e.val (g (eZ.val.symm (Gc ζ'))) = ζ'
    rw [hsymm, hgz', e.val.right_inv hζt]
  have hsz' : s (e.val.symm ζ') = z' := by
    rw [← hgz']; exact hsg z' (by rw [hgz']; exact hζE)
  simp only [chartFunction, Function.comp_apply, hco, hsymm, hsz']
  rw [EReal.coe_add, add_comm ((ρ ζ' : ℝ) : EReal), add_assoc]

end

end Hironaka.ThetaPshPushforward
