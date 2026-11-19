import Hironaka.Analytic.RegularizedMaxSmoothAnalyticType
import Hironaka.Analytic.RegularizedMaxThetaPsh
import Hironaka.Analytic.ThetaPshCollarGluing

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Collar gluing by the regularized maximum

`Hironaka.QuasiEquisingularCollarGluing.isThetaPshPotential_gluedMax` glues a
local theta-PSH branch into a global one with the ORDINARY maximum, under the
collar condition `f ≤ g` off an inner core.  That operation is the reason the
strong CT22 convention needs `ShiftedLaterCoreSeparation` downstream: the
ordinary maximum of two branches presented as `c·log Σ|·|² + smooth` is not of
that form near the crossing locus, so the presentation on an earlier core can
only be preserved by keeping later cores away from it — which, on a connected
manifold, collapses the atlas to one chart (I-0304).

Replacing the maximum by `eregularizedMax` removes that downstream constraint.
The price is a strictly quantitative collar, `f + δ ≤ g` instead of `f ≤ g`;
this is exactly the numerical cutoff gap of Copy-4, and the real-valued collar
data of `Hironaka.ScaledSmoothMaxCollarGluing` already states its collar in that
form.  Under it the glued function is *equal* to the global branch off the core,
so all three local descriptions are germ identities, not comparisons.
-/

open Set Filter
open scoped Topology

namespace Hironaka.RegularizedMaxCollarGluing

open Hironaka
open Hironaka
open Hironaka.AnalyticGluingData
open Hironaka.NumericalRestrictedVolumeScaffold
open Hironaka.RegularizedMaxEReal
open Hironaka.RegularizedMaxPsh
open Hironaka.RegularizedMaxConvexity
open Hironaka.RegularizedMaxERealPshRoute
open Hironaka.RegularizedMaxSmoothAnalyticType
open Hironaka.BoundedGlobalProduct

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A theta-PSH branch on `Ω` never takes the value `⊤` there. -/
theorem ThetaPlurisubharmonicOn.ne_top {θ : SmoothRealForm n M 2} {u : M → EReal}
    {Ω : Set M} (hu : ThetaPlurisubharmonicOn θ u Ω) {x : M} (hx : x ∈ Ω) :
    u x ≠ ⊤ := by
  let e : ComplexChart n M := complexChartAt (n := n) x
  have hxs : x ∈ e.val.source := mem_complexChartAt_source (n := n) x
  have hz : e.val x ∈ e.val.target := e.val.map_source hxs
  have hsymm : e.val.symm (e.val x) = x := e.val.left_inv hxs
  obtain ⟨W, ρ, hzW, hρ, hpsh⟩ := hu e (e.val x) hz (by rw [hsymm]; exact hx)
  have hne := (hpsh _ hzW).ne_top
  intro htop
  apply hne
  change u (e.val.symm (e.val x)) + (ρ (e.val x) : EReal) = ⊤
  rw [hsymm, htop]
  simp

/-- The collar glue: the regularized maximum inside `U`, the global branch
outside. -/
def eregularizedMaxGlued (U : Set M) (δ : ℝ) (f g : M → EReal) : M → EReal := by
  classical
  exact fun x => if x ∈ U then eregularizedMax δ (g x) (f x) else g x

@[simp] theorem eregularizedMaxGlued_of_mem {U : Set M} {δ : ℝ} {f g : M → EReal}
    {x : M} (hx : x ∈ U) :
    eregularizedMaxGlued U δ f g x = eregularizedMax δ (g x) (f x) := by
  simp [eregularizedMaxGlued, hx]

@[simp] theorem eregularizedMaxGlued_of_not_mem {U : Set M} {δ : ℝ} {f g : M → EReal}
    {x : M} (hx : x ∉ U) : eregularizedMaxGlued U δ f g x = g x := by
  simp [eregularizedMaxGlued, hx]

/-- The global branch is never decreased. -/
theorem le_eregularizedMaxGlued {U : Set M} {δ : ℝ} (hδ : 0 < δ) {f g : M → EReal}
    (hftop : ∀ x ∈ U, f x ≠ ⊤) (hgtop : ∀ x, g x ≠ ⊤) (x : M) :
    g x ≤ eregularizedMaxGlued U δ f g x := by
  by_cases hx : x ∈ U
  · rw [eregularizedMaxGlued_of_mem hx]
    exact (le_max_left _ _).trans (max_le_eregularizedMax hδ (hgtop x) (hftop x hx))
  · rw [eregularizedMaxGlued_of_not_mem hx]

/-- **Off the core the glue IS the global branch**, thanks to the scale-`δ`
collar.  With the ordinary maximum this is an inequality turned into an
equality by the collar; here it is an exact germ identity. -/
theorem eregularizedMaxGlued_eq_global {U U' : Set M} {δ : ℝ} (hδ : 0 < δ)
    {f g : M → EReal} (hgap : ∀ x ∈ U \ U', f x + (δ : EReal) ≤ g x)
    (hgtop : ∀ x, g x ≠ ⊤) {x : M} (hx : x ∉ U') :
    eregularizedMaxGlued U δ f g x = g x := by
  by_cases hxU : x ∈ U
  · rw [eregularizedMaxGlued_of_mem hxU]
    exact eregularizedMax_eq_left_of_gap hδ (hgap x ⟨hxU, hx⟩) (hgtop x)
  · exact eregularizedMaxGlued_of_not_mem hxU

theorem eregularizedMaxGlued_eventuallyEq_global {U U' : Set M} {δ : ℝ} (hδ : 0 < δ)
    {f g : M → EReal} (hclosure : closure U' ⊆ U)
    (hgap : ∀ x ∈ U \ U', f x + (δ : EReal) ≤ g x) (hgtop : ∀ x, g x ≠ ⊤)
    {x : M} (hx : x ∉ U) : eregularizedMaxGlued U δ f g =ᶠ[𝓝 x] g := by
  have hx' : x ∈ (closure U')ᶜ := fun hc => hx (hclosure hc)
  filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx'] with y hy
  exact eregularizedMaxGlued_eq_global hδ hgap hgtop (fun h => hy (subset_closure h))


/-! ## The two conclusions -/

/-- **The collar glue is a theta-PSH potential in the SAME background.**  This is
the regularized-max analogue of
`Hironaka.QuasiEquisingularCollarGluing.isThetaPshPotential_gluedMax`, and it
loses no curvature either. -/
theorem isThetaPshPotential_eregularizedMaxGlued
    {θ : SmoothRealForm n M 2} {U U' : Set M} {δ : ℝ} {f g : M → EReal}
    (hδ : 0 < δ) (hU : IsOpen U) (hclosure : closure U' ⊆ U)
    (hgap : ∀ x ∈ U \ U', f x + (δ : EReal) ≤ g x)
    (hf : ThetaPlurisubharmonicOn θ f U)
    (hg : IsThetaPshPotential θ g) :
    IsThetaPshPotential θ (eregularizedMaxGlued U δ f g) := by
  have hgtop : ∀ x, g x ≠ ⊤ := ThetaPlurisubharmonic.ne_top hg.1
  have hftop : ∀ x ∈ U, f x ≠ ⊤ := fun _ hx => ThetaPlurisubharmonicOn.ne_top hf hx
  refine ⟨?_, hg.2.mono (le_eregularizedMaxGlued hδ hftop hgtop)⟩
  intro e z hz
  by_cases hxU : e.val.symm z ∈ U
  · obtain ⟨W, ρ, hzW, hρ, hfpsh⟩ := hf e z hz hxU
    let O : Set (ComplexModel n) := e.val.target ∩ e.val.symm ⁻¹' U
    have hO : IsOpen O :=
      e.val.continuousOn_symm.isOpen_inter_preimage e.val.open_target hU
    have hzO : z ∈ O := ⟨hz, hxU⟩
    let V : Set (ComplexModel n) := W ∩ O
    have hV : IsOpen V := hρ.1.inter hO
    have hzV : z ∈ V := ⟨hzW, hzO⟩
    have hρV : IsSmoothLocalPotential θ e V ρ := hρ.mono hV inter_subset_left
    refine ⟨V, ρ, hzV, hρV, ?_⟩
    have hmain : PlurisubharmonicOn
        (fun y => eregularizedMax δ (chartFunction g e y + (ρ y : EReal))
          (chartFunction f e y + (ρ y : EReal))) V :=
      plurisubharmonicOn_eregularizedMax hδ
        (Hironaka.BoundedGlobalProduct.ThetaPlurisubharmonic.corrected_plurisubharmonicOn hg.1 e hρV)
        (hfpsh.mono inter_subset_left)
    intro y hy
    refine (hmain y hy).congr ?_
    filter_upwards [hV.mem_nhds hy] with w hw
    have hwU : e.val.symm w ∈ U := hw.2.2
    show eregularizedMax δ (chartFunction g e w + (ρ w : EReal))
        (chartFunction f e w + (ρ w : EReal))
      = chartFunction (eregularizedMaxGlued U δ f g) e w + (ρ w : EReal)
    rw [eregularizedMax_add_coe]
    congr 1
    exact (eregularizedMaxGlued_of_mem hwU).symm
  · obtain ⟨W, ρ, hzW, hρ, hgpsh⟩ := hg.1 e z hz
    have hglobal : eregularizedMaxGlued U δ f g =ᶠ[𝓝 (e.val.symm z)] g :=
      eregularizedMaxGlued_eventuallyEq_global hδ hclosure hgap hgtop hxU
    have hchart : chartFunction (eregularizedMaxGlued U δ f g) e =ᶠ[𝓝 z]
        chartFunction g e :=
      hglobal.comp_tendsto (e.val.continuousAt_symm hz)
    obtain ⟨V, hVsub, hV, hzV⟩ := mem_nhds_iff.mp hchart
    let Q : Set (ComplexModel n) := W ∩ V
    have hQ : IsOpen Q := hρ.1.inter hV
    have hzQ : z ∈ Q := ⟨hzW, hzV⟩
    have hρQ : IsSmoothLocalPotential θ e Q ρ := hρ.mono hQ inter_subset_left
    refine ⟨Q, ρ, hzQ, hρQ, ?_⟩
    intro y hy
    refine (hgpsh.mono inter_subset_left y hy).congr ?_
    filter_upwards [hQ.mem_nhds hy] with w hw
    rw [hVsub hw.2]


/-- **The strong CT22 convention survives the collar glue.**  The hypotheses on
the local branch are asked only over `U`, and the alignment only at points of
`U` where BOTH branches are poles.  There is no separation condition, and no
condition relating different charts. -/
theorem hasManifoldSmoothAnalyticSingularities_eregularizedMaxGlued
    {U U' : Set M} {δ : ℝ} {f g : M → EReal}
    (hδ : 0 < δ) (hU : IsOpen U) (hclosure : closure U' ⊆ U)
    (hgap : ∀ x ∈ U \ U', f x + (δ : EReal) ≤ g x) (hgtop : ∀ x, g x ≠ ⊤)
    (hg : HasManifoldSmoothAnalyticSingularities (n := n) g)
    (hf : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      e.val.symm z ∈ U → HasSmoothAnalyticSingularitiesAt (chartFunction f e) z)
    (halign : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      e.val.symm z ∈ U → chartFunction g e z = ⊥ → chartFunction f e z = ⊥ →
        ∃ (c : ℝ) (N : ℕ) (F : Fin N → ComplexModel n → ℂ),
          SmoothLogarithmicTypeAt (chartFunction g e) c F z ∧
          SmoothLogarithmicTypeAt (chartFunction f e) c F z) :
    HasManifoldSmoothAnalyticSingularities (n := n) (eregularizedMaxGlued U δ f g) := by
  intro e z hz
  by_cases hxU : e.val.symm z ∈ U
  · have hO : IsOpen (e.val.target ∩ e.val.symm ⁻¹' U) :=
      e.val.continuousOn_symm.isOpen_inter_preimage e.val.open_target hU
    have heq : chartFunction (eregularizedMaxGlued U δ f g) e =ᶠ[𝓝 z]
        fun y => eregularizedMax δ (chartFunction g e y) (chartFunction f e y) := by
      filter_upwards [hO.mem_nhds ⟨hz, hxU⟩] with w hw
      exact eregularizedMaxGlued_of_mem hw.2
    exact HasSmoothAnalyticSingularitiesAt.congr_eventuallyEq
      (hasSmoothAnalyticSingularitiesAt_eregularizedMax hδ (hg e z hz) (hf e z hz hxU)
        (halign e z hz hxU)) heq
  · have hchart : chartFunction (eregularizedMaxGlued U δ f g) e =ᶠ[𝓝 z]
        chartFunction g e :=
      (eregularizedMaxGlued_eventuallyEq_global hδ hclosure hgap hgtop hxU).comp_tendsto
        (e.val.continuousAt_symm hz)
    exact HasSmoothAnalyticSingularitiesAt.congr_eventuallyEq (hg e z hz) hchart

end

end Hironaka.RegularizedMaxCollarGluing
