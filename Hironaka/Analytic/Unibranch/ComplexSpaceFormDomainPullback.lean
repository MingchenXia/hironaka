import Hironaka.Analytic.Unibranch.ComplexSpaceThetaPSH
import Hironaka.Analytic.FormPullback

/-! Genuine smooth-form pullback along actual domain morphisms into the
ORIGINAL singular reduced complex space, retaining its original SpaceForm.
Blueprint: complex-space-form-domain-pullback.tex. No smooth-target proxy,
PSH/descent certificate, resolution or Hironaka construction is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology ContDiff
open Hironaka
open Hironaka.HironakaReducedComplexAnalyticSpaces
namespace Hironaka.Analytic.Unibranch

private theorem pullbackForm_germ_congr {m N k : ℕ}
    {F G : ComplexModel m → ComplexModel N} {z : ComplexModel m}
    (h : F =ᶠ[𝓝 z] G) (v : AmbientForm N k) :
    pullbackForm F v z = pullbackForm G v z := by
  simp only [pullbackForm,h.self_of_nhds,h.fderiv_eq]

namespace SpaceForm
variable {X : SourceReducedComplexSpace} {k m : ℕ}
  (θ : SpaceForm X k) {U : Opens (ComplexModel m)}
  (F : domainSpace U ⟶ X)

/-- Primitive actual local coordinates of the SAME locally ringed-space
morphism. Every field describes the original holomorphic lift, with no
form equality, smooth pullback or PSH conclusion included. -/
structure DomainLift (x : U) where
  chart : θ.ι
  window : Set (ComplexModel m)
  isOpen : IsOpen window
  mem : x.val ∈ window
  subset : window ⊆ U
  lift : ComplexModel m → ComplexModel (θ.chart chart).dim
  holomorphic : ContDiffOn ℂ ∞ lift window
  maps : MapsTo lift window (θ.chart chart).ambient
  factor : ∀ y : (univ : Set U), y.val.val ∈ window →
    ∃ c : (θ.chart chart).carrier, c.val.val = lift y.val.val ∧
      (θ.chart chart).toPoint c = F.hom.left.base y

/-- Genuine existing source-morphism factorization produces the actual
local lift; no lift/compatibility/pullback certificate is supplied. -/
theorem domainLift_nonempty (x : U) : Nonempty (DomainLift θ F x) := by
  let y : (univ : Set U) := ⟨x,trivial⟩
  obtain ⟨i,hi⟩ := θ.covers (F.hom.left.base y)
  obtain ⟨W,hW,hxW,hWU,G,hG,hmaps,hfac⟩ :=
    LocalEmbedding.exists_contDiffOn_factor F.hom.left (Over.w F.hom) (θ.chart i) y hi
  exact ⟨⟨i,W,hW,hxW,hWU,G,hG,hmaps,hfac⟩⟩

namespace DomainLift
variable {θ F}

/-- The actual local alternating tensor is genuinely smooth on its window. -/
theorem pullback_smooth {x : U} (A : DomainLift θ F x) :
    ContDiffOn ℝ ∞ (pullbackForm A.lift (θ.rep A.chart)) A.window := by
  apply SmoothRealForm.contDiffOn_compContinuousLinearMap
  · exact (θ.smooth A.chart).comp (A.holomorphic.restrict_scalars ℝ) A.maps
  · exact (A.holomorphic.restrict_scalars ℝ).fderiv_of_isOpen A.isOpen (by simp)

/-- Actual original singular-chart compatibility and actual morphism lifts
produce pullback independence on the literal source overlap. -/
theorem pullback_eq {x y : U} (A : DomainLift θ F x) (B : DomainLift θ F y)
    {z : ComplexModel m} (hzA : z ∈ A.window) (hzB : z ∈ B.window) :
    pullbackForm A.lift (θ.rep A.chart) z = pullbackForm B.lift (θ.rep B.chart) z := by
  let p : (univ : Set U) := ⟨⟨z,A.subset hzA⟩,trivial⟩
  obtain ⟨a,ha,hpa⟩ := A.factor p hzA
  obtain ⟨b,hb,hpb⟩ := B.factor p hzB
  change a.val.val = A.lift z at ha
  obtain ⟨W,H,haW,hH⟩ := (θ.chart A.chart).exists_isTransition (θ.chart B.chart) a
    ⟨b,hpb.trans hpa.symm⟩
  let D : Set (ComplexModel m) := (A.window ∩ A.lift ⁻¹' W) ∩ B.window
  have hD : IsOpen D :=
    (A.holomorphic.continuousOn.isOpen_inter_preimage A.isOpen hH.1).inter B.isOpen
  have hzD : z ∈ D := ⟨⟨hzA,by change A.lift z ∈ W; rw [← ha]; exact haW⟩,hzB⟩
  have hmaps : ∀ w ∈ D, A.lift w ∈ W ∧
      ∃ c : (θ.chart A.chart).carrier, c.val.val = A.lift w := by
    intro w hw
    obtain ⟨c,hc,-⟩ := A.factor ⟨⟨w,A.subset hw.1.1⟩,trivial⟩ hw.1.1
    exact ⟨hw.1.2,c,hc⟩
  have hvan := θ.compatible A.chart B.chart W H hH m D A.lift hD
    ((A.holomorphic.differentiableOn (by simp)).mono (fun _ hw => hw.1.1)) hmaps z hzD
  rw [pullbackForm_sub,Pi.sub_apply,sub_eq_zero] at hvan
  have heq : (H ∘ A.lift) =ᶠ[𝓝 z] B.lift := by
    filter_upwards [hD.mem_nhds hzD] with w hw
    let q : (univ : Set U) := ⟨⟨w,A.subset hw.1.1⟩,trivial⟩
    obtain ⟨a',ha',hpa'⟩ := A.factor q hw.1.1
    obtain ⟨b',hb',hpb'⟩ := B.factor q hw.2
    obtain ⟨c,hc,hpc⟩ := hH.2.2.2.2 a' (by rw [ha']; exact hw.1.2)
    have hcb : c = b' := (θ.chart B.chart).toPoint_injective
      (hpc.trans (hpa'.trans hpb'.symm))
    change H (A.lift w) = B.lift w
    rw [← ha',← hc,hcb,hb']
  have hAr : DifferentiableAt ℝ A.lift z :=
    ((A.holomorphic.differentiableOn (by simp)).differentiableAt
      (A.isOpen.mem_nhds hzA)).restrictScalars ℝ
  have hHr : DifferentiableAt ℝ H (A.lift z) :=
    (hH.2.2.1.differentiableAt (hH.1.mem_nhds hzD.1.2)).restrictScalars ℝ
  exact hvan.trans ((pullbackForm_comp hAr hHr (θ.rep B.chart)).trans
    (pullbackForm_germ_congr heq (θ.rep B.chart)))

end DomainLift

/-- Actual tensor field pulled back from the ORIGINAL singular complex
space by the SAME original domain morphism. Chosen actual lifts are
proved independent below; the arbitrary outside-domain extension is zero. -/
def pullbackToDomain : AmbientForm m k := by
  classical
  exact fun z =>
    if hz : z ∈ U then
      let A := Classical.choice (domainLift_nonempty θ F ⟨z,hz⟩)
      pullbackForm A.lift (θ.rep A.chart) z
    else 0

/-- Literal readback on EVERY actual ambient lift, no agreement premise. -/
theorem pullbackToDomain_eq {x : U} (A : DomainLift θ F x)
    {z : ComplexModel m} (hz : z ∈ A.window) :
    pullbackToDomain θ F z = pullbackForm A.lift (θ.rep A.chart) z := by
  have hzU := A.subset hz
  unfold pullbackToDomain
  split_ifs with h
  · exact (Classical.choice (domainLift_nonempty θ F ⟨z,hzU⟩)).pullback_eq A
      (Classical.choice (domainLift_nonempty θ F ⟨z,hzU⟩)).mem hz
  · exact (h hzU).elim

/-- The manufactured actual pullback is smooth on the ENTIRE original
source domain even when the target X is singular. No smoothness input
about X or a desired output tensor field is assumed. -/
theorem pullbackToDomain_smooth : ContDiffOn ℝ ∞ (pullbackToDomain θ F) U := by
  intro z hz
  let A := Classical.choice (domainLift_nonempty θ F ⟨z,hz⟩)
  have heq : pullbackToDomain θ F =ᶠ[𝓝 z] pullbackForm A.lift (θ.rep A.chart) := by
    filter_upwards [A.isOpen.mem_nhds A.mem] with w hw
    exact pullbackToDomain_eq θ F A hw
  exact ((A.pullback_smooth.contDiffAt (A.isOpen.mem_nhds A.mem)).congr_of_eventuallyEq
    heq).contDiffWithinAt

end SpaceForm
end Hironaka.Analytic.Unibranch
