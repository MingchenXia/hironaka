import Hironaka.Analytic.LocalPotentialPullback
import Hironaka.Analytic.HolomorphicPullback

set_option autoImplicit false

/-!
# Holomorphic pullback of actual global potentials

The raw quasi-PSH statement follows by transporting a target chart germ and
checking the inverse-chart identity on its actual domain. The theta-PSH
statement also transports its full smooth local-potential identity. Nondegeneracy is a
separate condition on the resulting function; in particular, this construction
does not assert that ordinary restriction is the trace of a singular potential.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.GlobalPotentialPullback

open Hironaka.HolomorphicMaps

variable {k n : ℕ} {V M : Type*}
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem manifoldQuasiPlurisubharmonic_comp {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    {u : M → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := n) u) :
    ManifoldQuasiPlurisubharmonic (n := k) (fun x => u (f x)) := by
  intro e z hz
  let d : ComplexChart n M := complexChartAt (f (e.val.symm z))
  have hzD : z ∈ coordinateDomain f e d :=
    ⟨hz, mem_complexChartAt_source (n := n) (f (e.val.symm z))⟩
  have hD := coordinateDomain_isOpen hf e d
  have hp := HolomorphicPullback.quasiPlurisubharmonicAt_comp_holomorphic hD
    (coordinateMap_contDiffOn hf e d) hzD
    (hu d (coordinateMap f e d z) (coordinateMap_mem_target hzD))
  apply hp.congr
  filter_upwards [hD.mem_nhds hzD] with y hy
  change u (d.val.symm (d.val (f (e.val.symm y)))) = u (f (e.val.symm y))
  exact congrArg u (d.val.left_inv hy.2)

/-- A nondegenerate pullback is a global quasi-PSH potential. Nondegeneracy of
the original potential alone is insufficient for this conclusion. -/
theorem isGlobalQuasiPshPotential_comp {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    {u : M → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := n) u)
    (hne : LocallyNondegenerate (fun x => u (f x))) :
    IsGlobalQuasiPshPotential (n := k) (fun x => u (f x)) :=
  ⟨manifoldQuasiPlurisubharmonic_comp hf hu, hne⟩

/-- Corrected target PSH germs and their smooth local potentials pull back
on the same genuine chart domain. No nondegeneracy is asserted here. -/
theorem thetaPlurisubharmonic_comp {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    {θ : SmoothRealForm n M 2} {u : M → EReal} (hu : ThetaPlurisubharmonic θ u) :
    ThetaPlurisubharmonic (SmoothRealForm.pullback hf θ) (fun x => u (f x)) := by
  intro e z hz
  let d := complexChartAt (n := n) (f (e.val.symm z))
  have hzd : z ∈ coordinateDomain f e d := ⟨hz, mem_complexChartAt_source _⟩
  obtain ⟨W, ρ, hzW, hρ, hp⟩ :=
    hu d (coordinateMap f e d z) (coordinateMap_mem_target hzd)
  have hD := LocalPotentialPullback.potentialDomain_isOpen hf e d hρ.1
  refine ⟨LocalPotentialPullback.potentialDomain f e d W, ρ ∘ coordinateMap f e d,
    ⟨hzd, hzW⟩, LocalPotentialPullback.isSmoothLocalPotential_pullback hf e hρ, ?_⟩
  have hpull := HolomorphicPullback.plurisubharmonicOn_comp_holomorphic hD
    (((coordinateMap_contDiffOn hf e d).mono inter_subset_left).differentiableOn
      (by simp)) (fun _ hy => hy.2) hp
  intro y hy
  apply (hpull y hy).congr
  filter_upwards [hD.mem_nhds hy] with w hw
  change u (d.val.symm (d.val (f (e.val.symm w)))) + (ρ (coordinateMap f e d w) : EReal) =
    u (f (e.val.symm w)) + (ρ (coordinateMap f e d w) : EReal)
  rw [d.val.left_inv hw.1.2]

/-- The strong theta-PSH predicate additionally needs a nondegenerate
restricted function; this is not automatic even for a closed embedding. -/
theorem isThetaPshPotential_comp {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    {θ : SmoothRealForm n M 2} {u : M → EReal} (hu : ThetaPlurisubharmonic θ u)
    (hne : LocallyNondegenerate (fun x => u (f x))) :
    IsThetaPshPotential (SmoothRealForm.pullback hf θ) (fun x => u (f x)) :=
  ⟨thetaPlurisubharmonic_comp hf hu, hne⟩

end Hironaka.GlobalPotentialPullback
