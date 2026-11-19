import Hironaka.Analytic.BoundedGlobalTruncation
import Hironaka.Analytic.AnalyticGluingData

set_option autoImplicit false

/-!
# Collar gluing for theta-plurisubharmonic potentials

This is the analytic gluing operation required by the finite-atlas stage of
regularization.  A theta-PSH branch defined on an open set is joined to a
global theta-PSH branch by a maximum, provided the local branch is below the
global branch on an explicit collar.  The proof works chartwise: inside the
open set the glued function is a local maximum, whereas outside it agrees
with the global branch on a neighbourhood.
-/

open Set Filter
open scoped Topology

namespace Hironaka.QuasiEquisingularCollarGluing


open Hironaka.AnalyticGluingData
open BoundedGlobalProduct

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- An explicit collar maximum globalizes a local theta-PSH branch.  The
collar condition ensures that no new boundary singularity is created, and the
global branch supplies local nondegeneracy. -/
theorem isThetaPshPotential_gluedMax
    {θ : SmoothRealForm n M 2} {U U' : Set M} {f g : M → EReal}
    (hU : IsOpen U) (hclosure : closure U' ⊆ U)
    (hcollar : ∀ x ∈ U \ U', f x ≤ g x)
    (hf : ThetaPlurisubharmonicOn θ f U)
    (hg : IsThetaPshPotential θ g) :
    IsThetaPshPotential θ (gluedMax U f g) := by
  refine ⟨?_, hg.2.mono ?_⟩
  · intro e z hz
    let x : M := e.val.symm z
    by_cases hxU : x ∈ U
    · obtain ⟨W, ρ, hzW, hρ, hfpsh⟩ := hf e z hz hxU
      let O : Set (ComplexModel n) := e.val.target ∩ e.val.symm ⁻¹' U
      have hO : IsOpen O := e.val.continuousOn_symm.isOpen_inter_preimage
        e.val.open_target hU
      have hzO : z ∈ O := ⟨hz, hxU⟩
      let V : Set (ComplexModel n) := W ∩ O
      have hV : IsOpen V := hρ.1.inter hO
      have hzV : z ∈ V := ⟨hzW, hzO⟩
      have hρV : IsSmoothLocalPotential θ e V ρ :=
        hρ.mono hV inter_subset_left
      refine ⟨V, ρ, hzV, hρV, ?_⟩
      have hmax : PlurisubharmonicOn
          (fun y => max (chartFunction f e y + (ρ y : EReal))
            (chartFunction g e y + (ρ y : EReal))) V :=
        (hfpsh.mono inter_subset_left).max
          (ThetaPlurisubharmonic.corrected_plurisubharmonicOn hg.1 e hρV)
      intro y hy
      refine (hmax y hy).congr ?_
      filter_upwards [hV.mem_nhds hy] with w hw
      have hwU : e.val.symm w ∈ U := hw.2.2
      change max (f (e.val.symm w) + (ρ w : EReal))
          (g (e.val.symm w) + (ρ w : EReal)) =
        gluedMax U f g (e.val.symm w) + (ρ w : EReal)
      rw [gluedMax_eq_max hwU]
      exact (max_add _ _ _).symm
    · obtain ⟨W, ρ, hzW, hρ, hgpsh⟩ := hg.1 e z hz
      have hxnot : x ∉ U := hxU
      have hglobal : gluedMax U f g =ᶠ[𝓝 x] g :=
        gluedMax_eventually_eq_global hclosure hcollar hxnot
      have hchart : chartFunction (gluedMax U f g) e =ᶠ[𝓝 z]
          chartFunction g e := by
        change (gluedMax U f g ∘ e.val.symm) =ᶠ[𝓝 z] (g ∘ e.val.symm)
        exact hglobal.comp_tendsto (e.val.continuousAt_symm hz)
      obtain ⟨V, hVsub, hV, hzV⟩ := mem_nhds_iff.mp hchart
      let Q : Set (ComplexModel n) := W ∩ V
      have hQ : IsOpen Q := hρ.1.inter hV
      have hzQ : z ∈ Q := ⟨hzW, hzV⟩
      have hρQ : IsSmoothLocalPotential θ e Q ρ :=
        hρ.mono hQ inter_subset_left
      refine ⟨Q, ρ, hzQ, hρQ, ?_⟩
      intro y hy
      refine (hgpsh.mono inter_subset_left y hy).congr ?_
      filter_upwards [hQ.mem_nhds hy] with w hw
      rw [hVsub hw.2]
  · intro x
    classical
    by_cases hxU : x ∈ U
    · rw [gluedMax_eq_max hxU]
      exact le_max_right _ _
    · simp [gluedMax, hxU]

end

end Hironaka.QuasiEquisingularCollarGluing
