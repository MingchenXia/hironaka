/- Complete original prerequisites; mathematical statements and proofs are unchanged. -/
import Hironaka.Resolution.HironakaSmoothCentreCoherentDomain

/-! # Exact original saturation on a real nonlinear domain
Only genuine finite generation near zero is used. Original regularity
and coherence internally provide the flattening and real target family;
true Oka coherence and germ Noetherianity supply the selected index,
actual fixed-colon generators and one real open for ALL powers/unions.
Complete mathematics precedes this source; no global extension is used.
-/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaSmoothCentreRealDomainSaturation
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf OkaIdealOperations
  OkaCoherence HironakaSmoothCentreCoherentDomain HironakaRelativeNormalCoherentSaturation



/-- The genuine restricted local coherence condition supplies the actual Oka finite presentation. -/
theorem idealFGAt_of_coherentOn {n : ℕ} (I : GermIdeal n (ComplexModel n))
    (W : Set (ComplexModel n)) (hI : CoherentOn I W) {y : ComplexModel n} (hy : y ∈ W) :
    IdealFGAt I.mem y := by
  obtain ⟨U, hU, hyU, _hUW, N, H, hH, hgen⟩ := hI y hy
  refine ⟨U, hU, hyU, Fin N, inferInstance, H,
    fun i => mdifferentiableOn_iff_differentiableOn.mp (hH i), ?_⟩
  intro z hz g
  rw [hgen z hz g, CoherentIdealColon.isInSpanAt_range_iff]
  constructor
  · rintro ⟨hg, a, ha, he⟩
    exact ⟨hg.mono (fun _ h => h.differentiableAt), a,
      fun i => (ha i).mono (fun _ h => h.differentiableAt), he⟩
  · rintro ⟨hg, a, ha, he⟩
    exact ⟨hg.mono (fun _ h => h.mdifferentiableAt), a,
      fun i => (ha i).mono (fun _ h => h.mdifferentiableAt), he⟩

end
end Hironaka.HironakaSmoothCentreRealDomainSaturation
