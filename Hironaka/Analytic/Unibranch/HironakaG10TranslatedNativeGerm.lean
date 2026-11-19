import Hironaka.Analytic.Unibranch.HironakaG10SourceOperatorTranslation
import Hironaka.Coherence.OkaGermBridge
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Filter
open scoped Topology
namespace Hironaka.Analytic.Unibranch.HironakaG10TranslatedNativeGerm
open Hironaka Hironaka
  OkaRelationSheaf OkaGermBridge HolGerm
  Hironaka.Analytic.Unibranch.HironakaG10SourceOperatorTranslation
noncomputable section

theorem germAt_shiftJoint (d t : ℕ) (p : ComplexModel d) (z : ComplexModel t)
    (f : ComplexModel d × ComplexModel t → ℂ) (hf : HolAt f (p,z)) :
    germAt (0,z) (fun x => f (shiftJoint d t p x)) = germAt (p,z) f := by
  have hf' : HolAt (fun x => f (shiftJoint d t p x)) (0,z) := by
    have h : HolAt f (shiftJoint d t p (0,z)) := by simpa [shiftJoint] using hf
    exact h.comp (continuous_shiftJoint d t p) (fun x => differentiable_shiftJoint d t p x)
  rw [germAt_of_holAt hf', germAt_of_holAt hf]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun x => by
    rcases x with ⟨u,v⟩
    simp [shiftJoint]
end
end Hironaka.Analytic.Unibranch.HironakaG10TranslatedNativeGerm
