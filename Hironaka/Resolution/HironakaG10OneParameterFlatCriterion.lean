import Hironaka.Resolution.HironakaG10OneParameterCokernelFlatness

/-!
# The full actual cokernel criterion over one smooth parameter

Actual `Module.Flat` implies the function-level coordinate regularity
condition on the same germ-matrix cokernel.  Together with Oka coherence
and the exact-fibre criterion this identifies the exact-start predicate
with actual module flatness over the one-variable parameter germ ring.
The base action is the internally constructed first-projection action.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology Matrix

namespace Hironaka.HironakaG10OneParameterFlatCriterion

noncomputable section

open OkaRelationSheaf OkaGermBridge HironakaG10FlatGermChain HironakaG10FlatRelationLift
  HironakaG10FlatSliceResolution
  HironakaG10LocFibreOpen HironakaG10OneVariableFlatness HironakaG10OneParameterCokernelFlatness

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] {a b : ℕ}

/-- Actual parameter flatness gives coordinate regularity of the same
function-level presentation; no scalar-action identification is assumed. -/
theorem regularAt_of_flat_germCokernel (F : Fin a → Fin b → ℂ × P → ℂ) (z₀ : P)
    (hF : ∀ i j, HolAt (F i j) ((0 : ℂ), z₀))
    (hflat : letI : Module (HolGerm ℂ) (germCokernel F z₀) := parameterModule F z₀
      Module.Flat (HolGerm ℂ) (germCokernel F z₀)) :
    RegularAt F (fun x => x.1) ((0 : ℂ), z₀) := by
  let _ : Module (HolGerm ℂ) (germCokernel F z₀) := parameterModule F z₀
  have hinj : Function.Injective (fun q : germCokernel F z₀ => coordinate • q) :=
    flat_iff_coordinate_smul_injective.mp hflat
  have hφ : HolAt (fun x : ℂ × P => x.1) ((0 : ℂ), z₀) :=
    Eventually.of_forall fun _ => differentiableAt_fst
  intro c hc hwc
  have hcv : germAt ((0 : ℂ), z₀) (fun x : ℂ × P => x.1) •
      germVec ((0 : ℂ), z₀) c =
        germVec ((0 : ℂ), z₀) (fun i x => x.1 * c i x) :=
    funext fun i => (germAt_mul hφ (hc i)).symm
  obtain ⟨v, hv⟩ :=
    (isCombinationAt_columns_iff_germ hF (fun i => hφ.mul (hc i))).mp hwc
  have hkill : coordinate •
      (Submodule.Quotient.mk (germVec ((0 : ℂ), z₀) c) : germCokernel F z₀) = 0 := by
    change (Submodule.Quotient.mk
      ((basePullback P coordinate) • germVec ((0 : ℂ), z₀) c) : germCokernel F z₀) = 0
    apply (Submodule.Quotient.mk_eq_zero (germImage F z₀)).mpr
    change ∃ v, germMat ((0 : ℂ), z₀) F *ᵥ v =
      basePullback P coordinate • germVec ((0 : ℂ), z₀) c
    rw [basePullback_coordinate z₀, hcv]
    exact ⟨v, hv⟩
  have hzero : (Submodule.Quotient.mk (germVec ((0 : ℂ), z₀) c) : germCokernel F z₀) = 0 :=
    hinj (by simpa only [smul_zero] using hkill)
  have hmem := (Submodule.Quotient.mk_eq_zero (germImage F z₀)).mp hzero
  apply (isCombinationAt_columns_iff_germ hF hc).mpr
  exact hmem

/-- On a product with one smooth base parameter, the exact-start predicate
is equivalent to actual flatness of its native germ cokernel. -/
theorem fibreFlatAt_iff_flat_germCokernel (hX : OkaProperty (ℂ × P))
    (F : Fin a → Fin b → ℂ × P → ℂ) (z₀ : P)
    (hF : ∀ i j, HolAt (F i j) ((0 : ℂ), z₀)) :
    letI : Module (HolGerm ℂ) (germCokernel F z₀) := parameterModule F z₀
    FibreFlatAt F ((0 : ℂ), z₀) ↔ Module.Flat (HolGerm ℂ) (germCokernel F z₀) := by
  let _ : Module (HolGerm ℂ) (germCokernel F z₀) := parameterModule F z₀
  constructor
  · exact flat_germCokernel_of_fibreFlatAt F z₀
  · intro hflat
    apply (HironakaG10FibreRegularCriterion.fibreFlatAt_iff_coordinate_regular hX F z₀ hF).mpr
    exact regularAt_of_flat_germCokernel F z₀ hF hflat

end

end Hironaka.HironakaG10OneParameterFlatCriterion
