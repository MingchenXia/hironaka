import Hironaka.Resolution.HironakaG10OneVariableFlatness
import Hironaka.Resolution.HironakaG10FibreRegularCriterion
import Hironaka.Resolution.HironakaG10FlatKoszulExact
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Actual flatness of the native presentation cokernel over one parameter

The module is the actual quotient by the image of the germ matrix at `(0,z₀)`.
Its parameter action is obtained internally from the genuine first-projection
map `HolGerm ℂ → HolGerm (ℂ × P)`.  Coordinate regularity, and hence the
one-parameter exact-fibre criterion, implies actual `Module.Flat` over that
parameter ring.  No comparison of scalar actions is a caller premise.
This proves the implication for a one-dimensional smooth base only.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology Matrix

namespace Hironaka.HironakaG10OneParameterCokernelFlatness

noncomputable section

open OkaRelationSheaf OkaGermBridge HironakaG10FlatGermChain HironakaG10FlatKoszulExact
  HironakaG10FlatSliceResolution HironakaG10LocFibreOpen HironakaG10OneVariableFlatness

variable (P : Type*) [NormedAddCommGroup P] [NormedSpace ℂ P]

/-- The actual pullback of base germs through the first projection. -/
def basePullback : HolGerm ℂ →+* HolGerm (ℂ × P) :=
  HolGerm.comap (ContinuousLinearMap.fst ℂ ℂ P)

variable {P}

/-- Translation to `(0,z₀)` changes only the fibre origin, so the actual
pullback of the base coordinate is precisely the first-coordinate germ. -/
theorem basePullback_coordinate (z₀ : P) :
    basePullback P coordinate = germAt ((0 : ℂ), z₀) (fun x : ℂ × P => x.1) := by
  have hφ : HolAt (fun x : ℂ × P => x.1) ((0 : ℂ), z₀) :=
    Eventually.of_forall fun _ => differentiableAt_fst
  rw [basePullback, coordinate, HolGerm.comap_mk, germAt_of_holAt hφ]
  apply HolGerm.mk_eq_mk_iff.mpr
  filter_upwards with x
  change x.1 = (0 : ℂ) + x.1
  exact (zero_add x.1).symm

variable {a b : ℕ}

/-- The actual image of the finite matrix of germs at `(0,z₀)`. -/
def germImage (F : Fin a → Fin b → ℂ × P → ℂ) (z₀ : P) :
    Submodule (HolGerm (ℂ × P)) (Fin a → HolGerm (ℂ × P)) :=
  LinearMap.range (germMat ((0 : ℂ), z₀) F).mulVecLin

/-- The genuine stalk presentation cokernel, using the original matrix. -/
abbrev germCokernel (F : Fin a → Fin b → ℂ × P → ℂ) (z₀ : P) : Type _ :=
  (Fin a → HolGerm (ℂ × P)) ⧸ germImage F z₀

/-- The parameter-module structure is restriction through the actual first
projection; this is constructed rather than supplied as an identification. -/
@[instance_reducible] def parameterModule (F : Fin a → Fin b → ℂ × P → ℂ) (z₀ : P) :
    Module (HolGerm ℂ) (germCokernel F z₀) :=
  Module.compHom (germCokernel F z₀) (basePullback P)

/-- Coordinate regularity of the presented germ module gives actual flatness
of its native cokernel over the one-variable analytic parameter ring. -/
theorem flat_germCokernel_of_regularAt (F : Fin a → Fin b → ℂ × P → ℂ) (z₀ : P)
    (hF : ∀ i j, HolAt (F i j) ((0 : ℂ), z₀))
    (hreg : RegularAt F (fun x => x.1) ((0 : ℂ), z₀)) :
    letI : Module (HolGerm ℂ) (germCokernel F z₀) := parameterModule F z₀
    Module.Flat (HolGerm ℂ) (germCokernel F z₀) := by
  let _ : Module (HolGerm ℂ) (germCokernel F z₀) := parameterModule F z₀
  have hφ : HolAt (fun x : ℂ × P => x.1) ((0 : ℂ), z₀) :=
    Eventually.of_forall fun _ => differentiableAt_fst
  have hz : ∀ q : germCokernel F z₀, coordinate • q = 0 → q = 0 := by
    intro q
    refine Submodule.Quotient.induction_on (germImage F z₀) q ?_
    intro c hc
    change (Submodule.Quotient.mk ((basePullback P coordinate) • c) :
      germCokernel F z₀) = 0 at hc
    have hm := (Submodule.Quotient.mk_eq_zero (germImage F z₀)).mp hc
    change ∃ v, germMat ((0 : ℂ), z₀) F *ᵥ v = basePullback P coordinate • c at hm
    rw [basePullback_coordinate z₀] at hm
    obtain ⟨v, hv⟩ := regular_germ hF hφ hreg c hm
    apply (Submodule.Quotient.mk_eq_zero (germImage F z₀)).mpr
    exact ⟨v, hv⟩
  apply flat_iff_coordinate_smul_injective.mpr
  intro x y hxy
  change coordinate • x = coordinate • y at hxy
  apply sub_eq_zero.mp
  apply hz
  rw [smul_sub]
  exact sub_eq_zero.mpr hxy

/-- For one smooth parameter, the exact-start predicate implies actual
flatness of the same germ-matrix cokernel with its actual base action. -/
theorem flat_germCokernel_of_fibreFlatAt (F : Fin a → Fin b → ℂ × P → ℂ) (z₀ : P)
    (h : FibreFlatAt F ((0 : ℂ), z₀)) :
    letI : Module (HolGerm ℂ) (germCokernel F z₀) := parameterModule F z₀
    Module.Flat (HolGerm ℂ) (germCokernel F z₀) := by
  let _ : Module (HolGerm ℂ) (germCokernel F z₀) := parameterModule F z₀
  obtain ⟨c, G, U, hU, hpU, hstart, hfib⟩ := h
  have hF : ∀ i j, HolAt (F i j) ((0 : ℂ), z₀) :=
    fun i j => holAt_of_differentiableOn hU (hstart.holF i j) hpU
  exact flat_germCokernel_of_regularAt F z₀ hF
    ((HironakaG10FibreRegularCriterion.slice_exact_iff_regularAt hstart hU hpU).mp hfib)

end

end Hironaka.HironakaG10OneParameterCokernelFlatness
