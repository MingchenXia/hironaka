import Hironaka.Resolution.HironakaG1RelativeBoundaryUnitLifts
import Mathlib.Geometry.Manifold.Submersion
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Actual unit-ratio ambient projections

Concrete finite product complex vector spaces carry actual source charts;
both projections are genuine chart-form submersions. The whole coordinate
germ identity is multiplication by an actual unit. No graph of two given
native embeddings or common GIVEN-Q presentation is assumed or exported.

Blueprint FIRST: `hironaka-g1-relative-boundary-projections.tex`.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1RelativeBoundaryProjections

noncomputable section

/-- Finite complex coordinate block with its ordinary product norm. -/
abbrev Block (r : ℕ) := Fin r → ℂ

/-- Actual coordinates: active x, ratio z, other x, other y. -/
abbrev Ambient (r a b : ℕ) := (Block r × Block r) × (Block a × Block b)

def unitLocus (r a b : ℕ) : Set (Ambient r a b) := {p | ∀ i, p.1.2 i ≠ 0}

theorem isOpen_unitLocus (r a b : ℕ) : IsOpen (unitLocus r a b) := by
  have hU : unitLocus r a b = ⋂ i : Fin r, {p : Ambient r a b | p.1.2 i ≠ 0} := by
    ext p
    simp only [unitLocus, mem_ofPred_eq, mem_iInter]
  rw [hU]
  exact isOpen_iInter_of_finite fun _ => isOpen_ne_fun (by fun_prop) continuous_const

def unitScaling (r a b : ℕ) (p : Ambient r a b) : Ambient r a b :=
  ((fun i => p.1.2 i * p.1.1 i, p.1.2), p.2)

def unitUnscaling (r a b : ℕ) (p : Ambient r a b) : Ambient r a b :=
  ((fun i => p.1.1 i / p.1.2 i, p.1.2), p.2)

theorem contDiff_unitScaling (r a b : ℕ) : ContDiff ℂ ∞ (unitScaling r a b) := by
  unfold unitScaling
  fun_prop

theorem contDiffOn_unitUnscaling (r a b : ℕ) :
    ContDiffOn ℂ ∞ (unitUnscaling r a b) (unitLocus r a b) := by
  apply ContDiffOn.prodMk
  · apply ContDiffOn.prodMk
    · apply contDiffOn_pi.mpr
      intro i
      exact (show ContDiffOn ℂ ∞ (fun p : Ambient r a b => p.1.1 i) (unitLocus r a b) by fun_prop).div
        (by fun_prop) (fun p hp => hp i)
    · fun_prop
  · fun_prop

theorem unitUnscaling_unitScaling (r a b : ℕ) (p : Ambient r a b) (hp : p ∈ unitLocus r a b) :
    unitUnscaling r a b (unitScaling r a b p) = p := by
  apply Prod.ext
  · apply Prod.ext
    · funext i
      exact mul_div_cancel_left₀ _ (hp i)
    · rfl
  · rfl

theorem unitScaling_unitUnscaling (r a b : ℕ) (p : Ambient r a b) (hp : p ∈ unitLocus r a b) :
    unitScaling r a b (unitUnscaling r a b p) = p := by
  apply Prod.ext
  · apply Prod.ext
    · funext i
      exact mul_div_cancel₀ _ (hp i)
    · rfl
  · rfl

/-- A GENUINE holomorphic chart on precisely the ratio-nonzero open. -/
def scalingChart (r a b : ℕ) : OpenPartialHomeomorph (Ambient r a b) (Ambient r a b) where
  toFun := unitScaling r a b
  invFun := unitUnscaling r a b
  source := unitLocus r a b
  target := unitLocus r a b
  map_source' _ hp := hp
  map_target' _ hp := hp
  left_inv' p hp := unitUnscaling_unitScaling r a b p hp
  right_inv' p hp := unitScaling_unitUnscaling r a b p hp
  open_source := isOpen_unitLocus r a b
  open_target := isOpen_unitLocus r a b
  continuousOn_toFun := (contDiff_unitScaling r a b).continuous.continuousOn
  continuousOn_invFun := (contDiffOn_unitUnscaling r a b).continuousOn

theorem scalingChart_mem_maximalAtlas (r a b : ℕ) :
    scalingChart r a b ∈ IsManifold.maximalAtlas 𝓘(ℂ, Ambient r a b) ∞ (Ambient r a b) := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · exact (contDiff_unitScaling r a b).contDiffOn.contMDiffOn
  · exact (contDiffOn_unitUnscaling r a b).contMDiffOn

private def leftBlockEquiv (r a b : ℕ) :
    Ambient r a b ≃L[ℂ] ((Block r × Block a) × (Block r × Block b)) where
  toFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  invFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def rightBlockEquiv (r a b : ℕ) :
    Ambient r a b ≃L[ℂ] ((Block r × Block b) × (Block r × Block a)) where
  toFun p := ((p.1.1, p.2.2), (p.1.2, p.2.1))
  invFun p := ((p.1.1, p.2.1), (p.2.2, p.1.2))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Literal first actual projection; no quotient or graph data are inputs. -/
def leftProjection (r a b : ℕ) (p : Ambient r a b) : Block r × Block a := (p.1.1, p.2.1)

/-- Literal second actual projection with genuine ratio-coordinate multiplication. -/
def rightProjection (r a b : ℕ) (p : Ambient r a b) : Block r × Block b :=
  (fun i => p.1.2 i * p.1.1 i, p.2.2)

/-- The first actual projection is a holomorphic submersion EVERYWHERE. -/
theorem leftProjection_isSubmersion (r a b : ℕ) :
    Manifold.IsSubmersionOfComplement (Block r × Block b)
      𝓘(ℂ, Ambient r a b) 𝓘(ℂ, Block r × Block a) ∞ (leftProjection r a b) := by
  intro p
  apply Manifold.IsSubmersionAtOfComplement.mk_of_charts (leftBlockEquiv r a b)
    (OpenPartialHomeomorph.refl (Ambient r a b)) (OpenPartialHomeomorph.refl (Block r × Block a))
    (mem_univ _) (mem_univ _)
  · apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn <;> exact contMDiffOn_id
  · apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn <;> exact contMDiffOn_id
  · intro _ _
    exact mem_univ _
  · intro _ _
    rfl

/-- The second actual map is a GENUINE chart-form holomorphic submersion
where all ratio coordinates are nonzero; no Jacobian-converse is assumed. -/
theorem rightProjection_isSubmersionAt (r a b : ℕ) (p : Ambient r a b) (hp : p ∈ unitLocus r a b) :
    Manifold.IsSubmersionAtOfComplement (Block r × Block a)
      𝓘(ℂ, Ambient r a b) 𝓘(ℂ, Block r × Block b) ∞ (rightProjection r a b) p := by
  apply Manifold.IsSubmersionAtOfComplement.mk_of_charts (rightBlockEquiv r a b)
    (scalingChart r a b) (OpenPartialHomeomorph.refl (Block r × Block b)) hp (mem_univ _)
    (scalingChart_mem_maximalAtlas r a b)
  · apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn <;> exact contMDiffOn_id
  · intro _ _
    exact mem_univ _
  · intro z hz
    change (rightProjection r a b (unitUnscaling r a b z)) = ((rightBlockEquiv r a b) z).1
    have hzU : z ∈ unitLocus r a b := by
      simpa [OpenPartialHomeomorph.extend, scalingChart] using hz
    have h := congrArg (fun p : Ambient r a b => (p.1.1, p.2.2))
      (unitScaling_unitUnscaling r a b z hzU)
    exact h

/-- Matching active member equation on the TRUE source open. -/
theorem rightProjection_coordinate_eq_zero_iff (r a b : ℕ) (p : Ambient r a b)
    (hp : p ∈ unitLocus r a b) (i : Fin r) :
    (rightProjection r a b p).1 i = 0 ↔ p.1.1 i = 0 :=
  mul_eq_zero.trans (or_iff_right (hp i))

/-- Actual translated original x-coordinate holomorphic germ. -/
def coordinateGerm (r a b : ℕ) (p : Ambient r a b) (i : Fin r) : HolGerm (Ambient r a b) :=
  HolGerm.mk (fun v => (p + v).1.1 i) (Eventually.of_forall fun _ => by fun_prop)

/-- Actual translated ratio-coordinate holomorphic germ. -/
def ratioGerm (r a b : ℕ) (p : Ambient r a b) (i : Fin r) : HolGerm (Ambient r a b) :=
  HolGerm.mk (fun v => (p + v).1.2 i) (Eventually.of_forall fun _ => by fun_prop)

/-- Germ of the ACTUAL target coordinate composed with the actual second map. -/
def pulledCoordinateGerm (r a b : ℕ) (p : Ambient r a b) (i : Fin r) : HolGerm (Ambient r a b) :=
  HolGerm.mk (fun v => (rightProjection r a b (p + v)).1 i) (Eventually.of_forall fun _ => by
    unfold rightProjection
    fun_prop)

theorem pulledCoordinateGerm_eq_mul (r a b : ℕ) (p : Ambient r a b) (i : Fin r) :
    pulledCoordinateGerm r a b p i = ratioGerm r a b p i * coordinateGerm r a b p i := by
  unfold pulledCoordinateGerm ratioGerm coordinateGerm
  rw [← HolGerm.mk_mul]
  rfl

theorem ratioGerm_isUnit (r a b : ℕ) (p : Ambient r a b) (hp : p ∈ unitLocus r a b) (i : Fin r) :
    IsUnit (ratioGerm r a b p i) := by
  apply (HolGerm.isUnit_iff_eval_ne_zero _).mpr
  simpa only [ratioGerm, HolGerm.eval_mk, add_zero] using hp i

/-- ENTIRE holomorphic coordinate ideal pullback, including off-member unit ideals. -/
theorem pulledCoordinateGerm_span_eq (r a b : ℕ) (p : Ambient r a b)
    (hp : p ∈ unitLocus r a b) (i : Fin r) :
    Ideal.span {pulledCoordinateGerm r a b p i} = Ideal.span {coordinateGerm r a b p i} := by
  rw [pulledCoordinateGerm_eq_mul, ← Ideal.span_singleton_mul_span_singleton,
    Ideal.span_singleton_eq_top.mpr (ratioGerm_isUnit r a b p hp i), Ideal.top_mul]

end
end Hironaka.HironakaG1RelativeBoundaryProjections
