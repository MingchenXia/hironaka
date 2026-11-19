import Hironaka.Algebra.NodeFieldSmoothBranch
import Hironaka.Geometry.StableModification.Resolution.LocalDVR

/-! The whole original regular branch constructs its own residue coefficients and formal coordinate. -/

noncomputable section

namespace Hironaka.Algebra.NodeFieldRegularBranch

open IsLocalRing NodeNonsplit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {K : Type u} [Field K] (q : Quadratic K)

section Residue

variable {R : Type v} [CommRing R] [IsLocalRing R] [Algebra K R]
  (φ : QuadraticNode q →ₐ[K] R) (hφ : Function.Surjective φ)

include q φ hφ

/-- The WHOLE actual original surjection supplies the SAME original target residue coefficients. -/
theorem residue_coefficient_surjective :
    Function.Surjective ((residue R).comp (algebraMap K R)) := by
  have hz : MvPowerSeries.constantCoeff q.series = 0 := by
    simp [Quadratic.series, Quadratic.value, Quadratic.map]
  let := NodeFieldQuadraticSource.equationLocalRing K q.series hz
  let := IsLocalHom.of_surjective φ.toRingHom hφ
  have hsource :=
    (NodeFieldQuadraticSource.equation_residue_coefficient_bijective K q.series hz).2
  intro c
  obtain ⟨r, rfl⟩ := residue_surjective c
  obtain ⟨x, rfl⟩ := hφ r
  obtain ⟨a, ha⟩ := hsource (residue (QuadraticNode q) x)
  refine ⟨a, ?_⟩
  have h := congrArg (ResidueField.map φ.toRingHom) ha
  change ResidueField.map φ.toRingHom (residue (QuadraticNode q)
    (algebraMap K (QuadraticNode q) a)) =
    ResidueField.map φ.toRingHom (residue (QuadraticNode q) x) at h
  rw [ResidueField.map_residue, ResidueField.map_residue] at h
  change residue R (φ (algebraMap K (QuadraticNode q) a)) = residue R (φ x) at h
  rw [φ.commutes] at h
  exact h

end Residue

variable {R : Type v} [CommRing R] [Algebra K R] [IsRegularLocalRing R]
  [IsAdicComplete (maximalIdeal R) R]
  (φ : QuadraticNode q →ₐ[K] R) (hφ : Function.Surjective φ)
  (hdim : ringKrullDim R = 1)

include q φ hφ hdim

/-- The actual complete regular target receives its OWN original-field formal coordinate internally. -/
def powerSeriesEquiv : PowerSeries K ≃ₐ[K] R :=
  Classical.choice
    (StableModification.Resolution.nonempty_powerSeries_algEquiv_of_ringKrullDim_eq_one
      hdim (residue_coefficient_surjective q φ hφ))

/-- The entire SAME original branch is carried to its internally constructed formal coordinate. -/
def branchMap : QuadraticNode q →ₐ[K] PowerSeries K :=
  (powerSeriesEquiv q φ hφ hdim).symm.toAlgHom.comp φ

/-- EVERY coefficient follows the unchanged original K-algebra maps. -/
theorem branchMap_coefficient (a : K) :
    branchMap q φ hφ hdim (algebraMap K (QuadraticNode q) a) = PowerSeries.C a :=
  (branchMap q φ hφ hdim).commutes a

/-- The WHOLE internally constructed original-field formal branch is surjective. -/
theorem branchMap_surjective : Function.Surjective (branchMap q φ hφ hdim) :=
  (powerSeriesEquiv q φ hφ hdim).symm.surjective.comp hφ

/-- The actual complete regular original branch INTERNALLY splits the SAME original quadratic. -/
def quotientEquiv : QuadraticNode q ≃ₐ[K] NodeFlatPresentation.SplitNode K :=
  NodeFieldSmoothBranch.quotientEquiv q (branchMap q φ hφ hdim)
    (branchMap_surjective q φ hφ hdim)

end Hironaka.Algebra.NodeFieldRegularBranch
