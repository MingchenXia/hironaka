import Hironaka.Analytic.Unibranch.HironakaG10BanachTaylorRemainder
import Hironaka.Manifold.ComplexManifold

/-! # Coordinate-word expansion for Banach-valued multilinear maps -/
set_option autoImplicit false
namespace Hironaka.Analytic.Unibranch.HironakaG10BanachMultilinearCoordinates
open Hironaka

/-- A continuous multilinear map applied diagonally expands as a finite sum
of coordinate monomials times its actual Banach-valued basis coefficients. -/
theorem diagonal_eq_coordinate_words
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (d k : ℕ)
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin k => ComplexModel d) E)
    (z : ComplexModel d) :
    p (fun _ => z) = ∑ w : Fin k → Fin d,
      (∏ i, z (w i)) • p (fun i => EuclideanSpace.single (w i) (1 : ℂ)) := by
  classical
  have hz : z = ∑ i : Fin d, z i • EuclideanSpace.single i (1 : ℂ) := by
    ext i
    change (EuclideanSpace.proj i : ComplexModel d →L[ℂ] ℂ) z =
      (EuclideanSpace.proj i : ComplexModel d →L[ℂ] ℂ)
        (∑ j : Fin d, z j • EuclideanSpace.single j (1 : ℂ))
    rw [map_sum]
    simp only [map_smul]
    change z i = ∑ j : Fin d, z j * (Pi.single j (1 : ℂ) : Fin d → ℂ) i
    simp [Pi.single_apply]
  have hExp := p.map_sum (fun (_ : Fin k) (i : Fin d) =>
    z i • EuclideanSpace.single i (1 : ℂ))
  have hArg : (fun (_ : Fin k) => ∑ i : Fin d, z i • EuclideanSpace.single i (1 : ℂ)) =
      (fun _ => z) := funext fun _ => hz.symm
  rw [hArg] at hExp
  rw [hExp]
  apply Finset.sum_congr rfl
  intro w hw
  rw [p.map_smul_univ]

end Hironaka.Analytic.Unibranch.HironakaG10BanachMultilinearCoordinates
