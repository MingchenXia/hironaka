import Hironaka.Algebra.ProjectiveProjectionFiniteChartRelation

/-!
# Whole actual original chart algebra generation by the actual discarded ratio
-/

noncomputable section

open MvPolynomial AlgebraicGeometry HomogeneousLocalization

namespace Hironaka.Algebra.ProjectiveSecant

open Geometry.ProjectiveIdeal ProjectiveProjectionFinite

universe u

attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ) (j : Fin (n + 1))
  {S : Type u} [CommRing S] (φ : CoordinateRing k j.succ →+* S)

/-- The literal whole remaining-coordinate ratio map into the actual original source chart. -/
def sourceProjectionChartMap : HomogeneousChartRing k j →+* S :=
  φ.comp ((MvPolynomial.rename (chartIndexLift n j)).toRingHom.comp (homogeneousChartDehom j).toRingHom)

/-- The actual original discarded-coordinate ratio in the whole original source chart. -/
def sourceDiscardedRatio : S := φ (MvPolynomial.X (discardedChartIndex n j))

/-- The actual base chart map retains every literal original remaining-coordinate polynomial. -/
theorem sourceProjectionChartMap_ratio (P : CoordinateRing k j) :
    sourceProjectionChartMap k n j φ (homogeneousChartRatioHom j P) =
      φ (MvPolynomial.rename (chartIndexLift n j) P) := by
  change φ (MvPolynomial.rename (chartIndexLift n j) (homogeneousChartDehom j (homogeneousChartRatioHom j P))) = _
  have h := AlgHom.congr_fun (homogeneousChartDehom_comp_ratioHom (R := k) j) P
  change homogeneousChartDehom j (homogeneousChartRatioHom j P) = P at h
  rw [h]

/-- Whole actual original polynomial surjectivity internally proves one-element algebra generation over the literal original remaining-ratio map. -/
theorem sourceProjectionChartMap_adjoin_eq_top (hsurj : Function.Surjective φ) :
    letI := (sourceProjectionChartMap k n j φ).toAlgebra
    Algebra.adjoin (HomogeneousChartRing k j) {sourceDiscardedRatio k n j φ} =
      (⊤ : Subalgebra _ S) := by
  let := (sourceProjectionChartMap k n j φ).toAlgebra
  let A := Algebra.adjoin (HomogeneousChartRing k j) {sourceDiscardedRatio k n j φ}
  apply top_unique
  intro z hz
  clear hz
  obtain ⟨P, rfl⟩ := hsurj z
  have hC (a : k) : φ (C a) ∈ A := by
    have h := A.algebraMap_mem (homogeneousChartRatioHom j (C a))
    change sourceProjectionChartMap k n j φ _ ∈ A at h
    simpa only [sourceProjectionChartMap_ratio, MvPolynomial.rename_C] using h
  have hX (i : ChartIndex j.succ) : φ (MvPolynomial.X i) ∈ A := by
    rcases i with ⟨i, hi⟩
    refine Fin.cases ?_ (fun l => ?_) i hi
    · intro hi0
      exact Algebra.subset_adjoin (Set.mem_singleton _)
    · intro hl
      let a : ChartIndex j := ⟨l, fun h => hl (congrArg Fin.succ h)⟩
      have h := A.algebraMap_mem (homogeneousChartRatioHom j (MvPolynomial.X a))
      change sourceProjectionChartMap k n j φ _ ∈ A at h
      simpa only [sourceProjectionChartMap_ratio, MvPolynomial.rename_X, chartIndexLift, a] using h
  induction P using MvPolynomial.induction_on with
  | C a => exact hC a
  | add P Q hP hQ => simpa only [map_add] using A.add_mem hP hQ
  | mul_X P i hP => simpa only [map_mul] using A.mul_mem hP (hX i)

end Hironaka.Algebra.ProjectiveSecant
