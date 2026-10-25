import DeJongAlterations.Composition
import DeJongAlterations.Geometry.AffineBlowupDominant
import DeJongAlterations.Geometry.ProjIntegral
import DeJongAlterations.Geometry.AffineBirational
import Mathlib.RingTheory.Localization.AsSubring

/-!
# Native affine blowups are alterations

For a nonzero finitely generated ideal in a domain, the actual Rees/Proj blowup
morphism is an alteration. The nonempty finite target neighbourhood is produced
from generic quasi-finiteness of an actual fraction chart and properness.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

namespace DeJongAlterations

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A genuine nonzero-generator chart proves quasi-finiteness at the blowup generic point. -/
theorem affineBlowupStructure_quasiFiniteAt_genericPoint (I : Ideal R) (hI : I ≠ ⊥) :
    letI : IsIntegral (affineBlowup I) := Geometry.ProjIntegral.isIntegral_affineBlowup I hI
    (affineBlowupStructure I).QuasiFiniteAt (genericPoint (affineBlowup I)) := by
  let : IsIntegral (affineBlowup I) := Geometry.ProjIntegral.isIntegral_affineBlowup I hI
  obtain ⟨g, hg, hg0⟩ : ∃ g ∈ I, g ≠ 0 := by
    by_contra! hzero
    apply hI
    apply le_antisymm
    · intro a ha
      change a = 0
      exact hzero a ha
    · exact bot_le
  let i := affineBlowupChartInclusion I g hg hg0
  have hq : (i ≫ affineBlowupStructure I).QuasiFiniteAt
      (genericPoint (Spec (.of (affineBlowupFractionChart I g)))) := by
    dsimp only [i]
    rw [affineBlowupChartInclusion_structure]
    exact Geometry.AffineBirational.quasiFiniteAt_genericPoint R
      (affineBlowupFractionChart I g) (FractionRing R)
  have hq' := (Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion
    (f := i) (g := affineBlowupStructure I)).mp hq
  simpa only [genericPoint_eq_of_isOpenImmersion i] using hq'

/-- The actual native blowup of a nonzero finitely generated ideal in a domain is an alteration. -/
theorem affineBlowupStructure_isAlteration (I : Ideal R) (hI : I ≠ ⊥) (hfg : I.FG) :
    IsAlteration (affineBlowupStructure I) := by
  let : IsIntegral (affineBlowup I) := Geometry.ProjIntegral.isIntegral_affineBlowup I hI
  let : IsProper (affineBlowupStructure I) := affineBlowupStructure_isProper I hfg
  let : IsDominant (affineBlowupStructure I) := affineBlowupStructure_isDominant I hI
  exact {
    sourceIntegral := inferInstance
    targetIntegral := inferInstance
    genericallyFinite := isGenericallyFinite_of_quasiFiniteAt_genericPoint _
      (affineBlowupStructure_quasiFiniteAt_genericPoint I hI) }

end DeJongAlterations
