import DeJongAlterations.Geometry.BlowupGluing
import DeJongAlterations.Geometry.BlowupIntegral
import DeJongAlterations.Geometry.AffineBlowupAlteration
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Properties of the actual globally glued blowup

Properness descends from the actual native affine blowups using their
constructed Cartesian comparisons. No local geometric certificate is
supplied to the public properness theorem.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace DeJongAlterations.Geometry.BlowupAlteration

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open BlowupGluing

/-- The actual spectra of all affine coordinate rings form a native open cover. -/
@[simps! I₀ X f]
def affineCoordinateOpenCover (X : Scheme.{u}) : X.OpenCover.{u} :=
  Scheme.Cover.mkOfCovers X.AffineZariskiSite
    (fun U => Spec Γ(X, U.1)) (fun U => U.2.fromSpec) (by
      intro x
      obtain ⟨U, hxU⟩ := Opens.mem_iSup.mp ((iSup_affineOpens_eq_top X).ge (Set.mem_univ x))
      have hU : IsAffineOpen U.1 := U.2
      refine ⟨⟨U.1, hU⟩, ?_⟩
      change x ∈ Set.range hU.fromSpec
      rw [hU.range_fromSpec]
      exact hxU)

variable {X : Scheme.{u}} (D : X.IdealSheafData)

/-- Zariski-local target properties of the actual blowup are detected on its
internally constructed native affine Cartesian charts. -/
private theorem property_of_affine_charts (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P]
    (hP : ∀ U : X.AffineZariskiSite, P (affineBlowupStructure (D.ideal ⟨U.1, U.2⟩))) :
    P (blowupStructure D) := by
  apply IsZariskiLocalAtTarget.of_openCover (affineCoordinateOpenCover X)
  intro U
  let h := (isPullback_chart D U).flip
  change P (pullback.snd (blowupStructure D) U.2.fromSpec)
  rw [← h.isoPullback_inv_snd]
  exact (P.cancel_left_of_respectsIso h.isoPullback.inv _).mpr (hP U)

/-- The genuine globally glued blowup of any native ideal on a locally
Noetherian scheme is proper over its original base. -/
theorem blowupStructure_isProper [IsLocallyNoetherian X] :
    IsProper (blowupStructure D) := by
  apply property_of_affine_charts D (@IsProper)
  intro U
  let : IsNoetherianRing Γ(X, U.1) :=
    IsLocallyNoetherian.component_noetherian ⟨U.1, U.2⟩
  exact affineBlowupStructure_isProper _ (D.ideal ⟨U.1, U.2⟩).fg_of_isNoetherianRing

/-- A proper-support blowup of an integral scheme is dominant over its actual base. -/
theorem blowupStructure_isDominant [IsIntegral X] (hD : D.support ≠ ⊤) :
    IsDominant (blowupStructure D) := by
  let x : X := genericPoint X
  obtain ⟨W, hW, hxW, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) (by trivial)
  let U : X.AffineZariskiSite := ⟨W, hW⟩
  let : Nonempty U.1 := ⟨⟨x, hxW⟩⟩
  let := BlowupIntegral.chartInclusion_comp_isDominant D hD U
  exact IsDominant.of_comp (chartInclusion D U) (blowupStructure D)

/-- Generic quasi-finiteness comes from one actual native affine blowup chart. -/
theorem blowupStructure_quasiFiniteAt_genericPoint [IsIntegral X] [IsLocallyNoetherian X]
    (hD : D.support ≠ ⊤) :
    letI := BlowupIntegral.isIntegral_blowup D hD
    (blowupStructure D).QuasiFiniteAt (genericPoint (blowup D)) := by
  let : IsIntegral (blowup D) := BlowupIntegral.isIntegral_blowup D hD
  let x : X := genericPoint X
  obtain ⟨W, hW, hxW, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) (by trivial)
  let U : X.AffineZariskiSite := ⟨W, hW⟩
  let : Nonempty U.1 := ⟨⟨x, hxW⟩⟩
  let I := D.ideal ⟨U.1, U.2⟩
  let : IsNoetherianRing Γ(X, U.1) :=
    IsLocallyNoetherian.component_noetherian ⟨U.1, U.2⟩
  have hI : I ≠ ⊥ := IntegralIdeal.ideal_ne_bot_of_support_ne_top D hD ⟨U.1, U.2⟩
  let : IsIntegral (affineBlowup I) := ProjIntegral.isIntegral_affineBlowup I hI
  let hA := affineBlowupStructure_isAlteration I hI I.fg_of_isNoetherianRing
  let := hA
  have hq : (chartInclusion D U ≫ blowupStructure D).QuasiFiniteAt
      (genericPoint (affineBlowup I)) := by
    rw [chartInclusion_structure]
    exact (Scheme.Hom.quasiFiniteAt_comp_iff
      (f := affineBlowupStructure I) (g := U.2.fromSpec)).mpr
        (hA.genericallyFinite.quasiFiniteAt_genericPoint _)
  have hq' := (Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion
    (f := chartInclusion D U) (g := blowupStructure D)).mp hq
  have heq : chartInclusion D U (genericPoint (affineBlowup I)) =
      genericPoint (blowup D) := genericPoint_eq_of_isOpenImmersion (chartInclusion D U)
  rw [heq] at hq'
  exact hq'

/-- The actual global blowup in a proper-support ideal of a locally Noetherian
integral scheme is an alteration, with its genuine source and structure map. -/
theorem blowupStructure_isAlteration [IsIntegral X] [IsLocallyNoetherian X]
    (hD : D.support ≠ ⊤) : IsAlteration (blowupStructure D) := by
  let : IsIntegral (blowup D) := BlowupIntegral.isIntegral_blowup D hD
  let : IsProper (blowupStructure D) := blowupStructure_isProper D
  let : IsDominant (blowupStructure D) := blowupStructure_isDominant D hD
  exact {
    sourceIntegral := inferInstance
    targetIntegral := inferInstance
    genericallyFinite := isGenericallyFinite_of_quasiFiniteAt_genericPoint _
      (blowupStructure_quasiFiniteAt_genericPoint D hD) }

end DeJongAlterations.Geometry.BlowupAlteration
