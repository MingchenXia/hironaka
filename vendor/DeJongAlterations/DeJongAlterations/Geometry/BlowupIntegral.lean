import DeJongAlterations.Geometry.BlowupGluing
import DeJongAlterations.Geometry.IntegralIdeal
import DeJongAlterations.Geometry.ProjIntegral
import DeJongAlterations.Geometry.AffineBlowupDominant
import Mathlib.Topology.Sets.OpenCover

/-!
# Integrality of the actual global blowup

The actual native affine blowup charts on nonempty base opens are integral.
Their composites to the integral base are dominant, which forces their open
images to intersect. Reduced descent and open-cover irreducibility finish.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace
open DeJongAlterations.Geometry.BlowupGluing

noncomputable section

namespace DeJongAlterations.Geometry.BlowupIntegral

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{u}}

/-- Empty base affine pieces can be discarded from the actual native blowup cover. -/
def nonemptyAffineBlowupCover (D : X.IdealSheafData) : (blowup D).OpenCover.{u} :=
  Scheme.Cover.mkOfCovers
    {U : X.AffineZariskiSite // Nonempty U.1}
    (fun U => affineBlowup (D.ideal ⟨U.val.1, U.val.2⟩))
    (fun U => chartInclusion D U.val)
    (by
      intro p
      obtain ⟨U, q, hq⟩ := (blowupCover D).exists_eq p
      change chartInclusion D U q = p at hq
      have hp : p ∈ (chartInclusion D U).opensRange := ⟨q, hq⟩
      rw [chartInclusion_opensRange] at hp
      have hU : Nonempty U.1 := ⟨⟨blowupStructure D p, hp⟩⟩
      exact ⟨⟨U, hU⟩, q, hq⟩)

variable [IsIntegral X]

/-- The actual spectrum chart of a nonempty affine open is dominant in an integral scheme. -/
theorem fromSpec_isDominant (U : X.AffineZariskiSite) [Nonempty U.1] :
    IsDominant U.2.fromSpec := by
  constructor
  change Dense (Set.range U.2.fromSpec)
  rw [U.2.range_fromSpec]
  exact U.1.isOpen.dense (Set.nonempty_coe_sort.mp (inferInstance : Nonempty U.1))

/-- Proper support supplies a genuine integral native blowup on each nonempty affine open. -/
theorem chart_isIntegral (D : X.IdealSheafData) (hD : D.support ≠ ⊤)
    (U : X.AffineZariskiSite) [Nonempty U.1] :
    IsIntegral (affineBlowup (D.ideal ⟨U.1, U.2⟩)) :=
  ProjIntegral.isIntegral_affineBlowup _
    (IntegralIdeal.ideal_ne_bot_of_support_ne_top D hD ⟨U.1, U.2⟩)

/-- Each nonempty actual affine blowup chart maps dominantly to the original integral scheme. -/
theorem chartInclusion_comp_isDominant (D : X.IdealSheafData) (hD : D.support ≠ ⊤)
    (U : X.AffineZariskiSite) [Nonempty U.1] :
    IsDominant (chartInclusion D U ≫ blowupStructure D) := by
  rw [chartInclusion_structure]
  let := fromSpec_isDominant U
  let := affineBlowupStructure_isDominant (D.ideal ⟨U.1, U.2⟩)
    (IntegralIdeal.ideal_ne_bot_of_support_ne_top D hD ⟨U.1, U.2⟩)
  infer_instance

/-- The actual open images of any two nonempty affine blowup pieces intersect. -/
theorem chartInclusion_not_disjoint (D : X.IdealSheafData) (hD : D.support ≠ ⊤)
    (U V : X.AffineZariskiSite) [Nonempty U.1] [Nonempty V.1] :
    ¬ Disjoint (chartInclusion D U).opensRange (chartInclusion D V).opensRange := by
  let := chartInclusion_comp_isDominant D hD U
  obtain ⟨p, hp⟩ := (chartInclusion D U ≫ blowupStructure D).denseRange.exists_mem_open
    V.1.isOpen (Set.nonempty_coe_sort.mp (inferInstance : Nonempty V.1))
  have hpV : chartInclusion D U p ∈ (chartInclusion D V).opensRange := by
    rw [chartInclusion_opensRange]
    exact hp
  intro hd
  exact hd.le_bot ⟨⟨p, rfl⟩, hpV⟩

/-- The actual global native blowup of a proper-support ideal sheaf on an integral scheme is integral. -/
theorem isIntegral_blowup (D : X.IdealSheafData) (hD : D.support ≠ ⊤) :
    IsIntegral (blowup D) := by
  let C := nonemptyAffineBlowupCover D
  let : ∀ i : C.I₀, IsIntegral (C.X i) := fun i => by
    let : Nonempty i.val.1 := i.property
    exact chart_isIntegral D hD i.val
  let : AlgebraicGeometry.IsReduced (blowup D) :=
    AlgebraicGeometry.IsReduced.of_openCover (blowup D) C
  have hpair : Pairwise (fun i j : C.I₀ =>
      ¬ Disjoint (C.f i).opensRange (C.f j).opensRange) := by
    intro i j _
    let : Nonempty i.val.1 := i.property
    let : Nonempty j.val.1 := j.property
    exact chartInclusion_not_disjoint D hD i.val j.val
  have hpre (i : C.I₀) : PreirreducibleSpace (C.f i).opensRange := by
    apply isPreirreducible_iff_preirreducibleSpace.mp
    have h := (PreirreducibleSpace.isPreirreducible_univ :
      IsPreirreducible (Set.univ : Set (C.X i))).image
      (C.f i) (C.f i).continuous.continuousOn
    simpa only [Set.image_univ, Scheme.Hom.coe_opensRange] using h
  let : PreirreducibleSpace (blowup D) :=
    PreirreducibleSpace.of_isOpenCover hpair C.isOpenCover_opensRange hpre
  let : Nonempty (blowup D) := by
    let x : X := Classical.choice inferInstance
    obtain ⟨W, hW, hxW, _⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) (by trivial)
    let U : X.AffineZariskiSite := ⟨W, hW⟩
    let : Nonempty U.1 := ⟨⟨x, hxW⟩⟩
    let : IsIntegral (affineBlowup (D.ideal ⟨U.1, U.2⟩)) :=
      chart_isIntegral D hD U
    exact ⟨chartInclusion D U (Classical.choice inferInstance)⟩
  let : IrreducibleSpace (blowup D) :=
    { toPreirreducibleSpace := inferInstance, toNonempty := inferInstance }
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end DeJongAlterations.Geometry.BlowupIntegral
