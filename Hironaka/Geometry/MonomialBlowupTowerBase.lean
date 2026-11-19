import Hironaka.Geometry.BlowupAlteration
import Hironaka.Geometry.BlowupProjective

/-!
# Actual finite global blowup towers

Natural-number recursion constructs native global blowups of the pullbacks
of specified ideals on the original scheme. All structure maps are actual.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.MonomialBlowupTowerBase

open BlowupGluing

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{u}}

/-- The actual finite tower, as genuine schemes over the original scheme. -/
def stage (D : ℕ → X.IdealSheafData) : ℕ → Over X
  | 0 => Over.mk (𝟙 X)
  | n + 1 => Over.mk
    (blowupStructure ((D n).comap (stage D n).hom) ≫ (stage D n).hom)

/-- The exact actual ideal sheaf blown up at the specified stage. -/
def stageCenter (D : ℕ → X.IdealSheafData) (n : ℕ) : (stage D n).left.IdealSheafData :=
  (D n).comap (stage D n).hom

/-- The successor transition is the actual native global blowup structure morphism. -/
def step (D : ℕ → X.IdealSheafData) (n : ℕ) : (stage D (n + 1)).left ⟶ (stage D n).left :=
  blowupStructure (stageCenter D n)

@[simp]
theorem stage_zero_left (D : ℕ → X.IdealSheafData) : (stage D 0).left = X := rfl

@[simp]
theorem stage_zero_hom (D : ℕ → X.IdealSheafData) : (stage D 0).hom = 𝟙 X := rfl

@[simp]
theorem stage_succ_left (D : ℕ → X.IdealSheafData) (n : ℕ) :
    (stage D (n + 1)).left = blowup (stageCenter D n) := rfl

@[reassoc (attr := simp)]
theorem step_structure (D : ℕ → X.IdealSheafData) (n : ℕ) :
    step D n ≫ (stage D n).hom = (stage D (n + 1)).hom := rfl

/-- The actual tower is locally Noetherian at every finite stage. -/
theorem stage_isLocallyNoetherian [IsLocallyNoetherian X]
    (D : ℕ → X.IdealSheafData) (n : ℕ) : IsLocallyNoetherian (stage D n).left := by
  induction n with
  | zero => exact inferInstanceAs (IsLocallyNoetherian X)
  | succ n ih =>
    let : IsLocallyNoetherian (stage D n).left := ih
    let : IsProper (blowupStructure (stageCenter D n)) :=
      BlowupAlteration.blowupStructure_isProper _
    exact LocallyOfFiniteType.isLocallyNoetherian (blowupStructure (stageCenter D n))

/-- Actual surjectivity of an alteration preserves proper support under the actual ideal comap. -/
theorem support_comap_ne_top {Y : Scheme.{u}} (D : X.IdealSheafData)
    (p : Y ⟶ X) [IsAlteration p] (hD : D.support ≠ ⊤) : (D.comap p).support ≠ ⊤ := by
  intro h
  apply hD
  apply top_le_iff.mp
  intro y _
  obtain ⟨x, rfl⟩ := IsAlteration.surjective p y
  have hx : x ∈ (D.comap p).support := by rw [h]; trivial
  rw [Scheme.IdealSheafData.support_comap] at hx
  exact hx

/-- The actual finite tower of proper-support centres consists of alterations of the original scheme. -/
theorem stage_isAlteration [IsIntegral X] [IsLocallyNoetherian X]
    (D : ℕ → X.IdealSheafData) (hD : ∀ n, (D n).support ≠ ⊤) (n : ℕ) :
    IsAlteration (stage D n).hom := by
  induction n with
  | zero => exact inferInstanceAs (IsAlteration (𝟙 X))
  | succ n ih =>
    let : IsAlteration (stage D n).hom := ih
    let : IsIntegral (stage D n).left := ih.sourceIntegral
    let : IsLocallyNoetherian (stage D n).left := stage_isLocallyNoetherian D n
    let : IsAlteration (step D n) := BlowupAlteration.blowupStructure_isAlteration
      (stageCenter D n) (support_comap_ne_top (D n) (stage D n).hom (hD n))
    exact IsAlteration.comp (step D n) (stage D n).hom

/-- Every actual finite stage preserves a given actual projective morphism to an affine Noetherian base. -/
theorem stage_comp_isProjective {R : Type u} [CommRing R] [IsNoetherianRing R]
    (D : ℕ → X.IdealSheafData) (p : X ⟶ Spec (CommRingCat.of R))
    (hp : IsProjectiveOver p) (n : ℕ) : IsProjectiveOver ((stage D n).hom ≫ p) := by
  induction n with
  | zero => simpa using hp
  | succ n ih =>
    change IsProjectiveOver ((blowupStructure (stageCenter D n) ≫ (stage D n).hom) ≫ p)
    rw [Category.assoc]
    exact BlowupProjective.blowupStructure_comp_isProjective
      (stageCenter D n) ((stage D n).hom ≫ p) ih

end Hironaka.Geometry.MonomialBlowupTowerBase
