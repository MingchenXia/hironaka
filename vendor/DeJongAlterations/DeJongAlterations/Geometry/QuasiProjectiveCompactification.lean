import DeJongAlterations.Geometry.ProjectiveCompactificationBoundary
import DeJongAlterations.Geometry.BoundaryRestriction
import DeJongAlterations.Geometry.BoundaryComposition

/-!
# The full conditional quasi-projective reduction in source 4.7

Quasi-projectivity means an actual native immersion into finite-dimensional
projective space over the original coefficient scheme. The actual projective
closure and boundary are constructed, and a projective-case solution is
transported back to the original input scheme, not merely its open range.

The projective-case existence statement is an explicit premise.
This does not prove Chow's lemma or the general alteration existence theorem.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

namespace DeJongAlterations

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- Native quasi-projectivity means an actual projective immersion with the original coefficient triangle. -/
def IsQuasiProjectiveOver (p : X ⟶ Spec (CommRingCat.of R)) : Prop :=
  ∃ (n : ℕ) (e : X ⟶ projectiveSpace R n),
    IsImmersion e ∧ e ≫ projectiveSpaceStructure R n = p

/-- A genuine native projective presentation is a genuine quasi-projective presentation. -/
theorem IsProjectiveOver.isQuasiProjective {p : X ⟶ Spec (CommRingCat.of R)}
    (hp : IsProjectiveOver p) : IsQuasiProjectiveOver p := by
  obtain ⟨n, e, he, hp⟩ := hp
  let := he
  exact ⟨n, e, inferInstance, hp⟩

namespace Geometry.QuasiProjectiveCompactification

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- Native quasi-projectivity supplies an actually constructed dense open projective-variety compactification. -/
theorem exists_compactification (p : X ⟶ Spec (CommRingCat.of k)) [IsVariety p]
    (hp : IsQuasiProjectiveOver p) :
    ∃ (Xbar : Scheme.{u}) (pbar : Xbar ⟶ Spec (CommRingCat.of k)) (j : X ⟶ Xbar),
      IsVariety pbar ∧ IsProjectiveOver pbar ∧ IsOpenImmersion j ∧ IsDominant j ∧ j ≫ pbar = p := by
  obtain ⟨n, e, he, hbase⟩ := hp
  let := he
  exact ProjectiveCompactification.exists_projective_compactification p e hbase

/-- The actual compactification extends the original closed subset and proves its properness internally. -/
theorem exists_compactification_with_boundary
    (p : X ⟶ Spec (CommRingCat.of k)) [IsVariety p]
    (hp : IsQuasiProjectiveOver p) (Z : Closeds X) :
    ∃ (Xbar : Scheme.{u}) (pbar : Xbar ⟶ Spec (CommRingCat.of k))
      (j : X ⟶ Xbar) (Dbar : Xbar.IdealSheafData),
      IsVariety pbar ∧ IsProjectiveOver pbar ∧ IsOpenImmersion j ∧ IsDominant j ∧
        j ≫ pbar = p ∧
        (Dbar.support : Set Xbar) = j '' (Z : Set X) ∪ (Set.range j)ᶜ ∧
        (Dbar.comap j).support = Z ∧ (Z ≠ ⊤ → Dbar.support ≠ ⊤) := by
  obtain ⟨n, e, he, hbase⟩ := hp
  let := he
  let D := Scheme.IdealSheafData.vanishingIdeal Z
  have hD : D.support = Z := by
    apply SetLike.coe_injective
    exact Scheme.IdealSheafData.coe_support_vanishingIdeal Z
  simpa only [hD] using
    ProjectiveCompactification.exists_projective_compactification_with_boundary p e hbase D

/-- An actual native open immersion identifies its original source with its actual open range. -/
def rangeIso (j : X ⟶ Y) [IsOpenImmersion j] : X ≅ j.opensRange.toScheme :=
  IsOpenImmersion.isoOfRangeEq j j.opensRange.ι (by rw [Scheme.Opens.range_ι]; rfl)

@[reassoc (attr := simp)]
theorem rangeIso_hom_ι (j : X ⟶ Y) [IsOpenImmersion j] :
    (rangeIso j).hom ≫ j.opensRange.ι = j :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc (attr := simp)]
theorem rangeIso_inv_j (j : X ⟶ Y) [IsOpenImmersion j] :
    (rangeIso j).inv ≫ j = j.opensRange.ι :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

/-- Transport only the actual alteration through a target isomorphism, retaining the full compactification and ideal. -/
@[simps! source compactification sourceStructure compactificationStructure alteration inclusion boundary]
def transportTargetIso
    {p : X ⟶ Spec (CommRingCat.of k)} {q : Y ⟶ Spec (CommRingCat.of k)}
    {Z : Set X} {W : Set Y} (a : Y ≅ X)
    (hp : a.hom ≫ p = q) (hZ : a.hom ⁻¹' Z = W)
    (d : AlterationWithBoundary q W) : AlterationWithBoundary p Z where
  source := d.source
  compactification := d.compactification
  sourceStructure := d.sourceStructure
  compactificationStructure := d.compactificationStructure
  alteration := d.alteration ≫ a.hom
  inclusion := d.inclusion
  boundary := d.boundary
  sourceVariety := d.sourceVariety
  compactificationVariety := d.compactificationVariety
  alterationOver := by rw [Category.assoc, hp]; exact d.alterationOver
  inclusionOver := d.inclusionOver
  isAlteration := by
    let := d.isAlteration
    let : IsIntegral Y := d.isAlteration.targetIntegral
    let : IsIntegral X := IsIntegral.of_isIso a.hom
    let : IsAlteration a.hom := isAlteration_of_isFinite a.hom
    exact IsAlteration.comp d.alteration a.hom
  isOpenImmersion := d.isOpenImmersion
  projective := d.projective
  regular := d.regular
  normalCrossings := d.normalCrossings
  boundarySupport := by
    change (d.boundary.support : Set d.compactification) =
      d.inclusion '' (d.alteration ⁻¹' (a.hom ⁻¹' Z)) ∪ (Set.range d.inclusion)ᶜ
    rw [hZ]
    exact d.boundarySupport

/-- Native target-isomorphism transport preserves actual generic etaleness. -/
theorem transportTargetIso_genericallyEtale
    {p : X ⟶ Spec (CommRingCat.of k)} {q : Y ⟶ Spec (CommRingCat.of k)}
    {Z : Set X} {W : Set Y} (a : Y ≅ X)
    (hp : a.hom ≫ p = q) (hZ : a.hom ⁻¹' Z = W)
    (d : AlterationWithBoundary q W) (hd : IsGenericallyEtale d.alteration) :
    IsGenericallyEtale (transportTargetIso a hp hZ d).alteration :=
  hd.comp (isGenericallyEtale_of_etale a.hom)

/-- The identical compactification morphism retains smoothness under actual target transport. -/
theorem transportTargetIso_perfectRefinement
    {p : X ⟶ Spec (CommRingCat.of k)} {q : Y ⟶ Spec (CommRingCat.of k)}
    {Z : Set X} {W : Set Y} (a : Y ≅ X)
    (hp : a.hom ≫ p = q) (hZ : a.hom ⁻¹' Z = W)
    (d : AlterationWithBoundary q W) (hd : IsGenericallyEtale d.alteration)
    (hs : Smooth d.compactificationStructure) :
    IsGenericallyEtale (transportTargetIso a hp hZ d).alteration ∧
      Smooth (transportTargetIso a hp hZ d).compactificationStructure :=
  ⟨transportTargetIso_genericallyEtale a hp hZ d hd, hs⟩

/-- Restrict an actual full output through an open immersion and return its alteration to the original source scheme. -/
@[simps! compactification compactificationStructure boundary]
def restrictToOriginal
    {p : X ⟶ Spec (CommRingCat.of k)} {q : Y ⟶ Spec (CommRingCat.of k)}
    {Z : Set X} {W : Set Y} (j : X ⟶ Y) [IsOpenImmersion j] [Nonempty X]
    (hover : j ≫ q = p) (hZ : j ⁻¹' W = Z) (hdiscard : (Set.range j)ᶜ ⊆ W)
    (d : AlterationWithBoundary q W) : AlterationWithBoundary p Z := by
  let : Nonempty j.opensRange := Nonempty.map (rangeIso j).hom inferInstance
  have hp : (rangeIso j).inv ≫ p = j.opensRange.ι ≫ q := by
    rw [← hover, ← Category.assoc, rangeIso_inv_j]
  have hz : (rangeIso j).inv ⁻¹' Z = j.opensRange.ι ⁻¹' W := by
    calc
      _ = (rangeIso j).inv ⁻¹' (j ⁻¹' W) := by rw [hZ]
      _ = ((rangeIso j).inv ≫ j) ⁻¹' W := rfl
      _ = _ := by rw [rangeIso_inv_j]
  exact transportTargetIso (rangeIso j).symm hp hz (d.restrict j.opensRange hdiscard)

/-- The actual restriction followed by the inverse range isomorphism preserves generic etaleness. -/
theorem restrictToOriginal_genericallyEtale
    {p : X ⟶ Spec (CommRingCat.of k)} {q : Y ⟶ Spec (CommRingCat.of k)}
    {Z : Set X} {W : Set Y} (j : X ⟶ Y) [IsOpenImmersion j] [Nonempty X]
    (hover : j ≫ q = p) (hZ : j ⁻¹' W = Z) (hdiscard : (Set.range j)ᶜ ⊆ W)
    (d : AlterationWithBoundary q W) (hd : IsGenericallyEtale d.alteration) :
    IsGenericallyEtale (restrictToOriginal j hover hZ hdiscard d).alteration := by
  let : Nonempty j.opensRange := Nonempty.map (rangeIso j).hom inferInstance
  change IsGenericallyEtale
    ((d.restrict j.opensRange hdiscard).alteration ≫ (rangeIso j).inv)
  exact (d.restrict_genericallyEtale j.opensRange hdiscard hd).comp
    (isGenericallyEtale_of_etale (rangeIso j).inv)

/-- The original projective-case compactification and its smoothness are retained exactly. -/
theorem restrictToOriginal_perfectRefinement
    {p : X ⟶ Spec (CommRingCat.of k)} {q : Y ⟶ Spec (CommRingCat.of k)}
    {Z : Set X} {W : Set Y} (j : X ⟶ Y) [IsOpenImmersion j] [Nonempty X]
    (hover : j ≫ q = p) (hZ : j ⁻¹' W = Z) (hdiscard : (Set.range j)ᶜ ⊆ W)
    (d : AlterationWithBoundary q W) (hd : IsGenericallyEtale d.alteration)
    (hs : Smooth d.compactificationStructure) :
    IsGenericallyEtale (restrictToOriginal j hover hZ hdiscard d).alteration ∧
      Smooth (restrictToOriginal j hover hZ hdiscard d).compactificationStructure :=
  ⟨restrictToOriginal_genericallyEtale j hover hZ hdiscard d hd, hs⟩

/-- The full conditional reduction in source 4.7: actual projective-case outputs produce outputs on the original quasi-projective variety. -/
theorem reduce_projective_case
    (p : X ⟶ Spec (CommRingCat.of k)) [IsVariety p]
    (hp : IsQuasiProjectiveOver p) (Z : Closeds X) (hZ : Z ≠ ⊤)
    (hprojective : ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of k)),
      IsVariety q → IsProjectiveOver q → ∀ W : Closeds Y, W ≠ ⊤ →
        Nonempty (AlterationWithBoundary q (W : Set Y))) :
    Nonempty (AlterationWithBoundary p (Z : Set X)) := by
  obtain ⟨Y, q, j, D, hq, hproj, hj, _hdom, hbase, hsupport, hcomap, hproper⟩ :=
    exists_compactification_with_boundary p hp Z
  let := hj
  obtain ⟨d⟩ := hprojective Y q hq hproj D.support (hproper hZ)
  have hpre : j ⁻¹' (D.support : Set Y) = (Z : Set X) := by
    simpa only [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage] using
      congrArg (fun T : Closeds X => (T : Set X)) hcomap
  have hdiscard : (Set.range j)ᶜ ⊆ (D.support : Set Y) := by
    intro y hy
    rw [hsupport]
    exact Or.inr hy
  exact ⟨restrictToOriginal j hbase hpre hdiscard d⟩

/-- The same actual source 4.7 reduction preserves generic etaleness and the identical smooth compactification morphism. -/
theorem reduce_projective_case_refined
    (p : X ⟶ Spec (CommRingCat.of k)) [IsVariety p]
    (hp : IsQuasiProjectiveOver p) (Z : Closeds X) (hZ : Z ≠ ⊤)
    (hprojective : ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of k)),
      IsVariety q → IsProjectiveOver q → ∀ W : Closeds Y, W ≠ ⊤ →
        ∃ d : AlterationWithBoundary q (W : Set Y),
          IsGenericallyEtale d.alteration ∧ Smooth d.compactificationStructure) :
    ∃ d : AlterationWithBoundary p (Z : Set X),
      IsGenericallyEtale d.alteration ∧ Smooth d.compactificationStructure := by
  obtain ⟨Y, q, j, D, hq, hproj, hj, _hdom, hbase, hsupport, hcomap, hproper⟩ :=
    exists_compactification_with_boundary p hp Z
  let := hj
  obtain ⟨d, hd, hs⟩ := hprojective Y q hq hproj D.support (hproper hZ)
  have hpre : j ⁻¹' (D.support : Set Y) = (Z : Set X) := by
    simpa only [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage] using
      congrArg (fun T : Closeds X => (T : Set X)) hcomap
  have hdiscard : (Set.range j)ᶜ ⊆ (D.support : Set Y) := by
    intro y hy
    rw [hsupport]
    exact Or.inr hy
  exact ⟨restrictToOriginal j hbase hpre hdiscard d,
    restrictToOriginal_perfectRefinement j hbase hpre hdiscard d hd hs⟩

end Geometry.QuasiProjectiveCompactification

end DeJongAlterations
