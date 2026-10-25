import DeJongAlterations.Geometry.ProjectiveIdealRepresentation
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Actual inverse projective charts of an affine morphism

The coordinate ratio basic opens and their localization rings are constructed
from the original morphism. This is the section-extension input for finite
projectivity preservation, including nonreduced sources.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial Opposite

namespace DeJongAlterations.Geometry.FiniteProjective

open ProjectiveIdeal

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} {n : ℕ}

/-- The actual inverse image of the ith native coordinate chart. -/
def chartOpen (g : Y ⟶ projectiveSpace R n) (i : Fin (n + 1)) : Y.Opens :=
  g ⁻¹ᵁ nativeCoordinateOpen i

/-- Pull back the whole native homogeneous-form section on its coordinate chart. -/
def chartForm (g : Y ⟶ projectiveSpace R n) (i : Fin (n + 1))
    (F : MvPolynomial (Fin (n + 1)) R) : Γ(Y, chartOpen g i) :=
  g.app (nativeCoordinateOpen i) (nativeFormSection i F)

/-- The actual coordinate ratio Xj/Xi on the original inverse chart. -/
def chartRatio (g : Y ⟶ projectiveSpace R n) (i j : Fin (n + 1)) :
    Γ(Y, chartOpen g i) := chartForm g i (X j)

/-- Every pulled-back coordinate chart is genuinely affine for an affine morphism. -/
theorem chartOpen_isAffine (g : Y ⟶ projectiveSpace R n) [IsAffineHom g]
    (i : Fin (n + 1)) : IsAffineOpen (chartOpen g i) :=
  (nativeCoordinateOpen_isAffine i).preimage g

/-- The actual basic open of a pulled-back ratio is the original chart intersection. -/
theorem chartRatio_basicOpen (g : Y ⟶ projectiveSpace R n) (i j : Fin (n + 1)) :
    Y.basicOpen (chartRatio g i j) = chartOpen g i ⊓ chartOpen g j := by
  dsimp only [chartRatio, chartForm, chartOpen]
  rw [← Scheme.preimage_basicOpen]
  exact congrArg (fun U : (NativeProjectiveScheme R n).Opens => g ⁻¹ᵁ U)
    (nativeFormSection_X_basicOpen i j)

/-- The genuine localization overlap is affine. -/
theorem chartOpen_inf_isAffine (g : Y ⟶ projectiveSpace R n) [IsAffineHom g]
    (i j : Fin (n + 1)) : IsAffineOpen (chartOpen g i ⊓ chartOpen g j) := by
  rw [← chartRatio_basicOpen]
  exact (chartOpen_isAffine g i).basicOpen _

/-- Germs of the original pulled-back ratio use the original morphism's stalk map. -/
theorem chartForm_germ (g : Y ⟶ projectiveSpace R n) (i : Fin (n + 1))
    (F : MvPolynomial (Fin (n + 1)) R) (x : Y) (hx : x ∈ chartOpen g i) :
    Y.presheaf.germ (chartOpen g i) x hx (chartForm g i F) =
      g.stalkMap x ((projectiveSpace R n).presheaf.germ (nativeCoordinateOpen i)
        (g x) hx (nativeFormSection i F)) := by
  exact (g.germ_stalkMap_apply (nativeCoordinateOpen i) x hx (nativeFormSection i F)).symm

/-- The actual self ratio is the unit section, including empty or nonreduced charts. -/
theorem chartRatio_self (g : Y ⟶ projectiveSpace R n) (i : Fin (n + 1)) :
    chartRatio g i i = 1 := by
  simp only [chartRatio, chartForm, nativeFormSection, coordinateDehom,
    MvPolynomial.aeval_X, coordinateDehomCoord_self, map_one]

/-- Actual affine localization extends a local section to each other coordinate
chart after multiplying a coordinate power. Equality holds in every overlap stalk. -/
theorem exists_chart_extension (g : Y ⟶ projectiveSpace R n) [IsAffineHom g]
    (i j : Fin (n + 1)) (b : Γ(Y, chartOpen g i)) :
    ∃ (d : ℕ) (c : Γ(Y, chartOpen g j)), ∀ (x : Y)
      (hi : x ∈ chartOpen g i) (hj : x ∈ chartOpen g j),
      Y.presheaf.germ (chartOpen g j) x hj c =
        Y.presheaf.germ (chartOpen g i) x hi b *
          Y.presheaf.germ (chartOpen g j) x hj (chartRatio g j i) ^ d := by
  let ξ := chartRatio g j i
  let W := Y.basicOpen ξ
  have hWi : W ≤ chartOpen g i := by
    change Y.basicOpen (chartRatio g j i) ≤ _
    rw [chartRatio_basicOpen]
    exact inf_le_right
  let z : Γ(Y, W) := Y.presheaf.map (homOfLE hWi).op b
  let : Algebra Γ(Y, chartOpen g j) Γ(Y, W) := Scheme.algebra_section_section_basicOpen ξ
  let : IsLocalization.Away ξ Γ(Y, W) := (chartOpen_isAffine g j).isLocalization_basicOpen ξ
  obtain ⟨d, c, hc⟩ := IsLocalization.Away.surj ξ z
  refine ⟨d, c, ?_⟩
  intro x hi hj
  have hxW : x ∈ W := by
    change x ∈ Y.basicOpen (chartRatio g j i)
    rw [chartRatio_basicOpen]
    exact ⟨hj, hi⟩
  have H := congrArg (Y.presheaf.germ W x hxW) hc
  change Y.presheaf.germ W x hxW
      (z * (Y.presheaf.map (homOfLE (Y.basicOpen_le ξ)).op ξ) ^ d) =
    Y.presheaf.germ W x hxW
      (Y.presheaf.map (homOfLE (Y.basicOpen_le ξ)).op c) at H
  have hres (t : Γ(Y, chartOpen g j)) :
      Y.presheaf.germ W x hxW
        (Y.presheaf.map (homOfLE (Y.basicOpen_le ξ)).op t) =
      Y.presheaf.germ (chartOpen g j) x hj t :=
    Y.presheaf.germ_res_apply (homOfLE (Y.basicOpen_le ξ)) x hxW t
  simpa only [z, map_mul, map_pow, hres, TopCat.Presheaf.germ_res_apply] using H.symm

/-- Actual homogeneous-form trivializations transform in the original source stalks. -/
theorem chartForm_germ_ratio (g : Y ⟶ projectiveSpace R n)
    (i j : Fin (n + 1)) (x : Y) (hi : x ∈ chartOpen g i) (hj : x ∈ chartOpen g j)
    {F : MvPolynomial (Fin (n + 1)) R} {d : ℕ} (hF : F.IsHomogeneous d) :
    Y.presheaf.germ (chartOpen g j) x hj (chartForm g j F) =
      Y.presheaf.germ (chartOpen g i) x hi (chartForm g i F) *
        Y.presheaf.germ (chartOpen g j) x hj (chartRatio g j i) ^ d := by
  simp only [chartRatio, chartForm_germ]
  simpa only [NativeProjectiveScheme, projectiveSpace, ProjectiveGrading,
    projectiveSpaceGrading, map_mul, map_pow] using congrArg (g.stalkMap x)
    (nativeFormSection_germ_ratio i j (g x) hi hj hF)

/-- Finitely many genuine denominator lifts can be raised to one common degree,
while retaining the original section on its entire original chart. -/
theorem exists_common_chart_extension (g : Y ⟶ projectiveSpace R n) [IsAffineHom g]
    (i : Fin (n + 1)) (b : Γ(Y, chartOpen g i)) :
    ∃ (d : ℕ) (s : ∀ j : Fin (n + 1), Γ(Y, chartOpen g j)), s i = b ∧
      ∀ (j : Fin (n + 1)) (x : Y) (hi : x ∈ chartOpen g i) (hj : x ∈ chartOpen g j),
        Y.presheaf.germ (chartOpen g j) x hj (s j) =
          Y.presheaf.germ (chartOpen g i) x hi b *
            Y.presheaf.germ (chartOpen g j) x hj (chartRatio g j i) ^ d := by
  classical
  choose e c hc using fun j : Fin (n + 1) => exists_chart_extension g i j b
  let d := Finset.univ.sup e
  let s (j : Fin (n + 1)) : Γ(Y, chartOpen g j) :=
    c j * chartRatio g j i ^ (d - e j)
  have ht (j : Fin (n + 1)) (x : Y) (hi : x ∈ chartOpen g i) (hj : x ∈ chartOpen g j) :
      Y.presheaf.germ (chartOpen g j) x hj (s j) =
        Y.presheaf.germ (chartOpen g i) x hi b *
          Y.presheaf.germ (chartOpen g j) x hj (chartRatio g j i) ^ d := by
    have he : e j ≤ d := Finset.le_sup (f := e) (Finset.mem_univ j)
    dsimp only [s]
    rw [map_mul, map_pow, hc j x hi hj, mul_assoc, ← pow_add, Nat.add_sub_of_le he]
  refine ⟨d, s, ?_, ht⟩
  apply TopCat.Presheaf.section_ext Y.sheaf (chartOpen g i)
  intro x hx
  change Y.presheaf.germ (chartOpen g i) x hx (s i) =
    Y.presheaf.germ (chartOpen g i) x hx b
  simpa only [chartRatio_self, map_one, one_pow, mul_one] using ht i x hx hx

end DeJongAlterations.Geometry.FiniteProjective
