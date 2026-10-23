import DeJongAlterations.StableModification.Resolution.StrictifyAlgebra
import DeJongAlterations.Geometry.CompletedLocalRing
import DeJongAlterations.Geometry.ReducedClosedSubscheme
import DeJongAlterations.Algebra.CompletionRegularityBasics
import DeJongAlterations.Algebra.NodeFittingGeometricNodeSupport
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Normal crossings divisors in completed-local form

Let `X` be a locally Noetherian scheme. For a closed subset `F ⊆ X` and a point `x` we write
`I(F)_x ⊆ 𝒪_{X,x}` for the ideal of germs vanishing on `F` (`localIdeal`, the stalk of the
vanishing ideal sheaf, i.e. of the reduced induced structure) and `I(F)_x Ô_{X,x}` for its
extension to the completion (`formalIdeal`).

A *normal crossings chart* (`NCChart`) at a closed point `x` for a finite family of closed
subsets `F_l` is a regular system of parameters `t_1, …, t_n` of `Ô_{X,x}` (elements of the
maximal ideal generating it, with linearly independent classes in `𝔪/𝔪²`) together with pairwise
disjoint sets `A_l ⊆ {1, …, n}` such that `I(F_l)_x Ô_{X,x} = (∏_{i ∈ A_l} t_i)` for every `l`. The
family is a *normal crossings family* with multiplicities at most `b_l` (`IsNCFamily F b`) if such
a chart with `|A_l| ≤ b_l` exists at every closed point. A closed subset `Z` is a *normal
crossings divisor* (`IsNormalCrossings`) if the one-member family `Z` has a chart at every closed
point: `I(Z)_x Ô_{X,x} = (t_1 ⋯ t_s)` for part `t_1, …, t_s` of a regular system of parameters.

This is the completed-local form of de Jong's normal crossings divisors (de Jong 1996, 2.4,
`references/dejong96-alterations/tex/page-0006.tex`: a divisor which becomes a strict normal
crossings divisor after a surjective étale base change); it is the form produced by the
resolution of semi-stable curves (de Jong 4.26–4.28, `page-0027.tex`, where the boundary is
computed in completed local coordinates).

## Main results

* `localIdeal_ne_top_iff`, `formalIdeal_ne_top_iff`: `x ∈ F` iff `I(F)_x` is proper.
* `localIdeal_preimage`: `I(f⁻¹F)_y = √(I(F)_{f(y)} 𝒪_{Y,y})`.
* `stalkIdeal_radical`: stalks commute with radicals of ideal sheaves.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

namespace DeJongAlterations.StableModification.Resolution.Strictify

set_option backward.isDefEq.respectTransparency false

open Algebra.NodeFittingIdealSheaf Algebra.NodeFittingGeometricNodeSupport

universe u

variable {X Y : Scheme.{u}}

/-- The ideal of germs at `x` vanishing on the closed subset `F`. -/
def localIdeal (F : Closeds X) (x : X) : Ideal (X.presheaf.stalk x) :=
  stalkIdeal (Scheme.IdealSheafData.vanishingIdeal F) x

/-- The extension of `localIdeal F x` to the completed local ring. -/
def formalIdeal (F : Closeds X) (x : X) : Ideal (X.completedLocalRing x) :=
  (localIdeal F x).map (X.toCompletedLocalRing x)

/-- A normal crossings chart at `x` for the family `F`: a regular system of parameters `t` of
`Ô_{X,x}` and disjoint index sets `A l` with `I(F l)_x Ô_{X,x} = (∏_{i ∈ A l} t_i)`. -/
structure NCChart [IsLocallyNoetherian X] {ι : Type*} (F : ι → Closeds X) (x : X) where
  /-- The number of parameters. -/
  n : ℕ
  /-- The parameters. -/
  t : Fin n → maximalIdeal (X.completedLocalRing x)
  /-- The parameters have linearly independent classes in `𝔪/𝔪²`. -/
  indep : LinearIndependent (ResidueField (X.completedLocalRing x))
    fun i ↦ (maximalIdeal (X.completedLocalRing x)).toCotangent (t i)
  /-- The parameters generate the maximal ideal. -/
  span_eq : Ideal.span (Set.range fun i ↦ (t i : X.completedLocalRing x)) =
    maximalIdeal (X.completedLocalRing x)
  /-- The branches of each member of the family. -/
  A : ι → Finset (Fin n)
  /-- Distinct members have no common branch. -/
  disjoint : Pairwise fun l l' ↦ Disjoint (A l) (A l')
  /-- The completed-local equations. -/
  formalIdeal_eq : ∀ l, formalIdeal (F l) x =
    Ideal.span {∏ i ∈ A l, (t i : X.completedLocalRing x)}

/-- A finite family of closed subsets is a *normal crossings family* with multiplicities at most
`b` if at every closed point it has a normal crossings chart with `|A l| ≤ b l`. -/
def IsNCFamily [IsLocallyNoetherian X] {ι : Type*} (F : ι → Closeds X) (b : ι → ℕ) : Prop :=
  ∀ x : X, IsClosed ({x} : Set X) → ∃ c : NCChart F x, ∀ l, (c.A l).card ≤ b l

/-- **Normal crossings divisors** (de Jong 2.4, completed-local form): at every closed point `x`,
`I(Z)_x Ô_{X,x} = (t_1 ⋯ t_s)` for part `t_1, …, t_s` of a regular system of parameters. -/
def IsNormalCrossings [IsLocallyNoetherian X] (Z : Closeds X) : Prop :=
  ∀ x : X, IsClosed ({x} : Set X) → Nonempty (NCChart (fun _ : Unit ↦ Z) x)

section Stalk

theorem localIdeal_le_maximalIdeal_iff (F : Closeds X) (x : X) :
    localIdeal F x ≤ maximalIdeal (X.presheaf.stalk x) ↔ x ∈ F := by
  rw [localIdeal, ← mem_support_iff_stalkIdeal_le_maximalIdeal,
    Geometry.ReducedClosedSubscheme.support_vanishingIdeal]

/-- `x ∈ F` iff the ideal of `F` at `x` is proper. -/
theorem localIdeal_ne_top_iff (F : Closeds X) (x : X) : localIdeal F x ≠ ⊤ ↔ x ∈ F := by
  rw [← localIdeal_le_maximalIdeal_iff]
  exact ⟨fun h ↦ le_maximalIdeal h, fun h htop ↦ (maximalIdeal.isMaximal _).ne_top
    (top_unique (htop ▸ h))⟩

variable [IsLocallyNoetherian X]

/-- `x ∈ F` iff the completed ideal of `F` at `x` is proper. -/
theorem formalIdeal_ne_top_iff (F : Closeds X) (x : X) : formalIdeal F x ≠ ⊤ ↔ x ∈ F := by
  rw [← localIdeal_ne_top_iff]
  constructor
  · intro h htop
    apply h
    rw [formalIdeal, htop, Ideal.map_top]
  · intro h htop
    apply h
    have := Algebra.CompletionRegularityBasics.comap_map (X.presheaf.stalk x) (localIdeal F x)
    rw [← this]
    change Ideal.comap (algebraMap _ _) (formalIdeal F x) = ⊤
    rw [htop, Ideal.comap_top]

end Stalk

section Radical

/-- Stalks of ideal sheaves commute with radicals. -/
theorem stalkIdeal_radical (J : X.IdealSheafData) (x : X) :
    stalkIdeal J.radical x = (stalkIdeal J x).radical := by
  obtain ⟨U, hxU⟩ := exists_affineOpens_mem x
  rw [stalkIdeal_eq_map_germ _ U hxU, stalkIdeal_eq_map_germ _ U hxU,
    Scheme.IdealSheafData.radical_ideal]
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  have hloc := U.2.isLocalization_stalk ⟨x, hxU⟩
  exact IsLocalization.map_radical (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
    (X.presheaf.stalk x) (J.ideal U)

/-- The ideal of a preimage: `I(f⁻¹F)_y = √(I(F)_{f(y)} 𝒪_{Y,y})`. -/
theorem localIdeal_preimage (f : Y ⟶ X) (F : Closeds X) (y : Y) :
    localIdeal (F.preimage f.continuous) y =
      ((localIdeal F (f y)).map (f.stalkMap y).hom).radical := by
  have h : Scheme.IdealSheafData.vanishingIdeal (F.preimage f.continuous) =
      ((Scheme.IdealSheafData.vanishingIdeal F).comap f).radical := by
    rw [← Scheme.IdealSheafData.vanishingIdeal_support, Scheme.IdealSheafData.support_comap,
      Geometry.ReducedClosedSubscheme.support_vanishingIdeal]
  rw [localIdeal, h, stalkIdeal_radical, stalkIdeal_comap]
  rfl

end Radical

end DeJongAlterations.StableModification.Resolution.Strictify
