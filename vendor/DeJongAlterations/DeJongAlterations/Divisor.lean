import DeJongAlterations.Regular
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Regular.Basic

/-!
# Divisors with strict normal crossings

The conditions of de Jong 1996, 2.3--2.4, stated with native ideal sheaves,
scheme-theoretic intersections and dimensions of ambient local rings.
-/

open AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace DeJongAlterations

variable {X : Scheme.{u}}

/-- An effective Cartier divisor is locally cut out by one non-zero-divisor.
The unit ideal is allowed, so the empty divisor is included. -/
def IsEffectiveCartierDivisor (D : X.IdealSheafData) : Prop :=
  ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
    ∃ t : Γ(X, U.1), IsRegular t ∧ D.ideal U = Ideal.span {t}

/-- The actual irreducible components of the support, as closed subsets of the ambient scheme. -/
def DivisorComponent (D : X.IdealSheafData) :=
  {C : Closeds X // ∃ S ∈ irreducibleComponents D.support,
    (Subtype.val : D.support → X) '' S = (C : Set X)}

/-- Every actual irreducible component of the support gives a divisor component.
Closedness of the support ensures that its ambient image is closed. -/
def divisorComponentOf (D : X.IdealSheafData) (S : Set D.support)
    (hS : S ∈ irreducibleComponents D.support) : DivisorComponent D :=
  ⟨⟨Subtype.val '' S, D.support.isClosed.isClosedEmbedding_subtypeVal.isClosedMap
      S (isClosed_of_mem_irreducibleComponents S hS)⟩, S, hS, rfl⟩

/-- In a Noetherian ambient space there are only finitely many divisor components. -/
instance divisorComponent_finite (D : X.IdealSheafData) [NoetherianSpace X] :
    Finite (DivisorComponent D) := by
  let : NoetherianSpace D.support := Topology.IsInducing.subtypeVal.noetherianSpace
  let : Finite {S : Set D.support // S ∈ irreducibleComponents D.support} :=
    (NoetherianSpace.finite_irreducibleComponents (α := D.support)).to_subtype
  apply Finite.of_surjective
    (fun S : {S : Set D.support // S ∈ irreducibleComponents D.support} =>
      divisorComponentOf D S.val S.property)
  intro C
  obtain ⟨S, hS, h⟩ := C.property
  refine ⟨⟨S, hS⟩, ?_⟩
  apply Subtype.ext
  exact SetLike.coe_injective h

/-- Scheme-theoretic intersection of reduced irreducible components.
The sum of the vanishing ideal sheaves is used, without taking its radical. -/
def componentIntersection (D : X.IdealSheafData) (J : Finset (DivisorComponent D)) :
    X.IdealSheafData :=
  ⨆ C ∈ J, Scheme.IdealSheafData.vanishingIdeal C.val

/-- The support of the scheme-theoretic component intersection is the actual
intersection of the component closed subsets. -/
theorem componentIntersection_support (D : X.IdealSheafData)
    (J : Finset (DivisorComponent D)) :
    (componentIntersection D J).support = ⨅ C ∈ J, C.val := by
  simp only [componentIntersection, Scheme.IdealSheafData.support_iSup]
  rfl

/-- Radical ideal sheaves with equal supports are equal. -/
theorem idealSheaf_eq_of_radical_of_support_eq (I J : X.IdealSheafData)
    (hI : I.radical = I) (hJ : J.radical = J) (h : I.support = J.support) : I = J := by
  rw [← hI, ← hJ, ← Scheme.IdealSheafData.vanishingIdeal_support,
    ← Scheme.IdealSheafData.vanishingIdeal_support, h]

set_option backward.isDefEq.respectTransparency false in
/-- A reduced closed subscheme is cut out by a radical ideal sheaf. -/
theorem idealSheaf_radical_eq_of_isReduced (D : X.IdealSheafData)
    [AlgebraicGeometry.IsReduced D.subscheme] : D.radical = D := by
  ext U : 2
  change (D.ideal U).radical = D.ideal U
  have hspec : AlgebraicGeometry.IsReduced
      (Spec (CommRingCat.of (Γ(X, U.1) ⧸ D.ideal U))) :=
    isReduced_of_isOpenImmersion (D.subschemeCover.f U)
  have hred : _root_.IsReduced (Γ(X, U.1) ⧸ D.ideal U) :=
    (affine_isReduced_iff _).mp hspec
  exact ((Ideal.isRadical_iff_quotient_reduced _).mpr hred).radical

/-- A reduced closed subscheme is uniquely determined by its support. -/
theorem idealSheaf_eq_of_isReduced_of_support_eq (I J : X.IdealSheafData)
    [AlgebraicGeometry.IsReduced I.subscheme] [AlgebraicGeometry.IsReduced J.subscheme]
    (h : I.support = J.support) : I = J :=
  idealSheaf_eq_of_radical_of_support_eq I J
    (idealSheaf_radical_eq_of_isReduced I) (idealSheaf_radical_eq_of_isReduced J) h

/-- Pure codimension measured at the generic point of every irreducible component.
The ambient local-ring dimension equals codimension for the Noetherian schemes
occurring in the theorem. Empty closed subsets have every pure codimension. -/
def HasPureCodimension (T : Closeds X) (r : ℕ) : Prop :=
  ∀ C ∈ irreducibleComponents T, ∀ x : X,
    IsGenericPoint x ((Subtype.val : T → X) '' C) →
      ringKrullDim (X.presheaf.stalk x) = r

/-- De Jong 2.4: a reduced effective Cartier divisor, regular ambient local
rings along its support, and regular intersections of distinct components
with the expected codimension. Intersections retain their scheme structure. -/
structure IsStrictNormalCrossings (D : X.IdealSheafData) : Prop where
  cartier : IsEffectiveCartierDivisor D
  reduced : AlgebraicGeometry.IsReduced D.subscheme
  regularAlong : ∀ x : X, x ∈ D.support → IsRegularLocalRing (X.presheaf.stalk x)
  intersectionsRegular : ∀ J : Finset (DivisorComponent D), J.Nonempty →
    IsRegularScheme (componentIntersection D J).subscheme
  intersectionsCodimension : ∀ J : Finset (DivisorComponent D), J.Nonempty →
    HasPureCodimension (componentIntersection D J).support J.card

/-- The empty divisor is effective Cartier: its local equation is the unit. -/
theorem isEffectiveCartierDivisor_top (X : Scheme.{u}) :
    IsEffectiveCartierDivisor (⊤ : X.IdealSheafData) := by
  intro x
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (x := x)
    (U := (⊤ : X.Opens)) (by trivial)
  refine ⟨⟨U, hU⟩, hxU, 1, isUnit_one.isRegular, ?_⟩
  simp

/-- The empty divisor has strict normal crossings, including on an empty scheme. -/
theorem isStrictNormalCrossings_top (X : Scheme.{u}) :
    IsStrictNormalCrossings (⊤ : X.IdealSheafData) := by
  have noComponent : ∀ C : DivisorComponent (⊤ : X.IdealSheafData), False := by
    intro C
    obtain ⟨S, hS, _⟩ := C.property
    obtain ⟨x, _⟩ := hS.1.nonempty
    exact (show False from x.property)
  have reduced : AlgebraicGeometry.IsReduced (⊤ : X.IdealSheafData).subscheme := by
    let : ∀ x : (⊤ : X.IdealSheafData).subscheme,
        _root_.IsReduced ((⊤ : X.IdealSheafData).subscheme.presheaf.stalk x) :=
      fun x => isEmptyElim x
    exact isReduced_of_isReduced_stalk _
  refine ⟨isEffectiveCartierDivisor_top X, reduced, ?_, ?_, ?_⟩
  · intro x hx
    exact (show False from hx).elim
  · intro J hJ
    obtain ⟨C, _⟩ := hJ
    exact (noComponent C).elim
  · intro J hJ
    obtain ⟨C, _⟩ := hJ
    exact (noComponent C).elim

end DeJongAlterations
