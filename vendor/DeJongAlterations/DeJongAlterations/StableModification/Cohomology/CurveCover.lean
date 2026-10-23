/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Cohomology.CechPushforward
import DeJongAlterations.StableModification.Cohomology.FiniteCoordinates
import DeJongAlterations.Projective

/-!
# Vanishing of Čech cohomology above the length of an affine cover

On a scheme `X` with affine diagonal, every finite cover of `X` by affine opens computes the same
Čech cohomology of a quasi-coherent module (lane COH1, `cechCohomologyIsoOfAffineCovers`). Hence,
if `X` has *some* finite affine cover with `r` members, then `Ȟᵖ(U, F) = 0` for `p ≥ r` and *every*
finite affine cover `U` (`isZero_cechCohomology_of_finiteAffineCover`).

For curves this gives the vanishing `Ȟⁱ = 0` for `i ≥ 2` which the two-term Mumford complex over a
valuation ring needs (`ValuationRing` chapter, `thm:sm-cohomology-valuation`), in two forms:

* `isZero_cechCohomology_of_two_affine`: `X` is the union of two affine opens (for a projective
  curve over a local base: the complements of two hypersurfaces without common point on `X`);
* `isZero_cechCohomology_of_isAffineHom`: there is an affine morphism `π : X → Y` to a scheme with
  a finite affine cover by `r` opens, e.g. a finite morphism to `ℙ¹` (whose two standard charts
  are projective coordinates, `isZero_cechCohomology_of_isAffineHom_projectiveCoordinates`);
* `isZero_cechCohomology_of_hypersurfaces`: `X` is a closed subscheme of `ℙⁿ_A` and two
  homogeneous forms of positive degree have no common zero on `X` (the complements `D₊(f) ∩ X`
  are affine, `isAffineOpen_preimage_basicOpen`); over a local ring `A` and for `X` universally
  closed over `A` it suffices that they have no common zero on the closed fibre
  (`eq_top_of_closedFibre_le`, `isZero_cechCohomology_of_hypersurfaces_closedFibre`).

The existence of such forms for a projective curve over a local base (a statement about curves
over the residue field) is not proved here. Blueprint:
`sm-cohomology-valuation.tex`, `lem:sm-val-curve-cover`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace DeJongAlterations.StableModification.Cohomology

noncomputable section

variable {X : Scheme.{u}} {R : Type u} [CommRing R] (F : X.Modules) [F.IsQuasicoherent]
  (c : R →+* Γ(X, ⊤))

/-- **Vanishing above the length of an affine cover**: on a scheme with affine diagonal, if some
finite affine cover `𝒱` has at most `p` members, then `Ȟᵖ(U, F) = 0` for every finite cover `U`
by affine opens and every quasi-coherent `F`. -/
theorem isZero_cechCohomology_of_finiteAffineCover
    [IsAffineHom (pullback.diagonal (terminal.from X))] {ι : Type u} [LinearOrder ι] [Fintype ι]
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) (hUa : ∀ i, IsAffineOpen (U i))
    (𝒱 : FiniteAffineCover X) (p : ℕ) (hp : Nat.card 𝒱.ι ≤ p) :
    IsZero (cechCohomology F U c p) := by
  have := Fintype.ofFinite 𝒱.ι
  exact (isZero_cechCohomology_of_card_le F 𝒱.U c p (by rwa [Nat.card_eq_fintype_card] at hp)).of_iso
    (cechCohomologyIsoOfAffineCovers F c hU 𝒱.iSup_eq_top hUa 𝒱.isAffineOpen p)

/-- The cover of `X` by two affine opens `W₀`, `W₁`, on a scheme with affine diagonal. -/
def FiniteAffineCover.ofTwo [IsAffineHom (pullback.diagonal (terminal.from X))]
    (W₀ W₁ : X.Opens) (h₀ : IsAffineOpen W₀) (h₁ : IsAffineOpen W₁) (h : W₀ ⊔ W₁ = ⊤) :
    FiniteAffineCover X where
  ι := ULift.{u} (Fin 2)
  U i := ![W₀, W₁] i.down
  iSup_eq_top := by
    apply top_unique
    rw [← h]
    refine sup_le ?_ ?_
    · exact le_iSup (fun i : ULift.{u} (Fin 2) => ![W₀, W₁] i.down) ⟨0⟩
    · exact le_iSup (fun i : ULift.{u} (Fin 2) => ![W₀, W₁] i.down) ⟨1⟩
  isAffineOpen_inf T hT := by
    have haff : ∀ i : ULift.{u} (Fin 2), IsAffineOpen (![W₀, W₁] i.down) := by
      rintro ⟨i⟩
      fin_cases i
      · exact h₀
      · exact h₁
    simpa [Finset.inf_eq_iInf] using
      IsAffineOpen.biInf (T : Set (ULift.{u} (Fin 2))) T.finite_toSet
        (Finset.coe_nonempty.mpr hT) (fun i _ => haff i)

/-- **Two affine opens give vanishing in degrees `≥ 2`**: if a scheme with affine diagonal is the
union of two affine opens, then `Ȟᵖ(U, F) = 0` for `p ≥ 2`, every finite cover `U` by affine
opens and every quasi-coherent `F`. -/
theorem isZero_cechCohomology_of_two_affine
    [IsAffineHom (pullback.diagonal (terminal.from X))] {ι : Type u} [LinearOrder ι] [Fintype ι]
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) (hUa : ∀ i, IsAffineOpen (U i))
    (W₀ W₁ : X.Opens) (h₀ : IsAffineOpen W₀) (h₁ : IsAffineOpen W₁) (h : W₀ ⊔ W₁ = ⊤)
    (p : ℕ) (hp : 2 ≤ p) : IsZero (cechCohomology F U c p) :=
  isZero_cechCohomology_of_finiteAffineCover F c U hU hUa (FiniteAffineCover.ofTwo W₀ W₁ h₀ h₁ h) p
    (by simpa [FiniteAffineCover.ofTwo] using hp)

/-- **Affine morphisms to schemes with short affine covers**: if `π : X → Y` is affine, `X` has
affine diagonal and `Y` has a finite affine cover with at most `p` members, then `Ȟᵖ(U, F) = 0`
for every finite cover `U` of `X` by affine opens and every quasi-coherent `F` on `X`. -/
theorem isZero_cechCohomology_of_isAffineHom
    [IsAffineHom (pullback.diagonal (terminal.from X))] {Y : Scheme.{u}} (π : X ⟶ Y)
    [IsAffineHom π] {ι : Type u} [LinearOrder ι] [Fintype ι]
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) (hUa : ∀ i, IsAffineOpen (U i))
    (𝒲 : FiniteAffineCover Y) (p : ℕ) (hp : Nat.card 𝒲.ι ≤ p) :
    IsZero (cechCohomology F U c p) :=
  isZero_cechCohomology_of_finiteAffineCover F c U hU hUa (𝒲.comap (π := π)) p hp

/-- **Finite morphisms to `ℙ¹`**: if `π : X → Y` is affine, `X` has affine diagonal and `Y` has
projective coordinates with two charts (e.g. `Y = ℙ¹_A`), then `Ȟᵖ(U, F) = 0` for `p ≥ 2`, every
finite cover `U` of `X` by affine opens and every quasi-coherent `F` on `X`. -/
theorem isZero_cechCohomology_of_isAffineHom_projectiveCoordinates
    [IsAffineHom (pullback.diagonal (terminal.from X))] {Y : Scheme.{u}} (π : X ⟶ Y)
    [IsAffineHom π] {A : Type u} [CommRing A] {d : A →+* Γ(Y, ⊤)}
    (D : ProjectiveCoordinates Y A d) (hD : Fintype.card D.ι = 2)
    {ι : Type u} [LinearOrder ι] [Fintype ι]
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) (hUa : ∀ i, IsAffineOpen (U i))
    (p : ℕ) (hp : 2 ≤ p) : IsZero (cechCohomology F U c p) :=
  isZero_cechCohomology_of_isAffineHom F c π U hU hUa D.toFiniteAffineCover p
    (by rw [← hD] at hp; exact (Nat.card_eq_fintype_card (α := D.ι)).trans_le hp)

section Hypersurfaces

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **Opens containing the closed fibre.** For a universally closed `p : X → Spec A` over a local
ring `A`, an open subset of `X` containing every point of the closed fibre is all of `X` (the
image of its closed complement is closed, so it contains the closed point if it is nonempty). -/
theorem eq_top_of_closedFibre_le {A : Type u} [CommRing A] [IsLocalRing A] {Y : Scheme.{u}}
    (q : Y ⟶ Spec (CommRingCat.of A)) [UniversallyClosed q] (W : Y.Opens)
    (hW : ∀ y : Y, q y = IsLocalRing.closedPoint A → y ∈ W) : W = ⊤ := by
  refine eq_top_iff.mpr fun z _ => ?_
  by_contra hz
  have hclosed : IsClosed (q '' (W : Set Y)ᶜ) := q.isClosedMap _ W.isOpen.isClosed_compl
  obtain ⟨z', hz', hz'q⟩ := (IsLocalRing.specializes_closedPoint (q z)).mem_closed hclosed
    ⟨z, hz, rfl⟩
  exact hz' (hW z' hz'q)

/-- **Complements of hypersurfaces are affine**: for a closed immersion `i : X → ℙⁿ_A` and a
homogeneous form `f` of positive degree, `i⁻¹ D₊(f)` is an affine open of `X`. -/
theorem isAffineOpen_preimage_basicOpen {A : Type u} [CommRing A] {n : ℕ}
    (i : X ⟶ projectiveSpace A n) [IsClosedImmersion i] (f : MvPolynomial (Fin (n + 1)) A)
    {d : ℕ} (hf : f ∈ projectiveSpaceGrading A n d) (hd : 0 < d) :
    IsAffineOpen (i ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading A n) f) := by
  have : IsAffineHom i := inferInstance
  exact @IsAffineOpen.preimage X (projectiveSpace A n) _
    (Proj.isAffineOpen_basicOpen (projectiveSpaceGrading A n) f hf hd) i this

/-- **Two hypersurfaces without common zero give vanishing in degrees `≥ 2`**: if `X` (with affine
diagonal) is a closed subscheme of `ℙⁿ_A` and two homogeneous forms `f`, `g` of positive degree
have no common zero on `X`, then `Ȟᵖ(U, F) = 0` for `p ≥ 2`, every finite cover `U` of `X` by
affine opens and every quasi-coherent `F`. -/
theorem isZero_cechCohomology_of_hypersurfaces
    [IsAffineHom (pullback.diagonal (terminal.from X))] {A : Type u} [CommRing A] {n : ℕ}
    (i : X ⟶ projectiveSpace A n) [IsClosedImmersion i] {ι : Type u} [LinearOrder ι] [Fintype ι]
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) (hUa : ∀ i, IsAffineOpen (U i))
    (f g : MvPolynomial (Fin (n + 1)) A) {d e : ℕ} (hf : f ∈ projectiveSpaceGrading A n d)
    (hd : 0 < d) (hg : g ∈ projectiveSpaceGrading A n e) (he : 0 < e)
    (hcov : i ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading A n) f ⊔
      i ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading A n) g = ⊤)
    (p : ℕ) (hp : 2 ≤ p) : IsZero (cechCohomology F U c p) :=
  isZero_cechCohomology_of_two_affine F c U hU hUa _ _
    (isAffineOpen_preimage_basicOpen i f hf hd) (isAffineOpen_preimage_basicOpen i g hg he) hcov
    p hp

/-- **Two hypersurfaces without common zero on the closed fibre**: as
`isZero_cechCohomology_of_hypersurfaces`, for `X` universally closed over a local ring `A`, when
`f` and `g` have no common zero on the closed fibre. -/
theorem isZero_cechCohomology_of_hypersurfaces_closedFibre
    [IsAffineHom (pullback.diagonal (terminal.from X))] {A : Type u} [CommRing A] [IsLocalRing A]
    {n : ℕ} (i : X ⟶ projectiveSpace A n) [IsClosedImmersion i]
    (q : X ⟶ Spec (CommRingCat.of A)) [UniversallyClosed q] {ι : Type u} [LinearOrder ι]
    [Fintype ι] (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) (hUa : ∀ i, IsAffineOpen (U i))
    (f g : MvPolynomial (Fin (n + 1)) A) {d e : ℕ} (hf : f ∈ projectiveSpaceGrading A n d)
    (hd : 0 < d) (hg : g ∈ projectiveSpaceGrading A n e) (he : 0 < e)
    (hcov : ∀ x : X, q x = IsLocalRing.closedPoint A →
      x ∈ i ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading A n) f ⊔
        i ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading A n) g)
    (p : ℕ) (hp : 2 ≤ p) : IsZero (cechCohomology F U c p) :=
  isZero_cechCohomology_of_hypersurfaces F c i U hU hUa f g hf hd hg he
    (eq_top_of_closedFibre_le q _ hcov) p hp

end Hypersurfaces

end

end DeJongAlterations.StableModification.Cohomology
