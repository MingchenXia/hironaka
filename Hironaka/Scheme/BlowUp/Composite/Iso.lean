/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.Composite
import Hironaka.Scheme.BlowUp.Composite.Main
import Hironaka.Scheme.BlowUp.Glue.Global
import Hironaka.Scheme.BlowUp.Glue.Product
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.BlowUp.Transform
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The composite of two blow-ups is one blow-up

With `b : X' ⟶ X` the blow-up along `I`, `E` its exceptional ideal, `J'` an ideal sheaf on `X'` and
`K_m = descendCenter I J' m` Hironaka's `J(m)` with `K_m.comap b = J' · E^m`
(`Hironaka.Scheme.BlowUp.Composite.Main`), the chain of canonical isomorphisms over `X`

  `B_{J'} X' ≅ B_{J' E^m} X' = B_{K_m 𝒪_{X'}} X' ≅ B_{I K_m} X`

gives Hironaka's unique isomorphism `h : X' → X₂` with `f' = f₀ ∘ f₁ ∘ h` between the composite of
the two monoidal transformations and the monoidal transformation with centre `J(m) J₀`
[Hir64, Ch. 0, §3, p. 133]; [Sta, Tag 080B].  The first step is the blow-up of a product with an
invertible factor (`blowUp.exists_mul_isInvertible_iso`, read backwards), the second the equality
of centres, the third the blow-up of a product centre (`blowUp.exists_mulIso`).  Isomorphisms over
`X` compose, and a canonical one stays canonical (`exists_unique_iso_over_of_iso`).
`blowUp.exists_comp_iso` chooses `m = m₀` and adds the support `|V(K)| = |Z| ∪ b(|Z'|)`.  The
result is used for the composite of a blow-up sequence
(`Hironaka.Scheme.BlowUpSequence.CompositeBlowUp`).
-/

public section

namespace AlgebraicGeometry

open Scheme.IdealSheafData

open AlgebraicGeometry CategoryTheory Scheme.IdealSheafData

universe u

section IsoOver

variable {A B C X : Scheme.{u}}

/-- Composing an isomorphism `e₁ : A ≅ B` over `X` with a canonical isomorphism `B ≅ C` over `X`
gives a canonical isomorphism `A ≅ C` over `X`: a morphism `ψ : A ⟶ C` over `X` gives the
morphism `e₁.inv ≫ ψ : B ⟶ C` over `X`, which is the canonical one. -/
theorem exists_unique_iso_over_of_iso {f : A ⟶ X} {g : B ⟶ X} {h : C ⟶ X}
    (e₁ : A ≅ B) (he₁ : e₁.hom ≫ g = f)
    (h₂ : ∃ e : B ≅ C, e.hom ≫ h = g ∧ ∀ ψ : B ⟶ C, ψ ≫ h = g → ψ = e.hom) :
    ∃ e : A ≅ C, e.hom ≫ h = f ∧ ∀ ψ : A ⟶ C, ψ ≫ h = f → ψ = e.hom := by
  obtain ⟨e₂, he₂, hu₂⟩ := h₂
  refine ⟨e₁ ≪≫ e₂, by rw [Iso.trans_hom, Category.assoc, he₂, he₁], fun ψ hψ => ?_⟩
  have key : e₁.inv ≫ ψ = e₂.hom :=
    hu₂ _ (by rw [Category.assoc, hψ, ← he₁, Iso.inv_hom_id_assoc])
  rw [Iso.trans_hom, ← key, Iso.hom_inv_id_assoc]

end IsoOver

section BlowUp

variable {X : Scheme.{u}}

/-- Equal centers have the same blow-up, over `X`. -/
theorem Scheme.IdealSheafData.blowUp.exists_iso_of_eq {L L' : X.IdealSheafData} (h : L = L') :
    ∃ e : blowUp L ≅ blowUp L', e.hom ≫ blowUpπ L' = blowUpπ L := by
  subst h
  exact ⟨Iso.refl _, Category.id_comp _⟩

/-- The trivial factor read from `blowUp J` ([Sta, Tag 080B]: a power of the exceptional ideal
cuts out an effective Cartier divisor, whose blow-up is trivial): for `L` invertible,
`blowUp J ≅ blowUp (J * L)` over `X`, uniquely — the
inverse of `blowUp.exists_mul_isInvertible_iso`; uniqueness from the universal property of
`blowUp (J * L)`, the pullback `(J * L).comap (π J) = E_J · L.comap (π J)` being invertible. -/
theorem Scheme.IdealSheafData.blowUp.exists_iso_mul_isInvertible (J L : X.IdealSheafData)
    (hL : L.IsInvertible) :
    ∃ e : blowUp J ≅ blowUp (J * L), e.hom ≫ blowUpπ (J * L) = blowUpπ J ∧
      ∀ ψ : blowUp J ⟶ blowUp (J * L), ψ ≫ blowUpπ (J * L) = blowUpπ J → ψ = e.hom := by
  obtain ⟨e, he, -⟩ := blowUp.exists_mul_isInvertible_iso J L hL
  have hinv : ((J * L).comap (blowUpπ J)).IsInvertible := by
    rw [comap_mul]
    exact (blowUp.isInvertible_comap_π J).mul (blowUp.isInvertible_comap_of_isInvertible J L hL)
  refine ⟨e.symm, by rw [Iso.symm_hom, ← he, Iso.inv_hom_id_assoc], fun ψ hψ => ?_⟩
  exact blowUp.hom_ext (J * L) (blowUpπ J) hinv ψ e.symm.hom hψ
    (by rw [Iso.symm_hom, ← he, Iso.inv_hom_id_assoc])

variable (I : X.IdealSheafData) (J' : (blowUp I).IdealSheafData)

/-- The chain `B_{IK_m}X ≅ B_{K_m𝒪_{X'}}X' = B_{J'𝓘_F^m}X' ≅ B_{J'}X' = X''` over `X`
[Hir64, Ch. 0, §3, p. 133]; [Sta, Tag 080B]: if `K_m.comap b = J' · E^m`, then
`blowUp J' ≅ blowUp (I * K_m)` over `X`, by a unique isomorphism over `X`. -/
theorem Scheme.IdealSheafData.blowUp.exists_iso_of_comap_descendCenter_eq (m : ℕ)
    (hm : (descendCenter I J' m).comap (blowUpπ I) = J' * I.exceptionalDivisor ^ m) :
    ∃ e : blowUp J' ≅ blowUp (I * descendCenter I J' m),
      e.hom ≫ blowUpπ (I * descendCenter I J' m) = blowUpπ J' ≫ blowUpπ I ∧
      ∀ ψ : blowUp J' ⟶ blowUp (I * descendCenter I J' m),
        ψ ≫ blowUpπ (I * descendCenter I J' m) = blowUpπ J' ≫ blowUpπ I → ψ = e.hom := by
  obtain ⟨e₁, he₁, -⟩ := blowUp.exists_iso_mul_isInvertible J' (I.exceptionalDivisor ^ m)
    (Scheme.IdealSheafData.isInvertible_pow (blowUp.isInvertible_comap_π I) m)
  obtain ⟨e₂, he₂⟩ := blowUp.exists_iso_of_eq hm.symm
  refine exists_unique_iso_over_of_iso
    (g := blowUpπ (J' * I.exceptionalDivisor ^ m) ≫ blowUpπ I) e₁
    (by rw [← Category.assoc, he₁]) ?_
  exact exists_unique_iso_over_of_iso e₂ (by rw [← Category.assoc, he₂])
    (blowUp.exists_mulIso I (descendCenter I J' m))

/-- **A composite of two blow-ups is a blow-up** [Hir64, Ch. 0, §3, pp. 132–133]; [Sta, Tag 080B]:
for `X` Noetherian there is an ideal sheaf `K` on `X`, with `|V(K)| = |Z| ∪ b(|Z'|)`
set-theoretically, such that the composite `X'' → X' → X` is the blow-up of `X` along `K`:
`blowUp J' ≅ blowUp K` over `X`, by a unique isomorphism over `X`; `K = I * K_{m₀}` for the
exponent `m₀` of `exists_comap_descendCenter_eq`. -/
theorem Scheme.IdealSheafData.blowUp.exists_comp_iso [IsNoetherian X] :
    ∃ K : X.IdealSheafData,
      (K.support : Set X) = (I.support : Set X) ∪ blowUpπ I '' (J'.support : Set (blowUp I)) ∧
      ∃ e : blowUp J' ≅ blowUp K,
        e.hom ≫ blowUpπ K = blowUpπ J' ≫ blowUpπ I ∧
        ∀ ψ : blowUp J' ⟶ blowUp K, ψ ≫ blowUpπ K = blowUpπ J' ≫ blowUpπ I → ψ = e.hom := by
  obtain ⟨m₀, hm₀⟩ := exists_comap_descendCenter_eq I J'
  exact ⟨I * descendCenter I J' m₀, support_mul_descendCenter I J' m₀ (hm₀ m₀ le_rfl),
    blowUp.exists_iso_of_comap_descendCenter_eq I J' m₀ (hm₀ m₀ le_rfl)⟩

end BlowUp

end AlgebraicGeometry
