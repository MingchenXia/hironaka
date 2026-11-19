/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Smooth.EtaleCover
public import Hironaka.Resolution.Algebraic.MaximalContact.Basic
import Hironaka.Scheme.IdealSheaf.Derivative.Pullback
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Étale equivalence of hypersurfaces of maximal contact

The second half of [Kol07, Definition 91] calls two hypersurfaces of maximal contact `H` and `H'`
**étale equivalent with respect to `(X, I, E)`** when there are étale surjections `ψ, ψ' : U ⇉ X`
with (1′) `ψ⁻¹(H) = ψ'⁻¹(H')`, (2′) `ψ^*(I) = ψ'^*(I)`, (3′) `ψ⁻¹(Eⁱ) = ψ'⁻¹(Eⁱ)` for every
component `Eⁱ` of `E`, and (4′) `ψ^*(h) − ψ'^*(h) ∈ MC ψ^*(I)` for every function `h` on `X`.

**Conventions.** The definition is stated for étale maps `ψ, ψ'` whose images each contain the
cosupport `cosupp(I, m) = {x | ord_x I ≥ m}` (`AlgebraicGeometry.EtaleImagePair X (cosupp I m)`)
in place of Kollár's étale surjections. With surjections, Theorem 92 would be false: for
`X = 𝔸¹`, `I = (xᵐ)`, `H = V(x)` and `H' = V(x(x − 1))`, every hypothesis of Theorem 92 holds,
but no étale surjections satisfy (1′) and (2′), since a point `u` of `U` over `1` along `ψ'` lies
over `H`, hence over `0`, along `ψ` by (1′), so `ψ^*(xᵐ)` vanishes at `u`, and then by (2′) so
does `ψ'^*(xᵐ)`, which is impossible at `1`. What the proof of Theorem 92 constructs are étale
neighbourhoods whose images cover the cosupport, and that is also what the functoriality argument
of [Kol07, Theorem 103, Step 2.3] uses. Condition (4′) is stated as the equality of morphisms
`ψ ∘ ι = ψ' ∘ ι` on the closed subscheme `V(MC(ψ^*I))` (`AgreeOn`). Kollár's `ψ, ψ'` are
morphisms of `k`-varieties: the field `comp_eq` (`ψ ≫ f = ψ' ≫ f`) records it, so that
`ψ̂' ∘ ψ̂⁻¹` is a `k`-automorphism of `Ô_{X,p}` (`FormallyEquivalentAt`,
`Hironaka/Resolution/Algebraic/MaximalContact/EtaleToFormal.lean`).

* `AgreeOn ψ ψ' M`: `ψ` and `ψ'` agree on the closed subscheme `V(M) ⊆ U`.
* `EtaleEquiv f I m E H H'`: the étale equivalence datum, an `EtaleImagePair X (cosupp I m)` with
  the conditions (1′)–(4′) and `ψ ≫ f = ψ' ≫ f`.
* `MC_comap_of_etale`: [Kol07, Lemma 74 (4)] for `MC`, `MC(ψ^*I) = ψ^*MC(I)` for an étale `ψ`
  (`derivativeIter_comap_of_smooth`), so (4′) may be read with either ideal.
* `EtaleEquiv.refl`: `H` is étale equivalent to itself through `U = X`, `ψ = ψ' = 𝟙 X`.
-/

@[expose] public section

namespace AlgebraicGeometry.Scheme.IdealSheafData

open CategoryTheory Scheme AlgebraicGeometry

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The morphisms `ψ, ψ' : U ⟶ X` **agree on the closed subscheme `V(M)`**: `ψ ∘ ι = ψ' ∘ ι` for
the closed immersion `ι : V(M) ⟶ U`. This is the form in which the condition (4′) of
[Kol07, Definition 91] is stated. -/
def AgreeOn {U : Scheme.{u}} (ψ ψ' : U ⟶ X) (M : U.IdealSheafData) : Prop :=
  M.subschemeι ≫ ψ = M.subschemeι ≫ ψ'

/-- `AgreeOn` unfolded. -/
theorem agreeOn_iff {U : Scheme.{u}} (ψ ψ' : U ⟶ X) (M : U.IdealSheafData) :
    AgreeOn ψ ψ' M ↔ M.subschemeι ≫ ψ = M.subschemeι ≫ ψ' :=
  Iff.rfl

/-- [Kol07, Definition 91], second half, with images containing the cosupport in place of
surjections: `H` and `H'` are **étale equivalent with respect to `(X, I, E)`**, for the mark `m`,
through the étale pair `ψ, ψ' : U ⟶ X` whose images each contain `cosupp(I, m) = {x | ord_x I ≥ m}`
(`EtaleImagePair`), when (1′) `ψ⁻¹(H) = ψ'⁻¹(H')`, (2′) `ψ^*I = ψ'^*I`, (3′) `ψ⁻¹(Eⁱ) = ψ'⁻¹(Eⁱ)`
for every component `Eⁱ` of `E`, and (4′) `ψ` and `ψ'` agree on `V(MC(ψ^*I))`; `ψ` and `ψ'` are
morphisms of `k`-schemes (`ψ ≫ f = ψ' ≫ f`, Kollár's varieties over `k`). Inverse images of closed
subschemes are Mathlib's `comap` of ideal sheaves. -/
structure EtaleEquiv (f : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (m : ℕ) (E : DivisorFamily X)
    (H H' : X.IdealSheafData) extends EtaleImagePair X {x | (m : ℕ∞) ≤ I.ord x} where
  /-- `ψ` and `ψ'` are morphisms of `k`-schemes. -/
  comp_eq : ψ ≫ f = ψ' ≫ f
  /-- (1′) `ψ⁻¹(H) = ψ'⁻¹(H')`. -/
  h1 : H.comap ψ = H'.comap ψ'
  /-- (2′) `ψ^*(I) = ψ'^*(I)`. -/
  h2 : I.comap ψ = I.comap ψ'
  /-- (3′) `ψ⁻¹(Eⁱ) = ψ'⁻¹(Eⁱ)` for every component. -/
  h3 : ∀ i, (E.component i).comap ψ = (E.component i).comap ψ'
  /-- (4′) `ψ` and `ψ'` agree on the closed subscheme `V(MC(ψ^*I))` (the `k`-structure of `U` is
  `ψ ≫ f`). -/
  h4 : AgreeOn ψ ψ' (MC (ψ ≫ f) (I.comap ψ) m)

namespace EtaleEquiv

variable {f : X ⟶ Spec (.of k)} {I : X.IdealSheafData} {m : ℕ} {E : DivisorFamily X}
  {H H' : X.IdealSheafData}

/-- The conditions (1′)–(4′) of an étale equivalence, bundled. -/
theorem conditions (Q : EtaleEquiv f I m E H H') :
    H.comap Q.ψ = H'.comap Q.ψ' ∧ I.comap Q.ψ = I.comap Q.ψ' ∧
      (∀ i, (E.component i).comap Q.ψ = (E.component i).comap Q.ψ') ∧
      AgreeOn Q.ψ Q.ψ' (MC (Q.ψ ≫ f) (I.comap Q.ψ) m) :=
  ⟨Q.h1, Q.h2, Q.h3, Q.h4⟩

/-- In place of Kollár's "étale surjections": the images of `ψ` and `ψ'` each contain the
cosupport `cosupp(I, m)`. -/
theorem covers_covers' (Q : EtaleEquiv f I m E H H') :
    {x | (m : ℕ∞) ≤ I.ord x} ⊆ Set.range Q.ψ.base ∧
      {x | (m : ℕ∞) ≤ I.ord x} ⊆ Set.range Q.ψ'.base :=
  ⟨Q.covers, Q.covers'⟩

/-- `ψ` and `ψ'` are morphisms over `k`: the field `comp_eq` restated. -/
theorem ψ_comp_eq (Q : EtaleEquiv f I m E H H') : Q.ψ ≫ f = Q.ψ' ≫ f :=
  Q.comp_eq

end EtaleEquiv

/-- [Kol07, Lemma 74 (4)] for `MC`, "`MC(ψ^*I) = ψ^*MC(I)`": for `X` smooth over `k` and
`ψ : U ⟶ X` étale, the maximal contact ideal of the pulled-back ideal (for the `k`-structure
`ψ ≫ f` of `U`) is the pullback of the maximal contact ideal (`derivativeIter_comap_of_smooth`). -/
theorem MC_comap_of_etale (f : X ⟶ Spec (.of k)) [Smooth f] {U : Scheme.{u}} (ψ : U ⟶ X)
    [Etale ψ] (I : X.IdealSheafData) (m : ℕ) :
    MC (ψ ≫ f) (I.comap ψ) m = (MC f I m).comap ψ :=
  derivativeIter_comap_of_smooth f ψ (m - 1) I

/-- The trivial instance: `H` is étale equivalent to itself through `U = X` and `ψ = ψ' = 𝟙 X`. -/
def EtaleEquiv.refl (f : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (m : ℕ) (E : DivisorFamily X)
    (H : X.IdealSheafData) : EtaleEquiv f I m E H H where
  U := X
  ψ := 𝟙 X
  ψ' := 𝟙 X
  etale_ψ := inferInstance
  etale_ψ' := inferInstance
  covers := fun x _ => ⟨x, rfl⟩
  covers' := fun x _ => ⟨x, rfl⟩
  comp_eq := rfl
  h1 := rfl
  h2 := rfl
  h3 := fun _ => rfl
  h4 := rfl

end AlgebraicGeometry.Scheme.IdealSheafData
