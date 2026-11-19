/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm36.Independence
public import Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineSpace
public import Hironaka.Scheme.BlowUpSequence.RestrictDivisors
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization.Basic
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization.ClosedEmbedding
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization.Functorial
import Hironaka.Resolution.Algebraic.Kol07.Thm36.IndexTransport
import Hironaka.Resolution.Algebraic.Kol07.Thm36.Lemma39
import Hironaka.Resolution.Algebraic.Kol07.Thm36.Stabilize
import Hironaka.Resolution.Algebraic.Stage.DimFreeTheorems
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Independence of the embedding

Kollár's resolution `BR(X)` of an affine scheme `X` is built from a closed embedding `X ↪ A` into
a smooth affine scheme. The proof of [Kol07, Theorem 36] shows that the result does not depend on
the embedding: since the principalization functor commutes with closed embeddings, it suffices to
compare embeddings into affine spaces `X ↪ 𝔸ⁿ`; the dimension `n` may be increased at will along
`𝔸ⁿ ↪ 𝔸ⁿ⁺ᵐ`; and by [Kol07, Lemma 39] two embeddings into affine spaces become conjugate under an
automorphism of a larger affine space, along which the functor is transported. This file carries
out that argument.

## The argument (`BR_affine_indep`)

For two admissible embeddings `emb₁ : X ↪ TA₁.X.left` and `emb₂ : X ↪ TA₂.X.left`:

1. **Boundary normalisation** (`BR_affine_emptiedTriple`): `BR_affine TAᵢ embᵢ` does not change
   when the boundary of `TAᵢ` (a family with empty index type) is replaced by the literal empty
   family, since the principalization sequence does not distinguish the two (`BP_emptiedTriple`).
2. **The ambient into affine space** (`exists_closedImmersion_affineSpace`): `TAᵢ.X.left` is affine
   of finite type over `k`, so its ring of functions is a finitely generated `k`-algebra and
   `TAᵢ.X.left ↪ 𝔸^{Nᵢ}` over `k`; the image of `TAᵢ.I` is nonzero everywhere because `TAᵢ.I` is, so
   `(𝔸^{Nᵢ}, TAᵢ.I.map ι, ∅)` is a triple, and `BR_affine` moves to it because `BP` commutes with
   closed embeddings [Kol07, Theorem 35 (5)] (`BR_affine_eq_affineSpaceTriple`).
3. **Stabilisation** to the common `𝔸ⁿ⁺ᵐ` along `coordInclFst n m` and `coordInclSnd n m`
   (`BR_affine_stabilizeFst`, `BR_affine_stabilizeSnd`), again by [Kol07, Theorem 35 (5)].
4. **Lemma 39** (`exists_aut_conj_embeddings`): an automorphism `φ` of `𝔸ⁿ⁺ᵐ` over `k` with
   `i₁ ≫ coordInclFst n m ≫ φ = i₂ ≫ coordInclSnd n m`.
5. **Transport along `φ`** (`BR_affine_conj`): `BP` commutes with the smooth surjection `φ`
   [Kol07, Theorem 35 (4)], and the ideal of the conjugated embedding is the inverse image of the
   ideal of the other (`Scheme.Hom.ker_comp`, `comap_map_of_isClosedImmersion`).
6. Back down the second side by steps 3, 2 and 1.

`BR_affine'_eq` then reads the embedding-free `BR_affine' k X` off any admissible pair.

## Conventions

The clauses of [Kol07, Theorem 35] used here are the library's `BP_pushforward_of_closedEmbedding`
and `BP_pullback_of_surjective` (`Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization`). The
independence theorem is the input to the affine part of Kollár's resolution functor
(`Hironaka.Resolution.Algebraic.Kol07.Thm36.BR`) and to its functoriality under smooth morphisms and
change of fields.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Hironaka Scheme IdealSheafData BlowUpSequence
  Hironaka.Sequence

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

/-! ### Boundary normalisation -/

omit [CharZero k] in
/-- The triple `T` with its boundary replaced by the empty family (the same ambient and ideal). -/
noncomputable def emptiedTriple (T : Triple k) : Triple k :=
  { T with E := DivisorFamily.empty T.X.left,
           isSnc := isSnc_empty_of_smooth (T.X.left ↘ Spec (CommRingCat.of k)) }

omit [CharZero k] in
theorem emptiedTriple_X (T : Triple k) : (emptiedTriple T).X.left = T.X.left := rfl

omit [CharZero k] in
theorem emptiedTriple_I (T : Triple k) : (emptiedTriple T).I = T.I := rfl

omit [CharZero k] in
theorem emptiedTriple_E (T : Triple k) : (emptiedTriple T).E = DivisorFamily.empty T.X.left := rfl

omit [CharZero k] in
theorem isEmpty_emptiedTriple_E_ι (T : Triple k) : IsEmpty (emptiedTriple T).E.ι :=
  inferInstanceAs (IsEmpty PEmpty)

/-- The principalization sequence does not distinguish a boundary with empty index type from the
empty family: with an empty boundary `BP` is the order reduction `BMO_1` (`BP_of_isEmpty`), which
is indifferent to empty members of the boundary (`dimFreeBMO_indifferentToEmptyMembers`). -/
theorem BP_emptiedTriple (T : Triple k) (hE : IsEmpty T.E.ι) :
    Hironaka.Sequence.BP T = Hironaka.Sequence.BP (emptiedTriple T) := by
  rw [BP_of_isEmpty T hE, BP_of_isEmpty (emptiedTriple T) (isEmpty_emptiedTriple_E_ι T)]
  have : IsEmpty (DivisorFamily.empty T.X.left).ι := inferInstanceAs (IsEmpty PEmpty)
  exact Hironaka.Stage.dimFreeBMO_indifferentToEmptyMembers Hironaka.Stage.stage0 1 ⟨T, 1⟩
    (DivisorFamily.empty T.X.left)
    (isSnc_empty_of_smooth (T.X.left ↘ Spec (CommRingCat.of k)))
    OrderEmbedding.ofIsEmpty (fun i => i.elim) (fun b _ => hE.elim b) ⟨le_rfl, rfl⟩ ⟨le_rfl, rfl⟩

/-- `BR_affine` does not distinguish a boundary with empty index type from the empty family. -/
theorem BR_affine_emptiedTriple (T : Triple k) (hE : IsEmpty T.E.ι) {X : Scheme.{u}}
    (emb : X ⟶ T.X.left) : BR_affine T emb = BR_affine (emptiedTriple T) emb := by
  unfold BR_affine
  rw [BP_emptiedTriple T hE]
  rfl

/-! ### The ambient into affine space -/

/-- For a morphism `g : X ⟶ Spec R`, `g = X.toSpecΓ ≫ Spec.map (ΓSpecIso.inv ≫ g.appTop)`
(the unit of the `Γ ⊣ Spec` adjunction). -/
theorem toSpecΓ_comp_Spec_map_appTop {X : Scheme.{u}} {R : CommRingCat.{u}} (g : X ⟶ Spec R) :
    X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ g.appTop) = g := by
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

omit [CharZero k] in
/-- An affine scheme `X` of finite type over `k` embeds as a closed subscheme into an affine space
over `k`: the ring of global sections is a finitely generated `k`-algebra (finite type read on
global sections, `HasRingHomProperty.iff_of_isAffine`), and a surjection `k[Fin N] → Γ(X, ⊤)`
gives the closed immersion `Spec.map` composed with `X ≅ Spec Γ(X, ⊤)`. Used for the ambient of
a triple here and for the affine members of the class of the resolution functor later. -/
theorem exists_closedImmersion_affineSpace_of_isAffine (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [IsAffine X]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] :
    ∃ (N : ℕ) (ι : X ⟶ Spec (CommRingCat.of (MvPolynomial (Fin N) k))),
      IsClosedImmersion ι ∧
        ι ≫ affineSpaceToSpec k N = X ↘ Spec (CommRingCat.of k) := by
  set φ : k →+* Γ(X, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (X ↘ Spec (CommRingCat.of k)).appTop).hom
    with hφ
  have hft : φ.FiniteType := by
    have h1 : RingHom.FiniteType ((X ↘ Spec (CommRingCat.of k)).appTop).hom :=
      (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)
        (f := X ↘ Spec (CommRingCat.of k))).mp inferInstance
    have h2 : Function.Surjective (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom :=
      fun x => ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom x, by simp⟩
    exact h1.comp (RingHom.FiniteType.of_surjective _ h2)
  let _ : Algebra k Γ(X, ⊤) := φ.toAlgebra
  have hfin : Algebra.FiniteType k Γ(X, ⊤) := hft
  obtain ⟨N, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hfin
  refine ⟨N, X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom f.toRingHom), ?_, ?_⟩
  · have := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom f.toRingHom) hf
    infer_instance
  · have hcomp : CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin N) k)) ≫
        CommRingCat.ofHom f.toRingHom =
        (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (X ↘ Spec (CommRingCat.of k)).appTop := by
      refine CommRingCat.hom_ext ?_
      rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom]
      exact f.comp_algebraMap
    unfold affineSpaceToSpec
    rw [Category.assoc, ← Spec.map_comp, hcomp]
    exact toSpecΓ_comp_Spec_map_appTop (X ↘ Spec (CommRingCat.of k))

omit [CharZero k] in
/-- The affine ambient `TA.X.left` of a triple embeds as a closed subscheme into an affine space
over `k`, the case `X := TA.X.left` of `exists_closedImmersion_affineSpace_of_isAffine` (the
triple's finite type supplies the instance). This is the passage from an arbitrary smooth affine
ambient to an affine space in the proof of [Kol07, Theorem 36]. -/
theorem exists_closedImmersion_affineSpace (TA : Triple k) [IsAffine TA.X.left] :
    ∃ (N : ℕ) (ι : TA.X.left ⟶ Spec (CommRingCat.of (MvPolynomial (Fin N) k))),
      IsClosedImmersion ι ∧
        ι ≫ affineSpaceToSpec k N = TA.X.left ↘ Spec (CommRingCat.of k) :=
  exists_closedImmersion_affineSpace_of_isAffine TA.X.left

/-! ### The three moves on affine-space triples -/

/-- Steps 1 and 2 of the argument: for a triple `TA` with empty boundary and a closed immersion
`ι : TA.X.left ↪ 𝔸^N` over `k`, `BR_affine` built in `TA` equals `BR_affine` built in the
affine-space triple `(𝔸^N, TA.I.map ι, ∅)`, by boundary normalisation and [Kol07, Theorem 35 (5)]
along `ι`. -/ theorem BR_affine_eq_affineSpaceTriple (TA : Triple k) (hE : IsEmpty TA.E.ι) {N : ℕ}
    (ι : TA.X.left ⟶ Spec (CommRingCat.of (MvPolynomial (Fin N) k))) [IsClosedImmersion ι]
    (hι : ι ≫ affineSpaceToSpec k N = TA.X.left ↘ Spec (CommRingCat.of k))
    {X : Scheme.{u}} (emb : X ⟶ TA.X.left) :
    BR_affine TA emb =
      BR_affine (affineSpaceTriple k N (TA.I.map ι)
        (isNonzeroEverywhere_map_of_isClosedImmersion ι TA.I TA.isNonzeroEverywhere))
        (emb ≫ ι) := by
  have hnz :=
    isNonzeroEverywhere_map_of_isClosedImmersion ι TA.I TA.isNonzeroEverywhere
  rw [BR_affine_emptiedTriple TA hE emb]
  have : IsClosedImmersion (X := (emptiedTriple TA).X.left)
    (Y := (affineSpaceTriple k N (TA.I.map ι) hnz).X.left) ι := ‹IsClosedImmersion ι›
  have hj : (affineSpaceTriple k N (TA.I.map ι) hnz).ClosedEmbedding (emptiedTriple TA) ι :=
    ⟨hι, rfl, (empty_comap ι).symm⟩
  exact (BR_affine_comp_eq_of_BP_eq_pushforward (emptiedTriple TA)
    (affineSpaceTriple k N (TA.I.map ι) hnz) ι
    (BP_pushforward_of_closedEmbedding (affineSpaceTriple k N (TA.I.map ι) hnz) (emptiedTriple TA)
      ι hj (isEmpty_affineSpaceTriple_E_ι k N (TA.I.map ι) hnz)) rfl emb).symm

/-- Step 3 of the argument, first block: stabilisation along `𝔸ⁿ ↪ 𝔸ⁿ⁺ᵐ`, `x ↦ (x, 0)`, by
[Kol07, Theorem 35 (5)] along `coordInclFst n m`. -/
theorem BR_affine_stabilizeFst {n m : ℕ}
    (I : (Spec (CommRingCat.of (MvPolynomial (Fin n) k))).IdealSheafData)
    (hI : IsNonzeroEverywhere I) {X : Scheme.{u}}
    (emb : X ⟶ Spec (CommRingCat.of (MvPolynomial (Fin n) k))) :
    BR_affine (affineSpaceTriple k n I hI) emb =
      BR_affine (affineSpaceTriple k (n + m) (I.map (coordInclFst n m))
        (isNonzeroEverywhere_map_of_isClosedImmersion (coordInclFst n m) I hI))
        (emb ≫ coordInclFst n m) := by
  have hnz := isNonzeroEverywhere_map_of_isClosedImmersion (coordInclFst n m) I hI
  exact (BR_affine_stabilize_of_BP_eq_pushforward I hI hnz
    (BP_pushforward_of_closedEmbedding (affineSpaceTriple k (n + m) (I.map (coordInclFst n m)) hnz)
      (affineSpaceTriple k n I hI) (coordInclFst n m)
      (affineSpaceTriple_closedEmbedding_coordInclFst I hI hnz)
      (isEmpty_affineSpaceTriple_E_ι k (n + m) (I.map (coordInclFst n m)) hnz)) emb).symm

/-- Step 3 of the argument, second block: stabilisation along `𝔸ᵐ ↪ 𝔸ⁿ⁺ᵐ`, `y ↦ (0, y)`, by
[Kol07, Theorem 35 (5)] along `coordInclSnd n m`. -/
theorem BR_affine_stabilizeSnd {n m : ℕ}
    (I : (Spec (CommRingCat.of (MvPolynomial (Fin m) k))).IdealSheafData)
    (hI : IsNonzeroEverywhere I) {X : Scheme.{u}}
    (emb : X ⟶ Spec (CommRingCat.of (MvPolynomial (Fin m) k))) :
    BR_affine (affineSpaceTriple k m I hI) emb =
      BR_affine (affineSpaceTriple k (n + m) (I.map (coordInclSnd n m))
        (isNonzeroEverywhere_map_of_isClosedImmersion (coordInclSnd n m) I hI))
        (emb ≫ coordInclSnd n m) := by
  have hnz := isNonzeroEverywhere_map_of_isClosedImmersion (coordInclSnd n m) I hI
  exact (BR_affine_comp_eq_of_BP_eq_pushforward (affineSpaceTriple k m I hI)
    (affineSpaceTriple k (n + m) (I.map (coordInclSnd n m)) hnz) (coordInclSnd n m)
    (BP_pushforward_of_closedEmbedding (affineSpaceTriple k (n + m) (I.map (coordInclSnd n m)) hnz)
      (affineSpaceTriple k m I hI) (coordInclSnd n m)
      (affineSpaceTriple_closedEmbedding_coordInclSnd I hI hnz)
      (isEmpty_affineSpaceTriple_E_ι k (n + m) (I.map (coordInclSnd n m)) hnz)) rfl emb).symm

/-- Step 5 of the argument: transport along an automorphism `φ` of `𝔸^N` over `k` carrying the
ideal `I₂` to `I₁`, by [Kol07, Theorem 35 (4)] for the smooth surjection `φ`
(`BP_pullback_of_surjective`) and `BR_affine_eq_of_BP_eq_pullback`. -/
theorem BR_affine_conj {N : ℕ}
    (I₁ I₂ : (Spec (CommRingCat.of (MvPolynomial (Fin N) k))).IdealSheafData)
    (h₁ : IsNonzeroEverywhere I₁) (h₂ : IsNonzeroEverywhere I₂)
    (φ : Spec (CommRingCat.of (MvPolynomial (Fin N) k)) ≅
      Spec (CommRingCat.of (MvPolynomial (Fin N) k)))
    (hφo : φ.hom ≫ affineSpaceToSpec k N = affineSpaceToSpec k N)
    (hI : I₁ = I₂.comap φ.hom) {X : Scheme.{u}}
    (emb : X ⟶ Spec (CommRingCat.of (MvPolynomial (Fin N) k))) :
    BR_affine (affineSpaceTriple k N I₁ h₁) emb =
      BR_affine (affineSpaceTriple k N I₂ h₂) (emb ≫ φ.hom) := by
  have : IsIso (X := (affineSpaceTriple k N I₁ h₁).X.left) (Y
    := (affineSpaceTriple k N I₂ h₂).X.left) φ.hom := inferInstanceAs (IsIso φ.hom)
  have : Smooth (X := (affineSpaceTriple k N I₁ h₁).X.left) (Y
    := (affineSpaceTriple k N I₂ h₂).X.left) φ.hom := inferInstanceAs (Smooth φ.hom)
  have hpb : (affineSpaceTriple k N I₁ h₁).IsPullbackOf (affineSpaceTriple k N I₂ h₂) φ.hom :=
    ⟨hφo, hI, (empty_comap φ.hom).symm⟩
  exact BR_affine_eq_of_BP_eq_pullback (affineSpaceTriple k N I₂ h₂)
    (affineSpaceTriple k N I₁ h₁) φ.hom
    (BP_pullback_of_surjective (affineSpaceTriple k N I₂ h₂) (affineSpaceTriple k N I₁ h₁) φ.hom
      (surjective_of_isIso (Z := (affineSpaceTriple k N I₁ h₁).X.left)
        (W := (affineSpaceTriple k N I₂ h₂).X.left) φ.hom) hpb) hI emb

/-! ### The theorem -/

section Assembly

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]

/-- **Independence of the embedding** [Kol07, Theorem 36, proof]: for any two admissible
embeddings `emb₁ : X ↪ TA₁.X.left` and `emb₂ : X ↪ TA₂.X.left` of a scheme `X` over `k`,
`BR_affine TA₁ emb₁ = BR_affine TA₂ emb₂`. The proof is Kollár's: both sides are moved to
affine-space triples (`BR_affine_eq_affineSpaceTriple`), stabilised to the common `𝔸ⁿ⁺ᵐ`
(`BR_affine_stabilizeFst`, `BR_affine_stabilizeSnd`), and the two coordinate embeddings are
conjugated by the automorphism of [Kol07, Lemma 39] (`exists_aut_conj_embeddings`), along which
`BR_affine` is transported (`BR_affine_conj`); the ideal of the conjugated embedding is the
inverse image of the other ideal (`Scheme.Hom.ker_comp`, `comap_map_of_isClosedImmersion`). -/
theorem BR_affine_indep (TA₁ TA₂ : Triple k) (emb₁ : X ⟶ TA₁.X.left) (emb₂ : X ⟶ TA₂.X.left)
    (h₁ : AdmissibleEmbedding k X TA₁ emb₁) (h₂ : AdmissibleEmbedding k X TA₂ emb₂) :
    BR_affine TA₁ emb₁ = BR_affine TA₂ emb₂ := by
  obtain ⟨hc₁, ho₁, ha₁, hE₁, hI₁⟩ := h₁
  obtain ⟨hc₂, ho₂, ha₂, hE₂, hI₂⟩ := h₂
  obtain ⟨n, ι₁, hcι₁, hoι₁⟩ := exists_closedImmersion_affineSpace TA₁
  obtain ⟨m, ι₂, hcι₂, hoι₂⟩ := exists_closedImmersion_affineSpace TA₂
  have hoi₁ : (emb₁ ≫ ι₁) ≫ affineSpaceToSpec k n =
      X ↘ Spec (CommRingCat.of k) := by
    rw [Category.assoc, hoι₁, ho₁.comp_over]
  have hoi₂ : (emb₂ ≫ ι₂) ≫ affineSpaceToSpec k m =
      X ↘ Spec (CommRingCat.of k) := by
    rw [Category.assoc, hoι₂, ho₂.comp_over]
  obtain ⟨φ, hφo, hφ⟩ := exists_aut_conj_embeddings (emb₁ ≫ ι₁) (emb₂ ≫ ι₂) hoi₁ hoi₂
  have hφ' : ((emb₁ ≫ ι₁) ≫ coordInclFst n m) ≫ φ.hom = (emb₂ ≫ ι₂) ≫ coordInclSnd n m := by
    rw [Category.assoc]
    exact hφ
  have hker₁ : (TA₁.I.map ι₁).map (coordInclFst n m) =
      ((emb₁ ≫ ι₁) ≫ coordInclFst n m).ker := by
    rw [← hI₁, Scheme.IdealSheafData.map_ker, Scheme.IdealSheafData.map_ker]
  have hker₂ : (TA₂.I.map ι₂).map (coordInclSnd n m) =
      ((emb₂ ≫ ι₂) ≫ coordInclSnd n m).ker := by
    rw [← hI₂, Scheme.IdealSheafData.map_ker, Scheme.IdealSheafData.map_ker]
  have hI : (TA₁.I.map ι₁).map (coordInclFst n m) =
      ((TA₂.I.map ι₂).map (coordInclSnd n m)).comap φ.hom := by
    rw [hker₁, hker₂, ← hφ', Scheme.Hom.ker_comp ((emb₁ ≫ ι₁) ≫ coordInclFst n m) φ.hom,
      comap_map_of_isClosedImmersion]
  have hnz₁ :=
    isNonzeroEverywhere_map_of_isClosedImmersion ι₁ TA₁.I TA₁.isNonzeroEverywhere
  have hnz₂ :=
    isNonzeroEverywhere_map_of_isClosedImmersion ι₂ TA₂.I TA₂.isNonzeroEverywhere
  have hnz₁' := isNonzeroEverywhere_map_of_isClosedImmersion (coordInclFst n m)
    (TA₁.I.map ι₁) hnz₁
  have hnz₂' := isNonzeroEverywhere_map_of_isClosedImmersion (coordInclSnd n m)
    (TA₂.I.map ι₂) hnz₂
  calc BR_affine TA₁ emb₁
      _ = BR_affine (affineSpaceTriple k n (TA₁.I.map ι₁) hnz₁) (emb₁ ≫ ι₁) :=
        BR_affine_eq_affineSpaceTriple TA₁ hE₁ ι₁ hoι₁ emb₁
      _ = BR_affine (affineSpaceTriple k (n + m) ((TA₁.I.map ι₁).map (coordInclFst n m)) hnz₁')
            ((emb₁ ≫ ι₁) ≫ coordInclFst n m) :=
        BR_affine_stabilizeFst (TA₁.I.map ι₁) hnz₁ (emb₁ ≫ ι₁)
      _ = BR_affine (affineSpaceTriple k (n + m) ((TA₂.I.map ι₂).map (coordInclSnd n m)) hnz₂')
            (((emb₁ ≫ ι₁) ≫ coordInclFst n m) ≫ φ.hom) :=
        BR_affine_conj ((TA₁.I.map ι₁).map (coordInclFst n m))
          ((TA₂.I.map ι₂).map (coordInclSnd n m)) hnz₁' hnz₂' φ hφo hI
          ((emb₁ ≫ ι₁) ≫ coordInclFst n m)
      _ = BR_affine (affineSpaceTriple k (n + m) ((TA₂.I.map ι₂).map (coordInclSnd n m)) hnz₂')
            ((emb₂ ≫ ι₂) ≫ coordInclSnd n m) :=
        congrArg (fun e => BR_affine
          (affineSpaceTriple k (n + m) ((TA₂.I.map ι₂).map (coordInclSnd n m)) hnz₂') e) hφ'
      _ = BR_affine (affineSpaceTriple k m (TA₂.I.map ι₂) hnz₂) (emb₂ ≫ ι₂) :=
        (BR_affine_stabilizeSnd (TA₂.I.map ι₂) hnz₂ (emb₂ ≫ ι₂)).symm
      _ = BR_affine TA₂ emb₂ := (BR_affine_eq_affineSpaceTriple TA₂ hE₂ ι₂ hoι₂ emb₂).symm

/-- The embedding-free `BR_affine' k X` equals `BR_affine TA emb` for every admissible pair
`(TA, emb)`: the pair chosen by `BR_affine'` is admissible and `BR_affine_indep` compares. -/
theorem BR_affine'_eq (TA : Triple k) (emb : X ⟶ TA.X.left) (h : AdmissibleEmbedding k X TA emb) :
    BR_affine' k X = BR_affine TA emb := by
  have hex : ∃ (TA : Triple k) (emb : X ⟶ TA.X.left), AdmissibleEmbedding k X TA emb := ⟨TA, emb, h⟩
  rw [BR_affine'_of_pos k X hex]
  exact BR_affine_indep _ _ _ _ hex.choose_spec.choose_spec h

end Assembly

end Hironaka.Resolution
