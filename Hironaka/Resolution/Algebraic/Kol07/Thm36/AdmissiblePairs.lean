/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineSpace
public import Hironaka.Resolution.Algebraic.Kol07.Thm36.Independence
import Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineEmbedding
import Hironaka.Resolution.Algebraic.Kol07.Thm36.Assembly
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Every affine scheme of finite type has an admissible embedding

The resolution of an affine scheme is defined through an admissible embedding `(TA, emb)`
(`Hironaka.Resolution.Algebraic.Kol07.Thm36.Independence`): a closed immersion over `k` into the
ambient of a triple with affine ambient and empty boundary, whose ideal is the kernel of the
embedding. To use that definition one needs such a pair to exist, and a triple asks for more than a
closed immersion into an affine scheme: its ideal must be nonzero in every stalk, so that its
principalization sequence is a genuine one (condition (2) of [Kol07, Notation 64]).

The construction, after "pick any embedding `X ↪ A` into a smooth affine scheme" [Kol07, Theorem
36, proof]: embed `X` into `𝔸^N_k` (`exists_closedImmersion_affineSpace_of_isAffine`, from the
finite type of the ring of global sections), then into `𝔸^{N+1}_k` through the coordinate
hyperplane `coordInclFst N 1`. The kernel of the composite `X ↪ 𝔸^{N+1}` contains the last
coordinate `x_{N+1}`, a nonzero global section of the integral scheme `𝔸^{N+1}`, so it is nonzero
in every stalk; `affineSpaceTriple k (N+1) _ _` is then the admissible ambient.

* `ker_coordInclFst_ideal_top_ne_bot`: the last coordinate lies in the kernel of the coordinate
  hyperplane, read on global sections through `ΓSpecIso` and `MvPolynomial.aeval`.
* `isNonzeroEverywhere_ker_comp_coordInclFst`: the kernel of `ι ≫ coordInclFst N 1` is nonzero in
  every stalk (`Scheme.Hom.le_ker_comp`, integrality of `𝔸^{N+1}`).
* `exists_admissibleEmbedding`: the admissible pair.
* `exists_admissibleEmbedding_of_codim`: an admissible pair whose ambient has Krull dimension
  `≥ 2` at the image of every generic point of `X` (`exists_affineEmbedding` composed with the
  coordinate hyperplane), the hypothesis of the clauses of Theorem 36 for the affine resolution.

These pairs are used to evaluate the affine resolution `BRAffine`
(`Hironaka.Resolution.Algebraic.Kol07.Thm36.BR`) and to derive its functoriality
(`Hironaka.Resolution.Algebraic.Kol07.Thm36.BRDescent`).
-/

public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Hironaka
  Scheme.IdealSheafData Hironaka.Sequence

namespace Hironaka.Resolution

variable {k : Type u} [Field k]

/-- The last coordinate of `𝔸^{N+1}` vanishes on the coordinate hyperplane `𝔸^N`: the kernel of
`coordInclFst N 1` has nonzero global sections. -/
theorem ker_coordInclFst_ideal_top_ne_bot (N : ℕ) :
    (coordInclFst (k := k) N 1).ker.ideal ⟨⊤, isAffineOpen_top _⟩ ≠ ⊥ := by
  intro hbot
  have hlast : finSumFinEquiv.symm (Fin.last N) = Sum.inr (0 : Fin 1) := by
    rw [show Fin.last N = Fin.natAdd N (0 : Fin 1) from Fin.ext (by simp),
      finSumFinEquiv_symm_apply_natAdd]
  have hv : (MvPolynomial.aeval (R := k) fun j : Fin (N + 1) =>
      Sum.elim (MvPolynomial.X : Fin N → MvPolynomial (Fin N) k) (fun _ => 0)
        (finSumFinEquiv.symm j)).toRingHom (MvPolynomial.X (Fin.last N)) = 0 := by
    change (MvPolynomial.aeval (R := k) fun j : Fin (N + 1) =>
      Sum.elim (MvPolynomial.X : Fin N → MvPolynomial (Fin N) k) (fun _ => 0)
        (finSumFinEquiv.symm j)) (MvPolynomial.X (Fin.last N)) = 0
    rw [MvPolynomial.aeval_X, hlast, Sum.elim_inr]
  -- the section `t := (ΓSpecIso).inv X_last` lies in the kernel and is nonzero
  have hnat := Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (MvPolynomial.aeval (R := k) fun j : Fin (N + 1) =>
      Sum.elim (MvPolynomial.X : Fin N → MvPolynomial (Fin N) k) (fun _ => 0)
        (finSumFinEquiv.symm j)).toRingHom)
  have hmem : (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin (N + 1)) k))).inv.hom
      (MvPolynomial.X (Fin.last N)) ∈
        (coordInclFst (k := k) N 1).ker.ideal ⟨⊤, isAffineOpen_top _⟩ := by
    rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
    have h := congrArg (fun g => g.hom (MvPolynomial.X (Fin.last N))) hnat
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    rw [hv, map_zero] at h
    exact h.symm
  rw [hbot, Ideal.mem_bot] at hmem
  have hinj := (Iso.commRingCatIsoToRingEquiv
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin (N + 1)) k))).symm).injective
  have h0 : (Iso.commRingCatIsoToRingEquiv
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin (N + 1)) k))).symm)
      (MvPolynomial.X (Fin.last N)) =
    (Iso.commRingCatIsoToRingEquiv
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin (N + 1)) k))).symm) 0 := by
    rw [map_zero]
    exact hmem
  exact MvPolynomial.X_ne_zero (Fin.last N) (hinj h0)

/-- The kernel of `ι ≫ coordInclFst N 1 : X ⟶ 𝔸^{N+1}` is nonzero at every point of `𝔸^{N+1}`:
it contains the last coordinate, and `𝔸^{N+1}` is integral, so no nonzero section vanishes in a
stalk. -/
theorem isNonzeroEverywhere_ker_comp_coordInclFst {X : Scheme.{u}} {N : ℕ}
    (ι : X ⟶ Spec (CommRingCat.of (MvPolynomial (Fin N) k))) :
    IsNonzeroEverywhere (ι ≫ coordInclFst (k := k) N 1).ker := by
  intro x
  rw [Scheme.IdealSheafData.stalkIdeal_eq_map_germ _ ⟨⊤, isAffineOpen_top _⟩ trivial]
  intro h
  have hinj := germ_injective_of_isIntegral _ (U := ⊤) x trivial
  have h0 := (Ideal.map_eq_bot_iff_of_injective hinj).mp h
  have hle := Scheme.IdealSheafData.le_def.mp
    (Scheme.Hom.le_ker_comp ι (coordInclFst (k := k) N 1)) ⟨⊤, isAffineOpen_top _⟩
  rw [h0] at hle
  exact ker_coordInclFst_ideal_top_ne_bot N (le_bot_iff.mp hle)

/-- Every affine scheme of finite type over `k` has an admissible pair ("embed `X` into an affine
space", [Kol07, Theorem 36, proof]): `X ↪ 𝔸^N ↪ 𝔸^{N+1}` through the coordinate hyperplane, whose
kernel is nonzero everywhere. -/
theorem exists_admissibleEmbedding (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [IsAffine X]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] :
    ∃ (TA : Triple k) (emb : X ⟶ TA.X.left), AdmissibleEmbedding k X TA emb := by
  obtain ⟨N, ι, hι, hover⟩ := exists_closedImmersion_affineSpace_of_isAffine (k := k) X
  have hne := isNonzeroEverywhere_ker_comp_coordInclFst (k := k) ι
  have hemb : IsClosedImmersion (ι ≫ coordInclFst (k := k) N 1) :=
    IsClosedImmersion.comp ι (coordInclFst (k := k) N 1)
  refine ⟨affineSpaceTriple k (N + 1) _ hne, ι ≫ coordInclFst (k := k) N 1, hemb, ?_,
    inferInstance, isEmpty_affineSpaceTriple_E_ι k _ _ _, rfl⟩
  constructor
  change (ι ≫ coordInclFst (k := k) N 1) ≫ affineSpaceToSpec k (N + 1) =
    X ↘ Spec (CommRingCat.of k)
  rw [Category.assoc, coordInclFst_comp_affineSpaceToSpec, hover]

/-- Every affine scheme of finite type over `k` has an admissible pair whose ambient has Krull
dimension `≥ 2` at the image of every generic point of `X` (the embedding `X ↪ A` into a smooth
affine scheme with `dim A ≥ dim X + 2` of the proofs of [Kol07, Theorem 36] and
[Kol07, Corollary 22]):
the codimension-two embedding `exists_affineEmbedding` into `𝔸^N`, followed by the coordinate
hyperplane `𝔸^N ↪ 𝔸^{N+1}` (a closed immersion: the stalk map is surjective, so the dimension of
the stalk does not decrease). -/
theorem exists_admissibleEmbedding_of_codim (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [IsAffine X]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] :
    ∃ (TA : Triple k) (emb : X ⟶ TA.X.left), AdmissibleEmbedding k X TA emb ∧
      ∀ η ∈ genericPoints X, 2 ≤ ringKrullDim (TA.X.left.presheaf.stalk (emb η)) := by
  obtain ⟨N, ι, hι, hover, hcodim⟩ := exists_affineEmbedding (k := k) X
  have hne := isNonzeroEverywhere_ker_comp_coordInclFst (k := k) ι
  have hemb : IsClosedImmersion (ι ≫ coordInclFst (k := k) N 1) :=
    IsClosedImmersion.comp ι (coordInclFst (k := k) N 1)
  refine ⟨affineSpaceTriple k (N + 1) _ hne, ι ≫ coordInclFst (k := k) N 1,
    ⟨hemb, ?_, inferInstance, isEmpty_affineSpaceTriple_E_ι k _ _ _, rfl⟩, ?_⟩
  · constructor
    change (ι ≫ coordInclFst (k := k) N 1) ≫ affineSpaceToSpec k (N + 1) =
      X ↘ Spec (CommRingCat.of k)
    rw [Category.assoc, coordInclFst_comp_affineSpaceToSpec]
    exact hover
  · intro η hη
    have h2 := hcodim η hη
    have hsurj := (coordInclFst (k := k) N 1).stalkMap_surjective (ι η)
    have hle := ringKrullDim_le_of_surjective ((coordInclFst (k := k) N 1).stalkMap (ι η)).hom hsurj
    change 2 ≤ ringKrullDim ((Spec (CommRingCat.of (MvPolynomial (Fin (N + 1)) k))).presheaf.stalk
      ((ι ≫ coordInclFst (k := k) N 1) η))
    rw [Scheme.Hom.comp_apply]
    exact le_trans h2 hle

end Hironaka.Resolution
