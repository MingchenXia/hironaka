/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Smooth.CoordinateSystem

/-!
# The graph of two coordinate systems: the definitions

Kollár realizes the formal automorphism `x_1 ↦ x_1'` between two local coordinate systems
`x_1, x_2, …, x_n` and `x_1', x_2, …, x_n` at a point `p` of the smooth `X` on an étale
neighbourhood: the closed subscheme `U_1(p) = (x_{11} − x_{21}' = x_{12} − x_{22} = ⋯ = 0) ⊆ X × X`
has two étale coordinate projections `ψ_p, ψ_p' : U_2(p) ⇉ X` after shrinking, `(p, p) ∈ U_2(p)`,
and its completion at `(p, p)` is the graph of the formal automorphism ([Kol07, 95], the proof of
Theorem 92). Włodarczyk takes the fibre product `U ×_{𝔸ⁿ} U` of the two étale coordinate
morphisms `φ_1, φ_2 : U → 𝔸ⁿ` and an irreducible component of it through the point above `x`
([Wlo05, Lemma 2.9.5], step (0) of the proof). This file defines the objects:

* `EtaleCoordinates.graph c c' := pullback φ_u φ_v`, with projections `graphFst = ψ_u`,
  `graphSnd = ψ_v` and `graphToProd : W ⟶ U ×_k U` (`pullback.mapDesc` along `𝔸ⁿ_k ⟶ Spec k`).
* `EtaleNbhdPair X p` (the pair `ψ, ψ' : U ⇉ X` of [Kol07, Definition 91], without surjectivity): a
  scheme `W` with a point `q` and two étale maps `ψ, ψ' : W ⟶ X` sending `q` to `p` with trivial
  residue field extension; `EtaleCoordinates.NbhdPair c c' hpU`: the same landing in `U`, carrying
  the coordinate identity `ψ^*(u_i) = ψ'^*(v_i)`, with `NbhdPair.toEtaleNbhdPair`.

The properties of the graph are proved in `GraphBasic.lean`, `GraphPoint.lean`, `GraphFormal.lean`,
`GraphCompletion.lean`, `GraphComponent.lean` and `GraphDiagonalPair.lean`; the pairs enter the
étale equivalence of hypersurfaces of maximal contact
(`Hironaka/Resolution/Algebraic/MaximalContact/`).
-/

@[expose] public section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

/-- The structure morphism `𝔸ⁿ_k = Spec k[t_0, …, t_{n-1}] ⟶ Spec k`. -/
noncomputable abbrev affineSpaceToSpec (k : Type u) [Field k] (n : ℕ) :
    Spec (.of (MvPolynomial (Fin n) k)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin n) k)))

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} {n : ℕ}
  {U : X.affineOpens}

namespace EtaleCoordinates

variable (c c' : EtaleCoordinates f n U)

/-- The graph scheme `W = U ×_{𝔸ⁿ} U` of the two coordinate systems, the fibre product of `φ_u`
and `φ_v` (Kollár's `U_1(p)`, [Kol07, 95]; Włodarczyk's `U ×_{𝔸ⁿ} U`, the proof of [Wlo05,
Lemma 2.9.5]). -/
noncomputable abbrev graph : Scheme.{u} :=
  pullback (toAffineSpace f U.1 c.v) (toAffineSpace f U.1 c'.v)

/-- The first projection `ψ_u : W ⟶ U`. -/
noncomputable abbrev graphFst : c.graph c' ⟶ (U.1 : Scheme.{u}) :=
  pullback.fst (toAffineSpace f U.1 c.v) (toAffineSpace f U.1 c'.v)

/-- The second projection `ψ_v : W ⟶ U`. -/
noncomputable abbrev graphSnd : c.graph c' ⟶ (U.1 : Scheme.{u}) :=
  pullback.snd (toAffineSpace f U.1 c.v) (toAffineSpace f U.1 c'.v)

/-- The map `W ⟶ U ×_k U` (Kollár's `U_1(p) ⊆ X × X`), `(ψ_u, ψ_v)`. -/
noncomputable abbrev graphToProd : c.graph c' ⟶
    pullback (toAffineSpace f U.1 c.v ≫ affineSpaceToSpec k n)
      (toAffineSpace f U.1 c'.v ≫ affineSpaceToSpec k n) :=
  pullback.mapDesc (toAffineSpace f U.1 c.v) (toAffineSpace f U.1 c'.v) (affineSpaceToSpec k n)

end EtaleCoordinates

/-- An **étale neighbourhood pair** of `p ∈ X`: a scheme `W` with a point `q` and two étale
morphisms `ψ, ψ' : W ⟶ X` sending `q` to `p`, with trivial residue field extension `κ(q) = κ(p)`
along both (the "étale surjections `ψ, ψ' : U ⇉ X`" of [Kol07, Definition 91] without the
surjectivity, which `EtaleCover.lean` handles; the "étale neighbourhoods `φ_u, φ_v : X̄ → X` of
`x = φ_u(x̄) = φ_v(x̄)`" of [Wlo05, Lemma 2.9.5]). -/
structure EtaleNbhdPair (X : Scheme.{u}) (p : X) where
  /-- The étale neighbourhood. -/
  W : Scheme.{u}
  /-- The point over `p`. -/
  q : W
  /-- The first étale map `ψ`. -/
  ψ : W ⟶ X
  /-- The second étale map `ψ'`. -/
  ψ' : W ⟶ X
  etale_ψ : Etale ψ
  etale_ψ' : Etale ψ'
  ψ_q : ψ.base q = p
  ψ'_q : ψ'.base q = p
  /-- `κ(q) = κ(p)` along `ψ`. -/
  isIso_residueFieldMap_ψ : IsIso (ψ.residueFieldMap q)
  /-- `κ(q) = κ(p)` along `ψ'`. -/
  isIso_residueFieldMap_ψ' : IsIso (ψ'.residueFieldMap q)

attribute [instance] EtaleNbhdPair.etale_ψ EtaleNbhdPair.etale_ψ'
  EtaleNbhdPair.isIso_residueFieldMap_ψ EtaleNbhdPair.isIso_residueFieldMap_ψ'

namespace EtaleCoordinates

variable (c c' : EtaleCoordinates f n U)

/-- For the coordinate data `u, v` on `U ∋ p`: an étale neighbourhood pair landing in `U`,
`ψ, ψ' : W ⟶ U` étale with `ψ(q) = ψ'(q) = p`, `κ(q) = κ(p)`, and the coordinate identity
`ψ^*(u_i) = ψ'^*(v_i)` for every `i` (Włodarczyk's `w_1 = φ_u^*(u) = φ_v^*(v)`,
`w_i = φ_u^*(u_i) = φ_v^*(u_i)`, the proof of [Wlo05, Lemma 2.9.5]). -/
structure NbhdPair {p : X} (hpU : p ∈ U.1) where
  /-- The étale neighbourhood. -/
  W : Scheme.{u}
  /-- The point over `p`. -/
  q : W
  /-- The first étale map `ψ : W ⟶ U`. -/
  ψ : W ⟶ (U.1 : Scheme.{u})
  /-- The second étale map `ψ' : W ⟶ U`. -/
  ψ' : W ⟶ (U.1 : Scheme.{u})
  etale_ψ : Etale ψ
  etale_ψ' : Etale ψ'
  ψ_q : ψ.base q = ⟨p, hpU⟩
  ψ'_q : ψ'.base q = ⟨p, hpU⟩
  isIso_residueFieldMap_ψ : IsIso (ψ.residueFieldMap q)
  isIso_residueFieldMap_ψ' : IsIso (ψ'.residueFieldMap q)
  /-- The coordinate identity `ψ^*(u_i) = ψ'^*(v_i)`. -/
  coord : ∀ i, ψ.appTop (U.1.topIso.inv (c.v i)) = ψ'.appTop (U.1.topIso.inv (c'.v i))

attribute [instance] NbhdPair.etale_ψ NbhdPair.etale_ψ' NbhdPair.isIso_residueFieldMap_ψ
  NbhdPair.isIso_residueFieldMap_ψ'

/-- The étale neighbourhood pair of `p ∈ X` underlying a pair for coordinate data on `U ∋ p`:
compose with the open immersion `U ⟶ X`. -/
noncomputable def NbhdPair.toEtaleNbhdPair {p : X} {hpU : p ∈ U.1} (P : c.NbhdPair c' hpU) :
    EtaleNbhdPair X p where
  W := P.W
  q := P.q
  ψ := P.ψ ≫ U.1.ι
  ψ' := P.ψ' ≫ U.1.ι
  etale_ψ := inferInstance
  etale_ψ' := inferInstance
  ψ_q := by rw [Scheme.Hom.comp_apply, P.ψ_q]; rfl
  ψ'_q := by rw [Scheme.Hom.comp_apply, P.ψ'_q]; rfl
  isIso_residueFieldMap_ψ := by
    rw [Scheme.residueFieldMap_comp]
    have h1 : IsIso (U.1.ι.residueFieldMap (P.ψ.base P.q)) := inferInstance
    have h2 : IsIso (P.ψ.residueFieldMap P.q) := P.isIso_residueFieldMap_ψ
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2
  isIso_residueFieldMap_ψ' := by
    rw [Scheme.residueFieldMap_comp]
    have h1 : IsIso (U.1.ι.residueFieldMap (P.ψ'.base P.q)) := inferInstance
    have h2 : IsIso (P.ψ'.residueFieldMap P.q) := P.isIso_residueFieldMap_ψ'
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2

end EtaleCoordinates

end AlgebraicGeometry
