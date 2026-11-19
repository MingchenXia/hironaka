/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Smooth.GraphBasic
public import Hironaka.Scheme.Smooth.GraphFormal
import Hironaka.Scheme.Smooth.GraphCompletion

/-!
# The étale neighbourhood pair of the graph at the diagonal point `(p, p)`

Kollár shrinks the graph `U₁(p)` to an open `U₂(p) ∋ (p, p)` on which "both coordinate
projections `ψₚ, ψₚ' : U₂(p) ⇉ X` are étale" ([Kol07, 95], the proof of Theorem 92). The graph
`U₁(p) = U ×_{𝔸ⁿ} U` of two étale coordinate systems `c, c'` on an affine `U ∋ p` (`graph`), its
two projections (`graphFst`, `graphSnd`, étale as base changes of the étale coordinate maps, so no
shrinking is needed), and the canonical point `(p, p) : Spec κ(p) ⟶ U₁(p)` (`graphPoint`) are
defined in `Graph.lean`, `GraphBasic.lean` and `GraphFormal.lean`. This module packages the pair AT
THE DIAGONAL POINT as a `NbhdPair` and proves the three properties the comparison of two
hypersurfaces of maximal contact needs of it
(`Hironaka/Resolution/Algebraic/MaximalContact/Theorem92.lean`):

* (i) both projections are morphisms of `k`-schemes (`graphFst_comp_structure`: `U₁(p) ⊆ X ×_k X`);
* (ii) `ψ^*(s) − ψ'^*(s) ∈ 𝔪_q` for every `s ∈ 𝒪_{X,p}`: the two projections induce the SAME
  identification of `κ(p)` with `κ(q)`, because `(p, p)` lies on the diagonal: the composites
  `Spec κ(p) → U₁(p) ⇉ X` are both the canonical `Spec κ(p) → X`, so the defects `ψ^*(s) − ψ'^*(s)`
  die under the local homomorphism `𝒪_{W,q} → 𝒪_{Spec κ(p)}` and hence lie in `𝔪_q` (this clause
  is what pins the pair's formal automorphism when `κ(p) ≠ k`; it is not in the sources);
* (iii) the graph equations `ψ^*(cᵢ) = ψ'^*(cᵢ')` on stalks (the coordinate identity `coord`).

The existence statement `exists_etaleNbhdPair_of_etaleCoordinates` packages the three properties
on an `EtaleNbhdPair`.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

/-- Two equal morphisms have equal stalk maps, up to the transport of the source stalk along the
two (propositionally equal) image points. -/
theorem stalkMap_stalkCongr_eq_of_eq {T X : Scheme.{u}} {g g' : T ⟶ X} (hg : g = g') (t : T)
    {p : X} (h1 : g.base t = p) (h2 : g'.base t = p) (s : X.presheaf.stalk p) :
    (g.stalkMap t).hom ((X.presheaf.stalkCongr (Inseparable.of_eq h1.symm)).hom s) =
      (g'.stalkMap t).hom ((X.presheaf.stalkCongr (Inseparable.of_eq h2.symm)).hom s) := by
  subst hg
  rfl

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} {n : ℕ}
  {U : X.affineOpens}

namespace EtaleCoordinates

variable (c c' : EtaleCoordinates f n U)

section DiagonalPair

variable {p : X} (hpU : p ∈ U.1)
  (hc : ∀ i, X.presheaf.germ U.1 p hpU (c.v i) ∈ maximalIdeal (X.presheaf.stalk p))
  (hc' : ∀ i, X.presheaf.germ U.1 p hpU (c'.v i) ∈ maximalIdeal (X.presheaf.stalk p))

/-- The point `(p, p)` of the graph `U₁(p) = U ×_{𝔸ⁿ} U` (the image of the morphism
`graphPoint : Spec κ(p) ⟶ W`). -/
noncomputable def graphDiagonalPoint : c.graph c' :=
  (c.graphPoint c' hpU hc hc').base default

theorem graphPoint_base_default :
    (c.graphPoint c' hpU hc hc').base default = c.graphDiagonalPoint c' hpU hc hc' := rfl

theorem graphFst_base_graphDiagonalPoint :
    (c.graphFst c').base (c.graphDiagonalPoint c' hpU hc hc') = ⟨p, hpU⟩ := by
  rw [graphDiagonalPoint, ← Scheme.Hom.comp_apply, graphPoint_graphFst,
    specResidueFieldToOpens_apply]

theorem graphSnd_base_graphDiagonalPoint :
    (c.graphSnd c').base (c.graphDiagonalPoint c' hpU hc hc') = ⟨p, hpU⟩ := by
  rw [graphDiagonalPoint, ← Scheme.Hom.comp_apply, graphPoint_graphSnd,
    specResidueFieldToOpens_apply]

theorem isIso_residueFieldMap_graphFst :
    IsIso ((c.graphFst c').residueFieldMap (c.graphDiagonalPoint c' hpU hc hc')) := by
  have : SurjectiveOnStalks (c.graphPoint c' hpU hc hc' ≫ c.graphFst c') := by
    rw [graphPoint_graphFst]; infer_instance
  exact isIso_residueFieldMap_of_comp (c.graphPoint c' hpU hc hc') (c.graphFst c') default

theorem isIso_residueFieldMap_graphSnd :
    IsIso ((c.graphSnd c').residueFieldMap (c.graphDiagonalPoint c' hpU hc hc')) := by
  have : SurjectiveOnStalks (c.graphPoint c' hpU hc hc' ≫ c.graphSnd c') := by
    rw [graphPoint_graphSnd]; infer_instance
  exact isIso_residueFieldMap_of_comp (c.graphPoint c' hpU hc hc') (c.graphSnd c') default

/-- The étale neighbourhood pair of `p` for the coordinate data `c, c'` given by the whole graph
`U₁(p) = U ×_{𝔸ⁿ} U` at the diagonal point `(p, p)` with its two étale projections (Kollár's
`U₂(p)`, [Kol07, 95], without shrinking; the proof of [Wlo05, Lemma 2.9.5]). -/
noncomputable def graphNbhdPair : c.NbhdPair c' hpU where
  W := c.graph c'
  q := c.graphDiagonalPoint c' hpU hc hc'
  ψ := c.graphFst c'
  ψ' := c.graphSnd c'
  etale_ψ := inferInstance
  etale_ψ' := inferInstance
  ψ_q := c.graphFst_base_graphDiagonalPoint c' hpU hc hc'
  ψ'_q := c.graphSnd_base_graphDiagonalPoint c' hpU hc hc'
  isIso_residueFieldMap_ψ := c.isIso_residueFieldMap_graphFst c' hpU hc hc'
  isIso_residueFieldMap_ψ' := c.isIso_residueFieldMap_graphSnd c' hpU hc hc'
  coord := c.graphFst_appTop_eq c'

/-- The étale neighbourhood pair of `p ∈ X` of the graph at its diagonal point: `graphNbhdPair`
composed with `U ⟶ X` (`NbhdPair.toEtaleNbhdPair`). -/
noncomputable abbrev graphEtaleNbhdPair : EtaleNbhdPair X p :=
  (c.graphNbhdPair c' hpU hc hc').toEtaleNbhdPair

/-- (i) Both projections of the graph are morphisms of `k`-schemes: `U₁(p) ⊆ X ×_k X` ([Kol07, 95];
`φ_u ψ_u = φ_v ψ_v` composed with the structure map of `𝔸ⁿ_k`). -/
theorem graphEtaleNbhdPair_comp_eq :
    (c.graphEtaleNbhdPair c' hpU hc hc').ψ ≫ f = (c.graphEtaleNbhdPair c' hpU hc hc').ψ' ≫ f := by
  change (c.graphFst c' ≫ U.1.ι) ≫ f = (c.graphSnd c' ≫ U.1.ι) ≫ f
  rw [Category.assoc, Category.assoc]
  exact c.graphFst_comp_structure c'

/-- The two composites `Spec κ(p) → U₁(p) ⇉ X` through the diagonal point are the canonical
`Spec κ(p) → X`, hence equal (Kollár's point `(p, p)`, [Kol07, 95]). -/
theorem graphPoint_comp_eq :
    c.graphPoint c' hpU hc hc' ≫ (c.graphEtaleNbhdPair c' hpU hc hc').ψ =
      c.graphPoint c' hpU hc hc' ≫ (c.graphEtaleNbhdPair c' hpU hc hc').ψ' := by
  change c.graphPoint c' hpU hc hc' ≫ c.graphFst c' ≫ U.1.ι =
    c.graphPoint c' hpU hc hc' ≫ c.graphSnd c' ≫ U.1.ι
  rw [← Category.assoc, graphPoint_graphFst, ← Category.assoc, graphPoint_graphSnd]

/-- The stalk map of the diagonal point `(p, p) : Spec κ(p) → W`, typed at the pair's stalk
`𝒪_{W,q}`. -/
noncomputable abbrev diagonalStalkMap :
    (c.graphEtaleNbhdPair c' hpU hc hc').W.presheaf.stalk (c.graphEtaleNbhdPair c' hpU hc hc').q ⟶
      (Spec (X.residueField p)).presheaf.stalk default :=
  (c.graphPoint c' hpU hc hc').stalkMap default

/-- `ψ^*` on the stalk, composed with the stalk map of the diagonal point `(p, p) : Spec κ(p) → W`,
is the stalk map of the composite `Spec κ(p) → W → X` (transported from `p`). -/
theorem diagonalStalkMap_stalkHom (s : X.presheaf.stalk p) :
    (c.diagonalStalkMap c' hpU hc hc').hom ((c.graphEtaleNbhdPair c' hpU hc hc').stalkHom s) =
      ((c.graphPoint c' hpU hc hc' ≫ (c.graphEtaleNbhdPair c' hpU hc hc').ψ).stalkMap
          default).hom
        ((X.presheaf.stalkCongr
          (Inseparable.of_eq (c.graphEtaleNbhdPair c' hpU hc hc').ψ_q.symm)).hom s) := by
  have h := Scheme.Hom.stalkMap_comp (c.graphPoint c' hpU hc hc')
    (c.graphEtaleNbhdPair c' hpU hc hc').ψ default
  simp only [h]
  rfl

/-- `ψ'^*` on the stalk, composed with the stalk map of the diagonal point. -/
theorem diagonalStalkMap_stalkHom' (s : X.presheaf.stalk p) :
    (c.diagonalStalkMap c' hpU hc hc').hom ((c.graphEtaleNbhdPair c' hpU hc hc').stalkHom' s) =
      ((c.graphPoint c' hpU hc hc' ≫ (c.graphEtaleNbhdPair c' hpU hc hc').ψ').stalkMap
          default).hom
        ((X.presheaf.stalkCongr
          (Inseparable.of_eq (c.graphEtaleNbhdPair c' hpU hc hc').ψ'_q.symm)).hom s) := by
  have h := Scheme.Hom.stalkMap_comp (c.graphPoint c' hpU hc hc')
    (c.graphEtaleNbhdPair c' hpU hc hc').ψ' default
  simp only [h]
  rfl

/-- (ii) At the diagonal point the two projections agree on functions to first order:
`ψ^*(s) − ψ'^*(s) ∈ 𝔪_q` for every `s ∈ 𝒪_{X,p}` — both induce the same identification
`κ(p) = κ(q)`. Proof: the defect is killed by the local homomorphism `𝒪_{W,q} → 𝒪_{Spec κ(p)}`
induced by `(p, p) : Spec κ(p) → W`, because the two composites `Spec κ(p) → W ⇉ X` coincide
(`graphPoint_comp_eq`), and a local homomorphism detects the maximal ideal. -/
theorem graphEtaleNbhdPair_stalkHom_sub_mem (s : X.presheaf.stalk p) :
    (c.graphEtaleNbhdPair c' hpU hc hc').stalkHom s -
        (c.graphEtaleNbhdPair c' hpU hc hc').stalkHom' s ∈
      maximalIdeal ((c.graphEtaleNbhdPair c' hpU hc hc').W.presheaf.stalk
        (c.graphEtaleNbhdPair c' hpU hc hc').q) := by
  have hx : (c.diagonalStalkMap c' hpU hc hc').hom
        ((c.graphEtaleNbhdPair c' hpU hc hc').stalkHom s) =
      (c.diagonalStalkMap c' hpU hc hc').hom
        ((c.graphEtaleNbhdPair c' hpU hc hc').stalkHom' s) := by
    rw [c.diagonalStalkMap_stalkHom c' hpU hc hc', c.diagonalStalkMap_stalkHom' c' hpU hc hc']
    exact stalkMap_stalkCongr_eq_of_eq (c.graphPoint_comp_eq c' hpU hc hc') default
      (c.graphEtaleNbhdPair c' hpU hc hc').ψ_q (c.graphEtaleNbhdPair c' hpU hc hc').ψ'_q s
  have hloc : IsLocalHom (c.diagonalStalkMap c' hpU hc hc').hom :=
    (inferInstance : IsLocalHom ((c.graphPoint c' hpU hc hc').stalkMap default).hom)
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have hu' := (isUnit_map_iff (c.diagonalStalkMap c' hpU hc hc').hom _).mpr hu
  rw [map_sub, hx, sub_self] at hu'
  exact not_isUnit_zero hu'

/-- (iii) The graph equations on stalks: `ψ^*(cᵢ) = ψ'^*(cᵢ')` (the coordinate identity `coord`,
read at the germs of the coordinates). -/
theorem graphEtaleNbhdPair_stalkHom_germ (i : Fin n) :
    (c.graphEtaleNbhdPair c' hpU hc hc').stalkHom (X.presheaf.germ U.1 p hpU (c.v i)) =
      (c.graphEtaleNbhdPair c' hpU hc hc').stalkHom' (X.presheaf.germ U.1 p hpU (c'.v i)) := by
  rw [graphEtaleNbhdPair, NbhdPair.toEtaleNbhdPair_stalkHom_germ,
    NbhdPair.toEtaleNbhdPair_stalkHom'_germ, (c.graphNbhdPair c' hpU hc hc').coord i]

include hc hc' in
/-- For two étale coordinate systems `c, c'` on an affine `U ∋ p` whose coordinates all vanish at
`p`, the graph `U₁(p)` at its diagonal point is an étale neighbourhood pair `Q` of `p` with (i)
`ψ ≫ f = ψ' ≫ f`, (ii) `ψ^*(s) − ψ'^*(s) ∈ 𝔪_q` for every `s ∈ 𝒪_{X,p}`, and (iii)
`ψ^*(cᵢ) = ψ'^*(cᵢ')` for every `i` (Kollár's "`(p, p) ∈ U₂(p) ⊂ U₁(p)` such that both coordinate
projections `ψₚ, ψₚ' : U₂(p) ⇉ X` are étale", [Kol07, 95]; the proof of [Wlo05, Lemma 2.9.5];
clause (ii) is not in the sources). -/
theorem exists_etaleNbhdPair_of_etaleCoordinates :
    ∃ Q : EtaleNbhdPair X p, Q.ψ ≫ f = Q.ψ' ≫ f ∧
      (∀ s, Q.stalkHom s - Q.stalkHom' s ∈ maximalIdeal (Q.W.presheaf.stalk Q.q)) ∧
      ∀ i, Q.stalkHom (X.presheaf.germ U.1 p hpU (c.v i)) =
        Q.stalkHom' (X.presheaf.germ U.1 p hpU (c'.v i)) :=
  ⟨c.graphEtaleNbhdPair c' hpU hc hc', c.graphEtaleNbhdPair_comp_eq c' hpU hc hc',
    c.graphEtaleNbhdPair_stalkHom_sub_mem c' hpU hc hc',
    c.graphEtaleNbhdPair_stalkHom_germ c' hpU hc hc'⟩

end DiagonalPair

end EtaleCoordinates

end AlgebraicGeometry
