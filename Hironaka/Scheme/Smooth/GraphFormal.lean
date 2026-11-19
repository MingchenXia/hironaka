/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.CompletionMap
public import Hironaka.Scheme.Smooth.GraphPoint
import Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Membership
import Hironaka.Scheme.Smooth.BlowUpSmoothChart
import Hironaka.Scheme.Smooth.GraphBasic

/-!
# Completions of the graph: the formal automorphism, the fixed locus, the point `(p, p)`

Kollár: "the completion of `U_1(p)` at `(p, p)` is the graph of `φ_p`" ([Kol07, 95], the proof of
Theorem 92): the two coordinate projections `ψ_p, ψ_p' : U_2(p) ⇉ X` induce isomorphisms
`Ô_{X,p} ≅ Ô_{U_2(p),(p,p)}`, and `φ := ψ̂' ∘ ψ̂⁻¹` is the formal automorphism `x_1 ↦ x_1'` of
[Kol07, Definition 91]. Włodarczyk adds that `φ_u, φ_v` coincide on the fixed locus of `v − u`
([Wlo05, Lemma 2.9.5], step (1) of the proof). The definitions:

* `EtaleNbhdPair.stalkHom Q`, `stalkHom' Q`: the local homomorphisms
  `ψ^*, ψ'^* : 𝒪_{X,p} →+* 𝒪_{W,q}` of an étale neighbourhood pair (`Graph.lean`), the stalk maps
  at `q` transported along `ψ(q) = p`.
* `EtaleNbhdPair.formalAutomorphism Q ha ha'`: `φ := (ψ̂'^*)⁻¹ ∘ ψ̂^*`, an automorphism of
  `Ô_{X,p}`, from the bijectivity of the two induced maps on completions (proved in
  `GraphCompletion.lean`).
* `EtaleCoordinates.fixedLocusIdeal c c'`, `fixedLocus`, `fixedLocusι`: the closed subscheme
  `Z = V(ψ_u^*(v_j − u_j) : j)` of the graph `W = U ×_{𝔸ⁿ} U`; `coincidenceLocus c c'`,
  `coincidenceLocusι`: the locus of `Z` where `ψ_u` and `ψ_v` coincide, the preimage of the
  diagonal of `φ_v` under `(ψ_u, ψ_v) : Z ⟶ U ×_{𝔸ⁿ} U`.
* `EtaleCoordinates.graphPoint c c' hpU hc hc'`: the canonical point `(p, p) : Spec κ(p) ⟶ W`
  when all coordinates vanish at `p` (the construction inside `exists_graph_point` of
  `GraphPoint.lean`, named).
-/

@[expose] public section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing TopologicalSpace

universe u

section EtaleNbhdPair

variable {X : Scheme.{u}} {p : X} (Q : EtaleNbhdPair X p)

/-- The local homomorphism `ψ^* : 𝒪_{X,p} →+* 𝒪_{W,q}` of the first map of an étale neighbourhood
pair: the stalk map `ψ.stalkMap q : 𝒪_{X,ψ(q)} ⟶ 𝒪_{W,q}` transported along `ψ(q) = p`. -/
noncomputable def EtaleNbhdPair.stalkHom : X.presheaf.stalk p →+* Q.W.presheaf.stalk Q.q :=
  (Q.ψ.stalkMap Q.q).hom.comp
    ((X.presheaf.stalkCongr (Inseparable.of_eq Q.ψ_q.symm)).commRingCatIsoToRingEquiv : _ →+* _)

/-- The local homomorphism `ψ'^* : 𝒪_{X,p} →+* 𝒪_{W,q}` of the second map. -/
noncomputable def EtaleNbhdPair.stalkHom' : X.presheaf.stalk p →+* Q.W.presheaf.stalk Q.q :=
  (Q.ψ'.stalkMap Q.q).hom.comp
    ((X.presheaf.stalkCongr (Inseparable.of_eq Q.ψ'_q.symm)).commRingCatIsoToRingEquiv : _ →+* _)

instance EtaleNbhdPair.isLocalHom_stalkHom : IsLocalHom Q.stalkHom :=
  RingHom.isLocalHom_comp _ _

instance EtaleNbhdPair.isLocalHom_stalkHom' : IsLocalHom Q.stalkHom' :=
  RingHom.isLocalHom_comp _ _

/-- The formal automorphism `φ := (ψ̂'^*)⁻¹ ∘ ψ̂^*` of `Ô_{X,p}` (the "automorphism `φ : X̂ → X̂`"
of [Kol07, Definition 91]), from the bijectivity of the two maps induced on the `𝔪`-adic
completions. For the pair of two coordinate systems it sends the completed germ of `u_i` to that
of `v_i` (the coordinate identity `ψ^*(u_i) = ψ'^*(v_i)`); Kollár's
`φ_p^*(x_1', x_2, …) = (x_1, x_2, …)` ([Kol07, 95]) is its inverse on functions. -/
noncomputable def EtaleNbhdPair.formalAutomorphism
    (ha : Function.Bijective (completionMap Q.stalkHom))
    (ha' : Function.Bijective (completionMap Q.stalkHom')) :
    AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p) ≃+*
      AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p) :=
  (RingEquiv.ofBijective _ ha).trans (RingEquiv.ofBijective _ ha').symm

theorem EtaleNbhdPair.completionMap_stalkHom'_formalAutomorphism
    (ha : Function.Bijective (completionMap Q.stalkHom))
    (ha' : Function.Bijective (completionMap Q.stalkHom'))
    (x : AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p)) :
    completionMap Q.stalkHom' (Q.formalAutomorphism ha ha' x) =
      completionMap Q.stalkHom x :=
  (RingEquiv.ofBijective _ ha').apply_symm_apply _

end EtaleNbhdPair

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} {n : ℕ}
  {U : X.affineOpens}

namespace EtaleCoordinates

section FixedLocus

variable (c c' : EtaleCoordinates f n U)

/-- The two projections of the graph are morphisms over `k`: `ψ_u ≫ (U ⟶ X ⟶ Spec k) =
ψ_v ≫ (U ⟶ X ⟶ Spec k)` (`φ_u ψ_u = φ_v ψ_v` composed with the structure map of `𝔸ⁿ_k`,
`toAffineSpace_comp_structure`). -/
theorem graphFst_comp_structure :
    c.graphFst c' ≫ U.1.ι ≫ f = c.graphSnd c' ≫ U.1.ι ≫ f := by
  conv_lhs => rw [← toAffineSpace_comp_structure f U.1 c.v]
  conv_rhs => rw [← toAffineSpace_comp_structure f U.1 c'.v]
  rw [← Category.assoc, graphFst_comp_toAffineSpace, Category.assoc]

/-- The ideal sheaf of the fixed locus `Z = V(ψ_u^*(v_j − u_j) : j) ⊆ W` of the graph
(Włodarczyk's `φ_u^{-1}(V(h))`, `h := v − u`, the proof of [Wlo05, Lemma 2.9.5]; Kollár's
`x_1 − x_1' ∈ MC(I)`, [Kol07, 95]): for `v = (x_1', x_2, …, x_n)` and `u = (x_1, x_2, …, x_n)`
only `j = 1` contributes. -/
noncomputable def fixedLocusIdeal : (c.graph c').IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (Ideal.span (Set.range fun j =>
    (c.graphFst c').appTop (U.1.topIso.inv (c'.v j)) -
      (c.graphFst c').appTop (U.1.topIso.inv (c.v j))))

/-- The fixed locus `Z ⊆ W` as a closed subscheme. -/
noncomputable abbrev fixedLocus : Scheme.{u} := (c.fixedLocusIdeal c').subscheme

/-- The closed immersion `Z ⟶ W` of the fixed locus. -/
noncomputable abbrev fixedLocusι : c.fixedLocus c' ⟶ c.graph c' :=
  (c.fixedLocusIdeal c').subschemeι

/-- On the fixed locus `Z` the two projections agree after composing with `φ_v`, i.e.
`ψ_u|_Z^*(v_j) = ψ_v|_Z^*(v_j)` for every `j`: on `Z`, `ψ_u^*(v_j) = ψ_u^*(u_j)`, and
`ψ_u^*(u_j) = ψ_v^*(v_j)` on all of `W` (the coordinate identity). -/
theorem fixedLocusι_comp_graphFst_comp_toAffineSpace :
    c.fixedLocusι c' ≫ c.graphFst c' ≫ toAffineSpace f U.1 c'.v =
      c.fixedLocusι c' ≫ c.graphSnd c' ≫ toAffineSpace f U.1 c'.v := by
  have hU : IsAffine (U.1 : Scheme.{u}) := U.2
  rw [← Category.assoc, ← Category.assoc]
  refine toAffineSpace_ext f c'.v c'.v _ _ ?_ fun j => ?_
  · rw [Category.assoc, Category.assoc, graphFst_comp_structure]
  · have hmem : (c.graphFst c').appTop (U.1.topIso.inv (c'.v j)) -
        (c.graphFst c').appTop (U.1.topIso.inv (c.v j)) ∈
        RingHom.ker ((c.fixedLocusIdeal c').subschemeι.app ⊤).hom := by
      rw [(c.fixedLocusIdeal c').ker_subschemeι_app ⟨⊤, isAffineOpen_top _⟩, fixedLocusIdeal,
        ofIdealTop_ideal_top]
      exact Ideal.subset_span ⟨j, rfl⟩
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hmem
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      CommRingCat.comp_apply, ← graphFst_appTop_eq]
    exact hmem

/-- The pair `(ψ_u|_Z, ψ_v|_Z) : Z ⟶ U ×_{𝔸ⁿ} U`, into the diagonal object of the étale coordinate
morphism `φ_v`. -/
noncomputable def fixedLocusToDiagonalObj :
    c.fixedLocus c' ⟶ pullback.diagonalObj (toAffineSpace f U.1 c'.v) :=
  pullback.lift (c.fixedLocusι c' ≫ c.graphFst c') (c.fixedLocusι c' ≫ c.graphSnd c')
    (by rw [Category.assoc, Category.assoc]
        exact c.fixedLocusι_comp_graphFst_comp_toAffineSpace c')

@[reassoc (attr := simp)]
theorem fixedLocusToDiagonalObj_fst :
    c.fixedLocusToDiagonalObj c' ≫ pullback.fst _ _ = c.fixedLocusι c' ≫ c.graphFst c' :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem fixedLocusToDiagonalObj_snd :
    c.fixedLocusToDiagonalObj c' ≫ pullback.snd _ _ = c.fixedLocusι c' ≫ c.graphSnd c' :=
  pullback.lift_snd _ _ _

/-- The coincidence locus of `ψ_u|_Z` and `ψ_v|_Z`: the preimage of the diagonal
`Δ : U ⟶ U ×_{𝔸ⁿ} U` of the étale `φ_v` under `(ψ_u|_Z, ψ_v|_Z)`, the equalizer of the two
restricted projections (Włodarczyk's locus where "`φ_u` and `φ_v` coincide", the proof of
[Wlo05, Lemma 2.9.5]). -/
noncomputable abbrev coincidenceLocus : Scheme.{u} :=
  pullback (c.fixedLocusToDiagonalObj c') (pullback.diagonal (toAffineSpace f U.1 c'.v))

/-- The immersion of the coincidence locus into the fixed locus `Z`. -/
noncomputable abbrev coincidenceLocusι : c.coincidenceLocus c' ⟶ c.fixedLocus c' :=
  pullback.fst _ _

end FixedLocus

section GraphPoint

variable (c c' : EtaleCoordinates f n U)

/-- The canonical point `(p, p) : Spec κ(p) ⟶ W` of the graph when all coordinates of both systems
vanish at `p` (Kollár's "`(p, p) ∈ U_2(p)`", [Kol07, 95]): the lift of `Spec κ(p) ⟶ U` along both
projections (the construction inside `exists_graph_point`, `GraphPoint.lean`). -/
noncomputable def graphPoint {p : X} (hpU : p ∈ U.1)
    (hc : ∀ i, X.presheaf.germ U.1 p hpU (c.v i) ∈ maximalIdeal (X.presheaf.stalk p))
    (hc' : ∀ i, X.presheaf.germ U.1 p hpU (c'.v i) ∈ maximalIdeal (X.presheaf.stalk p)) :
    Spec (X.residueField p) ⟶ c.graph c' :=
  pullback.lift (specResidueFieldToOpens (U := U) hpU) (specResidueFieldToOpens (U := U) hpU)
    (specResidueFieldToOpens_toAffineSpace_eq f hpU c.v c'.v hc hc')

@[reassoc (attr := simp)]
theorem graphPoint_graphFst {p : X} (hpU : p ∈ U.1)
    (hc : ∀ i, X.presheaf.germ U.1 p hpU (c.v i) ∈ maximalIdeal (X.presheaf.stalk p))
    (hc' : ∀ i, X.presheaf.germ U.1 p hpU (c'.v i) ∈ maximalIdeal (X.presheaf.stalk p)) :
    c.graphPoint c' hpU hc hc' ≫ c.graphFst c' = specResidueFieldToOpens (U := U) hpU :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem graphPoint_graphSnd {p : X} (hpU : p ∈ U.1)
    (hc : ∀ i, X.presheaf.germ U.1 p hpU (c.v i) ∈ maximalIdeal (X.presheaf.stalk p))
    (hc' : ∀ i, X.presheaf.germ U.1 p hpU (c'.v i) ∈ maximalIdeal (X.presheaf.stalk p)) :
    c.graphPoint c' hpU hc hc' ≫ c.graphSnd c' = specResidueFieldToOpens (U := U) hpU :=
  pullback.lift_snd _ _ _

end GraphPoint

end EtaleCoordinates

end AlgebraicGeometry
