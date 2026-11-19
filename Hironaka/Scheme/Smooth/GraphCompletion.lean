/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.CohenIso
public import Hironaka.Scheme.Smooth.GraphFormal
public import Hironaka.Scheme.IdealSheaf.Defs
import Hironaka.Algebra.Local.CompletionEtale
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.Smooth.Origin

/-!
# Completions of an étale neighbourhood pair

Kollár: for an étale neighbourhood pair `ψ, ψ'`, "`ψ` is invertible after completion", and
`φ := ψ̂' ∘ ψ̂⁻¹ : X̂ → X̂` is the automorphism sought (the remark after [Kol07, Definition 91]);
for the graph of two
coordinate systems, `φ_p^*(x_1', x_2, …) = (x_1, x_2, …)` and `φ^* Î = Î` ([Kol07, 95], the proof
of Theorem 92). Włodarczyk: an étale `φ` induces `Ô_{x',X'} ≅ Ô_{x,X}` (the proof of [Wlo05,
Lemma 2.6.5]).

* `bijective_completionMap_stalkMap`: an étale `ψ : W ⟶ Y` with `κ(q) = κ(ψ(q))` induces a
  bijection `Ô_{Y,ψ(q)} → Ô_{W,q}`: the stalk map is flat (`Flat.stalkMap`), carries `𝔪_{ψ(q)}`
  onto `𝔪_q` (`map_maximalIdeal_stalkMap_of_etale`, unramifiedness) and is bijective on residue
  fields, so the ring form `bijective_completionMap_of_flat_of_map_maximalIdeal`
  (`Hironaka/Algebra/Local/CompletionEtale.lean`) applies.
* `bijective_completionMap_stalkHom`, `…stalkHom'`, `formalAutomorphism_germ`,
  `formalAutomorphism_cohenEquivOfResidue_X`: for an étale neighbourhood pair `Q` both `ψ̂^*` and
  `ψ̂'^*` are bijective (the previous item composed with the transport along `ψ(q) = p`), and for
  the pair `P` of two coordinate systems the formal automorphism `φ = (ψ̂'^*)⁻¹ ∘ ψ̂^*` sends `û_i`
  to `v̂_i`: `ψ̂'^*(φ(û_i)) = ψ̂^*(û_i)` is the germ at `q` of `ψ^*(u_i) = ψ'^*(v_i)`
  (`graphFst_appTop_eq`) and `ψ̂'^*` is injective. Under the Cohen isomorphism `κ(p)⟦x⟧ ≅ Ô_{X,p}`
  with `x_i ↦ û_i` (`cohenMap_X`, `Hironaka/Algebra/Local/CohenIso.lean`) this reads `φ(x_i) =
  v̂_i`.
* `map_completionMap_stalkHom`, `…stalkHom'`, `map_adicCompletion_stalkIdeal_comap_eq_iff`:
  `ψ̂^*(Î_p) = (ψ^*I)^_q`, since the stalk of the pulled-back ideal sheaf is the extension of the
  stalk (`stalkIdeal_comap`) and completion commutes with extension of ideals
  (`map_completionMap_map`); so `(ψ^*I)^_q = (ψ'^*I)^_q` iff `φ(Î_p) = Î_p`.

The germ computation `germ_stalkHom` (`ψ^*` of the germ at `p` of a section of `U` is the germ at
`q` of `ψ^*(s)`) goes through Mathlib's `Scheme.Hom.germ_stalkMap_apply` and the transport of germs
along `stalkCongr` (`stalkCongr_germ`). These are the steps from the étale pair to the formal
automorphism of [Kol07, Definition 91]
(`Hironaka/Resolution/Algebraic/MaximalContact/EtaleToFormal.lean`).
-/

public section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing TopologicalSpace

universe u

section Etale

/-- An étale morphism `ψ : W ⟶ Y` with `κ(q) = κ(ψ(q))` induces an isomorphism
`Ô_{Y,ψ(q)} ≅ Ô_{W,q}` ("`ψ` is invertible after completion", the remark after
[Kol07, Definition 91]; the proof of [Wlo05, Lemma 2.6.5]). -/
theorem bijective_completionMap_stalkMap {W Y : Scheme.{u}} (ψ : W ⟶ Y) [Etale ψ] (q : W)
    [IsIso (ψ.residueFieldMap q)] :
    Function.Bijective (completionMap (ψ.stalkMap q).hom) :=
  bijective_completionMap_of_flat_of_map_maximalIdeal _ (Flat.stalkMap ψ q)
    (map_maximalIdeal_stalkMap_of_etale ψ q)
    (ConcreteCategory.bijective_of_isIso (ψ.residueFieldMap q))

end Etale

section Transport

variable {X : Scheme.{u}}

/-- The transport of stalks along an equality of points, on germs. -/
theorem stalkCongr_germ {x y : X} (h : x = y) (V : X.Opens) (hx : x ∈ V) (s : Γ(X, V)) :
    ((X.presheaf.stalkCongr (Inseparable.of_eq h)).commRingCatIsoToRingEquiv : _ →+* _)
        (X.presheaf.germ V x hx s) = X.presheaf.germ V y (h ▸ hx) s := by
  change (X.presheaf.stalkCongr (Inseparable.of_eq h)).hom (X.presheaf.germ V x hx s) = _
  exact TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hx
    (Inseparable.of_eq h).specializes' s

/-- The transport of stalks along an equality of points carries the stalk of an ideal sheaf to the
stalk of the same ideal sheaf. -/
theorem stalkIdeal_map_stalkCongr (I : X.IdealSheafData) {x y : X} (h : x = y) :
    (I.stalkIdeal x).map
        ((X.presheaf.stalkCongr (Inseparable.of_eq h)).commRingCatIsoToRingEquiv : _ →+* _) =
      I.stalkIdeal y := by
  subst h
  have : ((X.presheaf.stalkCongr (Inseparable.of_eq (rfl : x = x))).commRingCatIsoToRingEquiv :
      X.presheaf.stalk x →+* X.presheaf.stalk x) = RingHom.id _ := by
    ext z
    change (X.presheaf.stalkCongr _).hom z = z
    rw [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
      CommRingCat.id_apply]
  rw [this, Ideal.map_id]

end Transport

section EtaleNbhdPair

variable {X : Scheme.{u}} {p : X} (Q : EtaleNbhdPair X p)

/-- `ψ̂^* : Ô_{X,p} → Ô_{W,q}` is bijective for an étale neighbourhood pair. -/
theorem bijective_completionMap_stalkHom : Function.Bijective (completionMap Q.stalkHom) := by
  unfold EtaleNbhdPair.stalkHom
  rw [completionMap_comp]
  exact (bijective_completionMap_stalkMap Q.ψ Q.q).comp (completionEquiv _).bijective

/-- `ψ̂'^* : Ô_{X,p} → Ô_{W,q}` is bijective for an étale neighbourhood pair. -/
theorem bijective_completionMap_stalkHom' : Function.Bijective (completionMap Q.stalkHom') := by
  unfold EtaleNbhdPair.stalkHom'
  rw [completionMap_comp]
  exact (bijective_completionMap_stalkMap Q.ψ' Q.q).comp (completionEquiv _).bijective

/-- `ψ^*` on germs: the germ at `p` of a section `s` over `V ∋ p` goes to the germ at `q` of
`ψ^*(s)`. -/
theorem EtaleNbhdPair.stalkHom_germ (V : X.Opens) (hpV : p ∈ V) (s : Γ(X, V)) :
    Q.stalkHom (X.presheaf.germ V p hpV s) =
      Q.W.presheaf.germ (Q.ψ ⁻¹ᵁ V) Q.q (show Q.ψ.base Q.q ∈ V by rw [Q.ψ_q]; exact hpV)
        (Q.ψ.app V s) := by
  rw [EtaleNbhdPair.stalkHom, RingHom.comp_apply, stalkCongr_germ Q.ψ_q.symm]
  exact Q.ψ.germ_stalkMap_apply V Q.q _ s

/-- `ψ'^*` on germs. -/
theorem EtaleNbhdPair.stalkHom'_germ (V : X.Opens) (hpV : p ∈ V) (s : Γ(X, V)) :
    Q.stalkHom' (X.presheaf.germ V p hpV s) =
      Q.W.presheaf.germ (Q.ψ' ⁻¹ᵁ V) Q.q (show Q.ψ'.base Q.q ∈ V by rw [Q.ψ'_q]; exact hpV)
        (Q.ψ'.app V s) := by
  rw [EtaleNbhdPair.stalkHom', RingHom.comp_apply, stalkCongr_germ Q.ψ'_q.symm]
  exact Q.ψ'.germ_stalkMap_apply V Q.q _ s

/-- `ψ̂^*(Î_p) = (ψ^*I)^_q`: the completion of the stalk of `I` is carried to the completion of
the stalk of the pulled-back ideal sheaf. -/
theorem map_completionMap_stalkHom (I : X.IdealSheafData) :
    ((I.stalkIdeal p).map (algebraMap _ (AdicCompletion (maximalIdeal (X.presheaf.stalk p))
        (X.presheaf.stalk p)))).map (completionMap Q.stalkHom) =
      ((I.comap Q.ψ).stalkIdeal Q.q).map (algebraMap _
        (AdicCompletion (maximalIdeal (Q.W.presheaf.stalk Q.q)) (Q.W.presheaf.stalk Q.q))) := by
  rw [map_completionMap_map, Scheme.IdealSheafData.stalkIdeal_comap, EtaleNbhdPair.stalkHom,
    ← Ideal.map_map, stalkIdeal_map_stalkCongr I Q.ψ_q.symm]

/-- `ψ̂'^*(Î_p) = (ψ'^*I)^_q`. -/
theorem map_completionMap_stalkHom' (I : X.IdealSheafData) :
    ((I.stalkIdeal p).map (algebraMap _ (AdicCompletion (maximalIdeal (X.presheaf.stalk p))
        (X.presheaf.stalk p)))).map (completionMap Q.stalkHom') =
      ((I.comap Q.ψ').stalkIdeal Q.q).map (algebraMap _
        (AdicCompletion (maximalIdeal (Q.W.presheaf.stalk Q.q)) (Q.W.presheaf.stalk Q.q))) := by
  rw [map_completionMap_map, Scheme.IdealSheafData.stalkIdeal_comap, EtaleNbhdPair.stalkHom',
    ← Ideal.map_map, stalkIdeal_map_stalkCongr I Q.ψ'_q.symm]

/-- `ψ^*I` and `ψ'^*I` have equal completions at `q` iff the formal automorphism preserves `Î_p`
(Kollár's "`φ^* Î = Î`", [Kol07, 95]). -/
theorem map_adicCompletion_stalkIdeal_comap_eq_iff
    (ha : Function.Bijective (completionMap Q.stalkHom))
    (ha' : Function.Bijective (completionMap Q.stalkHom')) (I : X.IdealSheafData) :
    ((I.comap Q.ψ).stalkIdeal Q.q).map (algebraMap _
          (AdicCompletion (maximalIdeal (Q.W.presheaf.stalk Q.q)) (Q.W.presheaf.stalk Q.q))) =
        ((I.comap Q.ψ').stalkIdeal Q.q).map (algebraMap _
          (AdicCompletion (maximalIdeal (Q.W.presheaf.stalk Q.q)) (Q.W.presheaf.stalk Q.q))) ↔
      ((I.stalkIdeal p).map (algebraMap _ (AdicCompletion (maximalIdeal (X.presheaf.stalk p))
          (X.presheaf.stalk p)))).map (Q.formalAutomorphism ha ha' : _ →+* _) =
        (I.stalkIdeal p).map (algebraMap _ (AdicCompletion (maximalIdeal (X.presheaf.stalk p))
          (X.presheaf.stalk p))) := by
  rw [← map_completionMap_stalkHom, ← map_completionMap_stalkHom']
  have hcomp : (completionMap Q.stalkHom').comp (Q.formalAutomorphism ha ha' : _ →+* _) =
      completionMap Q.stalkHom :=
    RingHom.ext fun x => Q.completionMap_stalkHom'_formalAutomorphism ha ha' x
  have hinv : (RingEquiv.ofBijective _ ha').symm.toRingHom.comp (completionMap Q.stalkHom') =
      RingHom.id _ :=
    RingHom.ext fun x => (RingEquiv.ofBijective _ ha').symm_apply_apply x
  have hφ : (Q.formalAutomorphism ha ha' : _ →+* _) =
      (RingEquiv.ofBijective _ ha').symm.toRingHom.comp (completionMap Q.stalkHom) := by
    ext x
    rfl
  constructor
  · intro h
    rw [hφ, ← Ideal.map_map, h, Ideal.map_map, hinv, Ideal.map_id]
  · intro h
    rw [← hcomp, ← Ideal.map_map, h]

end EtaleNbhdPair

namespace EtaleCoordinates

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} {n : ℕ}
  {U : X.affineOpens} {c c' : EtaleCoordinates f n U} {p : X} {hpU : p ∈ U.1}
  (P : c.NbhdPair c' hpU)

/-- The germ at `x ∈ V` of a section of `X` over `V`, pushed to the stalk of the open subscheme
`V` along `V.ι`, is the germ of the same section read as a global section of `V`. -/
theorem _root_.AlgebraicGeometry.Scheme.Opens.germ_comp_ι_stalkMap (V : X.Opens) (x : V) :
    X.presheaf.germ V (V.ι.base x) x.2 ≫ V.ι.stalkMap x =
      V.topIso.inv ≫ V.toScheme.presheaf.germ ⊤ x trivial := by
  rw [← Scheme.Opens.stalkIso_inv, ← Scheme.Opens.germ_stalkIso_inv V ⊤ x trivial]
  exact (congrArg (· ≫ (V.stalkIso x).inv) (TopCat.Presheaf.germ_res' X.presheaf
    (eqToIso V.ι_image_top.symm).op.inv x.1 ⟨x, trivial, rfl⟩).symm).trans (Category.assoc _ _ _)

/-- For a pair landing in `U`, `ψ^*` of the germ at `p` of a section `s` of `U` is the germ at
`q` of `ψ^*(s)` (with `s` read as a global section of `U` through `topIso`). -/
theorem NbhdPair.toEtaleNbhdPair_stalkHom_germ (s : Γ(X, U.1)) :
    P.toEtaleNbhdPair.stalkHom (X.presheaf.germ U.1 p hpU s) =
      P.W.presheaf.germ ⊤ P.q trivial (P.ψ.appTop (U.1.topIso.inv s)) := by
  have e3 := congrArg (fun g => g s) (Scheme.Opens.germ_comp_ι_stalkMap U.1 (P.ψ.base P.q))
  simp only [CommRingCat.comp_apply] at e3
  refine (congrArg ((P.ψ ≫ U.1.ι).stalkMap P.q).hom
    (stalkCongr_germ P.toEtaleNbhdPair.ψ_q.symm U.1 hpU s)).trans ?_
  refine Eq.trans ?_ (Scheme.Hom.germ_stalkMap_apply P.ψ ⊤ P.q trivial (U.1.topIso.inv s))
  refine Eq.trans ?_ (congrArg (P.ψ.stalkMap P.q).hom e3)
  exact congrArg (fun g : X.presheaf.stalk ((P.ψ ≫ U.1.ι).base P.q) ⟶ P.W.presheaf.stalk P.q =>
    g.hom (X.presheaf.germ U.1 _ _ s)) (Scheme.Hom.stalkMap_comp P.ψ U.1.ι P.q)

/-- `ψ'^*` on germs, for a pair landing in `U`. -/
theorem NbhdPair.toEtaleNbhdPair_stalkHom'_germ (s : Γ(X, U.1)) :
    P.toEtaleNbhdPair.stalkHom' (X.presheaf.germ U.1 p hpU s) =
      P.W.presheaf.germ ⊤ P.q trivial (P.ψ'.appTop (U.1.topIso.inv s)) := by
  have e3 := congrArg (fun g => g s) (Scheme.Opens.germ_comp_ι_stalkMap U.1 (P.ψ'.base P.q))
  simp only [CommRingCat.comp_apply] at e3
  refine (congrArg ((P.ψ' ≫ U.1.ι).stalkMap P.q).hom
    (stalkCongr_germ P.toEtaleNbhdPair.ψ'_q.symm U.1 hpU s)).trans ?_
  refine Eq.trans ?_ (Scheme.Hom.germ_stalkMap_apply P.ψ' ⊤ P.q trivial (U.1.topIso.inv s))
  refine Eq.trans ?_ (congrArg (P.ψ'.stalkMap P.q).hom e3)
  exact congrArg (fun g : X.presheaf.stalk ((P.ψ' ≫ U.1.ι).base P.q) ⟶ P.W.presheaf.stalk P.q =>
    g.hom (X.presheaf.germ U.1 _ _ s)) (Scheme.Hom.stalkMap_comp P.ψ' U.1.ι P.q)

/-- The formal automorphism of a pair for the coordinate data `u, v` sends the completed germ of
`u_i` to that of `v_i` (Kollár's `φ_p^*(x_1', x_2, …) = (x_1, x_2, …)`, [Kol07, 95]; Włodarczyk's
functions `w_i`, the proof of [Wlo05, Lemma 2.9.5]). -/
theorem formalAutomorphism_germ
    (ha : Function.Bijective (completionMap P.toEtaleNbhdPair.stalkHom))
    (ha' : Function.Bijective (completionMap P.toEtaleNbhdPair.stalkHom')) (i : Fin n) :
    P.toEtaleNbhdPair.formalAutomorphism ha ha'
        (algebraMap _ (AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p))
          (X.presheaf.germ U.1 p hpU (c.v i))) =
      algebraMap _ (AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p))
        (X.presheaf.germ U.1 p hpU (c'.v i)) := by
  apply ha'.1
  rw [EtaleNbhdPair.completionMap_stalkHom'_formalAutomorphism, completionMap_algebraMap,
    completionMap_algebraMap, NbhdPair.toEtaleNbhdPair_stalkHom_germ,
    NbhdPair.toEtaleNbhdPair_stalkHom'_germ, P.coord i]

/-- The Cohen form: under `κ(p)⟦x⟧ ≅ Ô_{X,p}` with `x_i ↦ û_i` (`cohenEquivOfResidue`), the formal
automorphism is `x_i ↦ v̂_i` (Kollár's "`Ô_{p,X} ≅ K⟦x_1, …, x_n⟧` by (55), so the computations of
(94) apply", [Kol07, 95]). -/
theorem formalAutomorphism_cohenEquivOfResidue_X [IsLocallyNoetherian X]
    (ha : Function.Bijective (completionMap P.toEtaleNbhdPair.stalkHom))
    (ha' : Function.Bijective (completionMap P.toEtaleNbhdPair.stalkHom'))
    [Algebra (ResidueField (X.presheaf.stalk p))
      (AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p))]
    (hι : IsCoefficientAlgebra (X.presheaf.stalk p))
    (hx : maximalIdeal (X.presheaf.stalk p) =
      Ideal.span (Set.range fun i => X.presheaf.germ U.1 p hpU (c.v i)))
    (hd : (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk p)) (i : Fin n) :
    P.toEtaleNbhdPair.formalAutomorphism ha ha'
        (cohenEquivOfResidue (X.presheaf.stalk p) (fun i => X.presheaf.germ U.1 p hpU (c.v i))
          hι hx hd (MvPowerSeries.X i)) =
      algebraMap _ (AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p))
        (X.presheaf.germ U.1 p hpU (c'.v i)) := by
  rw [cohenEquivOfResidue_apply, cohenMap', cohenMap_X]
  exact formalAutomorphism_germ P ha ha' i

end EtaleCoordinates

end AlgebraicGeometry
