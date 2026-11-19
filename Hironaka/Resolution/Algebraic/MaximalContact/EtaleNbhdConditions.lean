/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MaximalContact.EtaleEquiv
public import Hironaka.Resolution.Algebraic.MaximalContact.FormalEquiv
public import Hironaka.Scheme.Smooth.GraphFormal
import Hironaka.Resolution.Algebraic.MaximalContact.AgreeOnSpread
import Hironaka.Resolution.Algebraic.MaximalContact.EtaleToFormal
import Hironaka.Scheme.Smooth.GraphCompletion
import Hironaka.Scheme.Smooth.GraphComponent
import Hironaka.Scheme.Smooth.IdealSheafSpreadOut

/-!
# From (91.1)–(91.4) at the completion to (1′)–(4′) on a neighbourhood

In the proof of Theorem 92 ([Kol07, 95]) the conditions (91.1)–(91.4) hold after completion at
`(p, p)`, so "(91.1′–4′) also hold in an open neighborhood `U(p) ∋ (p, p)` by (55)". For an étale
neighbourhood pair `ψ, ψ' : W ⇉ X` of `p`
whose automorphism `φ = θ⁻¹ = (ψ̂^*)⁻¹ ∘ ψ̂'^*` of `Ô_{X,p}` satisfies the conditions (91.1)–(91.4)
of [Kol07, Definition 91], this file produces an open `V ∋ q` of `W` with (1′) `ψ⁻¹(H) = ψ'⁻¹(H')`,
(2′) `ψ^*I = ψ'^*I`, (3′) `ψ⁻¹(Eⁱ) = ψ'⁻¹(Eⁱ)` and (4′) `ψ = ψ'` on `V(MC(ψ^*I))`: the hypotheses
of `formallyEquivalentAt_of_etaleNbhdPair` for the restricted pair, and the summand conditions of
the disjoint union in `Hironaka/Resolution/Algebraic/MaximalContact/EtaleEquivSigma.lean`.

* (1′)–(3′): `φ(Ĵ') = Ĵ` transports along `ψ̂^*` (`map_completionMap_stalkHom`, `ψ̂^* ∘ φ = ψ̂'^*`)
  to `(ψ^*J)^_q = (ψ'^*J')^_q`, and Kollár's appeal to [Kol07, Definition 55]
  (`exists_comap_eq_of_map_adicCompletion_eq`) spreads the equality of completions to an open
  neighbourhood; the finitely many opens (one for `H`, one for `I`, one per component of `E`) are
  intersected.
* (4′): `h − φ(h) ∈ \widehat{MC(I)}` gives `ψ̂^*(x) − ψ̂'^*(x) ∈ (ψ^*MC(I))^_q`, and
  `exists_agreeOn_of_forall_completionMap_sub_mem` (the equalizer argument) gives an open on which
  `ψ, ψ'` agree on `V(ψ^*MC(I))`; `MC(ψ^*I) = ψ^*MC(I)` is [Kol07, Lemma 74 (4)]
  (`MC_comap_of_etale`).
* Restriction to a smaller open: equalities of pulled-back ideal sheaves restrict along `V ⊆ V₁`
  by `comap_comp`; `AgreeOn` restricts because `V(M|_V) = V(M|_{V₁}) ×_{V₁} V`
  (`AgreeOn.restrict_of_le`, the pullback square `AlgebraicGeometry.isPullback_subschemeι_comap`).
-/

public section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

open CategoryTheory CategoryTheory.Limits IsLocalRing TopologicalSpace Scheme AlgebraicGeometry

section Restrict

variable {W X : Scheme.{u}}

/-- An equality of ideal sheaves on an open `V₁` restricts to every open `V ⊆ V₁`. -/
theorem comap_ι_eq_of_le {J J' : W.IdealSheafData} {V V₁ : W.Opens} (hle : V ≤ V₁)
    (h : J.comap V₁.ι = J'.comap V₁.ι) : J.comap V.ι = J'.comap V.ι := by
  rw [← Scheme.homOfLE_ι W hle, comap_comp, comap_comp, h]

/-- Agreement of `ψ, ψ'` on `V(M)` over an open `V₁` restricts to every open `V ⊆ V₁`:
`V(M|_V)` is the pullback of `V(M|_{V₁})` along `V ⟶ V₁`
(`AlgebraicGeometry.isPullback_subschemeι_comap`). -/
theorem AgreeOn.restrict_of_le (ψ ψ' : W ⟶ X) (M : W.IdealSheafData) {V V₁ : W.Opens}
    (hle : V ≤ V₁) (h : AgreeOn (V₁.ι ≫ ψ) (V₁.ι ≫ ψ') (M.comap V₁.ι)) :
    AgreeOn (V.ι ≫ ψ) (V.ι ≫ ψ') (M.comap V.ι) := by
  have hι : V.ι = W.homOfLE hle ≫ V₁.ι := (Scheme.homOfLE_ι W hle).symm
  have hM : M.comap V.ι = (M.comap V₁.ι).comap (W.homOfLE hle) := by rw [hι, comap_comp]
  rw [hM]
  have hsq := (isPullback_subschemeι_comap (M.comap V₁.ι) (W.homOfLE hle)).w
  have hsq' : ∀ {Y : Scheme.{u}} (φ : (V₁ : Scheme.{u}) ⟶ Y),
      ((M.comap V₁.ι).comap (W.homOfLE hle)).subschemeι ≫ W.homOfLE hle ≫ φ =
        subschemeMap ((M.comap V₁.ι).comap (W.homOfLE hle)) (M.comap V₁.ι) (W.homOfLE hle)
          (le_map_comap _ _) ≫ (M.comap V₁.ι).subschemeι ≫ φ := fun φ => by
    rw [← Category.assoc, hsq, Category.assoc]
  unfold AgreeOn at h ⊢
  rw [hι]
  simp only [Category.assoc]
  rw [hsq' (V₁.ι ≫ ψ), hsq' (V₁.ι ≫ ψ'), h]

end Restrict

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The maximal-adic completion of a local ring ([Kol07, Definition 55]). -/
local notation "Ô(" R ")" => AdicCompletion (maximalIdeal R) R

/-- Kollár's "(91.1′–4′) also hold in an open neighborhood `U(p) ∋ (p, p)` by (55)" ([Kol07, 95]):
for an étale neighbourhood pair `Q` of `p` whose automorphism `φ = θ⁻¹` satisfies (91.1)–(91.4) at
`p`, there is
an open `V ∋ q` in `W` on which (1′) `ψ⁻¹(H) = ψ'⁻¹(H')`, (2′) `ψ^*I = ψ'^*I`,
(3′) `ψ⁻¹(Eⁱ) = ψ'⁻¹(Eⁱ)` for every `i`, and (4′) `ψ` and `ψ'` agree on `V(MC(ψ^*I))`. (1′)–(3′)
by spreading out equalities of completions after the transports `map_completionMap_stalkHom(')`,
intersecting the finitely many opens; (4′) by `exists_agreeOn_of_forall_completionMap_sub_mem`
with [Kol07, Lemma 74 (4)]. -/
theorem exists_opens_conditions_of_formalAutomorphism [Smooth f] (I : X.IdealSheafData) (m : ℕ)
    (E : DivisorFamily X) (H H' : X.IdealSheafData) {p : X} (Q : EtaleNbhdPair X p)
    (ha : Function.Bijective (completionMap Q.stalkHom))
    (ha' : Function.Bijective (completionMap Q.stalkHom'))
    (h1 : (H'.completionIdeal p).map (Q.formalAutomorphism ha ha').symm = H.completionIdeal p)
    (h2 : (I.completionIdeal p).map (Q.formalAutomorphism ha ha').symm = I.completionIdeal p)
    (h3 : ∀ i, ((E.component i).completionIdeal p).map (Q.formalAutomorphism ha ha').symm =
      (E.component i).completionIdeal p)
    (h4 : ∀ h, h - (Q.formalAutomorphism ha ha').symm h ∈ (MC f I m).completionIdeal p) :
    ∃ V : Q.W.Opens, Q.q ∈ V ∧ H.comap (V.ι ≫ Q.ψ) = H'.comap (V.ι ≫ Q.ψ') ∧
      I.comap (V.ι ≫ Q.ψ) = I.comap (V.ι ≫ Q.ψ') ∧
      (∀ i, (E.component i).comap (V.ι ≫ Q.ψ) = (E.component i).comap (V.ι ≫ Q.ψ')) ∧
      AgreeOn (V.ι ≫ Q.ψ) (V.ι ≫ Q.ψ') (MC ((V.ι ≫ Q.ψ) ≫ f) (I.comap (V.ι ≫ Q.ψ)) m) := by
  classical
  have hX : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hW : IsLocallyNoetherian Q.W := LocallyOfFiniteType.isLocallyNoetherian Q.ψ
  -- `ψ̂^* ∘ φ = ψ̂'^*`
  have hcomp : (completionMap Q.stalkHom).comp
      ((Q.formalAutomorphism ha ha').symm : Ô(X.presheaf.stalk p) →+* Ô(X.presheaf.stalk p)) =
      completionMap Q.stalkHom' :=
    RingHom.ext fun x => Q.completionMap_stalkHom_formalAutomorphism_symm ha ha' x
  -- (91.i) at `p` transports to the equality of completions of `ψ^*J` and `ψ'^*J'` at `q`
  have trans : ∀ (J J' : X.IdealSheafData),
      (J'.completionIdeal p).map (Q.formalAutomorphism ha ha').symm = J.completionIdeal p →
      ((J.comap Q.ψ).stalkIdeal Q.q).map (algebraMap _ Ô(Q.W.presheaf.stalk Q.q)) =
        ((J'.comap Q.ψ').stalkIdeal Q.q).map (algebraMap _ Ô(Q.W.presheaf.stalk Q.q)) := by
    intro J J' hJ
    have hJ' : (J'.completionIdeal p).map
        ((Q.formalAutomorphism ha ha').symm : Ô(X.presheaf.stalk p) →+* Ô(X.presheaf.stalk p)) =
        J.completionIdeal p := hJ
    rw [← map_completionMap_stalkHom Q J, ← map_completionMap_stalkHom' Q J',
      ← completionIdeal_eq, ← completionIdeal_eq, ← hJ', Ideal.map_map, hcomp]
  -- (1′)–(3′) on opens
  obtain ⟨V₁, hqV₁, hV₁⟩ := exists_comap_eq_of_map_adicCompletion_eq (H.comap Q.ψ)
    (H'.comap Q.ψ') Q.q (trans H H' h1)
  obtain ⟨V₂, hqV₂, hV₂⟩ := exists_comap_eq_of_map_adicCompletion_eq (I.comap Q.ψ)
    (I.comap Q.ψ') Q.q (trans I I h2)
  choose V₃ hqV₃ hV₃ using fun i => exists_comap_eq_of_map_adicCompletion_eq
    ((E.component i).comap Q.ψ) ((E.component i).comap Q.ψ') Q.q (trans _ _ (h3 i))
  -- (4′) at the completion of `q`, then on an open
  have h4' : ∀ x : Ô(X.presheaf.stalk p),
      completionMap Q.stalkHom x - completionMap Q.stalkHom' x ∈
        ((MC f I m).comap Q.ψ).completionIdeal Q.q := by
    intro x
    have hx := h4 x
    rw [← Q.completionMap_stalkHom_formalAutomorphism_symm ha ha' x, ← map_sub,
      completionIdeal_eq, ← map_completionMap_stalkHom Q]
    rw [completionIdeal_eq] at hx
    exact Ideal.mem_map_of_mem _ hx
  obtain ⟨V₄, hqV₄, hV₄⟩ :=
    exists_agreeOn_of_forall_completionMap_sub_mem f Q ((MC f I m).comap Q.ψ) h4'
  -- the intersection of the finitely many opens
  let V₃' : Q.W.Opens := ⟨⋂ i, (V₃ i : Set Q.W), isOpen_iInter_of_finite fun i => (V₃ i).isOpen⟩
  have hqV₃' : Q.q ∈ V₃' := Set.mem_iInter.mpr hqV₃
  have hV₃'le : ∀ i, V₃' ≤ V₃ i := fun i => Set.iInter_subset (fun i => (V₃ i : Set Q.W)) i
  refine ⟨V₁ ⊓ V₂ ⊓ V₃' ⊓ V₄, ⟨⟨⟨hqV₁, hqV₂⟩, hqV₃'⟩, hqV₄⟩, ?_, ?_, fun i => ?_, ?_⟩
  · rw [comap_comp, comap_comp]
    exact comap_ι_eq_of_le (inf_le_left.trans (inf_le_left.trans inf_le_left)) hV₁
  · rw [comap_comp, comap_comp]
    exact comap_ι_eq_of_le (inf_le_left.trans (inf_le_left.trans inf_le_right)) hV₂
  · rw [comap_comp, comap_comp]
    exact comap_ι_eq_of_le (inf_le_left.trans (inf_le_right.trans (hV₃'le i))) (hV₃ i)
  · rw [MC_comap_of_etale f _ I m, comap_comp]
    exact AgreeOn.restrict_of_le Q.ψ Q.ψ' _ inf_le_right hV₄

end AlgebraicGeometry.Scheme.IdealSheafData
