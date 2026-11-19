/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MaximalContact.EtaleEquiv
public import Hironaka.Resolution.Algebraic.MaximalContact.Invariant
public import Hironaka.Scheme.Smooth.Graph
public import Hironaka.Scheme.Snc.Basic
import Hironaka.Resolution.Algebraic.MaximalContact.EtaleEquivSigma
import Hironaka.Resolution.Algebraic.MaximalContact.EtaleNbhdConditions
import Hironaka.Resolution.Algebraic.MaximalContact.Theorem92
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.Smooth.EtaleCoverFinite
import Hironaka.Scheme.Smooth.GraphComponent
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Theorem 92 with an affine étale neighbourhood

Kollár ends the proof of Theorem 92 ([Kol07, 95]) by covering `X` with the images of finitely many
of the neighbourhoods `U(p)`: "We can take `U` to be their disjoint union." The proof in
`Hironaka/Resolution/Algebraic/MaximalContact/Theorem92.lean` (`etaleEquiv_of_isMCInvariant`) takes
`U` to be the coproduct over all closed points of the cosupport, a cover that may be infinite. The
functoriality argument of [Kol07, Theorem 103, Step 2.3] applies a blow-up sequence functor to
the pulled-back triples on `U`, and `etaleEquivSeq_of_functor` asks for `U` to carry the
hypotheses it places on the base of a functor (the Lean form of the functoriality [Kol07, 34.1]):
quasi-compact and separated over `k`, of finite type, equidimensional smooth. This file supplies
them at once by making `U` affine:

* at each closed point `p` of the cosupport, the open `V ∋ (p, p)` on which (1′)–(4′) hold is
  shrunk to an affine open (`exists_isAffineOpen_mem_and_subset`), the four conditions
  restricting along the inclusion (`conditions_restrict_of_le`: `comap_ι_eq_of_le` and
  `AgreeOn.restrict_of_le`, with `MC` commuting with étale maps, [Kol07, Lemma 74 (4)]);
* finitely many of these affine opens have images covering the closed, hence compact, cosupport
  (`exists_finset_subset_biUnion_range`; `X` is quasi-compact over `k`);
* their disjoint union is the étale equivalence (`etaleEquivOfFamily`) and is affine (Mathlib: a
  finite coproduct of affine schemes is affine).

The result, `exists_etaleEquiv_isAffine`, is Theorem 92 with an affine `U`; the instances on
`U ↘ Spec k` are derived from it in
`Hironaka/Resolution/Algebraic/MaximalContact/FunctorIndependence.lean`.
-/

public section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

open CategoryTheory CategoryTheory.Limits TopologicalSpace Scheme AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The four conditions (1′)–(4′) of [Kol07, Definition 91] on an open `V₁` of an étale
neighbourhood pair restrict to every open `V ⊆ V₁`: (1′)–(3′) because `comap` composes, (4′)
because `V(MC(ψ^*I))` restricts to its trace (`AgreeOn.restrict_of_le`) and `MC` commutes with the
étale maps `V.ι ≫ ψ` ([Kol07, Lemma 74 (4)], `MC_comap_of_etale`). -/
theorem conditions_restrict_of_le [Smooth f] (I : X.IdealSheafData) (m : ℕ) (E : DivisorFamily X)
    (H H' : X.IdealSheafData) {p : X} (Q : EtaleNbhdPair X p) {V V₁ : Q.W.Opens} (hle : V ≤ V₁)
    (h1 : H.comap (V₁.ι ≫ Q.ψ) = H'.comap (V₁.ι ≫ Q.ψ'))
    (h2 : I.comap (V₁.ι ≫ Q.ψ) = I.comap (V₁.ι ≫ Q.ψ'))
    (h3 : ∀ i, (E.component i).comap (V₁.ι ≫ Q.ψ) = (E.component i).comap (V₁.ι ≫ Q.ψ'))
    (h4 : AgreeOn (V₁.ι ≫ Q.ψ) (V₁.ι ≫ Q.ψ')
      (MC ((V₁.ι ≫ Q.ψ) ≫ f) (I.comap (V₁.ι ≫ Q.ψ)) m)) :
    H.comap (V.ι ≫ Q.ψ) = H'.comap (V.ι ≫ Q.ψ') ∧ I.comap (V.ι ≫ Q.ψ) = I.comap (V.ι ≫ Q.ψ') ∧
      (∀ i, (E.component i).comap (V.ι ≫ Q.ψ) = (E.component i).comap (V.ι ≫ Q.ψ')) ∧
      AgreeOn (V.ι ≫ Q.ψ) (V.ι ≫ Q.ψ') (MC ((V.ι ≫ Q.ψ) ≫ f) (I.comap (V.ι ≫ Q.ψ)) m) := by
  have hM : ∀ W : Q.W.Opens, MC ((W.ι ≫ Q.ψ) ≫ f) (I.comap (W.ι ≫ Q.ψ)) m =
      (MC (Q.ψ ≫ f) (I.comap Q.ψ) m).comap W.ι := by
    intro W
    rw [MC_comap_of_etale f (W.ι ≫ Q.ψ) I m, MC_comap_of_etale f Q.ψ I m, comap_comp]
  refine ⟨?_, ?_, fun i => ?_, ?_⟩
  · rw [comap_comp, comap_comp] at h1 ⊢
    exact comap_ι_eq_of_le hle h1
  · rw [comap_comp, comap_comp] at h2 ⊢
    exact comap_ι_eq_of_le hle h2
  · have h := h3 i
    rw [comap_comp, comap_comp] at h ⊢
    exact comap_ι_eq_of_le hle h
  · rw [hM] at h4 ⊢
    exact AgreeOn.restrict_of_le Q.ψ Q.ψ' _ hle h4

/-- **Theorem 92 with an affine étale neighbourhood** (Kollár's "we can take `U` to be their
disjoint union", [Kol07, 95]): under the hypotheses of `etaleEquiv_of_isMCInvariant` with `X`
quasi-compact over `k`, there is an étale equivalence of `H` and `H'` with respect to `(X, I, E)`
whose scheme is affine, the disjoint union of finitely many affine opens of the graph
neighbourhoods `U(p)`. -/
theorem exists_etaleEquiv_isAffine [CharZero k] (n : ℕ) [SmoothOfRelativeDimension n f]
    [QuasiCompact f] (I : X.IdealSheafData) {m : ℕ} (hm : 1 ≤ m) (hI : IsMCInvariant f I m)
    (E : DivisorFamily X) (H H' : X.IdealSheafData) (hH : IsMaximalContact f I m H)
    (hH' : IsMaximalContact f I m H') (hHE : (E.append H).IsSnc) (hH'E : (E.append H').IsSnc) :
    ∃ Q : EtaleEquiv f I m E H H', IsAffine Q.U := by
  classical
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hcs : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hS : IsClosed {x | (m : ℕ∞) ≤ I.ord x} := isClosed_setOf_le_ord f n I m
  -- at every closed point of the cosupport, an affine open of a pair carrying (1′)–(4′)
  have key : ∀ p : {p : X // IsClosed ({p} : Set X) ∧ p ∈ {x | (m : ℕ∞) ≤ I.ord x}},
      ∃ (Q : EtaleNbhdPair X p.1) (V : Q.W.Opens), IsAffineOpen V ∧ Q.q ∈ V ∧
        Q.ψ ≫ f = Q.ψ' ≫ f ∧ H.comap (V.ι ≫ Q.ψ) = H'.comap (V.ι ≫ Q.ψ') ∧
        I.comap (V.ι ≫ Q.ψ) = I.comap (V.ι ≫ Q.ψ') ∧
        (∀ i, (E.component i).comap (V.ι ≫ Q.ψ) = (E.component i).comap (V.ι ≫ Q.ψ')) ∧
        AgreeOn (V.ι ≫ Q.ψ) (V.ι ≫ Q.ψ') (MC ((V.ι ≫ Q.ψ) ≫ f) (I.comap (V.ι ≫ Q.ψ)) m) := by
    intro p
    obtain ⟨Q, V₁, hqV₁, hf, h1, h2, h3, h4⟩ :=
      exists_etaleNbhdPair_conditions f n I hm hI E H H' hH hH' hHE hH'E p.1 p.2.1 p.2.2
    obtain ⟨V, hVaff, hqV, hle⟩ := exists_isAffineOpen_mem_and_subset hqV₁
    obtain ⟨h1', h2', h3', h4'⟩ := conditions_restrict_of_le f I m E H H' Q hle h1 h2 h3 h4
    exact ⟨Q, V, hVaff, hqV, hf, h1', h2', h3', h4'⟩
  choose Q V hVaff hqV hf h1 h2 h3 h4 using key
  -- finitely many of them cover the cosupport
  obtain ⟨t, hcov, hcov'⟩ := exists_finset_subset_biUnion_range f hS Q V hqV
  have hcovι : {x | (m : ℕ∞) ≤ I.ord x} ⊆
      ⋃ i : {p // p ∈ t}, Set.range ((V i.1).ι ≫ (Q i.1).ψ).base := by
    intro x hx
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp (hcov hx)
    exact Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hxp⟩
  have hcovι' : {x | (m : ℕ∞) ≤ I.ord x} ⊆
      ⋃ i : {p // p ∈ t}, Set.range ((V i.1).ι ≫ (Q i.1).ψ').base := by
    intro x hx
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp (hcov' hx)
    exact Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hxp⟩
  -- the disjoint union, affine as a finite coproduct of affine schemes
  have : ∀ i : {p // p ∈ t}, IsAffine ((V i.1).toScheme) := fun i => hVaff i.1
  refine ⟨etaleEquivOfFamily f I m E H H' (fun i : {p // p ∈ t} => (V i.1).toScheme)
    (fun i => (V i.1).ι ≫ (Q i.1).ψ) (fun i => (V i.1).ι ≫ (Q i.1).ψ') hcovι hcovι'
    (fun i => by rw [Category.assoc, Category.assoc, hf]) (fun i => h1 i.1) (fun i => h2 i.1)
    (fun i j => h3 i.1 j) (fun i => h4 i.1), ?_⟩
  change IsAffine (∐ fun i : {p // p ∈ t} => (V i.1).toScheme)
  infer_instance

end AlgebraicGeometry.Scheme.IdealSheafData
