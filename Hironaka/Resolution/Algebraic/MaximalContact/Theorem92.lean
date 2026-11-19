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
import Hironaka.Algebra.Local.RegularSystemCommon
import Hironaka.Algebra.RegularSmooth.SchemeForms
import Hironaka.Resolution.Algebraic.MaximalContact.Coordinates
import Hironaka.Resolution.Algebraic.MaximalContact.EtaleEquivSigma
import Hironaka.Resolution.Algebraic.MaximalContact.EtaleNbhdConditions
import Hironaka.Resolution.Algebraic.MaximalContact.GraphOfAutomorphism
import Hironaka.Scheme.Smooth.CoordinateSystemPair
import Hironaka.Scheme.Smooth.GraphCompletion
import Hironaka.Scheme.Smooth.GraphDiagonalPair
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Theorem 92: uniqueness of maximal contact up to étale equivalence

[Kol07, Theorem 92]: for `X` a smooth variety over a field of characteristic zero, `I` an
MC-invariant ideal sheaf, `m = max-ord I`, `E` a simple normal crossing divisor and `H, H' ⊂ X`
two smooth hypersurfaces of maximal contact for `I` such that `H + E` and `H' + E` both have
simple normal crossings, `H` and `H'` are étale equivalent with respect to `(X, I, E)`. The proof
is [Kol07, 95]: at every closed point `p` of the cosupport `cosupp(I, m)`,

1. `exists_coordinates` (`Hironaka/Resolution/Algebraic/MaximalContact/Coordinates.lean`) chooses
   coordinates `x₁, x₁' ∈ MC(I)` with `H = (x₁ = 0)`, `H' = (x₁' = 0)` and a common complement
   `y = (x₂, …, xₙ)` adapted to `E`; `n = d + 1` is the relative dimension;
2. `exists_etaleCoordinates_pair` (`Hironaka/Scheme/Smooth/CoordinateSystemPair.lean`) spreads the
   two regular systems `(x₁, y)`, `(x₁', y)` out to étale coordinate maps `c, c' : U → 𝔸ⁿ_k` on an
   affine `U ∋ p`;
3. the graph `U₁(p) = U ×_{𝔸ⁿ} U` at the diagonal point `(p, p)` is an étale neighbourhood pair
   over `k` with the graph equations and trivial action on `κ(p)`
   (`exists_etaleNbhdPair_of_etaleCoordinates`, `Hironaka/Scheme/Smooth/GraphDiagonalPair.lean`);
4. its automorphism satisfies (91.1)–(91.4): the completion of `U₁(p)` at `(p, p)` is the graph of
   the formal automorphism `φₚ`
   (`Hironaka/Resolution/Algebraic/MaximalContact/GraphOfAutomorphism.lean`);
5. the conditions (1′)–(4′) of étale equivalence hold on an open `U(p) ∋ (p, p)`
   (`exists_opens_conditions_of_formalAutomorphism`,
   `Hironaka/Resolution/Algebraic/MaximalContact/EtaleNbhdConditions.lean`);

and the disjoint union of the `U(p)` is the étale equivalence
(`nonempty_etaleEquiv_of_forall_isClosed`,
`Hironaka/Resolution/Algebraic/MaximalContact/EtaleEquivSigma.lean`). The output is `EtaleEquiv f I
m E H H'`, [Kol07, Definition 91] in the form where the images of `ψ, ψ'` contain the cosupport
(`Hironaka/Resolution/Algebraic/MaximalContact/EtaleEquiv.lean`, **Conventions**).

**Conventions.** Kollár's hypotheses that `E` is simple normal crossing and that `H, H'` are
smooth are not stated separately, since they follow from `H + E` and `H' + E` being simple normal
crossing; `m = max-ord I` is weakened to `m ≥ 1`. The affine form of the theorem
(`Hironaka/Resolution/Algebraic/MaximalContact/EtaleEquivAffine.lean`) is what the independence of
the order-reduction functor from the hypersurface
(`Hironaka/Resolution/Algebraic/MaximalContact/FunctorIndependence.lean`) uses.
-/

public section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

open CategoryTheory IsLocalRing Scheme AlgebraicGeometry

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f]

include n in
/-- The étale neighbourhood of one closed point of the cosupport ([Kol07, 95]): for a closed point
`p ∈ cosupp(I, m)` there is an étale neighbourhood pair `Q` of `p` over `k` and an open `V ∋ q` on
which the conditions (1′)–(4′) hold; steps 1–5 of the module docstring assembled. -/
theorem exists_etaleNbhdPair_conditions (I : X.IdealSheafData) {m : ℕ} (hm : 1 ≤ m)
    (hI : IsMCInvariant f I m) (E : DivisorFamily X) (H H' : X.IdealSheafData)
    (hH : IsMaximalContact f I m H) (hH' : IsMaximalContact f I m H')
    (hHE : (E.append H).IsSnc) (hH'E : (E.append H').IsSnc) (p : X) (hpc : IsClosed ({p} : Set X))
    (hp : (m : ℕ∞) ≤ I.ord p) :
    ∃ (Q : EtaleNbhdPair X p) (V : Q.W.Opens), Q.q ∈ V ∧ Q.ψ ≫ f = Q.ψ' ≫ f ∧
      H.comap (V.ι ≫ Q.ψ) = H'.comap (V.ι ≫ Q.ψ') ∧
      I.comap (V.ι ≫ Q.ψ) = I.comap (V.ι ≫ Q.ψ') ∧
      (∀ i, (E.component i).comap (V.ι ≫ Q.ψ) = (E.component i).comap (V.ι ≫ Q.ψ')) ∧
      AgreeOn (V.ι ≫ Q.ψ) (V.ι ≫ Q.ψ') (MC ((V.ι ≫ Q.ψ) ≫ f) (I.comap (V.ι ≫ Q.ψ)) m) := by
  classical
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hpf : PerfectField k := PerfectField.ofCharZero
  have hreg := isRegularLocalRing_stalk f p
  -- the coordinates
  obtain ⟨d, x₁, x₁', y, hx₁, hx₁', hHp, hH'p, hz, hz', c₀, -, hc₀⟩ :=
    exists_coordinates f n I hm E H H' hH hH' hHE hH'E p hp
  -- `d + 1 = n`
  have hdim : ((d + 1 : ℕ) : WithBot ℕ∞) = (n : WithBot ℕ∞) :=
    hz.2.trans (Scheme.ringKrullDim_stalk_of_smoothOfRelativeDimension_of_isClosed f n hpc)
  have hdn : d + 1 = n := by exact_mod_cast hdim
  subst hdn
  -- the étale coordinate maps
  obtain ⟨U, hpU, c, c', hcv, hc'v, -⟩ := exists_etaleCoordinates_pair f (d + 1) hpc
    (Fin.cons x₁ y) 0 x₁' hz.1.symm (by rw [Fin.update_cons_zero]; exact hz'.1.symm)
  have hc : ∀ i, X.presheaf.germ U.1 p hpU (c.v i) ∈ maximalIdeal (X.presheaf.stalk p) :=
    fun i => by rw [hcv]; exact mem_maximalIdeal_of_eq_span hz.1.symm i
  have hc' : ∀ i, X.presheaf.germ U.1 p hpU (c'.v i) ∈ maximalIdeal (X.presheaf.stalk p) :=
    fun i => by rw [hc'v, Fin.update_cons_zero]; exact mem_maximalIdeal_of_eq_span hz'.1.symm i
  -- the pair at `(p, p)`
  obtain ⟨Q, hf, hres, hQ⟩ := c.exists_etaleNbhdPair_of_etaleCoordinates c' hpU hc hc'
  have hQ' : ∀ i, Q.stalkHom ((Fin.cons x₁ y : Fin (d + 1) → X.presheaf.stalk p) i) =
      Q.stalkHom' ((Fin.cons x₁' y : Fin (d + 1) → X.presheaf.stalk p) i) := fun i => by
    have := hQ i
    rwa [hcv, hc'v, Fin.update_cons_zero] at this
  -- the completion of `U₁(p)` at `(p, p)` is the graph of `φₚ`
  have ha := bijective_completionMap_stalkHom Q
  have ha' := bijective_completionMap_stalkHom' Q
  obtain ⟨h1, h2, h3, h4⟩ := conditions_formalAutomorphism_symm f (d + 1) I hm hI E H H' hpc hp
    x₁ x₁' y hx₁ hx₁' hHp hH'p hz' (fun i hi => ⟨c₀ ⟨i, hi⟩, hc₀ ⟨i, hi⟩⟩) Q hf hres hQ' ha ha'
  -- (91.1′–4′) on an open `U(p)`
  obtain ⟨V, hqV, hV1, hV2, hV3, hV4⟩ :=
    exists_opens_conditions_of_formalAutomorphism f I m E H H' Q ha ha' h1 h2 h3 h4
  exact ⟨Q, V, hqV, hf, hV1, hV2, hV3, hV4⟩

include n in
/-- **[Kol07, Theorem 92]** (proof: [Kol07, 95]): for `X` smooth over `k` of characteristic zero,
`I` MC-invariant, `m ≥ 1`, and `H, H'` hypersurfaces of maximal contact for `I` with `H + E`,
`H' + E` simple normal crossing, `H` and `H'` are étale equivalent with respect to `(X, I, E)`
(`EtaleEquiv`, [Kol07, Definition 91] in the form where the images of `ψ, ψ'` contain the
cosupport). The module docstring says which hypotheses of the printed statement are implied or
weakened. -/
theorem etaleEquiv_of_isMCInvariant (I : X.IdealSheafData) {m : ℕ} (hm : 1 ≤ m)
    (hI : IsMCInvariant f I m) (E : DivisorFamily X) (H H' : X.IdealSheafData)
    (hH : IsMaximalContact f I m H) (hH' : IsMaximalContact f I m H')
    (hHE : (E.append H).IsSnc) (hH'E : (E.append H').IsSnc) :
    Nonempty (EtaleEquiv f I m E H H') := by
  classical
  choose Q V hqV hf h1 h2 h3 h4 using
    fun p : {p : X // IsClosed ({p} : Set X) ∧ p ∈ {x | (m : ℕ∞) ≤ I.ord x}} =>
      exists_etaleNbhdPair_conditions f n I hm hI E H H' hH hH' hHE hH'E p.1 p.2.1 p.2.2
  exact nonempty_etaleEquiv_of_forall_isClosed f n I m E H H' Q V hqV hf h1 h2 h3 h4

end AlgebraicGeometry.Scheme.IdealSheafData
