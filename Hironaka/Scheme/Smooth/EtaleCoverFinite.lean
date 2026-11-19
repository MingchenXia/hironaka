/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Smooth.Graph
import Hironaka.Algebra.Util.JacobsonCover
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Finitely many étale neighbourhoods cover the closed set

Kollár: "The images of finitely many of the `U(p)` cover `X`" ([Kol07, 95], the proof of
Theorem 92). Read on the relevant closed set `S`, for a family of étale neighbourhood pairs
`Q p : EtaleNbhdPair X p` (`Hironaka/Scheme/Smooth/Graph.lean`) given at the closed points `p` of
`S`:

* the image of the open `V p ⊆ W_p` under the étale `ψ_p` is open (étale morphisms are universally
  open, Mathlib's `UniversallyOpen.of_flat`) and contains `p` (`mem_range_ι_comp_ψ`);
* for `X` locally of finite type over a field, `X` is Jacobson
  (`LocallyOfFiniteType.jacobsonSpace`), so these images, over the closed points `p` of the closed
  set `S`, cover `S` (`subset_iUnion_range_ι_comp_ψ`, `…ψ'`; the topology is
  `Hironaka/Algebra/Util/JacobsonCover.lean`: every point of `S` specializes to a closed point of
  `S`);
* for `X` quasi-compact, finitely many closed points suffice, and one finite set serves both
  families of images by covering with the intersections `ψ_p(V p) ∩ ψ'_p(V p)`
  (`exists_finset_subset_biUnion_range`).

The finite family is assembled into one étale pair on a disjoint union in
`Hironaka/Resolution/Algebraic/MaximalContact/EtaleEquivSigma.lean`.
-/

public section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

variable {X : Scheme.{u}}

/-- The point `p` lies in the image of the open `V ∋ q` under `ψ`. -/
theorem mem_range_ι_comp_ψ {p : X} (Q : EtaleNbhdPair X p) {V : Q.W.Opens} (hV : Q.q ∈ V) :
    p ∈ Set.range (V.ι ≫ Q.ψ).base :=
  ⟨(⟨Q.q, hV⟩ : (V : Scheme.{u})), Q.ψ_q⟩

/-- The point `p` lies in the image of the open `V ∋ q` under `ψ'`. -/
theorem mem_range_ι_comp_ψ' {p : X} (Q : EtaleNbhdPair X p) {V : Q.W.Opens} (hV : Q.q ∈ V) :
    p ∈ Set.range (V.ι ≫ Q.ψ').base :=
  ⟨(⟨Q.q, hV⟩ : (V : Scheme.{u})), Q.ψ'_q⟩

variable {k : Type u} [Field k]

/-- The images `ψ_p(V p)`, over the closed points `p` of a closed set `S`, cover `S`: the closed
points are dense in every closed subset of the Jacobson space `X`. -/
theorem subset_iUnion_range_ι_comp_ψ (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] {S : Set X}
    (hS : IsClosed S)
    (Q : ∀ p : {p : X // IsClosed {p} ∧ p ∈ S}, EtaleNbhdPair X p.1)
    (V : ∀ p, (Q p).W.Opens) (hV : ∀ p, (Q p).q ∈ V p) :
    S ⊆ ⋃ p, Set.range ((V p).ι ≫ (Q p).ψ).base := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  exact subset_iUnion_of_isOpen_of_closedPoints hS _
    (fun p => ((V p).ι ≫ (Q p).ψ).isOpenMap.isOpen_range)
    (fun p => mem_range_ι_comp_ψ (Q p) (hV p))

/-- The images `ψ'_p(V p)` cover `S` as well. -/
theorem subset_iUnion_range_ι_comp_ψ' (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] {S : Set X}
    (hS : IsClosed S)
    (Q : ∀ p : {p : X // IsClosed {p} ∧ p ∈ S}, EtaleNbhdPair X p.1)
    (V : ∀ p, (Q p).W.Opens) (hV : ∀ p, (Q p).q ∈ V p) :
    S ⊆ ⋃ p, Set.range ((V p).ι ≫ (Q p).ψ').base := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  exact subset_iUnion_of_isOpen_of_closedPoints hS _
    (fun p => ((V p).ι ≫ (Q p).ψ').isOpenMap.isOpen_range)
    (fun p => mem_range_ι_comp_ψ' (Q p) (hV p))

/-- For `X` quasi-compact, finitely many closed points `p_1, …, p_N` of `S` have
`⋃ ψ_{p_i}(V p_i) ⊇ S` and `⋃ ψ'_{p_i}(V p_i) ⊇ S` ("the images of finitely many of the `U(p)`
cover `X`", [Kol07, 95]): cover `S` by the open sets `ψ_p(V p) ∩ ψ'_p(V p) ∋ p` and take a finite
subcover of the compact closed set `S`. -/
theorem exists_finset_subset_biUnion_range (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    [CompactSpace X] {S : Set X} (hS : IsClosed S)
    (Q : ∀ p : {p : X // IsClosed {p} ∧ p ∈ S}, EtaleNbhdPair X p.1)
    (V : ∀ p, (Q p).W.Opens) (hV : ∀ p, (Q p).q ∈ V p) :
    ∃ t : Finset {p : X // IsClosed {p} ∧ p ∈ S},
      S ⊆ ⋃ p ∈ t, Set.range ((V p).ι ≫ (Q p).ψ).base ∧
        S ⊆ ⋃ p ∈ t, Set.range ((V p).ι ≫ (Q p).ψ').base := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  set O : {p : X // IsClosed {p} ∧ p ∈ S} → Set X := fun p =>
    Set.range ((V p).ι ≫ (Q p).ψ).base ∩ Set.range ((V p).ι ≫ (Q p).ψ').base with hO
  have hOopen : ∀ p, IsOpen (O p) := fun p =>
    ((V p).ι ≫ (Q p).ψ).isOpenMap.isOpen_range.inter ((V p).ι ≫ (Q p).ψ').isOpenMap.isOpen_range
  have hpO : ∀ p, p.1 ∈ O p := fun p =>
    ⟨mem_range_ι_comp_ψ (Q p) (hV p), mem_range_ι_comp_ψ' (Q p) (hV p)⟩
  obtain ⟨t, ht⟩ := hS.isCompact.elim_finite_subcover O hOopen
    (subset_iUnion_of_isOpen_of_closedPoints hS O hOopen hpO)
  exact ⟨t, ht.trans (Set.iUnion₂_mono fun p _ => Set.inter_subset_left),
    ht.trans (Set.iUnion₂_mono fun p _ => Set.inter_subset_right)⟩

end AlgebraicGeometry
