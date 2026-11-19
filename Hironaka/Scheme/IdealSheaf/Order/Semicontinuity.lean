/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Derivative.Sheaf
public import Mathlib.Topology.Semicontinuity.Defs
import Hironaka.Scheme.IdealSheaf.Derivative.Cosupport
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Upper semicontinuity of the order function

[Kol07, Definition 47]: "It is easy to see that `x ↦ ord_x I` is a constructible and
upper-semi-continuous function on `X`." The characteristic-zero route through derivatives
([Kol07, Lemma 74 (3)]; [Wlo05, Lemma 2.6.2], `supp(I, μ) = V(D^{μ−1}(I))` is closed): on a scheme
smooth of relative dimension `n` over a field `k` of characteristic zero,

* `{x : ord_x I ≥ m} = V(D^{m−1} I)` for `m ≥ 1`, the cosupport transfer of
  `Hironaka/Scheme/IdealSheaf/Derivative/Cosupport.lean` (`le_ord_iff_mem_support_derivativeIter`)
  read as an equality of sets (`setOf_le_ord_eq_support_derivativeIter`);
* `{ord ≥ m}` is closed for every `m ∈ ℕ` (`m = 0`: the whole space; `m ≥ 1`: a support, closed by
  Mathlib's `isClosed_supportSet`), and `{ord = ∞} = ⋂_m {ord ≥ m}` is closed; it is `{x : I_x = 0}`
  by Krull (`ord_eq_top_iff`, for `X` locally Noetherian, automatic for a scheme locally of finite
  type over a field, `isLocallyNoetherian_of_field`);
* `x ↦ ord_x I` is upper semicontinuous into `ℕ∞` with its order topology, Mathlib's
  `UpperSemicontinuous`, that is, every `{x : ord_x I ≥ y}` is closed
  (`upperSemicontinuous_iff_isClosed_preimage`), which is the previous point for `y = m` and
  `y = ∞`.

Used for the constructibility and the finiteness of the order
(`Hironaka/Scheme/IdealSheaf/Order/Constructible.lean`), for its monotonicity along specialization
(`Hironaka/Scheme/IdealSheaf/Order/Specialization.lean`), and directly in
`Hironaka/Resolution/Algebraic/Hir64/OrderProduct.lean`,
`Hironaka/Resolution/Algebraic/Hir64/Corollary1.lean`,
`Hironaka/Resolution/Algebraic/Hir64/TrivializationLoci.lean`,
`Hironaka/Resolution/Algebraic/MaximalContact/EtaleEquivSigma.lean`,
`Hironaka/Resolution/Algebraic/MaximalContact/Existence.lean` and on manifolds
(`Hironaka/Manifold/IdealSheaf/Order.lean`).
-/

public section

namespace AlgebraicGeometry.Scheme.IdealSheafData

open CategoryTheory IsLocalRing TopologicalSpace

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- A scheme locally of finite type over a field is locally Noetherian: on every affine open the
ring of sections is a finitely generated `k`-algebra, hence Noetherian. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.isLocallyNoetherian_of_field [LocallyOfFiniteType f] :
    IsLocallyNoetherian X := by
  refine isLocallyNoetherian_of_affine_cover (S := fun U : X.affineOpens => U)
    (iSup_affineOpens_eq_top X) fun U => ?_
  let _ := f.sectionsAlgebra U.1
  have := f.finiteType_sectionsAlgebra U.2
  exact Algebra.FiniteType.isNoetherianRing k Γ(X, U.1)

/-- The infinite level set as an intersection: `{ord = ∞} = ⋂_m {ord ≥ m}`. -/
theorem setOf_ord_eq_top_eq_iInter (I : X.IdealSheafData) :
    {x | I.ord x = ⊤} = ⋂ m : ℕ, {x | (m : ℕ∞) ≤ I.ord x} := by
  ext x
  rw [Set.mem_iInter]
  exact ENat.eq_top_iff_forall_ge

/-- `{ord = ∞} = {x : I_x = 0}` on a scheme locally of finite type over a field (Krull's
intersection theorem). -/
theorem setOf_ord_eq_top_eq_setOf_stalkIdeal_eq_bot [LocallyOfFiniteType f] (I : X.IdealSheafData) :
    {x | I.ord x = ⊤} = {x | I.stalkIdeal x = ⊥} := by
  have := f.isLocallyNoetherian_of_field
  ext x
  exact ord_eq_top_iff I x

section Smooth

variable [CharZero k] (n : ℕ) [SmoothOfRelativeDimension n f]

include n in
/-- [Kol07, Lemma 74 (3)]; [Wlo05, Lemma 2.6.2]: `{x : ord_x I ≥ m} = V(D^{m−1} I)` for `m ≥ 1`,
the cosupport transfer as an equality of sets. -/
theorem setOf_le_ord_eq_support_derivativeIter (I : X.IdealSheafData) {m : ℕ} (hm : 1 ≤ m) :
    {x | (m : ℕ∞) ≤ I.ord x} = ((I.derivativeIter f (m - 1)).support : Set X) := by
  ext x
  exact le_ord_iff_mem_support_derivativeIter f n I x hm

include f n in
/-- `{x : ord_x I ≥ m}` is closed for every `m ∈ ℕ` (for `m = 0` it is `X`; for `m ≥ 1` it is the
support `V(D^{m−1} I)`). -/
theorem isClosed_setOf_le_ord (I : X.IdealSheafData) (m : ℕ) :
    IsClosed {x | (m : ℕ∞) ≤ I.ord x} := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : {x | ((0 : ℕ) : ℕ∞) ≤ I.ord x} = Set.univ := Set.eq_univ_of_forall fun x => by simp
    rw [this]
    exact isClosed_univ
  · rw [setOf_le_ord_eq_support_derivativeIter f n I hm]
    exact (I.derivativeIter f (m - 1)).support.isClosed

include f n in
/-- `{x : ord_x I = ∞}` is closed. -/
theorem isClosed_setOf_ord_eq_top (I : X.IdealSheafData) : IsClosed {x | I.ord x = ⊤} := by
  rw [setOf_ord_eq_top_eq_iInter]
  exact isClosed_iInter fun m => isClosed_setOf_le_ord f n I m

include f n in
/-- [Kol07, Definition 47]: `x ↦ ord_x I` is upper semicontinuous into `ℕ∞` with its order
topology — every `{x : ord_x I ≥ y}` is closed. -/
theorem upperSemicontinuous_ord (I : X.IdealSheafData) : UpperSemicontinuous fun x => I.ord x := by
  rw [upperSemicontinuous_iff_isClosed_preimage]
  intro y
  induction y using ENat.recTopCoe with
  | top =>
    have : (fun x => I.ord x) ⁻¹' Set.Ici ⊤ = {x | I.ord x = ⊤} := by
      ext x
      change ⊤ ≤ I.ord x ↔ I.ord x = ⊤
      exact top_le_iff
    rw [this]
    exact isClosed_setOf_ord_eq_top f n I
  | coe m => exact isClosed_setOf_le_ord f n I m

end Smooth

end AlgebraicGeometry.Scheme.IdealSheafData
