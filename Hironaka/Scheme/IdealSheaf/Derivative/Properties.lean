/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.CohenIso
public import Hironaka.Scheme.IdealSheaf.Order.Constructible
public import Hironaka.Algebra.Local.CompletionCoords
public import Hironaka.Scheme.IdealSheaf.Derivative.Sheaf
public import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Algebra.Local.DerivativeCompletion
import Hironaka.Scheme.IdealSheaf.Derivative.Cosupport
import Hironaka.Scheme.IdealSheaf.Derivative.StalkCoords
import Hironaka.Scheme.IdealSheaf.StalkLe
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Basic properties of the derivative ideal sheaf

[Kol07, Lemma 74 (1), (2), (5)], "higher derivatives have the usual properties", stated there
without proof, and the remark after [Kol07, Definition 73]: if `max-ord I ≤ m` then `Dᵐ(I) = 𝒪_X`,
so the `Dʳ(I)` form an ascending chain `I ⊂ D(I) ⊂ ⋯ ⊂ Dᵐ(I) = 𝒪_X`. The converse is
[Wlo05, Definition 2.7.1]: a marked ideal `(I, μ)` is of maximal order if `max{ord_x I} ≤ μ`, "or
equivalently `D^μ(I) = 𝒪_X`".

* Order properties, with no hypothesis on `f`: `I ≤ D(I)`, `Dʳ(Dˢ(I)) = D^{r+s}(I)`
  ([Kol07, Lemma 74 (1)]), monotonicity in `I` and in `r`, and once `Dᵐ(I) = 𝒪_X` so is every
  later `Dʳ(I)`; these are order facts about `ofIdeals` and iterates.
* On a scheme locally of finite type over `k`, sectionwise: `D(I + J) = D(I) + D(J)`
  (`derivative_sup`, from `Ideal.derivative_sup` of `Hironaka/Algebra/Derivative/Basic.lean`, a
  `k`-derivation being additive; this is immediate from the definition and is not one of the items
  of Lemma 74) and the product rule `Dʳ(I·J) ≤ ⨆_{i ≤ r} Dⁱ(I) D^{r−i}(J)` ([Kol07, Lemma 74 (2)],
  `derivativeIter_mul_le`, from Leibniz for every `k`-derivation).
* On a smooth `k`-scheme in characteristic zero: `D^μ(I) = 𝒪_X ⟺ max-ord I ≤ μ`
  (`derivativeIter_eq_top_iff_maxOrd_le`): `D^μ(I)` is the unit ideal sheaf iff its support
  `{ord ≥ μ + 1}` (`Hironaka/Scheme/IdealSheaf/Derivative/Cosupport.lean`) is empty iff every `ord_x
  I ≤ μ` (`maxOrd_le_iff`, `Hironaka/Scheme/IdealSheaf/Order/Constructible.lean`).
* [Kol07, Lemma 74 (5)], `D(Î) = \widehat{D(I)}`, in coordinates: for coordinates whose `k`-linear
  `∂ᵢ` span the `k`-derivations, `c.adicCompletion.D (J R̂) = (D_k J) R̂`
  (`D_adicCompletion_derivative`, from `D_adicCompletion` of
  `Hironaka/Algebra/Local/DerivativeCompletion.lean`), and at a point with residue field algebraic
  over `k` such coordinates exist on the stalk
  (`Hironaka/Scheme/IdealSheaf/Derivative/StalkCoords.lean`), giving `c.adicCompletion.D (I_x
  Ô_{X,x}) = D(I)_x Ô_{X,x}` (`exists_regularCoords_D_adicCompletion`, which nothing else in the
  library uses).

Used for Theorem 88 (`Hironaka/Scheme/BlowUpSequence/Theorem88Basic.lean`,
`Hironaka/Resolution/Algebraic/Kol07/Theorem88BlowUp.lean`,
`Hironaka/Resolution/Algebraic/Kol07/Theorem88Sequence.lean`), for the transforms of derivatives
(`Hironaka/Scheme/BlowUpSequence/TransformDerivative.lean`), for the logarithmic derivative sheaf
(`Hironaka/Scheme/IdealSheaf/Derivative/LogarithmicSheaf.lean`), for tuning
(`Hironaka/Resolution/Algebraic/Tuning/Sheaf.lean`) and for functoriality
(`Hironaka/Resolution/Algebraic/OrderReduction/Functorial.lean`).
-/

public section

open IsLocalRing

/-! ### The completion, in coordinates ([Kol07, Lemma 74 (5)]) -/

namespace IsLocalRing.RegularCoords

variable {k : Type*} [CommRing k] {R : Type*} [CommRing R] [IsRegularLocalRing R] [Algebra ℚ R]
  [Algebra k R] {n : ℕ} (c : RegularCoords R n)

/-- [Kol07, Lemma 74 (5)], `D(Ĵ) = \widehat{D(J)}`: for coordinates whose `k`-linear `∂ᵢ` span
the `k`-derivations, the coordinate derivative of `J R̂` on the completion is the extension of
Kollár's image ideal `D_k(J)`. -/
theorem D_adicCompletion_derivative (hk : c.IsLinearOver k) (hs : c.SpansDerivations k)
    (J : Ideal R) :
    c.adicCompletion.D (J.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) =
      (Ideal.derivative k J).map (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
  rw [c.D_adicCompletion, Ideal.derivative_eq_D c hk hs]

end IsLocalRing.RegularCoords

namespace AlgebraicGeometry.Scheme.IdealSheafData

open CategoryTheory TopologicalSpace IsLocalRing

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-! ### Order properties, with no hypothesis on `f` -/

/-- `I ⊆ D(I)` ([Kol07, (73.2)]). -/
theorem le_derivative (I : X.IdealSheafData) : I ≤ derivative f I :=
  le_ofIdeals_iff.mpr fun U => letI := f.sectionsAlgebra U.1; Ideal.le_derivative (I.ideal U)

/-- `D` is monotone. -/
theorem derivative_mono {I J : X.IdealSheafData} (h : I ≤ J) : derivative f I ≤ derivative f J :=
  ofIdeals_mono fun U => letI := f.sectionsAlgebra U.1; Ideal.derivative_mono (h U)

/-- [Kol07, Lemma 74 (1)]: `Dʳ(Dˢ(I)) = D^{r+s}(I)`. -/
theorem derivativeIter_derivativeIter (r s : ℕ) (I : X.IdealSheafData) :
    derivativeIter f r (derivativeIter f s I) = derivativeIter f (r + s) I :=
  (Function.iterate_add_apply _ _ _ _).symm

/-- `I ⊆ Dʳ(I)`. -/
theorem le_derivativeIter (r : ℕ) (I : X.IdealSheafData) : I ≤ derivativeIter f r I := by
  induction r with
  | zero => exact le_rfl
  | succ r ih => rw [derivativeIter_succ]; exact ih.trans (le_derivative f _)

/-- `Dʳ` is monotone. -/
theorem derivativeIter_mono (r : ℕ) {I J : X.IdealSheafData} (h : I ≤ J) :
    derivativeIter f r I ≤ derivativeIter f r J := by
  induction r with
  | zero => exact h
  | succ r ih => rw [derivativeIter_succ, derivativeIter_succ]; exact derivative_mono f ih

/-- The `Dʳ(I)` ascend in `r` (the chain after [Kol07, Definition 73]). -/
theorem derivativeIter_mono_left {r s : ℕ} (h : r ≤ s) (I : X.IdealSheafData) :
    derivativeIter f r I ≤ derivativeIter f s I := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_comm, ← derivativeIter_derivativeIter]
  exact le_derivativeIter f t _

/-- Once `Dᵐ(I) = 𝒪_X`, so is every later `Dʳ(I)`. -/
theorem derivativeIter_eq_top_of_le (I : X.IdealSheafData) {m r : ℕ} (h : m ≤ r)
    (hm : derivativeIter f m I = ⊤) : derivativeIter f r I = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← hm]
  exact derivativeIter_mono_left f h I

/-! ### Sums and products on a scheme locally of finite type, sectionwise -/

section FiniteType

variable [LocallyOfFiniteType f]

/-- `Dʳ(I)(U) = Dʳ(I(U))` on every affine open (`ideal_derivative` of
`Hironaka/Scheme/IdealSheaf/Derivative/Sheaf.lean`, iterated). -/
theorem ideal_derivativeIter (r : ℕ) (I : X.IdealSheafData) (U : X.affineOpens) :
    (derivativeIter f r I).ideal U =
      letI := f.sectionsAlgebra U.1; Ideal.derivativeIter k r (I.ideal U) := by
  let _ := f.sectionsAlgebra U.1
  induction r with
  | zero => rfl
  | succ r ih => rw [derivativeIter_succ, ideal_derivative, ih, Ideal.derivativeIter_succ]

/-- `D(I ⊔ J) = D(I) ⊔ D(J)`, immediate from the definition of `D`. -/
theorem derivative_sup (I J : X.IdealSheafData) :
    derivative f (I ⊔ J) = derivative f I ⊔ derivative f J := by
  ext U : 2
  let _ := f.sectionsAlgebra U.1
  simp only [ideal_derivative f, ideal_sup, Pi.sup_apply, Ideal.derivative_sup]

/-- `D(I + J) = D(I) + D(J)` (the sum of ideal sheaves is their supremum). -/
theorem derivative_add (I J : X.IdealSheafData) :
    derivative f (I + J) = derivative f I + derivative f J :=
  derivative_sup f I J

/-- [Kol07, Lemma 74 (2)] for `r = 1`: `D(IJ) ⊆ D(I) J + I D(J)`. -/
theorem derivative_mul_le (I J : X.IdealSheafData) :
    derivative f (I * J) ≤ derivative f I * J + I * derivative f J := by
  change derivative f (I * J) ≤ derivative f I * J ⊔ I * derivative f J
  intro U
  let _ := f.sectionsAlgebra U.1
  simp only [ideal_derivative f, ideal_sup, ideal_mul, Pi.sup_apply, Pi.mul_apply]
  exact Ideal.derivative_mul_le _ _

/-- [Kol07, Lemma 74 (2)], the product rule `Dʳ(I·J) ⊆ ∑_{i=0}^r Dⁱ(I) D^{r−i}(J)`, the sum of
ideal sheaves being their supremum. -/
theorem derivativeIter_mul_le (r : ℕ) (I J : X.IdealSheafData) :
    derivativeIter f r (I * J) ≤
      ⨆ i ∈ Finset.range (r + 1), derivativeIter f i I * derivativeIter f (r - i) J := by
  intro U
  let _ := f.sectionsAlgebra U.1
  have h : (⨆ i ∈ Finset.range (r + 1), derivativeIter f i I * derivativeIter f (r - i) J).ideal U =
      ⨆ i ∈ Finset.range (r + 1),
        Ideal.derivativeIter k i (I.ideal U) * Ideal.derivativeIter k (r - i) (J.ideal U) := by
    rw [ideal_iSup', iSup_apply]
    refine iSup_congr fun i => ?_
    rw [ideal_iSup', iSup_apply]
    refine iSup_congr fun _ => ?_
    rw [ideal_mul, Pi.mul_apply, ideal_derivativeIter f, ideal_derivativeIter f]
  rw [h, ideal_derivativeIter f, ideal_mul, Pi.mul_apply]
  exact Ideal.derivativeIter_mul_le _ _ _

end FiniteType

/-! ### Maximal order and the completion on a smooth `k`-scheme in characteristic zero -/

section Smooth

variable [CharZero k] (n : ℕ) [SmoothOfRelativeDimension n f]

include f n in
/-- [Wlo05, Definition 2.7.1]: `(I, μ)` is of maximal order, `D^μ(I) = 𝒪_X`, iff `max-ord I ≤ μ`.
The support of `D^μ(I)` is `{ord ≥ μ + 1}`, empty iff every `ord_x I ≤ μ`. -/
theorem derivativeIter_eq_top_iff_maxOrd_le (I : X.IdealSheafData) (μ : ℕ) :
    derivativeIter f μ I = ⊤ ↔ I.maxOrd ≤ μ := by
  have key : ∀ x : X, x ∈ (derivativeIter f μ I).support ↔ (μ : ℕ∞) + 1 ≤ I.ord x := fun x => by
    rw [← Nat.cast_succ, le_ord_iff_mem_support_derivativeIter f n I x (Nat.le_add_left 1 μ),
      Nat.add_sub_cancel]
  rw [← support_eq_bot_iff, ← Closeds.coe_eq_empty, Set.eq_empty_iff_forall_notMem, maxOrd_le_iff]
  refine forall_congr' fun x => ?_
  rw [SetLike.mem_coe, key x, not_le, ENat.lt_add_one_iff (ENat.natCast_ne_top μ)]

include f n in
/-- The remark after [Kol07, Definition 73]: if `max-ord I ≤ m` then `Dᵐ(I) = 𝒪_X`. -/
theorem derivativeIter_eq_top_of_maxOrd_le (I : X.IdealSheafData) {m : ℕ} (h : I.maxOrd ≤ m) :
    derivativeIter f m I = ⊤ :=
  (derivativeIter_eq_top_iff_maxOrd_le f n I m).mpr h

include n in
/-- [Kol07, Lemma 74 (5)] at a stalk: at a point with residue field algebraic over `k`, the stalk
carries coordinates spanning the `k`-derivations, and for them `D(Î_x) = \widehat{D(I)_x}` in
`Ô_{X,x}`: the coordinate derivative of `I_x Ô_{X,x}` is the extension of the stalk
`D(I)_x = D_k(I_x)`. -/
theorem exists_regularCoords_D_adicCompletion (I : X.IdealSheafData) (x : X)
    (halg : letI := f.stalkAlgebra x
      Algebra.IsAlgebraic k (ResidueField (X.presheaf.stalk x))) :
    letI := f.stalkAlgebra x
    letI := f.stalkAlgebraRat x
    haveI := @isRegularLocalRing_stalk k _ X f
      (SmoothOfRelativeDimension.smooth n f) x
    ∃ (m : ℕ) (c : RegularCoords (X.presheaf.stalk x) m),
      c.IsLinearOver k ∧ c.SpansDerivations k ∧
        c.adicCompletion.D ((I.stalkIdeal x).map (algebraMap (X.presheaf.stalk x)
            (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)))) =
          ((derivative f I).stalkIdeal x).map (algebraMap (X.presheaf.stalk x)
            (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))) := by
  let _ := f.stalkAlgebra x
  let _ := f.stalkAlgebraRat x
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hft : LocallyOfFiniteType f := inferInstance
  have hreg := @isRegularLocalRing_stalk k _ X f hsm x
  obtain ⟨m, c, hk, hs⟩ := exists_regularCoords_stalk_of_isAlgebraic f n x halg
  refine ⟨m, c, hk, hs, ?_⟩
  rw [stalkIdeal_derivative f I x, c.D_adicCompletion_derivative hk hs]

end Smooth

end AlgebraicGeometry.Scheme.IdealSheafData
