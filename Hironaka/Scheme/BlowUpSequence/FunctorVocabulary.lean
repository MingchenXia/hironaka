/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Order.Along
public import Hironaka.Scheme.BlowUpSequence.Basic
public import Hironaka.Scheme.FiniteType
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Hironaka.Scheme.BlowUpSequence.Assignment
public import Hironaka.Scheme.Resolution.Basic
/-!
# The vocabulary of blow-up sequence functors on triples

The notions through which Kollár's functorial principalization and resolution theorems
[Kol07, Theorems 35 and 36] are proved, on top of the vocabulary of the statements (divisor
families, transforms along a succession, the functors of the main theorems). No main theorem is
stated with them.

* `MarkedTriple k`: the marked triples `(X, I, m, E)` of [Kol07, Notation 64], a triple
  `AlgebraicGeometry.Triple k` with a mark `m`; `Triple.IsOrderBlowUp`,
  `MarkedTriple.IsOrderGeBlowUp`: the smooth blow-ups of order `m`, respectively `≥ m`, of
  [Kol07, Definition 65].
* On a succession `S : BlowUpSequence X`: `IsOrderSeq`, `IsOrderGeSeq`, the smooth blow-up
  sequences of order `m`, respectively `≥ m`, starting with a triple [Kol07, Definition 66], whose
  induced ideals are the weak transforms, respectively the marked transforms.
* `OrderSeqFunctor k m Dom`, `OrderGeSeqFunctor k Dom`: smooth blow-up sequence functors of order
  `m` on a class of triples, respectively of order `≥ m` on a class of marked triples
  [Kol07, Definitions 31 and 66, Theorems 68 and 69], with the no-empty-blow-up output convention of
  [Kol07, 32] as a field, and their `endResult` (the associated resolution functor `R`). The
  functoriality properties of [Kol07, 34] as predicates on them: `IsPullbackOf` and `CommutesWith`,
  `CommutesWithSmoothSurjections`, `CommutesWithSmooth` (34.1); `IsBaseChangeOf` and
  `CommutesWithBaseChange` (34.2); `ClosedEmbedding` and
  `CommutesWithClosedEmbeddings`, `CommutesWithClosedEmbeddingsOfEmptyDivisor` (34.3, and Theorem
  35's "whenever `E = ∅`"); `WeaklyCommutesWithClosedEmbeddings` and its `E = ∅` form (34.4).
* The setting of [Kol07, Proposition 37] (gluing a functor defined on affine schemes): `IsSigmaOf`
  and `ClosedUnderSigma` (a triple is the disjoint union of a family; a class closed under finite
  disjoint unions, [Kol07, Warning 38]), `IsAffineScheme`, and for a triple the two auxiliary
  schemes of the proof, `coverScheme` (`X' = ∐ᵢ Uᵢ` over the finite affine cover `affineCover`) with
  `coverDesc` (`g : X' → X`) and `coverPair` (`X'' = X' ×_X X'`) with `coverFst`, `coverSnd`; and
  `BlowUpSequence.AgreeOnOverlaps`, the descent datum of the proof.
* The setting of [Kol07, Theorem 105] (globalization of blow-up sequence functors):
  `IsGlobalizationClass M` (a class of smooth morphisms closed under fibre products and coproducts),
  `openImmersionCoprods` (the coproducts of open immersions), `Triple.GlobalizationData M GT LT`
  (global and local triples), `CommutesWithSurjectionsIn`, and from its proof `Triple.IsLocalCover`
  and `Triple.LocalCoversFibreClosed`, the closure of the local class under the fibre products the
  proof forms.

The triples are those of the statement of Theorem 35, `AlgebraicGeometry.Triple k`
(`Hironaka.Scheme.Resolution.Defs`): an algebraic `k`-scheme `T.X` smooth of a single relative
dimension over `k`, an ideal sheaf `T.I` and a divisor family `T.E` on its underlying scheme
`T.X.left`. The notions on triples defined here live in the namespace `AlgebraicGeometry.Triple`,
so that dot notation reaches them; the instances on `T.X.left` (separated, of finite type and
smooth over `k`) are those of `Hironaka.Scheme.Resolution.Basic`.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry

noncomputable section

namespace Hironaka

open Scheme

variable {X Y : Scheme.{u}}

/-! ### Triples and marked triples (Kollár Notation 64) -/

/-- Kollár's **marked triple** `(X, I, m, E)` [Kol07, Notation 64 and its footnote] ("I consider the
pair `(I, m)` as one item, so `(X, I, m, E)` is still a triple"): a triple whose ideal carries the
mark `m ∈ ℕ`. -/
structure MarkedTriple (k : Type u) [Field k] extends AlgebraicGeometry.Triple k where
  /-- The mark `m` of the marked ideal `(I, m)`. -/
  m : ℕ

end Hironaka

namespace AlgebraicGeometry.Triple

open Hironaka Scheme

variable {k : Type u} [Field k]

/-- A **smooth blow-up of order `m`** of the triple `(X, I, E)` [Kol07, Definition 65 (1)–(2)],
given with `max-ord I = m`: a centre `Z ⊂ X` smooth over `k` [Kol07, Notation 19], having simple
normal crossings with `E` [Kol07, Definition 24 (4), `HasSncWith`], with `ord_Z I = m` (the order of
`I` at every generic point of `Z`). The hypothesis `max-ord I = m` of the definition's preamble is
carried by the statements that use it. -/
def IsOrderBlowUp (T : Triple k) (Z : T.X.left.IdealSheafData) (m : ℕ) : Prop :=
  Smooth (Z.subschemeι ≫ (T.X.left ↘ Spec (CommRingCat.of k))) ∧ T.E.HasSncWith Z ∧
    T.I.OrdAlongEq Z.support (m : ℕ∞)

end AlgebraicGeometry.Triple

namespace Hironaka

open Scheme

variable {X Y : Scheme.{u}}

namespace MarkedTriple

variable {k : Type u} [Field k]

/-- A **smooth blow-up** of the marked triple `(X, I, m, E)` [Kol07, Definition 65 (1′)–(2′)]: a
centre `Z ⊂ X` smooth over `k`, having simple normal crossings with `E`, with `ord_Z I ≥ m` at every
generic point of `Z`. -/
def IsOrderGeBlowUp (T : MarkedTriple k) (Z : T.X.left.IdealSheafData) : Prop :=
  Smooth (Z.subschemeι ≫ (T.X.left ↘ Spec (CommRingCat.of k))) ∧ T.E.HasSncWith Z ∧
    T.I.LeOrdAlong Z.support (T.m : ℕ∞)

end MarkedTriple

end Hironaka

namespace AlgebraicGeometry.Scheme.BlowUpSequence

open Scheme

open Hironaka

variable {X Y : Scheme.{u}}

/-- `S` is a **smooth blow-up sequence of order `m` starting with `(X, I, E)`**
[Kol07, Definition 66], given with `max-ord I = m`: (2) each `π_i` is a smooth blow-up (`IsSmooth`:
the centres are smooth over `k`), and for every `i`, with the induced data `I_i = weakTransformSeq`,
`E_i = totalTransformSeq` of clause (1) of the definition: (3) `Z_i` has simple normal crossings
with `E_i`, and (4) `ord_{Z_i} I_i = m`. Codimension-one and empty centres are allowed
[Kol07, Definition 66 and Warning 20]. -/
def IsOrderSeq {k : Type u} [Field k] {X : Scheme.{u}} (S : BlowUpSequence X)
    (f : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (E : DivisorFamily X) (m : ℕ) :
    Prop :=
  S.IsSmooth f ∧ ∀ i : Fin S.length,
    (S.totalTransformSeq E i.castSucc).HasSncWith (S.center i) ∧
      (S.weakTransformSeq I i.castSucc).OrdAlongEq (S.center i).support (m : ℕ∞)

/-- `S` is a **smooth blow-up sequence of order `≥ m` starting with `(X, I, m, E)`**
[Kol07, Definition 66]: (2′) each `π_i` is a smooth blow-up, and for every `i`, with the induced
marked data `(I_i, m) = markedTransformSeq`, `E_i = totalTransformSeq` of clause (1′): (3′) `Z_i`
has simple normal crossings with `E_i`, and (4′) `ord_{Z_i} I_i ≥ m`. -/
def IsOrderGeSeq {k : Type u} [Field k] {X : Scheme.{u}} (S : BlowUpSequence X)
    (f : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ) (E : DivisorFamily X) :
    Prop :=
  S.IsSmooth f ∧ ∀ i : Fin S.length,
    (S.totalTransformSeq E i.castSucc).HasSncWith (S.center i) ∧
      (S.markedTransformSeq I m i.castSucc).LeOrdAlong (S.center i).support (m : ℕ∞)

end AlgebraicGeometry.Scheme.BlowUpSequence

namespace Hironaka

open Scheme

variable {X Y : Scheme.{u}}

/-! ### Blow-up sequence functors on triples and marked triples -/

/-- A **smooth blow-up sequence functor of order `m`** on the class `Dom` of triples: Kollár's
blow-up sequence functor [Kol07, Definition 31] enriched as in the last paragraph of
[Kol07, Definition 66] (functors `B` with `B(X, I, E)` "a blow-up sequence starting with
`(X, I, E)`") and shaped as in [Kol07, Theorem 68] ("a smooth blow-up sequence functor `BO_m` of
order `m`" defined on triples with `max-ord I ≤ m`) — an assignment of a smooth blow-up sequence of
order `m` starting with `(X, I, E)` (`IsOrderSeq`, Definition 66) to every triple of the class,
"with specified centers" (the sequence carries them; "the length of the sequence `r`, the schemes
`X_i` and the centers `Z_i` all depend on `(X, I, E)`"), whose outputs contain no empty blow-ups
[Kol07, 32]. The functoriality clauses of [Kol07, 34] are separate predicates below. -/
structure OrderSeqAssignment (k : Type u) [Field k] (m : ℕ) (Dom : Triple k → Prop) where
  /-- The blow-up sequence `B(X, I, E)` assigned to a triple of the class. -/
  seq : ∀ T : Triple k, Dom T → BlowUpSequence T.X.left
  /-- `B(X, I, E)` is a smooth blow-up sequence of order `m` starting with `(X, I, E)`. -/
  isOrderSeq : ∀ T h, (seq T h).IsOrderSeq (T.X.left ↘ Spec (CommRingCat.of k)) T.I T.E m
  /-- The output contains no empty blow-ups [Kol07, 32]. -/
  noEmptyCenters : ∀ T h, (seq T h).NoEmptyCenters

/-- A **smooth blow-up sequence functor of order `≥ m`** on the class `Dom` of marked triples: the
last paragraph of [Kol07, Definition 66] ("`B(X, I, m, E)` … a blow-up sequence starting with
`(X, I, m, E)`") in the shape of [Kol07, Theorem 69] ("a smooth blow-up sequence functor `BMO_m` of
order `≥ m`" defined on marked triples `(X, I, m, E)`) — an assignment of a smooth blow-up sequence
of order `≥ m` starting with `(X, I, m, E)` (`IsOrderGeSeq`, with the triple's own mark `m`) to
every marked triple of the class, whose outputs contain no empty blow-ups [Kol07, 32]. -/
structure OrderGeSeqAssignment (k : Type u) [Field k] (Dom : MarkedTriple k → Prop) where
  /-- The blow-up sequence `B(X, I, m, E)` assigned to a marked triple of the class. -/
  seq : ∀ T : MarkedTriple k, Dom T → BlowUpSequence T.X.left
  /-- `B(X, I, m, E)` is a smooth blow-up sequence of order `≥ m` starting with `(X, I, m, E)`. -/
  isOrderGeSeq : ∀ T h, (seq T h).IsOrderGeSeq (T.X.left ↘ Spec (CommRingCat.of k)) T.I T.m T.E
  /-- The output contains no empty blow-ups [Kol07, 32]. -/
  noEmptyCenters : ∀ T h, (seq T h).NoEmptyCenters

namespace OrderSeqAssignment

variable {k : Type u} [Field k] {m : ℕ} {Dom : Triple k → Prop}

/-- [Kol07, Definition 31]: the (partial) resolution functor `R` associated to a blow-up sequence
functor `B` sends `(X, I, E)` to "the end result of the blow-up sequence",
`R : (X, I, E) ↦ (Π : X_r → X)`. -/
def endResult (B : OrderSeqAssignment k m Dom) (T : Triple k) (h : Dom T) :
    Σ Y : Scheme.{u}, Y ⟶ T.X.left :=
  ⟨(B.seq T h).last, (B.seq T h).composite⟩

end OrderSeqAssignment

namespace OrderGeSeqAssignment

variable {k : Type u} [Field k] {Dom : MarkedTriple k → Prop}

/-- [Kol07, Definition 31] for the marked version: the resolution functor associated to `B`,
`(X, I, m, E) ↦ (Π : X_r → X)`. -/
def endResult (B : OrderGeSeqAssignment k Dom) (T : MarkedTriple k) (h : Dom T) :
    Σ Y : Scheme.{u}, Y ⟶ T.X.left :=
  ⟨(B.seq T h).last, (B.seq T h).composite⟩

end OrderGeSeqAssignment

end Hironaka

/-! ### Disjoint unions of triples (Kollár Warning 38) -/

namespace AlgebraicGeometry.Triple

open Hironaka Scheme

variable {k : Type u} [Field k]

/-- [Kol07, Warning 38] ("we need to know `B` for the disconnected affine scheme `∐ᵢ Uᵢ`") with
[Kol07, Notation 64 (1)] (`X` "possibly reducible"): the triple `T` is the **disjoint union** of the
family `Ts` along the morphisms `ι i : (Ts i).X.left ⟶ T.X.left` — the cofan `(ι i)ᵢ` is a coproduct
of schemes, each `ι i` is over `Spec k`, and the data of `T` restrict along `ι i` to the data of
`Ts i`: the ideal by `comap`, the ordered divisor family componentwise (so every `Ts i` carries the
index set of `T`, as the restrictions `(Uᵢ, g^* I, g^{-1} E)` in the proof of
[Kol07, Proposition 37] do). -/
def IsSigmaOf (T : Triple k) {σ : Type u} (Ts : σ → Triple k) (ι : ∀ i, (Ts i).X.left ⟶ T.X.left) :
    Prop :=
  Nonempty (Limits.IsColimit (Limits.Cofan.mk T.X.left ι)) ∧
    (∀ i, ι i ≫ (T.X.left ↘ Spec (CommRingCat.of k)) = (Ts i).X.left ↘ Spec (CommRingCat.of k)) ∧
    (∀ i, (Ts i).I = T.I.comap (ι i)) ∧ ∀ i, (Ts i).E = T.E.comap (ι i)

/-- [Kol07, Warning 38]: the class `Dom` of triples is **closed under finite disjoint unions** — a
triple that is the disjoint union of a finite nonempty family of members of the class is a member.
(The domain of a blow-up sequence functor must contain the disconnected schemes `∐ᵢ Uᵢ`: a
resolution functor on connected schemes extends to disconnected ones automatically, "but for blow-up
sequence functors this is not at all the case".) -/
def ClosedUnderSigma (Dom : Triple k → Prop) : Prop :=
  ∀ {σ : Type u} [Finite σ] [Nonempty σ] (Ts : σ → Triple k) (T : Triple k)
    (ι : ∀ i, (Ts i).X.left ⟶ T.X.left), T.IsSigmaOf Ts ι → (∀ i, Dom (Ts i)) → Dom T

end AlgebraicGeometry.Triple

namespace Hironaka

open Scheme

variable {X Y : Scheme.{u}}

namespace MarkedTriple

variable {k : Type u} [Field k]

/-- [Kol07, Warning 38] for marked triples: `T` is the disjoint union of the family `Ts` along `ι` —
the underlying triples are (`Triple.IsSigmaOf`) and the marks agree. -/
def IsSigmaOf (T : MarkedTriple k) {σ : Type u} (Ts : σ → MarkedTriple k)
    (ι : ∀ i, (Ts i).X.left ⟶ T.X.left) : Prop :=
  T.toTriple.IsSigmaOf (fun i => (Ts i).toTriple) ι ∧ ∀ i, (Ts i).m = T.m

/-- [Kol07, Warning 38]: the class `Dom` of marked triples is closed under finite disjoint unions.
-/
def ClosedUnderSigma (Dom : MarkedTriple k → Prop) : Prop :=
  ∀ {σ : Type u} [Finite σ] [Nonempty σ] (Ts : σ → MarkedTriple k) (T : MarkedTriple k)
    (ι : ∀ i, (Ts i).X.left ⟶ T.X.left), T.IsSigmaOf Ts ι → (∀ i, Dom (Ts i)) → Dom T

end MarkedTriple

end Hironaka

/-! ### Pull-back data and Kollár's 34.1 for blow-up sequence functors -/

namespace AlgebraicGeometry.Triple

open Hironaka Scheme

variable {k : Type u} [Field k]

/-- [Kol07, 34.1] ("`B(Y, h^* I, h^{-1}(E))`"): the triple `T'` carries the **pull-back data** of
`T` along `h : T'.X.left ⟶ T.X.left` — `h` is over `Spec k`, and the ideal and the ordered divisor
family of `T'` are the inverse images of those of `T`. The pulled-back triple `Triple.pullback` of
`Hironaka.Sequence` is the canonical instance. -/
def IsPullbackOf (T' T : Triple k) (h : T'.X.left ⟶ T.X.left) : Prop :=
  h ≫ (T.X.left ↘ Spec (CommRingCat.of k)) = (T'.X.left ↘ Spec (CommRingCat.of k)) ∧
    T'.I = T.I.comap h ∧ T'.E = T.E.comap h

end AlgebraicGeometry.Triple

namespace Hironaka

open Scheme

variable {X Y : Scheme.{u}}

namespace MarkedTriple

variable {k : Type u} [Field k]

/-- [Kol07, 34.1] for marked triples (the footnote of Notation 64): `T'` carries the pull-back data
of `T` along `h` and the same mark. -/
def IsPullbackOf (T' T : MarkedTriple k) (h : T'.X.left ⟶ T.X.left) : Prop :=
  T'.toTriple.IsPullbackOf T.toTriple h ∧ T'.m = T.m

end MarkedTriple

namespace OrderSeqAssignment

variable {k : Type u} [Field k] {m : ℕ} {Dom : Triple k → Prop}

/-- [Kol07, 34.1]: a blow-up sequence functor `B` **commutes with `h`** if
"`B(Y, h^* I, h^{-1}(E)) = h^* B(X, I, E)`" — for triples `T'`, `T` of the class and
`h : T'.X.left ⟶ T.X.left`, the value on `T'` is the pull-back (`BlowUpSequence.pullback`,
[Kol07, Definition 30.1]) of the value on `T`; an equality of terms of `BlowUpSequence T'.X.left`,
hence of centres. Used with `T'.IsPullbackOf T h` and `[Smooth h]`. -/
def CommutesWith (B : OrderSeqAssignment k m Dom) {T T' : Triple k}
    (h : T'.X.left ⟶ T.X.left) : Prop :=
  ∀ (hT : Dom T) (hT' : Dom T'), B.seq T' hT' = (B.seq T hT).pullback h

/-- [Kol07, 34.1], first bullet: `B` **commutes with smooth surjections** — with every smooth
surjective `h : T'.X.left ⟶ T.X.left` between triples of the class for which `T'` carries the
pull-back data of `T`. -/
def CommutesWithSmoothSurjections (B : OrderSeqAssignment k m Dom) : Prop :=
  ∀ (T T' : Triple k) (h : T'.X.left ⟶ T.X.left) [Smooth h], Function.Surjective h →
    T'.IsPullbackOf T h → B.CommutesWith h

/-- [Kol07, 34.1], both bullets: `B` **commutes with smooth morphisms** — it commutes with every
smooth surjection, and for every smooth `h`, `B(Y, h^* I, h^{-1}(E))` is obtained from the pull-back
`h^* B(X, I, E)` "by deleting every blow-up `h^* π_i` whose center is empty" and reindexing
(`BlowUpSequence.eraseEmpty`). -/
def CommutesWithSmooth (B : OrderSeqAssignment k m Dom) : Prop :=
  B.CommutesWithSmoothSurjections ∧
    ∀ (T T' : Triple k) (h : T'.X.left ⟶ T.X.left) [Smooth h], T'.IsPullbackOf T h →
      ∀ (hT : Dom T) (hT' : Dom T'), B.seq T' hT' = ((B.seq T hT).pullback h).eraseEmpty

end OrderSeqAssignment

namespace OrderGeSeqAssignment

variable {k : Type u} [Field k] {Dom : MarkedTriple k → Prop}

/-- [Kol07, 34.1] for marked functors: `B(Y, h^* I, m, h^{-1}(E)) = h^* B(X, I, m, E)`. -/
def CommutesWith (B : OrderGeSeqAssignment k Dom) {T T' : MarkedTriple k}
    (h : T'.X.left ⟶ T.X.left) : Prop :=
  ∀ (hT : Dom T) (hT' : Dom T'), B.seq T' hT' = (B.seq T hT).pullback h

/-- [Kol07, 34.1], first bullet, for marked functors. -/
def CommutesWithSmoothSurjections (B : OrderGeSeqAssignment k Dom) : Prop :=
  ∀ (T T' : MarkedTriple k) (h : T'.X.left ⟶ T.X.left) [Smooth h], Function.Surjective h →
    T'.IsPullbackOf T h → B.CommutesWith h

/-- [Kol07, 34.1], both bullets, for marked functors. -/
def CommutesWithSmooth (B : OrderGeSeqAssignment k Dom) : Prop :=
  B.CommutesWithSmoothSurjections ∧
    ∀ (T T' : MarkedTriple k) (h : T'.X.left ⟶ T.X.left) [Smooth h], T'.IsPullbackOf T h →
      ∀ (hT : Dom T) (hT' : Dom T'), B.seq T' hT' = ((B.seq T hT).pullback h).eraseEmpty

end OrderGeSeqAssignment

end Hironaka

/-! ### Base-change data and Kollár's 34.2 for blow-up sequence functors -/

namespace AlgebraicGeometry.Triple

open Hironaka Scheme

variable {k : Type u} [Field k] {L : Type u} [Field L]

/-- [Kol07, 34.2] ("take the fiber product `X_{L,σ} := X_K ×_{Spec K} Spec L` … similarly we get
`I_{L,σ}` and `E_{L,σ}`"): the triple `T'` over `L` carries the **base-change data** of the triple
`T` over `k` along the field extension `σ : k →+* L` through `p : T'.X.left ⟶ T.X.left` — the square
of `p`, the two structure morphisms and `Spec σ` is cartesian (`T'.X.left = X_{L,σ}`), and the ideal
and the ordered divisor family of `T'` are the inverse images of those of `T`. This is the square of
the change-of-fields clause of `AlgebraicGeometry.exists_functorial_principalization`; the
base-changed triple `Triple.baseChange` of `Hironaka.Sequence` is the canonical instance. -/
def IsBaseChangeOf (T' : Triple L) (T : Triple k) (σ : k →+* L) (p : T'.X.left ⟶ T.X.left) : Prop :=
  IsPullback p (T'.X.left ↘ Spec (CommRingCat.of L)) (T.X.left ↘ Spec (CommRingCat.of k))
      (Spec.map (CommRingCat.ofHom σ)) ∧
    T'.I = T.I.comap p ∧ T'.E = T.E.comap p

end AlgebraicGeometry.Triple

namespace Hironaka

open Scheme

variable {X Y : Scheme.{u}}

namespace MarkedTriple

variable {k : Type u} [Field k] {L : Type u} [Field L]

/-- [Kol07, 34.2] for marked triples (the footnote of Notation 64): `T'` carries the base-change
data of `T` along `σ` through `p` and the same mark. -/
def IsBaseChangeOf (T' : MarkedTriple L) (T : MarkedTriple k) (σ : k →+* L)
    (p : T'.X.left ⟶ T.X.left) : Prop :=
  T'.toTriple.IsBaseChangeOf T.toTriple σ p ∧ T'.m = T.m

end MarkedTriple

namespace OrderSeqAssignment

variable {k : Type u} [Field k] {L : Type u} [Field L] {m : ℕ} {Dom : Triple k → Prop}
  {Dom' : Triple L → Prop}

/-- [Kol07, 34.2]: "we say that `B` **commutes with `σ`** if `B(X_{L,σ}, I_{L,σ}, E_{L,σ})` is the
blow-up sequence `(π_i)_{L,σ}` with centers `(Z_i)_{L,σ}`" — for the functor `B` over `k` and the
functor `B'` over `L` of the same order (a blow-up sequence functor is given for every field at once
in the main theorems): on triples `T` of `B`'s class and `T'` of `B'`'s class with `T'` carrying the
base-change data of `T` along `σ` through `p`, the value on `T'` is the pull-back of the value on
`T` along `p` (`BlowUpSequence.pullback`, [Kol07, Definition 30.1]: for the flat `p` its stages are
the fibre products `(X_i)_{L,σ}` and its centres the `(Z_i)_{L,σ}`); an equality of terms of
`BlowUpSequence T'.X.left`, hence of centres. -/
def CommutesWithBaseChange (B : OrderSeqAssignment k m Dom) (B' : OrderSeqAssignment L m Dom')
    (σ : k →+* L) : Prop :=
  ∀ (T : Triple k) (T' : Triple L) (p : T'.X.left ⟶ T.X.left), T'.IsBaseChangeOf T σ p →
    ∀ (hT : Dom T) (hT' : Dom' T'), B'.seq T' hT' = (B.seq T hT).pullback p

end OrderSeqAssignment

namespace OrderGeSeqAssignment

variable {k : Type u} [Field k] {L : Type u} [Field L] {Dom : MarkedTriple k → Prop}
  {Dom' : MarkedTriple L → Prop}

/-- [Kol07, 34.2] for marked functors: `B'(X_{L,σ}, I_{L,σ}, m, E_{L,σ}) = (B(X, I, m, E))_{L,σ}`.
-/
def CommutesWithBaseChange (B : OrderGeSeqAssignment k Dom) (B' : OrderGeSeqAssignment L Dom')
    (σ : k →+* L) : Prop :=
  ∀ (T : MarkedTriple k) (T' : MarkedTriple L) (p : T'.X.left ⟶ T.X.left), T'.IsBaseChangeOf T σ p →
    ∀ (hT : Dom T) (hT' : Dom' T'), B'.seq T' hT' = (B.seq T hT).pullback p

end OrderGeSeqAssignment

end Hironaka

namespace Hironaka

open Scheme

variable {X Y : Scheme.{u}}

end Hironaka

/-! ### Proposition 37's setting: the affine class and the two auxiliary schemes -/

namespace AlgebraicGeometry.Triple

open Hironaka Scheme

variable {k : Type u} [Field k]

/-- [Kol07, Proposition 37] ("a blow-up sequence functor defined on affine schemes over a field
`k`"): the class of triples whose underlying scheme is affine — the proposition's domain, closed
under finite disjoint unions (`closedUnderSigma_isAffine` in `Hironaka.Sequence`). -/
def IsAffineScheme (T : Triple k) : Prop := AlgebraicGeometry.IsAffine T.X.left

/-- The proof of [Kol07, Proposition 37] ("choose an open affine cover `X = ∪ Uᵢ`"): a finite affine
open cover of the underlying scheme of `T` — Mathlib's affine cover, refined to a finite subcover
(`T.X.left` is quasi-compact over `Spec k`). -/
noncomputable def affineCover (T : Triple k) : Scheme.OpenCover.{u} T.X.left :=
  have : CompactSpace T.X.left :=
    QuasiCompact.compactSpace_of_compactSpace (T.X.left ↘ Spec (CommRingCat.of k))
  T.X.left.affineCover.finiteSubcover

/-- The proof of [Kol07, Proposition 37]: `X' := ∐ᵢ Uᵢ`, the disjoint union of the members of the
finite affine cover. -/
noncomputable abbrev coverScheme (T : Triple k) : Scheme.{u} := ∐ fun i => T.affineCover.X i

/-- The proof of [Kol07, Proposition 37] ("a smooth surjection `g : X' → X`"): the morphism induced
by the inclusions of the members of the cover. -/
noncomputable def coverDesc (T : Triple k) : T.coverScheme ⟶ T.X.left :=
  Limits.Sigma.desc T.affineCover.f

/-- `X'` is a scheme over `Spec k` through `g`. -/
noncomputable instance instOverCoverScheme (T : Triple k) :
    T.coverScheme.Over (Spec (CommRingCat.of k)) :=
  ⟨T.coverDesc ≫ (T.X.left ↘ Spec (CommRingCat.of k))⟩

/-- `g : X' → X` is a morphism over `Spec k`. -/
instance instIsOverCoverDesc (T : Triple k) : T.coverDesc.IsOver (Spec (CommRingCat.of k)) := ⟨rfl⟩

/-- The `X'' := ∐_{i ≤ j} Uᵢ ∩ Uⱼ` of the proof of [Kol07, Proposition 37], which one may "also
think of … as the fiber product `X' ×_X X'`": the fibre product `X' ×_X X'`. -/
noncomputable abbrev coverPair (T : Triple k) : Scheme.{u} :=
  Limits.pullback T.coverDesc T.coverDesc

/-- The proof of [Kol07, Proposition 37]: the first projection `τ₁ : X'' → X'`. -/
noncomputable def coverFst (T : Triple k) : T.coverPair ⟶ T.coverScheme :=
  Limits.pullback.fst T.coverDesc T.coverDesc

/-- The proof of [Kol07, Proposition 37]: the second projection `τ₂ : X'' → X'`. -/
noncomputable def coverSnd (T : Triple k) : T.coverPair ⟶ T.coverScheme :=
  Limits.pullback.snd T.coverDesc T.coverDesc

/-- `X''` is a scheme over `Spec k` through `τ₁`. -/
noncomputable instance instOverCoverPair (T : Triple k) :
    T.coverPair.Over (Spec (CommRingCat.of k)) :=
  ⟨T.coverFst ≫ (T.coverScheme ↘ Spec (CommRingCat.of k))⟩

/-- `τ₁` is over `Spec k`. -/
instance instIsOverCoverFst (T : Triple k) : T.coverFst.IsOver (Spec (CommRingCat.of k)) := ⟨rfl⟩

/-- `τ₂` is over `Spec k`: `τ₁ ≫ g = τ₂ ≫ g` (the fibre-product square). -/
instance instIsOverCoverSnd (T : Triple k) : T.coverSnd.IsOver (Spec (CommRingCat.of k)) :=
  ⟨by
    have h : T.coverFst ≫ T.coverDesc = T.coverSnd ≫ T.coverDesc := Limits.pullback.condition
    change T.coverSnd ≫ T.coverDesc ≫ (T.X.left ↘ Spec (CommRingCat.of k)) =
      T.coverFst ≫ T.coverDesc ≫ (T.X.left ↘ Spec (CommRingCat.of k))
    rw [← Category.assoc, ← Category.assoc, h]⟩

end AlgebraicGeometry.Triple

namespace Hironaka

open Scheme

variable {X Y : Scheme.{u}}

namespace MarkedTriple

variable {k : Type u} [Field k]

/-- [Kol07, Proposition 37] for marked triples: the class with affine underlying scheme. -/
def IsAffineScheme (T : MarkedTriple k) : Prop := AlgebraicGeometry.IsAffine T.X.left

end MarkedTriple

end Hironaka

/-! ### Closed-embedding situations and Kollár's 34.3 for blow-up sequence functors -/

namespace AlgebraicGeometry.Triple

open Hironaka Scheme

variable {k : Type u} [Field k]

/-- The **closed-embedding situation** `(Y, I_Y, E|_Y) ↪ (X, I_X, E)` along `j : Y ↪ X` of
[Kol07, 34.3] — `j` is a closed embedding of smooth `k`-schemes (the closed immersion is an instance
argument `[IsClosedImmersion j]` at the use sites, as `[Smooth h]` in 34.1; smoothness and `0 ≠ I`
are the triples' fields; `j` is a `k`-morphism), the ideal sheaves satisfy
`𝒪_X / I_X = j_*(𝒪_Y / I_Y)` — `I_X = j_* I_Y`, Mathlib's `IdealSheafData.map` along `j`, the form
of clause (5) of `AlgebraicGeometry.exists_functorial_principalization` — and `E` is an snc divisor
on `X` with `E|_Y` snc on `Y`: the family of `T_Y` is the restriction `E.comap j` of that of `T_X`,
its snc-ness being `T_Y.isSnc`. -/
def ClosedEmbedding (TX TY : Triple k) (j : TY.X.left ⟶ TX.X.left) : Prop :=
  j ≫ (TX.X.left ↘ Spec (CommRingCat.of k)) = (TY.X.left ↘ Spec (CommRingCat.of k)) ∧
    TX.I = TY.I.map j ∧ TY.E = TX.E.comap j

end AlgebraicGeometry.Triple

namespace Hironaka

open Scheme

variable {X Y : Scheme.{u}}

namespace MarkedTriple

variable {k : Type u} [Field k]

/-- [Kol07, 34.3] for marked triples ([Kol07, Claim 71.2]:
`BMO_1(X, I, 1, ∅) = τ_* BMO_1(Y, J, 1, ∅)`): the closed-embedding situation with the same mark. -/
def ClosedEmbedding (TX TY : MarkedTriple k) (j : TY.X.left ⟶ TX.X.left) : Prop :=
  TX.toTriple.ClosedEmbedding TY.toTriple j ∧ TY.m = TX.m

end MarkedTriple

namespace OrderSeqAssignment

variable {k : Type u} [Field k] {m : ℕ} {Dom : Triple k → Prop}

/-- [Kol07, 34.3]: "we say that `B` **commutes with closed embeddings** if
`B(X, I_X, E) = j_* B(Y, I_Y, E|_Y)`" in every closed-embedding situation between triples of the
class — the value on `T_X` is the push-forward (`BlowUpSequence.pushforward`,
[Kol07, Definition 30.3]) of the value on `T_Y`; an equality of terms of
`BlowUpSequence T_X.X.left`, hence of centres. -/
def CommutesWithClosedEmbeddings (B : OrderSeqAssignment k m Dom) : Prop :=
  ∀ (TX TY : Triple k) (j : TY.X.left ⟶ TX.X.left) [IsClosedImmersion j],
    Triple.ClosedEmbedding TX TY j →
    ∀ (hX : Dom TX) (hY : Dom TY), B.seq TX hX = (B.seq TY hY).pushforward j

/-- [Kol07, Theorem 35 (5)] and [Kol07, Claim 71.2] ("in both of these claims we assume that
`E = ∅`"): `B` **commutes with closed embeddings whenever `E = ∅`** — 34.3's clause restricted to
the situations whose divisor family on `X` (hence on `Y`) is empty; the form of clause (5) of
`AlgebraicGeometry.exists_functorial_principalization` (`IsEmpty E.ι`). -/
def CommutesWithClosedEmbeddingsOfEmptyDivisor (B : OrderSeqAssignment k m Dom) : Prop :=
  ∀ (TX TY : Triple k) (j : TY.X.left ⟶ TX.X.left) [IsClosedImmersion j],
    Triple.ClosedEmbedding TX TY j →
    IsEmpty TX.E.ι → ∀ (hX : Dom TX) (hY : Dom TY), B.seq TX hX = (B.seq TY hY).pushforward j

end OrderSeqAssignment

namespace OrderGeSeqAssignment

variable {k : Type u} [Field k] {Dom : MarkedTriple k → Prop}

/-- [Kol07, 34.3] for marked functors ([Kol07, Claim 71.2]): `B` commutes with closed embeddings,
`B(X, I_X, m, E) = j_* B(Y, I_Y, m, E|_Y)`. -/
def CommutesWithClosedEmbeddings (B : OrderGeSeqAssignment k Dom) : Prop :=
  ∀ (TX TY : MarkedTriple k) (j : TY.X.left ⟶ TX.X.left) [IsClosedImmersion j],
    MarkedTriple.ClosedEmbedding TX TY j →
      ∀ (hX : Dom TX) (hY : Dom TY), B.seq TX hX = (B.seq TY hY).pushforward j

/-- [Kol07, Claim 71.2] for marked functors: `B` commutes with closed embeddings whenever `E = ∅`.
-/
def CommutesWithClosedEmbeddingsOfEmptyDivisor (B : OrderGeSeqAssignment k Dom) : Prop :=
  ∀ (TX TY : MarkedTriple k) (j : TY.X.left ⟶ TX.X.left) [IsClosedImmersion j],
    MarkedTriple.ClosedEmbedding TX TY j → IsEmpty TX.E.ι →
      ∀ (hX : Dom TX) (hY : Dom TY), B.seq TX hX = (B.seq TY hY).pushforward j

end OrderGeSeqAssignment

/-! ### Theorem 105's hypotheses: a class of morphisms, global and local triples -/

/-- [Kol07, Theorem 105 (1)]: "a class of smooth morphisms `M`" closed under fibre products and
coproducts (for instance all smooth morphisms, all étale morphisms or all open immersions) — a
property `M` of morphisms of schemes (Mathlib's `MorphismProperty`) whose members are smooth, which
is stable under base change ("closed under fiber products" as the proof uses it: "the two coordinate
projections `τ₁, τ₂ : X'' → X'` are in `M`") and which is closed under coproducts (as the proof uses
it: for members `gᵢ : Uᵢ → X`, "let `X' := ∐ᵢ Uₓᵢ` be the disjoint union and `g : X' → X` the
induced `M`-morphism"). Kollár's third example is read as the class of coproducts of open immersions
(`openImmersionCoprods`): the open immersions themselves are not closed under coproducts
(`not_isGlobalizationClass_isOpenImmersion` in `Hironaka.Sequence`). -/
structure IsGlobalizationClass (M : MorphismProperty Scheme.{u}) : Prop where
  /-- Every member of `M` is smooth. -/
  smooth : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), M f → Smooth f
  /-- `M` is closed under fibre products: stable under base change. -/
  isStableUnderBaseChange : M.IsStableUnderBaseChange
  /-- `M` is closed under coproducts: the morphism a coproduct of members induces is a member. -/
  sigmaDesc : ∀ {σ : Type u} {U : σ → Scheme.{u}} {X : Scheme.{u}} (g : ∀ i, U i ⟶ X),
    (∀ i, M (g i)) → M (Limits.Sigma.desc g)

/-- [Kol07, Theorem 105 (1)] ("all open immersions") read as its proof and Step 3 of the proof of
[Kol07, Theorem 103] use it ("let `g : X* → X` be the coproduct of the injections `X^(j) ↪ X`"; "if
`M = {open immersions}` … this is the only case we need for the proof of (103)"): `f : Y ⟶ X` is a
**coproduct of open immersions** — `Y` is a coproduct of schemes `Uᵢ` (a cofan `ιᵢ : Uᵢ ⟶ Y` that is
a colimit, as in `Triple.IsSigmaOf`) and every `ιᵢ ≫ f : Uᵢ ⟶ X` is an open immersion. -/
def _root_.AlgebraicGeometry.openImmersionCoprods : MorphismProperty Scheme.{u} := fun Y _ f =>
  ∃ (σ : Type u) (U : σ → Scheme.{u}) (ι : ∀ i, U i ⟶ Y),
    Nonempty (Limits.IsColimit (Limits.Cofan.mk Y ι)) ∧ ∀ i, IsOpenImmersion (ι i ≫ f)

end Hironaka

namespace AlgebraicGeometry.Triple

open Hironaka Scheme

variable {k : Type u} [Field k]

/-- [Kol07, Theorem 105 (2)]: "two classes of triples `GT` (global triples) and `LT` (local
triples)" such that (i) for every `(X, I, E) ∈ GT` and `x ∈ X` some `M`-morphism
`gₓ : (x' ∈ Uₓ) → (x ∈ X)` has `(Uₓ, g^* I, g^{-1} E)` in `LT`, and (ii) `LT` is closed under
disjoint unions — for a class `M` of morphisms and two classes `GT`, `LT` of triples: (i) every
point of a global triple lies in the image of an `M`-morphism from a local triple carrying the
pull-back data (`IsPullbackOf`; `(Uₓ, g^* I, g^{-1} E)` is a triple in the sense of Notation 64
because it is in `LT`); (ii) `LT` is closed under finite disjoint unions (`ClosedUnderSigma`,
[Kol07, Warning 38]). No inclusion `LT ⊆ GT` is assumed (Kollár states none); Theorem 105's
"extension" is agreement on `LT ∩ GT`. -/
structure GlobalizationData (M : MorphismProperty Scheme.{u}) (GT LT : Triple k → Prop) :
    Prop where
  /-- (i): every point of a global triple has a local triple over it along a member of `M`. -/
  exists_isPullbackOf : ∀ T : Triple k, GT T → ∀ x : T.X.left,
    ∃ (T' : Triple k) (g : T'.X.left ⟶ T.X.left),
      M g ∧ x ∈ Set.range g ∧ T'.IsPullbackOf T g ∧ LT T'
  /-- (ii): `LT` is closed under finite disjoint unions. -/
  closedUnderSigma : ClosedUnderSigma LT

end AlgebraicGeometry.Triple

namespace Hironaka

open Scheme

variable {X Y : Scheme.{u}}

namespace OrderSeqAssignment

variable {k : Type u} [Field k] {m : ℕ} {Dom : Triple k → Prop}

/-- [Kol07, Theorem 105 (3)]: "a blow-up sequence functor `B` defined on `LT` that commutes with
surjections in `M`" — `B.CommutesWith h` (the equation `B(Y, h^* I, h^{-1}(E)) = h^* B(X, I, E)` of
34.1) for every surjective `h : T'.X.left ⟶ T.X.left` in `M` between triples of which `T'` carries
the pull-back data of `T`; for `M` = all smooth morphisms this is `CommutesWithSmoothSurjections`.
The same predicate on `GT` is the conclusion's clause for the extension `B̄`. -/
def CommutesWithSurjectionsIn (B : OrderSeqAssignment k m Dom) (M : MorphismProperty Scheme.{u}) :
    Prop :=
  ∀ (T T' : Triple k) (h : T'.X.left ⟶ T.X.left), M h → Function.Surjective h →
    T'.IsPullbackOf T h → B.CommutesWith h

end OrderSeqAssignment

namespace OrderGeSeqAssignment

variable {k : Type u} [Field k] {Dom : MarkedTriple k → Prop}

/-- [Kol07, Theorem 105 (3)] for marked functors: `B` commutes with every surjection in `M` between
marked triples of which the source carries the pull-back data of the target. -/
def CommutesWithSurjectionsIn (B : OrderGeSeqAssignment k Dom) (M : MorphismProperty Scheme.{u}) :
    Prop :=
  ∀ (T T' : MarkedTriple k) (h : T'.X.left ⟶ T.X.left), M h → Function.Surjective h →
    T'.IsPullbackOf T h → B.CommutesWith h

end OrderGeSeqAssignment

/-! ### Kollár's 34.4: closed embeddings, weak form -/

namespace OrderSeqAssignment

variable {k : Type u} [Field k] {m : ℕ} {Dom : Triple k → Prop}

/-- [Kol07, 34.4], in the setting of (34.3): `B` **weakly commutes with closed embeddings** if
"`j^* B(X, I_X, E) = B(Y, I_Y, E|_Y)`" — in every closed-embedding situation between triples of the
class (`Triple.ClosedEmbedding`), the restriction to `Y` of the value on `T_X` — Kollár's `j^*` of
[Kol07, Definition 30.2], here `BlowUpSequence.pullback` along the closed immersion `j` — is the
value on `T_Y`; an equality of terms of `BlowUpSequence T_Y.X.left`, hence of centres. -/
def WeaklyCommutesWithClosedEmbeddings (B : OrderSeqAssignment k m Dom) : Prop :=
  ∀ (TX TY : Triple k) (j : TY.X.left ⟶ TX.X.left) [IsClosedImmersion j],
    Triple.ClosedEmbedding TX TY j →
    ∀ (hX : Dom TX) (hY : Dom TY), (B.seq TX hX).pullback j = B.seq TY hY

/-- [Kol07, 34.4] restricted to the situations with `E = ∅` — the weak counterpart of
[Kol07, Theorem 35 (5)] and the form in which the proof of Theorem 36 uses the clause ("Using that
`BP` weakly commutes with closed embeddings (34.4)", for `BP(A, I_X, ∅)`). -/
def WeaklyCommutesWithClosedEmbeddingsOfEmptyDivisor (B : OrderSeqAssignment k m Dom) : Prop :=
  ∀ (TX TY : Triple k) (j : TY.X.left ⟶ TX.X.left) [IsClosedImmersion j],
    Triple.ClosedEmbedding TX TY j →
    IsEmpty TX.E.ι → ∀ (hX : Dom TX) (hY : Dom TY), (B.seq TX hX).pullback j = B.seq TY hY

end OrderSeqAssignment

namespace OrderGeSeqAssignment

variable {k : Type u} [Field k] {Dom : MarkedTriple k → Prop}

/-- [Kol07, 34.4] for marked functors (the notation of [Kol07, Claim 71.2], with the mark carried
along): `B` weakly commutes with closed embeddings, `j^* B(X, I_X, m, E) = B(Y, I_Y, m, E|_Y)`. -/
def WeaklyCommutesWithClosedEmbeddings (B : OrderGeSeqAssignment k Dom) : Prop :=
  ∀ (TX TY : MarkedTriple k) (j : TY.X.left ⟶ TX.X.left) [IsClosedImmersion j],
    MarkedTriple.ClosedEmbedding TX TY j →
      ∀ (hX : Dom TX) (hY : Dom TY), (B.seq TX hX).pullback j = B.seq TY hY

/-- [Kol07, 34.4] for marked functors, restricted to `E = ∅` (the standing assumption of
[Kol07, Claim 71.2]). -/
def WeaklyCommutesWithClosedEmbeddingsOfEmptyDivisor (B : OrderGeSeqAssignment k Dom) : Prop :=
  ∀ (TX TY : MarkedTriple k) (j : TY.X.left ⟶ TX.X.left) [IsClosedImmersion j],
    MarkedTriple.ClosedEmbedding TX TY j → IsEmpty TX.E.ι →
      ∀ (hX : Dom TX) (hY : Dom TY), (B.seq TX hX).pullback j = B.seq TY hY

end OrderGeSeqAssignment

end Hironaka

namespace AlgebraicGeometry.Scheme.BlowUpSequence

open Scheme

open Hironaka

variable {X Y : Scheme.{u}}

/-! ### The descent datum of Proposition 37's proof -/

/-- The proof of [Kol07, Proposition 37], equations (37.1)–(37.2), for whole sequences: given a
family of morphisms `ι i : W i ⟶ X` (in the proof, the members of an affine open cover), a family of
blow-up sequences `S i` on the `W i` **agree on the overlaps** when the pull-backs of `S i` and
`S j` to the fibre product `W i ×_X W j` agree, for all `i, j` — the descent datum from which the
proof reconstructs a sequence on `X`. -/
def AgreeOnOverlaps {X : Scheme.{u}} {σ : Type u} {W : σ → Scheme.{u}} (ι : ∀ i, W i ⟶ X)
    (S : ∀ i, BlowUpSequence (W i)) : Prop :=
  ∀ i j, (S i).pullback (Limits.pullback.fst (ι i) (ι j)) =
    (S j).pullback (Limits.pullback.snd (ι i) (ι j))

end AlgebraicGeometry.Scheme.BlowUpSequence

namespace Hironaka

open Scheme

variable {X Y : Scheme.{u}}

end Hironaka

/-! ### Theorem 105's proof: local covers and the fibre-product hypothesis -/

namespace AlgebraicGeometry.Triple

open Hironaka Scheme

variable {k : Type u} [Field k]

/-- The proof of [Kol07, Theorem 105] chooses `M`-morphisms `gₓᵢ : Uₓᵢ → X` whose images cover `X`
and forms the disjoint union `X' := ∐ᵢ Uₓᵢ` with "the induced `M`-morphism" `g : X' → X`, so that
`(X', g^* I, g^{-1} E) ∈ LT`: `g : T'.X.left ⟶ T.X.left` is a **local `M`-cover** of the global
triple `T` by the local triple `T'` — `T ∈ GT`, `T' ∈ LT`, `g ∈ M`, `g` surjective, and `T'` carries
the pull-back data of `T` along `g` (`IsPullbackOf`). -/
def IsLocalCover (M : MorphismProperty Scheme.{u}) (GT LT : Triple k → Prop) (T T' : Triple k)
    (g : T'.X.left ⟶ T.X.left) : Prop :=
  GT T ∧ LT T' ∧ M g ∧ Function.Surjective g ∧ T'.IsPullbackOf T g

/-- A hypothesis implicit in the proof of [Kol07, Theorem 105]: Kollár applies `B` to
`X'' := X' ×_X X'` ("the blow-up sequence `B` for `X''` starts with blowing up `Z₀''`; since `B`
commutes with the `τᵢ` …"), which requires `(X'', τ₁^* g^* I, …) ∈ LT` although clauses (1)–(3) of
the theorem state no such condition; the commutation and the uniqueness of the extension use
`Y' ×_X X'` for local covers `Y' → Y → X` and `X' → X` in the same way. The class `LT` is **closed
under fibre products of local covers**: for two local `M`-covers `g₁ : T₁.X.left ⟶ T.X.left`,
`g₂ : T₂.X.left ⟶ T.X.left` of a global triple `T`, a triple `T₁₂` whose scheme is the fibre product
`T₁.X.left ×_{T.X.left} T₂.X.left` (`IsPullback p₁ p₂ g₁ g₂`) and which carries the pull-back data
of `T₁` along `p₁` is in `LT`. This is closure of `LT` under base change along the `M`-morphism `g₁`
restricted to local covers over a common global triple; the unrestricted closure ("`LT` closed under
base change along every `M`-morphism") fails for the affine class of Proposition 37 (an open
subscheme of an affine scheme need not be affine, and every open immersion is a coproduct of open
immersions), while this form holds in both instances used in the library (affine: `X` is separated,
so the fibre product of affines over it is affine; maximal contact: the hypersurface restricts). -/
def LocalCoversFibreClosed (M : MorphismProperty Scheme.{u}) (GT LT : Triple k → Prop) : Prop :=
  ∀ {T T₁ T₂ : Triple k} {g₁ : T₁.X.left ⟶ T.X.left} {g₂ : T₂.X.left ⟶ T.X.left},
    IsLocalCover M GT LT T T₁ g₁ → IsLocalCover M GT LT T T₂ g₂ →
    ∀ {T₁₂ : Triple k} {p₁ : T₁₂.X.left ⟶ T₁.X.left} {p₂ : T₁₂.X.left ⟶ T₂.X.left},
      IsPullback p₁ p₂ g₁ g₂ → T₁₂.IsPullbackOf T₁ p₁ → LT T₁₂

end AlgebraicGeometry.Triple


end
