/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Snc.EraseFamily
public import Hironaka.Resolution.Algebraic.Balanced.Basic
public import Hironaka.Resolution.Algebraic.BoundaryClearing.Data
import Hironaka.Resolution.Algebraic.BoundaryClearing.Center
import Hironaka.Resolution.Algebraic.BoundaryClearing.Transform
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.Center
import Hironaka.Resolution.Algebraic.MaximalContact.Transform
import Hironaka.Resolution.Algebraic.Snc.SncInvertible
import Hironaka.Scheme.BlowUp.BlowUpMap
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Hironaka.Scheme.BlowUpSequence.OrderAlongCenter
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.RestrictDivisors
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Snc.RelativeDimension
import Hironaka.Scheme.Snc.RestrictHypersurface
import Hironaka.Scheme.Snc.TotalTransformSmoothBlowUp
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The restriction to `S = E^j`: the restricted marked triple and the output sequence

The proof of [Kol07, Lemma 102] continues on `S := E^j`, with injection `τ : S ↪ X` and
`E_S := (E − E^j)|_S`: by the going-up theorem [Kol07, Theorem 84], the blow-up sequences of order
`≥ m` starting with the marked triple `(S, I_0|_S, m, E_S)` correspond to the blow-up sequences of
order `m` starting with `(X_0, I_0, E − E^j)`, and Kollár sets
`BD_{n,m,j}(X, I, E) := τ_* BMO_{n−1,m}(S, I_0|_S, m, E_S) ∘ π_{-1}`: the output of order reduction
for marked ideals in dimension `n − 1`, pushed forward along `τ` ([Kol07, 30.3]) and composed on
the right with the first blow-up `π_{-1}`.

This module defines the restricted marked triple and the output sequence, and proves exactly what
the definitions need: the four obligations of a marked triple (smooth, equidimensional, ideal
nonzero on every component, family snc) with their supporting lemmas, and the dimension bound that
`rawSeq` needs to apply the inductive functor. The remaining properties are proved in
`Composite.lean` and `Output.lean`.

* Kollár's `E − E^j` is `DivisorFamily.erase E j` (`Hironaka/Scheme/Snc/EraseFamily.lean`).
* `BD.centerS T m j`: `Z_{-1}` viewed on `S = E^j`, the pull-back `Z_{-1}.comap S.subschemeι`;
  since `Z_{-1} ⊆ S`, it is `Z_{-1}` itself (its push-forward back to `X` is `Z_{-1}`), and as an
  ideal on `S` it is locally the zero ideal (on the components of `S` inside `cosupp(I, m)`) or the
  unit ideal.
* `BD.restrictedTriple T m j hI hmax`: the marked triple `(S, I_0|_S, m, E_S)`. **Where it
  lives.** Kollár's `S` is `E^j` on `X_0`, i.e. the birational transform of `E^j` under the trivial
  blow-up `π_{-1}`, which drops the components inside `Z_{-1}`. Here this is the first stage of the
  blow-up sequence ON `S` whose first center is `Z_{-1}|_S`: `X_S := blowUp S (Z_{-1}|_S)`
  (= `S` minus those components), and the marked triple is the one induced after that step (the
  last paragraph of [Kol07, Definition 66]): `I_S` is the marked transform of `I|_S` with control
  `m` (= `I_0|_S`; the degenerate analogue of [Kol07, Lemma 62], see `markedTransform_centerS_eq`),
  `E_S` the total transform of `(E − E^j)|_S`
  (= `(E_0 − E^j)|_S` member by member, plus the exceptional member of `Z_{-1}|_S`, which is empty
  on `X_S`; the total-transform convention of this library, as for `X_0`). The closed immersion
  `τ : X_S ⟶ X_0 = blowUp X Z_{-1}` is `blowUpMap S.subschemeι Z_{-1}`
  (`Hironaka/Scheme/BlowUp/BlowUpMap.lean`), with kernel the birational transform of `E^j`.
  **Why on the `S`-side.** Kollár applies the going-up theorem to `(X_0, I_0, E − E^j)`; Theorem 84
  as printed needs the ideal D-balanced, and `I_0` is not known to be. Kollár's own reading is the
  Warning in [Kol07, 104]: the consequences of Theorem 84 hold for any sequence of blow-ups of
  order `m` starting from the D-balanced `I`, here the COMPOSITE sequence on `S` starting with
  `(S, I|_S, m, E_S)`, first center `Z_{-1}|_S`, then the `BMO` output. That is the going-up
  statement of `Hironaka/Resolution/Algebraic/Kol07/GoingUp.lean`; the marked triple is the induced
  one after the first step because `(S, I|_S, m, (E − E^j)|_S)` itself is not a marked triple
  (`I|_S` vanishes on the components of `S` inside `cosupp(I, m)`). Its fields are proof
  obligations, discharged here: `X_S` is smooth over `k` of relative dimension `n' − 1` when `X` has
  relative dimension `n'` (through `τ`: the birational transform of `E^j` is a smooth divisor of
  `X_0`, and `τ` is an isomorphism onto it), `I_S` is nonzero on every component (`Transform.lean`
  through `markedTransform_centerS_eq` and
  `τ`), `E_S` is snc (restriction of the snc family `E − E^j + E^j` to `E^j`, then the total
  transform of a family having snc with the center). The triple is `restrictedTripleD` (and the
  output below `rawSeqD`) at `D = E^j`, `F = E − E^j`: the same constructions for an arbitrary
  member `D` and family `F` satisfying `RestrictedHyps`, which `Indifference.lean` varies.
* `BD.tailSeq T m j hI hmax hn B hDom`: Kollár's `τ_* BMO_{n−1,m}(S, I_0|_S, m, E_S)`, the
  push-forward along `τ` of `B`'s sequence on the restricted marked triple (a sequence on `X_0`).
* `BD.rawSeq T m j hI hmax hn B hDom`: the output before the deletion of empty blow-ups
  ([Kol07, 32]): the composite sequence on `S` (first center `Z_{-1}|_S`, then
  `B(S, I_0|_S, m, E_S)` for the given marked functor `B` of the shape of [Kol07, Theorem 69] in
  dimensions `≤ n − 1`) pushed forward to `X` along `S ↪ X` ([Kol07, 30.3]). Its first blow-up is
  the blow-up of `X` along `(Z_{-1}|_S).map ι = Z_{-1}`, i.e. `π_{-1}`, and its tail is `τ_* B(…)`;
  the functor `BD_{n,m,j}` is this with the empty blow-ups deleted
  (`OrderSeqAssignment.ofEraseEmpty`, `Hironaka/Scheme/BlowUpSequence/Functor.lean`), defined in
  `Output.lean` once `Composite.lean` gives its order condition.
* `BD.Domain n m j`: Lemma 102's standing assumptions after its first paragraph ("from now on we
  assume that `I` is D-balanced"): `dim X ≤ n`, `I` D-balanced, `max-ord I = m`, and a `j`-th
  member of `E` (positions as in `BDClass`). The extension to `BDClass` by tuning (`Tuned.lean`)
  and by the convention of [Kol07, Theorem 68] for `max-ord I < m` (the sequence is empty) is
  `Assembly.lean`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme.IdealSheafData
  Hironaka Scheme Scheme.Hom BlowUpSequence Hironaka.Sequence

namespace Hironaka.BD

variable {k : Type u} [Field k]

/-- `E` has simple normal crossings with its member `E^j` ([Kol07, Definition 24, (4)]). -/
theorem hasSncWith_component_self (T : Triple k) (j : T.E.ι) :
    T.E.HasSncWith (T.E.component j) :=
  DivisorFamily.hasSncWith_component T.E T.isSnc.2 j

section Component

variable [CharZero k] (T : Triple k) (j : T.E.ι)

/-- `E^j` is smooth over `k` ("each `E^i` is smooth", [Kol07, Definition 24]). -/
theorem smooth_component :
    Smooth ((T.E.component j).subschemeι ≫ (T.X.left ↘ Spec (.of k))) :=
  smooth_of_hasSncWith (T.X.left ↘ Spec (.of k)) (hasSncWith_component_self T j)

omit [CharZero k] in
/-- `E^j` is a smooth divisor ([Kol07, Definition 24, (1)–(2)]): regular, and locally
`(z_{c(j)} = 0)` for a member of a regular system of parameters. The case `F = T.E` of
`Hironaka.Snc.isSmoothDivisor_component_of_isSnc`
(`Hironaka/Resolution/Algebraic/Snc/SncInvertible.lean`). -/
theorem isSmoothDivisor_component : IsSmoothDivisor (T.E.component j) :=
  Hironaka.Snc.isSmoothDivisor_component_of_isSnc (T.X.left ↘ Spec (.of k)) T.isSnc j

/-- The restriction of `E − E^j` to `E^j` is snc (Kollár's `E_S := (E − E^j)|_S` in the proof of
[Kol07, Lemma 102]; the last sentence of [Kol07, Definition 24]): the snc coordinates of `E` at a
point of `E^j` restrict to snc coordinates of the other members (the restriction lemma applied with
`Z := E^j` itself), and each restricted member is regular, being a smooth center of the restricted
family. -/
theorem isSnc_restrictedFamily :
    ((T.E.erase j).comap (T.E.component j).subschemeι).IsSnc := by
  set ι := (T.E.component j).subschemeι with hιdef
  have hreg : ∀ x : T.X.left, IsRegularLocalRing (T.X.left.presheaf.stalk x) := fun x =>
    isRegularLocalRing_stalk (T.X.left ↘ Spec (.of k)) x
  have hE' : ((T.E.erase j).append ι.ker).IsSnc := by
    rw [hιdef, Scheme.IdealSheafData.ker_subschemeι]
    exact DivisorFamily.isSnc_erase_append T.E j T.isSnc
  have hZ : ((T.E.erase j).append ι.ker).HasSncWith ι.ker :=
    DivisorFamily.hasSncWith_component _ hE'.2 (toLex (Sum.inr PUnit.unit))
  have h := hasSncWith_comap_of_isClosedImmersion ι hreg hZ le_rfl
  rw [hιdef, Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.comap_subschemeι_eq_bot]
    at h
  have hat : ∀ y, ∃ (n : ℕ) (z : Fin n → _),
      ((T.E.erase j).comap (T.E.component j).subschemeι).IsSncAt y z := fun y => by
    obtain ⟨n, z, hz, -⟩ := h y (by rw [Scheme.IdealSheafData.support_bot]; trivial)
    exact ⟨n, z, hz⟩
  refine ⟨fun i => ?_, hat⟩
  have := smooth_component T j
  exact isRegular_subscheme_of_hasSncWith ((T.E.component j).subschemeι ≫ (T.X.left ↘ Spec (.of k)))
    (DivisorFamily.hasSncWith_component _ hat i)

end Component

/-- The center `Z_{-1}` viewed on Kollár's `S = E^j` (the proof of [Kol07, Lemma 102]): its
pull-back along `S ↪ X`. Since `Z_{-1} ⊆ E^j`, pushing it forward returns `Z_{-1}`
(`map_centerS`, `Composite.lean`). -/
noncomputable def centerS (T : Triple k) (m : ℕ) (j : T.E.ι) :
    (T.E.component j).subscheme.IdealSheafData :=
  (Zminus1 T.I m (T.E.component j)).comap (T.E.component j).subschemeι

section CenterS

variable [CharZero k] (T : Triple k) (m : ℕ) (j : T.E.ι)

omit [CharZero k] in
/-- On `S`, the ideal `Z_{-1}|_S` is locally the zero ideal: at a point of `Z_{-1}` the stalk of
`Z_{-1}` is the stalk of `E^j` (`Center.lean`), whose image in the stalk of `S` is zero. -/
theorem stalkIdeal_centerS_eq_bot {y : (T.E.component j).subscheme}
    (hy : y ∈ (centerS T m j).support) : (centerS T m j).stalkIdeal y = ⊥ := by
  have hx : (T.E.component j).subschemeι y ∈ (Zminus1 T.I m (T.E.component j)).support :=
    (mem_support_comap_iff_apply _ _ y).mp hy
  have hk := ker_stalkMap_of_isClosedImmersion (T.E.component j).subschemeι y
  rw [Scheme.IdealSheafData.ker_subschemeι] at hk
  change ((Zminus1 T.I m (T.E.component j)).comap (T.E.component j).subschemeι).stalkIdeal y = ⊥
  rw [stalkIdeal_comap, stalkIdeal_Zminus1_eq T m j hx, ← hk]
  exact le_bot_iff.mp (Ideal.map_le_iff_le_comap.mpr (RingHom.ker_eq_comap_bot _).le)

/-- `Z_{-1}|_S` has simple normal crossings with `E_S = (E − E^j)|_S` ([Kol07, Definition 65];
[Kol07, Definition 24, (4)]): its stalks are zero where it lives (the empty set of coordinates). -/
theorem hasSncWith_centerS :
    ((T.E.erase j).comap (T.E.component j).subschemeι).HasSncWith (centerS T m j) := by
  intro y hy
  obtain ⟨n, z, hz⟩ := (isSnc_restrictedFamily T j).2 y
  refine ⟨n, z, hz, ∅, ?_⟩
  rw [stalkIdeal_centerS_eq_bot T m j hy]
  simp

/-- `F^m` divides `π_{-1}^* I` (Kollár's formula (58.1), [Kol07, 58]; `F^m · I_0 = π_{-1}^* I` in
`Transform.lean`). -/
theorem exceptionalDivisor_pow_dvd_comap (hmax : T.I.maxOrd = m) :
    (Zminus1 T.I m (T.E.component j)).exceptionalDivisor ^ m ∣
      T.I.comap (Zminus1 T.I m (T.E.component j)).blowUpπ :=
  ⟨_, (exceptionalDivisor_pow_mul_weakTransform T m j hmax).symm⟩

/-- The marked transform of `I|_S` along `Z_{-1}|_S` is the restriction of `I_0 = (π_{-1})^{-1}_* I`
along `τ = blowUpMap S.subschemeι Z_{-1}`, Kollár's `I_0|_S`: the degenerate analogue of
[Kol07, Lemma 62] (marked transforms commute with restriction to a hypersurface `H ⊋ Z` containing
the center), whose hypothesis `Z ⊊ H` excludes this case, as Kollár notes after its proof; here
`Z_{-1}|_S` is locally `S` itself or empty, and the equality is proved directly ([Kol07, Remark 67]
for the marked form). -/
theorem markedTransform_centerS_eq (hmax : T.I.maxOrd = m) :
    (T.I.comap (T.E.component j).subschemeι).markedTransform (centerS T m j) m =
      (T.I.weakTransform (Zminus1 T.I m (T.E.component j))).comap
        (Scheme.Hom.blowUpMap (T.E.component j).subschemeι (Zminus1 T.I m (T.E.component j))) := by
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  have := smooth_Zminus1 T m j
  change (T.I.comap
      (T.E.component j).subschemeι).markedTransform ((Zminus1 T.I m
      (T.E.component j)).comap (T.E.component j).subschemeι) m = _
  rw [markedTransform_comap_blowUpMap_of_pow_dvd _ _ _ _
      (exceptionalDivisor_pow_dvd_comap T m j hmax),
    ← weakTransform_eq_markedTransform_of_smooth (T.X.left ↘ Spec (.of k)) n _ _
      (ordAlongEq_Zminus1 T m j hmax)]

omit [CharZero k] in
/-- `τ = blowUpMap S.subschemeι Z_{-1}` is a closed immersion into `X_0` whose kernel is the
birational transform `(π_{-1})^{-1}_* E^j` of `E^j`: its image is Kollár's `S` on `X_0` (the proof
of [Kol07, Lemma 102]). -/
theorem ker_blowUpMap_component :
    (Scheme.Hom.blowUpMap (T.E.component j).subschemeι (Zminus1 T.I m (T.E.component j))).ker =
      (T.E.component j).strictTransform (Zminus1 T.I m (T.E.component j)) :=
  ker_blowUpMap_subschemeι _ _

/-- If `X` is smooth of relative dimension `n` over `k`, then `X_S = blowUp S (Z_{-1}|_S)` is smooth
of relative dimension `n − 1` (Kollár's `S`, of dimension `n − 1`, in the proof of
[Kol07, Lemma 102]): through `τ`, an isomorphism onto the birational transform of `E^j`, a smooth
divisor of `X_0`, which has relative dimension `n − 1`. -/
theorem smoothOfRelativeDimension_blowUpπ_centerS (n : ℕ)
    [SmoothOfRelativeDimension n (T.X.left ↘ Spec (.of k))] :
    SmoothOfRelativeDimension (n - 1) ((centerS T m j).blowUpπ ≫
      (T.E.component j).subschemeι ≫ (T.X.left ↘ Spec (.of k))) := by
  change SmoothOfRelativeDimension (n - 1)
    (((Zminus1 T.I m (T.E.component j)).comap (T.E.component j).subschemeι).blowUpπ ≫
      (T.E.component j).subschemeι ≫ (T.X.left ↘ Spec (.of k)))
  set f := T.X.left ↘ Spec (.of k) with hfdef
  set Z := Zminus1 T.I m (T.E.component j) with hZdef
  set ι := (T.E.component j).subschemeι with hιdef
  set τ := Scheme.Hom.blowUpMap ι Z with hτdef
  have hcomm : (Z.comap ι).blowUpπ ≫ ι = τ ≫ Z.blowUpπ :=
    (blowUpMap_π ι Z).symm
  rw [← Category.assoc, hcomm, Category.assoc]
  have hZs := smooth_Zminus1 T m j
  have hπ : SmoothOfRelativeDimension n (Z.blowUpπ ≫ f) :=
    smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n Z
  have hS0 : IsSmoothDivisor ((T.E.component j).strictTransform Z) :=
    isSmoothDivisor_strictTransform_of_le f n Z hZs (T.E.component j)
      (isSmoothDivisor_component T j) (component_le_Zminus1 T m j)
  have hS0' : SmoothOfRelativeDimension (n - 1)
      (((T.E.component j).strictTransform Z).subschemeι ≫ Z.blowUpπ ≫ f) :=
    smoothOfRelativeDimension_of_isSmoothDivisor (Z.blowUpπ ≫ f) n _ hS0
  have hτ : IsClosedImmersion τ :=
    isClosedImmersion_blowUpMap_of_isClosedImmersion ι Z
  have hker : τ.ker = (T.E.component j).strictTransform Z := ker_blowUpMap_component T m j
  have key : ∀ J : Z.blowUp.IdealSheafData, J = (T.E.component j).strictTransform Z →
      SmoothOfRelativeDimension (n - 1) (J.subschemeι ≫ Z.blowUpπ ≫ f) := by
    rintro J rfl
    exact hS0'
  have himg : SmoothOfRelativeDimension (n - 1) (τ.imageι ≫ Z.blowUpπ ≫ f) :=
      key _ hker
  rw [← τ.toImage_imageι, Category.assoc]
  have h0 : SmoothOfRelativeDimension 0 τ.toImage := inferInstance
  simpa using (inferInstance :
    SmoothOfRelativeDimension (0 + (n - 1)) (τ.toImage ≫ τ.imageι ≫ Z.blowUpπ ≫ f))

/-- The family of the restricted marked triple, the total transform of `(E − E^j)|_S` along
`Z_{-1}|_S`, is snc (Kollár's `E_S` in the proof of [Kol07, Lemma 102]):
`AlgebraicGeometry.totalTransform_isSnc` (`Hironaka/Scheme/BlowUpSequence/Triple.lean`), `E_S` being
snc and having snc with the center. -/
theorem isSnc_totalTransform_centerS :
    (((T.E.erase j).comap (T.E.component j).subschemeι).totalTransform (centerS T m j)).IsSnc := by
  have := smooth_component T j
  exact totalTransform_isSnc ((T.E.component j).subschemeι ≫ (T.X.left ↘ Spec (.of k)))
    _ _ (isSnc_restrictedFamily T j) (hasSncWith_centerS T m j)

/-- The marked transform of `I|_S` along `Z_{-1}|_S` is nonzero on every irreducible component of
`X_S`: it is `I_0|_S` (`markedTransform_centerS_eq`), and `τ` is an isomorphism onto the birational
transform of `E^j`, on whose components `I_0` is nonzero (`Transform.lean`). -/
theorem isNonzeroEverywhere_markedTransform_centerS
    (hI : T.I.IsDBalanced (T.X.left ↘ Spec (.of k)) m) (hmax : T.I.maxOrd = m) :
    IsNonzeroEverywhere
      ((T.I.comap (T.E.component j).subschemeι).markedTransform (centerS T m j) m) := by
  rw [markedTransform_centerS_eq T m j hmax]
  set Z := Zminus1 T.I m (T.E.component j) with hZdef
  set ι := (T.E.component j).subschemeι with hιdef
  set τ := Scheme.Hom.blowUpMap ι Z with hτdef
  have hτ : IsClosedImmersion τ :=
    isClosedImmersion_blowUpMap_of_isClosedImmersion ι Z
  have hker : τ.ker = (T.E.component j).strictTransform Z := ker_blowUpMap_component T m j
  have key : ∀ J : Z.blowUp.IdealSheafData, J = (T.E.component j).strictTransform Z →
      IsNonzeroEverywhere ((T.I.weakTransform Z).comap J.subschemeι) := by
    rintro J rfl
    exact isNonzeroEverywhere_comap_weakTransform T m j hI hmax
  rw [← τ.toImage_imageι, Scheme.IdealSheafData.comap_comp]
  have h1 : IsIso τ.toImage := inferInstance
  have h4 : Flat τ.toImage := inferInstance
  exact isNonzeroEverywhere_comap_of_flat τ.toImage (key _ hker)

end CenterS

/-! ### The restricted marked triple with the member and the family as parameters -/

section RestrictedD

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated f] (I : X.IdealSheafData) (m : ℕ) (D : X.IdealSheafData) (F : DivisorFamily X)

/-- The centre `Z_{-1}|_D` of the restricted triple, for an arbitrary member `D` (`centerS T m j` is
this at `D = E^j`). -/
noncomputable def centerSD : D.subscheme.IdealSheafData :=
  (Zminus1 I m D).comap D.subschemeι

/-- The facts about `(D, F)` that make the restricted marked triple a marked triple: they hold for
`D = E^j`, `F = E − E^j` (`restrictedHyps_component`) and are transported along equalities of `D`
(`Indifference.lean`). -/
structure RestrictedHyps : Prop where
  smooth : Smooth ((centerSD I m D).blowUpπ ≫ D.subschemeι ≫ f)
  equidim : ∃ n', SmoothOfRelativeDimension n' ((centerSD I m D).blowUpπ ≫ D.subschemeι ≫ f)
  isNonzeroEverywhere : IsNonzeroEverywhere ((I.comap D.subschemeι).markedTransform
      (centerSD I m D) m)
  isSnc : ((F.comap D.subschemeι).totalTransform (centerSD I m D)).IsSnc

/-- The restricted marked triple `(D, I|_D, m, F_D)` for a member `D` and a family `F`: the scheme
`blowUp D (Z_{-1}|_D)`, the marked transform of `I|_D` with control `m`, the mark `m`, and the
total transform of `F|_D`. -/
noncomputable def restrictedTripleD (h : RestrictedHyps f I m D F) : MarkedTriple k where
  X := .ofHom ((centerSD I m D).blowUpπ ≫ D.subschemeι ≫ f)
    (by
      have : IsLocallyNoetherian D.subscheme := (D.subschemeι ≫ f).isLocallyNoetherian_of_field
      have : IsProper (centerSD I m D).blowUpπ := blowUp.isProper_π _
      exact inferInstanceAs (FiniteType ((centerSD I m D).blowUpπ ≫ D.subschemeι ≫ f)))
    (by
      have : IsLocallyNoetherian D.subscheme := (D.subschemeι ≫ f).isLocallyNoetherian_of_field
      have : IsProper (centerSD I m D).blowUpπ := blowUp.isProper_π _
      exact inferInstanceAs (IsSeparated ((centerSD I m D).blowUpπ ≫ D.subschemeι ≫ f)))
  smoothOfRelativeDimension := h.equidim
  I := (I.comap D.subschemeι).markedTransform (centerSD I m D) m
  isNonzeroEverywhere := h.isNonzeroEverywhere
  E := (F.comap D.subschemeι).totalTransform (centerSD I m D)
  isSnc := h.isSnc
  m := m

variable {Dom : MarkedTriple k → Prop} (B : OrderGeSeqAssignment k Dom)

/-- The raw output with the member and the family as parameters: `π_{-1}` on `D` followed by `B`
on the restricted triple, pushed forward along `D ↪ X`. -/
noncomputable def rawSeqD (h : RestrictedHyps f I m D F)
    (hdom : Dom (restrictedTripleD f I m D F h)) : BlowUpSequence X :=
  (cons D.subscheme (centerSD I m D) (B.seq (restrictedTripleD f I m D F h) hdom)).pushforward
    D.subschemeι

end RestrictedD

/-- The facts making the restricted marked triple a marked triple hold at `D = E^j`,
`F = E − E^j`, for a D-balanced `I` with `max-ord I = m`: `X_S` is smooth over `k` of relative
dimension one less than `X`; the ideal is nonzero on every component (`Transform.lean`); the
family is snc. -/
theorem restrictedHyps_component [CharZero k] (T : Triple k) (m : ℕ) (j : T.E.ι)
    (hI : T.I.IsDBalanced (T.X.left ↘ Spec (.of k)) m) (hmax : T.I.maxOrd = m) :
    RestrictedHyps (T.X.left ↘ Spec (.of k)) T.I m (T.E.component j) (T.E.erase j) where
  smooth := by
    obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
    have := smoothOfRelativeDimension_blowUpπ_centerS T m j n
    exact SmoothOfRelativeDimension.smooth (n - 1) ((centerS T m j).blowUpπ ≫
      (T.E.component j).subschemeι ≫ (T.X.left ↘ Spec (.of k)))
  equidim := by
    obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
    exact ⟨n - 1, smoothOfRelativeDimension_blowUpπ_centerS T m j n⟩
  isNonzeroEverywhere := isNonzeroEverywhere_markedTransform_centerS T m j hI hmax
  isSnc := isSnc_totalTransform_centerS T m j

/-- **The restricted marked triple `(S, I_0|_S, m, E_S)`** of the proof of [Kol07, Lemma 102],
`S := E^j`, `E_S := (E − E^j)|_S`, for a D-balanced `I` with `max-ord I = m`: the marked triple
induced after the first step of the sequence on `S` with center `Z_{-1}|_S` (see the module
docstring), i.e. the scheme `X_S = blowUp S (Z_{-1}|_S)`, the marked transform of `I|_S` with
control `m` (= `I_0|_S`, `markedTransform_centerS_eq`), the mark `m`, and the total transform of
`(E − E^j)|_S`: `restrictedTripleD` at `D = E^j`, `F = E − E^j`. -/
noncomputable def restrictedTriple [CharZero k] (T : Triple k) (m : ℕ) (j : T.E.ι)
    (hI : T.I.IsDBalanced (T.X.left ↘ Spec (.of k)) m) (hmax : T.I.maxOrd = m) : MarkedTriple k :=
  restrictedTripleD (T.X.left ↘ Spec (.of k)) T.I m (T.E.component j) (T.E.erase j)
    (restrictedHyps_component T m j hI hmax)

section Restricted

variable [CharZero k] (T : Triple k) (m : ℕ) (j : T.E.ι)
  (hI : T.I.IsDBalanced (T.X.left ↘ Spec (.of k)) m) (hmax : T.I.maxOrd = m)

/-- The restricted marked triple has dimension `≤ n − 1` when `(X, I, E)` has dimension `≤ n`. -/
theorem hasDimLE_restrictedTriple {n : ℕ} (hn : T.HasDimLE n) :
    (restrictedTriple T m j hI hmax).toTriple.HasDimLE (n - 1) := by
  obtain ⟨n', hn'n, hn'⟩ := hn
  have : SmoothOfRelativeDimension n' (T.X.left ↘ Spec (.of k)) := hn'
  exact ⟨n' - 1, by omega, smoothOfRelativeDimension_blowUpπ_centerS T m j n'⟩

/-- **The output sequence on `X`** before the deletion of empty blow-ups: the composite sequence on
`S = E^j` whose first center is `Z_{-1}|_S` and whose tail is `B(S, I_0|_S, m, E_S)`, for a marked
functor `B` (the shape of [Kol07, Theorem 69], defined on the marked triples of dimension `≤ n − 1`
and mark `m`; the inductive hypothesis `BMO_{n−1,m}`), pushed forward to `X` along `S ↪ X`
([Kol07, 30.3]). Its first blow-up is the blow-up of `X` along `(Z_{-1}|_S).map ι = Z_{-1}`,
Kollár's `π_{-1}`, and its tail is `τ_* B(…)` (the proof of [Kol07, Lemma 102]). The functor
`BD_{n,m,j}` deletes the empty blow-ups ([Kol07, 32]). This is `rawSeqD` at `D = E^j`,
`F = E − E^j`. -/
noncomputable def rawSeq {n : ℕ} (hn : T.HasDimLE n) {Dom : MarkedTriple k → Prop}
    (B : OrderGeSeqAssignment k Dom)
    (hDom : ∀ T' : MarkedTriple k, T'.toTriple.HasDimLE (n - 1) → T'.m = m → Dom T') :
    BlowUpSequence T.X.left :=
  rawSeqD (T.X.left ↘ Spec (.of k)) T.I m (T.E.component j) (T.E.erase j) B
    (restrictedHyps_component T m j hI hmax)
    (hDom _ (hasDimLE_restrictedTriple T m j hI hmax hn) rfl)

/-- **The tail of the output**, Kollár's `τ_* BMO_{n−1,m}(S, I_0|_S, m, E_S)` (the proof of
[Kol07, Lemma 102]): the push-forward along `τ` (`pushforwardBlowUp`, the closed immersion
`X_S ⟶ X_0` over `S ↪ X`) of `B`'s sequence on the restricted marked triple; a blow-up sequence on
`X_0`, the blow-up of `X` along `(Z_{-1}|_S).map ι = Z_{-1}`. `rawSeq` is `π_{-1}` followed by it
(`pushforward_cons`, `Hironaka/Scheme/BlowUpSequence/Pushforward.lean`). -/
noncomputable def tailSeq {n : ℕ} (hn : T.HasDimLE n) {Dom : MarkedTriple k → Prop}
    (B : OrderGeSeqAssignment k Dom)
    (hDom : ∀ T' : MarkedTriple k, T'.toTriple.HasDimLE (n - 1) → T'.m = m → Dom T') :
    BlowUpSequence ((centerS T m j).map (T.E.component j).subschemeι).blowUp :=
  BlowUpSequence.pushforward (Y := (centerS T m j).blowUp)
    (B.seq (restrictedTriple T m j hI hmax)
      (hDom _ (hasDimLE_restrictedTriple T m j hI hmax hn) rfl))
    (pushforwardBlowUp (T.E.component j).subschemeι (centerS T m j))

end Restricted

/-- **The standing assumptions of [Kol07, Lemma 102] after its first paragraph** ("from now on we
assume that `I` is D-balanced"): the domain of the construction of `BD_{n,m,j}`, the triples with
`dim X ≤ n`, `I` D-balanced with `max-ord I = m`, and a `j`-th member of `E` (positions as in
`BDClass`). The extension to `BDClass n m j` (tuning, `Tuned.lean`; the empty sequence for
`max-ord I < m`, the convention of [Kol07, Theorem 68]) is `Assembly.lean`. -/
def Domain (n m j : ℕ) (T : Triple k) : Prop :=
  T.HasDimLE n ∧ T.I.IsDBalanced (T.X.left ↘ Spec (.of k)) m ∧ T.I.maxOrd = m ∧
    j < Fintype.card T.E.ι

end Hironaka.BD
