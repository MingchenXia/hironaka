/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Basic
import Hironaka.Resolution.Algebraic.Kol07.Globalization
import Hironaka.Resolution.Algebraic.Kol07.Globalize
import Hironaka.Resolution.Algebraic.OrderReduction.Step3Globalization
import Hironaka.Resolution.Algebraic.Stage.ClosedEmbeddingDescent
import Hironaka.Scheme.BlowUpSequence.Functoriality
import Hironaka.Scheme.BlowUpSequence.RestrictDivisors
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.Snc.RelativeDimension
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Claim 71.2: the local reduction to a hypersurface

Kollár's proof of Claim 71.2 [Kol07, 108]: the identity is "a local question on `X`", so one may
assume a chain of smooth subvarieties `Y = Y₀ ⊂ Y₁ ⊂ ⋯ ⊂ Y_c = X`, each a hypersurface in the next.
This module produces ONE step of that chain, on a surjective coproduct of open subschemes of `X`
(the "local question"), for a closed embedding `j : Y ↪ X` of smooth schemes with `Y` nowhere dense
— the case `max-ord(ker j) ≤ 1`, i.e. `ker j` is nonzero on every component and of order `1` along
`Y`:

* `HypersurfaceCover TX TY j` packages the data: a coproduct of open immersions `g : X' → X`
  (surjective, smooth), the cartesian square `Y' = Y ×_X X'` with its closed immersion `j'` and
  restriction `h_S`, the pulled-back marked triples `TX'`, `TY'`, a smooth hypersurface `H ⊂ X'`
  **containing `Y'`** with its marked triple `TH' = (H, ℓ_* J', 1, ∅)`, and the factorization
  `j' = ℓ ≫ (H ↪ X')` — both `H ⊂ X'` and `Y' ⊂ H` being closed embeddings of marked triples with
  `E = ∅`, and `dim H ≤ dim X − 1`.
* `exists_hypersurfaceCover` builds it: the hypersurface is a **hypersurface of maximal contact for
  `(ker j, 1)`** — [Kol07, Theorem 80] for the ideal of `Y` itself at the mark `1`, where
  `MC(ker j, 1) = ker j` (`MC_one`), so that `H ≤ ker j` says exactly `Y ⊆ H`. The local cover of
  the triple `(X, ker j, ∅)` for the class `BO_{n,1}` (`exists_isLocalCover` at
  `globalizationData_localClass`, Step 3 of the proof of [Kol07, Theorem 103]) supplies at once the
  surjective coproduct of open immersions `g`, the pulled-back triple, and such an `H` on the
  coproduct. The square is Mathlib's fibre product `Y ×_X X'` (`pullback.fst`, a closed immersion by
  base change, with kernel `(ker j).comap g` — `ker_fst_of_isClosedImmersion`); `ℓ` is the lift of
  `j'` through `H ↪ X'` (`IsClosedImmersion.lift`, since `H ≤ ker j'`); `TH'`'s ideal `ℓ_* J'` is
  nonzero on every component by `isNonzeroEverywhere_map_of_isClosedImmersion`, its boundary is
  empty, and its dimension is one less than `X'`'s (`smoothOfRelativeDimension_of_isSmoothDivisor`).

Kollár's sentence, read with Theorem 80 at `(ker j, 1)`, is the whole content; every ingredient is a
general lemma of the library.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Hironaka Scheme
  IdealSheafData BlowUpSequence Scheme.IdealSheafData Hironaka.Sequence Hironaka.BO

namespace Hironaka.Stage

variable {k : Type u} [Field k] [CharZero k]

/-- The data of one step of the local chain of [Kol07, 108]: on a surjective coproduct of open
immersions `g : X' → X`, the pulled-back closed embedding `j' : Y' → X'` (a cartesian square over
`j`) factors through a smooth hypersurface `H ⊂ X'` of `X'`, `j' = ℓ ≫ (H ↪ X')`, both factors
closed embeddings of marked triples with empty boundary. -/
structure HypersurfaceCover (n : ℕ) (TX TY : MarkedTriple k) (j : TY.X.left ⟶ TX.X.left) where
  /-- The marked triple of `X'`. -/
  TX' : MarkedTriple k
  /-- The marked triple of `Y' = Y ×_X X'`. -/
  TY' : MarkedTriple k
  /-- The marked triple of the hypersurface `H`, with the ideal `ℓ_* J'`. -/
  TH' : MarkedTriple k
  /-- The cover `g : X' → X`, a coproduct of open immersions. -/
  g : TX'.X.left ⟶ TX.X.left
  smooth_g : Smooth g
  surjective_g : Function.Surjective g
  /-- The closed immersion `Y' → X'`. -/
  j' : TY'.X.left ⟶ TX'.X.left
  isClosedImmersion_j' : IsClosedImmersion j'
  /-- The restriction `Y' → Y` of the cover. -/
  hS : TY'.X.left ⟶ TY.X.left
  smooth_hS : Smooth hS
  surjective_hS : Function.Surjective hS
  /-- The cartesian square `j' ≫ g = hS ≫ j`. -/
  sq : IsPullback j' hS g j
  pullback_TX' : TX'.IsPullbackOf TX g
  pullback_TY' : TY'.IsPullbackOf TY hS
  /-- The hypersurface `H ↪ X'`. -/
  Hι : TH'.X.left ⟶ TX'.X.left
  isClosedImmersion_Hι : IsClosedImmersion Hι
  isSmoothDivisor_ker : IsSmoothDivisor Hι.ker
  /-- The lift `Y' → H` of `j'`. -/
  ℓ : TY'.X.left ⟶ TH'.X.left
  isClosedImmersion_ℓ : IsClosedImmersion ℓ
  fac : ℓ ≫ Hι = j'
  closedEmbedding_X' : MarkedTriple.ClosedEmbedding TX' TH' Hι
  closedEmbedding_H : MarkedTriple.ClosedEmbedding TH' TY' ℓ
  isEmpty_E' : IsEmpty TX'.E.ι
  /-- `X'` has the dimension bound `≤ n + 1` of `X`. -/
  hasDimLE_X' : TX'.toTriple.HasDimLE (n + 1)
  /-- `H` has dimension `≤ n`, one less than `X`. -/
  hasDimLE_H : TH'.toTriple.HasDimLE n

/-- [Kol07, 108] with [Kol07, Theorem 80] at `(ker j, 1)`: for a closed embedding `j : Y ↪ X` of
marked triples with `E = ∅` and `max-ord(ker j) ≤ 1` (`Y` nowhere dense in `X`, `Y` possibly empty),
the data of one step of the local chain exist. -/
theorem exists_hypersurfaceCover {n : ℕ} (TX TY : MarkedTriple k) (j : TY.X.left ⟶ TX.X.left)
    [IsClosedImmersion j] (hj : MarkedTriple.ClosedEmbedding TX TY j) (hE : IsEmpty TX.E.ι)
    (hTX : TX.BMOClass (n + 1) 1) (hK : j.ker.maxOrd ≤ ((1 : ℕ) : ℕ∞)) [Nonempty TX.X.left] :
    Nonempty (HypersurfaceCover n TX TY j) := by
  have hPF : PerfectField k := PerfectField.ofCharZero
  -- `ker j` is nonzero on every component: its order is never `⊤`
  have hKnz : IsNonzeroEverywhere j.ker := by
    intro x hx
    have : IsLocallyNoetherian TX.X.left := (TX.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
    have h1 : j.ker.ord x = ⊤ := (ord_eq_top_iff j.ker x).mpr hx
    have h2 : j.ker.ord x ≤ ((1 : ℕ) : ℕ∞) := (maxOrd_le_iff _).mp hK x
    rw [h1] at h2
    exact absurd h2 (by simp)
  -- the triple `(X, ker j, ∅)` in the class of `BO_{n+1,1}`
  let TK : Triple k := { TX.toTriple with I := j.ker, isNonzeroEverywhere := hKnz }
  have hTK : Triple.BOClass (n + 1) 1 TK := ⟨le_rfl, hTX.2.1, hK⟩
  have : Nonempty TK.X.left := ‹Nonempty TX.X.left›
  -- the local cover of Step 3 of Theorem 103: a surjective coproduct of open immersions carrying a
  -- hypersurface of maximal contact for `(ker j, 1)`, i.e. a smooth hypersurface containing `Y`
  obtain ⟨T', g, -, hLT, hM, hsurj, hpb⟩ :=
    Triple.exists_isLocalCover (globalizationData_localClass (n + 1) 1) hTK
  obtain ⟨H, hH, hmc⟩ := hLT.2
  have hHle : H ≤ j.ker.comap g := by
    have h := hmc
    change H ≤ MC (T'.X.left ↘ Spec (.of k)) T'.I 1 at h
    rwa [MC_one, hpb.2.1] at h
  have hsm : Smooth g := openImmersionCoprods.smooth hM
  have hgo : g.IsOver (Spec (.of k)) := ⟨hpb.1⟩
  -- the pulled-back triple of `X`
  let TX' : MarkedTriple k := MarkedTriple.pullback TX T'.smoothOfRelativeDimension g
  have hpbX : TX'.IsPullbackOf TX g :=
    MarkedTriple.isPullbackOf_pullback TX T'.smoothOfRelativeDimension g
  -- the fibre product `Y' = Y ×_X X'` with its closed immersion and restriction
  let Y' : Scheme.{u} := Limits.pullback g j
  let j' : Y' ⟶ T'.X.left := pullback.fst g j
  let hS : Y' ⟶ TY.X.left := pullback.snd g j
  have sq : IsPullback j' hS g j := IsPullback.of_hasPullback g j
  have hM' : openImmersionCoprods hS :=
    isStableUnderBaseChange_openImmersionCoprods.of_isPullback sq hM
  have hsmS : Smooth hS := openImmersionCoprods.smooth hM'
  have hetS : Etale hS := openImmersionCoprods_etale hS hM'
  have hsepS : IsSeparated hS := openImmersionCoprods_isSeparated hM'
  have hsurjS : Function.Surjective hS := by
    intro y
    obtain ⟨x', hx'⟩ := hsurj (j y)
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback x' y hx'
    exact ⟨z, hz⟩
  let _ : Y'.Over (Spec (.of k)) := ⟨hS ≫ (TY.X.left ↘ Spec (.of k))⟩
  have hSo : hS.IsOver (Spec (.of k)) := ⟨rfl⟩
  have hcptX' : CompactSpace T'.X.left :=
    QuasiCompact.compactSpace_of_compactSpace (T'.X.left ↘ Spec (.of k))
  have hcptY' : CompactSpace Y' := QuasiCompact.compactSpace_of_compactSpace j'
  have : LocallyOfFiniteType (Y' ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (hS ≫ (TY.X.left ↘ Spec (.of k))))
  have : IsSeparated (Y' ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated (hS ≫ (TY.X.left ↘ Spec (.of k))))
  have : QuasiCompact (Y' ↘ Spec (.of k)) := inferInstance
  have hY' : ∃ d : ℕ, SmoothOfRelativeDimension d (Y' ↘ Spec (.of k)) := by
    obtain ⟨d, hd⟩ := TY.smoothOfRelativeDimension
    exact ⟨0 + d, smoothOfRelativeDimension_comp 0 d hS (TY.X.left ↘ Spec (.of k))⟩
  let TY' : MarkedTriple k := MarkedTriple.pullback TY hY' hS
  have hpbY : TY'.IsPullbackOf TY hS := MarkedTriple.isPullbackOf_pullback TY hY' hS
  -- the closed embedding `TX' ⊃ TY'` of marked triples along `j'`
  have hover' : j' ≫ (T'.X.left ↘ Spec (.of k)) = hS ≫ (TY.X.left ↘ Spec (.of k)) := by
    rw [← hpb.1, ← Category.assoc, sq.w, Category.assoc]
    change hS ≫ j ≫ (TX.X.left ↘ Spec (.of k)) = _
    rw [hj.1.1]
  have hI' : TX.I.comap g = (TY.I.comap hS).map j' := by
    rw [hj.1.2.1]
    exact comap_map_of_isPullback sq TY.I
  have hE' : TY.E.comap hS = (TX.E.comap g).comap j' := by
    rw [hj.1.2.2, ← DivisorFamily.comap_comp, ← DivisorFamily.comap_comp, sq.w]
  -- the hypersurface `H ↪ X'` and the lift of `j'`
  have hker' : j'.ker = j.ker.comap g := ker_fst_of_isClosedImmersion j g
  have hHle' : H.subschemeι.ker ≤ j'.ker := by
    rw [ker_subschemeι, hker']
    exact hHle
  let ℓ : Y' ⟶ H.subscheme := IsClosedImmersion.lift H.subschemeι j' hHle'
  have hfac : ℓ ≫ H.subschemeι = j' := IsClosedImmersion.lift_fac H.subschemeι j' hHle'
  have hcij' : IsClosedImmersion j' := inferInstanceAs (IsClosedImmersion (pullback.fst g j))
  have hciH : IsClosedImmersion H.subschemeι := inferInstance
  have hciℓ : IsClosedImmersion ℓ := by
    have : IsClosedImmersion (ℓ ≫ H.subschemeι) := by
      rw [hfac]
      exact hcij'
    exact IsClosedImmersion.of_comp_isClosedImmersion ℓ H.subschemeι
  have hHsd : IsSmoothDivisor H.subschemeι.ker := by
    rw [ker_subschemeι]
    exact hH
  -- the dimension of `X'` and of `H`
  obtain ⟨n', hn'le, hn'⟩ := hLT.1.2.1
  have hn'i : SmoothOfRelativeDimension n' (T'.X.left ↘ Spec (.of k)) := hn'
  have hHdim : SmoothOfRelativeDimension (n' - 1) (H.subschemeι ≫ (T'.X.left ↘ Spec (.of k))) :=
    smoothOfRelativeDimension_of_isSmoothDivisor (T'.X.left ↘ Spec (.of k)) n' H hH
  have hHsm : Smooth (H.subschemeι ≫ (T'.X.left ↘ Spec (.of k))) :=
    SmoothOfRelativeDimension.smooth (n' - 1) _
  have hEι : IsEmpty ((TX.E.comap g).comap H.subschemeι).ι := hE
  -- the marked triple of the hypersurface, with the ideal `ℓ_* J'`
  let TH' : MarkedTriple k :=
    { X := .ofHom (H.subschemeι ≫ (T'.X.left ↘ Spec (.of k)))
        (inferInstanceAs (FiniteType (H.subschemeι ≫ (T'.X.left ↘ Spec (.of k)))))
        (inferInstanceAs (IsSeparated (H.subschemeι ≫ (T'.X.left ↘ Spec (.of k)))))
      smoothOfRelativeDimension := ⟨n' - 1, hHdim⟩
      I := TY'.I.map ℓ
      isNonzeroEverywhere :=
        isNonzeroEverywhere_map_of_isClosedImmersion ℓ TY'.I TY'.isNonzeroEverywhere
      E := (TX.E.comap g).comap H.subschemeι
      isSnc := isSnc_of_isEmpty (H.subschemeι ≫ (T'.X.left ↘ Spec (.of k))) _
      m := 1 }
  refine ⟨⟨TX', TY', TH', g, hsm, hsurj, j', hcij', hS, hsmS, hsurjS, sq, hpbX, hpbY,
    H.subschemeι, hciH, hHsd, ℓ, hciℓ, hfac, ⟨⟨rfl, ?_, rfl⟩, hTX.2.2.symm⟩,
    ⟨⟨?_, rfl, ?_⟩, hj.2.trans hTX.2.2⟩, hE, hLT.1.2.1, ⟨n' - 1, by omega, hHdim⟩⟩⟩
  · -- `TX'.I = (ℓ_* J').map (H ↪ X')`
    change TX.I.comap g = (TY'.I.map ℓ).map H.subschemeι
    exact hI'.trans ((congrArg (fun f : Y' ⟶ T'.X.left => TY'.I.map f) hfac.symm).trans
      (map_comp TY'.I ℓ H.subschemeι))
  · -- the structure morphism of `Y'` factors through `H`
    change ℓ ≫ H.subschemeι ≫ (T'.X.left ↘ Spec (.of k)) = hS ≫ (TY.X.left ↘ Spec (.of k))
    rw [← Category.assoc, hfac]
    exact hover'
  · -- `TY'.E = TH'.E.comap ℓ`
    change TY.E.comap hS = ((TX.E.comap g).comap H.subschemeι).comap ℓ
    rw [hE', ← hfac, DivisorFamily.comap_comp]

end Hironaka.Stage
