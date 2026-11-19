/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.Triple
public import Hironaka.Scheme.BlowUpSequence.ConcatPullback
import Hironaka.Resolution.Algebraic.Kol07.EraseEmptyInduced
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.Functorial
import Hironaka.Resolution.Algebraic.Tuning.Transform
import Hironaka.Scheme.BlowUpSequence.BaseChange
import Hironaka.Scheme.BlowUpSequence.DisjointUnion
import Hironaka.Scheme.BlowUpSequence.Functoriality
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The disjoined triple commutes with smooth pullback and base change

The functoriality of the principalization functor, clauses (4) and (5) of [Kol07, Theorem 35],
"follow[s] from the corresponding functoriality properties in (69) and from (71.2)" [Kol07, 72];
for this the disjoined triple `Hironaka.disjoinedTriple T = (X', π^* I, ∑ E^i)` must
carry the pullback data of `disjoinedTriple T'` along the lift of a smooth `g : X' ⟶ X`
([Kol07, 34.1]) and the base-change data along the lift of the projection `X_{L,σ} ⟶ X`
([Kol07, 34.2]). `disjoin_functorial`
(`Hironaka/Resolution/Algebraic/Kol07/Thm35/Disjoin/Functorial.lean`) gives `disjoinSeq (E.comap g)
= (disjoinSeq E).pullback g`, an equality of sequences, so the last stages agree only up to an
`eqToHom`, and `pullbackLastHom` (`Hironaka/Scheme/BlowUpSequence/ConcatPullback.lean`) is the lift
of `g` to the last stages. This module assembles the two into

* `Triple.disjoinedMap g e : (disjoinedTriple T').X.left ⟶ (disjoinedTriple T).X.left`, the lift of
  `g` across the identification `e` of the disjoining sequences;
* `disjoinedTriple_isPullbackOf`: `disjoinedTriple T'` is the pullback of `disjoinedTriple T` along
  it whenever `T'` is the pullback of `T` along a flat `g` ([Kol07, 34.1] for the disjoined
  triples);
* `disjoinedTriple_isBaseChangeOf`: the same for the base change along `σ : k →+* L`
  ([Kol07, 34.2]), the pulled-back square being the stage square of
  `Hironaka/Scheme/BlowUpSequence/BaseChange.lean` at the last stage pasted on the `eqToHom`.

The one non-formal point is the ordered family `∑ E^i` (`collapsedFamily`): it is the total
transform at the end of the disjoining sequence with the birational transforms of the original
members collapsed into `E^0` (`DivisorFamily.collapse`), and collapsing commutes with inverse
images, componentwise, the collapsed member being a product (`collapse_comap`,
`comap_finset_prod`), while the total transform and the marking of the original members commute
with flat pullback by `totalTransformSeq_pullback` and the transport of `originalIdx`, in the
recursive form of `subfamily_originalIdx_pullback` (`collapse_originalIdx_pullback`).
The collapse is defined at the end of an arbitrary sequence `S`, so that the `eqToHom` of
`disjoin_functorial` can be absorbed along an equality of sequences (`collapsedFamily_congr`). The
decidability instance of the collapsed predicate is carried explicitly through the recursion
(`collapse_congr_inst`: the collapse does not depend on it), since the constructive instance
found for `· ∈ Set.range f` on a finite type and the classical one are not definitionally equal.

One general fact about sequences is placed here beside its use:
`Triple.IsBaseChangeOf.isPullback_pullbackLastHom`, the last-stage lift of a base change is again
a base change (the stage square `Triple.IsBaseChangeOf.isPullback_pullbackStageHom` at the last
index across the identification `pullbackStageIdx_last`). This module is the first that imports
`pullbackStageIdx_last` (`EraseEmptyInduced.lean`), `pullbackLastHom` (`ConcatPullback.lean`) and
`isPullback_pullbackStageHom` (`BaseChange.lean`) together.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Scheme BlowUpSequence

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-! ### Collapsing commutes with inverse images -/

/-- The collapse does not depend on the decidability instance of the collapsed predicate. -/
theorem collapse_congr_inst (F : DivisorFamily X) (p : F.ι → Prop) (i₁ i₂ : DecidablePred p) :
    @DivisorFamily.collapse X F p i₁ = @DivisorFamily.collapse X F p i₂ := by
  have : i₁ = i₂ := funext fun a => Subsingleton.elim _ _
  subst this
  rfl

/-- Collapsing a set of members commutes with the inverse image along any morphism: the collapsed
member is a product, and inverse images of ideal sheaves are multiplicative (`comap_finset_prod`);
the other members are unchanged. (The index type of `F.comap φ` is that of `F` only by unfolding,
so the decidability instance is passed by hand.) -/
theorem collapse_comap (F : DivisorFamily X) (p : F.ι → Prop) [hp : DecidablePred p] (φ : Y ⟶ X) :
    (F.collapse p).comap φ = @DivisorFamily.collapse Y (F.comap φ) p hp := by
  obtain ⟨ι, c⟩ := F
  unfold DivisorFamily.collapse DivisorFamily.comap
  congr 1
  funext j
  induction j using WithBot.recBotCoe with
  | bot => exact Scheme.IdealSheafData.comap_finset_prod _ _ φ
  | coe a => rfl

/-- Transport of a collapse of the total transform along an equality of stage indices: the
`eqToHom` of the stage identification is absorbed (the analogue for `collapse` of
`subfamily_totalTransformSeq_eq_idx`). -/
theorem collapse_totalTransformSeq_eq_idx (S : BlowUpSequence X) (E : DivisorFamily X)
    {i j : Fin (S.length + 1)} (e : i = j)
    (P : ∀ i : Fin (S.length + 1), (S.totalTransformSeq E i).ι → Prop)
    (iP : ∀ i, DecidablePred (P i)) :
    @DivisorFamily.collapse _ (S.totalTransformSeq E j) (P j) (iP j) =
      (@DivisorFamily.collapse _ (S.totalTransformSeq E i) (P i) (iP i)).comap
        (eqToHom (congrArg S.stage e.symm)) := by
  cases e
  rw [eqToHom_refl, DivisorFamily.comap_id]

/-- Congruence of the collapse of the total transform along the marked original members, along an
equality of the starting families (the analogue for `collapse` of
`subfamily_originalIdx_congr`). -/
theorem collapse_originalIdx_congr (S : BlowUpSequence X) (F₁ F₂ : DivisorFamily X) (e : F₁ = F₂)
    (i : Fin (S.length + 1)) {T : Type u} (x₁ : T → F₁.ι) (x₂ : T → F₂.ι) (hx : HEq x₁ x₂)
    (i₁ : DecidablePred fun b => b ∈ Set.range fun t => S.originalIdx F₁ i (x₁ t))
    (i₂ : DecidablePred fun b => b ∈ Set.range fun t => S.originalIdx F₂ i (x₂ t)) :
    @DivisorFamily.collapse _ (S.totalTransformSeq F₁ i) _ i₁ =
      @DivisorFamily.collapse _ (S.totalTransformSeq F₂ i) _ i₂ := by
  subst e
  cases hx
  exact collapse_congr_inst _ _ i₁ i₂

/-- Along a flat `g`, the total transform at stage `⟨j, hj⟩` with the birational transforms of the
marked original members `x t` collapsed pulls back to the corresponding collapse of the
pulled-back sequence (`totalTransformSeq_pullback`, `subfamily_originalIdx_pullback`): by
recursion on the sequence, the marked members carried through the first blow-up as
`toLex (Sum.inl (x t))`; at the base the collapse commutes with the inverse image
(`collapse_comap`). -/
theorem collapse_originalIdx_pullback :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) {Y : Scheme.{u}} (g : Y ⟶ X) [Flat g]
      (E : DivisorFamily X) (j : ℕ) (hj : j < S.length + 1) {T : Type u} (x : T → E.ι)
      (i₁ : DecidablePred fun b => b ∈ Set.range fun t =>
        (S.pullback g).originalIdx (E.comap g) (S.pullbackStageIdx g ⟨j, hj⟩) (x t))
      (i₂ : DecidablePred fun b => b ∈ Set.range fun t => S.originalIdx E ⟨j, hj⟩ (x t)),
      @DivisorFamily.collapse _
          ((S.pullback g).totalTransformSeq (E.comap g) (S.pullbackStageIdx g ⟨j, hj⟩)) _ i₁ =
        (@DivisorFamily.collapse _ (S.totalTransformSeq E ⟨j, hj⟩) _ i₂).comap
          (S.pullbackStageHom g ⟨j, hj⟩)
  | _, nil _, _, g, _, E, _, _, _, _, i₁, i₂ =>
    Eq.trans (collapse_congr_inst _ _ i₁ i₂) (collapse_comap E _ g (hp := i₂)).symm
  | _, cons _ _ _, _, g, _, E, 0, _, _, _, i₁, i₂ =>
    Eq.trans (collapse_congr_inst _ _ i₁ i₂) (collapse_comap E _ g (hp := i₂)).symm
  | _, cons X D rest, Y, g, _, E, j + 1, hj, T, x, i₁, i₂ => by
    have hflat : Flat (Scheme.Hom.blowUpMap g D) := flat_blowUpMap g D
    exact (collapse_originalIdx_congr (rest.pullback (Scheme.Hom.blowUpMap g D))
      ((E.comap g).totalTransform (D.comap g)) ((E.totalTransform D).comap
          (Scheme.Hom.blowUpMap g D))
      (totalTransform_comap_of_flat g D E)
      (rest.pullbackStageIdx (Scheme.Hom.blowUpMap g D) ⟨j, Nat.lt_of_succ_lt_succ hj⟩)
      (fun t => toLex (Sum.inl (x t))) (fun t => toLex (Sum.inl (x t))) HEq.rfl i₁
      (Classical.decPred _)).trans
      (collapse_originalIdx_pullback rest (Scheme.Hom.blowUpMap g D) (E.totalTransform D) j
        (Nat.lt_of_succ_lt_succ hj) (fun t => toLex (Sum.inl (x t))) (Classical.decPred _) i₂)

/-! ### The collapsed family at the end of a sequence -/

/-- The collapsed family along an equality of sequences: the `eqToHom` of the last stages is
absorbed. -/
theorem collapsedFamily_congr {S S' : BlowUpSequence X} (e : S = S') (E : DivisorFamily X) :
    collapsedFamily S E =
      (collapsedFamily S' E).comap (eqToHom (congrArg BlowUpSequence.last e)) := by
  subst e
  rw [eqToHom_refl, DivisorFamily.comap_id]

/-- The collapsed family of the pulled-back sequence is the inverse image of the collapsed family
along the last-stage lift (`collapse_originalIdx_pullback` at the last index, across
`pullbackStageIdx_last`). -/
theorem collapsedFamily_pullback (S : BlowUpSequence X) (g : Y ⟶ X) [Flat g]
    (E : DivisorFamily X) :
    collapsedFamily (S.pullback g) (E.comap g) =
      (collapsedFamily S E).comap (S.pullbackLastHom g) := by
  have key := collapse_originalIdx_pullback S g E S.length (Nat.lt_succ_self _) (fun a : E.ι => a)
    (Classical.decPred _) (Classical.decPred _)
  unfold collapsedFamily
  have h1 := collapse_congr_inst ((S.pullback g).totalTransformSeq (E.comap g) (Fin.last _))
    (fun a => a ∈ Set.range ((S.pullback g).originalIdx (E.comap g) (Fin.last _)))
    inferInstance (Classical.decPred _)
  have h2 := collapse_congr_inst (S.totalTransformSeq E (Fin.last _))
    (fun a => a ∈ Set.range (S.originalIdx E (Fin.last _))) inferInstance (Classical.decPred _)
  rw [h1, h2]
  refine (collapse_totalTransformSeq_eq_idx (S.pullback g) (E.comap g) (pullbackStageIdx_last S g)
    (fun i a => a ∈ Set.range ((S.pullback g).originalIdx (E.comap g) i))
    (fun _ => Classical.decPred _)).trans ?_
  refine Eq.trans (congrArg (fun F : DivisorFamily _ =>
    F.comap (eqToHom (congrArg (S.pullback g).stage (pullbackStageIdx_last S g).symm))) key) ?_
  exact (DivisorFamily.comap_comp _ _ _).symm

end Hironaka.Sequence

namespace AlgebraicGeometry.Triple

open Hironaka

open Scheme

open Hironaka.Sequence AlgebraicGeometry

variable {k : Type u} [Field k] {L : Type u} [Field L]

/-! ### A general fact about sequences -/

/-- The last-stage lift of the projection of a base change is again a base change
([Kol07, 34.2] at the last stage): the stage square `isPullback_pullbackStageHom` at the last
index across the identification `pullbackStageIdx_last`. -/
theorem IsBaseChangeOf.isPullback_pullbackLastHom {T : Triple k} {T' : Triple L} {σ : k →+* L}
    {p : T'.X.left ⟶ T.X.left} (hp : T'.IsBaseChangeOf T σ p) (S : BlowUpSequence T.X.left) :
    IsPullback (S.pullbackLastHom p)
      ((S.pullback p).composite ≫ (T'.X.left ↘ Spec (.of L)))
      (S.composite ≫ (T.X.left ↘ Spec (.of k))) (Spec.map (CommRingCat.ofHom σ)) := by
  have sq := hp.isPullback_pullbackStageHom S (Fin.last _)
  have hiso : IsPullback
      (eqToHom (congrArg (S.pullback p).stage (pullbackStageIdx_last S p).symm))
      (eqToHom (congrArg (S.pullback p).stage (pullbackStageIdx_last S p).symm) ≫
        ((S.pullback p).stageMap (S.pullbackStageIdx p (Fin.last _)) ≫ (T'.X.left ↘ Spec (.of L))))
      ((S.pullback p).stageMap (S.pullbackStageIdx p (Fin.last _)) ≫ (T'.X.left ↘ Spec (.of L)))
      (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]⟩
  have key := hiso.paste_horiz sq
  rw [Category.id_comp] at key
  change IsPullback (eqToHom _ ≫ S.pullbackStageHom p (Fin.last _))
    ((S.pullback p).stageMap (Fin.last _) ≫ (T'.X.left ↘ Spec (.of L))) _ _
  rwa [stageMap_eq_idx (S.pullback p) (pullbackStageIdx_last S p), Category.assoc]

/-! ### The lift to the disjoined triples -/

/-- The lift of `g : T'.X.left ⟶ T.X.left` to the disjoined triples (over possibly different base
fields), across the identification `e` of the disjoining sequence of `T'.E` with the pullback of
that of `T.E` (`disjoin_functorial`) and the last-stage lift `pullbackLastHom`. -/
noncomputable def disjoinedMap [CharZero k] [CharZero L] {T : Triple k} {T' : Triple L}
    (g : T'.X.left ⟶ T.X.left) (e : disjoinSeq T'.E = (disjoinSeq T.E).pullback g) :
    (disjoinedTriple T').X.left ⟶ (disjoinedTriple T).X.left :=
  eqToHom (congrArg BlowUpSequence.last e) ≫ (disjoinSeq T.E).pullbackLastHom g

/-- The disjoining sequence of the pullback data is the pullback of the disjoining sequence
(`disjoinSeq_comap_of_flat` read through `IsPullbackOf`). -/
theorem IsPullbackOf.disjoinSeq_eq {T T' : Triple k} {g : T'.X.left ⟶ T.X.left} [Flat g]
    (h : T'.IsPullbackOf T g) : disjoinSeq T'.E = (disjoinSeq T.E).pullback g := by
  rw [h.2.2]
  exact disjoinSeq_comap_of_flat g T.E

/-- The disjoining sequence of the base-change data is the pullback of the disjoining sequence
(`disjoinSeq_comap_of_flat`, the projection being flat). -/
theorem IsBaseChangeOf.disjoinSeq_eq {T : Triple k} {T' : Triple L} {σ : k →+* L}
    {p : T'.X.left ⟶ T.X.left} (h : T'.IsBaseChangeOf T σ p) :
    disjoinSeq T'.E = (disjoinSeq T.E).pullback p := by
  have := h.flat
  rw [h.2.2]
  exact disjoinSeq_comap_of_flat p T.E

/-- If `T'` carries the pullback data of `T` along a flat `g`, the disjoined triple of `T'`
carries the pullback data of the disjoined triple of `T` along the lift `disjoinedMap`
([Kol07, 72 and 34.1]): the structure morphism and the ideal by `pullbackLastHom_comp_composite`,
the ordered family by `collapsedFamily_pullback`. -/
theorem disjoinedTriple_isPullbackOf [CharZero k] {T T' : Triple k}
    (g : T'.X.left ⟶ T.X.left) [Flat g] (h : T'.IsPullbackOf T g) :
    (disjoinedTriple T').IsPullbackOf (disjoinedTriple T)
      (disjoinedMap g h.disjoinSeq_eq) := by
  obtain ⟨X', eqd, I', nz, E', snc⟩ := T'
  change X'.left ⟶ T.X.left at g
  have hI : I' = T.I.comap g := h.2.1
  have hE : E' = T.E.comap g := h.2.2
  subst hI hE
  have hover : g ≫ (T.X.left ↘ Spec (.of k)) = (X'.left ↘ Spec (.of k)) := h.1
  have e : disjoinSeq (T.E.comap g) = (disjoinSeq T.E).pullback g := disjoinSeq_comap_of_flat g T.E
  refine ⟨?_, ?_, ?_⟩
  · change (eqToHom (congrArg BlowUpSequence.last e) ≫ (disjoinSeq T.E).pullbackLastHom g) ≫
      ((disjoinSeq T.E).composite ≫ (T.X.left ↘ Spec (.of k))) =
      (disjoinSeq (T.E.comap g)).composite ≫ (X'.left ↘ Spec (.of k))
    rw [Category.assoc, ← Category.assoc ((disjoinSeq T.E).pullbackLastHom g),
      pullbackLastHom_comp_composite, Category.assoc, hover, ← Category.assoc,
      eqToHom_comp_composite_of_eq e]
  · change (T.I.comap g).comap (disjoinSeq (T.E.comap g)).composite =
      (T.I.comap (disjoinSeq T.E).composite).comap
        (eqToHom (congrArg BlowUpSequence.last e) ≫ (disjoinSeq T.E).pullbackLastHom g)
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, Category.assoc,
      pullbackLastHom_comp_composite, ← Category.assoc, eqToHom_comp_composite_of_eq e]
  · change collapsedFamily _ (T.E.comap g) = (collapsedFamily _ T.E).comap
      (eqToHom (congrArg BlowUpSequence.last e) ≫ (disjoinSeq T.E).pullbackLastHom g)
    rw [collapsedFamily_congr e, collapsedFamily_pullback, DivisorFamily.comap_comp]

/-- If `T'` carries the base-change data of `T` along `σ` through `p`, the disjoined triple of
`T'` carries the base-change data of the disjoined triple of `T` through the lift `disjoinedMap`
([Kol07, 72 and 34.2]): the cartesian square by `IsBaseChangeOf.isPullback_pullbackLastHom`
pasted on the `eqToHom`, the ideal and the ordered family as for the pullback data. -/
theorem disjoinedTriple_isBaseChangeOf [CharZero k] [CharZero L] {T : Triple k} {T' : Triple L}
    (σ : k →+* L) (p : T'.X.left ⟶ T.X.left) (h : T'.IsBaseChangeOf T σ p) :
    (disjoinedTriple T').IsBaseChangeOf (disjoinedTriple T) σ
      (disjoinedMap p h.disjoinSeq_eq) := by
  have hflat : Flat p := h.flat
  obtain ⟨X', eqd, I', nz, E', snc⟩ := T'
  change X'.left ⟶ T.X.left at p
  have hI : I' = T.I.comap p := h.2.1
  have hE : E' = T.E.comap p := h.2.2
  subst hI hE
  have e : disjoinSeq (T.E.comap p) = (disjoinSeq T.E).pullback p := disjoinSeq_comap_of_flat p T.E
  refine ⟨?_, ?_, ?_⟩
  · have key := h.isPullback_pullbackLastHom (disjoinSeq T.E)
    have hiso : IsPullback (eqToHom (congrArg BlowUpSequence.last e))
        (eqToHom (congrArg BlowUpSequence.last e) ≫
          (((disjoinSeq T.E).pullback p).composite ≫ (X'.left ↘ Spec (.of L))))
        (((disjoinSeq T.E).pullback p).composite ≫ (X'.left ↘ Spec (.of L))) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]⟩
    have key2 := hiso.paste_horiz key
    rw [Category.id_comp, ← Category.assoc, eqToHom_comp_composite_of_eq e] at key2
    exact key2
  · change (T.I.comap p).comap (disjoinSeq (T.E.comap p)).composite =
      (T.I.comap (disjoinSeq T.E).composite).comap
        (eqToHom (congrArg BlowUpSequence.last e) ≫ (disjoinSeq T.E).pullbackLastHom p)
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, Category.assoc,
      pullbackLastHom_comp_composite, ← Category.assoc, eqToHom_comp_composite_of_eq e]
  · change collapsedFamily _ (T.E.comap p) = (collapsedFamily _ T.E).comap
      (eqToHom (congrArg BlowUpSequence.last e) ≫ (disjoinSeq T.E).pullbackLastHom p)
    rw [collapsedFamily_congr e, collapsedFamily_pullback, DivisorFamily.comap_comp]

end AlgebraicGeometry.Triple
