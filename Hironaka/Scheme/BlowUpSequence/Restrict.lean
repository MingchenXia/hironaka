/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Pullback
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
/-!
# Restriction of a blow-up sequence to a closed subscheme

For a closed subscheme `j : S ↪ X` and a blow-up sequence `B` starting with `X`, the restriction
`j^* B = B|_S` of [Kol07, 30.2] is the sequence starting with `S` whose centers are `Z_i ∩ S_i`,
with `S_{i+1} = B_{Z_i ∩ S_i} S_i` "naturally identified with the birational transform
`(π_i)⁻¹_* S_i ⊂ X_{i+1}`" (Kollár cites [Har77, Proposition II.7.15]), "thus there are natural
embeddings
`S_i ↪ X_i`".
Here the restriction is the pullback `S.pullback J.subschemeι` of
`Hironaka/Scheme/BlowUpSequence/Pullback.lean` (the inverse image ideal `D.comap J.subschemeι` is
the ideal of `Z ∩ S` in `S`), and the natural embedding of one step is the morphism of blow-ups
`blowUpMap J.subschemeι D`.

The one-step statement, that this morphism is a closed immersion with kernel the strict transform,
is proved in `Hironaka/Scheme/BlowUp/ClosedImmersionLift.lean`: `B_{Z ∩ S} S` is isomorphic to the
strict transform `V(Jˢ) ⊆ B_Z X` compatibly with the maps to `X` ([Har77, Proposition II.7.15],
`exists_iso_strictTransform_subscheme`); the composite `e.hom ≫ (strictTransform D J).subschemeι`
is therefore a morphism over `J.subschemeι`, hence equal to the lift by the uniqueness clause of
the universal property (`eq_blowUpMap`), and an isomorphism followed by a closed immersion is a
closed immersion.

This module proves the stagewise statements. From the one-step case (for every closed immersion
`j`, `blowUpMap j D` is a closed immersion with kernel `strictTransform D j.ker`,
`AlgebraicGeometry.isClosedImmersion_blowUpMap_of_isClosedImmersion` and
`AlgebraicGeometry.ker_blowUpMap_of_isClosedImmersion`, through the scheme-theoretic image of `j`),
by induction every stage lift `S.pullbackStageHom j i` is a closed immersion with kernel
`S.strictTransformSeq j.ker i` (`isClosedImmersion_pullbackStageHom`, `ker_pullbackStageHom`);
Kollár's "`S_{i+1}` is naturally identified with the birational transform `(π_i)⁻¹_* S_i`" is the
isomorphism `exists_iso_strictTransformSeq` onto the subscheme of that kernel, given by Mathlib's
`Scheme.Hom.toImage`. When every center `Z_i` lies in the strict transform `S_i`, the restricted
sequence of a smooth sequence is smooth (`isSmooth_pullback_of_strictTransformSeq_le`): the
smoothness of `Z_i ⊆ S_i` is transported along the isomorphism `V(Z_i ∩ S_i) ≅ V(Z_i)` of
`isPullback_of_isClosedImmersion` (`exists_iso_subscheme_comap_of_ker_le`), whose ideal-sheaf form
`(Z.comap g).map g = Z` for `g.ker ≤ Z` (`map_comap_of_ker_le`) is used in
`Hironaka/Scheme/BlowUpSequence/Pushforward.lean` for `j_* j^* B = B`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme BlowUpSequence

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-! ### Stagewise: the natural embeddings `S_i ↪ X_i` -/

/-- Every stage lift of the pullback along a closed immersion is a closed immersion, in the
`⟨n, hn⟩` form of the indices. -/
theorem isClosedImmersion_pullbackStageHom_mk (S : BlowUpSequence X) (j : Y ⟶ X)
    [IsClosedImmersion j] (n : ℕ) (hn : n < S.length + 1) :
    IsClosedImmersion (S.pullbackStageHom j ⟨n, hn⟩) := by
  induction S generalizing Y n with
  | nil X => exact ‹IsClosedImmersion j›
  | cons X D rest ih =>
    cases n with
    | zero => exact ‹IsClosedImmersion j›
    | succ n =>
      have := isClosedImmersion_blowUpMap_of_isClosedImmersion j D
      exact ih (Scheme.Hom.blowUpMap j D) n (Nat.lt_of_succ_lt_succ hn)

/-- The kernel of the `n`-th stage lift is the `n`-th strict transform of the image of `j`, in the
`⟨n, hn⟩` form of the indices. -/
theorem ker_pullbackStageHom_mk (S : BlowUpSequence X) (j : Y ⟶ X) [IsClosedImmersion j] (n : ℕ)
    (hn : n < S.length + 1) :
    (S.pullbackStageHom j ⟨n, hn⟩).ker = S.strictTransformSeq j.ker ⟨n, hn⟩ := by
  induction S generalizing Y n with
  | nil X => rfl
  | cons X D rest ih =>
    cases n with
    | zero => rfl
    | succ n =>
      have := isClosedImmersion_blowUpMap_of_isClosedImmersion j D
      have h := ih (Scheme.Hom.blowUpMap j D) n (Nat.lt_of_succ_lt_succ hn)
      rw [ker_blowUpMap_of_isClosedImmersion] at h
      exact h

/-- Every stage lift of the pullback along a closed immersion is a closed immersion: the natural
embeddings `S_i ↪ X_i` of [Kol07, 30.2]. -/
theorem isClosedImmersion_pullbackStageHom (S : BlowUpSequence X) (j : Y ⟶ X) [IsClosedImmersion j]
    (i : Fin (S.length + 1)) : IsClosedImmersion (S.pullbackStageHom j i) := by
  obtain ⟨n, hn⟩ := i
  exact isClosedImmersion_pullbackStageHom_mk S j n hn

/-- The kernel of the `i`-th stage lift is the `i`-th strict transform of the image of `j`: the
image of `S_i ↪ X_i` is `(Π_i)⁻¹_* S`. -/
theorem ker_pullbackStageHom (S : BlowUpSequence X) (j : Y ⟶ X) [IsClosedImmersion j]
    (i : Fin (S.length + 1)) : (S.pullbackStageHom j i).ker = S.strictTransformSeq j.ker i := by
  obtain ⟨n, hn⟩ := i
  exact ker_pullbackStageHom_mk S j n hn

/-- The `i`-th stage of the restriction to `V(J)` is isomorphic to the strict transform
`S.strictTransformSeq J i`, the isomorphism followed by the strict transform's inclusion being the
natural embedding `pullbackStageHom` ([Kol07, 30.2], citing [Har77, Proposition II.7.15]). -/
theorem exists_iso_strictTransformSeq (S : BlowUpSequence X) (J : X.IdealSheafData)
    (i : Fin (S.length + 1)) :
    ∃ e : (S.pullback J.subschemeι).stage (S.pullbackStageIdx J.subschemeι i) ≅
        (S.strictTransformSeq J i).subscheme,
      e.hom ≫ (S.strictTransformSeq J i).subschemeι = S.pullbackStageHom J.subschemeι i := by
  have hci := isClosedImmersion_pullbackStageHom S J.subschemeι i
  have hker : (S.pullbackStageHom J.subschemeι i).ker = S.strictTransformSeq J i := by
    rw [ker_pullbackStageHom, Scheme.IdealSheafData.ker_subschemeι]
  rw [← hker]
  exact ⟨asIso (S.pullbackStageHom J.subschemeι i).toImage,
    (S.pullbackStageHom J.subschemeι i).toImage_imageι⟩

/-! ### Centers inside the strict transforms -/

/-- For a closed immersion `g : Y ⟶ X` whose kernel lies in `Z` (`V(Z) ⊆ Y`), the closed subscheme
of the inverse image ideal `Z.comap g` is `V(Z)` itself, compatibly with the inclusions into `X`:
the fibre product `V(Z) ×_X Y` is `V(Z)` (Mathlib's `isPullback_of_isClosedImmersion`). -/
theorem exists_iso_subscheme_comap_of_ker_le (g : Y ⟶ X) [IsClosedImmersion g]
    (Z : X.IdealSheafData) (hle : g.ker ≤ Z) :
    ∃ φ : (Z.comap g).subscheme ≅ Z.subscheme,
      φ.hom ≫ Z.subschemeι = (Z.comap g).subschemeι ≫ g := by
  have hle' : g.ker ≤ Z.subschemeι.ker := by rwa [Scheme.IdealSheafData.ker_subschemeι]
  have hfac : IsClosedImmersion.lift g Z.subschemeι hle' ≫ g = Z.subschemeι :=
    IsClosedImmersion.lift_fac g Z.subschemeι hle'
  have hpb : IsPullback (𝟙 Z.subscheme) (IsClosedImmersion.lift g Z.subschemeι hle')
      Z.subschemeι g :=
    isPullback_of_isClosedImmersion (𝟙 Z.subscheme) g _ Z.subschemeι
      (by rw [Category.id_comp, hfac])
      (by
        rw [Scheme.Hom.ker_eq_bot_of_isIso (𝟙 Z.subscheme), eq_bot_iff]
        calc g.ker.comap Z.subschemeι ≤ Z.comap Z.subschemeι :=
              Scheme.IdealSheafData.comap_mono Z.subschemeι hle
          _ = ⊥ := Scheme.IdealSheafData.comap_subschemeι_eq_bot Z)
  refine ⟨Z.comapIso g ≪≫ hpb.flip.isoPullback.symm, ?_⟩
  have h1 : hpb.flip.isoPullback.inv = Limits.pullback.snd g Z.subschemeι := by
    rw [← Category.comp_id hpb.flip.isoPullback.inv]
    exact hpb.flip.isoPullback_inv_snd
  rw [Iso.trans_hom, Iso.symm_hom, h1, Category.assoc, ← Limits.pullback.condition,
    ← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]

/-- If every center `Z_i` is a closed subscheme of the strict transform `S_i` of `V(J)` and `S` is
a smooth blow-up sequence, its restriction to `V(J)` is a smooth blow-up sequence on `V(J)`: the
restricted center `Z_i ∩ S_i` is `Z_i` itself (`exists_iso_subscheme_comap_of_ker_le` for the
stage lift, whose kernel is `S_i`). This is the situation of a hypersurface of maximal contact
[Kol07, Definition 78]. -/
theorem isSmooth_pullback_of_strictTransformSeq_le {k : Type u} [Field k] (S : BlowUpSequence X)
    (J : X.IdealSheafData) (f : X ⟶ Spec (.of k))
    (hZ : ∀ i : Fin S.length, S.strictTransformSeq J i.castSucc ≤ S.center i)
    (h : S.IsSmooth f) : (S.pullback J.subschemeι).IsSmooth (J.subschemeι ≫ f) := by
  intro i'
  obtain ⟨i, rfl⟩ : ∃ i : Fin S.length, i' = S.pullbackCenterIdx J.subschemeι i :=
    ⟨Fin.cast (length_pullback S J.subschemeι) i', Fin.ext rfl⟩
  rw [center_pullback]
  have hci := isClosedImmersion_pullbackStageHom S J.subschemeι i.castSucc
  have hle : (S.pullbackStageHom J.subschemeι i.castSucc).ker ≤ S.center i := by
    rw [ker_pullbackStageHom, Scheme.IdealSheafData.ker_subschemeι]
    exact hZ i
  obtain ⟨φ, hφ⟩ := exists_iso_subscheme_comap_of_ker_le
    (S.pullbackStageHom J.subschemeι i.castSucc) (S.center i) hle
  have hst : (S.pullback J.subschemeι).stageMap (S.pullbackCenterIdx J.subschemeι i).castSucc ≫
      J.subschemeι ≫ f =
        S.pullbackStageHom J.subschemeι i.castSucc ≫ S.stageMap i.castSucc ≫ f := by
    have hsq := pullbackStageHom_stageMap S J.subschemeι i.castSucc
    rw [← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ f) hsq.symm
  rw [hst, ← Category.assoc, ← hφ, Category.assoc]
  have := h i
  infer_instance

/-- For a closed immersion `g` and a closed subscheme `Z` of its image (`g.ker ≤ Z`), pushing the
restriction `Z ∩ g(Y)` forward gives `Z` back: `(Z.comap g).map g = Z`. The `IsIso` case is
`map_comap_of_isIso` (`Hironaka/Scheme/BlowUp/Glue/Trivial.lean`); this is the closed-immersion
form, through the isomorphism `exists_iso_subscheme_comap_of_ker_le`. -/
theorem map_comap_of_ker_le (g : Y ⟶ X) [IsClosedImmersion g] (Z : X.IdealSheafData)
    (hle : g.ker ≤ Z) : (Z.comap g).map g = Z := by
  obtain ⟨φ, hφ⟩ := exists_iso_subscheme_comap_of_ker_le g Z hle
  calc (Z.comap g).map g = ((Z.comap g).subschemeι ≫ g).ker := rfl
    _ = (φ.hom ≫ Z.subschemeι).ker := by rw [hφ]
    _ = Z.subschemeι.ker := Scheme.Hom.ker_comp_of_isIso _ _
    _ = Z := Scheme.IdealSheafData.ker_subschemeι Z

end AlgebraicGeometry
