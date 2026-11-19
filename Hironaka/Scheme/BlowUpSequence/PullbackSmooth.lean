/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Basic
import Hironaka.Scheme.BlowUp.BlowUpMapSquare
import Hironaka.Scheme.BlowUpSequence.Pullback
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The pullback of a smooth blow-up sequence is smooth

"If `B` is a smooth blow-up sequence then so is `h^* B`" [Kol07, 30.1]. The center `Z_i ×_X Y` of
the pulled-back sequence is `(Z_i).comap h_i` (`center_pullback`), and the closed subscheme
`V(Z.comap g)` is the base change of `V(Z)` along `g`: the square

  `V(Z.comap g) ⟶ Y`, `V(Z.comap g) ⟶ V(Z)`, `g : Y ⟶ X`, `V(Z) ⟶ X`

is cartesian (Mathlib's `isPullback_of_isClosedImmersion`). So the structure morphism of
`V(Z.comap g)` factors as the base change `V(Z.comap g) ⟶ V(Z)` of `g`, smooth when `g` is and of
the same relative dimension, followed by the structure morphism of `V(Z)`, and smoothness (and the
relative dimension, additively) follows by composition. Applied at every stage with `g = h_i`
(smooth by `smooth_pullbackStageHom`) this gives the statement in both forms, `IsSmooth` and
`IsSmoothOfRelativeDimension`; see also [Wlo05, Proposition 2.4.2 (1)].
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Limits Scheme BlowUpSequence

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- If `V(Z) → W` is smooth and `g` is smooth, then `V(Z.comap g) → W` through `g` is smooth: the
base change of `g` followed by the structure morphism of `V(Z)`. -/
theorem smooth_subschemeι_comap_comp {W : Scheme.{u}} (Z : X.IdealSheafData) (g : Y ⟶ X)
    [Smooth g] (φ : X ⟶ W) [Smooth (Z.subschemeι ≫ φ)] :
    Smooth ((Z.comap g).subschemeι ≫ g ≫ φ) := by
  have sq := isPullback_subschemeι_comap Z g
  have hψ : Smooth (Scheme.IdealSheafData.subschemeMap (Z.comap g) Z g
      (Scheme.IdealSheafData.le_map_comap Z g)) :=
    property_of_isPullback _ sq.flip inferInstance
  rw [← Category.assoc, sq.w, Category.assoc]
  infer_instance

/-- The equidimensional form: relative dimensions add along the factorisation through the base
change. -/
theorem smoothOfRelativeDimension_subschemeι_comap_comp {W : Scheme.{u}} (Z : X.IdealSheafData)
    (g : Y ⟶ X) {d : ℕ} [SmoothOfRelativeDimension d g] (φ : X ⟶ W) {e : ℕ}
    [SmoothOfRelativeDimension e (Z.subschemeι ≫ φ)] :
    SmoothOfRelativeDimension (d + e) ((Z.comap g).subschemeι ≫ g ≫ φ) := by
  have sq := isPullback_subschemeι_comap Z g
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{u} d
  have hψ : SmoothOfRelativeDimension d (Scheme.IdealSheafData.subschemeMap (Z.comap g) Z g
      (Scheme.IdealSheafData.le_map_comap Z g)) :=
    property_of_isPullback _ sq.flip inferInstance
  rw [← Category.assoc, sq.w, Category.assoc]
  exact smoothOfRelativeDimension_comp d e _ _

/-- The pullback along a smooth `h` of a sequence whose centers are smooth over `k` has centers
smooth over `k`: "if `B` is a smooth blow-up sequence then so is `h^* B`" [Kol07, 30.1]. -/
theorem IsSmooth.pullback (f : X ⟶ Spec (.of k)) (h : Y ⟶ X) [Smooth h] {S : BlowUpSequence X}
    (hS : S.IsSmooth f) : (S.pullback h).IsSmooth (h ≫ f) := by
  rintro ⟨j, hj⟩
  have hj' : j < S.length := by rwa [length_pullback] at hj
  have hc : (S.pullback h).center ⟨j, hj⟩ =
      (S.center ⟨j, hj'⟩).comap (S.pullbackStageHom h ⟨j, Nat.lt_succ_of_lt hj'⟩) :=
    center_pullback_mk S h j hj'
  have hm : (S.pullback h).stageMap (⟨j, hj⟩ : Fin (S.pullback h).length).castSucc ≫ h =
      S.pullbackStageHom h ⟨j, Nat.lt_succ_of_lt hj'⟩ ≫ S.stageMap ⟨j, Nat.lt_succ_of_lt hj'⟩ :=
    (pullbackStageHom_stageMap_mk S h j (Nat.lt_succ_of_lt hj')).symm
  rw [← Category.assoc ((S.pullback h).stageMap _) h f, hm, hc, Category.assoc]
  have hZ : Smooth ((S.center ⟨j, hj'⟩).subschemeι ≫ S.stageMap ⟨j, Nat.lt_succ_of_lt hj'⟩ ≫ f) :=
    hS ⟨j, hj'⟩
  have := smooth_pullbackStageHom S h ⟨j, Nat.lt_succ_of_lt hj'⟩
  exact smooth_subschemeι_comap_comp _ _ _

/-- The equidimensional form: for `h` smooth of relative dimension `d`, the pullback of a sequence
smooth of relative dimension `n` is smooth of relative dimension `n + d`, the codimensions of the
centers unchanged. -/
theorem IsSmoothOfRelativeDimension.pullback (f : X ⟶ Spec (.of k)) (h : Y ⟶ X) {d : ℕ}
    [SmoothOfRelativeDimension d h] {S : BlowUpSequence X} {n : ℕ}
    (hS : S.IsSmoothOfRelativeDimension f n) :
    (S.pullback h).IsSmoothOfRelativeDimension (h ≫ f) (n + d) := by
  have : Smooth h := SmoothOfRelativeDimension.smooth d h
  rintro ⟨j, hj⟩
  have hj' : j < S.length := by rwa [length_pullback] at hj
  obtain ⟨r, hr, hq⟩ := hS ⟨j, hj'⟩
  have hq' : SmoothOfRelativeDimension (n - r)
      ((S.center ⟨j, hj'⟩).subschemeι ≫ S.stageMap ⟨j, Nat.lt_succ_of_lt hj'⟩ ≫ f) := hq
  refine ⟨r, le_trans hr (Nat.le_add_right n d), ?_⟩
  have hc : (S.pullback h).center ⟨j, hj⟩ =
      (S.center ⟨j, hj'⟩).comap (S.pullbackStageHom h ⟨j, Nat.lt_succ_of_lt hj'⟩) :=
    center_pullback_mk S h j hj'
  have hm : (S.pullback h).stageMap (⟨j, hj⟩ : Fin (S.pullback h).length).castSucc ≫ h =
      S.pullbackStageHom h ⟨j, Nat.lt_succ_of_lt hj'⟩ ≫ S.stageMap ⟨j, Nat.lt_succ_of_lt hj'⟩ :=
    (pullbackStageHom_stageMap_mk S h j (Nat.lt_succ_of_lt hj')).symm
  rw [← Category.assoc ((S.pullback h).stageMap _) h f, hm, hc, Category.assoc]
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{u} d
  have hg : SmoothOfRelativeDimension d (S.pullbackStageHom h ⟨j, Nat.lt_succ_of_lt hj'⟩) :=
    property_of_isPullback _
      (isPullback_pullbackStageHom S h ⟨j, Nat.lt_succ_of_lt hj'⟩) inferInstance
  have key := smoothOfRelativeDimension_subschemeι_comap_comp (S.center ⟨j, hj'⟩)
    (S.pullbackStageHom h ⟨j, Nat.lt_succ_of_lt hj'⟩) (S.stageMap ⟨j, Nat.lt_succ_of_lt hj'⟩ ≫ f)
    (d := d) (e := n - r)
  have hnat : d + (n - r) = n + d - r := by omega
  rwa [hnat] at key

end AlgebraicGeometry
