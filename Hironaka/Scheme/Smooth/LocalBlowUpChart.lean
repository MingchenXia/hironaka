/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.BirationalTransform
public import Hironaka.Scheme.BlowUp.AffineBlowUp.Chart
public import Hironaka.Scheme.BlowUp.Defs
public import Hironaka.Scheme.IdealSheaf.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Membership
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Smooth.ChartRing
import Hironaka.Scheme.Smooth.LocalBlowUp
import Hironaka.Scheme.Smooth.LocalBlowUpStalk
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The stalks of `B_Z X` along the exceptional divisor are localizations of the chart ring

Kollár's proof of Lemma 61 "chooses local coordinates as above" at a point of the exceptional
divisor ([Kol07, Lemma 61]): in adapted parameters `y` at `z = π(q) ∈ Z` with `Z_z = (y_0, …, y_ρ)`,
the point `q` lies in the chart of some `y_j`, `j ≤ ρ`, of the local blow-up of `Spec 𝒪_{X,z}`
along `Z_z` (the cartesian square of `LocalBlowUp.lean`), whose stalks are those of `B_Z X`
(`LocalBlowUpStalk.lean`), and the chart is `Spec` of the affine blow-up algebra
`𝒪_{X,z}[Z_z/y_j]`, which is the chart ring `chartRing y' ρ` of Kollár's coordinates (60.2) once
the parameters are permuted so that `y_j` is the last center coordinate
(`affineBlowUpAlgebra_span_eq_chartRing`, `ChartRing.lean`). So `𝒪_{B,q}` is the localization of
the chart ring at a prime `𝔮` of the fibre over `𝔪_z`, compatibly with `π^♯`
(`exists_stalk_equiv_localization_chart`): the identification
`exists_stalk_equiv_localization_chartOrigin_of_isIso` at the origin of the chart, extended to
every point over `z` (Hauser's local blow-up at any point of the fibre, [Hau14, Definition 4.16]).

The steps: `hasChartData_of_chart` runs the identification from a given point of a chart instead
of its origin (the chart data packaged as the predicate `HasChartData`), `exists_hasChartData`
finds the chart of some generator `y_j` containing the point (the charts cover the affine
blow-up), and the main theorem permutes the parameters and identifies the algebra with `chartRing`
by two transports of the packaged data.

Used for the order of an ideal at a point of the exceptional divisor
(`Hironaka/Scheme/IdealSheaf/Order/Lemma61.lean`) and for the transform of a smooth center
(`Hironaka/Scheme/BlowUpSequence/SmoothCenter.lean`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory IsLocalRing Scheme.IdealSheafData

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The transposition of `j` and `ρ` preserves the initial segment `{i | i ≤ ρ}` when `j ≤ ρ`. -/
theorem image_swap_Iic {n : ℕ} {j ρ : Fin n} (hj : j ≤ ρ) :
    (Equiv.swap j ρ) '' {i | i ≤ ρ} = {i | i ≤ ρ} := by
  ext i
  constructor
  · rintro ⟨i', hi', rfl⟩
    change i' ≤ ρ at hi'
    change Equiv.swap j ρ i' ≤ ρ
    rw [Equiv.swap_apply_def]
    split_ifs
    · exact le_rfl
    · exact hj
    · exact hi'
  · intro hi
    change i ≤ ρ at hi
    refine ⟨Equiv.swap j ρ i, ?_, Equiv.swap_apply_self _ _ _⟩
    change Equiv.swap j ρ i ≤ ρ
    rw [Equiv.swap_apply_def]
    split_ifs
    · exact le_rfl
    · exact hj
    · exact hi

/-- The chart data at a point `q` of `B_Z X` over `x`, for a subalgebra `C ⊆ 𝒪_{X,x}[1/a]`: a prime
`𝔮` of `C` lying over `𝔪_x` and an isomorphism `𝒪_{B,q} ≅ C_𝔮` compatible with `π^♯` on germs.
(Packaged as a predicate so that the identifications of the generator and of the chart algebra are
cheap transports.) -/
def HasChartData (Z : X.IdealSheafData) (x : X) (q : blowUp Z) (a : X.presheaf.stalk x)
    (C : Subalgebra (X.presheaf.stalk x) (Localization.Away a)) : Prop :=
  ∃ (𝔮 : Ideal C) (_ : 𝔮.IsPrime),
    maximalIdeal (X.presheaf.stalk x) ≤ 𝔮.comap (algebraMap (X.presheaf.stalk x) C) ∧
      ∃ e : (blowUp Z).presheaf.stalk q ≃+* Localization.AtPrime 𝔮,
        ∀ (V : X.Opens) (hxV : x ∈ V) (hV : blowUpπ Z q ∈ V) (s : Γ(X, V)),
          e ((blowUpπ Z).stalkMap q (X.presheaf.germ V (blowUpπ Z q) hV s)) =
            algebraMap C (Localization.AtPrime 𝔮)
              (algebraMap (X.presheaf.stalk x) C (X.presheaf.germ V x hxV s))

/-- The chart data at a chart point of the local blow-up (the identification of `LocalBlowUp.lean`
run from a given point of the chart instead of its origin): for a point `p` of the chart of `a`
lying over `𝔪_x`, `𝒪_{B,φ(chart p)}` is the localization of the affine blow-up algebra at `p`. -/
theorem hasChartData_of_chart (Z : X.IdealSheafData) {x : X}
    (φ : affineBlowUp (Z.stalkIdeal x) ⟶ blowUp Z)
    (H : IsPullback φ (affineBlowUp.π (Z.stalkIdeal x)) (blowUpπ Z) (X.fromSpecStalk x))
    (a : Z.stalkIdeal x) (p : Spec (.of (affineBlowUpAlgebra (Z.stalkIdeal x) a)))
    (hp : Spec.map (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x) (affineBlowUpAlgebra (Z.stalkIdeal x) a))) p =
      closedPoint (X.presheaf.stalk x)) :
    HasChartData Z x (φ (affineBlowUp.chart (Z.stalkIdeal x) a p)) a
      (affineBlowUpAlgebra (Z.stalkIdeal x) a) := by
  classical
  let q := affineBlowUp.chart (Z.stalkIdeal x) a p
  have hcomap : (PrimeSpectrum.asIdeal p).comap
      (algebraMap (X.presheaf.stalk x) (affineBlowUpAlgebra (Z.stalkIdeal x) a)) =
      maximalIdeal (X.presheaf.stalk x) := by
    have := congrArg PrimeSpectrum.asIdeal hp
    rw [Spec.map_apply] at this
    exact this
  have hq_iso := isIso_stalkMap_of_isPullback_fromSpecStalk H q
  obtain ⟨e₁, he₁⟩ := exists_ringEquiv_stalk_chart (Z.stalkIdeal x) a p
  let E : (blowUp Z).presheaf.stalk (φ q) ≃+* (affineBlowUp (Z.stalkIdeal x)).presheaf.stalk q :=
    RingEquiv.ofBijective (φ.stalkMap q).hom (ConcreteCategory.bijective_of_isIso _)
  refine ⟨PrimeSpectrum.asIdeal p, PrimeSpectrum.isPrime p, le_of_eq hcomap.symm, E.trans e₁, ?_⟩
  intro V hxV hV s
  have hV' : (φ ≫ blowUpπ Z) q ∈ V := hV
  have hg := stalkMap_germ_eq_of_eq_comp_fromSpecStalk x (φ ≫ blowUpπ Z) H.w q V hxV hV' s
  have h1 : φ.stalkMap q ((blowUpπ Z).stalkMap (φ q)
        (X.presheaf.germ V (blowUpπ Z (φ q)) hV s)) =
      (φ ≫ blowUpπ Z).stalkMap q (X.presheaf.germ V ((φ ≫ blowUpπ Z) q) hV' s) := by
    rw [Scheme.Hom.stalkMap_comp]
    rfl
  have h2 := stalkMap_chart_stalkMap_π (Z.stalkIdeal x) a p
    (X.presheaf.germ V x hxV s)
  have h3 := he₁ (algebraMap _ _ (X.presheaf.germ V x hxV s))
  have hinj := (ConcreteCategory.bijective_of_isIso
    ((affineBlowUp.chart (Z.stalkIdeal x) a).stalkMap p)).1
  have h4 : (affineBlowUp.π (Z.stalkIdeal x)).stalkMap q
        ((Spec (X.presheaf.stalk x)).presheaf.germ ⊤ (affineBlowUp.π (Z.stalkIdeal x) q) trivial
          ((Scheme.ΓSpecIso (X.presheaf.stalk x)).inv (X.presheaf.germ V x hxV s))) =
      e₁.symm (algebraMap _ _ (algebraMap _ _ (X.presheaf.germ V x hxV s))) :=
    hinj (h2.trans h3.symm)
  have h5 : E ((blowUpπ Z).stalkMap (φ q) (X.presheaf.germ V (blowUpπ Z (φ q)) hV s)) =
      φ.stalkMap q ((blowUpπ Z).stalkMap (φ q)
        (X.presheaf.germ V (blowUpπ Z (φ q)) hV s)) := rfl
  -- `rw` along this chain times out (keyed matching against the stalk terms); compose the
  -- equalities explicitly instead (as in `LocalBlowUp.lean`).
  change (E.trans e₁) ((blowUpπ Z).stalkMap (φ q)
      (X.presheaf.germ V (blowUpπ Z (φ q)) hV s)) =
    algebraMap _ _ (algebraMap _ _ (X.presheaf.germ V x hxV s))
  exact (RingEquiv.trans_apply _ _ _).trans
    ((congrArg e₁ ((h5.trans h1).trans (hg.trans h4))).trans (e₁.apply_symm_apply _))

/-- The chart at a point of the fibre: for `q ∈ B_Z X` over `x` and adapted parameters `y` with
`Z_x = (y_0, …, y_ρ)`, the point `q` lies in the chart of some `y_j`, `j ≤ ρ`, of the local
blow-up (the charts cover the affine blow-up), and the chart data of `hasChartData_of_chart` hold
there. -/
theorem exists_hasChartData (Z : X.IdealSheafData) {x : X} {n' : ℕ}
    (y : Fin n' → X.presheaf.stalk x) (ρ : Fin n') (hZ : Z.stalkIdeal x = chartCenter y ρ)
    (q : blowUp Z) (hq : blowUpπ Z q = x) :
    ∃ j : Fin n', j ≤ ρ ∧
      HasChartData Z x q (y j) (affineBlowUpAlgebra (Z.stalkIdeal x) (y j)) := by
  classical
  obtain ⟨φ, H⟩ := exists_isPullback_fromSpecStalk Z x
  have hqx : blowUpπ Z q = X.fromSpecStalk x (closedPoint (X.presheaf.stalk x)) := by
    rw [hq, Scheme.fromSpecStalk_closedPoint]
  obtain ⟨q', hq'φ, hq'π⟩ := Scheme.exists_preimage_of_isPullback H q (closedPoint _) hqx
  subst hq'φ
  obtain ⟨⟨a, ha⟩, hmem⟩ := affineBlowUp.exists_mem_opensRange_chart_of_span_eq
    (Z.stalkIdeal x) (y '' {i | i ≤ ρ}) hZ.symm q'
  obtain ⟨j, hj, rfl⟩ := ha
  obtain ⟨p, hp⟩ := hmem
  subst hp
  have hclosed : Spec.map (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x) (affineBlowUpAlgebra (Z.stalkIdeal x) (y j)))) p =
      closedPoint (X.presheaf.stalk x) := by
    have h : (affineBlowUp.chart (Z.stalkIdeal x) _ ≫ affineBlowUp.π (Z.stalkIdeal x)) p =
        closedPoint (X.presheaf.stalk x) := hq'π
    rwa [affineBlowUp.chart_π] at h
  exact ⟨j, hj, hasChartData_of_chart Z φ H _ p hclosed⟩

/-- The identification with PRESCRIBED adapted parameters: at `q ∈ B_Z X` over `z = π(q)`, for any
`y` with `Z_z = (y_0, …, y_ρ) = chartCenter y ρ`, the point `q` lies in the chart of some `y_j`,
`j ≤ ρ`, and after the transposition `(j ρ)`, which keeps the center, `𝒪_{B,q}` is the
localization of the chart ring `𝒪_{X,z}[y_i/y_j]` at a prime `𝔮` lying over `𝔪_z`, compatibly
with `π^♯`. -/
theorem exists_stalk_equiv_localization_chart_of_chartCenter (Z : X.IdealSheafData) (q : blowUp Z)
    {n' : ℕ} (y : Fin n' → X.presheaf.stalk (blowUpπ Z q)) (ρ : Fin n')
    (hZ : Z.stalkIdeal (blowUpπ Z q) = chartCenter y ρ) :
    ∃ j : Fin n', j ≤ ρ ∧
      Z.stalkIdeal (blowUpπ Z q) = chartCenter (y ∘ Equiv.swap j ρ) ρ ∧
      ∃ (𝔮 : Ideal (chartRing (y ∘ Equiv.swap j ρ) ρ)) (_ : 𝔮.IsPrime),
        maximalIdeal (X.presheaf.stalk (blowUpπ Z q)) ≤
            𝔮.comap (algebraMap (X.presheaf.stalk (blowUpπ Z q))
              (chartRing (y ∘ Equiv.swap j ρ) ρ)) ∧
          ∃ e : (blowUp Z).presheaf.stalk q ≃+* Localization.AtPrime 𝔮,
            ∀ c : X.presheaf.stalk (blowUpπ Z q),
              e ((blowUpπ Z).stalkMap q c) =
                algebraMap (chartRing (y ∘ Equiv.swap j ρ) ρ) (Localization.AtPrime 𝔮)
                  (algebraMap (X.presheaf.stalk (blowUpπ Z q))
                    (chartRing (y ∘ Equiv.swap j ρ) ρ) c) := by
  classical
  obtain ⟨j, hj, h⟩ := exists_hasChartData Z y ρ hZ q rfl
  -- permute the parameters so that the chart of `y j` is the chart of the last center coordinate
  have hyρ : (y ∘ Equiv.swap j ρ) ρ = y j := by
    change y (Equiv.swap j ρ ρ) = y j
    rw [Equiv.swap_apply_right]
  have hZ'' : Z.stalkIdeal (blowUpπ Z q) = chartCenter (y ∘ Equiv.swap j ρ) ρ := by
    rw [hZ, chartCenter, chartCenter, Set.image_comp, image_swap_Iic hj]
  -- the generator `y j` is `(y ∘ swap) ρ`, and the affine blow-up algebra is the chart ring
  -- (`affineBlowUpAlgebra_span_eq_chartRing`): two cheap transports of the packaged chart data
  have h1 : HasChartData Z (blowUpπ Z q) q ((y ∘ Equiv.swap j ρ) ρ)
      (affineBlowUpAlgebra (Z.stalkIdeal (blowUpπ Z q)) ((y ∘ Equiv.swap j ρ) ρ)) :=
    hyρ.symm ▸ h
  have hC : affineBlowUpAlgebra (Z.stalkIdeal (blowUpπ Z q)) ((y ∘ Equiv.swap j ρ) ρ) =
      chartRing (y ∘ Equiv.swap j ρ) ρ := by
    rw [hZ'']
    exact affineBlowUpAlgebra_span_eq_chartRing (y ∘ Equiv.swap j ρ) ρ
  have h2 : HasChartData Z (blowUpπ Z q) q ((y ∘ Equiv.swap j ρ) ρ)
      (chartRing (y ∘ Equiv.swap j ρ) ρ) := hC ▸ h1
  obtain ⟨𝔮, hprime, hle, e, he⟩ := h2
  refine ⟨j, hj, hZ'', 𝔮, hprime, hle, e, fun c => ?_⟩
  obtain ⟨V, hV, s, rfl⟩ := X.presheaf.exists_germ_eq c
  exact he V hV hV s

/-- At a point `q` of `B_Z X` over `z ∈ Z`, for suitable adapted parameters `y` at `z` with
`Z_z = (y_0, …, y_ρ)`, the stalk `𝒪_{B,q}` is the localization of the chart ring `𝒪_{X,z}[y_i/y_ρ]`
at a prime `𝔮` lying over `𝔪_z`, compatibly with `π^♯` ("choose local coordinates as above", the
proof of [Kol07, Lemma 61]; Hauser's local blow-up, [Hau14, Definition 4.16]). -/
theorem exists_stalk_equiv_localization_chart {k : Type u} [Field k] [CharZero k]
    (f : X ⟶ Spec (.of k)) (n r : ℕ) [SmoothOfRelativeDimension n f] (Z : X.IdealSheafData)
    [SmoothOfRelativeDimension (n - r) (Z.subschemeι ≫ f)] (hrn : r ≤ n) (q : blowUp Z)
    (hq : blowUpπ Z q ∈ Z.support) :
    ∃ (n' : ℕ) (y : Fin n' → X.presheaf.stalk (blowUpπ Z q)) (ρ : Fin n'),
      (n' : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk (blowUpπ Z q)) ∧
      maximalIdeal (X.presheaf.stalk (blowUpπ Z q)) = Ideal.span (Set.range y) ∧
      Z.stalkIdeal (blowUpπ Z q) = chartCenter y ρ ∧
      ∃ (𝔮 : Ideal (chartRing y ρ)) (_ : 𝔮.IsPrime),
        maximalIdeal (X.presheaf.stalk (blowUpπ Z q)) ≤
            𝔮.comap (algebraMap (X.presheaf.stalk (blowUpπ Z q)) (chartRing y ρ)) ∧
          ∃ e : (blowUp Z).presheaf.stalk q ≃+* Localization.AtPrime 𝔮,
            ∀ c : X.presheaf.stalk (blowUpπ Z q),
              e ((blowUpπ Z).stalkMap q c) =
                algebraMap (chartRing y ρ) (Localization.AtPrime 𝔮)
                  (algebraMap (X.presheaf.stalk (blowUpπ Z q)) (chartRing y ρ) c) := by
  classical
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hsm' : Smooth (Z.subschemeι ≫ f) := SmoothOfRelativeDimension.smooth (n - r) _
  obtain ⟨n', y, hn', hy, hZ⟩ := exists_adaptedParameters Z f n r hrn hq
  -- a point of the local blow-up over `q`, for the degenerate cases
  obtain ⟨φ, H⟩ := exists_isPullback_fromSpecStalk Z (blowUpπ Z q)
  obtain ⟨q', -, -⟩ := Scheme.exists_preimage_of_isPullback H q (closedPoint _)
    (by rw [Scheme.fromSpecStalk_closedPoint])
  have hZbot : Z.stalkIdeal (blowUpπ Z q) = ⊥ → False := by
    intro hZ0
    have : IsEmpty (affineBlowUp (Z.stalkIdeal (blowUpπ Z q))) := by
      rw [hZ0]
      exact affineBlowUp.isEmpty_bot
    exact this.false q'
  have hn0 : 0 < n' := by
    rcases Nat.eq_zero_or_pos n' with h0 | h0
    · exfalso
      subst h0
      apply hZbot
      rw [hZ, Set.eq_empty_of_isEmpty ({j : Fin 0 | j.val < r}), Set.image_empty, Ideal.span_empty]
    · exact h0
  have hr0 : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · exfalso
      subst h0
      apply hZbot
      have hemp : {j : Fin n' | j.val < 0} = ∅ := by
        ext j
        simp
      rw [hZ, hemp, Set.image_empty, Ideal.span_empty]
    · exact h0
  let ρ : Fin n' := ⟨min (r - 1) (n' - 1), by omega⟩
  have hset : {j : Fin n' | j.val < r} = {j | j ≤ ρ} := by
    ext j
    change j.val < r ↔ j ≤ ρ
    rw [Fin.le_def]
    change j.val < r ↔ j.val ≤ min (r - 1) (n' - 1)
    have := j.2
    omega
  have hZ' : Z.stalkIdeal (blowUpπ Z q) = chartCenter y ρ := by
    rw [hZ, hset]
    rfl
  obtain ⟨j, hj, hZ'', 𝔮, hprime, hle, e, he⟩ :=
    exists_stalk_equiv_localization_chart_of_chartCenter Z q y ρ hZ'
  have hrange : Set.range (y ∘ Equiv.swap j ρ) = Set.range y := by
    rw [Set.range_comp, (Equiv.swap j ρ).surjective.range_eq, Set.image_univ]
  exact ⟨n', y ∘ Equiv.swap j ρ, ρ, hn', by rw [hy, hrange], hZ'', 𝔮, hprime, hle, e, he⟩

end AlgebraicGeometry
