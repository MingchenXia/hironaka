/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MaximalContact.FormalEquiv
public import Hironaka.Resolution.Algebraic.MaximalContact.Invariant
public import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
public import Hironaka.Scheme.Smooth.GraphFormal
import Hironaka.Algebra.Local.CoefficientFieldUnique
import Hironaka.Algebra.Local.PowerSeriesEndomorphism
import Hironaka.Algebra.Local.RegularSystemCommon
import Hironaka.Resolution.Algebraic.MaximalContact.CompletionIdealMap
import Hironaka.Resolution.Algebraic.MaximalContact.EtaleToFormal
import Hironaka.Resolution.Algebraic.MaximalContact.FormalEquivBridge
import Hironaka.Resolution.Algebraic.MaximalContact.FormalEquivExists
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The completion of `U₁(p)` at `(p, p)` is the graph of `φₚ`

The sentence of [Kol07, 95] "The completion of `U₁(p)` at `(p, p)` is the graph of `φₚ`", made
precise for an étale neighbourhood pair `ψ, ψ' : W ⇉ X` of the graph of the two coordinate
systems: the automorphism `φ := (ψ̂^*)⁻¹ ∘ ψ̂'^*` of `Ô_{X,p}` (`EtaleNbhdPair.formalAutomorphism`,
inverted) satisfies the conditions (91.1)–(91.4) of [Kol07, Definition 91], so it is the
automorphism of the formal half of Theorem 92
(`Hironaka/Resolution/Algebraic/MaximalContact/FormalEquivExists.lean`) and the completed graph is
its graph. This is the step of the proof of Theorem 92
(`Hironaka/Resolution/Algebraic/MaximalContact/Theorem92.lean`) that passes from the formal
automorphism to the étale neighbourhood.

## The coefficient field

The first ingredient is the uniqueness of the `k`-linear coefficient field of `Ô_{X,p}` at a
closed point (`coefficientField_ext`): `κ(p)/k` is algebraic, hence separable in characteristic
zero and formally unramified, and `Ô_{X,p}` is a Noetherian local ring, so
`IsLocalRing.algHom_ext_of_residue_eq` applies. This is what pins a residue-trivial
`k`-automorphism of `Ô_{X,p} ≅ κ(p)⟦X⟧` by its values on the coordinates: it must fix the
coefficient field, hence is `κ(p)`-linear on the chart. `k`-linearity alone would not pin it: an
automorphism of `κ(p)` over `k` applied to the coefficients is `k`-linear, fixes the coordinates
and is not the identity.
-/

public section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

open CategoryTheory IsLocalRing Scheme Hironaka.Local AlgebraicGeometry

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f]

/-- The maximal-adic completion of a local ring ([Kol07, Definition 55]). -/
local notation "Ô(" R ")" => AdicCompletion (maximalIdeal R) R

include n in
/-- Uniqueness of the field of representatives over `k` (the subfield `k' ⊂ Ô_{p,X}` of
[Kol07, Definition 55]): two `k`-algebra homomorphisms `κ(p) → Ô_{X,p}` at a closed point `p` with
the same residue composite are equal. `κ(p)/k` is algebraic
(`isAlgebraic_residueField_of_isClosed`), hence separable and formally unramified in characteristic
zero, and `Ô_{X,p}` is Noetherian local: `IsLocalRing.algHom_ext_of_residue_eq`. -/
theorem coefficientField_ext {p : X} (hpc : IsClosed ({p} : Set X))
    (σ₁ σ₂ : letI := f.stalkAlgebra p
      ResidueField (X.presheaf.stalk p) →ₐ[k] Ô(X.presheaf.stalk p))
    (h : haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
      haveI : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
      ∀ a, IsLocalRing.residue Ô(X.presheaf.stalk p) (σ₁ a) =
        IsLocalRing.residue Ô(X.presheaf.stalk p) (σ₂ a)) :
    σ₁ = σ₂ := by
  let _ := f.stalkAlgebra p
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
  have : Algebra.IsAlgebraic k (ResidueField (X.presheaf.stalk p)) :=
    isAlgebraic_residueField_of_isClosed f n hpc
  have : PerfectField k := PerfectField.ofCharZero
  have : Algebra.IsSeparable k (ResidueField (X.presheaf.stalk p)) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have := Algebra.FormallyUnramified.of_isSeparable k (ResidueField (X.presheaf.stalk p))
  exact algHom_ext_of_residue_eq σ₁ σ₂ h


include n in
/-- Kollár's "The completion of `U₁(p)` at `(p, p)` is the graph of `φₚ`" ([Kol07, 95]): for a
closed point `p` of `cosupp(I, m)`, `m ≥ 1`, `I` MC-invariant, coordinates `x₁, x₁' ∈ MC(I)_p` with
`H_p = (x₁)`, `H'_p = (x₁')`, `(x₁', y)` a regular system and every `Eⁱ` through `p` equal to
`(y_j)`, and an étale neighbourhood pair `Q` of `p` over `k` with `ψ^*(s) − ψ'^*(s) ∈ 𝔪_q` and the
graph equations `ψ^*((x₁, y)ᵢ) = ψ'^*((x₁', y)ᵢ)`, the automorphism `φ := θ⁻¹ = (ψ̂^*)⁻¹ ∘ ψ̂'^*` of
`Ô_{X,p}` satisfies (91.1)–(91.4). Proof: `φ` is `k`-linear, sends `x̂₁' ↦ x̂₁` and `ŷⱼ ↦ ŷⱼ` (the
graph equations through `ψ̂^*`, `ψ̂'^*`), and is trivial modulo `𝔪̂` (the residue condition,
completed), hence fixes the `k`-linear coefficient field of the chart `Φ'` of `(x₁', y)`
(`coefficientField_ext`); on the chart it is therefore a `κ(p)`-substitution
`X₀ ↦ X₀ + Φ'⁻¹(x̂₁ − x̂₁')`, `Xᵢ ↦ Xᵢ`, of the form `1 + Φ'⁻¹(\widehat{MC(I)})`, the shape of
`exists_formalAutomorphism`; (91.2) is then `map_comap_completionIdeal_eq_of_isOnePlus`
([Kol07, Proposition 94]), (91.4) the calculus of substitutions `1 + B`, (91.1) and (91.3)
`map_completionIdeal_eq_of_stalkIdeal_eq_span`. -/
theorem conditions_formalAutomorphism_symm (I : X.IdealSheafData) {m : ℕ} (hm : 1 ≤ m)
    (hI : IsMCInvariant f I m) (E : DivisorFamily X) (H H' : X.IdealSheafData) {p : X}
    (hpc : IsClosed ({p} : Set X)) (hp : (m : ℕ∞) ≤ I.ord p) {d : ℕ}
    (x₁ x₁' : X.presheaf.stalk p) (y : Fin d → X.presheaf.stalk p)
    (hx₁ : x₁ ∈ (MC f I m).stalkIdeal p) (hx₁' : x₁' ∈ (MC f I m).stalkIdeal p)
    (hH : H.stalkIdeal p = Ideal.span {x₁}) (hH' : H'.stalkIdeal p = Ideal.span {x₁'})
    (hz' : IsRegularSystemOfParameters (Fin.cons x₁' y))
    (hE : ∀ i, p ∈ (E.component i).support →
      ∃ j, (E.component i).stalkIdeal p = Ideal.span {y j})
    (Q : EtaleNbhdPair X p) (hf : Q.ψ ≫ f = Q.ψ' ≫ f)
    (hres : ∀ s, Q.stalkHom s - Q.stalkHom' s ∈ maximalIdeal (Q.W.presheaf.stalk Q.q))
    (hQ : ∀ i, Q.stalkHom ((Fin.cons x₁ y : Fin (d + 1) → X.presheaf.stalk p) i) =
      Q.stalkHom' ((Fin.cons x₁' y : Fin (d + 1) → X.presheaf.stalk p) i))
    (ha : Function.Bijective (completionMap Q.stalkHom))
    (ha' : Function.Bijective (completionMap Q.stalkHom')) :
    (H'.completionIdeal p).map (Q.formalAutomorphism ha ha').symm = H.completionIdeal p ∧
    (I.completionIdeal p).map (Q.formalAutomorphism ha ha').symm = I.completionIdeal p ∧
    (∀ i, ((E.component i).completionIdeal p).map (Q.formalAutomorphism ha ha').symm =
      (E.component i).completionIdeal p) ∧
    ∀ h, h - (Q.formalAutomorphism ha ha').symm h ∈ (MC f I m).completionIdeal p := by
  classical
  let _ := f.stalkAlgebra p
  let _ := f.stalkAlgebraRat p
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hloc : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
  have hlocW : IsLocallyNoetherian Q.W := LocallyOfFiniteType.isLocallyNoetherian Q.ψ
  have hreg := isRegularLocalRing_stalk f p
  set ι := algebraMap (X.presheaf.stalk p) Ô(X.presheaf.stalk p) with hι
  -- `θ` on the coordinates: `θ(x̂₁) = x̂₁'`, `θ(ŷⱼ) = ŷⱼ` (the graph equations)
  have hθz : ∀ i, Q.formalAutomorphism ha ha' (ι ((Fin.cons x₁ y : Fin (d + 1) → _) i)) =
      ι ((Fin.cons x₁' y : Fin (d + 1) → _) i) := fun i => by
    apply ha'.1
    rw [Q.completionMap_stalkHom'_formalAutomorphism, hι, completionMap_algebraMap,
      completionMap_algebraMap, hQ i]
  have hφz : ∀ i, (Q.formalAutomorphism ha ha').symm (ι ((Fin.cons x₁' y : Fin (d + 1) → _) i)) =
      ι ((Fin.cons x₁ y : Fin (d + 1) → _) i) := fun i => by
    rw [RingEquiv.symm_apply_eq]
    exact (hθz i).symm
  have hφx₁ : (Q.formalAutomorphism ha ha').symm (ι x₁') = ι x₁ := by
    have := hφz 0
    rwa [Fin.cons_zero, Fin.cons_zero] at this
  have hφy : ∀ j : Fin d, (Q.formalAutomorphism ha ha').symm (ι (y j)) = ι (y j) := fun j => by
    have := hφz j.succ
    rwa [Fin.cons_succ, Fin.cons_succ] at this
  -- `θ ≡ 1` modulo `𝔪̂` (the residue condition, completed)
  have hθres : ∀ x, Q.formalAutomorphism ha ha' x - x ∈ maximalIdeal Ô(X.presheaf.stalk p) := by
    intro x
    obtain ⟨s, hs⟩ := exists_sub_algebraMap_mem_maximalIdeal_pow x 1
    have key : completionMap Q.stalkHom' (Q.formalAutomorphism ha ha' x - x) ∈
        maximalIdeal (AdicCompletion (maximalIdeal (Q.W.presheaf.stalk Q.q))
          (Q.W.presheaf.stalk Q.q)) := by
      rw [map_sub, Q.completionMap_stalkHom'_formalAutomorphism]
      have e1 : completionMap Q.stalkHom x - completionMap Q.stalkHom' x =
          algebraMap _ _ (Q.stalkHom s - Q.stalkHom' s) +
            (completionMap Q.stalkHom (x - ι s) - completionMap Q.stalkHom' (x - ι s)) := by
        rw [map_sub, map_sub, map_sub, hι, completionMap_algebraMap, completionMap_algebraMap]
        ring
      rw [e1]
      refine Ideal.add_mem _ ?_ (Ideal.sub_mem _ ?_ ?_)
      · rw [AdicCompletion.maximalIdeal_eq_map]
        exact Ideal.mem_map_of_mem _ (hres s)
      · have := completionMap_mem_maximalIdeal_pow (φ := Q.stalkHom) hs
        rwa [pow_one] at this
      · have := completionMap_mem_maximalIdeal_pow (φ := Q.stalkHom') hs
        rwa [pow_one] at this
    rw [mem_maximalIdeal, mem_nonunits_iff] at key ⊢
    exact fun hu => key ((isUnit_map_iff (completionMap Q.stalkHom') _).mpr hu)
  have hφres : ∀ x, (Q.formalAutomorphism ha ha').symm x - x ∈
      maximalIdeal Ô(X.presheaf.stalk p) := fun x => by
    have := hθres ((Q.formalAutomorphism ha ha').symm x)
    rw [RingEquiv.apply_symm_apply] at this
    rw [← neg_sub]
    exact neg_mem_iff.mpr this
  -- the chart of `(x₁', y)`, with coordinates adapted to it
  obtain ⟨c', hc'x, hk', hs'⟩ := exists_regularCoords_eq f n hpc (Fin.cons x₁' y) hz'
  obtain ⟨σ, hσ⟩ := exists_coefficientField_over (X.presheaf.stalk p) k
  set Φ' := cohenAlgEquivCoords c' σ hσ with hΦ'
  have hΦ'X : ∀ i, Φ' (MvPowerSeries.X i) = ι ((Fin.cons x₁' y : Fin (d + 1) → _) i) := fun i => by
    rw [hΦ', cohenAlgEquivOver_X, hc'x]
  have hΦ'C : ∀ a, IsLocalRing.residue Ô(X.presheaf.stalk p) (Φ' (MvPowerSeries.C a)) =
      residueFieldEquiv (X.presheaf.stalk p) a := fun a => by
    rw [hΦ', residue_cohenAlgEquivOver_C]
  have hΦ'Ca : ∀ a, Φ' (MvPowerSeries.C a) = σ a := fun a => by
    rw [hΦ', cohenAlgEquivOver_C]
  -- `φ` as a `k`-algebra automorphism, fixing the coefficient field `σ`
  let φₐ : Ô(X.presheaf.stalk p) ≃ₐ[k] Ô(X.presheaf.stalk p) :=
    AlgEquiv.ofRingEquiv (f := (Q.formalAutomorphism ha ha').symm)
      (Q.formalAutomorphism_symm_algebraMap f hf ha ha')
  have hφₐ : ∀ x, φₐ x = (Q.formalAutomorphism ha ha').symm x := fun _ => rfl
  have hσφ : (φₐ : Ô(X.presheaf.stalk p) →ₐ[k] Ô(X.presheaf.stalk p)).comp σ = σ := by
    refine coefficientField_ext f n hpc _ _ fun a => ?_
    exact Ideal.Quotient.eq.mpr (hφres (σ a))
  have hφσ : ∀ a, φₐ (σ a) = σ a := fun a => AlgHom.congr_fun hσφ a
  -- `g := Φ'⁻¹ ∘ φ ∘ Φ'` on the chart: a `κ(p)`-algebra automorphism
  set g₀ := (Φ'.trans φₐ).trans Φ'.symm with hg₀
  have hg₀apply : ∀ F, g₀ F = Φ'.symm (φₐ (Φ' F)) := fun F => by
    rw [hg₀, AlgEquiv.trans_apply, AlgEquiv.trans_apply]
  have hg₀C : ∀ a, g₀ (MvPowerSeries.C a) = MvPowerSeries.C a := fun a => by
    rw [hg₀apply, hΦ'Ca, hφσ, AlgEquiv.symm_apply_eq, hΦ'Ca]
  have hg₀X : ∀ i, g₀ (MvPowerSeries.X i) = Φ'.symm (ι ((Fin.cons x₁ y : Fin (d + 1) → _) i)) :=
    fun i => by rw [hg₀apply, hΦ'X, hφₐ, hφz]
  let g : MvPowerSeries (Fin (d + 1)) (ResidueField (X.presheaf.stalk p))
      ≃ₐ[ResidueField (X.presheaf.stalk p)]
        MvPowerSeries (Fin (d + 1)) (ResidueField (X.presheaf.stalk p)) :=
    AlgEquiv.ofRingEquiv (f := g₀.toRingEquiv) fun a => by
      change g₀ (algebraMap _ _ a) = algebraMap _ _ a
      rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      exact hg₀C a
  have hgapply : ∀ F, g F = g₀ F := fun F => rfl
  have hφapply : ∀ h, (Q.formalAutomorphism ha ha').symm h = Φ' (g (Φ'.symm h)) := fun h => by
    rw [hgapply, hg₀apply, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, hφₐ]
  have hX0 : Φ'.symm (ι x₁') = MvPowerSeries.X 0 := by
    rw [AlgEquiv.symm_apply_eq, hΦ'X 0, Fin.cons_zero]
  have hXsucc : ∀ i : Fin d, Φ'.symm (ι (y i)) = MvPowerSeries.X i.succ := fun i => by
    rw [AlgEquiv.symm_apply_eq, hΦ'X i.succ, Fin.cons_succ]
  have hgX0 : g (MvPowerSeries.X 0) = MvPowerSeries.X 0 + Φ'.symm (ι (x₁ - x₁')) := by
    rw [hgapply, hg₀X, Fin.cons_zero, ← hX0, ← map_add, ← map_add]
    congr 2
    ring
  have hgXsucc : ∀ i : Fin d, g (MvPowerSeries.X i.succ) = MvPowerSeries.X i.succ := fun i => by
    rw [hgapply, hg₀X, Fin.cons_succ, hXsucc]
  -- the variables go into `𝔪`: `x₁ ∈ MC(I)_p ⊆ 𝔪_p`, `yⱼ ∈ 𝔪_p`
  have hx₁m : ι x₁ ∈ maximalIdeal Ô(X.presheaf.stalk p) :=
    completionIdeal_MC_le_maximalIdeal f n I m hm hp
      (by rw [completionIdeal_eq]; exact Ideal.mem_map_of_mem _ hx₁)
  have hgmem : ∀ i, g (MvPowerSeries.X i) ∈
      maximalIdeal (MvPowerSeries (Fin (d + 1)) (ResidueField (X.presheaf.stalk p))) := fun i => by
    rw [hgapply, hg₀X, symm_mem_maximalIdeal_iff f n]
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [Fin.cons_zero]; exact hx₁m
    · rw [Fin.cons_succ]
      exact algebraMap_mem_maximalIdeal_adicCompletion f n
        (by simpa using mem_maximalIdeal_of_eq_span hz'.1.symm j.succ)
  let gA : MvPowerSeries (Fin (d + 1)) (ResidueField (X.presheaf.stalk p))
      →ₐ[ResidueField (X.presheaf.stalk p)]
        MvPowerSeries (Fin (d + 1)) (ResidueField (X.presheaf.stalk p)) := g
  have hgAmem : ∀ i, gA (MvPowerSeries.X i) ∈
      maximalIdeal (MvPowerSeries (Fin (d + 1)) (ResidueField (X.presheaf.stalk p))) := hgmem
  -- the form `1 + Φ'⁻¹(MC(I)^)`
  set B := ((MC f I m).completionIdeal p).comap Φ' with hB
  have hg : IsOnePlus B g := by
    refine ⟨⟨fun i => gA (MvPowerSeries.X i), hasSubst_of_forall_X_mem gA hgAmem,
      AlgHom.ext fun F => eq_substAlgHom_of_forall_X_mem gA hgAmem F⟩, fun i => ?_⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [hgX0, add_sub_cancel_left, hB, Ideal.mem_comap, AlgEquiv.apply_symm_apply,
        completionIdeal_eq]
      exact Ideal.mem_map_of_mem _ (Ideal.sub_mem _ hx₁ hx₁')
    · rw [hgXsucc, sub_self]
      exact zero_mem _
  -- (91.2): `φ(Î) = Î` from the invariance on the chart
  have hd := map_comap_completionIdeal_eq_of_isOnePlus f n I hm hI hpc hp (Fin.cons x₁' y) hz'
    Φ' hΦ'X hΦ'C g hg
  have h91_2 : (I.completionIdeal p).map (Q.formalAutomorphism ha ha').symm =
      I.completionIdeal p := by
    refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun x hx => ?_) fun x hx => ?_
    · rw [Ideal.mem_comap, hφapply, ← Ideal.mem_comap (f := Φ'), ← hd]
      exact Ideal.mem_map_of_mem _ (by rw [Ideal.mem_comap, AlgEquiv.apply_symm_apply]; exact hx)
    · have hx' : Φ'.symm x ∈ ((I.completionIdeal p).comap Φ').map g := by
        rw [hd, Ideal.mem_comap, AlgEquiv.apply_symm_apply]; exact hx
      obtain ⟨w, hw, hwx⟩ := Ideal.mem_map_iff_of_surjective _ g.surjective |>.mp hx'
      have hΦ'w : Φ' w ∈ I.completionIdeal p := Ideal.mem_comap.mp hw
      have : (Q.formalAutomorphism ha ha').symm (Φ' w) = x := by
        rw [hφapply, AlgEquiv.symm_apply_apply, hwx, AlgEquiv.apply_symm_apply]
      rw [← this]
      exact Ideal.mem_map_of_mem _ hΦ'w
  -- (91.4): `h − φ(h) ∈ MC(I)^` from the `1 + B` calculus on the chart
  have hBle :
      B ≤ maximalIdeal (MvPowerSeries (Fin (d + 1)) (ResidueField (X.presheaf.stalk p))) := by
    rw [hB, ← comap_maximalIdeal_ringEquiv Φ'.toRingEquiv]
    exact Ideal.comap_mono (completionIdeal_MC_le_maximalIdeal f n I m hm hp)
  have hgA : ∀ i, gA (MvPowerSeries.X i) - MvPowerSeries.X i ∈ B := hg.2
  have h91_4 : ∀ h, h - (Q.formalAutomorphism ha ha').symm h ∈ (MC f I m).completionIdeal p :=
    fun h => by
    have hF := sub_map_mem_of_forall_sub_X_mem gA B hBle hgA (Φ'.symm h)
    have : (Q.formalAutomorphism ha ha').symm h - h = Φ' (g (Φ'.symm h) - Φ'.symm h) := by
      rw [map_sub, AlgEquiv.apply_symm_apply, hφapply]
    rw [← neg_sub, this]
    exact neg_mem_iff.mpr (Ideal.mem_comap.mp hF)
  -- (91.1) and (91.3) from the completed principal ideals
  refine ⟨map_completionIdeal_eq_of_stalkIdeal_eq_span H' H hH' hH _ hφx₁, h91_2, fun i => ?_,
    h91_4⟩
  by_cases hpi : p ∈ (E.component i).support
  · obtain ⟨j, hj⟩ := hE i hpi
    exact map_completionIdeal_eq_of_stalkIdeal_eq_span _ _ hj hj _ (hφy j)
  · rw [completionIdeal_eq_top_of_notMem_support _ hpi, Ideal.map_top]

end AlgebraicGeometry.Scheme.IdealSheafData
