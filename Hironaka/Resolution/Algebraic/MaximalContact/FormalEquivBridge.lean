/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.CohenDerivation
public import Hironaka.Resolution.Algebraic.MaximalContact.FormalEquiv
public import Hironaka.Resolution.Algebraic.MaximalContact.Invariant
public import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Algebra.Local.DerivativeCompletion
import Hironaka.Algebra.Local.PowerSeriesEndomorphism
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.IdealSheaf.Derivative.StalkCoords
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Smooth.DifferentialBasis
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# From the stalk of a smooth scheme to Kollár's `K⟦x⟧` computations

The ring-level results of `Hironaka/Algebra/Local/CohenDerivation.lean` ([Kol07, Proposition 94] on
the chart) are stated for a regular local `k`-algebra `R` with coordinates `c` whose derivations are
`k`-linear and whose residue field is algebraic over `k`, and for the Cohen isomorphism
`cohenAlgEquivCoords c σ hσ` built from `c`. At a closed point `p` of a smooth `k`-scheme this file
supplies the inputs and translates the outputs into the form used by the proof of the formal half
of Theorem 92 (`Hironaka/Resolution/Algebraic/MaximalContact/FormalEquivExists.lean`):

* `isAlgebraic_residueField_of_isClosed`: at a closed point `κ(p)` is algebraic over `k`
  (`trdeg_k κ(p) = 0`, `trdeg_residueField_stalk_eq_zero_of_isClosed`).
* `exists_regularCoords_eq`: coordinates on `𝒪_{X,p}` with a prescribed regular system of
  parameters `z` as `c.x`, `k`-linear and spanning the `k`-derivations: the coordinates of
  `exists_regularCoords_stalk_of_isAlgebraic` changed to `z` by `changeCoords`, with
  `transportPderiv_isLinearOver`, `transport_over` and `transportPderiv_comm_over`.
* `isMCInvariant_stalk`: MC-invariance of the ideal sheaf `I` in the sense of [Kol07, 53.1] gives
  `MC(I_p)·D(I_p) ⊆ I_p` in any such coordinates (`stalkIdeal_mul`, `stalkIdeal_MC`,
  `stalkIdeal_derivative` and `derivative_eq_D`), hence, since derivatives commute with completion
  ([Kol07, Lemma 74 (5)]), for `Î` in the completed coordinates (`isMCInvariant_adicCompletion`).
* `completionIdeal_MC_le_maximalIdeal`: `\widehat{MC(I)} ⊆ 𝔪Ô_{X,p}` at a point of `cosupp(I, m)`
  (`MC(I)` has order `1` there, [Kol07, Definition 79]).
* `cohenAlgEquiv_eq`: a `k`-algebra isomorphism `Φ : κ(p)⟦X⟧ ≃ₐ[k] Ô_{X,p}` with `Φ(Xᵢ) = ι(c.xᵢ)`
  whose constants are a coefficient field is the Cohen isomorphism `cohenAlgEquivCoords c σ hσ`
  for `σ := Φ ∘ C`: `Φ'⁻¹ ∘ Φ` is a `K`-algebra automorphism of `K⟦X⟧` fixing the `Xᵢ`, hence the
  identity (`algHom_ext_of_forall_X_mem`; this is the identification `Ô_{p,X} ≅ K⟦x₁, …, xₙ⟧` of
  [Kol07, Notation 93]). So the statements of `FormalEquivExists.lean`, quantified over any such
  `Φ`, follow from the ring-level results for the Cohen isomorphism:
  `isInvariantOnePlus_comap_completionIdeal` ([Kol07, Proposition 94 (1)]) and
  `map_comap_completionIdeal_eq_of_isOnePlus` (the equality `φ^* Î = Î`).
-/

@[expose] public section

namespace AlgebraicGeometry.Scheme.IdealSheafData

open CategoryTheory IsLocalRing MvPowerSeries

universe u

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f]

/-- The maximal-adic completion of a local ring ([Kol07, Definition 55]). -/
local notation "Ô(" R ")" => AdicCompletion (maximalIdeal R) R

include n in
/-- At a closed point the residue field is algebraic over `k` (`trdeg_k κ(p) = 0`). -/
theorem isAlgebraic_residueField_of_isClosed {p : X} (hpc : IsClosed ({p} : Set X)) :
    letI := f.stalkAlgebra p
    Algebra.IsAlgebraic k (ResidueField (X.presheaf.stalk p)) := by
  let _ := f.stalkAlgebra p
  exact trdeg_eq_zero_iff.mp (trdeg_residueField_stalk_eq_zero_of_isClosed f n hpc)

include n in
/-- Coordinates on the stalk at a closed point that are `k`-linear and span the `k`-derivations,
with a prescribed regular system of parameters `z` as the coordinates: change of coordinates
(`changeCoords`) from any such structure. -/
theorem exists_regularCoords_eq {p : X} (hpc : IsClosed ({p} : Set X)) {d : ℕ}
    (z : Fin d → X.presheaf.stalk p) (hz : IsRegularSystemOfParameters z) :
    letI := f.stalkAlgebra p
    letI := f.stalkAlgebraRat p
    haveI := @isRegularLocalRing_stalk k _ X f
      (SmoothOfRelativeDimension.smooth n f) p
    ∃ c : RegularCoords (X.presheaf.stalk p) d, c.x = z ∧ c.IsLinearOver k ∧
      c.SpansDerivations k := by
  let _ := f.stalkAlgebra p
  let _ := f.stalkAlgebraRat p
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n f
  have := isRegularLocalRing_stalk f p
  have halg := isAlgebraic_residueField_of_isClosed f n hpc
  obtain ⟨d₀, c₀, hk₀, hs₀⟩ :=
    exists_regularCoords_stalk_of_isAlgebraic f n p halg
  have hd : d₀ = d := by
    have h1 := c₀.card
    have h2 := hz.2
    rw [← h2] at h1
    exact_mod_cast h1
  subst hd
  have hzspan : maximalIdeal (X.presheaf.stalk p) = Ideal.span (Set.range z) := hz.1.symm
  refine ⟨c₀.changeCoords z hzspan
    (fun i j g => c₀.transportPderiv_comm_over hk₀ hs₀ z hzspan i j g),
    rfl, fun i a => c₀.transportPderiv_isLinearOver hk₀ z i a, fun δ g => ?_⟩
  exact RegularCoords.SpansDerivations.transport_over c₀ hs₀ z hzspan δ g

section Invariance

variable (I : X.IdealSheafData) (m : ℕ) {p : X} {d : ℕ}

include n in
/-- [Kol07, 53.1] at the stalk: if `I` is MC-invariant then `MC(I_p)·D(I_p) ⊆ I_p` in coordinates
`c` that are `k`-linear and span the `k`-derivations (the predicate
`RegularCoords.IsMCInvariant`). -/
theorem isMCInvariant_stalk (hI : IsMCInvariant f I m)
    (c : letI := f.stalkAlgebraRat p
      haveI := @isRegularLocalRing_stalk k _ X f
        (SmoothOfRelativeDimension.smooth n f) p
      RegularCoords (X.presheaf.stalk p) d)
    (hk : letI := f.stalkAlgebra p; letI := f.stalkAlgebraRat p
      haveI := @isRegularLocalRing_stalk k _ X f
        (SmoothOfRelativeDimension.smooth n f) p
      c.IsLinearOver k)
    (hs : letI := f.stalkAlgebra p; letI := f.stalkAlgebraRat p
      haveI := @isRegularLocalRing_stalk k _ X f
        (SmoothOfRelativeDimension.smooth n f) p
      c.SpansDerivations k) :
    letI := f.stalkAlgebraRat p
    haveI := @isRegularLocalRing_stalk k _ X f
      (SmoothOfRelativeDimension.smooth n f) p
    c.IsMCInvariant (I.stalkIdeal p) m := by
  let _ := f.stalkAlgebra p
  let _ := f.stalkAlgebraRat p
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n f
  have := isRegularLocalRing_stalk f p
  have h1 := stalkIdeal_mono hI p
  rw [stalkIdeal_mul, stalkIdeal_MC f n I m p c hk hs, stalkIdeal_derivative f I p,
    Ideal.derivative_eq_D c hk hs] at h1
  exact h1

include n in
/-- MC-invariance passes to the completion, since derivatives commute with completion
([Kol07, Lemma 74 (5)]): `Î` is MC-invariant in the completed coordinates. -/
theorem isMCInvariant_adicCompletion (hI : IsMCInvariant f I m)
    (c : letI := f.stalkAlgebraRat p
      haveI := @isRegularLocalRing_stalk k _ X f
        (SmoothOfRelativeDimension.smooth n f) p
      RegularCoords (X.presheaf.stalk p) d)
    (hk : letI := f.stalkAlgebra p; letI := f.stalkAlgebraRat p
      haveI := @isRegularLocalRing_stalk k _ X f
        (SmoothOfRelativeDimension.smooth n f) p
      c.IsLinearOver k)
    (hs : letI := f.stalkAlgebra p; letI := f.stalkAlgebraRat p
      haveI := @isRegularLocalRing_stalk k _ X f
        (SmoothOfRelativeDimension.smooth n f) p
      c.SpansDerivations k) :
    letI := f.stalkAlgebraRat p
    haveI := @isRegularLocalRing_stalk k _ X f
      (SmoothOfRelativeDimension.smooth n f) p
    c.adicCompletion.IsMCInvariant (I.completionIdeal p) m := by
  let _ := f.stalkAlgebra p
  let _ := f.stalkAlgebraRat p
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n f
  have := isRegularLocalRing_stalk f p
  rw [completionIdeal_eq, c.isMCInvariant_adicCompletion_iff]
  exact isMCInvariant_stalk f n I m hI c hk hs

include n in
/-- At a point of `cosupp(I, m)` the completed maximal contact ideal lies in the maximal ideal of
`Ô_{X,p}` (`MC(I)` has order `1` there, the remark in [Kol07, Definition 79]). -/
theorem completionIdeal_MC_le_maximalIdeal (hm : 1 ≤ m) (hp : (m : ℕ∞) ≤ I.ord p) :
    haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
    haveI : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
    (MC f I m).completionIdeal p ≤ maximalIdeal Ô(X.presheaf.stalk p) := by
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hft : LocallyOfFiniteType f := inferInstance
  have hloc : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
  have hsupp : p ∈ (MC f I m).support := by
    have h := coe_support_MC f n I hm
    have : p ∈ ((MC f I m).support : Set X) := by rw [h]; exact hp
    exact this
  have hle : (MC f I m).stalkIdeal p ≤ maximalIdeal (X.presheaf.stalk p) :=
    (mem_support_iff_stalkIdeal_le_maximalIdeal _ _).mp hsupp
  rw [completionIdeal_eq, AdicCompletion.maximalIdeal_eq_map]
  exact Ideal.map_mono hle

end Invariance

section Cohen

variable {p : X} {d : ℕ}

/-- The coefficient field `Φ ∘ C` of a `k`-algebra isomorphism `Φ : κ(p)⟦X⟧ ≃ₐ[k] Ô_{X,p}`. -/
noncomputable def coefficientFieldOfEquiv
    (Φ : letI := f.stalkAlgebra p
      MvPowerSeries (Fin d) (ResidueField (X.presheaf.stalk p)) ≃ₐ[k] Ô(X.presheaf.stalk p)) :
    letI := f.stalkAlgebra p
    ResidueField (X.presheaf.stalk p) →ₐ[k] Ô(X.presheaf.stalk p) :=
  letI := f.stalkAlgebra p
  Φ.toAlgHom.comp ((Algebra.ofId (ResidueField (X.presheaf.stalk p))
    (MvPowerSeries (Fin d) (ResidueField (X.presheaf.stalk p)))).restrictScalars k)

omit [CharZero k] in
/-- The coefficient field of `Φ` unfolded: `(Φ ∘ C)(a) = Φ(C a)`. -/
theorem coefficientFieldOfEquiv_apply
    (Φ : letI := f.stalkAlgebra p
      MvPowerSeries (Fin d) (ResidueField (X.presheaf.stalk p)) ≃ₐ[k] Ô(X.presheaf.stalk p))
    (a : ResidueField (X.presheaf.stalk p)) :
    coefficientFieldOfEquiv f Φ a = Φ (C a) := by
  let _ := f.stalkAlgebra p
  change Φ (algebraMap (ResidueField (X.presheaf.stalk p)) _ a) = Φ (C a)
  rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

include n in
/-- The identification `Ô_{p,X} ≅ K⟦x₁, …, xₙ⟧` of [Kol07, Notation 93] as a uniqueness statement:
a `k`-algebra isomorphism `Φ : κ(p)⟦X⟧ ≃ₐ[k] Ô_{X,p}` with `Φ(Xᵢ) = ι(c.xᵢ)` whose constants form
a coefficient field is the Cohen isomorphism of the coordinates `c` for the coefficient field
`Φ ∘ C`. -/
theorem cohenAlgEquiv_eq
    (c : letI := f.stalkAlgebraRat p
      haveI := @isRegularLocalRing_stalk k _ X f
        (SmoothOfRelativeDimension.smooth n f) p
      RegularCoords (X.presheaf.stalk p) d)
    (Φ : letI := f.stalkAlgebra p
      MvPowerSeries (Fin d) (ResidueField (X.presheaf.stalk p)) ≃ₐ[k] Ô(X.presheaf.stalk p))
    (hΦX : letI := f.stalkAlgebraRat p
      haveI := @isRegularLocalRing_stalk k _ X f
        (SmoothOfRelativeDimension.smooth n f) p
      ∀ i, Φ (MvPowerSeries.X i) = algebraMap (X.presheaf.stalk p) Ô(X.presheaf.stalk p) (c.x i))
    (hΦC : letI := f.stalkAlgebra p
      haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
      haveI : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
      ∀ a : ResidueField (X.presheaf.stalk p),
        IsLocalRing.residue Ô(X.presheaf.stalk p) (Φ (C a)) =
          residueFieldEquiv (X.presheaf.stalk p) a) :
    letI := f.stalkAlgebra p
    letI := f.stalkAlgebraRat p
    haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
    haveI : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
    haveI := @isRegularLocalRing_stalk k _ X f
      (SmoothOfRelativeDimension.smooth n f) p
    Φ = cohenAlgEquivCoords c (coefficientFieldOfEquiv f Φ)
      (fun a => by rw [coefficientFieldOfEquiv_apply]; exact hΦC a) := by
  let _ := f.stalkAlgebra p
  let _ := f.stalkAlgebraRat p
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hloc : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
  have := isRegularLocalRing_stalk f p
  set σ := coefficientFieldOfEquiv f Φ with hσdef
  have hσ : ∀ a, IsLocalRing.residue Ô(X.presheaf.stalk p) (σ a) =
      residueFieldEquiv (X.presheaf.stalk p) a :=
    fun a => by rw [hσdef, coefficientFieldOfEquiv_apply]; exact hΦC a
  set Φ' := cohenAlgEquivCoords c σ hσ with hΦ'
  -- `g := Φ'⁻¹ ∘ Φ` fixes the variables and the constants
  set g := Φ.trans Φ'.symm with hg
  have hgX : ∀ i, g (MvPowerSeries.X i) = MvPowerSeries.X i := fun i => by
    rw [hg, AlgEquiv.trans_apply, hΦX, ← cohenAlgEquivOver_X σ hσ c.x c.span_x c.card i,
      AlgEquiv.symm_apply_apply]
  have hgC : ∀ a, g (C a) = C a := fun a => by
    rw [hg, AlgEquiv.trans_apply, ← coefficientFieldOfEquiv_apply, ← hσdef,
      ← cohenAlgEquivOver_C σ hσ c.x c.span_x c.card a, AlgEquiv.symm_apply_apply]
  -- as a `K`-algebra endomorphism
  let gK : MvPowerSeries (Fin d) (ResidueField (X.presheaf.stalk p))
      →ₐ[ResidueField (X.presheaf.stalk p)]
        MvPowerSeries (Fin d) (ResidueField (X.presheaf.stalk p)) :=
    { toRingHom := (g : MvPowerSeries (Fin d) (ResidueField (X.presheaf.stalk p)) →+* _)
      commutes' := fun a => by
        simp only [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
        exact hgC a }
  have hgK : gK = AlgHom.id _ _ :=
    algHom_ext_of_forall_X_mem gK (AlgHom.id _ _)
      (fun i => by
        change g (MvPowerSeries.X i) ∈ _
        rw [hgX]
        exact X_mem_maximalIdeal_mvPowerSeries i)
      (fun i => by change g (MvPowerSeries.X i) = MvPowerSeries.X i; exact hgX i)
  refine AlgEquiv.ext fun F => ?_
  have : g F = F := by
    have h := congrArg (fun φ => φ F) hgK
    exact h
  rw [hg, AlgEquiv.trans_apply, AlgEquiv.symm_apply_eq] at this
  exact this

end Cohen

end AlgebraicGeometry.Scheme.IdealSheafData
