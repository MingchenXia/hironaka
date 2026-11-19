/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.FormalAut
public import Hironaka.Resolution.Algebraic.MaximalContact.FormalEquiv
public import Hironaka.Resolution.Algebraic.MaximalContact.Invariant
public import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
public import Hironaka.Scheme.Snc.Basic
import Hironaka.Algebra.Local.PowerSeriesEndomorphism
import Hironaka.Algebra.Local.PowerSeriesRegular
import Hironaka.Algebra.Local.RegularSystemCommon
import Hironaka.Resolution.Algebraic.MaximalContact.CompletionIdealMap
import Hironaka.Resolution.Algebraic.MaximalContact.Coordinates
import Hironaka.Resolution.Algebraic.MaximalContact.FormalEquivBridge
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Theorem 92, the formal half: formal equivalence at a closed point of the cosupport

The formal part of the proof of [Kol07, Theorem 92], which is [Kol07, 95], assembled from: the
coordinates `x₁, x₁' ∈ MC(I)_p`, `y = (x₂, …, xₙ)`
(`Hironaka/Resolution/Algebraic/MaximalContact/Coordinates.lean`), the `k`-linear Cohen isomorphisms
(`Hironaka/Algebra/Local/CoefficientFieldOver.lean`), [Kol07, Proposition 94] on the chart
(`Hironaka/Algebra/Local/CohenDerivation.lean`) with its stalk-level inputs
(`Hironaka/Resolution/Algebraic/MaximalContact/FormalEquivBridge.lean`), the completed principal
ideals (`Hironaka/Resolution/Algebraic/MaximalContact/CompletionIdealMap.lean`) and the calculus of
substitutions of the form `1 + B` (`Hironaka/Algebra/Local/PowerSeriesEndomorphism.lean`).

**Why it holds.** At a closed point `p ∈ cosupp(I, m)` take Kollár's coordinates
`x₁, x₁' ∈ MC(I)_p`, `y = (x₂, …, xₙ)` and the chart `Φ' : κ(p)⟦X⟧ ≃ₐ[k] Ô_{X,p}` of `(x₁', y)` for
a coefficient field `σ`.

* *The automorphism on the chart* (`exists_formalAutomorphism`): the chart `Φ` of `(x₁, y)` for
  the same `σ` gives `g := Φ'⁻¹ ∘ Φ`, a `κ(p)`-algebra automorphism of `κ(p)⟦X⟧` (it fixes the
  constants) with `g(X₀) = Φ'⁻¹(ι x₁) = X₀ + Φ'⁻¹(ι(x₁ − x₁'))` and `g(Xᵢ₊₁) = Xᵢ₊₁`, Kollár's
  `φ^*(x₁', x₂, …) = (x₁' + (x₁ − x₁'), x₂, …)`; it is a substitution because it sends the `Xᵢ`
  into `𝔪` ([Kol07, Notation 93]), and of the form `1 + Φ'⁻¹(\widehat{MC(I)})` because
  `x₁ − x₁' ∈ MC(I)_p`.
* *Invariance of `Î`* (`isInvariantOnePlus_comap_completionIdeal`,
  `map_comap_completionIdeal_eq_of_isOnePlus`): any chart sending the variables to a prescribed
  regular system of parameters and the constants to a coefficient field is the Cohen isomorphism
  of coordinates adapted to that regular system (`cohenAlgEquiv_eq`, `exists_regularCoords_eq`),
  for which the ring-level Proposition 94 applies; the inputs are MC-invariance of `Î` in the
  completed coordinates and `\widehat{MC(I)} ⊆ 𝔪Ô`.
* *Assembly* (`formallyEquivalentAt_of_isMCInvariant`): `φ := Φ' ∘ g ∘ Φ'⁻¹` is a `k`-algebra
  automorphism of `Ô_{X,p}` (`Φ'` is `k`-linear, `g` is `κ(p)`- hence `k`-linear). (91.1):
  `φ(ι x₁') = ι x₁`, so `φ(Ĥ') = Ĥ`; (91.2): `g(Φ'⁻¹ Î) = Φ'⁻¹ Î` transports to `φ(Î) = Î`;
  (91.3): `φ(ι yⱼ) = ι yⱼ` fixes the completed equations of the `Eⁱ` through `p`, and those not
  through `p` have unit completed ideal; (91.4): `g(F) − F ∈ Φ'⁻¹(\widehat{MC(I)})` for all `F`,
  so `h − φ(h) ∈ \widehat{MC(I)}` for all `h`. That is [Kol07, Definition 91]
  (`FormallyEquivalentAt`).

The invariance statement is used again in
`Hironaka/Resolution/Algebraic/MaximalContact/GraphOfAutomorphism.lean`, where the automorphism of
`Ô_{X,p}` induced by an étale neighbourhood of the graph is shown to satisfy (91.2), on the way to
the étale half of Theorem 92 (`Hironaka/Resolution/Algebraic/MaximalContact/Theorem92.lean`).
-/

public section

namespace AlgebraicGeometry.Scheme.IdealSheafData

open CategoryTheory IsLocalRing Scheme MvPowerSeries

universe u

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f]

/-- The maximal-adic completion of a local ring ([Kol07, Definition 55]). -/
local notation "Ô(" R ")" => AdicCompletion (maximalIdeal R) R

section MaximalIdeal

variable {p : X}

omit [CharZero k] in
include n in
/-- Membership in the maximal ideal is transported along a `k`-algebra isomorphism of the
completion with `κ(p)⟦X⟧`. -/
theorem symm_mem_maximalIdeal_iff {d : ℕ}
    (Φ : letI := f.stalkAlgebra p
      MvPowerSeries (Fin d) (ResidueField (X.presheaf.stalk p)) ≃ₐ[k] Ô(X.presheaf.stalk p))
    (x : Ô(X.presheaf.stalk p)) :
    letI := f.stalkAlgebra p
    haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
    haveI : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
    Φ.symm x ∈ maximalIdeal (MvPowerSeries (Fin d) (ResidueField (X.presheaf.stalk p))) ↔
      x ∈ maximalIdeal Ô(X.presheaf.stalk p) := by
  let _ := f.stalkAlgebra p
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hloc : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
  rw [← comap_maximalIdeal_ringEquiv Φ.toRingEquiv, Ideal.mem_comap]
  change Φ (Φ.symm x) ∈ _ ↔ _
  rw [AlgEquiv.apply_symm_apply]

omit [CharZero k] in
include n in
/-- The canonical image of an element of `𝔪_p` lies in the maximal ideal of the completion. -/
theorem algebraMap_mem_maximalIdeal_adicCompletion {x : X.presheaf.stalk p}
    (hx : x ∈ maximalIdeal (X.presheaf.stalk p)) :
    haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
    haveI : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
    algebraMap (X.presheaf.stalk p) Ô(X.presheaf.stalk p) x ∈
      maximalIdeal Ô(X.presheaf.stalk p) := by
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hloc : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
  rw [AdicCompletion.maximalIdeal_eq_map]
  exact Ideal.mem_map_of_mem _ hx

end MaximalIdeal

section

variable (I : X.IdealSheafData) (m : ℕ) {p : X}

omit [CharZero k] in
include n in
/-- Kollár's automorphism in [Kol07, 95], on the chart `Φ'` of `(x₁', y)`:
`φ^*(x₁', x₂, …, xₙ) = (x₁' + (x₁ − x₁'), x₂, …, xₙ)` is a `κ(p)`-algebra automorphism of `κ(p)⟦X⟧`
of the form `1 + Φ'⁻¹(\widehat{MC(I)})` with `g(X₀) = X₀ + Φ'⁻¹(ι(x₁ − x₁'))` and
`g(Xᵢ₊₁) = Xᵢ₊₁`, namely `Φ'⁻¹ ∘ Φ` for the chart `Φ` of `(x₁, y)` with the same constants
([Kol07, Notation 93]). -/
theorem exists_formalAutomorphism {d : ℕ} (x₁ x₁' : X.presheaf.stalk p)
    (y : Fin d → X.presheaf.stalk p) (hx₁ : x₁ ∈ (MC f I m).stalkIdeal p)
    (hx₁' : x₁' ∈ (MC f I m).stalkIdeal p) (hz : IsRegularSystemOfParameters (Fin.cons x₁ y))
    (Φ' : letI := f.stalkAlgebra p
      MvPowerSeries (Fin (d + 1)) (ResidueField (X.presheaf.stalk p)) ≃ₐ[k] Ô(X.presheaf.stalk p))
    (hΦ'X : ∀ i, Φ' (MvPowerSeries.X i) = algebraMap (X.presheaf.stalk p) Ô(X.presheaf.stalk p)
      ((Fin.cons x₁' y : Fin (d + 1) → X.presheaf.stalk p) i))
    (hΦ'C : letI := f.stalkAlgebra p
      haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
      haveI : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
      ∀ a : ResidueField (X.presheaf.stalk p),
        IsLocalRing.residue Ô(X.presheaf.stalk p) (Φ' (MvPowerSeries.C a)) =
          residueFieldEquiv (X.presheaf.stalk p) a) :
    letI := f.stalkAlgebra p
    ∃ g : MvPowerSeries (Fin (d + 1)) (ResidueField (X.presheaf.stalk p))
        ≃ₐ[ResidueField (X.presheaf.stalk p)]
          MvPowerSeries (Fin (d + 1)) (ResidueField (X.presheaf.stalk p)),
      IsOnePlus (((MC f I m).completionIdeal p).comap Φ') g ∧
      g (MvPowerSeries.X 0) = MvPowerSeries.X 0 +
        Φ'.symm (algebraMap (X.presheaf.stalk p) Ô(X.presheaf.stalk p) (x₁ - x₁')) ∧
      ∀ i : Fin d, g (MvPowerSeries.X i.succ) = MvPowerSeries.X i.succ := by
  let _ := f.stalkAlgebra p
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hloc : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
  have hreg := isRegularLocalRing_stalk f p
  set ι := algebraMap (X.presheaf.stalk p) Ô(X.presheaf.stalk p) with hι
  set σ := coefficientFieldOfEquiv f Φ' with hσdef
  have hσ : ∀ a, IsLocalRing.residue Ô(X.presheaf.stalk p) (σ a) =
      residueFieldEquiv (X.presheaf.stalk p) a :=
    fun a => by rw [hσdef, coefficientFieldOfEquiv_apply]; exact hΦ'C a
  set Φ := cohenAlgEquivOver σ hσ (Fin.cons x₁ y) hz.1.symm hz.2 with hΦ
  have hΦX : ∀ i, Φ (MvPowerSeries.X i) = ι ((Fin.cons x₁ y : Fin (d + 1) → _) i) :=
    cohenAlgEquivOver_X σ hσ _ hz.1.symm hz.2
  have hΦC : ∀ a, Φ (MvPowerSeries.C a) = Φ' (MvPowerSeries.C a) := fun a => by
    rw [hΦ, cohenAlgEquivOver_C, hσdef, coefficientFieldOfEquiv_apply]
  -- `g₀ := Φ'⁻¹ ∘ Φ`, a `k`-algebra automorphism fixing the constants
  set g₀ := Φ.trans Φ'.symm with hg₀
  have hg₀C : ∀ a, g₀ (MvPowerSeries.C a) = MvPowerSeries.C a := fun a => by
    rw [hg₀, AlgEquiv.trans_apply, hΦC, AlgEquiv.symm_apply_apply]
  have hg₀X : ∀ i, g₀ (MvPowerSeries.X i) = Φ'.symm (ι ((Fin.cons x₁ y : Fin (d + 1) → _) i)) :=
    fun i => by rw [hg₀, AlgEquiv.trans_apply, hΦX]
  -- as a `κ(p)`-algebra automorphism
  let g : MvPowerSeries (Fin (d + 1)) (ResidueField (X.presheaf.stalk p))
      ≃ₐ[ResidueField (X.presheaf.stalk p)]
        MvPowerSeries (Fin (d + 1)) (ResidueField (X.presheaf.stalk p)) :=
    AlgEquiv.ofRingEquiv (f := g₀.toRingEquiv) fun a => by
      change g₀ (algebraMap _ _ a) = algebraMap _ _ a
      rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      exact hg₀C a
  have hgapply : ∀ F, g F = g₀ F := fun F => rfl
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
  -- the variables go into `𝔪`
  have hgmem : ∀ i, g (MvPowerSeries.X i) ∈
      maximalIdeal (MvPowerSeries (Fin (d + 1)) (ResidueField (X.presheaf.stalk p))) := fun i => by
    rw [hgapply, hg₀X, symm_mem_maximalIdeal_iff f n]
    exact algebraMap_mem_maximalIdeal_adicCompletion f n (mem_maximalIdeal_of_eq_span hz.1.symm i)
  let gA : MvPowerSeries (Fin (d + 1)) (ResidueField (X.presheaf.stalk p))
      →ₐ[ResidueField (X.presheaf.stalk p)]
        MvPowerSeries (Fin (d + 1)) (ResidueField (X.presheaf.stalk p)) := g
  have hgAmem : ∀ i, gA (MvPowerSeries.X i) ∈
      maximalIdeal (MvPowerSeries (Fin (d + 1)) (ResidueField (X.presheaf.stalk p))) := hgmem
  refine ⟨g, ⟨⟨fun i => gA (MvPowerSeries.X i), hasSubst_of_forall_X_mem gA hgAmem,
    AlgHom.ext fun F => eq_substAlgHom_of_forall_X_mem gA hgAmem F⟩, fun i => ?_⟩,
    hgX0, hgXsucc⟩
  -- the form `1 + Φ'⁻¹(MC(I)^)`
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [hgX0, add_sub_cancel_left, Ideal.mem_comap, AlgEquiv.apply_symm_apply, completionIdeal_eq]
    exact Ideal.mem_map_of_mem _ (Ideal.sub_mem _ hx₁ hx₁')
  · rw [hgXsucc, sub_self]
    exact zero_mem _

end

section

variable (I : X.IdealSheafData) {m : ℕ} {p : X}

include n in
/-- [Kol07, Proposition 94 (1)] at the stalk, as used in [Kol07, 95]: for `I` MC-invariant, `p` a
closed point of `cosupp(I, m)`, `m ≥ 1`, and a `k`-linear chart `Φ` sending the variables to a
regular system of parameters `z` and the constants to a coefficient field, the ideal `Φ⁻¹(Î)` of
`κ(p)⟦X⟧` is invariant under every automorphism of the form `1 + Φ⁻¹(\widehat{MC(I)})`. -/
theorem isInvariantOnePlus_comap_completionIdeal (hm : 1 ≤ m) (hI : IsMCInvariant f I m)
    (hpc : IsClosed ({p} : Set X)) (hp : (m : ℕ∞) ≤ I.ord p) {d : ℕ}
    (z : Fin d → X.presheaf.stalk p) (hz : IsRegularSystemOfParameters z)
    (Φ : letI := f.stalkAlgebra p
      MvPowerSeries (Fin d) (ResidueField (X.presheaf.stalk p)) ≃ₐ[k] Ô(X.presheaf.stalk p))
    (hΦX : ∀ i, Φ (MvPowerSeries.X i) =
      algebraMap (X.presheaf.stalk p) Ô(X.presheaf.stalk p) (z i))
    (hΦC : letI := f.stalkAlgebra p
      haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
      haveI : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
      ∀ a : ResidueField (X.presheaf.stalk p),
        IsLocalRing.residue Ô(X.presheaf.stalk p) (Φ (MvPowerSeries.C a)) =
          residueFieldEquiv (X.presheaf.stalk p) a) :
    IsInvariantOnePlus ((I.completionIdeal p).comap Φ)
      (((MC f I m).completionIdeal p).comap Φ) := by
  let _ := f.stalkAlgebra p
  let _ := f.stalkAlgebraRat p
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hloc : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
  have hreg := isRegularLocalRing_stalk f p
  have halg := isAlgebraic_residueField_of_isClosed f n hpc
  have hchar : CharZero (ResidueField (X.presheaf.stalk p)) :=
    charZero_of_injective_algebraMap (algebraMap k (ResidueField (X.presheaf.stalk p))).injective
  obtain ⟨c, hcx, hk, hs⟩ := exists_regularCoords_eq f n hpc z hz
  have hΦX' : ∀ i, Φ (MvPowerSeries.X i) =
      algebraMap (X.presheaf.stalk p) Ô(X.presheaf.stalk p) (c.x i) := fun i => by
    rw [hcx]; exact hΦX i
  have hΦeq := cohenAlgEquiv_eq f n c Φ hΦX' hΦC
  set σ := coefficientFieldOfEquiv f Φ with hσdef
  have hσ : ∀ a, IsLocalRing.residue Ô(X.presheaf.stalk p) (σ a) =
      residueFieldEquiv (X.presheaf.stalk p) a :=
    fun a => by rw [hσdef, coefficientFieldOfEquiv_apply]; exact hΦC a
  have hinv := isMCInvariant_adicCompletion f n I m hI c hk hs
  have hMC := adicCompletion_MC_completionIdeal f n I m p c hk hs
  have hB : c.adicCompletion.MC (I.completionIdeal p) m ≤ maximalIdeal Ô(X.presheaf.stalk p) := by
    rw [hMC]; exact completionIdeal_MC_le_maximalIdeal f n I m hm hp
  have := isInvariantOnePlus_comap_cohenAlgEquivCoords c hk σ hσ (I.completionIdeal p) m hinv hB
  rw [hMC] at this
  rw [hΦeq]
  exact this

include n in
/-- Kollár's `φ^* Î = Î` in [Kol07, 95], condition (91.2), in equality form: every automorphism `g`
of the form `1 + Φ⁻¹(\widehat{MC(I)})` satisfies `g(Φ⁻¹ Î) = Φ⁻¹ Î`. -/
theorem map_comap_completionIdeal_eq_of_isOnePlus (hm : 1 ≤ m) (hI : IsMCInvariant f I m)
    (hpc : IsClosed ({p} : Set X)) (hp : (m : ℕ∞) ≤ I.ord p) {d : ℕ}
    (z : Fin d → X.presheaf.stalk p) (hz : IsRegularSystemOfParameters z)
    (Φ : letI := f.stalkAlgebra p
      MvPowerSeries (Fin d) (ResidueField (X.presheaf.stalk p)) ≃ₐ[k] Ô(X.presheaf.stalk p))
    (hΦX : ∀ i, Φ (MvPowerSeries.X i) =
      algebraMap (X.presheaf.stalk p) Ô(X.presheaf.stalk p) (z i))
    (hΦC : letI := f.stalkAlgebra p
      haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
      haveI : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
      ∀ a : ResidueField (X.presheaf.stalk p),
        IsLocalRing.residue Ô(X.presheaf.stalk p) (Φ (MvPowerSeries.C a)) =
          residueFieldEquiv (X.presheaf.stalk p) a)
    (g : MvPowerSeries (Fin d) (ResidueField (X.presheaf.stalk p))
        ≃ₐ[ResidueField (X.presheaf.stalk p)]
          MvPowerSeries (Fin d) (ResidueField (X.presheaf.stalk p)))
    (hg : IsOnePlus (((MC f I m).completionIdeal p).comap Φ) g) :
    ((I.completionIdeal p).comap Φ).map g = (I.completionIdeal p).comap Φ := by
  let _ := f.stalkAlgebra p
  have := isInvariantOnePlus_comap_completionIdeal f n I hm hI hpc hp z hz Φ hΦX hΦC g hg
  exact Ideal.map_eq_of_map_le g.toRingEquiv _ this

end

section

include n in
/-- **The formal half of [Kol07, Theorem 92]** ([Kol07, 95]): under the hypotheses of Theorem 92,
`H` and `H'` are formally equivalent at every closed point `p ∈ cosupp(I, m)` with respect to
`(X, I, E)`. -/
theorem formallyEquivalentAt_of_isMCInvariant (I : X.IdealSheafData) {m : ℕ} (hm : 1 ≤ m)
    (hI : IsMCInvariant f I m) (E : DivisorFamily X) (H H' : X.IdealSheafData)
    (hH : IsMaximalContact f I m H) (hH' : IsMaximalContact f I m H')
    (hHE : (E.append H).IsSnc) (hH'E : (E.append H').IsSnc) (p : X) (hpc : IsClosed ({p} : Set X))
    (hp : (m : ℕ∞) ≤ I.ord p) :
    FormallyEquivalentAt f I m E H H' p := by
  classical
  let _ := f.stalkAlgebra p
  let _ := f.stalkAlgebraRat p
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hloc : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
  have hreg := isRegularLocalRing_stalk f p
  set ι := algebraMap (X.presheaf.stalk p) Ô(X.presheaf.stalk p) with hι
  -- the coordinates `x₁, x₁', y`
  obtain ⟨d, x₁, x₁', y, hx₁, hx₁', hHp, hH'p, hz, hz', c₀, hc₀inj, hc₀⟩ :=
    exists_coordinates f n I hm E H H' hH hH' hHE hH'E p hp
  -- the chart of `(x₁', y)`, with coordinates adapted to it
  obtain ⟨c', hc'x, hk', hs'⟩ := exists_regularCoords_eq f n hpc (Fin.cons x₁' y) hz'
  obtain ⟨σ, hσ⟩ := exists_coefficientField_over (X.presheaf.stalk p) k
  set Φ' := cohenAlgEquivCoords c' σ hσ with hΦ'
  have hΦ'X : ∀ i, Φ' (MvPowerSeries.X i) = ι ((Fin.cons x₁' y : Fin (d + 1) → _) i) := fun i => by
    rw [hΦ', cohenAlgEquivOver_X, hc'x]
  have hΦ'C : ∀ a, IsLocalRing.residue Ô(X.presheaf.stalk p) (Φ' (MvPowerSeries.C a)) =
      residueFieldEquiv (X.presheaf.stalk p) a := fun a => by
    rw [hΦ', residue_cohenAlgEquivOver_C]
  -- the automorphism on the chart
  obtain ⟨g, hg, hgX0, hgXsucc⟩ :=
    exists_formalAutomorphism f n I m x₁ x₁' y hx₁ hx₁' hz Φ' hΦ'X hΦ'C
  -- Kollár's `φ^* = Φ' ∘ g ∘ Φ'⁻¹` on `Ô_{X,p}`
  set φ : Ô(X.presheaf.stalk p) ≃ₐ[k] Ô(X.presheaf.stalk p) :=
    (Φ'.symm.trans (g.restrictScalars k)).trans Φ' with hφ
  have hφapply : ∀ h, φ h = Φ' (g (Φ'.symm h)) := fun h => by
    rw [hφ, AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply]
  have hX0 : Φ'.symm (ι x₁') = MvPowerSeries.X 0 := by
    rw [AlgEquiv.symm_apply_eq, hΦ'X 0, Fin.cons_zero]
  have hXsucc : ∀ i : Fin d, Φ'.symm (ι (y i)) = MvPowerSeries.X i.succ := fun i => by
    rw [AlgEquiv.symm_apply_eq, hΦ'X i.succ, Fin.cons_succ]
  -- `φ(ι x₁') = ι x₁` and `φ(ι yᵢ) = ι yᵢ`
  have hφx₁ : φ (ι x₁') = ι x₁ := by
    rw [hφapply, hX0, hgX0, map_add, AlgEquiv.apply_symm_apply, hΦ'X 0, Fin.cons_zero, ← map_add]
    congr 1
    ring
  have hφy : ∀ i, φ (ι (y i)) = ι (y i) := fun i => by
    rw [hφapply, hXsucc, hgXsucc, hΦ'X i.succ, Fin.cons_succ]
  -- (91.2): `φ(Î) = Î` from the invariance on the chart
  set B := ((MC f I m).completionIdeal p).comap Φ' with hB
  have hd := map_comap_completionIdeal_eq_of_isOnePlus f n I hm hI hpc hp (Fin.cons x₁' y) hz'
    Φ' hΦ'X hΦ'C g hg
  have h91_2 : (I.completionIdeal p).map φ = I.completionIdeal p := by
    refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun x hx => ?_) fun x hx => ?_
    · rw [Ideal.mem_comap, hφapply, ← Ideal.mem_comap (f := Φ'), ← hd]
      exact Ideal.mem_map_of_mem _ (by rw [Ideal.mem_comap, AlgEquiv.apply_symm_apply]; exact hx)
    · have hx' : Φ'.symm x ∈ ((I.completionIdeal p).comap Φ').map g := by
        rw [hd, Ideal.mem_comap, AlgEquiv.apply_symm_apply]; exact hx
      obtain ⟨w, hw, hwx⟩ := Ideal.mem_map_iff_of_surjective _ g.surjective |>.mp hx'
      have hΦ'w : Φ' w ∈ I.completionIdeal p := Ideal.mem_comap.mp hw
      have : φ (Φ' w) = x := by
        rw [hφapply, AlgEquiv.symm_apply_apply, hwx, AlgEquiv.apply_symm_apply]
      rw [← this]
      exact Ideal.mem_map_of_mem _ hΦ'w
  -- (91.4): `h − φ(h) ∈ MC(I)^` from the `1 + B` calculus on the chart
  have hBle :
      B ≤ maximalIdeal (MvPowerSeries (Fin (d + 1)) (ResidueField (X.presheaf.stalk p))) := by
    rw [hB, ← comap_maximalIdeal_ringEquiv Φ'.toRingEquiv]
    exact Ideal.comap_mono (completionIdeal_MC_le_maximalIdeal f n I m hm hp)
  let gA : MvPowerSeries (Fin (d + 1)) (ResidueField (X.presheaf.stalk p))
      →ₐ[ResidueField (X.presheaf.stalk p)]
        MvPowerSeries (Fin (d + 1)) (ResidueField (X.presheaf.stalk p)) := g
  have hgA : ∀ i, gA (MvPowerSeries.X i) - MvPowerSeries.X i ∈ B := hg.2
  have h91_4 : ∀ h, h - φ h ∈ (MC f I m).completionIdeal p := fun h => by
    have hF := sub_map_mem_of_forall_sub_X_mem gA B hBle hgA (Φ'.symm h)
    have : φ h - h = Φ' (g (Φ'.symm h) - Φ'.symm h) := by
      rw [map_sub, AlgEquiv.apply_symm_apply, hφapply]
    rw [← neg_sub, this]
    exact neg_mem_iff.mpr (Ideal.mem_comap.mp hF)
  -- Definition 91
  rw [formallyEquivalentAt_iff]
  refine ⟨φ, ?_, h91_2, fun i => ?_, h91_4⟩
  · exact map_completionIdeal_eq_of_stalkIdeal_eq_span H' H hH'p hHp φ hφx₁
  · by_cases hpi : p ∈ (E.component i).support
    · exact map_completionIdeal_eq_of_stalkIdeal_eq_span _ _ (hc₀ ⟨i, hpi⟩) (hc₀ ⟨i, hpi⟩) φ
        (hφy _)
    · rw [completionIdeal_eq_top_of_notMem_support _ hpi, Ideal.map_top]

end

end AlgebraicGeometry.Scheme.IdealSheafData
