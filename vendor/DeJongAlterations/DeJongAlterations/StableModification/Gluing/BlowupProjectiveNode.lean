/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane T45C)
-/
import DeJongAlterations.StableModification.Blowups.NodeChart
import DeJongAlterations.StableModification.Blowups.Transport
import DeJongAlterations.StableModification.LocalUniformization.ModelCentre

/-!
# The blow-up of the node locus `(u, v, π)` of `A[u,v]/(uv - π²b)`

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), proof of
Proposition 4.3.1, stage 1 (T:2976–2990), blows up `(u, π)` in a node chart
`N = A[u,v]/(uv - πb)` with `|u| = |π|`. The centre `V(u, π)` of that blow-up is a curve, not
contained in the modification locus `V(u, v, π)`; the trivial extension of `Bl_{(u,π)}` to a global
curve is therefore *not* the blow-up of an ideal sheaf supported on the modification locus, and
SERRE-I does not apply to it. When moreover `|v| ≤ |u|` (which one
can always arrange by exchanging `u` and `v`), `b = πb'` with `b' ∈ A`, and we blow up instead the
ideal `(u, v, π)` (BND's `Blowups.nodeLocusIdeal`) of `N = A[u,v]/(uv - π²b')`, whose zero locus
is the modification locus itself. Its three charts are node models:

* the `π`-chart `A[u/π, v/π]` with `(u/π)(v/π) = b'` (`piChartInclusion`);
* the `u`-chart `A[u, π/u]` with `u (π/u) = π` (`uChartInclusion'`), where `v/u = (π/u)² b'`;
* the `v`-chart `A[v, π/v]` with `v (π/v) = π` (`vChartInclusion`).

Hence (`locusBlowup_isStrictlySemistable`) the blow-up is strictly semi-stable over `A`, it is a
modification, an isomorphism off `V(u, v, π)`, covered by spectra of integrally closed domains;
and (`locusBlowup_centre`) a valuation with `|u| = |π|` is centred in the smooth open
`{u/π invertible}` of the `π`-chart. This replaces `Bl_{(u,π)}` in the projective version of the
node stage (`PLAN-T5.md` node A4).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Polynomial

universe u

namespace DeJongAlterations.StableModification.Gluing.LocusBlowup

open DeJongAlterations Curves Algebra.NodeBlowupChart Blowups

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Chart

/-! ### Charts of affine blow-ups given by node evaluations -/

variable {A : Type u} [CommRing A] {N : Type u} [CommRing N] [IsDomain N] [Algebra A N]
  (J : Ideal N) (g : N) (hg : g ∈ J) (hg0 : g ≠ 0) {c : A}
  (ev : Node A c →ₐ[A] FractionRing N) (hinj : Function.Injective ev)
  (hrange : ev.range = (affineBlowupFractionChart J g).restrictScalars A)

/-- The fraction chart `N[J/g]` presented as a node ring. -/
def chartEquiv : Node A c ≃ₐ[A] (affineBlowupFractionChart J g).restrictScalars A :=
  (AlgEquiv.ofInjective ev hinj).trans (Subalgebra.equivOfEq _ _ hrange)

/-- The chart `Spec (Node A c) → Bl_J(Spec N)`. -/
def chartInclusion : Spec (.of (Node A c)) ⟶ affineBlowup J :=
  Spec.map (chartEquiv J g ev hinj hrange).toRingEquiv.toCommRingCatIso.inv ≫
    affineBlowupChartInclusion J g hg hg0

instance : IsOpenImmersion (chartInclusion J g hg hg0 ev hinj hrange) := by
  dsimp only [chartInclusion]
  infer_instance

/-- The original ring map `N → Node A c` of the chart. -/
def chartOriginalMap : N →ₐ[A] Node A c :=
  (chartEquiv J g ev hinj hrange).symm.toAlgHom.comp
    (IsScalarTower.toAlgHom A N (affineBlowupFractionChart J g))

theorem ev_chartOriginalMap (r : N) :
    ev (chartOriginalMap J g ev hinj hrange r) = algebraMap N (FractionRing N) r := by
  change ((chartEquiv J g ev hinj hrange ((chartEquiv J g ev hinj hrange).symm
    (algebraMap N (affineBlowupFractionChart J g) r)) : FractionRing N)) = _
  rw [AlgEquiv.apply_symm_apply]
  rfl

theorem chartInclusion_structure :
    chartInclusion J g hg hg0 ev hinj hrange ≫ affineBlowupStructure J =
      Spec.map (CommRingCat.ofHom (chartOriginalMap J g ev hinj hrange).toRingHom) := by
  dsimp only [chartInclusion]
  rw [Category.assoc, affineBlowupChartInclusion_structure, ← Spec.map_comp]
  congr 1

theorem chartInclusion_opensRange :
    (chartInclusion J g hg hg0 ev hinj hrange).opensRange = affineBlowupChartOpen J g hg := by
  dsimp only [chartInclusion]
  rw [Scheme.Hom.opensRange_comp_of_isIso, affineBlowupFractionChartInclusion_opensRange]

end Chart

theorem chartInclusion_nodeModel {A : Type u} [CommRing A] {c₀ : A} [IsDomain (Node A c₀)]
    (J : Ideal (Node A c₀)) (g : Node A c₀) (hg : g ∈ J) (hg0 : g ≠ 0) {c : A}
    (ev : Node A c →ₐ[A] FractionRing (Node A c₀)) (hinj : Function.Injective ev)
    (hrange : ev.range = (affineBlowupFractionChart J g).restrictScalars A) :
    chartInclusion J g hg hg0 ev hinj hrange ≫ affineBlowupStructure J ≫ nodeModel c₀ =
      nodeModel c := by
  rw [← Category.assoc, chartInclusion_structure]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext a : 2
  exact (chartOriginalMap J g ev hinj hrange).commutes a

section Node

variable {A : Type u} [CommRing A] [IsDomain A] (π b : A) [Fact (π ≠ 0)] [Fact (b ≠ 0)]

theorem fact_mul_ne_zero : Fact (π * b ≠ 0) := ⟨mul_ne_zero Fact.out Fact.out⟩

attribute [local instance] fact_mul_ne_zero

/-- The node ring `N = A[u,v]/(uv - π²b)`. -/
local notation "N" => Node A (π * (π * b))

/-- Its fraction field. -/
local notation "F" => FractionRing (Node A (π * (π * b)))

/-- The ideal `(u, v, π)` of `N`. -/
abbrev locusIdeal : Ideal N := nodeLocusIdeal π (π * b)

omit [IsDomain A] [Fact (π ≠ 0)] [Fact (b ≠ 0)] in
theorem locusIdeal_fg : (locusIdeal π b).FG :=
  Submodule.fg_span (((Set.finite_singleton _).insert _).insert _)

omit [IsDomain A] [Fact (π ≠ 0)] [Fact (b ≠ 0)] in
theorem coordinate0_mem_locusIdeal : coordinate (π * (π * b)) 0 ∈ locusIdeal π b :=
  Ideal.subset_span (Set.mem_insert _ _)

omit [IsDomain A] [Fact (π ≠ 0)] [Fact (b ≠ 0)] in
theorem coordinate1_mem_locusIdeal : coordinate (π * (π * b)) 1 ∈ locusIdeal π b :=
  Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))

omit [IsDomain A] [Fact (π ≠ 0)] [Fact (b ≠ 0)] in
theorem algebraMap_mem_locusIdeal : algebraMap A N π ∈ locusIdeal π b :=
  Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))

theorem coordinate_ne_zero (i : Fin 2) : coordinate (π * (π * b)) i ≠ 0 :=
  Algebra.NodeDomain.nodeCoordinate_ne_zero (π * (π * b))
    (mul_ne_zero Fact.out (mul_ne_zero Fact.out Fact.out)) i

theorem algebraMap_ne_zero : algebraMap A N π ≠ 0 := algebraMap_ne_zero_node π (π * b)

/-- `u`, `v`, `π`, `b` in the fraction field of `N`. -/
abbrev fu : F := fractionCoordinate π (π * b)
/-- The second coordinate in the fraction field. -/
abbrev fv : F := fractionCoordinate1 π (π * b)
/-- The parameter `π` in the fraction field. -/
abbrev fπ : F := algebraMap A F π
/-- The parameter `b` in the fraction field. -/
abbrev fb : F := algebraMap A F b

theorem fπ_ne_zero : fπ π b ≠ 0 := fractionParameter_ne_zero π (π * b)

theorem fb_ne_zero : fb π b ≠ 0 := by
  rw [fb, IsScalarTower.algebraMap_apply A N F]
  exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
    ((map_ne_zero_iff _ (Algebra.NodeDomain.algebraMap_nodeQuotient_injective (π * (π * b))
      (mul_ne_zero Fact.out (mul_ne_zero Fact.out Fact.out)))).mpr Fact.out)

omit [IsDomain A] [Fact (π ≠ 0)] [Fact (b ≠ 0)] in
theorem fu_mul_fv : fu π b * fv π b = fπ π b * (fπ π b * fb π b) := by
  have hrel := congrArg (algebraMap N F) (Algebra.NodeDomain.nodeCoordinateProduct (π * (π * b)))
  simpa only [fu, fv, fπ, fb, fractionCoordinate, fractionCoordinate1, coordinate, map_mul,
    ← IsScalarTower.algebraMap_apply A N F] using hrel

/-! #### The `π`-chart `A[u/π, v/π]`, `(u/π)(v/π) = b` -/

theorem fu_div_ne_zero : fu π b / fπ π b ≠ 0 :=
  div_ne_zero (fractionCoordinate_ne_zero π (π * b)) (fπ_ne_zero π b)

theorem aeval_fu_div_injective :
    Function.Injective (Polynomial.aeval (fu π b / fπ π b) : A[X] →ₐ[A] F) := by
  rw [← transcendental_iff_injective]
  intro h
  have h' := h.smul π
  rw [Algebra.smul_def, mul_div_cancel₀ _ (fπ_ne_zero π b)] at h'
  exact (transcendental_iff_injective.mpr (fractionCoordinate_aeval_injective π (π * b))) h'

/-- The evaluation of the `π`-chart: `(u/π, v/π)`. -/
def piEvaluation : Node A b →ₐ[A] F :=
  nodeEvaluationAlgHom b (Fact.out : b ≠ 0) (fu π b / fπ π b) (fu_div_ne_zero π b)

theorem piEvaluation_injective : Function.Injective (piEvaluation π b) :=
  nodeEvaluation_injective b (Fact.out : b ≠ 0) _ (fu_div_ne_zero π b) (aeval_fu_div_injective π b)

theorem piEvaluation_coordinate0 : piEvaluation π b (coordinate b 0) = fu π b / fπ π b :=
  nodeEvaluation_coordinate0 _ _ _ _

theorem piEvaluation_coordinate1 : piEvaluation π b (coordinate b 1) = fv π b / fπ π b := by
  rw [show piEvaluation π b (coordinate b 1) = fb π b / (fu π b / fπ π b) from
    nodeEvaluation_coordinate1 _ _ _ _]
  rw [div_div_eq_mul_div, div_eq_div_iff (fractionCoordinate_ne_zero π (π * b)) (fπ_ne_zero π b)]
  linear_combination -(fu_mul_fv π b)

theorem original_mem_piEvaluation_range (r : N) : algebraMap N F r ∈ (piEvaluation π b).range := by
  apply nodeHom_mem (π * (π * b)) (IsScalarTower.toAlgHom A N F)
  · change fu π b ∈ _
    rw [show fu π b = fπ π b * (fu π b / fπ π b) by field_simp [fπ_ne_zero π b]]
    exact (piEvaluation π b).range.mul_mem ((piEvaluation π b).range.algebraMap_mem π)
      ⟨coordinate b 0, piEvaluation_coordinate0 π b⟩
  · change fv π b ∈ _
    rw [show fv π b = fπ π b * (fv π b / fπ π b) by field_simp [fπ_ne_zero π b]]
    exact (piEvaluation π b).range.mul_mem ((piEvaluation π b).range.algebraMap_mem π)
      ⟨coordinate b 1, piEvaluation_coordinate1 π b⟩

/-- The `π`-chart image as an `N`-subalgebra. -/
def piRangeOverNode : Subalgebra N F where
  __ := (piEvaluation π b).range.toSubsemiring
  algebraMap_mem' := original_mem_piEvaluation_range π b

theorem ratio_mem_piRange {a : N} (ha : a ∈ locusIdeal π b) :
    algebraMap N F a / fπ π b ∈ piRangeOverNode π b := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    rcases ha with rfl | rfl | rfl
    · exact ⟨coordinate b 0, piEvaluation_coordinate0 π b⟩
    · exact ⟨coordinate b 1, piEvaluation_coordinate1 π b⟩
    · rw [← IsScalarTower.algebraMap_apply, div_self (fπ_ne_zero π b)]
      exact (piRangeOverNode π b).one_mem
  | zero => simp
  | add a c _ _ hia hic => simpa only [map_add, add_div] using (piRangeOverNode π b).add_mem hia hic
  | smul r a _ hia =>
    change algebraMap N F (r * a) / _ ∈ _
    rw [map_mul, mul_div_assoc]
    exact (piRangeOverNode π b).mul_mem ((piRangeOverNode π b).algebraMap_mem r) hia

theorem piEvaluation_range : (piEvaluation π b).range =
    (affineBlowupFractionChart (locusIdeal π b) (algebraMap A N π)).restrictScalars A := by
  apply le_antisymm
  · rintro _ ⟨r, rfl⟩
    apply nodeHom_mem b (piEvaluation π b)
    · rw [piEvaluation_coordinate0]
      change algebraMap N F (coordinate _ 0) / algebraMap N F (algebraMap A N π) ∈ _
      exact Algebra.subset_adjoin (R := N)
        (Set.mem_range_self (⟨_, coordinate0_mem_locusIdeal π b⟩ : locusIdeal π b))
    · rw [piEvaluation_coordinate1]
      change algebraMap N F (coordinate _ 1) / algebraMap N F (algebraMap A N π) ∈ _
      exact Algebra.subset_adjoin (R := N)
        (Set.mem_range_self (⟨_, coordinate1_mem_locusIdeal π b⟩ : locusIdeal π b))
  · have hle : affineBlowupFractionChart (locusIdeal π b) (algebraMap A N π) ≤
        piRangeOverNode π b := by
      apply Algebra.adjoin_le
      rintro _ ⟨a, rfl⟩
      have := ratio_mem_piRange π b a.2
      rwa [fπ, IsScalarTower.algebraMap_apply A N F] at this
    exact hle

/-- **The `π`-chart** `Spec A[u/π, v/π]/((u/π)(v/π) - b) → Bl_{(u,v,π)} N`. -/
def piChartInclusion : Spec (.of (Node A b)) ⟶ affineBlowup (locusIdeal π b) :=
  chartInclusion (locusIdeal π b) (algebraMap A N π) (algebraMap_mem_locusIdeal π b)
    (algebraMap_ne_zero π b) (piEvaluation π b) (piEvaluation_injective π b)
    (piEvaluation_range π b)

instance : IsOpenImmersion (piChartInclusion π b) := by
  dsimp only [piChartInclusion]
  infer_instance

/-! #### The `u`-chart `A[u, π/u]`, `u (π/u) = π` -/

theorem fv_div_fu : fv π b / fu π b = (fπ π b / fu π b) ^ 2 * fb π b := by
  have hu := fractionCoordinate_ne_zero π (π * b)
  rw [div_pow, div_mul_eq_mul_div, div_eq_div_iff hu (pow_ne_zero 2 hu)]
  linear_combination (fu π b) * fu_mul_fv π b

theorem ratio_mem_uRange {a : N} (ha : a ∈ locusIdeal π b) :
    algebraMap N F a / fu π b ∈ uChartRangeOverNode π (π * b) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    rcases ha with rfl | rfl | rfl
    · change fu π b / fu π b ∈ _
      rw [div_self (fractionCoordinate_ne_zero π (π * b))]
      exact (uChartRangeOverNode π (π * b)).one_mem
    · change fv π b / fu π b ∈ _
      rw [fv_div_fu]
      refine (uChartRangeOverNode π (π * b)).mul_mem
        ((uChartRangeOverNode π (π * b)).pow_mem ⟨coordinate π 1, ?_⟩ 2) ?_
      · exact uChartEvaluation_coordinate1 π (π * b)
      · rw [fb, IsScalarTower.algebraMap_apply A N F]
        exact (uChartRangeOverNode π (π * b)).algebraMap_mem _
    · rw [← IsScalarTower.algebraMap_apply]
      exact ⟨coordinate π 1, uChartEvaluation_coordinate1 π (π * b)⟩
  | zero => simp
  | add a c _ _ hia hic =>
    simpa only [map_add, add_div] using (uChartRangeOverNode π (π * b)).add_mem hia hic
  | smul r a _ hia =>
    change algebraMap N F (r * a) / _ ∈ _
    rw [map_mul, mul_div_assoc]
    exact (uChartRangeOverNode π (π * b)).mul_mem
      ((uChartRangeOverNode π (π * b)).algebraMap_mem r) hia

theorem uEvaluation_range : (uChartEvaluation π (π * b)).range =
    (affineBlowupFractionChart (locusIdeal π b)
      (coordinate (π * (π * b)) 0)).restrictScalars A := by
  apply le_antisymm
  · rintro _ ⟨r, rfl⟩
    apply nodeHom_mem π (uChartEvaluation π (π * b))
    · rw [uChartEvaluation_coordinate0]
      exact (affineBlowupFractionChart (locusIdeal π b) _).algebraMap_mem _
    · rw [uChartEvaluation_coordinate1]
      change algebraMap N F (algebraMap A N π) / algebraMap N F (coordinate _ 0) ∈ _
      exact Algebra.subset_adjoin (R := N)
        (Set.mem_range_self (⟨_, algebraMap_mem_locusIdeal π b⟩ : locusIdeal π b))
  · have hle : affineBlowupFractionChart (locusIdeal π b) (coordinate (π * (π * b)) 0) ≤
        uChartRangeOverNode π (π * b) := by
      apply Algebra.adjoin_le
      rintro _ ⟨a, rfl⟩
      exact ratio_mem_uRange π b a.2
    exact hle

/-- **The `u`-chart** `Spec A[u, π/u]/(u (π/u) - π) → Bl_{(u,v,π)} N`. -/
def uChartInclusion' : Spec (.of (Node A π)) ⟶ affineBlowup (locusIdeal π b) :=
  chartInclusion (locusIdeal π b) (coordinate (π * (π * b)) 0) (coordinate0_mem_locusIdeal π b)
    (coordinate_ne_zero π b 0) (uChartEvaluation π (π * b)) (uChartEvaluation_injective π (π * b))
    (uEvaluation_range π b)

instance : IsOpenImmersion (uChartInclusion' π b) := by
  dsimp only [uChartInclusion']
  infer_instance

/-! #### The `v`-chart `A[v, π/v]`, `v (π/v) = π` -/

/-- The evaluation of the `v`-chart: `(v, π/v)`. -/
def vEvaluation : Node A π →ₐ[A] F :=
  nodeEvaluationAlgHom π (Fact.out : π ≠ 0) (fv π b) (fractionCoordinate1_ne_zero π (π * b))

theorem vEvaluation_injective : Function.Injective (vEvaluation π b) :=
  nodeEvaluation_injective π (Fact.out : π ≠ 0) _ (fractionCoordinate1_ne_zero π (π * b))
    (fractionCoordinate1_aeval_injective π (π * b))

theorem vEvaluation_coordinate0 : vEvaluation π b (coordinate π 0) = fv π b :=
  nodeEvaluation_coordinate0 _ _ _ _

theorem vEvaluation_coordinate1 : vEvaluation π b (coordinate π 1) = fπ π b / fv π b :=
  nodeEvaluation_coordinate1 _ _ _ _

theorem fu_div_fv : fu π b / fv π b = (fπ π b / fv π b) ^ 2 * fb π b := by
  have hv := fractionCoordinate1_ne_zero π (π * b)
  rw [div_pow, div_mul_eq_mul_div, div_eq_div_iff hv (pow_ne_zero 2 hv)]
  linear_combination (fv π b) * fu_mul_fv π b

theorem original_mem_vEvaluation_range (r : N) : algebraMap N F r ∈ (vEvaluation π b).range := by
  have hv := fractionCoordinate1_ne_zero π (π * b)
  apply nodeHom_mem (π * (π * b)) (IsScalarTower.toAlgHom A N F)
  · change fu π b ∈ _
    rw [show fu π b = fv π b * (fu π b / fv π b) by field_simp [hv], fu_div_fv]
    refine (vEvaluation π b).range.mul_mem ⟨coordinate π 0, vEvaluation_coordinate0 π b⟩
      ((vEvaluation π b).range.mul_mem ((vEvaluation π b).range.pow_mem
        ⟨coordinate π 1, vEvaluation_coordinate1 π b⟩ 2) ((vEvaluation π b).range.algebraMap_mem b))
  · exact ⟨coordinate π 0, vEvaluation_coordinate0 π b⟩

/-- The `v`-chart image as an `N`-subalgebra. -/
def vRangeOverNode : Subalgebra N F where
  __ := (vEvaluation π b).range.toSubsemiring
  algebraMap_mem' := original_mem_vEvaluation_range π b

theorem ratio_mem_vRange {a : N} (ha : a ∈ locusIdeal π b) :
    algebraMap N F a / fv π b ∈ vRangeOverNode π b := by
  have hv := fractionCoordinate1_ne_zero π (π * b)
  induction ha using Submodule.span_induction with
  | mem a ha =>
    rcases ha with rfl | rfl | rfl
    · change fu π b / fv π b ∈ _
      rw [fu_div_fv]
      exact (vRangeOverNode π b).mul_mem ((vRangeOverNode π b).pow_mem
        ⟨coordinate π 1, vEvaluation_coordinate1 π b⟩ 2)
        (by rw [fb, IsScalarTower.algebraMap_apply A N F]
            exact (vRangeOverNode π b).algebraMap_mem _)
    · change fv π b / fv π b ∈ _
      rw [div_self hv]
      exact (vRangeOverNode π b).one_mem
    · rw [← IsScalarTower.algebraMap_apply]
      exact ⟨coordinate π 1, vEvaluation_coordinate1 π b⟩
  | zero => simp
  | add a c _ _ hia hic => simpa only [map_add, add_div] using (vRangeOverNode π b).add_mem hia hic
  | smul r a _ hia =>
    change algebraMap N F (r * a) / _ ∈ _
    rw [map_mul, mul_div_assoc]
    exact (vRangeOverNode π b).mul_mem ((vRangeOverNode π b).algebraMap_mem r) hia

theorem vEvaluation_range : (vEvaluation π b).range =
    (affineBlowupFractionChart (locusIdeal π b)
      (coordinate (π * (π * b)) 1)).restrictScalars A := by
  apply le_antisymm
  · rintro _ ⟨r, rfl⟩
    apply nodeHom_mem π (vEvaluation π b)
    · rw [vEvaluation_coordinate0]
      exact (affineBlowupFractionChart (locusIdeal π b) _).algebraMap_mem _
    · rw [vEvaluation_coordinate1]
      change algebraMap N F (algebraMap A N π) / algebraMap N F (coordinate _ 1) ∈ _
      exact Algebra.subset_adjoin (R := N)
        (Set.mem_range_self (⟨_, algebraMap_mem_locusIdeal π b⟩ : locusIdeal π b))
  · have hle : affineBlowupFractionChart (locusIdeal π b) (coordinate (π * (π * b)) 1) ≤
        vRangeOverNode π b := by
      apply Algebra.adjoin_le
      rintro _ ⟨a, rfl⟩
      exact ratio_mem_vRange π b a.2
    exact hle

/-- **The `v`-chart** `Spec A[v, π/v]/(v (π/v) - π) → Bl_{(u,v,π)} N`. -/
def vChartInclusion : Spec (.of (Node A π)) ⟶ affineBlowup (locusIdeal π b) :=
  chartInclusion (locusIdeal π b) (coordinate (π * (π * b)) 1) (coordinate1_mem_locusIdeal π b)
    (coordinate_ne_zero π b 1) (vEvaluation π b) (vEvaluation_injective π b) (vEvaluation_range π b)

instance : IsOpenImmersion (vChartInclusion π b) := by
  dsimp only [vChartInclusion]
  infer_instance

end Node

section Geometry

variable {A : Type u} [CommRing A] [IsDomain A] (π b : A) [Fact (π ≠ 0)] [Fact (b ≠ 0)]

attribute [local instance] fact_mul_ne_zero

/-- The structure morphism `Bl_{(u,v,π)} N → Spec A`. -/
abbrev locusBlowupMorphism : affineBlowup (locusIdeal π b) ⟶ Spec (.of A) :=
  affineBlowupStructure (locusIdeal π b) ≫ nodeModel (π * (π * b))

theorem piChartInclusion_morphism :
    piChartInclusion π b ≫ locusBlowupMorphism π b = nodeModel b :=
  chartInclusion_nodeModel _ _ _ _ _ _ _

theorem uChartInclusion'_morphism :
    uChartInclusion' π b ≫ locusBlowupMorphism π b = nodeModel π :=
  chartInclusion_nodeModel _ _ _ _ _ _ _

theorem vChartInclusion_morphism :
    vChartInclusion π b ≫ locusBlowupMorphism π b = nodeModel π :=
  chartInclusion_nodeModel _ _ _ _ _ _ _

theorem piChartInclusion_opensRange :
    (piChartInclusion π b).opensRange = affineBlowupChartOpen (locusIdeal π b)
      (algebraMap A _ π) (algebraMap_mem_locusIdeal π b) :=
  chartInclusion_opensRange _ _ _ _ _ _ _

theorem uChartInclusion'_opensRange :
    (uChartInclusion' π b).opensRange = affineBlowupChartOpen (locusIdeal π b)
      (coordinate (π * (π * b)) 0) (coordinate0_mem_locusIdeal π b) :=
  chartInclusion_opensRange _ _ _ _ _ _ _

theorem vChartInclusion_opensRange :
    (vChartInclusion π b).opensRange = affineBlowupChartOpen (locusIdeal π b)
      (coordinate (π * (π * b)) 1) (coordinate1_mem_locusIdeal π b) :=
  chartInclusion_opensRange _ _ _ _ _ _ _

/-- The three charts cover the blow-up. -/
theorem mem_range_charts (x : affineBlowup (locusIdeal π b)) :
    x ∈ Set.range (piChartInclusion π b) ∨ x ∈ Set.range (uChartInclusion' π b) ∨
      x ∈ Set.range (vChartInclusion π b) := by
  let gens : Fin 3 → Node A (π * (π * b)) :=
    ![coordinate (π * (π * b)) 0, coordinate (π * (π * b)) 1, algebraMap A _ π]
  have hgens : ∀ i, gens i ∈ locusIdeal π b := by
    intro i
    fin_cases i
    · exact coordinate0_mem_locusIdeal π b
    · exact coordinate1_mem_locusIdeal π b
    · exact algebraMap_mem_locusIdeal π b
  have hspan : Ideal.span (Set.range gens) = locusIdeal π b := by
    rw [locusIdeal, nodeLocusIdeal]
    congr 1
    ext y
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.exists_fin_succ,
      Fin.exists_fin_zero, gens]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    constructor
    · rintro (h | h | h | h) <;> simp_all
    · rintro (h | h | h) <;> simp [h]
  have hx : x ∈ ⨆ i, affineBlowupChartOpen (locusIdeal π b) (gens i) (hgens i) := by
    rw [iSup_affineBlowupChartOpen_of_span _ gens hgens hspan]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  fin_cases i
  · right; left
    change x ∈ ((uChartInclusion' π b).opensRange : Set _)
    rw [uChartInclusion'_opensRange]
    exact hi
  · right; right
    change x ∈ ((vChartInclusion π b).opensRange : Set _)
    rw [vChartInclusion_opensRange]
    exact hi
  · left
    change x ∈ ((piChartInclusion π b).opensRange : Set _)
    rw [piChartInclusion_opensRange]
    exact hi

/-- **The blow-up of `(u, v, π)` is strictly semi-stable** (without marks) over `A`: its three
charts are node models. -/
theorem locusBlowup_isStrictlySemistable :
    IsStrictlySemistable (locusBlowupMorphism π b) ⊤ := by
  refine IsStrictlySemistable.of_openCover fun x ↦ ?_
  rcases mem_range_charts π b x with h | h | h
  · refine ⟨_, h, isStrictlySemistable_opensRange_of_comp _ _ ?_⟩
    rw [piChartInclusion_morphism]
    exact isStrictlySemistable_nodeModel b
  · refine ⟨_, h, isStrictlySemistable_opensRange_of_comp _ _ ?_⟩
    rw [uChartInclusion'_morphism]
    exact isStrictlySemistable_nodeModel π
  · refine ⟨_, h, isStrictlySemistable_opensRange_of_comp _ _ ?_⟩
    rw [vChartInclusion_morphism]
    exact isStrictlySemistable_nodeModel π

theorem locusIdeal_ne_bot : locusIdeal π b ≠ ⊥ := by
  intro h
  have := coordinate0_mem_locusIdeal π b
  rw [h, Ideal.mem_bot] at this
  exact coordinate_ne_zero π b 0 this

/-- The blow-up of `(u, v, π)` is a modification. -/
theorem locusBlowup_isModification : IsModification (affineBlowupStructure (locusIdeal π b)) :=
  isModification_affineBlowupStructure _ (locusIdeal_ne_bot π b) (locusIdeal_fg π b)

omit [IsDomain A] [Fact (π ≠ 0)] [Fact (b ≠ 0)] in
theorem locusBlowup_isProper : IsProper (affineBlowupStructure (locusIdeal π b)) :=
  affineBlowupStructure_isProper _ (locusIdeal_fg π b)

instance isSeparated_locusBlowup : (affineBlowup (locusIdeal π b)).IsSeparated := by
  have := locusBlowup_isProper π b
  exact ValCurves.isSeparated_of_isSeparated (affineBlowupStructure (locusIdeal π b))

omit [IsDomain A] [Fact (π ≠ 0)] [Fact (b ≠ 0)] in
/-- The centre complement of `(u, v, π)` is BND's `nodeLocusComplement`. -/
theorem affineBlowupCenterComplement_locusIdeal :
    affineBlowupCenterComplement (locusIdeal π b) = nodeLocusComplement π (π * b) := by
  apply SetLike.coe_injective
  change (PrimeSpectrum.zeroLocus ((locusIdeal π b : Ideal (Node A (π * (π * b)))) :
    Set (Node A (π * (π * b)))))ᶜ = _
  rw [← compl_compl ((nodeLocusComplement π (π * b) : Set (Spec (.of (Node A (π * (π * b))))))),
    ← range_nodeLocus]
  congr 1
  have h : Set.range (nodeLocus π (π * b)) =
      Set.range (PrimeSpectrum.comap (S := Node A (π * (π * b)) ⧸ nodeLocusIdeal π (π * b))
        (Ideal.Quotient.mk (nodeLocusIdeal π (π * b)))) := rfl
  rw [h, range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]

/-- **The blow-up of `(u, v, π)` is an isomorphism off `V(u, v, π)`.** -/
theorem locusBlowup_isIso :
    IsIso (affineBlowupStructure (locusIdeal π b) ∣_ nodeLocusComplement π (π * b)) := by
  rw [← affineBlowupCenterComplement_locusIdeal]
  exact affineBlowupStructure_centerComplement_isIso _

/-- The blow-up of `(u, v, π)` is covered by spectra of integrally closed domains. -/
theorem locusBlowup_cover [IsIntegrallyClosed A] (m : affineBlowup (locusIdeal π b)) :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B) (_ : IsIntegrallyClosed B)
      (j : Spec (.of B) ⟶ affineBlowup (locusIdeal π b)) (_ : IsOpenImmersion j),
      m ∈ Set.range j := by
  rcases mem_range_charts π b m with h | h | h
  · exact ⟨Node A b, inferInstance, Algebra.NodeDomain.nodeQuotient_isDomain b Fact.out,
      Algebra.NodeNormal.node_isIntegrallyClosed b Fact.out, _, inferInstance, h⟩
  · exact ⟨Node A π, inferInstance, Algebra.NodeDomain.nodeQuotient_isDomain π Fact.out,
      Algebra.NodeNormal.node_isIntegrallyClosed π Fact.out, _, inferInstance, h⟩
  · exact ⟨Node A π, inferInstance, Algebra.NodeDomain.nodeQuotient_isDomain π Fact.out,
      Algebra.NodeNormal.node_isIntegrallyClosed π Fact.out, _, inferInstance, h⟩

/-- The smooth open `{u/π invertible}` of the `π`-chart. -/
def locusBlowupSmoothOpen : (affineBlowup (locusIdeal π b)).Opens :=
  piChartInclusion π b ''ᵁ Geometry.NodeFamilySmooth.coordinateOpen b 0

end Geometry

section Centre

open ValCurves LocalUniformization

variable {A : Type u} [CommRing A] [IsDomain A] (π b : A) [Fact (π ≠ 0)] [Fact (b ≠ 0)]

attribute [local instance] fact_mul_ne_zero

variable {L : Type u} [Field L] {ι : Node A (π * (π * b)) →+* L} (hι : Function.Injective ι)
include hι

/-- The `π`-chart mapped to `L`: `u/π ↦ ι(u)/ι(π)`, `v/π ↦ ι(v)/ι(π)`. -/
def piChartRingHom : Node A b →+* L := (IsFractionRing.lift hι).comp (piEvaluation π b).toRingHom

theorem piChartRingHom_comp :
    (piChartRingHom π b hι).comp
      (chartOriginalMap (locusIdeal π b) (algebraMap A _ π) (piEvaluation π b)
        (piEvaluation_injective π b) (piEvaluation_range π b)).toRingHom = ι := by
  refine RingHom.ext fun r ↦ ?_
  rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, piChartRingHom,
    RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ev_chartOriginalMap,
    IsFractionRing.lift_algebraMap]

theorem piChartRingHom_coordinate0 :
    piChartRingHom π b hι (coordinate b 0) =
      ι (coordinate (π * (π * b)) 0) / ι (algebraMap A _ π) := by
  rw [piChartRingHom, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    piEvaluation_coordinate0, map_div₀, fu, fractionCoordinate, IsFractionRing.lift_algebraMap, fπ,
    IsScalarTower.algebraMap_apply A (Node A (π * (π * b))) (FractionRing _),
    IsFractionRing.lift_algebraMap]

theorem piChartRingHom_coordinate1 :
    piChartRingHom π b hι (coordinate b 1) =
      ι (coordinate (π * (π * b)) 1) / ι (algebraMap A _ π) := by
  rw [piChartRingHom, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    piEvaluation_coordinate1, map_div₀, fv, fractionCoordinate1, IsFractionRing.lift_algebraMap, fπ,
    IsScalarTower.algebraMap_apply A (Node A (π * (π * b))) (FractionRing _),
    IsFractionRing.lift_algebraMap]

theorem piChartRingHom_algebraMap (c : A) :
    piChartRingHom π b hι (algebraMap A (Node A b) c) = ι (algebraMap A _ c) := by
  rw [piChartRingHom, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    AlgHom.commutes, IsScalarTower.algebraMap_apply A (Node A (π * (π * b))) (FractionRing _),
    IsFractionRing.lift_algebraMap]

theorem piChartRingHom_mem {V : ValuationSubring L} (hO : ∀ r, ι r ∈ V)
    (hu : ι (coordinate (π * (π * b)) 0) / ι (algebraMap A _ π) ∈ V)
    (hv : ι (coordinate (π * (π * b)) 1) / ι (algebraMap A _ π) ∈ V) (r : Node A b) :
    piChartRingHom π b hι r ∈ V := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective r
  induction P using MvPolynomial.induction_on with
  | C c =>
    change piChartRingHom π b hι (algebraMap A (Node A b) c) ∈ V
    rw [piChartRingHom_algebraMap]
    exact hO _
  | add P Q hP hQ => simpa only [map_add] using add_mem hP hQ
  | mul_X P i hP =>
    rw [map_mul, map_mul]
    refine mul_mem hP ?_
    fin_cases i
    · change piChartRingHom π b hι (coordinate b 0) ∈ V
      rw [piChartRingHom_coordinate0]
      exact hu
    · change piChartRingHom π b hι (coordinate b 1) ∈ V
      rw [piChartRingHom_coordinate1]
      exact hv

/-- **Centres on the blow-up of `(u, v, π)`** (the projective node stage). Let `ι : N → L` be
injective and `V` a valuation ring of `L` containing `ι(N)` with `u/π` a unit of `V` and
`v/π ∈ V`. For every lift `η : Spec L → Bl_{(u,v,π)} N` of the point given by `ι`, `V` has a
centre on the blow-up, and every centre lies in the smooth open `{u/π invertible}` of the
`π`-chart. -/
theorem locusBlowup_centre (V : RiemannZariskiSpace L) (hO : ∀ r, ι r ∈ V.valuationSubring)
    (hu : ι (coordinate (π * (π * b)) 0) / ι (algebraMap A _ π) ∈ V.valuationSubring)
    (hu' : ι (algebraMap A _ π) / ι (coordinate (π * (π * b)) 0) ∈ V.valuationSubring)
    (hv : ι (coordinate (π * (π * b)) 1) / ι (algebraMap A _ π) ∈ V.valuationSubring)
    {η : Spec (.of L) ⟶ affineBlowup (locusIdeal π b)}
    (hη : η ≫ affineBlowupStructure (locusIdeal π b) = Spec.map (CommRingCat.ofHom ι)) :
    (∃ y, IsCentre η V y) ∧ ∀ y, IsCentre η V y → y ∈ locusBlowupSmoothOpen π b := by
  have hιu : ι (coordinate (π * (π * b)) 0) ≠ 0 :=
    (map_ne_zero_iff ι hι).mpr (coordinate_ne_zero π b 0)
  have hιπ : ι (algebraMap A _ π) ≠ 0 := (map_ne_zero_iff ι hι).mpr (algebraMap_ne_zero π b)
  have hg₀ := piChartRingHom_mem π b hι hO hu hv
  have : IsIso (affineBlowupStructure (locusIdeal π b) ∣_ PrimeSpectrum.basicOpen
      (algebraMap A (Node A (π * (π * b))) π)) :=
    affineBlowupStructure_restrict_isIso _ _ (algebraMap_mem_locusIdeal π b)
      (algebraMap_ne_zero π b)
  have hcomp : Spec.map (CommRingCat.ofHom (piChartRingHom π b hι)) ≫ piChartInclusion π b ≫
      affineBlowupStructure (locusIdeal π b) = Spec.map (CommRingCat.ofHom ι) := by
    rw [piChartInclusion, chartInclusion_structure, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      piChartRingHom_comp]
  have hη₀ : Spec.map (CommRingCat.ofHom (piChartRingHom π b hι)) ≫ piChartInclusion π b = η := by
    refine eq_of_comp_eq_of_isIso_restrict (affineBlowupStructure (locusIdeal π b))
      (PrimeSpectrum.basicOpen (algebraMap A (Node A (π * (π * b))) π)) ?_ ?_
    · rw [Category.assoc, hcomp, hη]
    · intro z
      rw [Category.assoc, hcomp]
      exact specMap_mem_basicOpen ι hιπ z
  have hcen : IsCentre η V
      (piChartInclusion π b (affineCentre (piChartRingHom π b hι) V hg₀)) := by
    rw [← hη₀]
    exact (isCentre_affineCentre (piChartRingHom π b hι) V hg₀).comp (piChartInclusion π b)
  refine ⟨⟨_, hcen⟩, fun y hy ↦ ?_⟩
  rw [hy.unique hcen, locusBlowupSmoothOpen, Scheme.Hom.apply_mem_image_iff]
  change coordinate b 0 ∉ (affineCentre (piChartRingHom π b hι) V hg₀).asIdeal
  rw [mem_affineCentre_asIdeal_iff]
  have hx : (piChartRingHom π b hι) (coordinate b 0) =
      ι (coordinate (π * (π * b)) 0) / ι (algebraMap A _ π) := piChartRingHom_coordinate0 π b hι
  exact not_mem_maximalIdeal_of_inv_mem (V := V.valuationSubring) (hg₀ (coordinate b 0))
    (by rw [hx, inv_div]; exact hu') (by rw [hx]; exact div_ne_zero hιu hιπ)

end Centre

end DeJongAlterations.StableModification.Gluing.LocusBlowup
