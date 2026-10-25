import DeJongAlterations.StableModification.Resolution.GlobalStages
import DeJongAlterations.StableModification.Resolution.Strictify

/-!
# Regularity, normal crossings and the assembly of the resolution

At the end of the two stages (`GlobalStages`) every closed point of the modification `C'` has a
formal regular chart (`RegChart`) for the pulled back boundary ideal sheaves `E'`. Then
(blueprint `def:sm-dj-formal-nc`, `thm:sm-dj-nc-resolution`, `thm:sm-dj-semistable-resolution`):

* `RegChart.isRegularLocalRing`, `RegChart.linearIndependent`: the chart coordinates are a regular
  system of parameters of `Ô_{C',y}`;
* `RegChart.map_radical_iInf`: the radical of `⋂ E'_β` has trace `(∏_{j ∈ A} T_j)` — the product
  of the coordinates occurring in some boundary monomial (`⊆` since the `T_j` are prime, END-SNC's
  `prime_param`, `span_prod_param_eq_inf`; `⊇` since this product comes from `𝒪_{C',y}` up to a
  unit, `RegChart.rad`, and extension to the completion is faithfully flat);
* `regular_and_normalCrossings_of_regChart`: `C'` is regular and `⋃ supp E'_β` is a normal
  crossings divisor (`Strictify.IsNormalCrossings`, the completed-local form of de Jong 2.4);
* `exists_alterationWithBoundary_of_regChart`: composing with the strictification of lane END-SNC
  (`Strictify.exists_alterationWithBoundary`, de Jong 2.4) gives an `AlterationWithBoundary`
  whose alteration is a modification.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

namespace DeJongAlterations.StableModification.Resolution.Global

set_option backward.isDefEq.respectTransparency false

open Strictify Algebra.NodeFittingIdealSheaf
open Algebra.CompletionRegularityBasics

universe u

section RegChartAlgebra

variable {O : Type*} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] {ι : Type*} {m : ℕ}
  {E : ι → Ideal O}

local notation "Rh" => AdicCompletion (maximalIdeal O) O

namespace RegChart

variable (c : RegChart O m E)

theorem T_mem (j : Fin (m + 1)) : c.T j ∈ maximalIdeal Rh :=
  c.span_eq ▸ Ideal.subset_span ⟨j, rfl⟩

/-- The coordinates of a regular chart, as elements of the maximal ideal. -/
def t (j : Fin (m + 1)) : maximalIdeal Rh := ⟨c.T j, c.T_mem j⟩

/-- A regular chart on a ring of dimension at least `m + 1` makes `Ô` regular. -/
theorem isRegularLocalRing (c : RegChart O m E) (hdim : (m + 1 : WithBot ℕ∞) ≤ ringKrullDim O) :
    IsRegularLocalRing Rh :=
  isRegularLocalRing_of_span_eq c.T c.span_eq (by
    have := hdim.trans (Algebra.CompletionRegularityAscent.ringKrullDim_le_completion O)
    exact_mod_cast this)

/-- The coordinates of a regular chart are a regular system of parameters. -/
theorem linearIndependent (hdim : (m + 1 : WithBot ℕ∞) ≤ ringKrullDim O) :
    LinearIndependent (ResidueField Rh) fun j ↦ (maximalIdeal Rh).toCotangent (c.t j) := by
  have := c.isRegularLocalRing hdim
  have hspan := cotangent_span_top_of_span_eq c.t c.span_eq
  refine linearIndependent_of_top_le_span_of_card_eq_finrank hspan ?_
  have hle : Module.finrank (ResidueField Rh) (CotangentSpace Rh) ≤ m + 1 := by
    have := finrank_range_le_card (R := ResidueField Rh)
      (fun j ↦ (maximalIdeal Rh).toCotangent (c.t j))
    rw [Set.finrank, top_le_iff.mp hspan, finrank_top, Fintype.card_fin] at this
    exact this
  have hge : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ Module.finrank (ResidueField Rh) (CotangentSpace Rh) := by
    rw [(IsRegularLocalRing.iff_finrank_cotangentSpace Rh).mp inferInstance]
    have := hdim.trans (Algebra.CompletionRegularityAscent.ringKrullDim_le_completion O)
    exact_mod_cast this
  have hge' : m + 1 ≤ Module.finrank (ResidueField Rh) (CotangentSpace Rh) := by exact_mod_cast hge
  rw [Fintype.card_fin]
  change m + 1 = Module.finrank (ResidueField Rh) (CotangentSpace Rh)
  omega

/-- The product of the boundary coordinates is the product over the coordinates occurring in some
boundary monomial. -/
theorem prod_boundaryExp [DecidablePred fun j ↦ ∃ β, c.exp β j ≠ 0] :
    ∏ j, c.T j ^ boundaryExp c.exp j =
      ∏ j ∈ Finset.univ.filter (fun j ↦ ∃ β, c.exp β j ≠ 0), (c.t j : Rh) := by
  rw [Finset.prod_filter]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  unfold boundaryExp
  split_ifs <;> simp [t]

/-- **The formal ideal of the boundary at a regular chart**: the radical of `⋂ E_β` has trace
`(∏_{j ∈ A} T_j)`, `A` the set of coordinates occurring in some boundary monomial. -/
theorem map_radical_iInf [Fintype ι] (c : RegChart O m E)
    (hdim : (m + 1 : WithBot ℕ∞) ≤ ringKrullDim O) :
    ((⨅ β, E β).radical).map (algebraMap O Rh) =
      Ideal.span {∏ j, c.T j ^ boundaryExp c.exp j} := by
  classical
  have hreg := c.isRegularLocalRing hdim
  have hli := c.linearIndependent hdim
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro h hh
    obtain ⟨M, hM⟩ := hh
    rw [Ideal.mem_comap, c.prod_boundaryExp, span_prod_param_eq_inf c.t hli]
    simp only [Submodule.mem_finsetInf]
    intro j hj
    obtain ⟨β, hβ⟩ := (Finset.mem_filter.mp hj).2
    have hβM : algebraMap O Rh (h ^ M) ∈ Ideal.span {∏ i, c.T i ^ c.exp β i} := by
      rw [← c.trace_E β]
      exact Ideal.mem_map_of_mem _ ((Submodule.mem_iInf _).mp hM β)
    have hdvd : (c.t j : Rh) ∣ algebraMap O Rh h ^ M := by
      rw [← map_pow]
      refine dvd_trans ?_ (Ideal.mem_span_singleton.mp hβM)
      exact dvd_trans (dvd_pow_self _ hβ) (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
    exact Ideal.mem_span_singleton.mpr ((prime_param c.t hli j).dvd_of_dvd_pow hdvd)
  · obtain ⟨f, hf⟩ := c.rad
    set Pm := ∏ j, c.T j ^ boundaryExp c.exp j
    -- a bound for all boundary exponents
    let M : ℕ := ∑ β, ∑ j, c.exp β j + 1
    have hexpM : ∀ β j, c.exp β j ≤ M * boundaryExp c.exp j := by
      intro β j
      unfold boundaryExp
      split_ifs with hj
      · have h1 : c.exp β j ≤ ∑ j, c.exp β j :=
          Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
        have h2 : ∑ j, c.exp β j ≤ ∑ β, ∑ j, c.exp β j :=
          Finset.single_le_sum (f := fun β ↦ ∑ j, c.exp β j) (fun _ _ ↦ Nat.zero_le _)
            (Finset.mem_univ β)
        simp only [M]
        omega
      · push Not at hj
        simp [hj β]
    have hfrad : f ∈ (⨅ β, E β).radical := by
      refine ⟨M, (Submodule.mem_iInf _).mpr fun β ↦ ?_⟩
      rw [← comap_map O (E β), Ideal.mem_comap, c.trace_E β, map_pow]
      have hPf : Pm ∣ algebraMap O Rh f :=
        Ideal.mem_span_singleton.mp (hf ▸ Ideal.mem_span_singleton_self _)
      refine Ideal.mem_span_singleton.mpr (dvd_trans ?_ (pow_dvd_pow_of_dvd hPf M))
      rw [show Pm ^ M = ∏ j, (c.T j ^ boundaryExp c.exp j) ^ M from (Finset.prod_pow _ _ _).symm]
      refine Finset.prod_dvd_prod_of_dvd _ _ fun j _ ↦ ?_
      rw [← pow_mul, mul_comm]
      exact pow_dvd_pow _ (hexpM β j)
    rw [← hf, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ hfrad

end RegChart

end RegChartAlgebra

section Geometry

variable {k : Type u} [Field k] [IsAlgClosed k] {ι : Type*}

/-- **Regularity and normal crossings from regular charts** (blueprint `thm:sm-dj-nc-resolution`).
If every closed point of the integral `k`-scheme `X'` of dimension `m + 1` has a formal regular
chart for the boundary ideal sheaves `E'`, then `X'` is regular and the union of the supports of
the `E'` is a normal crossings divisor. -/
theorem regular_and_normalCrossings_of_regChart {X' : Scheme.{u}} [IsIntegral X']
    [IsLocallyNoetherian X'] (q : X' ⟶ Spec (.of k)) [LocallyOfFiniteType q] {m : ℕ}
    (hdim : topologicalKrullDim X' = (m + 1 : ℕ)) [Fintype ι] (E' : ι → X'.IdealSheafData)
    (h : ∀ y : X', IsClosed ({y} : Set X') →
      Nonempty (RegChart (X'.presheaf.stalk y) m fun β ↦ stalkIdeal (E' β) y)) :
    IsRegularScheme X' ∧ IsNormalCrossings (⨅ β, E' β).support := by
  classical
  have hdimy : ∀ y : X', IsClosed ({y} : Set X') →
      (m + 1 : WithBot ℕ∞) ≤ ringKrullDim (X'.presheaf.stalk y) := by
    intro y hy
    rw [ringKrullDim_stalk_eq_of_isClosed q y hy, hdim]
    simp
  refine ⟨isRegularScheme_of_closedPoints q fun y hy ↦ ?_, fun y hy ↦ ?_⟩
  · obtain ⟨c⟩ := h y hy
    have := c.isRegularLocalRing (hdimy y hy)
    exact Algebra.CompletionRegularity.isRegularLocalRing_of_completion _
  · obtain ⟨c⟩ := h y hy
    refine ⟨{ n := m + 1
              t := c.t
              indep := c.linearIndependent (hdimy y hy)
              span_eq := c.span_eq
              A := fun _ ↦ Finset.univ.filter fun j ↦ ∃ β, c.exp β j ≠ 0
              disjoint := fun l l' hll' ↦ absurd (Subsingleton.elim l l') hll'
              formalIdeal_eq := fun _ ↦ ?_ }⟩
    rw [formalIdeal, localIdeal_support, stalkIdeal_iInf]
    rw [show X'.toCompletedLocalRing y = algebraMap _ _ from rfl,
      c.map_radical_iInf (hdimy y hy), c.prod_boundaryExp]

omit [IsAlgClosed k] in
/-- A point lies in the support of a finite infimum of ideal sheaves iff it lies in one of the
supports. -/
theorem mem_support_iInf_iff {X : Scheme.{u}} [Finite ι] (E : ι → X.IdealSheafData) (x : X) :
    x ∈ (⨅ β, E β).support ↔ ∃ β, x ∈ (E β).support := by
  simp only [mem_support_iff_stalkIdeal_ne_top, stalkIdeal_iInf, ne_eq, iInf_eq_top, not_forall]

/-- **Assembly** (blueprint `thm:sm-dj-semistable-resolution`). Let `p : C → Spec k` be a projective
variety of dimension `m + 1` with boundary ideal sheaves `E`, and `Z₀` the union of their
supports. If some integral projective modification `π : C' → C` has formal regular charts for the
pulled back boundary ideals at all closed points, then `(C, Z₀)` has an alteration with boundary
which is a modification (`C'` is regular, `π⁻¹ Z₀` has normal crossings, and the strictification
of lane END-SNC, `Strictify.exists_alterationWithBoundary`, makes it strict). -/
theorem exists_alterationWithBoundary_of_regChart {C : Scheme.{u}} (p : C ⟶ Spec (.of k))
    [IsVariety p] {m : ℕ} (hdim : topologicalKrullDim C = (m + 1 : ℕ)) [Fintype ι]
    (E : ι → C.IdealSheafData) (Z₀ : Set C) (hZ₀ : ∀ x, x ∈ Z₀ ↔ ∃ β, x ∈ (E β).support)
    (h : ∃ (C' : Scheme.{u}) (_ : IsIntegral C') (_ : IsLocallyNoetherian C') (π : C' ⟶ C),
      IsModification π ∧ IsProjectiveOver (π ≫ p) ∧
      ∀ y : C', IsClosed ({y} : Set C') →
        Nonempty (RegChart (C'.presheaf.stalk y) m fun β ↦ stalkIdeal ((E β).comap π) y)) :
    ∃ d : AlterationWithBoundary p Z₀, IsModification d.alteration := by
  obtain ⟨C', _, _, π, hmod, hproj, hchart⟩ := h
  have : IsModification π := hmod
  have : IsProper (π ≫ p) := hproj.isProper
  have : IsVariety (π ≫ p) := { }
  have hdim' : topologicalKrullDim C' = (m + 1 : ℕ) := by
    rw [DeJong.topologicalKrullDim_eq_of_isModification p π, hdim]
  obtain ⟨hreg, hnc⟩ := regular_and_normalCrossings_of_regChart (π ≫ p) hdim'
    (fun β ↦ (E β).comap π) hchart
  obtain ⟨d', hd'⟩ := Strictify.exists_alterationWithBoundary (π ≫ p) hproj hreg _ hnc
  have hZ' : ((⨅ β, (E β).comap π).support : Set C') = π ⁻¹' Z₀ := by
    ext y
    rw [SetLike.mem_coe, mem_support_iInf_iff, Set.mem_preimage, hZ₀]
    simp only [Scheme.IdealSheafData.support_comap]
    rfl
  have : IsModification d'.alteration := hd'
  refine ⟨
    { source := d'.source
      compactification := d'.compactification
      sourceStructure := d'.sourceStructure
      compactificationStructure := d'.compactificationStructure
      alteration := d'.alteration ≫ π
      inclusion := d'.inclusion
      boundary := d'.boundary
      sourceVariety := d'.sourceVariety
      compactificationVariety := d'.compactificationVariety
      alterationOver := by rw [Category.assoc]; exact d'.alterationOver
      inclusionOver := d'.inclusionOver
      isAlteration := @IsModification.toIsAlteration _ _ _ (IsModification.comp _ _)
      isOpenImmersion := d'.isOpenImmersion
      projective := d'.projective
      regular := d'.regular
      normalCrossings := d'.normalCrossings
      boundarySupport := ?_ }, IsModification.comp _ _⟩
  rw [d'.boundarySupport]
  congr 2
  ext y
  exact Set.ext_iff.mp hZ' (d'.alteration y)

end Geometry

end DeJongAlterations.StableModification.Resolution.Global
