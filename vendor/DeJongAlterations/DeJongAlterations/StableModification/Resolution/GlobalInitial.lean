import DeJongAlterations.StableModification.Resolution.GlobalSections
import DeJongAlterations.StableModification.Resolution.GlobalParameters

/-!
# Algebraic inputs of the initial charts

Ingredients of the formal charts of a nodal curve `g : C → Y` at the closed points of `C`, the
starting point of de Jong's resolution (de Jong 1996, 3.3–3.5, 4.23–4.27,
`references/dejong96-alterations/tex/page-0013.tex`–`page-0015.tex`, `page-0026.tex`,
`page-0027.tex`; blueprint chapter `sm-dj-resolution-global.tex`, `lem:sm-dj-initial-charts`):

* `exists_colonIter_stable`, `NodeChart.n_le_of_iterColon_eq`: on a quasi-compact locally
  Noetherian scheme the iterated colons `(N : E^L)` stabilize, which bounds the exponents `n_i` of
  all node charts uniformly (the bound `B` of the stage-one invariant `Stage1Inv`; de Jong 3.4 uses
  the finiteness of the set of possible `n_T` instead);
* `exists_adapted_parameters`: a regular system of parameters at a point of `Y` containing the
  local equations of the components of the strict normal crossings divisor through it
  (`exists_component_parameters`, `Strictify.exists_extend_parameters`);
* `span_regCoords_eq`, `exists_nodeModel_ringEquiv`: from the local models of lane END-LOC
  (`Ô_{C,x} ≅ Ô_{Y,y}[[w]]` or `Ô_{Y,y}[[u, v]]/(uv - ∏ t_i^{n_i})`) to the coordinates of a
  formal regular chart (`RegChart`) and to a formal node chart (`NodeChart`), with the
  recognition lemma `exists_nodeModel_algEquiv`;
* `ringKrullDim_powerSeries_eq`, `ringKrullDim_splitNodeRing_eq`: both local models have dimension
  `dim Y + 1`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

namespace DeJongAlterations.StableModification.Resolution.Global

set_option backward.isDefEq.respectTransparency false

open Strictify Algebra.NodeFittingIdealSheaf

universe u

section Stable

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- Iterated colon ideal sheaves increase. -/
theorem colonIter_mono (J K : X.IdealSheafData) : Monotone (colonIter J K) :=
  monotone_nat_of_le_succ fun l ↦ by
    have : colonIter J K (l + 1) = colonIdealSheaf (colonIter J K l) K :=
      Function.iterate_succ_apply' _ _ _
    rw [this]
    exact le_colonIdealSheaf _ _

/-- **The iterated colons stabilize** on a quasi-compact locally Noetherian scheme: there is `L`
such that `(N : K^L) = (N : K^{L+1})` at every point, for finitely many `K`. -/
theorem exists_colonIter_stable [CompactSpace X] {ι : Type*} [Finite ι] (N : X.IdealSheafData)
    (E : ι → X.IdealSheafData) :
    ∃ L : ℕ, ∀ β x, stalkIdeal (colonIter N (E β) L) x =
      stalkIdeal (colonIter N (E β) (L + 1)) x := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have hU : ∀ (U : X.affineOpens) (β : ι), ∃ L, ∀ l, L ≤ l →
      (colonIter N (E β) L).ideal U = (colonIter N (E β) l).ideal U := by
    intro U β
    have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    exact monotone_stabilizes_iff_noetherian.mpr inferInstance
      ⟨fun l ↦ (colonIter N (E β) l).ideal U, fun a b hab ↦ colonIter_mono N (E β) hab U⟩
  choose L hL using hU
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens ↦ (U.1 : Set X))
    (fun U ↦ U.1.isOpen) (fun x _ ↦ by
      obtain ⟨U, hxU⟩ := exists_affineOpens_mem x
      exact Set.mem_iUnion.mpr ⟨U, hxU⟩)
  refine ⟨t.sup fun U ↦ Finset.univ.sup (L U), fun β x ↦ ?_⟩
  obtain ⟨U, hUt, hxU⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  have hle : L U β ≤ t.sup fun U ↦ Finset.univ.sup (L U) :=
    (Finset.le_sup (f := L U) (Finset.mem_univ β)).trans
      (Finset.le_sup (f := fun U ↦ Finset.univ.sup (L U)) hUt)
  rw [stalkIdeal_eq_map_germ _ U hxU, stalkIdeal_eq_map_germ _ U hxU, ← hL U β _ hle,
    ← hL U β _ (hle.trans (Nat.le_succ _))]

end Stable

section NodeBound

variable {k : Type*} [Field k] {m : ℕ}

/-- `(U, V, Z^a) ⊆ (U, V, Z^b)` forces `b ≤ a`, for `b ≤ n`. -/
theorem le_of_nIdeal_le (n : Fin m → ℕ) {a b : Fin m → ℕ} (hb : b ≤ n)
    (h : nIdeal k n a ≤ nIdeal k n b) : b ≤ a := by
  have ha : nodeZMon k n a ∈ nIdeal k n b := h (Ideal.subset_span (by simp))
  rw [nodeZMon, mk_mem_nIdeal_iff k n b hb, zMon_eq_monomial,
    truncate_monomial _ _ _ (zExp_uv a), monomial_one_dvd_iff] at ha
  have hle : zExp b ≤ zExp a := by
    by_contra hne
    have := ha (zExp a) hne
    rw [MvPowerSeries.coeff_monomial_same] at this
    exact one_ne_zero this
  intro l
  have := hle l.succ.succ
  rwa [zExp_apply_succ_succ, zExp_apply_succ_succ] at this

/-- **A uniform bound for the node exponents.** If the iterated colon `(N : E_α^L)` is stable at
a node chart with `exp α = e_i`, then `n_i ≤ L`. -/
theorem NodeChart.n_le_of_iterColon_eq {O : Type*} [CommRing O] [IsLocalRing O]
    [IsNoetherianRing O] {ι : Type*} {N : Ideal O} {E : ι → Ideal O}
    (c : NodeChart k O m N E) (α : ι) (i : Fin m) (hi : c.exp α = Pi.single i 1) (L : ℕ)
    (hL : (fun J : Ideal O ↦ J.colon ((E α : Ideal O) : Set O))^[L] N =
      (fun J : Ideal O ↦ J.colon ((E α : Ideal O) : Set O))^[L + 1] N) :
    c.n i ≤ L := by
  have h1 := c.trace_iterColon α L
  have h2 := c.trace_iterColon α (L + 1)
  rw [hL, h2] at h1
  have h3 : nIdeal k c.n (c.n - (L + 1) • c.exp α) = nIdeal k c.n (c.n - L • c.exp α) := by
    have := congrArg (Ideal.comap c.e) h1
    rwa [Ideal.comap_map_of_bijective _ c.e.bijective,
      Ideal.comap_map_of_bijective _ c.e.bijective] at this
  have h4 := le_of_nIdeal_le (k := k) c.n (a := c.n - (L + 1) • c.exp α)
    (b := c.n - L • c.exp α) (fun l ↦ Nat.sub_le _ _) h3.le i
  rw [hi] at h4
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h4
  omega

end NodeBound

section Parameters

variable {Y : Scheme.{u}}

/-- **Regular parameters adapted to a strict normal crossings divisor.** At a point `y` with
`𝒪_{Y,y}` regular of dimension `m`, the local equations `t_D` of the components `D ∋ y` of `B`
(`exists_component_parameters`) extend to a regular system of parameters `z_1, …, z_m`, with
`t_D = z_{j(D)}` for an injective `j`. -/
theorem exists_adapted_parameters [IsNoetherian Y] (B : Y.IdealSheafData)
    (hB : IsStrictNormalCrossings B) (y : Y) [IsRegularLocalRing (Y.presheaf.stalk y)] {m : ℕ}
    (hm : ringKrullDim (Y.presheaf.stalk y) = m) :
    ∃ (z : Fin m → Y.presheaf.stalk y) (j : {D : DivisorComponent B // y ∈ D.val} → Fin m),
      Function.Injective j ∧ Ideal.span (Set.range z) = maximalIdeal (Y.presheaf.stalk y) ∧
      (∀ l, z l ∉ maximalIdeal (Y.presheaf.stalk y) ^ 2) ∧
      (∀ D, stalkIdeal (Scheme.IdealSheafData.vanishingIdeal D.1.val) y = Ideal.span {z (j D)}) ∧
      stalkIdeal B y = Ideal.span {∏ᶠ D, z (j D)} := by
  classical
  set R := Y.presheaf.stalk y
  obtain ⟨t, ht1, ht2, hli⟩ := exists_component_parameters B hB y
  let K := {D : DivisorComponent B // y ∈ D.val}
  have : Finite K := inferInstance
  let : Fintype K := Fintype.ofFinite K
  let eK := Fintype.equivFin K
  let t' : Fin (Fintype.card K) → maximalIdeal R := t ∘ eK.symm
  have hli' : LinearIndependent (ResidueField R)
      fun i ↦ (maximalIdeal R).toCotangent (t' i) :=
    hli.comp eK.symm eK.symm.injective
  obtain ⟨e, T, hTt, hT, hTspan⟩ := exists_extend_parameters t' hli'
  have hcard : Fintype.card K + e = m := by
    have h1 := hT.fintype_card_le_finrank
    rw [Fintype.card_fin, ← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace] at h1
    have h2 : (maximalIdeal R).spanFinrank ≤ Fintype.card K + e := by
      rw [← hTspan]
      refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)).trans ?_
      rw [← Set.image_univ]
      exact (Set.ncard_image_le Set.finite_univ).trans (by simp)
    have h3 := (isRegularLocalRing_iff R).mp inferInstance
    rw [hm] at h3
    have h4 : (maximalIdeal R).spanFinrank = m := by exact_mod_cast h3
    omega
  set z : Fin m → R := fun l ↦ (T (Fin.cast hcard.symm l) : R) with hz
  set j : K → Fin m := fun D ↦ Fin.cast hcard (Fin.castAdd e (eK D)) with hj
  have hzj : ∀ D, z (j D) = t D := by
    intro D
    simp only [hz, hj, Fin.cast_cast, Fin.cast_eq_self, hTt, t', Function.comp_apply,
      Equiv.symm_apply_apply]
  refine ⟨z, j, fun D D' h ↦ eK.injective (Fin.castAdd_injective _ _ (Fin.cast_injective _ h)),
    ?_, fun l hl ↦ ?_, fun D ↦ by rw [hzj, ht1], by rw [ht2]; simp only [hzj]⟩
  · rw [← hTspan]
    congr 1
    ext a
    simp only [Set.mem_range, hz]
    constructor
    · rintro ⟨l, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨l, rfl⟩; exact ⟨Fin.cast hcard l, by simp⟩
  · have hne := hT.ne_zero (Fin.cast hcard.symm l)
    exact hne ((Ideal.toCotangent_eq_zero _ _).mpr hl)

end Parameters

section ChartAlgebra

open Algebra.CompletionLocalMap MvPowerSeries

variable {R O : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing O]
  [IsLocalRing O] [IsNoetherianRing O] (ψ : R →+* O) [IsLocalHom ψ]

local notation "Rh" => AdicCompletion (maximalIdeal R) R
local notation "Oh" => AdicCompletion (maximalIdeal O) O

/-- Generators of `𝔪_R` generate `𝔪_{R̂}`. -/
theorem span_algebraMap_eq_maximalIdeal {m : ℕ} (z : Fin m → R)
    (hz : Ideal.span (Set.range z) = maximalIdeal R) :
    Ideal.span (Set.range fun l ↦ algebraMap R Rh (z l)) = maximalIdeal Rh := by
  rw [AdicCompletion.maximalIdeal_eq_map, ← hz, Ideal.map_span, ← Set.range_comp]
  rfl

/-- **The coordinates of a regular chart** at a point with smooth fibre: if
`φ : Ô ≃ R̂[[w]]` over `R̂`, the coordinate `φ⁻¹ w` and the images of a regular system of
parameters `z` of `R` generate `𝔪_{Ô}`. -/
theorem span_regCoords_eq {m : ℕ} (z : Fin m → R) (hz : Ideal.span (Set.range z) = maximalIdeal R)
    (φ : Oh ≃+* PowerSeries Rh) (hφ : ∀ a, φ (completionMap ψ a) = PowerSeries.C a) :
    Ideal.span (Set.range (Fin.cons (φ.symm PowerSeries.X)
      fun l ↦ algebraMap O Oh (ψ (z l)) : Fin (m + 1) → Oh)) = maximalIdeal Oh := by
  have h1 := maximalIdeal_powerSeries (A := Rh) _ (span_algebraMap_eq_maximalIdeal z hz)
  have h2 : maximalIdeal Oh = (maximalIdeal (PowerSeries Rh)).map φ.symm :=
    (IsLocalRing.map_ringEquiv_maximalIdeal φ.symm).symm
  rw [h2, h1, Ideal.map_span, Fin.range_cons, Set.image_insert_eq, ← Set.range_comp,
    ← Set.range_comp]
  congr 3
  funext l
  apply φ.injective
  simp only [Function.comp_apply, RingEquiv.apply_symm_apply]
  rw [← completionMap_algebraMap ψ, hφ]

/-- **Recognition of the initial node chart.** If `φ : Ô ≃ R̂[[u, v]]/(uv - ∏ ẑ_i^{n_i})` over
`R̂`, for a regular system of parameters `z` of `R` and `∑ n_i ≥ 1`, and `dim Ô ≥ m + 1`, then
`Ô` is the formal node model `k[[U, V, Z]]/(UV - ∏ Z_i^{n_i})` with `U, V ↦ φ⁻¹ u, φ⁻¹ v` and
`Z_i ↦ ψ(z_i)`. -/
theorem exists_nodeModel_ringEquiv {k : Type*} [Field k] [Algebra k Oh]
    (hres : Function.Surjective (algebraMap k (ResidueField Oh)))
    {m : ℕ} (z : Fin m → R) (hz : Ideal.span (Set.range z) = maximalIdeal R)
    (n : Fin m → ℕ) (hn : ∑ i, n i ≠ 0) (h : Rh) (hh : h = ∏ i, algebraMap R Rh (z i) ^ n i)
    (φ : Oh ≃+* SplitNodeRing Rh h)
    (hφ : ∀ a, φ (completionMap ψ a) = Ideal.Quotient.mk _ (C a))
    (hdim : (m + 1 : WithBot ℕ∞) ≤ ringKrullDim Oh) :
    ∃ e : NodeModel k n ≃+* Oh, e (nodeU k n) = φ.symm (splitNodeCoordinate Rh h 0) ∧
      e (nodeV k n) = φ.symm (splitNodeCoordinate Rh h 1) ∧
      ∀ i, e (nodeZ k n i) = algebraMap O Oh (ψ (z i)) := by
  subst hh
  let π : MvPowerSeries (Fin 2) Rh →+* SplitNodeRing Rh (∏ i, algebraMap R Rh (z i) ^ n i) :=
    Ideal.Quotient.mk _
  have : IsLocalRing (SplitNodeRing Rh (∏ i, algebraMap R Rh (z i) ^ n i)) := φ.isLocalRing
  have hmaxS := maximalIdeal_mvPowerSeries_fin_two (A := Rh) _
    (span_algebraMap_eq_maximalIdeal z hz)
  have hmaxO : maximalIdeal Oh =
      (maximalIdeal (SplitNodeRing Rh (∏ i, algebraMap R Rh (z i) ^ n i))).map φ.symm :=
    (IsLocalRing.map_ringEquiv_maximalIdeal φ.symm).symm
  have hz' : ∀ l, φ.symm (π (C (algebraMap R Rh (z l)))) = algebraMap O Oh (ψ (z l)) := by
    intro l
    apply φ.injective
    rw [RingEquiv.apply_symm_apply, ← completionMap_algebraMap ψ, hφ]
  have hspan : Ideal.span (insert (φ.symm (π (X 0))) (insert (φ.symm (π (X 1)))
      (Set.range fun l ↦ algebraMap O Oh (ψ (z l))))) = maximalIdeal Oh := by
    rw [hmaxO, ← map_maximalIdeal_of_surjective π Ideal.Quotient.mk_surjective, hmaxS,
      Ideal.map_span, Ideal.map_span, Set.image_image, Set.image_insert_eq, Set.image_insert_eq,
      ← Set.range_comp, ← Set.range_comp]
    simp only [Function.comp_def, hz']
  have hrel : φ.symm (π (X 0)) * φ.symm (π (X 1)) =
      ∏ i, (algebraMap O Oh (ψ (z i))) ^ n i := by
    have hrel : π (X 0 * X 1) = π (C (∏ i, algebraMap R Rh (z i) ^ n i)) := by
      rw [← sub_eq_zero, ← map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    calc φ.symm (π (X 0)) * φ.symm (π (X 1)) = φ.symm (π (X 0 * X 1)) := by
          rw [map_mul, map_mul]
      _ = φ.symm (π (C (∏ i, algebraMap R Rh (z i) ^ n i))) := congrArg (fun t ↦ φ.symm t) hrel
      _ = ∏ i, φ.symm (π (C (algebraMap R Rh (z i)))) ^ n i := by
          simp only [map_prod, map_pow]
      _ = _ := by simp only [hz']
  obtain ⟨e, heU, heV, heZ⟩ := exists_nodeModel_algEquiv (k := k) n hn hres
    (φ.symm (π (X 0))) (φ.symm (π (X 1))) (fun l ↦ algebraMap O Oh (ψ (z l))) hspan hrel hdim
  exact ⟨e.toRingEquiv, heU, heV, heZ⟩

end ChartAlgebra

section Dimension

open MvPowerSeries

variable {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- `dim A[[w]] ≤ m + 1` if `𝔪_A` has `m` generators. -/
theorem ringKrullDim_powerSeries_le {m : ℕ} (z : Fin m → A)
    (hz : Ideal.span (Set.range z) = maximalIdeal A) :
    ringKrullDim (PowerSeries A) ≤ (m + 1 : ℕ) := by
  refine (ringKrullDim_le_spanFinrank_maximalIdeal _).trans ?_
  rw [maximalIdeal_powerSeries _ hz]
  have hfin : (insert (PowerSeries.X : PowerSeries A)
      ((PowerSeries.C : A →+* PowerSeries A) '' Set.range z)).Finite :=
    ((Set.finite_range z).image _).insert _
  have h1 := Submodule.spanFinrank_span_le_ncard_of_finite (R := PowerSeries A) hfin
  have h2 : (insert (PowerSeries.X : PowerSeries A)
      ((PowerSeries.C : A →+* PowerSeries A) '' Set.range z)).ncard ≤ m + 1 := by
    refine (Set.ncard_insert_le _ _).trans ?_
    gcongr
    rw [← Set.range_comp, ← Set.image_univ]
    exact (Set.ncard_image_le Set.finite_univ).trans (by simp)
  exact_mod_cast h1.trans h2

/-- `dim A[[u, v]] ≤ m + 2` if `𝔪_A` has `m` generators. -/
theorem ringKrullDim_mvPowerSeries_fin_two_le {m : ℕ} (z : Fin m → A)
    (hz : Ideal.span (Set.range z) = maximalIdeal A) :
    ringKrullDim (MvPowerSeries (Fin 2) A) ≤ (m + 2 : ℕ) := by
  refine (ringKrullDim_le_spanFinrank_maximalIdeal _).trans ?_
  rw [maximalIdeal_mvPowerSeries_fin_two _ hz]
  have hfin : (insert (X 0 : MvPowerSeries (Fin 2) A) (insert (X 1)
      ((C : A →+* MvPowerSeries (Fin 2) A) '' Set.range z))).Finite :=
    (((Set.finite_range z).image _).insert _).insert _
  have h1 := Submodule.spanFinrank_span_le_ncard_of_finite (R := MvPowerSeries (Fin 2) A) hfin
  have h2 : (insert (X 0 : MvPowerSeries (Fin 2) A) (insert (X 1)
      ((C : A →+* MvPowerSeries (Fin 2) A) '' Set.range z))).ncard ≤ m + 2 := by
    refine (Set.ncard_insert_le _ _).trans ?_
    refine (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1).trans ?_
    have : ((C : A →+* MvPowerSeries (Fin 2) A) '' Set.range z).ncard ≤ m := by
      rw [← Set.range_comp, ← Set.image_univ]
      exact (Set.ncard_image_le Set.finite_univ).trans (by simp)
    omega
  exact_mod_cast h1.trans h2

end Dimension

section RegularDimension

open MvPowerSeries

variable {A : Type*} [CommRing A] [IsRegularLocalRing A]

/-- **The dimension of the formal power series model**: `dim A[[w]] = m + 1` for a regular local
ring `A` of dimension `m`. -/
theorem ringKrullDim_powerSeries_eq {m : ℕ}
    (hm : ringKrullDim A = m) : ringKrullDim (PowerSeries A) = (m + 1 : ℕ) := by
  obtain ⟨s, hscard, hspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank (IsNoetherian.noetherian (maximalIdeal A))
  have hs : s.card = m := by
    have := (isRegularLocalRing_iff A).mp inferInstance
    rw [hm, ← hscard] at this
    exact_mod_cast this
  let z : Fin m → A := fun l ↦ (s.equivFin.symm (Fin.cast hs.symm l) : A)
  have hz : Ideal.span (Set.range z) = maximalIdeal A := by
    rw [← hspan]
    congr 1
    ext a
    simp only [Set.mem_range, Finset.mem_coe, z]
    constructor
    · rintro ⟨l, rfl⟩; exact Subtype.mem _
    · intro ha
      exact ⟨Fin.cast hs (s.equivFin ⟨a, ha⟩), by simp⟩
  refine le_antisymm (ringKrullDim_powerSeries_le z hz) ?_
  have := ringKrullDim_succ_le_ringKrullDim_powerseries (R := A)
  rw [hm] at this
  exact_mod_cast this

/-- **The dimension of the split node** `A[[u, v]]/(uv - h)` over a regular local ring `A` of
dimension `m`, `h ∈ 𝔪_A`: it is `m + 1`. -/
theorem ringKrullDim_splitNodeRing_eq {m : ℕ}
    (hm : ringKrullDim A = m) {h : A} (hh : h ∈ maximalIdeal A) :
    ringKrullDim (SplitNodeRing A h) = (m + 1 : ℕ) := by
  have : IsDomain A := Algebra.RegularLocalDomain.isDomain_of_isRegularLocalRing A
  obtain ⟨s, hscard, hspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank (IsNoetherian.noetherian (maximalIdeal A))
  have hs : s.card = m := by
    have := (isRegularLocalRing_iff A).mp inferInstance
    rw [hm, ← hscard] at this
    exact_mod_cast this
  let z : Fin m → A := fun l ↦ (s.equivFin.symm (Fin.cast hs.symm l) : A)
  have hz : Ideal.span (Set.range z) = maximalIdeal A := by
    rw [← hspan]
    congr 1
    ext a
    simp only [Set.mem_range, Finset.mem_coe, z]
    constructor
    · rintro ⟨l, rfl⟩; exact Subtype.mem _
    · intro ha
      exact ⟨Fin.cast hs (s.equivFin ⟨a, ha⟩), by simp⟩
  apply le_antisymm
  · -- the equation is a non-zero-divisor
    have hf0 : (X (0 : Fin 2) * X 1 - C h : MvPowerSeries (Fin 2) A) ≠ 0 := by
      intro h0
      classical
      have := congrArg (coeff (Finsupp.single 0 1 + Finsupp.single 1 1)) h0
      rw [map_sub, X_def, X_def, monomial_mul_monomial, coeff_monomial, if_pos rfl, coeff_C,
        if_neg, map_zero, one_mul, sub_zero] at this
      · exact one_ne_zero this
      · intro h00
        have := congrArg (fun d ↦ d 0) h00
        simp at this
    have hnzd : (X (0 : Fin 2) * X 1 - C h : MvPowerSeries (Fin 2) A) ∈
        nonZeroDivisors (MvPowerSeries (Fin 2) A) :=
      mem_nonZeroDivisors_of_ne_zero hf0
    have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnzd
    have h2 := ringKrullDim_mvPowerSeries_fin_two_le z hz
    have h3 : ringKrullDim (SplitNodeRing A h) + 1 ≤ ((m + 1 : ℕ) : WithBot ℕ∞) + 1 := by
      refine h1.trans (h2.trans ?_)
      push_cast
      rw [add_assoc]
      norm_num
    exact ENat.WithBot.add_le_add_one_right_iff.mp h3
  · have hle := Algebra.RegularQuotient.ringKrullDim_le_quotient_parameter_add_one
      (MvPowerSeries (Fin 2) A) (splitNodeEquation_mem_maximalIdeal A hh)
    have h2 := (ringKrullDim_add_two_le_mvPowerSeries_fin_two (A := A)).trans hle
    rw [hm] at h2
    have h3 : (((m + 1 : ℕ) : WithBot ℕ∞)) + 1 ≤ ringKrullDim (SplitNodeRing A h) + 1 := by
      have : ((m : ℕ) : WithBot ℕ∞) + 2 = (((m + 1 : ℕ) : WithBot ℕ∞)) + 1 := by
        push_cast
        ring
      rw [← this]
      exact h2
    exact ENat.WithBot.add_le_add_one_right_iff.mp h3

end RegularDimension

end DeJongAlterations.StableModification.Resolution.Global
