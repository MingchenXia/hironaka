/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.GenusLocal
import DeJongAlterations.StableModification.CurvesField.GenusCech
import DeJongAlterations.StableModification.Cohomology.CechPushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# The genus formula (Temkin, Lemma B.1)

Let `π : Y → X` be an affine morphism of schemes and `k → Γ(X, 𝒪_X)` a field of constants. For
every affine open `V ⊆ X` assume that `π^♯ : Γ(V, 𝒪_X) → Γ(π⁻¹V, 𝒪_Y)` is injective with
finite-dimensional cokernel (for a reduced curve `X` and its normalization `Y`: the
normalization is finite and birational, and `π_*𝒪_Y / 𝒪_X` is a skyscraper). The **δ-invariant**
`δ(x) = dim_k (π_*𝒪_Y / 𝒪_X)_x` of a point `x ∈ X` is computed in any affine chart
(`chartDelta`, independent of the chart by `chartDelta_eq`); it vanishes outside a finite set of
closed points. The **δ-formula** (`eulerChar_eq_add_finsum_delta`) states

  `χ(Y, 𝒪_Y) = χ(X, 𝒪_X) + ∑ᶠ x, δ(x)`,

equivalently `p_a(X) = p_a(Y) + ∑ᶠ x, δ(x)` for `p_a = 1 - χ(𝒪)` (`arithmeticGenus_eq`). For the
normalization `Y = C̃` of a connected reduced projective curve `C` over `k = k̄` (components
`C̃_1, …, C̃_r`, `r = |C⁰|`, of genus `g_i`) one has `χ(𝒪_{C̃}) = r - ∑ g_i` and this is Temkin's
genus formula `p_a(C) = 1 - |C⁰| + ∑_{x ∈ C} g(x)`, Lemma B.1 of M. Temkin, *Stable modification
of relative curves*, J. Algebraic Geom. 19 (2010) (`references/temkin10-stable-modification`,
`semi-stable.tex`, lines 4413–4433), with `g(x) = δ(x)` for closed points and `g(η_i) = g_i`.

The proof follows Temkin: the long exact sequence of `0 → 𝒪_X → π_*𝒪_Y → π_*𝒪_Y/𝒪_X → 0`,
`H^i(X, π_*𝒪_Y) = H^i(Y, 𝒪_Y)` for affine `π`, and the computation of the cohomology of the
skyscraper. Here cohomology is Čech cohomology for finite affine covers (`Cohomology.cohomology`),
the cokernel sheaf is replaced by the termwise cokernel of the Čech complexes (`GenusCech`), and
the skyscraper computation is the inclusion–exclusion identity
`∑_{T ≠ ∅} (-1)^{#T + 1} dim (B_T / A_T) = ∑ᶠ x, δ(x)` (`sum_cokerFinrank_eq_finsum_delta`), from
the local decomposition `dim (B_V / A_V) = ∑_{x ∈ V} δ(x)` (`cokerFinrank_eq_finsum_delta`).

## Main definitions

* `chartDelta π c V hV x hx`: `dim_k (Γ(π⁻¹V, 𝒪_Y) / Γ(V, 𝒪_X))_x` in the affine chart `V ∋ x`.
* `deltaInvariant π c x`: the δ-invariant of `x` (any affine chart); `deltaInvariant_eq_delta`
  identifies it with `CurvesField.delta` of the local ring `𝒪_{X,x}` in the semilocal ring of `Y`
  over `x`.
* `eulerChar X c = ∑ (-1)^i dim_k H^i(X, 𝒪_X)`, `arithmeticGenus X c = 1 - eulerChar X c`.

Blueprint: `sm-curves-fields-genus.tex`, `def:sm-delta-global`, `lem:sm-delta-chart`,
`thm:sm-delta-formula`, `lem:sm-genus-formula`.
-/

namespace DeJongAlterations.StableModification.CurvesField.Genus

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Module
open DeJongAlterations.StableModification.Cohomology DeJongAlterations.Geometry.ProperSteinProjectiveCech

set_option autoImplicit false

universe u

noncomputable section

variable {X Y : Scheme.{u}} (π : Y ⟶ X) {k : Type u} [Field k] (c : k →+* Γ(X, ⊤))

section Chart

/-- The δ-invariant of `x` computed in the affine chart `V ∋ x`:
`dim_k (Γ(π⁻¹V, 𝒪_Y) / Γ(V, 𝒪_X))_{𝔭_x}`. -/
def chartDelta (V : X.Opens) (hV : IsAffineOpen V) (x : X) (hx : x ∈ V) : ℕ :=
  deltaAt (sectionsRingHom c (le_top : V ≤ ⊤)) (π.app V).hom (hV.primeIdealOf ⟨x, hx⟩)

variable {π c}

lemma chartDelta_congr {V W : X.Opens} (h : V = W) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (x : X) (hx : x ∈ V) (hx' : x ∈ W) : chartDelta π c V hV x hx = chartDelta π c W hW x hx' := by
  subst h
  rfl

/-- Restricting the constants from `V` to a smaller open. -/
lemma sectionsRingHom_comp {V W : X.Opens} (h : W ≤ V) :
    (X.presheaf.map (homOfLE h).op).hom.comp (sectionsRingHom c (le_top : V ≤ ⊤)) =
      sectionsRingHom c (le_top : W ≤ ⊤) := by
  ext a
  simp only [sectionsRingHom, RingHom.coe_comp, Function.comp_apply]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- **Passing to a basic open does not change the δ-invariant.** -/
theorem chartDelta_basicOpen [IsAffineHom π] (V : X.Opens) (hV : IsAffineOpen V) (f : Γ(X, V)) (x : X)
    (hx : x ∈ X.basicOpen f) :
    chartDelta π c (X.basicOpen f) (hV.basicOpen f) x hx =
      chartDelta π c V hV x (X.basicOpen_le f hx) := by
  set ρ := (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
  set σ := (Y.presheaf.map (homOfLE (π.preimage_mono (X.basicOpen_le f))).op).hom
  have hcomm : (π.app (X.basicOpen f)).hom.comp ρ = σ.comp (π.app V).hom := by
    have := π.naturality (homOfLE (X.basicOpen_le f)).op
    exact congrArg CommRingCat.Hom.hom this
  have hρ : letI := ρ.toAlgebra; IsLocalization.Away f Γ(X, X.basicOpen f) :=
    hV.isLocalization_basicOpen f
  have hσ : letI := σ.toAlgebra; IsLocalization.Away ((π.app V).hom f) Γ(Y, π ⁻¹ᵁ X.basicOpen f) :=
    (hV.preimage π).isLocalization_of_eq_basicOpen ((π.app V).hom f)
      (homOfLE (π.preimage_mono (X.basicOpen_le f))) (Scheme.preimage_basicOpen π f)
  have key := deltaAt_away (sectionsRingHom c (le_top : V ≤ ⊤)) (π.app V).hom ρ σ
    (π.app (X.basicOpen f)).hom hcomm f hρ hσ ((hV.basicOpen f).primeIdealOf ⟨x, hx⟩)
  rw [sectionsRingHom_comp] at key
  unfold chartDelta
  rw [key]
  congr 1
  have hp := IsAffineOpen.comap_primeIdealOf_appLE (f := 𝟙 X) V hV (X.basicOpen f)
    (hV.basicOpen f) (X.basicOpen_le f) hx
  ext1
  exact congrArg PrimeSpectrum.asIdeal hp

/-- **The δ-invariant does not depend on the affine chart.** -/
theorem chartDelta_eq [IsAffineHom π] {V W : X.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (x : X) (hxV : x ∈ V) (hxW : x ∈ W) : chartDelta π c V hV x hxV = chartDelta π c W hW x hxW := by
  obtain ⟨f, hfW, hxf⟩ := hV.exists_basicOpen_le (V := W) ⟨x, hxW⟩ hxV
  obtain ⟨g, hgD, hxg⟩ := hW.exists_basicOpen_le (V := X.basicOpen f) ⟨x, hxf⟩ hxW
  have hD : IsAffineOpen (X.basicOpen f) := hV.basicOpen f
  set g' : Γ(X, X.basicOpen f) := X.presheaf.map (homOfLE hfW).op g
  have hg' : X.basicOpen g' = X.basicOpen g := by
    rw [Scheme.basicOpen_res]
    exact inf_eq_right.2 hgD
  have hxg' : x ∈ X.basicOpen g' := hg' ▸ hxg
  rw [← chartDelta_basicOpen V hV f x hxf, ← chartDelta_basicOpen W hW g x hxg,
    ← chartDelta_basicOpen (X.basicOpen f) hD g' x hxg']
  exact chartDelta_congr hg' _ _ x hxg' hxg

variable (π c) in
/-- The δ-invariant of a point: `dim_k (π_*𝒪_Y / 𝒪_X)_x`, computed in any affine chart (and `0`
if there is none). -/
def deltaInvariant (x : X) : ℕ := by
  classical
  exact if h : ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V then
    chartDelta π c h.choose h.choose_spec.1 x h.choose_spec.2 else 0

/-- The δ-invariant is computed by every affine chart. -/
theorem chartDelta_eq_deltaInvariant [IsAffineHom π] (V : X.Opens) (hV : IsAffineOpen V) (x : X)
    (hx : x ∈ V) : chartDelta π c V hV x hx = deltaInvariant π c x := by
  have h : ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V := ⟨V, hV, hx⟩
  rw [deltaInvariant, dif_pos h]
  exact chartDelta_eq hV _ x hx _

/-- **The δ-invariant is Temkin's `g(x)`**: in any affine chart `V ∋ x`, `δ(x)` is the codimension
`dim_k (B_𝔭 / A_𝔭)` of the local ring `A_𝔭 = 𝒪_{X,x}` in the semilocal ring
`B_𝔭 = Γ(π⁻¹V, 𝒪_Y)_𝔭` over `x` (`CurvesField.delta` of the image of `A_𝔭`), for
`A = Γ(V, 𝒪_X)`, `B = Γ(π⁻¹V, 𝒪_Y)` and `𝔭` the prime of `x`. -/
theorem deltaInvariant_eq_delta [IsAffineHom π] (V : X.Opens) (hV : IsAffineOpen V) (x : X)
    (hx : x ∈ V) :
    letI := (sectionsRingHom c (le_top : V ≤ ⊤)).toAlgebra
    letI := (π.app V).hom.toAlgebra
    letI := ((π.app V).hom.comp (sectionsRingHom c (le_top : V ≤ ⊤))).toAlgebra
    haveI : IsScalarTower k Γ(X, V) Γ(Y, π ⁻¹ᵁ V) := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI := isScalarTower_localization k (A := Γ(X, V)) (B := Γ(Y, π ⁻¹ᵁ V))
      (hV.primeIdealOf ⟨x, hx⟩ : PrimeSpectrum Γ(X, V)).asIdeal.primeCompl
    deltaInvariant π c x = CurvesField.delta k (IsScalarTower.toAlgHom k
      (Localization.AtPrime (hV.primeIdealOf ⟨x, hx⟩ : PrimeSpectrum Γ(X, V)).asIdeal)
      (Localization (Algebra.algebraMapSubmonoid Γ(Y, π ⁻¹ᵁ V)
        (hV.primeIdealOf ⟨x, hx⟩ : PrimeSpectrum Γ(X, V)).asIdeal.primeCompl))).range := by
  rw [← chartDelta_eq_deltaInvariant V hV x hx]
  exact deltaAt_eq_delta _ _ _

section Points

variable {V : X.Opens} (hV : IsAffineOpen V)

/-- The point of `V` corresponding to a prime of `Γ(V, 𝒪_X)`. -/
lemma fromSpec_mem (p : Spec Γ(X, V)) : hV.fromSpec p ∈ V := by
  change hV.fromSpec p ∈ (V : Set X)
  rw [← hV.range_fromSpec]
  exact ⟨p, rfl⟩

lemma primeIdealOf_fromSpec (p : Spec Γ(X, V)) :
    hV.primeIdealOf ⟨hV.fromSpec p, fromSpec_mem hV p⟩ = p :=
  hV.fromSpec.isOpenEmbedding.injective (hV.fromSpec_primeIdealOf ⟨hV.fromSpec p, _⟩)

end Points

/-- **Local decomposition of the cokernel over an affine open**: if `Γ(π⁻¹V, 𝒪_Y) / Γ(V, 𝒪_X)`
is finite-dimensional, its dimension is `∑ᶠ x ∈ V, δ(x)`, the sum having finite support. -/
theorem cokerFinrank_eq_finsum_delta [IsAffineHom π] (V : X.Opens) (hV : IsAffineOpen V)
    (hfin : IsFiniteCoker (sectionsRingHom c (le_top : V ≤ ⊤)) (π.app V).hom) :
    {x : X | x ∈ V ∧ deltaInvariant π c x ≠ 0}.Finite ∧
      cokerFinrank (sectionsRingHom c (le_top : V ≤ ⊤)) (π.app V).hom =
        ∑ᶠ x ∈ (V : Set X), deltaInvariant π c x := by
  obtain ⟨hsupp, -, hsum⟩ := cokerFinrank_eq_finsum _ _ hfin
  have hpt : ∀ p : Spec Γ(X, V),
      deltaAt (sectionsRingHom c (le_top : V ≤ ⊤)) (π.app V).hom p = deltaInvariant π c (hV.fromSpec p) := by
    intro p
    rw [← chartDelta_eq_deltaInvariant V hV _ (fromSpec_mem hV p), chartDelta, primeIdealOf_fromSpec]
  refine ⟨?_, ?_⟩
  · refine (hsupp.image hV.fromSpec).subset ?_
    rintro x ⟨hx, hδ⟩
    refine ⟨hV.primeIdealOf ⟨x, hx⟩, ?_, hV.fromSpec_primeIdealOf ⟨x, hx⟩⟩
    intro h
    apply hδ
    have := hpt (hV.primeIdealOf ⟨x, hx⟩)
    rw [hV.fromSpec_primeIdealOf ⟨x, hx⟩] at this
    exact this.symm.trans h
  · rw [hsum, ← hV.range_fromSpec, finsum_mem_range hV.fromSpec.isOpenEmbedding.injective]
    exact finsum_congr hpt

end Chart

section InclusionExclusion

open Finset

/-- Membership in a finite intersection of opens. -/
lemma mem_finsetInf {ι : Type*} (U : ι → X.Opens) (T : Finset ι) (x : X) :
    x ∈ T.inf U ↔ ∀ i ∈ T, x ∈ U i := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T _ ih =>
    rw [Finset.inf_insert, TopologicalSpace.Opens.mem_inf, ih, Finset.forall_mem_insert]

/-- The alternating count of the nonempty sets of indices all satisfying `P`, when some index
satisfies `P`, is `1`. -/
lemma sum_nonempty_neg_one_pow {ι : Type*} [Fintype ι] [DecidableEq ι] (P : ι → Prop)
    [DecidablePred P] (h : ∃ i, P i) :
    ∑ T ∈ univ.filter (fun T : Finset ι => T.Nonempty),
      (if ∀ i ∈ T, P i then (-1 : ℤ) ^ (T.card + 1) else 0) = 1 := by
  set I := univ.filter P
  have hI : I ≠ ∅ := by
    obtain ⟨i, hi⟩ := h
    exact Finset.ne_empty_of_mem (Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩)
  rw [← Finset.sum_filter, Finset.filter_filter]
  have hset : univ.filter (fun T : Finset ι => T.Nonempty ∧ ∀ i ∈ T, P i) = I.powerset.erase ∅ := by
    ext T
    simp only [mem_filter, mem_univ, true_and, mem_erase, mem_powerset, I]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨h₁.ne_empty, fun i hi => Finset.mem_filter.2 ⟨Finset.mem_univ i, h₂ i hi⟩⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨Finset.nonempty_iff_ne_empty.2 h₁, fun i hi => (Finset.mem_filter.1 (h₂ hi)).2⟩
  rw [hset, Finset.sum_erase_eq_sub (Finset.empty_mem_powerset I)]
  have h0 : ∑ T ∈ I.powerset, (-1 : ℤ) ^ (T.card + 1) = 0 := by
    have := Finset.sum_powerset_neg_one_pow_card (x := I)
    rw [if_neg hI] at this
    simp only [pow_succ, ← Finset.sum_mul, this, zero_mul]
  rw [h0]
  simp

variable [IsAffineHom π]

/-- **The skyscraper computation (inclusion–exclusion).** For a finite affine cover `U` of `X`
whose intersections have finite-dimensional cokernels, the δ-invariant has finite support and
`∑_{T ≠ ∅} (-1)^{#T + 1} dim_k (Γ(π⁻¹U_T, 𝒪_Y) / Γ(U_T, 𝒪_X)) = ∑ᶠ x, δ(x)`. -/
theorem sum_cokerFinrank_eq_finsum_delta (𝒰 : FiniteAffineCover X) [Fintype 𝒰.ι]
    (hfin : ∀ T : Finset 𝒰.ι, T.Nonempty →
      IsFiniteCoker (sectionsRingHom c (le_top : T.inf 𝒰.U ≤ ⊤)) (π.app (T.inf 𝒰.U)).hom) :
    (Function.support (deltaInvariant π c)).Finite ∧
      ∑ T ∈ univ.filter (fun T : Finset 𝒰.ι => T.Nonempty), (-1 : ℤ) ^ (T.card + 1) *
          (cokerFinrank (sectionsRingHom c (le_top : T.inf 𝒰.U ≤ ⊤)) (π.app (T.inf 𝒰.U)).hom : ℤ) =
        ((∑ᶠ x, deltaInvariant π c x : ℕ) : ℤ) := by
  classical
  have hcov : ∀ x : X, ∃ i, x ∈ 𝒰.U i := fun x => by
    have : x ∈ ⨆ i, 𝒰.U i := by rw [𝒰.iSup_eq_top]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have hloc := fun (T : Finset 𝒰.ι) (hT : T.Nonempty) =>
    cokerFinrank_eq_finsum_delta (π := π) (c := c) (T.inf 𝒰.U) (𝒰.isAffineOpen_inf T hT)
      (hfin T hT)
  have hsupp : (Function.support (deltaInvariant π c)).Finite := by
    refine (Set.finite_iUnion fun i : 𝒰.ι => (hloc {i} (Finset.singleton_nonempty i)).1).subset ?_
    intro x hx
    obtain ⟨i, hi⟩ := hcov x
    refine Set.mem_iUnion.2 ⟨i, ?_, hx⟩
    simpa using hi
  refine ⟨hsupp, ?_⟩
  set S := hsupp.toFinset
  have hS : ∀ (W : Set X), ∑ᶠ x ∈ W, deltaInvariant π c x = ∑ x ∈ S, if x ∈ W then deltaInvariant π c x else 0 := by
    intro W
    rw [finsum_mem_def, finsum_eq_sum_of_support_subset]
    · exact Finset.sum_congr rfl fun x _ => by simp [Set.indicator_apply]
    · intro x hx
      simp only [Set.Finite.coe_toFinset, S, Function.mem_support] at hx ⊢
      intro h
      apply hx
      simp [Set.indicator_apply, h]
  have hS' : ∑ᶠ x, deltaInvariant π c x = ∑ x ∈ S, deltaInvariant π c x :=
    finsum_eq_sum_of_support_subset _ (by simp [S])
  have hT : ∀ T ∈ univ.filter (fun T : Finset 𝒰.ι => T.Nonempty),
      (-1 : ℤ) ^ (T.card + 1) *
        (cokerFinrank (sectionsRingHom c (le_top : T.inf 𝒰.U ≤ ⊤)) (π.app (T.inf 𝒰.U)).hom : ℤ) =
      ∑ x ∈ S, (if ∀ i ∈ T, x ∈ 𝒰.U i then (-1 : ℤ) ^ (T.card + 1) else 0) * deltaInvariant π c x := by
    intro T hT
    have hTne : T.Nonempty := (Finset.mem_filter.1 hT).2
    rw [(hloc T hTne).2, hS, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have := mem_finsetInf 𝒰.U T x
    by_cases hx : ∀ i ∈ T, x ∈ 𝒰.U i
    · have hx' : x ∈ ((T.inf 𝒰.U : X.Opens) : Set X) := this.2 hx
      rw [if_pos hx', if_pos hx, mul_comm]
    · have hx' : x ∉ ((T.inf 𝒰.U : X.Opens) : Set X) := fun h => hx (this.1 h)
      rw [if_neg hx', if_neg hx]
      simp
  rw [Finset.sum_congr rfl hT, Finset.sum_comm, hS', Nat.cast_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_mul, sum_nonempty_neg_one_pow (fun i => x ∈ 𝒰.U i) (hcov x), one_mul]

end InclusionExclusion

section Formula

/-- The structure sheaf is quasi-coherent (it is free of rank one). -/
instance isQuasicoherent_unit (X : Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Limits.coproductUniqueIso (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf))
    (inferInstance : (SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1}).IsQuasicoherent)

variable (X) in
/-- The Euler characteristic `χ(X, 𝒪_X) = ∑ᵢ (-1)^i dim_k H^i(X, 𝒪_X)` of the structure sheaf of
a quasi-compact scheme with affine diagonal, with `k`-coefficients through `c : k → Γ(X, 𝒪_X)`
(Čech cohomology of a finite affine cover, independent of the cover by
`Cohomology.cohomologyIsoCech`). -/
def eulerChar [CompactSpace X] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    (c : k →+* Γ(X, ⊤)) : ℤ :=
  (cechComplex (SheafOfModules.unit X.ringCatSheaf) (FiniteAffineCover.choose X).U c).homologyEulerChar

variable (X) in
/-- The arithmetic genus `p_a(X) = 1 - χ(X, 𝒪_X)`; for a curve with `H^i(X, 𝒪_X) = 0` for `i ≥ 2`
this is Temkin's `p_a = 1 - h⁰(𝒪_X) + h¹(𝒪_X)` (`semi-stable.tex`, l. 4411). -/
def arithmeticGenus [CompactSpace X]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))] (c : k →+* Γ(X, ⊤)) : ℤ :=
  1 - eulerChar X c

/-- The comparison map `𝒪_X → π_*𝒪_Y`. -/
def structureMap : SheafOfModules.unit X.ringCatSheaf ⟶
    (Scheme.Modules.pushforward π).obj (SheafOfModules.unit Y.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit π.toRingCatSheafHom

/-- The comparison map on Čech diagrams `Γ(U_T, 𝒪_X) → Γ(π⁻¹U_T, 𝒪_Y)`. -/
def cechStructureMap {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    cechDiagram (SheafOfModules.unit X.ringCatSheaf) U c ⟶
      cechDiagram ((Scheme.Modules.pushforward π).obj (SheafOfModules.unit Y.ringCatSheaf)) U c :=
  sectionsDiagramMap c (structureMap π) (fun T => T.inf U) (fun _ _ h => Finset.inf_mono h)
    (fun _ => le_top)

lemma cechStructureMap_app_apply {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (T : Finset ι)
    (a : Γ(X, T.inf U)) : ((cechStructureMap π c U).app T).hom a = (π.app (T.inf U)).hom a := rfl

/-- The cokernel of the Čech comparison map is `Γ(π⁻¹V, 𝒪_Y) / Γ(V, 𝒪_X)`. -/
lemma cechCoker_equiv (V : X.Opens) :
      (FiniteDimensional k (sectionsModuleCat ((Scheme.Modules.pushforward π).obj
          (SheafOfModules.unit Y.ringCatSheaf)) c V le_top ⧸
          LinearMap.range (sectionsMap c (structureMap π) V le_top).hom) ↔
        IsFiniteCoker (sectionsRingHom c (le_top : V ≤ ⊤)) (π.app V).hom) ∧
      finrank k (sectionsModuleCat ((Scheme.Modules.pushforward π).obj
          (SheafOfModules.unit Y.ringCatSheaf)) c V le_top ⧸
          LinearMap.range (sectionsMap c (structureMap π) V le_top).hom) =
        cokerFinrank (sectionsRingHom c (le_top : V ≤ ⊤)) (π.app V).hom := by
  let ψ := sectionsRingHom c (le_top : V ≤ ⊤)
  let φ := (π.app V).hom
  let _ : Algebra k Γ(X, V) := ψ.toAlgebra
  let _ : Algebra Γ(X, V) Γ(Y, π ⁻¹ᵁ V) := φ.toAlgebra
  let _ : Algebra k Γ(Y, π ⁻¹ᵁ V) := (φ.comp ψ).toAlgebra
  have : IsScalarTower k Γ(X, V) Γ(Y, π ⁻¹ᵁ V) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let M := sectionsModuleCat ((Scheme.Modules.pushforward π).obj
    (SheafOfModules.unit Y.ringCatSheaf)) c V le_top
  let P := LinearMap.range (sectionsMap c (structureMap π) V le_top).hom
  let ι : M ≃ₗ[k] Γ(Y, π ⁻¹ᵁ V) :=
    { toFun := fun b => b
      invFun := fun b => b
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let Q : Submodule k Γ(Y, π ⁻¹ᵁ V) :=
    (LinearMap.range (Algebra.linearMap Γ(X, V) Γ(Y, π ⁻¹ᵁ V))).restrictScalars k
  have hPQ : P.map ι.toLinearMap = Q := by
    ext b
    simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.restrictScalars_mem, Q, P]
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨_, ⟨a, rfl⟩, rfl⟩
  let e : (M ⧸ P) ≃ₗ[k] Coker Γ(X, V) Γ(Y, π ⁻¹ᵁ V) :=
    (Submodule.Quotient.equiv P Q ι hPQ).trans
      (Submodule.Quotient.restrictScalarsEquiv k
        (LinearMap.range (Algebra.linearMap Γ(X, V) Γ(Y, π ⁻¹ᵁ V))))
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, e.finrank_eq⟩
  · exact Module.Finite.equiv e
  · have : FiniteDimensional k (Coker Γ(X, V) Γ(Y, π ⁻¹ᵁ V)) := h
    exact Module.Finite.equiv e.symm

variable [CompactSpace X] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
  [CompactSpace Y] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from Y))]
  [IsAffineHom π]

/-- **The δ-formula.** Let `π : Y → X` be an affine morphism of quasi-compact schemes with affine
diagonal, `k → Γ(X, 𝒪_X)` a field of constants, and assume that for every affine open `V ⊆ X` the
map `Γ(V, 𝒪_X) → Γ(π⁻¹V, 𝒪_Y)` is injective with finite-dimensional cokernel, and that the
cohomology of `𝒪_X` is finite-dimensional. Then the cohomology of `𝒪_Y` is finite-dimensional,
the δ-invariant has finite support, and `χ(Y, 𝒪_Y) = χ(X, 𝒪_X) + ∑ᶠ x, δ(x)`. -/
theorem eulerChar_eq_add_finsum_delta
    (hinj : ∀ V : X.Opens, IsAffineOpen V → Function.Injective (π.app V).hom)
    (hfin : ∀ V : X.Opens, IsAffineOpen V →
      IsFiniteCoker (sectionsRingHom c (le_top : V ≤ ⊤)) (π.app V).hom)
    (hX : ∀ i, FiniteDimensional k (cohomology (SheafOfModules.unit X.ringCatSheaf) c i)) :
    (∀ i, FiniteDimensional k
        (cohomology (SheafOfModules.unit Y.ringCatSheaf) (π.appTop.hom.comp c) i)) ∧
      (Function.support (deltaInvariant π c)).Finite ∧
      eulerChar Y (π.appTop.hom.comp c) = eulerChar X c + ((∑ᶠ x, deltaInvariant π c x : ℕ) : ℤ) := by
  classical
  let 𝒰 := FiniteAffineCover.choose X
  let _ : Fintype 𝒰.ι := Fintype.ofFinite _
  set α := cechStructureMap π c 𝒰.U
  have hinj' : ∀ T : Finset 𝒰.ι, T.Nonempty → Function.Injective (α.app T).hom :=
    fun T hT => hinj _ (𝒰.isAffineOpen_inf T hT)
  have hfin' : ∀ T : Finset 𝒰.ι, T.Nonempty → FiniteDimensional k
      ((cechDiagram ((Scheme.Modules.pushforward π).obj (SheafOfModules.unit Y.ringCatSheaf))
        𝒰.U c).obj T ⧸ LinearMap.range (α.app T).hom) := fun T hT => by
    obtain ⟨hiff, -⟩ := cechCoker_equiv π c (T.inf 𝒰.U)
    exact hiff.2 (hfin _ (𝒰.isAffineOpen_inf T hT))
  have h₁ : ∀ i, FiniteDimensional k
      ((subsetCechComplex.{u, u} (cechDiagram (SheafOfModules.unit X.ringCatSheaf) 𝒰.U c)).homology i) :=
    hX
  obtain ⟨h₂, hsum⟩ := sum_homology_cech_of_injective hinj' hfin'
  have e := fun i => cohomologyPushforwardIso π (SheafOfModules.unit Y.ringCatSheaf) c i
  have hY : ∀ i, FiniteDimensional k
      (cohomology (SheafOfModules.unit Y.ringCatSheaf) (π.appTop.hom.comp c) i) := fun i => by
    have : FiniteDimensional k (cohomology ((Scheme.Modules.pushforward π).obj
      (SheafOfModules.unit Y.ringCatSheaf)) c i) := h₂ i
    exact Module.Finite.equiv (e i).toLinearEquiv
  have hrank : ∀ i, finrank k (cohomology (SheafOfModules.unit Y.ringCatSheaf)
      (π.appTop.hom.comp c) i) = finrank k ((subsetCechComplex.{u, u} (cechDiagram
        ((Scheme.Modules.pushforward π).obj (SheafOfModules.unit Y.ringCatSheaf)) 𝒰.U c)).homology i) :=
    fun i => (e i).toLinearEquiv.finrank_eq.symm
  obtain ⟨hsupp, hδ⟩ := sum_cokerFinrank_eq_finsum_delta π c 𝒰
    (fun T hT => hfin _ (𝒰.isAffineOpen_inf T hT))
  refine ⟨hY, hsupp, ?_⟩
  have hχY : eulerChar Y (π.appTop.hom.comp c) = ∑ i ∈ Finset.range (Fintype.card 𝒰.ι),
      (-1 : ℤ) ^ i * finrank k ((subsetCechComplex.{u, u} (cechDiagram
        ((Scheme.Modules.pushforward π).obj (SheafOfModules.unit Y.ringCatSheaf)) 𝒰.U c)).homology i) := by
    rw [eulerChar, homologyEulerChar_eq_sum _ (Fintype.card 𝒰.ι)]
    · exact Finset.sum_congr rfl fun i _ => by rw [← hrank i]
    · intro i hi
      have : Subsingleton (cohomology ((Scheme.Modules.pushforward π).obj
          (SheafOfModules.unit Y.ringCatSheaf)) c i) :=
        subsingleton_subsetCechComplex_homology (cechDiagram
          ((Scheme.Modules.pushforward π).obj (SheafOfModules.unit Y.ringCatSheaf)) 𝒰.U c) i hi
      exact (e i).toLinearEquiv.symm.toEquiv.subsingleton
  have hχX : eulerChar X c = ∑ i ∈ Finset.range (Fintype.card 𝒰.ι), (-1 : ℤ) ^ i *
      finrank k ((subsetCechComplex.{u, u}
        (cechDiagram (SheafOfModules.unit X.ringCatSheaf) 𝒰.U c)).homology i) :=
    homologyEulerChar_eq_sum _ _ (subsingleton_subsetCechComplex_homology _)
  rw [hχY, hχX, hsum, ← hδ]
  refine congrArg _ (Finset.sum_congr rfl fun T _ => ?_)
  obtain ⟨-, hr⟩ := cechCoker_equiv π c (T.inf 𝒰.U)
  rw [← hr]
  rfl

/-- **The genus formula in δ-form** (Temkin, Lemma B.1): under the hypotheses of the δ-formula,
`p_a(X) = p_a(Y) + ∑ᶠ x, δ(x)`. -/
theorem arithmeticGenus_eq
    (hinj : ∀ V : X.Opens, IsAffineOpen V → Function.Injective (π.app V).hom)
    (hfin : ∀ V : X.Opens, IsAffineOpen V →
      IsFiniteCoker (sectionsRingHom c (le_top : V ≤ ⊤)) (π.app V).hom)
    (hX : ∀ i, FiniteDimensional k (cohomology (SheafOfModules.unit X.ringCatSheaf) c i)) :
    arithmeticGenus X c =
      arithmeticGenus Y (π.appTop.hom.comp c) + ((∑ᶠ x, deltaInvariant π c x : ℕ) : ℤ) := by
  rw [arithmeticGenus, arithmeticGenus, (eulerChar_eq_add_finsum_delta π c hinj hfin hX).2.2]
  ring

end Formula

end

end DeJongAlterations.StableModification.CurvesField.Genus
