/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.ClosureLocalAlgebra
import DeJongAlterations.StableModification.Curves.SemistableNormalHypersurface
import DeJongAlterations.StableModification.Curves.SemistableNormalSmooth

/-!
# The split node `L[u, v]/(uv)` and its étale neighbourhoods

For a ring `L`, the split node `N = L[u, v]/(uv)` (`Algebra.NodeBlowupChart.Node L 0`) has the
quotients `N/(u) ≅ L[v]`, `N/(v) ≅ L[u]` (`nodeQuotEquiv`) and, for an ideal `𝔞` of `L`,
`N/(u, 𝔞) ≅ (L/𝔞)[v]` (`isDomain_isIntegrallyClosed_quot_coordinate_sup`); the origin
`(u, v)` is a prime over `0 ⊂ L` (`isPrime_originIdeal`).

For an étale `N`-algebra `W` and a prime `𝔔` of `W`, the quotient of the local ring `W_𝔔` by an
ideal `I` of `N` is an integral domain if `N/I` is an integrally closed domain
(`isDomain_localization_quotient_of_etale`). From these facts,
`localStructure_of_nodeZero` proves `LocalStructure` for a local ring `A` with a faithfully flat
local `A`-algebra `A'` in which the two branches `u = 0` and `v = 0` of a split node are prime and
have reduced fibres, and meet in a point over the generic point (the case `c = 0` of the node
chart `O[u, v]/(uv - c)`; Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19
(2010), T:3164–3166).

Blueprint: `sm-blow-down-unconditional.tex`, `lem:sm-bdu-split-node`.
-/

noncomputable section

open IsLocalRing
open scoped TensorProduct

namespace DeJongAlterations.StableModification.BlowDown.ClosureLocal

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open DeJongAlterations.Algebra.NodeBlowupChart (Node coordinate)

section Line

variable (L : Type u) [CommRing L]

/-- `L[X₀, X₁]/(X₀) ≅ L[X]`, `X₁ ↦ X`. -/
def quotientXZeroEquiv :
    (MvPolynomial (Fin 2) L ⧸ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) L)}) ≃ₐ[L]
      Polynomial L :=
  AlgEquiv.ofAlgHom
    (Ideal.Quotient.liftₐ _ (MvPolynomial.aeval ![0, Polynomial.X]) fun a ha => by
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      simp)
    (Polynomial.aeval (Ideal.Quotient.mk _ (MvPolynomial.X 1)))
    (by
      apply Polynomial.algHom_ext
      rw [AlgHom.comp_apply, Polynomial.aeval_X, AlgHom.id_apply]
      change MvPolynomial.aeval ![0, Polynomial.X] (MvPolynomial.X (1 : Fin 2)) = _
      rw [MvPolynomial.aeval_X]
      rfl)
    (by
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro i
      fin_cases i
      · change Polynomial.aeval (Ideal.Quotient.mk _ (MvPolynomial.X 1))
          (MvPolynomial.aeval ![0, Polynomial.X] (MvPolynomial.X (0 : Fin 2))) =
          Ideal.Quotient.mk _ (MvPolynomial.X 0)
        rw [MvPolynomial.aeval_X]
        change Polynomial.aeval _ (0 : Polynomial L) = _
        rw [map_zero]
        exact (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)).symm
      · change Polynomial.aeval (Ideal.Quotient.mk _ (MvPolynomial.X 1))
          (MvPolynomial.aeval ![0, Polynomial.X] (MvPolynomial.X (1 : Fin 2))) =
          Ideal.Quotient.mk _ (MvPolynomial.X 1)
        rw [MvPolynomial.aeval_X]
        exact Polynomial.aeval_X _)

/-- `L[X₀, X₁]/(Xᵢ) ≅ L[X]`. -/
def quotientXEquiv (i : Fin 2) :
    (MvPolynomial (Fin 2) L ⧸ Ideal.span {(MvPolynomial.X i : MvPolynomial (Fin 2) L)}) ≃ₐ[L]
      Polynomial L :=
  match i with
  | 0 => quotientXZeroEquiv L
  | 1 => Curves.SemistableNormal.quotientXOneEquiv L

end Line

section NodeQuotients

variable {L : Type u} [CommRing L] (c : L)

/-- The coordinate ideal `(uᵢ)` of the node is the image of `(Xᵢ)`. -/
theorem span_coordinate_eq (i : Fin 2) :
    Ideal.span {coordinate c i} = (Ideal.span {(MvPolynomial.X i : MvPolynomial (Fin 2) L)}).map
      (Ideal.Quotient.mkₐ L (Algebra.NodeChart.uChartIdeal L c)) := by
  rw [Ideal.map_span, Set.image_singleton]
  rfl

/-- For `c = 0`, the equation `X₀X₁ - c` lies in `(Xᵢ)`. -/
theorem uChartIdeal_le_span_X (hc : c = 0) (i : Fin 2) :
    Algebra.NodeChart.uChartIdeal L c ≤ Ideal.span {(MvPolynomial.X i : MvPolynomial (Fin 2) L)} := by
  rw [Algebra.NodeChart.uChartIdeal, Ideal.span_le, Set.singleton_subset_iff, hc, map_zero,
    sub_zero]
  fin_cases i
  · exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

/-- **The branches of the split node**: `N/(uᵢ) ≅ L[X]`. -/
def nodeQuotEquiv (hc : c = 0) (i : Fin 2) :
    (Node L c ⧸ Ideal.span {coordinate c i}) ≃ₐ[L] Polynomial L :=
  (Ideal.quotientEquivAlgOfEq L (span_coordinate_eq c i)).trans
    ((DoubleQuot.quotQuotEquivQuotSupₐ L _ _).trans
      ((Ideal.quotientEquivAlgOfEq L (sup_eq_right.mpr (uChartIdeal_le_span_X c hc i))).trans
        (quotientXEquiv L i)))

/-- The branches of the split node over an integrally closed domain are integrally closed
domains. -/
theorem isDomain_isIntegrallyClosed_quot_coordinate [IsDomain L] [IsIntegrallyClosed L]
    (hc : c = 0) (i : Fin 2) :
    IsDomain (Node L c ⧸ Ideal.span {coordinate c i}) ∧
      IsIntegrallyClosed (Node L c ⧸ Ideal.span {coordinate c i}) := by
  let e := (nodeQuotEquiv c hc i).toRingEquiv
  exact ⟨e.injective.isDomain e.toRingHom, IsIntegrallyClosed.of_equiv e.symm⟩

/-- **The fibres of the branches of the split node**: for a maximal ideal `𝔞` of `L`,
`N/(uᵢ, 𝔞) ≅ (L/𝔞)[X]` is an integrally closed domain. -/
theorem isDomain_isIntegrallyClosed_quot_coordinate_sup (hc : c = 0) (i : Fin 2) (𝔞 : Ideal L)
    [𝔞.IsMaximal] :
    IsDomain (Node L c ⧸ (Ideal.span {coordinate c i} ⊔ 𝔞.map (algebraMap L (Node L c)))) ∧
      IsIntegrallyClosed
        (Node L c ⧸ (Ideal.span {coordinate c i} ⊔ 𝔞.map (algebraMap L (Node L c)))) := by
  let e := nodeQuotEquiv c hc i
  let mk := Ideal.Quotient.mk (Ideal.span {coordinate c i})
  have hJe : 𝔞.map Polynomial.C =
      ((𝔞.map (algebraMap L (Node L c))).map mk).map (e.toRingEquiv : _ →+* Polynomial L) := by
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
    refine RingHom.ext fun a => ?_
    change Polynomial.C a = e (Ideal.Quotient.mkₐ L _ (algebraMap L (Node L c) a))
    rw [AlgHom.commutes, AlgEquiv.commutes]
    rfl
  let := Ideal.Quotient.field 𝔞
  let f₁ := (DoubleQuot.quotQuotEquivQuotSup (Ideal.span {coordinate c i})
      (𝔞.map (algebraMap L (Node L c)))).symm
  let f₂ := Ideal.quotientEquiv _ _ e.toRingEquiv hJe
  let f₃ : Polynomial L ⧸ 𝔞.map Polynomial.C ≃+* Polynomial (L ⧸ 𝔞) :=
    (Ideal.polynomialQuotientEquivQuotientPolynomial 𝔞).symm
  let g := (f₁.trans f₂).trans f₃
  exact ⟨g.injective.isDomain g.toRingHom, IsIntegrallyClosed.of_equiv g.symm⟩

/-- The origin `(u, v)` of the split node. -/
def originIdeal : Ideal (Node L c) := Ideal.span {coordinate c 0, coordinate c 1}

/-- **The origin of the split node over a domain is a prime over `0`.** -/
theorem isPrime_originIdeal [IsDomain L] (hc : c = 0) :
    (originIdeal c).IsPrime ∧ (originIdeal c).comap (algebraMap L (Node L c)) = ⊥ := by
  let mkU := Ideal.Quotient.mk (Algebra.NodeChart.uChartIdeal L c)
  have hO : originIdeal c = (Curves.SemistableNormal.originIdeal L).map mkU := by
    rw [originIdeal, Curves.SemistableNormal.originIdeal, Ideal.map_span, Set.image_pair]
    rfl
  have hle : Algebra.NodeChart.uChartIdeal L c ≤ Curves.SemistableNormal.originIdeal L :=
    (uChartIdeal_le_span_X c hc 0).trans (Ideal.span_mono (by simp))
  have hbij := Curves.SemistableNormal.algebraMap_originQuotient_bijective L
  let e₂ : L ≃+* MvPolynomial (Fin 2) L ⧸ Curves.SemistableNormal.originIdeal L :=
    RingEquiv.ofBijective _ hbij
  let e₁ : Node L c ⧸ originIdeal c ≃+* L :=
    ((Ideal.quotEquivOfEq hO).trans ((DoubleQuot.quotQuotEquivQuotSup _ _).trans
      (Ideal.quotEquivOfEq (sup_eq_right.mpr hle)))).trans e₂.symm
  have hdom : IsDomain (Node L c ⧸ originIdeal c) := e₁.injective.isDomain e₁.toRingHom
  refine ⟨(Ideal.Quotient.isDomain_iff_prime _).mp hdom, ?_⟩
  have he₁ : ∀ a : L, e₁ (Ideal.Quotient.mk _ (algebraMap L (Node L c) a)) = a := by
    intro a
    apply e₂.injective
    simp only [e₁, RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
    rfl
  ext a
  rw [Ideal.mem_comap, Ideal.mem_bot, ← Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro ha
    have := congrArg e₁ ha
    rwa [he₁, map_zero] at this
  · rintro rfl
    rw [map_zero, map_zero]

end NodeQuotients

section EtaleQuotient

variable {N W : Type u} [CommRing N] [CommRing W] [Algebra N W] [Algebra.Etale N W]

/-- **Quotients of local rings of an étale algebra**: for an ideal `I` of `N` with `N/I` an
integrally closed domain and a prime `𝔔 ⊇ IW` of `W`, `W_𝔔 / I W_𝔔` is a domain (it is the local
ring of the étale `N/I`-algebra `W/IW` at `𝔔`). -/
theorem isDomain_localization_quotient_of_etale (I : Ideal N) [IsDomain (N ⧸ I)]
    [IsIntegrallyClosed (N ⧸ I)] (𝔔 : Ideal W) [𝔔.IsPrime]
    (hI : I.map (algebraMap N W) ≤ 𝔔) :
    IsDomain (Localization.AtPrime 𝔔 ⧸ I.map (algebraMap N (Localization.AtPrime 𝔔))) := by
  set J := I.map (algebraMap N W)
  set S := W ⧸ J
  have : Algebra.FormallyEtale (N ⧸ I) S := Curves.SemistableNormal.formallyEtale_quotient_map N W I
  have : Algebra.FinitePresentation (N ⧸ I) S := by
    have : Algebra.FinitePresentation (N ⧸ I) ((N ⧸ I) ⊗[N] W) := inferInstance
    exact Algebra.FinitePresentation.equiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor W I).symm
  have : Algebra.Etale (N ⧸ I) S := ⟨inferInstance, inferInstance⟩
  have hJ : RingHom.ker (Ideal.Quotient.mk J) ≤ 𝔔 := by
    rw [Ideal.mk_ker]
    exact hI
  set 𝔔' : Ideal S := 𝔔.map (Ideal.Quotient.mk J)
  have : 𝔔'.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hJ
  obtain ⟨hdom, -⟩ := Curves.isDomain_isIntegrallyClosed_localization_of_etale
    (N ⧸ I) 𝔔'
  -- `W_𝔔 / J W_𝔔` is the localization of `S` at `𝔔'`
  set A' := Localization.AtPrime 𝔔
  have hmap : J.map (algebraMap W A') = I.map (algebraMap N A') := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid S 𝔔.primeCompl)
      (A' ⧸ J.map (algebraMap W A')) := inferInstance
  have hsub : Algebra.algebraMapSubmonoid S 𝔔.primeCompl = 𝔔'.primeCompl := by
    ext x
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [Algebra.algebraMapSubmonoid, Submonoid.mem_map, Ideal.mem_primeCompl_iff]
    constructor
    · rintro ⟨w', hw', hww'⟩ hmem
      apply hw'
      have h1 : Ideal.Quotient.mk J w' ∈ 𝔔' := by
        change algebraMap W S w' ∈ 𝔔'
        rw [hww']
        exact hmem
      rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at h1
      obtain ⟨w'', hw'', hw''e⟩ := h1
      rw [Ideal.Quotient.eq] at hw''e
      have := 𝔔.sub_mem hw'' (hI hw''e)
      simpa using this
    · intro hw
      refine ⟨w, fun hmem => hw (Ideal.mem_map_of_mem _ hmem), rfl⟩
  rw [hsub] at hloc
  let e : Localization.AtPrime 𝔔' ≃ₐ[S] A' ⧸ J.map (algebraMap W A') :=
    IsLocalization.algEquiv 𝔔'.primeCompl _ _
  have : IsDomain (A' ⧸ J.map (algebraMap W A')) :=
    e.symm.injective.isDomain e.symm.toRingEquiv.toRingHom
  rw [hmap] at this
  exact this

end EtaleQuotient

section SplitNode

variable {R A A' : Type*} [CommRing R] [CommRing A] [CommRing A'] [Algebra R A] [Algebra A A']
  [Algebra R A'] [IsScalarTower R A A']

/-- **Torsion-freeness over a prime**: over a flat `A`-algebra `A'`, if `y ∉ P` for a prime `P` and
`y x = 0`, then `x ∈ P A'` (equational criterion for flatness). -/
theorem mem_map_of_mul_eq_zero [Module.Flat A A'] {P : Ideal A} [P.IsPrime] {y : A} (hy : y ∉ P)
    {x : A'} (h : algebraMap A A' y * x = 0) : x ∈ P.map (algebraMap A A') := by
  have h' : ∑ _i : Unit, y • x = 0 := by simpa [Algebra.smul_def] using h
  obtain ⟨k, a, z, hx, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
    (f := fun _ : Unit => y) (x := fun _ => x) h'
  have hx0 : x = ∑ j, a () j • z j := hx ()
  rw [hx0]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [Algebra.smul_def]
  refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
  have hj := ha j
  simp only [Finset.univ_unique, Finset.sum_singleton] at hj
  exact (‹P.IsPrime›.mem_or_mem (hj ▸ P.zero_mem)).resolve_left hy

/-- In a ring whose only minimal prime is `P`, the elements of `P` are nilpotent. -/
theorem isNilpotent_of_forall_minimalPrimes_eq {P : Ideal A} (hP : P ∈ minimalPrimes A)
    (hall : ∀ P' ∈ minimalPrimes A, P' = P) {x : A} (hx : x ∈ P) : IsNilpotent x := by
  have hset : (⊥ : Ideal A).minimalPrimes = {P} :=
    Set.eq_singleton_iff_unique_mem.mpr ⟨hP, hall⟩
  have h := Ideal.sInf_minimalPrimes (I := (⊥ : Ideal A))
  rw [hset, sInf_singleton] at h
  have : x ∈ (⊥ : Ideal A).radical := h ▸ hx
  obtain ⟨n, hn⟩ := this
  exact ⟨n, hn⟩

variable [Module.FaithfullyFlat A A'] (𝔭 : Ideal R) {u v : A'}

/-- One branch: if the minimal primes `P₁ = (u) ∩ A` and `P₂ = (v) ∩ A` of `A` are distinct
(`(u)`, `(v)` primes of `A'` with `uv = 0`), then `P₁ A' = (u)`, so the fibre of `A / P₁` embeds
in that of `A' / (u)`. -/
theorem isReduced_quotient_sup_of_branch (huv : u * v = 0) (hu : (Ideal.span {u}).IsPrime)
    (hP₁ : (Ideal.span {u}).comap (algebraMap A A') ∈ minimalPrimes A)
    (hne : (Ideal.span {v}).comap (algebraMap A A') ≠ (Ideal.span {u}).comap (algebraMap A A'))
    (hP₂ : (Ideal.span {v}).comap (algebraMap A A') ∈ minimalPrimes A)
    (hred : IsReduced (A' ⧸ (Ideal.span {u} ⊔ 𝔭.map (algebraMap R A')))) :
    IsReduced (A ⧸ ((Ideal.span {u}).comap (algebraMap A A') ⊔ 𝔭.map (algebraMap R A))) := by
  set P₁ := (Ideal.span {u}).comap (algebraMap A A')
  set P₂ := (Ideal.span {v}).comap (algebraMap A A')
  have : P₁.IsPrime := Ideal.comap_isPrime _ _
  -- an element of `P₂ ∖ P₁`
  obtain ⟨y, hyP₂, hyP₁⟩ : ∃ y ∈ P₂, y ∉ P₁ := by
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm hcon (hP₁.2 hP₂.1 hcon))
  -- `P₁ A' = (u)`
  have hmap : P₁.map (algebraMap A A') = Ideal.span {u} := by
    refine le_antisymm Ideal.map_comap_le fun x hx => ?_
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (show algebraMap A A' y ∈ Ideal.span {v} from hyP₂)
    refine mem_map_of_mul_eq_zero hyP₁ ?_
    rw [← hb]
    linear_combination (a * b) * huv
  have hmap' : (P₁ ⊔ 𝔭.map (algebraMap R A)).map (algebraMap A A') =
      Ideal.span {u} ⊔ 𝔭.map (algebraMap R A') := by
    rw [Ideal.map_sup, hmap, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hle : P₁ ⊔ 𝔭.map (algebraMap R A) ≤
      (Ideal.span {u} ⊔ 𝔭.map (algebraMap R A')).comap (algebraMap A A') := by
    rw [← hmap']
    exact Ideal.le_comap_map
  have hinj : Function.Injective (Ideal.quotientMap _ (algebraMap A A') hle) := by
    refine Ideal.quotientMap_injective' ?_
    rw [← hmap', Ideal.comap_map_eq_self_of_faithfullyFlat]
  exact isReduced_of_injective _ hinj

/-- **The local structure from a split node** (blueprint `lem:sm-bdu-split-node`): let `A'` be a
faithfully flat `A`-algebra containing `u, v` with `uv = 0`, `(u)`, `(v)` prime with reduced fibres
over `𝔭`, and a prime `𝔫 ∋ u, v` over the generic point of `R`. Then `A` has `LocalStructure`. -/
theorem localStructure_of_split (huv : u * v = 0) (hu : (Ideal.span {u}).IsPrime)
    (hv : (Ideal.span {v}).IsPrime)
    (hredu : IsReduced (A' ⧸ (Ideal.span {u} ⊔ 𝔭.map (algebraMap R A'))))
    (hredv : IsReduced (A' ⧸ (Ideal.span {v} ⊔ 𝔭.map (algebraMap R A'))))
    (𝔫 : Ideal A') [𝔫.IsPrime] (hu𝔫 : u ∈ 𝔫) (hv𝔫 : v ∈ 𝔫)
    (h𝔫 : 𝔫.comap (algebraMap R A') = ⊥) : LocalStructure R A 𝔭 := by
  set Pu := (Ideal.span {u}).comap (algebraMap A A')
  set Pv := (Ideal.span {v}).comap (algebraMap A A')
  have hinjA : Function.Injective (algebraMap A A') := FaithfulSMul.algebraMap_injective A A'
  -- the minimal primes of `A` are `Pu` and `Pv`
  have hcases : ∀ P ∈ minimalPrimes A, P = Pu ∨ P = Pv := by
    intro P hP
    obtain ⟨Q, hQ, rfl⟩ := exists_mem_minimalPrimes_comap_eq (A' := A') hP
    have : Q.IsPrime := hQ.1.1
    rcases ‹Q.IsPrime›.mem_or_mem (show u * v ∈ Q from huv ▸ Q.zero_mem) with h | h
    · left
      have hle : Ideal.span {u} ≤ Q := (Ideal.span_singleton_le_iff_mem _).mpr h
      rw [le_antisymm (hQ.2 ⟨hu, bot_le⟩ hle) hle]
    · right
      have hle : Ideal.span {v} ≤ Q := (Ideal.span_singleton_le_iff_mem _).mpr h
      rw [le_antisymm (hQ.2 ⟨hv, bot_le⟩ hle) hle]
  -- products of elements of `Pu` and `Pv` vanish
  have hprod : ∀ x ∈ Pu, ∀ y ∈ Pv, x * y = 0 := by
    intro x hx y hy
    apply hinjA
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (show algebraMap A A' x ∈ Ideal.span {u} from hx)
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (show algebraMap A A' y ∈ Ideal.span {v} from hy)
    rw [map_mul, map_zero, ← ha, ← hb]
    linear_combination (a * b) * huv
  have hPun : Pu ≤ 𝔫.comap (algebraMap A A') :=
    Ideal.comap_mono ((Ideal.span_singleton_le_iff_mem _).mpr hu𝔫)
  have hPvn : Pv ≤ 𝔫.comap (algebraMap A A') :=
    Ideal.comap_mono ((Ideal.span_singleton_le_iff_mem _).mpr hv𝔫)
  -- two distinct minimal primes are `Pu` and `Pv`
  have htwo : ∀ P ∈ minimalPrimes A, ∀ P₂ ∈ minimalPrimes A, P₂ ≠ P →
      (P = Pu ∧ P₂ = Pv) ∨ (P = Pv ∧ P₂ = Pu) := by
    intro P hP P₂ hP₂ hne
    rcases hcases P hP with rfl | rfl <;> rcases hcases P₂ hP₂ with rfl | rfl
    · exact absurd rfl hne
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact absurd rfl hne
  refine ⟨fun P hP hred0 => ?_, fun P hP w hw h𝔭w hPw => ?_⟩
  · by_cases hall : ∀ P' ∈ minimalPrimes A, P' = P
    · -- `P` is the nilradical, hence contained in `𝔭A`
      have hle : P ≤ 𝔭.map (algebraMap R A) := by
        intro x hx
        have hnil := isNilpotent_of_forall_minimalPrimes_eq hP hall hx
        have h0 : Ideal.Quotient.mk (𝔭.map (algebraMap R A)) x = 0 :=
          (hnil.map (Ideal.Quotient.mk _)).eq_zero
        exact Ideal.Quotient.eq_zero_iff_mem.mp h0
      rw [sup_eq_right.mpr hle]
      exact hred0
    · push Not at hall
      obtain ⟨P₂, hP₂, hne⟩ := hall
      rcases htwo P hP P₂ hP₂ hne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact isReduced_quotient_sup_of_branch 𝔭 huv hu hP hne hP₂ hredu
      · exact isReduced_quotient_sup_of_branch 𝔭 (by rw [mul_comm]; exact huv) hv hP hne hP₂
          hredv
  · -- a second minimal prime exists, else `P` would be the nilradical
    have hall : ¬ ∀ P' ∈ minimalPrimes A, P' = P := by
      intro hall
      apply hPw
      intro x hx
      obtain ⟨m, hm⟩ := isNilpotent_of_forall_minimalPrimes_eq hP hall hx
      exact hw.mem_of_pow_mem m (hm ▸ w.zero_mem)
    push Not at hall
    obtain ⟨P₂, hP₂, hne⟩ := hall
    set n := 𝔫.comap (algebraMap A A')
    have : n.IsPrime := Ideal.comap_isPrime _ _
    have hPn : P ≤ n := by rcases hcases P hP with rfl | rfl <;> assumption
    have hP₂n : P₂ ≤ n := by rcases hcases P₂ hP₂ with rfl | rfl <;> assumption
    refine ⟨n, inferInstance, hPn, ?_, ?_, P₂, hP₂, hne, hP₂n⟩
    · rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, h𝔫]
    -- `A_n` is not a domain: `x ∈ P ∖ P₂`, `y ∈ P₂ ∖ P` have `xy = 0`
    have hP' : P.IsPrime := hP.1.1
    have hP₂' : P₂.IsPrime := hP₂.1.1
    obtain ⟨x, hxP, hxP₂⟩ : ∃ x ∈ P, x ∉ P₂ := by
      by_contra hcon
      push Not at hcon
      exact hne.symm (le_antisymm hcon (hP₂.2 hP.1 hcon))
    obtain ⟨y, hyP₂, hyP⟩ : ∃ y ∈ P₂, y ∉ P := by
      by_contra hcon
      push Not at hcon
      exact hne (le_antisymm hcon (hP.2 hP₂.1 hcon))
    have hxy : x * y = 0 := by
      rcases htwo P hP P₂ hP₂ hne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hprod x hxP y hyP₂
      · rw [mul_comm]
        exact hprod y hyP₂ x hxP
    intro hdom
    have := hdom
    have hx0 : algebraMap A (Localization.AtPrime n) x ≠ 0 := by
      intro h0
      obtain ⟨⟨s, hs⟩, hsx⟩ := (IsLocalization.map_eq_zero_iff n.primeCompl _ x).mp h0
      have : s * x ∈ P₂ := hsx ▸ P₂.zero_mem
      exact hs (hP₂n ((hP₂'.mem_or_mem this).resolve_right hxP₂))
    have hy0 : algebraMap A (Localization.AtPrime n) y ≠ 0 := by
      intro h0
      obtain ⟨⟨s, hs⟩, hsy⟩ := (IsLocalization.map_eq_zero_iff n.primeCompl _ y).mp h0
      have : s * y ∈ P := hsy ▸ P.zero_mem
      exact hs (hPn ((hP'.mem_or_mem this).resolve_right hyP))
    exact (mul_ne_zero hx0 hy0) (by rw [← map_mul, hxy, map_zero])

end SplitNode

end DeJongAlterations.StableModification.BlowDown.ClosureLocal
