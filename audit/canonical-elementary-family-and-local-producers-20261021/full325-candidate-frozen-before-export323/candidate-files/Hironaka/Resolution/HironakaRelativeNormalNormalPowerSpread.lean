/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.HolGermSubExact
import Hironaka.Resolution.HironakaRelativeNormalTranslatedTaylorFunctions

/-!
Actual finite-order recursive normal-power expressions on one genuine nearby open.
Mathematics.tex complete proofs were written first. Formal/native registration pending root.
No fixed-order open is asserted common to all orders. Whole original normalflat/G8 OPEN.
-/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff Nat
namespace Hironaka.HironakaRelativeNormalNormalPowerSpread
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
  HolomorphicTaylorTail HironakaRelativeNormalIdeal HironakaRelativeNormalTaylorCoefficients
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalTranslatedTaylorFunctions
  NormalTaylorOrder HironakaRelativeNormalMonomialBasis HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetMonomialSpan HironakaRelativeNormalDeformationInitialRelations

theorem exists_actual_recursive_normal_power_open {n k : ℕ} (q : ℕ)
    {f : ComplexModel n → ℂ} (hp : InNormalPow k (0 : ComplexModel n) q f) :
    ∃ U : Set (ComplexModel n), IsOpen U ∧ 0 ∈ U ∧
      ∀ a ∈ U, InNormalPow k a q f := by
  induction q generalizing f with
  | zero =>
    obtain ⟨U,hUf,hU,h0⟩ := eventually_nhds_iff.mp hp
    refine ⟨U,hU,h0,?_⟩
    intro a ha
    filter_upwards [hU.mem_nhds ha] with z hz
    exact hUf z hz
  | succ q ih =>
    obtain ⟨H,hH0,hH,he⟩ := hp
    have hfamily : ∀ i : Fin n, ∃ U : Set (ComplexModel n), IsOpen U ∧ 0 ∈ U ∧
        ∀ a ∈ U, InNormalPow k a q (H i) := fun i => ih (hH i)
    choose U hU h0 hmem using hfamily
    have hd : ∀ᶠ a in 𝓝 (0 : ComplexModel n), ∀ i : Fin n, InNormalPow k a q (H i) := by
      apply eventually_all.mpr
      intro i
      filter_upwards [(hU i).mem_nhds (h0 i)] with a ha
      exact hmem i a ha
    have hwhole : ∀ᶠ a in 𝓝 (0 : ComplexModel n), InNormalPow k a (q+1) f := by
      filter_upwards [hd,he.eventually_nhds] with a ha hfa
      exact ⟨H,hH0,ha,hfa⟩
    obtain ⟨W,hWf,hW,h0W⟩ := eventually_nhds_iff.mp hwhole
    exact ⟨W,hW,h0W,hWf⟩

theorem actualAffineTranslation_tendsto_zero {n : ℕ} (a : ComplexModel n) :
    Tendsto (actualAffineTranslation n a) (𝓝 0) (𝓝 a) := by
  simpa only [actualAffineTranslation_zero] using
    (actualAffineTranslation_contMDiff n a).continuous.tendsto (0 : ComplexModel n)

theorem InNormalPow_actualAffineTranslation {n k : ℕ} {a : ComplexModel n}
    (ha : a ∈ complexCoordinatePlane n k) (q : ℕ)
    {f : ComplexModel n → ℂ} (hp : InNormalPow k a q f) :
    InNormalPow k (0 : ComplexModel n) q (f ∘ actualAffineTranslation n a) := by
  induction q generalizing f with
  | zero =>
    filter_upwards [(actualAffineTranslation_tendsto_zero a).eventually hp] with z hz
    exact hz.comp z ((differentiableAt_const a).add differentiableAt_id)
  | succ q ih =>
    obtain ⟨H,hH0,hH,he⟩ := hp
    refine ⟨fun i => H i ∘ actualAffineTranslation n a,?_,fun i => ih (hH i),?_⟩
    · intro i hi
      funext z
      simp only [hH0 i hi,Function.comp_apply,Pi.zero_apply]
    · filter_upwards [(actualAffineTranslation_tendsto_zero a).eventually he] with z hz
      change f (actualAffineTranslation n a z) = _
      rw [hz]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i.val < k
      · simp only [hH0 i hi,Function.comp_apply,Pi.zero_apply,mul_zero]
      · have hzero : a i = 0 := ha i (by omega)
        change (a+z) i * H i (a+z) = z i * H i (a+z)
        have heval : (a+z) i = a i+z i := rfl
        rw [heval,hzero,zero_add]

theorem actualAffineTranslation_holAt {n : ℕ} {a : ComplexModel n}
    {f : ComplexModel n → ℂ} (hf : HolAt f a) :
    HolAt (f ∘ actualAffineTranslation n a) 0 := by
  filter_upwards [(actualAffineTranslation_tendsto_zero a).eventually hf] with z hz
  exact hz.comp z ((differentiableAt_const a).add differentiableAt_id)

theorem exists_actual_nearby_normal_power (d t q : ℕ)
    {f : ComplexModel (d+t) → ℂ} (hf : HolAt f 0)
    (hp : HolGerm.mk f hf ∈ normalIdeal d t ^ q) :
    ∃ U : Set (ComplexModel (d+t)), IsOpen U ∧ 0 ∈ U ∧
      ∃ hhol : ∀ a ∈ U, HolAt (f ∘ actualAffineTranslation (d+t) a) 0,
        ∀ a (ha : a ∈ U), a ∈ complexCoordinatePlane (d+t) d →
          HolGerm.mk (f ∘ actualAffineTranslation (d+t) a) (hhol a ha) ∈ normalIdeal d t ^ q := by
  have hexpr := (mem_normalIdeal_pow_iff_InNormalPow d t q hf).mp hp
  obtain ⟨U,hU,h0,hmem⟩ := exists_actual_recursive_normal_power_open q hexpr
  have hhol : ∀ a ∈ U, HolAt (f ∘ actualAffineTranslation (d+t) a) 0 :=
    fun a ha => actualAffineTranslation_holAt (hmem a ha).eventually_differentiableAt
  refine ⟨U,hU,h0,hhol,?_⟩
  intro a ha hc
  exact mem_normalIdeal_pow_of_InNormalPow d t q (hhol a ha)
    (InNormalPow_actualAffineTranslation hc q (hmem a ha))

theorem exists_actual_nearby_whole_quotient_identity (d t q : ℕ)
    {f g : ComplexModel (d+t) → ℂ} (hf : HolAt f 0) (hg : HolAt g 0)
    (he : Ideal.Quotient.mk (normalIdeal d t ^ q) (HolGerm.mk f hf) =
      Ideal.Quotient.mk (normalIdeal d t ^ q) (HolGerm.mk g hg)) :
    ∃ U : Set (ComplexModel (d+t)), IsOpen U ∧ 0 ∈ U ∧
      ∃ hF : ∀ a ∈ U, HolAt (f ∘ actualAffineTranslation (d+t) a) 0,
      ∃ hG : ∀ a ∈ U, HolAt (g ∘ actualAffineTranslation (d+t) a) 0,
        ∀ a (ha : a ∈ U), a ∈ complexCoordinatePlane (d+t) d →
          Ideal.Quotient.mk (normalIdeal d t ^ q) (HolGerm.mk (f ∘ actualAffineTranslation (d+t) a) (hF a ha)) =
            Ideal.Quotient.mk (normalIdeal d t ^ q) (HolGerm.mk (g ∘ actualAffineTranslation (d+t) a) (hG a ha)) := by
  have hfg := eventually_differentiableAt_sub hf hg
  have hp : HolGerm.mk (fun z => f z-g z) hfg ∈ normalIdeal d t ^ q := by
    rw [HolGerm.mk_sub f g hf hg]
    exact Ideal.Quotient.eq.mp he
  have hexpr := (mem_normalIdeal_pow_iff_InNormalPow d t q hfg).mp hp
  obtain ⟨V,hV,h0V,hpow⟩ := exists_actual_recursive_normal_power_open q hexpr
  obtain ⟨F,hF,h0F,hfmem⟩ := exists_actual_recursive_normal_power_open (k := d) 0 hf
  obtain ⟨G,hG,h0G,hgmem⟩ := exists_actual_recursive_normal_power_open (k := d) 0 hg
  let W := V ∩ F ∩ G
  have hFW : ∀ a ∈ W, HolAt (f ∘ actualAffineTranslation (d+t) a) 0 :=
    fun a ha => actualAffineTranslation_holAt (hfmem a ha.1.2)
  have hGW : ∀ a ∈ W, HolAt (g ∘ actualAffineTranslation (d+t) a) 0 :=
    fun a ha => actualAffineTranslation_holAt (hgmem a ha.2)
  refine ⟨W,(hV.inter hF).inter hG,⟨⟨h0V,h0F⟩,h0G⟩,hFW,hGW,?_⟩
  intro a ha hc
  have htranslated := InNormalPow_actualAffineTranslation hc q (hpow a ha.1.1)
  have hm := mem_normalIdeal_pow_of_InNormalPow d t q
    (eventually_differentiableAt_sub (hFW a ha) (hGW a ha)) htranslated
  rw [HolGerm.mk_sub _ _ (hFW a ha) (hGW a ha)] at hm
  exact Ideal.Quotient.eq.mpr hm

theorem exists_actual_nearby_finite_whole_quotient_identities (d t q : ℕ)
    {μ : Type} [Finite μ] (F G : μ → ComplexModel (d+t) → ℂ)
    (hF : ∀ i, HolAt (F i) 0) (hG : ∀ i, HolAt (G i) 0)
    (he : ∀ i, Ideal.Quotient.mk (normalIdeal d t ^ q) (HolGerm.mk (F i) (hF i)) =
      Ideal.Quotient.mk (normalIdeal d t ^ q) (HolGerm.mk (G i) (hG i))) :
    ∃ U : Set (ComplexModel (d+t)), IsOpen U ∧ 0 ∈ U ∧
      ∃ hFU : ∀ a ∈ U, ∀ i, HolAt (F i ∘ actualAffineTranslation (d+t) a) 0,
      ∃ hGU : ∀ a ∈ U, ∀ i, HolAt (G i ∘ actualAffineTranslation (d+t) a) 0,
        ∀ a (ha : a ∈ U), a ∈ complexCoordinatePlane (d+t) d → ∀ i,
          Ideal.Quotient.mk (normalIdeal d t ^ q) (HolGerm.mk (F i ∘ actualAffineTranslation (d+t) a) (hFU a ha i)) =
            Ideal.Quotient.mk (normalIdeal d t ^ q) (HolGerm.mk (G i ∘ actualAffineTranslation (d+t) a) (hGU a ha i)) := by
  classical
  have hfamily := fun i => exists_actual_nearby_whole_quotient_identity d t q (hF i) (hG i) (he i)
  choose U hU h0 hFU hGU heU using hfamily
  let W := ⋂ i, U i
  have hFW : ∀ a ∈ W, ∀ i, HolAt (F i ∘ actualAffineTranslation (d+t) a) 0 :=
    fun a ha i => hFU i a (Set.mem_iInter.mp ha i)
  have hGW : ∀ a ∈ W, ∀ i, HolAt (G i ∘ actualAffineTranslation (d+t) a) 0 :=
    fun a ha i => hGU i a (Set.mem_iInter.mp ha i)
  refine ⟨W,isOpen_iInter_of_finite hU,Set.mem_iInter.mpr h0,hFW,hGW,?_⟩
  exact fun a ha hc i => heU i a (Set.mem_iInter.mp ha i) hc

private theorem actual_finite_product_hol {n : ℕ} {μ : Type} (s : Finset μ)
    (F : μ → ComplexModel n → ℂ) (hF : ∀ i, HolAt (F i) 0) :
    HolAt (fun z => ∏ i ∈ s, F i z) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact Eventually.of_forall fun _ => differentiableAt_const (1 : ℂ)
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using eventually_differentiableAt_mul (hF i) ih

private theorem mk_actual_finite_product {n : ℕ} {μ : Type} (s : Finset μ)
    (F : μ → ComplexModel n → ℂ) (hF : ∀ i, HolAt (F i) 0) :
    HolGerm.mk (fun z => ∏ i ∈ s, F i z) (actual_finite_product_hol s F hF) =
      ∏ i ∈ s, HolGerm.mk (F i) (hF i) := by
  apply Subtype.ext
  rw [HolGerm.coe_mk, SubmonoidClass.coe_finsetProd]
  simp only [HolGerm.coe_mk]
  have he := map_prod (Germ.coeRingHom (𝓝 (0 : ComplexModel n)) :
    (ComplexModel n → ℂ) →+* Germ (𝓝 (0 : ComplexModel n)) ℂ) F s
  simp only [Germ.coe_coeRingHom] at he
  rw [← he, Finset.prod_fn]

def actualNormalMonomialFunction (d t : ℕ) (α : Fin t →₀ ℕ)
    (z : ComplexModel (d+t)) : ℂ := ∏ i, z (i.natAdd d) ^ α i

theorem actualNormalMonomialFunction_holAt (d t : ℕ) (α : Fin t →₀ ℕ) :
    HolAt (actualNormalMonomialFunction d t α) 0 :=
  actual_finite_product_hol Finset.univ _ (fun i =>
    eventually_differentiableAt_pow (Eventually.of_forall fun _ =>
      (EuclideanSpace.proj (i.natAdd d) : ComplexModel (d+t) →L[ℂ] ℂ).differentiableAt) (α i))

theorem mk_actualNormalMonomialFunction (d t : ℕ) (α : Fin t →₀ ℕ) :
    HolGerm.mk (actualNormalMonomialFunction d t α) (actualNormalMonomialFunction_holAt d t α) =
      normalExponentMonomial d t α := by
  let F : Fin t → ComplexModel (d+t) → ℂ := fun i z => z (i.natAdd d) ^ α i
  have hcoord : ∀ i : Fin t, HolAt (fun z : ComplexModel (d+t) => z (i.natAdd d)) 0 :=
    fun i => Eventually.of_forall fun _ =>
      (EuclideanSpace.proj (i.natAdd d) : ComplexModel (d+t) →L[ℂ] ℂ).differentiableAt
  have hF : ∀ i, HolAt (F i) 0 := fun i => eventually_differentiableAt_pow (hcoord i) (α i)
  calc
    _ = ∏ i, HolGerm.mk (F i) (hF i) := mk_actual_finite_product Finset.univ F hF
    _ = normalExponentMonomial d t α := by
      apply Finset.prod_congr rfl
      intro i _
      exact HolGerm.mk_pow _ (hcoord i) (α i)


def actualNormalPolynomialFunction (d t q : ℕ)
    (C : normalExponentIndex t q → ComplexModel d → ℂ) : ComplexModel (d+t) → ℂ :=
  letI := normalExponentFintype t q
  fun z => ∑ α, C α (tangentProjection d t z) * actualNormalMonomialFunction d t α.val z

theorem actualNormalPolynomialFunction_holAt (d t q : ℕ)
    (C : normalExponentIndex t q → ComplexModel d → ℂ) (hC : ∀ α, HolAt (C α) 0) :
    HolAt (actualNormalPolynomialFunction d t q C) 0 := by
  let := normalExponentFintype t q
  exact eventually_differentiableAt_sum Finset.univ (fun α =>
    eventually_differentiableAt_mul (eventually_differentiableAt_comp_clm (tangentProjection d t) (hC α))
      (actualNormalMonomialFunction_holAt d t α.val))

theorem mk_actualNormalPolynomialFunction (d t q : ℕ)
    (C : normalExponentIndex t q → ComplexModel d → ℂ) (hC : ∀ α, HolAt (C α) 0) :
    let := normalExponentFintype t q
    HolGerm.mk (actualNormalPolynomialFunction d t q C) (actualNormalPolynomialFunction_holAt d t q C hC) =
      ∑ α, tangentPullback d t (HolGerm.mk (C α) (hC α)) * normalExponentMonomial d t α.val := by
  let := normalExponentFintype t q
  dsimp only
  let F := fun α z => C α (tangentProjection d t z) * actualNormalMonomialFunction d t α.val z
  have hF : ∀ α, HolAt (F α) 0 := fun α => eventually_differentiableAt_mul
    (eventually_differentiableAt_comp_clm (tangentProjection d t) (hC α))
    (actualNormalMonomialFunction_holAt d t α.val)
  calc
    _ = ∑ α, HolGerm.mk (F α) (hF α) := HolGerm.mk_sum Finset.univ F hF
    _ = _ := by
      apply Finset.sum_congr rfl
      intro α _
      calc
        _ = HolGerm.mk (C α ∘ tangentProjection d t)
            (eventually_differentiableAt_comp_clm (tangentProjection d t) (hC α)) *
            HolGerm.mk (actualNormalMonomialFunction d t α.val) (actualNormalMonomialFunction_holAt d t α.val) :=
          HolGerm.mk_mul _ _ _ _
        _ = _ := by
          rw [mk_actualNormalMonomialFunction]
          have he : tangentPullback d t (HolGerm.mk (C α) (hC α)) =
              HolGerm.mk (C α ∘ tangentProjection d t)
                (eventually_differentiableAt_comp_clm (tangentProjection d t) (hC α)) :=
            compAlgHom_mk _ _ _ _ _
          rw [he]

theorem quotient_actualNormalPolynomialFunction (d t q : ℕ)
    (C : normalExponentIndex t q → ComplexModel d → ℂ) (hC : ∀ α, HolAt (C α) 0) :
    let := tangentAlgebra d t
    let := normalExponentFintype t q
    Ideal.Quotient.mk (normalIdeal d t ^ q)
      (HolGerm.mk (actualNormalPolynomialFunction d t q C) (actualNormalPolynomialFunction_holAt d t q C hC)) =
      ∑ α, HolGerm.mk (C α) (hC α) • normalMonomialBasis d t q α := by
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  dsimp only
  rw [mk_actualNormalPolynomialFunction d t q C hC,map_sum]
  apply Finset.sum_congr rfl
  intro α _
  rw [normalMonomialBasis_apply]
  have he : tangentPullback d t (HolGerm.mk (C α) (hC α)) * normalExponentMonomial d t α.val =
      HolGerm.mk (C α) (hC α) • normalExponentMonomial d t α.val := by
    rw [Algebra.smul_def]
    rfl
  rw [he]
  exact (Ideal.Quotient.mkₐ (HolGerm (ComplexModel d)) (normalIdeal d t ^ q)).toLinearMap.map_smul _ _

theorem exists_actual_whole_basis_coefficient_functions (d t q : ℕ)
    (f : ComplexModel (d+t) → ℂ) (hf : HolAt f 0) :
    let := tangentAlgebra d t
    let := normalExponentFintype t q
    ∃ C : normalExponentIndex t q → ComplexModel d → ℂ,
      ∃ hC : ∀ α, HolAt (C α) 0,
        (∀ α, (normalMonomialBasis d t q).repr (Ideal.Quotient.mk (normalIdeal d t ^ q) (HolGerm.mk f hf)) α =
          HolGerm.mk (C α) (hC α)) ∧
        Ideal.Quotient.mk (normalIdeal d t ^ q) (HolGerm.mk f hf) =
          Ideal.Quotient.mk (normalIdeal d t ^ q)
            (HolGerm.mk (actualNormalPolynomialFunction d t q C) (actualNormalPolynomialFunction_holAt d t q C hC)) := by
  classical
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  dsimp only
  let y := Ideal.Quotient.mk (normalIdeal d t ^ q) (HolGerm.mk f hf)
  choose C hC he using fun α => HolGerm.exists_eq_mk ((normalMonomialBasis d t q).repr y α)
  refine ⟨C,hC,he,?_⟩
  rw [quotient_actualNormalPolynomialFunction d t q C hC]
  conv_rhs => arg 2; ext α; rw [← he α]
  exact ((normalMonomialBasis d t q).sum_repr y).symm


theorem actualNormalMonomialFunction_actualAffineTranslation (d t : ℕ)
    (α : Fin t →₀ ℕ) {a : ComplexModel (d+t)} (ha : a ∈ complexCoordinatePlane (d+t) d)
    (z : ComplexModel (d+t)) :
    actualNormalMonomialFunction d t α (actualAffineTranslation (d+t) a z) =
      actualNormalMonomialFunction d t α z := by
  apply Finset.prod_congr rfl
  intro i _
  have h0 : a (i.natAdd d) = 0 := ha _ (by simp)
  change ((a+z) (i.natAdd d)) ^ α i = z (i.natAdd d) ^ α i
  have he : (a+z) (i.natAdd d) = a (i.natAdd d) + z (i.natAdd d) := rfl
  rw [he,h0,zero_add]

theorem actualNormalPolynomialFunction_actualAffineTranslation (d t q : ℕ)
    (C : normalExponentIndex t q → ComplexModel d → ℂ)
    {a : ComplexModel (d+t)} (ha : a ∈ complexCoordinatePlane (d+t) d) :
    actualNormalPolynomialFunction d t q C ∘ actualAffineTranslation (d+t) a =
      actualNormalPolynomialFunction d t q (fun α => C α ∘ actualAffineTranslation d (tangentProjection d t a)) := by
  let := normalExponentFintype t q
  funext z
  apply Finset.sum_congr rfl
  intro α _
  rw [actualNormalMonomialFunction_actualAffineTranslation d t α.val ha]
  have he : tangentProjection d t (actualAffineTranslation (d+t) a z) =
      actualAffineTranslation d (tangentProjection d t a) (tangentProjection d t z) := map_add _ _ _
  rw [he]
  rfl


theorem exists_actual_nearby_finite_basis_coefficient_functions (d t q : ℕ)
    {μ : Type} [Finite μ] (F : μ → ComplexModel (d+t) → ℂ) (hF : ∀ i, HolAt (F i) 0) :
    let := tangentAlgebra d t
    let := normalExponentFintype t q
    ∃ U : Set (ComplexModel (d+t)), IsOpen U ∧ 0 ∈ U ∧
      ∃ C : μ → normalExponentIndex t q → ComplexModel d → ℂ,
      ∃ hC : ∀ i α, HolAt (C i α) 0,
      ∃ hFU : ∀ a ∈ U, ∀ i, HolAt (F i ∘ actualAffineTranslation (d+t) a) 0,
      ∃ hCU : ∀ a ∈ U, ∀ i α,
        HolAt (C i α ∘ actualAffineTranslation d (tangentProjection d t a)) 0,
        (∀ i α, (normalMonomialBasis d t q).repr
          (Ideal.Quotient.mk (normalIdeal d t ^ q) (HolGerm.mk (F i) (hF i))) α =
            HolGerm.mk (C i α) (hC i α)) ∧
        ∀ a (ha : a ∈ U), a ∈ complexCoordinatePlane (d+t) d → ∀ i α,
          (normalMonomialBasis d t q).repr
            (Ideal.Quotient.mk (normalIdeal d t ^ q)
              (HolGerm.mk (F i ∘ actualAffineTranslation (d+t) a) (hFU a ha i))) α =
            HolGerm.mk (C i α ∘ actualAffineTranslation d (tangentProjection d t a)) (hCU a ha i α) := by
  classical
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  dsimp only
  choose C hC horigin hexpand using fun i => exists_actual_whole_basis_coefficient_functions d t q (F i) (hF i)
  obtain ⟨V,hV,h0V,hFV,hPV,heV⟩ := exists_actual_nearby_finite_whole_quotient_identities d t q
    F (fun i => actualNormalPolynomialFunction d t q (C i)) hF
    (fun i => actualNormalPolynomialFunction_holAt d t q (C i) (hC i)) hexpand
  have hbase : ∀ k : μ × normalExponentIndex t q,
      ∃ E : Set (ComplexModel d), IsOpen E ∧ 0 ∈ E ∧ ∀ u ∈ E, HolAt (C k.1 k.2) u :=
    fun k => exists_actual_recursive_normal_power_open (k := d) 0 (hC k.1 k.2)
  choose E hE h0E hCE using hbase
  let W := V ∩ ⋂ k : μ × normalExponentIndex t q, tangentProjection d t ⁻¹' E k
  have hCW : ∀ a ∈ W, ∀ i α, HolAt (C i α ∘ actualAffineTranslation d (tangentProjection d t a)) 0 :=
    fun a ha i α => actualAffineTranslation_holAt (hCE (i,α) _ (Set.mem_iInter.mp ha.2 (i,α)))
  have hFW : ∀ a ∈ W, ∀ i, HolAt (F i ∘ actualAffineTranslation (d+t) a) 0 := fun a ha i => hFV a ha.1 i
  refine ⟨W,hV.inter (isOpen_iInter_of_finite (fun k => (hE k).preimage (tangentProjection d t).continuous)),
    ⟨h0V,Set.mem_iInter.mpr (fun k => by simpa only [Set.mem_preimage,map_zero] using h0E k)⟩,
    C,hC,hFW,hCW,horigin,?_⟩
  intro a ha hc i α
  have hmk : HolGerm.mk (actualNormalPolynomialFunction d t q (C i) ∘ actualAffineTranslation (d+t) a) (hPV a ha.1 i) =
      HolGerm.mk (actualNormalPolynomialFunction d t q
        (fun β => C i β ∘ actualAffineTranslation d (tangentProjection d t a)))
        (actualNormalPolynomialFunction_holAt d t q _ (hCW a ha i)) := by
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Filter.EventuallyEq.of_eq (actualNormalPolynomialFunction_actualAffineTranslation d t q (C i) hc)
  have he := heV a ha.1 hc i
  rw [hmk,quotient_actualNormalPolynomialFunction d t q _ (hCW a ha i)] at he
  rw [he]
  exact congrFun ((normalMonomialBasis d t q).repr_sum_self
    (fun β => HolGerm.mk (C i β ∘ actualAffineTranslation d (tangentProjection d t a)) (hCW a ha i β))) α


theorem exists_original_coherent_nearby_basis_coefficient_functions (d t q : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    let := tangentAlgebra d t
    let := normalExponentFintype t q
    ∃ U : Set (ComplexModel (d+t)), IsOpen U ∧ 0 ∈ U ∧
      ∃ (N : ℕ) (S : Fin N → ComplexModel (d+t) → ℂ),
        (∀ i, MDifferentiableOn 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) (S i) U) ∧
        (∀ a ∈ U, ∀ f, I.mem a f ↔ IsInSpanAt (n := d+t) (· ∈ range S) a f) ∧
        ∃ hhol : ∀ a ∈ U, ∀ i, HolAt (S i ∘ actualAffineTranslation (d+t) a) 0,
          (∀ a (ha : a ∈ U), originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I a) =
            Ideal.span (range fun i => HolGerm.mk (S i ∘ actualAffineTranslation (d+t) a) (hhol a ha i))) ∧
          (∀ a ∈ U, ∀ f, (actualTranslatedOriginalSheaf I a).mem 0 f ↔
            IsInSpanAt (n := d+t) (· ∈ range fun i => S i ∘ actualAffineTranslation (d+t) a) 0 f) ∧
          actualTranslatedJetImageDictionary d t I U N S hhol ∧
          ∃ hS0 : ∀ i, HolAt (S i) 0,
          ∃ C : Fin N → normalExponentIndex t q → ComplexModel d → ℂ,
          ∃ hC : ∀ i α, HolAt (C i α) 0,
          ∃ hCU : ∀ a ∈ U, ∀ i α,
            HolAt (C i α ∘ actualAffineTranslation d (tangentProjection d t a)) 0,
            (∀ i α, (normalMonomialBasis d t q).repr
              (Ideal.Quotient.mk (normalIdeal d t ^ q) (HolGerm.mk (S i) (hS0 i))) α =
                HolGerm.mk (C i α) (hC i α)) ∧
            ∀ a (ha : a ∈ U), a ∈ complexCoordinatePlane (d+t) d → ∀ i α,
              (normalMonomialBasis d t q).repr
                (Ideal.Quotient.mk (normalIdeal d t ^ q)
                  (HolGerm.mk (S i ∘ actualAffineTranslation (d+t) a) (hhol a ha i))) α =
                HolGerm.mk (C i α ∘ actualAffineTranslation d (tangentProjection d t a)) (hCU a ha i α) := by
  classical
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  dsimp only
  obtain ⟨U,hU,h0,N,S,hS,hgen,hhol,hideal,hmem,himage⟩ := exists_original_coherent_actual_translated_jets d t I hI
  have hS0 : ∀ i, HolAt (S i) 0 := by
    intro i
    simpa only [actualAffineTranslation,Function.comp_def,zero_add] using hhol 0 h0 i
  obtain ⟨V,hV,h0V,C,hC,hFV,hCV,horigin,hnearby⟩ :=
    exists_actual_nearby_finite_basis_coefficient_functions d t q S hS0
  let W := U ∩ V
  have hSW : ∀ a ∈ W, ∀ i, HolAt (S i ∘ actualAffineTranslation (d+t) a) 0 :=
    fun a ha i => hhol a ha.1 i
  have hCW : ∀ a ∈ W, ∀ i α,
      HolAt (C i α ∘ actualAffineTranslation d (tangentProjection d t a)) 0 :=
    fun a ha i α => hCV a ha.2 i α
  refine ⟨W,hU.inter hV,⟨h0,h0V⟩,N,S,fun i => (hS i).mono inter_subset_left,
    fun a ha f => hgen a ha.1 f,hSW,fun a ha => hideal a ha.1,
    fun a ha f => hmem a ha.1 f,?_,hS0,C,hC,hCW,horigin,?_⟩
  · exact fun a ha r => himage a ha.1 r
  · exact fun a ha hc i α => hnearby a ha.2 hc i α


end
end Hironaka.HironakaRelativeNormalNormalPowerSpread
