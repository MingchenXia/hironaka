/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaRelativeNormalIdeal
import Hironaka.Blowup.BlowupFlatCoordinates

/-!
# Entire original smooth-centre ideals and true relative power quotients

Original RegularAtDim and actual closed smooth centre geometry internally
produce a genuinely recentered original flattening, its entire nonlinear
holomorphic germ algebra equivalence, the WHOLE original vanishing stalk
ideal and ALL its powers. Every original quotient is genuinely transported,
and its entire relative finite module over the actual original tangential
base algebra is internally constructed from true finite normal words.
Module finiteness does not establish normal flatness, freeness, higher-HS
transformation or general G8 termination. No conclusion certificate is input
to the final actual regular-point or actual closed-centre producers.
Blueprint: `hironaka-smooth-centre-relative-ideal-extension.tex`.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaSmoothCentreRelativeIdeal
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan
  HironakaHolomorphicJetRankLoci HironakaHolomorphicJetChartInvariance
  HironakaRelativeNormalIdeal BlowupFlatCoordinates
open Hironaka
attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass
noncomputable section
variable {n : ℕ}

/-- Actual nonlinear original flattening, translated to its genuine zero centre. -/
def recenteredEquiv (p : ComplexModel n) (Φ : LocalHolomorphicEquivAt p) :
    LocalHolomorphicEquivAt (0 : ComplexModel n) where
  source := (fun z => z+p) ⁻¹' Φ.source
  target := Φ.target
  isOpen_source := Φ.isOpen_source.preimage (continuous_id.add continuous_const)
  isOpen_target := Φ.isOpen_target
  center_mem_source := by simpa only [mem_preimage, zero_add] using Φ.center_mem_source
  toFun := fun z => Φ.toFun (z+p)
  invFun := fun w => Φ.invFun w-p
  toFun_holomorphic := by
    intro z hz
    exact ((Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hz)).comp z
      (differentiableAt_id.add_const p)).differentiableWithinAt
  invFun_holomorphic := fun w hw =>
    ((Φ.invFun_holomorphic w hw).sub_const p)
  mapsTo_toFun := fun z hz => Φ.mapsTo_toFun hz
  mapsTo_invFun := by
    intro w hw
    change Φ.invFun w-p+p ∈ Φ.source
    rw [sub_add_cancel]
    exact Φ.mapsTo_invFun hw
  left_inv := by
    intro z hz
    rw [Φ.left_inv _ hz, add_sub_cancel_right]
  right_inv := by
    intro w hw
    rw [sub_add_cancel]
    exact Φ.right_inv w hw

/-- The actual original base-value identity makes the internally recentered equivalence fix zero. -/
theorem recenteredEquiv_zero (p : ComplexModel n) (Φ : LocalHolomorphicEquivAt p)
    (h0 : Φ.toFun p = 0) : (recenteredEquiv p Φ).toFun 0 = 0 := by
  simpa only [recenteredEquiv, zero_add] using h0

/-- The real entire germ algebra equivalence induced by the actual original flattening. -/
def flatteningGermEquiv (p : ComplexModel n) (Φ : LocalHolomorphicEquivAt p)
    (h0 : Φ.toFun p = 0) : HolGerm (ComplexModel n) ≃ₐ[ℂ] HolGerm (ComplexModel n) :=
  localGermAlgEquiv (recenteredEquiv p Φ) (recenteredEquiv_zero p Φ h0)

section Manifold
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] (x : M)

/-- The true entire map of each original coordinate equals its original flattened chart germ. -/
theorem flatteningGermEquiv_coordinateGerm
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0) (j : Fin n) :
    flatteningGermEquiv _ Φ h0 (coordinateGerm j) =
      chartTranslatedGerm x x (mem_chart_source _ x) (flatCoord Φ j)
        (holomorphicAt_flatCoord Φ j (mem_flatDomain_self Φ)) := by
  unfold flatteningGermEquiv coordinateGerm
  rw [localGermAlgEquiv_mk]
  simp only [chartTranslatedGerm, translatedGerm]
  apply HolGerm.mk_eq_mk_iff.mpr
  let e := chartAt (ComplexModel n) x
  have ht : Tendsto (fun z : ComplexModel n => z+e x) (𝓝 0) (𝓝 (e x)) := by
    simpa only [id_eq, zero_add] using (continuous_id.add_const (e x)).tendsto (0 : ComplexModel n)
  filter_upwards [ht.eventually (e.open_target.mem_nhds (e.map_source (mem_chart_source _ x)))] with z hz
  change Φ.toFun (z+e x) j = Φ.toFun (e (e.symm (z+e x))) j
  rw [e.right_inv hz]

private theorem chartTranslatedGerm_congr {f g : M → ℂ}
    (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x) (heq : f =ᶠ[𝓝 x] g) :
    chartTranslatedGerm x x (mem_chart_source _ x) f hf =
      chartTranslatedGerm x x (mem_chart_source _ x) g hg := by
  simp only [chartTranslatedGerm, translatedGerm]
  apply HolGerm.mk_eq_mk_iff.mpr
  let e := chartAt (ComplexModel n) x
  have ht : Tendsto (fun z : ComplexModel n => e.symm (z+e x)) (𝓝 0) (𝓝 x) := by
    have ha : Tendsto (fun z : ComplexModel n => z+e x) (𝓝 0) (𝓝 (e x)) := by
      simpa only [id_eq, zero_add] using (continuous_id.add_const (e x)).tendsto (0 : ComplexModel n)
    have hb := (e.continuousAt_symm (e.map_source (mem_chart_source _ x))).tendsto
    simpa only [e.left_inv (mem_chart_source _ x), Function.comp_def] using hb.comp ha
  exact ht.eventually heq

private theorem chartTranslatedGerm_sum_mul {ι : Type*} [Fintype ι]
    (f g : ι → M → ℂ) (hf : ∀ i, HolomorphicAt n (f i) x)
    (hg : ∀ i, HolomorphicAt n (g i) x) :
    chartTranslatedGerm x x (mem_chart_source _ x) (fun y => ∑ i, f i y*g i y)
        (HolomorphicAt.sum Finset.univ fun i _ => (hf i).mul (hg i)) =
      ∑ i, chartTranslatedGerm x x (mem_chart_source _ x) (f i) (hf i) *
        chartTranslatedGerm x x (mem_chart_source _ x) (g i) (hg i) := by
  simp only [chartTranslatedGerm, translatedGerm]
  rw [HolGerm.mk_sum Finset.univ]
  · exact Finset.sum_congr rfl fun i _ => HolGerm.mk_mul _ _ _ _
  · intro i
    exact translated_holomorphic _ (CartanLocalReduction.holAt_comp_chart_symm (mem_chart_source _ x)
      ((hf i).mul (hg i)))

/-- ALL original vanishing stalk germs are exactly the transported WHOLE coordinate-plane normal ideal. -/
theorem whole_vanishing_stalk_eq_map_normalIdeal {d t : ℕ}
    [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]
    (C : Set M) (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x) = 0)
    (hflat : ∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
      chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) :
    wholeChartStalkIdeal (vanishingIdeal (n := d+t) C) x x (mem_chart_source _ x) =
      Ideal.map (flatteningGermEquiv _ Φ h0).toRingEquiv.toRingHom (normalIdeal d t) := by
  let E := flatteningGermEquiv _ Φ h0
  let J := Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t)
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro g ⟨f, hf, hmem, rfl⟩
    obtain ⟨b, hb0, hb, he⟩ := exists_eq_sum_flatCoord Φ hsrc hflat (mem_flatDomain_self Φ) hmem
    have hG : ∀ i, HolomorphicAt (d+t) (flatCoord Φ i) x :=
      fun i => holomorphicAt_flatCoord Φ i (mem_flatDomain_self Φ)
    rw [chartTranslatedGerm_congr x hf (HolomorphicAt.sum Finset.univ fun i _ => (hb i).mul (hG i)) he,
      chartTranslatedGerm_sum_mul x b (flatCoord Φ) hb hG, Fin.sum_univ_add]
    have hz : ∑ i : Fin d,
        chartTranslatedGerm x x (mem_chart_source _ x) (b (i.castAdd t)) (hb _) *
          chartTranslatedGerm x x (mem_chart_source _ x) (flatCoord Φ (i.castAdd t)) (hG _) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hbi := hb0 (i.castAdd t) i.isLt
      simp only [hbi]
      change HolGerm.mk (fun _ : ComplexModel (d+t) => (0 : ℂ)) eventually_differentiableAt_zero * _ = 0
      have he0 : HolGerm.mk (fun _ : ComplexModel (d+t) => (0 : ℂ)) eventually_differentiableAt_zero = 0 := HolGerm.mk_zero
      rw [he0, zero_mul]
    rw [hz, zero_add]
    apply Ideal.sum_mem
    intro i _
    apply Ideal.mul_mem_left
    have hcoord : normalCoordinate d t i ∈ normalIdeal d t := Ideal.subset_span ⟨i, rfl⟩
    have hm := Ideal.mem_map_of_mem E.toRingEquiv.toRingHom hcoord
    change E (normalCoordinate d t i) ∈ J at hm
    dsimp only [E, normalCoordinate] at hm
    rw [flatteningGermEquiv_coordinateGerm x Φ h0] at hm
    exact hm
  · change Ideal.map E.toRingEquiv.toRingHom (Ideal.span (range (normalCoordinate d t))) ≤ _
    rw [Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro g ⟨a, ⟨i, rfl⟩, rfl⟩
    change E (normalCoordinate d t i) ∈ _
    dsimp only [E, normalCoordinate]
    rw [flatteningGermEquiv_coordinateGerm x Φ h0]
    apply Ideal.subset_span
    refine ⟨flatCoord Φ (i.natAdd d), holomorphicAt_flatCoord Φ _ (mem_flatDomain_self Φ), ?_, rfl⟩
    exact flatCoord_mem_vanishingIdeal Φ hflat (by simp) (mem_flatDomain_self Φ)

end Manifold

/-- The actual all-q representative can be expressed with ENTIRE original tangential coefficient germs. -/
theorem exists_normalWord_coefficient_representative (d t q : ℕ) (g : HolGerm (ComplexModel (d+t))) :
    ∃ a : monomialIndex t q → HolGerm (ComplexModel d),
      g - ∑ w, tangentPullback d t (a w) * normalWord d t w ∈ normalIdeal d t ^ q := by
  let := tangentAlgebra d t
  obtain ⟨p, hp, hrem⟩ := exists_normalWord_representative d t q g
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (HolGerm (ComplexModel d))).mp hp
  refine ⟨a, ?_⟩
  have he : (∑ w, tangentPullback d t (a w) * normalWord d t w) = p := by
    rw [← ha]
    apply Finset.sum_congr rfl
    intro w _
    rw [Algebra.smul_def]
    rfl
  rwa [he]

/-- Whole original tangential algebra transported by the actual entire nonlinear germ map. -/
@[instance_reducible] def transportedNormalAlgebra (d t : ℕ)
    (E : HolGerm (ComplexModel (d+t)) ≃ₐ[ℂ] HolGerm (ComplexModel (d+t))) :
    Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
  (E.toAlgHom.comp (tangentPullback d t)).toRingHom.toAlgebra

/-- The finite genuine transported normal word family over the ENTIRE base germ ring. -/
def transportedWordSpan (d t q : ℕ)
    (E : HolGerm (ComplexModel (d+t)) ≃ₐ[ℂ] HolGerm (ComplexModel (d+t))) :
    letI := transportedNormalAlgebra d t E
    Submodule (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
  letI := transportedNormalAlgebra d t E
  Submodule.span (HolGerm (ComplexModel d)) (range fun w : monomialIndex t q => E (normalWord d t w))

/-- Genuine all-power whole representatives in the internally transported tangential algebra. -/
theorem exists_transported_normalWord_representative (d t q : ℕ)
    (E : HolGerm (ComplexModel (d+t)) ≃ₐ[ℂ] HolGerm (ComplexModel (d+t)))
    (g : HolGerm (ComplexModel (d+t))) :
    letI := transportedNormalAlgebra d t E
    ∃ p ∈ transportedWordSpan d t q E,
      g-p ∈ Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t) ^ q := by
  let := transportedNormalAlgebra d t E
  obtain ⟨a, hrem⟩ := exists_normalWord_coefficient_representative d t q (E.symm g)
  let P := ∑ w : monomialIndex t q, a w • E (normalWord d t w)
  refine ⟨P, ?_, ?_⟩
  · exact Submodule.sum_mem _ fun w _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, rfl⟩)
  · have hm := Ideal.mem_map_of_mem E.toRingEquiv.toRingHom hrem
    rw [Ideal.map_pow] at hm
    have he : E.toRingEquiv.toRingHom
        (E.symm g - ∑ w, tangentPullback d t (a w) * normalWord d t w) = g-P := by
      change E (E.symm g - ∑ w, tangentPullback d t (a w) * normalWord d t w) = g-P
      rw [map_sub, map_sum, E.apply_symm_apply]
      congr 1
      apply Finset.sum_congr rfl
      intro w _
      rw [map_mul, Algebra.smul_def]
      rfl
    rwa [he] at hm

/-- Literal entire original quotients by a whole ideal plus each transported true power are finite base modules. -/
theorem finite_quotient_sup_mapped_normalIdeal_pow (d t q : ℕ)
    (E : HolGerm (ComplexModel (d+t)) ≃ₐ[ℂ] HolGerm (ComplexModel (d+t)))
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    letI := transportedNormalAlgebra d t E
    Module.Finite (HolGerm (ComplexModel d))
      (HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t) ^ q)) := by
  let := transportedNormalAlgebra d t E
  let J := I ⊔ Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t) ^ q
  let Q := (Ideal.Quotient.mkₐ (HolGerm (ComplexModel d)) J).toLinearMap
  have he : (transportedWordSpan d t q E).map Q = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨p, hp, hrem⟩ := exists_transported_normalWord_representative d t q E g
    apply Submodule.mem_map.mpr
    refine ⟨p, hp, ?_⟩
    change Ideal.Quotient.mk J p = Ideal.Quotient.mk J g
    exact (Ideal.Quotient.eq.mpr ((show Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t) ^ q ≤ J from le_sup_right) hrem)).symm
  apply Module.Finite.of_fg_top
  rw [← he]
  exact (Submodule.fg_span (Set.finite_range _)).map Q

/-- The actual nonlinear germ algebra map transports ALL whole normal ideal powers. -/
theorem map_normalIdeal_pow (d t q : ℕ)
    (E : HolGerm (ComplexModel (d+t)) ≃ₐ[ℂ] HolGerm (ComplexModel (d+t))) :
    Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t ^ q) =
      Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t) ^ q := Ideal.map_pow _ _ _

/-- The literal entire quotient is transported using the true whole inverse ideal and every actual normal power. -/
def transportedPowerQuotientAlgEquiv (d t q : ℕ)
    (E : HolGerm (ComplexModel (d+t)) ≃ₐ[ℂ] HolGerm (ComplexModel (d+t)))
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    (HolGerm (ComplexModel (d+t)) ⧸
      (Ideal.comap E.toRingEquiv.toRingHom I ⊔ normalIdeal d t ^ q)) ≃ₐ[ℂ]
    (HolGerm (ComplexModel (d+t)) ⧸
      (I ⊔ Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t) ^ q)) :=
  Ideal.quotientEquivAlg _ _ E (by
    change I ⊔ Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t) ^ q =
      Ideal.map E.toRingEquiv.toRingHom (Ideal.comap E.toRingEquiv.toRingHom I ⊔ normalIdeal d t ^ q)
    rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_comap_of_surjective E.toRingEquiv.toRingHom E.surjective])

section RegularProducer
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- Original actual regularity internally produces the entire ideal, every power, whole quotient transport and real finite relative base modules. -/
theorem exists_regular_relative_ideal (C : Set M) (x : M)
    (hreg : RegularAtDim (n := d+t) C x d) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target ∧
      ∃ h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x) = 0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      let E := flatteningGermEquiv _ Φ h0
      let K := wholeChartStalkIdeal (vanishingIdeal (n := d+t) C) x x (mem_chart_source _ x)
      K = Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t) ∧
      (∀ q : ℕ, Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t ^ q) = K ^ q) ∧
      (∀ (q : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))),
        Nonempty ((HolGerm (ComplexModel (d+t)) ⧸
          (Ideal.comap E.toRingEquiv.toRingHom I ⊔ normalIdeal d t ^ q)) ≃ₐ[ℂ]
          (HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ K ^ q)))) ∧
      (letI := transportedNormalAlgebra d t E
        ∀ (q : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))),
          Module.Finite (HolGerm (ComplexModel d))
            (HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ K ^ q))) := by
  obtain ⟨_, _, Φ, hsrc, h0, hflat⟩ := hreg
  have hK := whole_vanishing_stalk_eq_map_normalIdeal x C Φ hsrc h0 hflat
  refine ⟨Φ, hsrc, h0, hflat, hK, ?_, ?_, ?_⟩
  · intro q
    rw [map_normalIdeal_pow, ← hK]
  · intro q I
    rw [hK]
    exact ⟨transportedPowerQuotientAlgEquiv d t q (flatteningGermEquiv _ Φ h0) I⟩
  · intro q I
    rw [hK]
    exact finite_quotient_sup_mapped_normalIdeal_pow d t q (flatteningGermEquiv _ Φ h0) I

end RegularProducer

section ClosedProducer
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

@[instance_reducible] private def chartedSpaceOfSumEq (d t : ℕ) (he : d+t=n) : ChartedSpace (ComplexModel (d+t)) M :=
  he.symm ▸ (inferInstance : ChartedSpace (ComplexModel n) M)

private theorem complexManifoldOfSumEq (d t : ℕ) (he : d+t=n) :
    letI := chartedSpaceOfSumEq (M := M) d t he
    IsComplexManifold (d+t) M := by
  subst n
  exact inferInstance

/-- True closed smooth centre geometry supplies every actual point its own dimension and the whole relative ideal/power/quotient/base-module producer. -/
theorem exists_closed_smooth_relative_ideal (C : Set M)
    (hC : Hironaka.BlowupSequences.IsClosedSubmanifold n C) (x : M) (hx : x ∈ C) :
    ∃ d t : ℕ, ∃ he : d+t=n,
      letI := chartedSpaceOfSumEq (M := M) d t he
      letI := complexManifoldOfSumEq (M := M) d t he
      ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
        Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target ∧
        ∃ h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x) = 0,
        (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
          chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
          (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
        let E := flatteningGermEquiv _ Φ h0
        let K := wholeChartStalkIdeal (vanishingIdeal (n := d+t) C) x x (mem_chart_source _ x)
        K = Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t) ∧
        (∀ q : ℕ, Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t ^ q) = K ^ q) ∧
        (∀ (q : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))),
          Nonempty ((HolGerm (ComplexModel (d+t)) ⧸
            (Ideal.comap E.toRingEquiv.toRingHom I ⊔ normalIdeal d t ^ q)) ≃ₐ[ℂ]
            (HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ K ^ q)))) ∧
        (letI := transportedNormalAlgebra d t E
          ∀ (q : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))),
            Module.Finite (HolGerm (ComplexModel d))
              (HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ K ^ q))) := by
  obtain ⟨d, hreg⟩ := hC.2 x hx
  have hd : d ≤ n := hreg.1
  generalize ht : n-d=t
  have he : d+t=n := by omega
  subst n
  refine ⟨d, t, rfl, ?_⟩
  exact exists_regular_relative_ideal C x hreg

end ClosedProducer

end
end Hironaka.HironakaSmoothCentreRelativeIdeal
