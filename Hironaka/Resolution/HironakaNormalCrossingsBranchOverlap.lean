/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.HolomorphicCoordinateFactorization
import Mathlib.Algebra.BigOperators.Associated
import Hironaka.Blowup.BlowupFlatCoordinates

import Hironaka.MarkedIdeal.GermIdealOrderValue
import Hironaka.MarkedIdeal.GermIdealOrderBounds

set_option autoImplicit false

/-!
# Intrinsic branches on actual normal-crossing chart overlaps

Original holomorphic coordinates produce prime branches and a unique
matching from the genuine carrier zero union. Actual units and finite
intersection germs are constructed internally. This does not assert
that the ordered canonical invariant ignores branch labels.
Blueprint: `hironaka-normal-crossings-branch-overlap-extension.tex`.
-/

open Set Filter
open scoped Topology

namespace Hironaka.HironakaNormalCrossingsBranchOverlap

open HolomorphicGermReducednessBridge AnalyticGermDecomposition

open Hironaka

noncomputable section

variable {n : ℕ}

/-- A true nonzero first derivative internally makes the actual equation germ prime. -/
theorem prime_germ_of_fderiv_ne_zero {f : ComplexModel n → ℂ}
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) (hf0 : f 0 = 0)
    (hdf : fderiv ℂ f 0 ≠ 0) : Prime (HolGerm.mk f hf) := by
  let : UniqueFactorizationMonoid (HolGerm (ComplexModel n)) :=
    ActualHolomorphicGermFactoriality.uniqueFactorizationMonoid_holGerm_euclidean n
  apply UniqueFactorizationMonoid.irreducible_iff_prime.mp
  constructor
  · intro hunit
    exact ((HolGerm.isUnit_iff_eval_ne_zero _).mp hunit) hf0
  · intro a b hab
    by_contra hunit
    push Not at hunit
    obtain ⟨g, hg, rfl⟩ := HolGerm.exists_eq_mk a
    obtain ⟨h, hh, rfl⟩ := HolGerm.exists_eq_mk b
    have hg0 : g 0 = 0 := by
      by_contra hne
      exact hunit.1 ((HolGerm.isUnit_iff_eval_ne_zero _).mpr hne)
    have hh0 : h 0 = 0 := by
      by_contra hne
      exact hunit.2 ((HolGerm.isUnit_iff_eval_ne_zero _).mpr hne)
    have heq : f =ᶠ[𝓝 0] fun z => g z * h z :=
      HolGerm.mk_eq_mk_iff.mp (hab.trans (HolGerm.mk_mul g h hg hh).symm)
    apply hdf
    rw [heq.fderiv_eq]
    change fderiv ℂ (g * h) 0 = 0
    rw [(hg.self_of_nhds.hasFDerivAt.mul hh.self_of_nhds.hasFDerivAt).fderiv]
    ext v
    simp [hg0, hh0]

private theorem holomorphic_product {ι : Type*} (s : Finset ι)
    (f : ι → ComplexModel n → ℂ)
    (hf : ∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (f i) z) :
    ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (fun z => ∏ i ∈ s, f i z) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using eventually_differentiableAt_const (E := ComplexModel n) 1
  | @insert i s hi ih =>
      simpa only [Finset.prod_insert hi] using eventually_differentiableAt_mul (hf i) ih

private theorem germ_product {ι : Type*} (s : Finset ι)
    (f : ι → ComplexModel n → ℂ)
    (hf : ∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (f i) z) :
    HolGerm.mk (fun z => ∏ i ∈ s, f i z) (holomorphic_product s f hf) =
      ∏ i ∈ s, HolGerm.mk (f i) (hf i) := by
  apply Subtype.ext
  rw [HolGerm.coe_mk, SubmonoidClass.coe_finsetProd]
  simp only [HolGerm.coe_mk]
  have h := map_prod
    (Germ.coeRingHom (𝓝 (0 : ComplexModel n)) :
      (ComplexModel n → ℂ) →+* Germ (𝓝 (0 : ComplexModel n)) ℂ) f s
  simp only [Germ.coe_coeRingHom] at h
  rw [← h, Finset.prod_fn]

private theorem exists_associated_of_zero_subset {ι : Type*} [Fintype ι]
    (f : ComplexModel n → ℂ) (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z)
    (hp : Prime (HolGerm.mk f hf))
    (g : ι → ComplexModel n → ℂ)
    (hg : ∀ j, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (g j) z)
    (hgp : ∀ j, Prime (HolGerm.mk (g j) (hg j)))
    (hzero : ∀ᶠ z in 𝓝 0, f z = 0 → ∃ j, g j z = 0) :
    ∃ j, Associated (HolGerm.mk f hf) (HolGerm.mk (g j) (hg j)) := by
  classical
  let P : ComplexModel n → ℂ := fun z => ∏ j, g j z
  have hP : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ P z := holomorphic_product Finset.univ g hg
  have hvan : HolGerm.mk P hP ∈ vanishingIdeal {z | ∀ _ : Fin 1, f z = 0} := by
    apply mem_vanishingIdeal_mk.mpr
    filter_upwards [hzero] with z hz hzf
    obtain ⟨j, hj⟩ := hz (hzf 0)
    exact Finset.prod_eq_zero (Finset.mem_univ j) hj
  let I : Ideal (HolGerm (ComplexModel n)) := Ideal.span {HolGerm.mk f hf}
  have hrad : HolGerm.mk P hP ∈ I.radical :=
    RueckertNullstellensatz.vanishingIdeal_le_radical I (fun _ : Fin 1 => f)
      (fun _ => ⟨hf, Ideal.subset_span (Set.mem_singleton _)⟩) hvan
  have hIr : I.IsRadical := (Ideal.isPrime_span_singleton_of_prime hp).isRadical
  rw [hIr.radical] at hrad
  have hdiv : HolGerm.mk f hf ∣ ∏ j, HolGerm.mk (g j) (hg j) := by
    rw [← germ_product Finset.univ g hg]
    exact Ideal.mem_span_singleton.mp hrad
  obtain ⟨j, _, hj⟩ := hp.exists_mem_finset_dvd hdiv
  exact ⟨j, hp.irreducible.associated_of_dvd (hgp j).irreducible hj⟩

/-- The actual zero union, not a supplied matching, produces the unique branch bijection. -/
theorem exists_unique_branch_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → ComplexModel n → ℂ) (g : κ → ComplexModel n → ℂ)
    (hf : ∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (f i) z)
    (hg : ∀ j, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (g j) z)
    (hfp : ∀ i, Prime (HolGerm.mk (f i) (hf i)))
    (hgp : ∀ j, Prime (HolGerm.mk (g j) (hg j)))
    (hfd : ∀ i i', Associated (HolGerm.mk (f i) (hf i)) (HolGerm.mk (f i') (hf i')) → i = i')
    (hgd : ∀ j j', Associated (HolGerm.mk (g j) (hg j)) (HolGerm.mk (g j') (hg j')) → j = j')
    (hzero : ∀ᶠ z in 𝓝 0, (∃ i, f i z = 0) ↔ ∃ j, g j z = 0) :
    ∃! σ : ι ≃ κ, ∀ i, Associated (HolGerm.mk (f i) (hf i)) (HolGerm.mk (g (σ i)) (hg (σ i))) := by
  classical
  have hfg : ∀ i, ∃ j, Associated (HolGerm.mk (f i) (hf i)) (HolGerm.mk (g j) (hg j)) := by
    intro i
    exact exists_associated_of_zero_subset (f i) (hf i) (hfp i) g hg hgp
      (hzero.mono fun z hz hi => hz.mp ⟨i, hi⟩)
  have hgf : ∀ j, ∃ i, Associated (HolGerm.mk (g j) (hg j)) (HolGerm.mk (f i) (hf i)) := by
    intro j
    exact exists_associated_of_zero_subset (g j) (hg j) (hgp j) f hf hfp
      (hzero.mono fun z hz hj => hz.mpr ⟨j, hj⟩)
  choose s hs using hfg
  have hinj : Function.Injective s := by
    intro i i' h
    apply hfd
    exact (hs i).trans (h ▸ (hs i').symm)
  have hsurj : Function.Surjective s := by
    intro j
    obtain ⟨i, hi⟩ := hgf j
    exact ⟨i, hgd _ _ (hs i |>.symm.trans hi.symm)⟩
  let σ : ι ≃ κ := Equiv.ofBijective s ⟨hinj, hsurj⟩
  refine ⟨σ, hs, ?_⟩
  intro τ hτ
  apply Equiv.ext
  intro i
  exact hgd _ _ ((hτ i).symm.trans (hs i))

private theorem coordinate_holomorphic {F : ComplexModel n → ComplexModel n}
    (hF : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ F z) (i : Fin n) :
    ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (fun z => F z i) z := by
  filter_upwards [hF] with z hz
  exact (EuclideanSpace.proj (𝕜 := ℂ) i).differentiableAt.comp z hz

private theorem coordinate_fderiv {F : ComplexModel n → ComplexModel n}
    (hF : DifferentiableAt ℂ F 0) (i : Fin n) (v : ComplexModel n) :
    fderiv ℂ (fun z => F z i) 0 v = (fderiv ℂ F 0 v) i := by
  have h := fderiv_comp (𝕜 := ℂ) 0
    (EuclideanSpace.proj (𝕜 := ℂ) i).differentiableAt hF
  rw [ContinuousLinearMap.fderiv] at h
  simpa only [ContinuousLinearMap.comp_apply,
    Function.comp_def, EuclideanSpace.coe_proj] using
    congrArg (fun L : ComplexModel n →L[ℂ] ℂ => L v) h

/-- Association yields an actual original holomorphic unit, with no supplied factorization. -/
theorem exists_unit_equation_of_associated {f g : ComplexModel n → ℂ}
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z)
    (hg : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ g z)
    (hassoc : Associated (HolGerm.mk f hf) (HolGerm.mk g hg)) :
    ∃ b : ComplexModel n → ℂ, (∀ᶠ z in 𝓝 0, DifferentiableAt ℂ b z) ∧
      b 0 ≠ 0 ∧ f =ᶠ[𝓝 0] fun z => b z * g z := by
  obtain ⟨v, hv⟩ := hassoc.symm
  obtain ⟨b, hb, hrep⟩ := HolGerm.exists_eq_mk (v : HolGerm (ComplexModel n))
  refine ⟨b, hb, ?_, ?_⟩
  · have h := (HolGerm.isUnit_iff_eval_ne_zero _).mp v.isUnit
    simpa only [hrep, HolGerm.eval_mk] using h
  · apply HolGerm.mk_eq_mk_iff.mp
    rw [HolGerm.mk_mul b g hb hg, ← hrep, mul_comm]
    exact hv.symm

private theorem zero_set_eq_of_associated {f g : ComplexModel n → ℂ}
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z)
    (hg : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ g z)
    (hassoc : Associated (HolGerm.mk f hf) (HolGerm.mk g hg)) :
    ∀ᶠ z in 𝓝 0, f z = 0 ↔ g z = 0 := by
  obtain ⟨b, hb, hb0, heq⟩ := exists_unit_equation_of_associated hf hg hassoc
  have hbne : ∀ᶠ z in 𝓝 0, b z ≠ 0 :=
    hb.self_of_nhds.continuousAt.eventually (isOpen_compl_singleton.mem_nhds hb0)
  filter_upwards [heq, hbne] with z hz hbz
  rw [hz, mul_eq_zero, or_iff_right hbz]

private theorem associated_of_zero_set_eq {f g : ComplexModel n → ℂ}
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z)
    (hg : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ g z)
    (hfp : Prime (HolGerm.mk f hf)) (hgp : Prime (HolGerm.mk g hg))
    (heq : ∀ᶠ z in 𝓝 0, f z = 0 ↔ g z = 0) :
    Associated (HolGerm.mk f hf) (HolGerm.mk g hg) := by
  obtain ⟨j, hj⟩ := exists_associated_of_zero_subset f hf hfp
    (fun _ : Fin 1 => g) (fun _ => hg) (fun _ => hgp)
    (heq.mono fun z hz hfz => ⟨0, hz.mp hfz⟩)
  exact hj

/-- The true surjective coordinate differential produces each genuine prime branch. -/
theorem prime_coordinate_of_surjective_fderiv {F : ComplexModel n → ComplexModel n}
    (hF : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ F z) (hF0 : F 0 = 0)
    (hsurj : Function.Surjective (fderiv ℂ F 0)) (i : Fin n) :
    Prime (HolGerm.mk (fun z => F z i) (coordinate_holomorphic hF i)) := by
  apply prime_germ_of_fderiv_ne_zero
  · simp [hF0]
  · intro hzero
    obtain ⟨v, hv⟩ := hsurj (AnalyticJacobianSingularCore.coordinateDirection i)
    have h := coordinate_fderiv hF.self_of_nhds i v
    rw [hzero, hv] at h
    simp [AnalyticJacobianSingularCore.coordinateDirection] at h

/-- Different original coordinate rows cannot become associated under a true local chart. -/
theorem eq_of_associated_coordinates_of_surjective_fderiv
    {F : ComplexModel n → ComplexModel n}
    (hF : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ F z) (hF0 : F 0 = 0)
    (hsurj : Function.Surjective (fderiv ℂ F 0)) (i j : Fin n)
    (hassoc : Associated
      (HolGerm.mk (fun z => F z i) (coordinate_holomorphic hF i))
      (HolGerm.mk (fun z => F z j) (coordinate_holomorphic hF j))) : i = j := by
  by_contra hij
  obtain ⟨B, hB⟩ := hassoc.dvd
  obtain ⟨b, hb, hrep⟩ := HolGerm.exists_eq_mk B
  have heq : (fun z => F z j) =ᶠ[𝓝 0] fun z => F z i * b z := by
    apply HolGerm.mk_eq_mk_iff.mp
    rw [HolGerm.mk_mul (fun z => F z i) b (coordinate_holomorphic hF i) hb, ← hrep]
    exact hB
  obtain ⟨v, hv⟩ := hsurj (AnalyticJacobianSingularCore.coordinateDirection j)
  have hdj := coordinate_fderiv hF.self_of_nhds j v
  have hdi := coordinate_fderiv hF.self_of_nhds i v
  rw [hv] at hdj hdi
  have hprod := ((coordinate_holomorphic hF i).self_of_nhds.hasFDerivAt.mul
    hb.self_of_nhds.hasFDerivAt).fderiv
  have h := congrArg (fun L : ComplexModel n →L[ℂ] ℂ => L v)
    (heq.fderiv_eq.trans hprod)
  simp only [add_apply, smul_apply, hF0, PiLp.zero_apply, zero_smul, zero_add] at h
  rw [hdj, hdi] at h
  simp [AnalyticJacobianSingularCore.coordinateDirection, hij] at h

private theorem shifted_holomorphic {q : ComplexModel n}
    (Φ : LocalHolomorphicEquivAt (n := n) q) :
    ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (fun z => Φ.toFun (z + q)) z := by
  have ht : Tendsto (fun z : ComplexModel n => z + q) (𝓝 0) (𝓝 q) := by
    simpa only [zero_add] using (continuous_add_const q).tendsto 0
  filter_upwards [ht.eventually (Φ.isOpen_source.mem_nhds Φ.center_mem_source)] with z hz
  exact (Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hz)).comp z
    (differentiableAt_id.add_const q)

/-- The genuine local inverse internally produces a surjective differential of the original chart. -/
theorem surjective_fderiv_shifted {q : ComplexModel n}
    (Φ : LocalHolomorphicEquivAt (n := n) q) :
    Function.Surjective (fderiv ℂ (fun z => Φ.toFun (z + q)) 0) := by
  have hdF := Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds Φ.center_mem_source)
  have hqT := Φ.mapsTo_toFun Φ.center_mem_source
  have hdG := Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hqT)
  have heq : (Φ.toFun ∘ Φ.invFun) =ᶠ[𝓝 (Φ.toFun q)] id := by
    filter_upwards [Φ.isOpen_target.mem_nhds hqT] with z hz
    exact Φ.right_inv z hz
  have hcomp := fderiv_comp (𝕜 := ℂ) (Φ.toFun q)
    (by simpa only [Φ.left_inv q Φ.center_mem_source] using hdF) hdG
  rw [heq.fderiv_eq, fderiv_id, Φ.left_inv q Φ.center_mem_source] at hcomp
  have hsurj : Function.Surjective (fderiv ℂ Φ.toFun q) := by
    intro w
    refine ⟨fderiv ℂ Φ.invFun (Φ.toFun q) w, ?_⟩
    exact (congrArg (fun L : ComplexModel n →L[ℂ] ComplexModel n => L w) hcomp).symm
  have hshift := fderiv_comp (𝕜 := ℂ) (f := fun z : ComplexModel n => z + q)
    (g := Φ.toFun) 0
    (by simpa only [id_eq, zero_add] using hdF)
    (differentiableAt_id.add_const q)
  have hadd : fderiv ℂ (fun z : ComplexModel n => z + q) 0 = ContinuousLinearMap.id ℂ _ := by
    exact ((hasFDerivAt_id (𝕜 := ℂ) (0 : ComplexModel n)).add_const q).fderiv
  simp only [zero_add, hadd, ContinuousLinearMap.comp_id] at hshift
  change fderiv ℂ (fun z => Φ.toFun (z + q)) 0 = fderiv ℂ Φ.toFun q at hshift
  rw [hshift]
  exact hsurj

/-- Equal actual NC chart zero unions internally produce a unique branch bijection. -/
theorem exists_unique_coordinate_branch_equiv {q : ComplexModel n}
    (Φ Ψ : LocalHolomorphicEquivAt (n := n) q)
    (hΦ0 : Φ.toFun q = 0) (hΨ0 : Ψ.toFun q = 0)
    (S T : Finset (Fin n))
    (hzero : ∀ᶠ z in 𝓝 0,
      (∃ i ∈ S, Φ.toFun (z + q) i = 0) ↔ ∃ j ∈ T, Ψ.toFun (z + q) j = 0) :
    ∃! σ : S ≃ T, ∀ i : S, Associated
      (HolGerm.mk (fun z => Φ.toFun (z + q) i) (coordinate_holomorphic (shifted_holomorphic Φ) i))
      (HolGerm.mk (fun z => Ψ.toFun (z + q) (σ i))
        (coordinate_holomorphic (shifted_holomorphic Ψ) (σ i))) := by
  refine exists_unique_branch_equiv
    (fun (i : S) z => Φ.toFun (z + q) i)
    (fun (j : T) z => Ψ.toFun (z + q) j)
    (fun i => coordinate_holomorphic (shifted_holomorphic Φ) i)
    (fun j => coordinate_holomorphic (shifted_holomorphic Ψ) j) ?_ ?_ ?_ ?_ ?_
  · intro i
    exact prime_coordinate_of_surjective_fderiv (shifted_holomorphic Φ)
      (by simpa only [zero_add] using hΦ0) (surjective_fderiv_shifted Φ) i
  · intro j
    exact prime_coordinate_of_surjective_fderiv (shifted_holomorphic Ψ)
      (by simpa only [zero_add] using hΨ0) (surjective_fderiv_shifted Ψ) j
  · intro i i' h
    apply Subtype.ext
    exact eq_of_associated_coordinates_of_surjective_fderiv (shifted_holomorphic Φ)
      (by simpa only [zero_add] using hΦ0) (surjective_fderiv_shifted Φ) i i' h
  · intro j j' h
    apply Subtype.ext
    exact eq_of_associated_coordinates_of_surjective_fderiv (shifted_holomorphic Ψ)
      (by simpa only [zero_add] using hΨ0) (surjective_fderiv_shifted Ψ) j j' h
  · simpa only [Subtype.exists, Finset.mem_coe, exists_prop] using hzero

/-- Original chart zero unions produce all actual units on one common neighbourhood. -/
theorem exists_coordinate_unit_branch_equiv {q : ComplexModel n}
    (Φ Ψ : LocalHolomorphicEquivAt (n := n) q)
    (hΦ0 : Φ.toFun q = 0) (hΨ0 : Ψ.toFun q = 0)
    (S T : Finset (Fin n))
    (hzero : ∀ᶠ z in 𝓝 0,
      (∃ i ∈ S, Φ.toFun (z + q) i = 0) ↔ ∃ j ∈ T, Ψ.toFun (z + q) j = 0) :
    ∃ (σ : S ≃ T) (b : S → ComplexModel n → ℂ), S.card = T.card ∧
      (∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (b i) z) ∧
      (∀ i, b i 0 ≠ 0) ∧
      ∀ᶠ z in 𝓝 0, ∀ i : S, Φ.toFun (z + q) i = b i z * Ψ.toFun (z + q) (σ i) := by
  classical
  obtain ⟨σ, hσ, _⟩ := exists_unique_coordinate_branch_equiv Φ Ψ hΦ0 hΨ0 S T hzero
  have hunit := fun i : S => exists_unit_equation_of_associated
    (coordinate_holomorphic (shifted_holomorphic Φ) i)
    (coordinate_holomorphic (shifted_holomorphic Ψ) (σ i)) (hσ i)
  choose b hb hb0 hbeq using hunit
  exact ⟨σ, b, by simpa using Fintype.card_congr σ, hb, hb0, eventually_all.mpr hbeq⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

open BlowupFlatCoordinates Hironaka.HolomorphicIdealSheaves

/-- From two actual original carrier flattenings, all branch germs are internally matched. -/
theorem exists_unique_original_branch_equiv {x : M} {H : Set M}
    (Φ Ψ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (hΨ0 : Ψ.toFun (chartAt (ComplexModel n) x x) = 0)
    (S T : Finset (Fin n))
    (hΦH : ∀ y ∈ flatDomain Φ, y ∈ H ↔ ∃ i ∈ S, flatCoord Φ i y = 0)
    (hΨH : ∀ y ∈ flatDomain Ψ, y ∈ H ↔ ∃ j ∈ T, flatCoord Ψ j y = 0) :
    ∃! σ : S ≃ T, ∀ i : S,
      ∀ᶠ y in 𝓝 x, flatCoord Φ i y = 0 ↔ flatCoord Ψ (σ i) y = 0 := by
  let e := chartAt (ComplexModel n) x
  let q := e x
  have ht : Tendsto (fun z : ComplexModel n => z + q) (𝓝 0) (𝓝 q) := by
    simpa only [zero_add] using (continuous_add_const q).tendsto 0
  have hInv : Tendsto (fun z : ComplexModel n => e.symm (z + q)) (𝓝 0) (𝓝 x) := by
    simpa only [Function.comp_def, e.left_inv (mem_chart_source _ x)] using
      (e.continuousAt_symm (e.map_source (mem_chart_source _ x))).tendsto.comp ht
  have hdom : ∀ᶠ z in 𝓝 0, z + q ∈ e.target ∧
      e.symm (z + q) ∈ flatDomain Φ ∩ flatDomain Ψ :=
    (ht.eventually (e.open_target.mem_nhds (e.map_source (mem_chart_source _ x)))).and
      (hInv.eventually (((isOpen_flatDomain Φ).inter (isOpen_flatDomain Ψ)).mem_nhds
        ⟨mem_flatDomain_self Φ, mem_flatDomain_self Ψ⟩))
  have hzero : ∀ᶠ z in 𝓝 0,
      (∃ i ∈ S, Φ.toFun (z + q) i = 0) ↔ ∃ j ∈ T, Ψ.toFun (z + q) j = 0 := by
    filter_upwards [hdom] with z hz
    have hh := (hΦH _ hz.2.1).symm.trans (hΨH _ hz.2.2)
    change (∃ i ∈ S, Φ.toFun (e (e.symm (z + q))) i = 0) ↔
      ∃ j ∈ T, Ψ.toFun (e (e.symm (z + q))) j = 0 at hh
    rwa [e.right_inv hz.1] at hh
  obtain ⟨σ, hσ, hσunique⟩ := exists_unique_coordinate_branch_equiv Φ Ψ hΦ0 hΨ0 S T hzero
  have hC : Tendsto (fun y : M => e y - q) (𝓝 x) (𝓝 0) := by
    simpa only [q, sub_self] using (e.continuousAt (mem_chart_source _ x)).sub_const q
  refine ⟨σ, ?_, ?_⟩
  · intro i
    have heq := zero_set_eq_of_associated
      (coordinate_holomorphic (shifted_holomorphic Φ) i)
      (coordinate_holomorphic (shifted_holomorphic Ψ) (σ i)) (hσ i)
    simpa only [flatCoord, e, q, sub_add_cancel] using hC.eventually heq
  · intro τ hτ
    apply hσunique
    intro i
    apply associated_of_zero_set_eq
      (coordinate_holomorphic (shifted_holomorphic Φ) i)
      (coordinate_holomorphic (shifted_holomorphic Ψ) (τ i))
      (prime_coordinate_of_surjective_fderiv (shifted_holomorphic Φ)
        (by simpa only [zero_add] using hΦ0) (surjective_fderiv_shifted Φ) i)
      (prime_coordinate_of_surjective_fderiv (shifted_holomorphic Ψ)
        (by simpa only [zero_add] using hΨ0) (surjective_fderiv_shifted Ψ) (τ i))
    filter_upwards [hdom, hInv.eventually (hτ i)] with z hz heq
    change Φ.toFun (e (e.symm (z + q))) i = 0 ↔
      Ψ.toFun (e (e.symm (z + q))) (τ i) = 0 at heq
    rwa [e.right_inv hz.1] at heq

/-- The genuine matching supplies intrinsic original branch counts and all intersection germs. -/
theorem exists_original_branch_equiv_intersections {x : M} {H : Set M}
    (Φ Ψ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (hΨ0 : Ψ.toFun (chartAt (ComplexModel n) x x) = 0)
    (S T : Finset (Fin n))
    (hΦH : ∀ y ∈ flatDomain Φ, y ∈ H ↔ ∃ i ∈ S, flatCoord Φ i y = 0)
    (hΨH : ∀ y ∈ flatDomain Ψ, y ∈ H ↔ ∃ j ∈ T, flatCoord Ψ j y = 0) :
    ∃ σ : S ≃ T, S.card = T.card ∧
      ∀ᶠ y in 𝓝 x,
        (∀ i : S, flatCoord Φ i y = 0 ↔ flatCoord Ψ (σ i) y = 0) ∧
        ∀ A : Finset S, (∀ i ∈ A, flatCoord Φ i y = 0) ↔
          ∀ i ∈ A, flatCoord Ψ (σ i) y = 0 := by
  classical
  obtain ⟨σ, hσ, _⟩ := exists_unique_original_branch_equiv Φ Ψ hΦ0 hΨ0 S T hΦH hΨH
  refine ⟨σ, by simpa using Fintype.card_congr σ, ?_⟩
  filter_upwards [eventually_all.mpr hσ] with y hy
  refine ⟨hy, fun A => ⟨fun h i hi => (hy i).mp (h i hi), fun h i hi => (hy i).mpr (h i hi)⟩⟩

end
end Hironaka.HironakaNormalCrossingsBranchOverlap
