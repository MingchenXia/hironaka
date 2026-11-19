import Hironaka.Analytic.Unibranch.HironakaG10LfMatsumura
import Hironaka.Analytic.Unibranch.HironakaG10LfChartAlgebra
import Hironaka.Analytic.Unibranch.HironakaG10LfChart

/-!
# Item 1: the local flatness criterion over a singular base (lane G10LF, for G10TM's plan)

Module and statement names fixed by lane G10TM's plan (`work/hironaka-run0081-20261117/G10TM/STATUS.md`,
"Item 1 statement (for G10FR/G10GF)").

* **(1a) `flat_of_maximalIdeal_rTensor_injective`** — `B → C` a local homomorphism of Noetherian local
  rings, `M` a finite `C`-module: if `𝔪_B ⊗_B M → M` is injective (`Tor₁^B(B/𝔪_B, M) = 0`), then `M` is
  flat over `B` (Matsumura, Th. 22.3, (3) ⇒ (1); the converse is
  `Module.Flat.rTensor_preserves_injective_linearMap`). Proof without `Tor` in
  `HironakaG10LfMatsumura`.
* **(1b) chart form, any base ideal `I ≤ 𝔪`** — `ExactStartModAt d t I G F p` (`G` is an exact start of
  `F` modulo `I · 𝒪` at `p`); **`chartFlat_iff_fibreExactAt`**: then lane G10MW's `ChartFlat d t F p I`
  (flatness of `(𝒪_d ⧸ I) ⊗ coker F` over `𝒪_d ⧸ I`) holds iff the fibre start `(G(p.1,·), F(p.1,·))` is
  exact at `p.2` (`FibreExactAt`); **`exists_exactStartModAt`**: such starts exist (Noetherianity of
  `𝒪_{d+t}`). Algebra in `HironakaG10LfChartAlgebra`, slice dictionary in `HironakaG10LfChart`.

No named input. BP: hironaka-g10lf-local-flatness.tex.
-/

set_option autoImplicit false

open Set Filter Function
open scoped Topology Matrix TensorProduct

namespace Hironaka.Analytic.Unibranch.HironakaG10TmLocalFlatness

/-- **(1a) Local flatness criterion (Matsumura Th. 22.3, (3) ⇒ (1)), Tor-free.** -/
theorem flat_of_maximalIdeal_rTensor_injective
    {B C M : Type*} [CommRing B] [CommRing C] [IsLocalRing B] [IsLocalRing C]
    [IsNoetherianRing B] [IsNoetherianRing C] [Algebra B C] [IsLocalHom (algebraMap B C)]
    [AddCommGroup M] [Module C M] [Module B M] [IsScalarTower B C M] [Module.Finite C M]
    (h : Function.Injective ((IsLocalRing.maximalIdeal B).subtype.rTensor M)) :
    Module.Flat B M :=
  HironakaG10LfMatsumura.flat_of_maximalIdeal_rTensor_injective (C := C) M h

noncomputable section

open Hironaka Hironaka OkaRelationSheaf OkaGermBridge
  HironakaG10FlatGermChain HironakaG10LocSheafExact HironakaG10LocFibreOpen
  Hironaka.Analytic.Unibranch.HironakaG10SmoothBaseFlatOpen Hironaka.Analytic.Unibranch.HironakaG10LfChart
  Hironaka.Analytic.Unibranch.HironakaG10LfChartAlgebra

local instance (d t : ℕ) :
    Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel d × ComplexModel t)) :=
  (basePullback d t).toAlgebra

/-- `G` is an exact start of `F` modulo `I · 𝒪` at `p`. -/
def ExactStartModAt (d t : ℕ) (I : Ideal (HolGerm (ComplexModel d))) {a b c : ℕ}
    (G : Fin b → Fin c → ComplexModel d × ComplexModel t → ℂ)
    (F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ) (p : ComplexModel d × ComplexModel t) :
    Prop :=
  (∀ i k, ∑ j, germAt p (F i j) * germAt p (G j k) ∈ I.map (basePullback d t)) ∧
  ∀ v : Fin b → HolGerm (ComplexModel d × ComplexModel t),
    (∀ i, ∑ j, germAt p (F i j) * v j ∈ I.map (basePullback d t)) →
      ∃ w : Fin c → HolGerm (ComplexModel d × ComplexModel t),
        ∀ j, v j - ∑ k, germAt p (G j k) * w k ∈ I.map (basePullback d t)

/-- **(1b) Chart-level local flatness criterion over `𝒪_d ⧸ I`, any `I ≤ 𝔪`.** For an exact start
`G` of `F` modulo `I`, flatness of the chart cokernel over `𝒪_d ⧸ I` is exactness of the fibre start
at `p`. -/
theorem chartFlat_iff_fibreExactAt (d t : ℕ) (I : Ideal (HolGerm (ComplexModel d)))
    (hI : I ≤ IsLocalRing.maximalIdeal _) {a b c : ℕ}
    (F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ)
    (G : Fin b → Fin c → ComplexModel d × ComplexModel t → ℂ) (p : ComplexModel d × ComplexModel t)
    (hF : ∀ i j, HolAt (F i j) p) (hG : ∀ j k, HolAt (G j k) p)
    (hstart : ExactStartModAt d t I G F p) :
    HironakaG10MwWindowFamily.ChartFlat d t F p I ↔ FibreExactAt G F p.1 p.2 := by
  have := isNoetherianRing_base d
  have := isNoetherianRing_prod d t
  have : IsLocalHom
      (algebraMap (HolGerm (ComplexModel d)) (HolGerm (ComplexModel d × ComplexModel t))) :=
    isLocalHom_basePullback d t
  have : Module.Flat (HolGerm (ComplexModel d)) (HolGerm (ComplexModel d × ComplexModel t)) :=
    basePullback_flat d t
  have hker : (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d))).map
      (algebraMap (HolGerm (ComplexModel d)) (HolGerm (ComplexModel d × ComplexModel t))) =
      RingHom.ker (sliceHom d t) := (ker_sliceHom d t).symm
  let F' : Matrix (Fin a) (Fin b) (HolGerm (ComplexModel d × ComplexModel t)) :=
    fun i j => germAt p (F i j)
  let G' : Matrix (Fin b) (Fin c) (HolGerm (ComplexModel d × ComplexModel t)) :=
    fun j k => germAt p (G j k)
  refine (flat_quotient_baseChange_coker_iff I hI F' G' (fun i k => hstart.1 i k) hstart.2).trans ?_
  rw [hker]
  refine (sliceExact_iff_matExact (sliceHom d t) (sliceHom_surjective d t) F' G').trans ?_
  have e1 : F'.map (sliceHom d t) = germMat p.2 (fib F p.1) := germ_matrix_map_sliceHom d t F p hF
  have e2 : G'.map (sliceHom d t) = germMat p.2 (fib G p.1) := germ_matrix_map_sliceHom d t G p hG
  rw [e1, e2]
  exact (exact_iff_matExact (holAt_fibMatrix d t F p hF) (holAt_fibMatrix d t G p hG)).symm

/-- **(1b) Exact starts modulo `I` exist** (the relation module modulo `I` is finitely generated). -/
theorem exists_exactStartModAt (d t : ℕ) (I : Ideal (HolGerm (ComplexModel d))) {a b : ℕ}
    (F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ) (p) (hF : ∀ i j, HolAt (F i j) p) :
    ∃ (c : ℕ) (G : Fin b → Fin c → ComplexModel d × ComplexModel t → ℂ),
      (∀ j k, HolAt (G j k) p) ∧ ExactStartModAt d t I G F p := by
  have := isNoetherianRing_prod d t
  let J : Ideal (HolGerm (ComplexModel d × ComplexModel t)) := I.map (basePullback d t)
  let K : Submodule (HolGerm (ComplexModel d × ComplexModel t))
      (Fin b → HolGerm (ComplexModel d × ComplexModel t)) :=
    { carrier := {v | ∀ i, ∑ j, germAt p (F i j) * v j ∈ J}
      add_mem' := by
        intro v w hv hw i
        have h1 : ∑ j, germAt p (F i j) * (v + w) j =
            ∑ j, germAt p (F i j) * v j + ∑ j, germAt p (F i j) * w j := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun j _ => by rw [Pi.add_apply, mul_add]
        show ∑ j, germAt p (F i j) * (v + w) j ∈ J
        rw [h1]
        exact J.add_mem (hv i) (hw i)
      zero_mem' := by
        intro i
        show ∑ j, germAt p (F i j) * (0 : Fin b → HolGerm (ComplexModel d × ComplexModel t)) j ∈ J
        simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]
        exact J.zero_mem
      smul_mem' := by
        intro r v hv i
        have h1 : ∑ j, germAt p (F i j) * (r • v) j = r * ∑ j, germAt p (F i j) * v j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by rw [Pi.smul_apply, smul_eq_mul]; ring
        show ∑ j, germAt p (F i j) * (r • v) j ∈ J
        rw [h1]
        exact J.mul_mem_left r (hv i) }
  obtain ⟨c, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian K)
  choose G hG hGs using fun j k => exists_germAt_eq (s k j) p
  refine ⟨c, G, hG, fun i k => ?_, fun v hv => ?_⟩
  · have hk : s k ∈ K := hs ▸ Submodule.subset_span ⟨k, rfl⟩
    have h1 : ∑ j, germAt p (F i j) * germAt p (G j k) = ∑ j, germAt p (F i j) * s k j :=
      Finset.sum_congr rfl fun j _ => by rw [hGs]
    rw [h1]
    exact hk i
  · have hvK : v ∈ K := hv
    rw [← hs, Submodule.mem_span_range_iff_exists_fun] at hvK
    obtain ⟨w, hw⟩ := hvK
    refine ⟨w, fun j => ?_⟩
    have h1 : v j - ∑ k, germAt p (G j k) * w k = 0 := by
      rw [← hw, sub_eq_zero, Finset.sum_apply]
      exact Finset.sum_congr rfl fun k _ => by rw [Pi.smul_apply, smul_eq_mul, hGs, mul_comm]
    rw [h1]
    exact J.zero_mem

end

end Hironaka.Analytic.Unibranch.HironakaG10TmLocalFlatness
