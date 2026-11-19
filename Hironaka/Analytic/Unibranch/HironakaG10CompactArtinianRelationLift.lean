import Hironaka.Analytic.Unibranch.HironakaG10ArtinianHolomorphicMatrix
import Hironaka.Analytic.GAGA.CoreCTheoremB
import Hironaka.Analytic.Unibranch.HironakaG10CartanBoxBridge
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.StdBasis

/-!
# Actual local and compact holomorphic lifting of parameter-valued relations

Whole tensor germs have actual holomorphic representatives.  A flat actual
germ cokernel then lifts scalar residue relations to holomorphic parameter
relations.  The compact construction uses the actual finite complex block
matrix, with no supplied encoding or solution certificate.
-/

set_option autoImplicit false

open Filter Set Metric
open scoped Topology TensorProduct

namespace Hironaka.Analytic.Unibranch.HironakaG10CompactArtinianRelationLift

open Hironaka OkaRelationSheaf OkaGermBridge
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianRelationLift
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianHolomorphicMatrix
  Hironaka.Analytic.Unibranch.HironakaG10FlatRelationLift

noncomputable section

variable {Q X : Type*} {ι : Type} [NormedCommRing Q] [NormedAlgebra ℂ Q]
  [FiniteDimensional ℂ Q] [NormedAddCommGroup X] [NormedSpace ℂ X]
  [Fintype ι] [DecidableEq ι]

local instance : Algebra ℂ (HolGerm X) :=
  (HolGerm.constHom : ℂ →+* HolGerm X).toAlgebra

omit [FiniteDimensional ℂ Q] in
/-- Every whole tensor germ is represented by an actual parameter-valued
holomorphic function at the same original point. -/
theorem exists_tensorGermAt_eq (b : Module.Basis ι ℂ Q) (z : X)
    (s : Q ⊗[ℂ] HolGerm X) :
    ∃ g : X → Q, (∀ᶠ x in 𝓝 z, DifferentiableAt ℂ g x) ∧ tensorGermAt b z g = s := by
  choose f hf hfeq using fun i => exists_germAt_eq (parameterTensorEquiv b s i) z
  let g : X → Q := fun x => ∑ i, f i x • b i
  refine ⟨g, ?_, ?_⟩
  · filter_upwards [eventually_all.mpr hf] with x hx
    exact DifferentiableAt.fun_sum fun i _ => (hx i).smul_const _
  · apply (parameterTensorEquiv b).injective
    apply funext
    intro i
    rw [tensorGermAt_coordinate]
    have hcoord : (fun x => b.coord i (g x)) = f i := by
      funext x
      simp [g, map_sum, map_smul, Module.Basis.coord_apply, Finsupp.single_apply]
    rw [hcoord, hfeq]

section FiniteProducts

variable {A M k : Type*} [CommRing A] [AddCommGroup M] [Module A M]
  [Fintype k] [DecidableEq k]

/-- Ideal multiples on finite product modules are exactly the
coordinatewise ideal multiples. -/
theorem mem_ideal_smul_pi_iff (I : Ideal A) (v : k → M) :
    v ∈ I • (⊤ : Submodule A (k → M)) ↔ ∀ j, v j ∈ I • (⊤ : Submodule A M) := by
  constructor
  · intro hv j
    have hle : (I • (⊤ : Submodule A (k → M))).map (LinearMap.proj j) ≤
        I • (⊤ : Submodule A M) := by
      rw [Submodule.map_smul'', Submodule.map_top]
      exact smul_mono_right I le_top
    exact hle (Submodule.mem_map_of_mem hv)
  · intro hv
    have hsingle (j : k) : Pi.single j (v j) ∈ I • (⊤ : Submodule A (k → M)) := by
      have hle : (I • (⊤ : Submodule A M)).map (LinearMap.single A (fun _ : k => M) j) ≤
          I • (⊤ : Submodule A (k → M)) := by
        rw [Submodule.map_smul'', Submodule.map_top]
        exact smul_mono_right I le_top
      exact hle (Submodule.mem_map_of_mem (hv j))
    have hsum : (∑ j : k, Pi.single j (v j)) ∈ I • (⊤ : Submodule A (k → M)) :=
      (I • (⊤ : Submodule A (k → M))).sum_mem (fun j _ => hsingle j)
    simpa only [Finset.univ_sum_single] using hsum

end FiniteProducts

variable {a k : Type} [Fintype a] [Fintype k] [DecidableEq a] [DecidableEq k]

/-- The actual whole tensor-germ presentation map, with its genuine
parameter-algebra action. -/
def matrixGermMap (b : Module.Basis ι ℂ Q) (z : X) (F : a → k → X → Q) :
    (k → Q ⊗[ℂ] HolGerm X) →ₗ[Q] (a → Q ⊗[ℂ] HolGerm X) :=
  (Matrix.mulVecLin (fun i j => tensorGermAt b z (F i j))).restrictScalars Q

omit [FiniteDimensional ℂ Q] [DecidableEq ι] [Fintype a] [DecidableEq a] [DecidableEq k] in
theorem matrixGermMap_apply (b : Module.Basis ι ℂ Q) (z : X) (F : a → k → X → Q)
    (v : k → Q ⊗[ℂ] HolGerm X) (i : a) :
    matrixGermMap b z F v i = ∑ j, tensorGermAt b z (F i j) * v j :=
  rfl

omit [Fintype ι] [DecidableEq ι] [Fintype a] [Fintype k] [DecidableEq a] [DecidableEq k] in
theorem holomorphic_residue (ε : Q →ₐ[ℂ] ℂ) {f : X → Q} {z : X}
    (hf : ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ f x) : HolAt (fun x => ε (f x)) z := by
  filter_upwards [hf] with x hx
  exact ε.toLinearMap.toContinuousLinearMap.differentiableAt.comp x hx

/-- A genuine flat tensor-germ cokernel lifts an actual holomorphic
residue relation to an actual local holomorphic relation. -/
theorem exists_local_relation_lift (b : Module.Basis ι ℂ Q) (ε : Q →ₐ[ℂ] ℂ)
    {z : X} (F : a → k → X → Q) (g₀ : k → X → ℂ)
    (hF : ∀ i j, ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ (F i j) x)
    (hg₀ : ∀ j, HolAt (g₀ j) z)
    (hrel : ∀ i, ∀ᶠ x in 𝓝 z, ∑ j, ε (F i j x) * g₀ j x = 0)
    (hflat : Module.Flat Q ((a → Q ⊗[ℂ] HolGerm X) ⧸
      LinearMap.range (matrixGermMap b z F))) :
    ∃ g : k → X → Q,
      (∀ j, ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ (g j) x) ∧
      (∀ i, ∀ᶠ x in 𝓝 z, ∑ j, F i j x * g j x = 0) ∧
      ∀ j, ∀ᶠ x in 𝓝 z, ε (g j x) = g₀ j x := by
  let p : k → Q ⊗[ℂ] HolGerm X := fun j => (1 : Q) ⊗ₜ[ℂ] germAt z (g₀ j)
  let u : k → X → Q := fun j x => g₀ j x • (1 : Q)
  have hu (j : k) : ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ (u j) x :=
    (hg₀ j).mono fun _ hx => hx.smul_const _
  have hp (i : a) : residueTensor ε (matrixGermMap b z F p i) = 0 := by
    have hrow : matrixGermMap b z F p i =
        tensorGermAt b z (fun x => ∑ j, F i j x * u j x) := by
      rw [matrixGermMap_apply]
      calc
        (∑ j, tensorGermAt b z (F i j) * p j) =
            ∑ j, tensorGermAt b z (F i j) * tensorGermAt b z (u j) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [show tensorGermAt b z (u j) = p j from tensorGermAt_smul_const b (hg₀ j) 1]
        _ = _ := (matrix_tensorGermAt_mul b (G := fun j (_ : Unit) => u j)
          hF (fun j _ => hu j) i ()).symm
    have hhol : ∀ᶠ x in 𝓝 z,
        DifferentiableAt ℂ (fun x => ∑ j, F i j x * u j x) x := by
      filter_upwards [eventually_all.mpr (hF i), eventually_all.mpr hu] with x hxF hxu
      exact DifferentiableAt.fun_sum fun j _ => (hxF j).mul (hxu j)
    rw [hrow, residueTensor_tensorGermAt b ε hhol]
    apply (germAt_eq_zero_iff (holomorphic_residue ε hhol)).mpr
    filter_upwards [hrel i] with x hx
    simpa [u, map_sum, map_mul, map_smul, mul_comm] using hx
  let : Module.Flat Q ((a → Q ⊗[ℂ] HolGerm X) ⧸
      LinearMap.range (matrixGermMap b z F)) := hflat
  let : Module.Free ℂ (HolGerm X) :=
    Module.Free.of_basis (Module.Basis.ofVectorSpace ℂ (HolGerm X))
  let : Module.Free Q (Q ⊗[ℂ] HolGerm X) :=
    Algebra.TensorProduct.instFree ℂ Q (HolGerm X)
  let : Module.Free Q (a → Q ⊗[ℂ] HolGerm X) :=
    Module.Free.function (R := Q) (M := Q ⊗[ℂ] HolGerm X) (ι := a)
  let : Module.Flat Q (a → Q ⊗[ℂ] HolGerm X) := Module.Flat.of_free
  obtain ⟨v, hv, hvmod⟩ := exists_relation_lift_mod_of_flat (matrixGermMap b z F)
    (RingHom.ker ε.toRingHom) p ((mem_ideal_smul_pi_iff _ _).mpr fun i =>
      (residueTensor_eq_zero_iff_mem_ideal_smul ε _).mp (hp i))
  have hvzero : matrixGermMap b z F v = 0 := hv
  choose g hg hgv using fun j => exists_tensorGermAt_eq b z (v j)
  refine ⟨g, hg, ?_, ?_⟩
  · intro i
    have hhol : ∀ᶠ x in 𝓝 z,
        DifferentiableAt ℂ (fun x => ∑ j, F i j x * g j x) x := by
      filter_upwards [eventually_all.mpr (hF i), eventually_all.mpr hg] with x hxF hxg
      exact DifferentiableAt.fun_sum fun j _ => (hxF j).mul (hxg j)
    apply (tensorGermAt_eq_zero_iff b hhol).mp
    rw [matrix_tensorGermAt_mul b (G := fun j (_ : Unit) => g j) hF (fun j _ => hg j) i ()]
    simp_rw [hgv]
    exact congrFun hvzero i
  · intro j
    apply (germAt_eq_germAt_iff (holomorphic_residue ε (hg j)) (hg₀ j)).mp
    rw [← residueTensor_tensorGermAt b ε (hg j), hgv]
    have hmod := (mem_ideal_smul_pi_iff (RingHom.ker ε.toRingHom) (p - v)).mp hvmod j
    have hz := (residueTensor_eq_zero_iff_mem_ideal_smul ε (p j - v j)).mpr hmod
    rw [map_sub, sub_eq_zero] at hz
    simpa only [p, residueTensor_tmul, map_one, one_smul] using hz.symm

/-- Reconstruct a parameter-valued column from its finite complex
coefficients. -/
def reconstructColumn (b : Module.Basis ι ℂ Q) (c : k × ι → ℂ) : k → Q :=
  fun j => ∑ l, c (j, l) • b l

/-- The actual finite complex linear system imposing both the original
matrix relation and its prescribed residue. -/
def relationSystemMatrix (b : Module.Basis ι ℂ Q) (ε : Q →ₐ[ℂ] ℂ)
    (F : a → k → X → Q) : ((a × ι) ⊕ k) → (k × ι) → X → ℂ
  | Sum.inl p, q => complexBlockMatrix b F p q
  | Sum.inr j, q => fun _ => if j = q.1 then ε (b q.2) else 0

def relationSystemTarget (g₀ : k → X → ℂ) : ((a × ι) ⊕ k) → X → ℂ
  | Sum.inl _ => fun _ => 0
  | Sum.inr j => g₀ j

omit [FiniteDimensional ℂ Q] [NormedAddCommGroup X] [NormedSpace ℂ X]
  [DecidableEq ι] [Fintype a] [DecidableEq a] in
theorem relationSystemMatrix_top_apply (b : Module.Basis ι ℂ Q) (ε : Q →ₐ[ℂ] ℂ)
    (F : a → k → X → Q) (x : X) (c : k × ι → ℂ) (i : a) (r : ι) :
    (∑ q, relationSystemMatrix b ε F (Sum.inl (i, r)) q x * c q) =
      b.coord r (∑ j, F i j x * reconstructColumn b c j) := by
  simp only [relationSystemMatrix, Fintype.sum_prod_type, complexBlockMatrix,
    reconstructColumn, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  exact mul_comm _ _

omit [NormedAddCommGroup X] [NormedSpace ℂ X] [DecidableEq ι] [Fintype a] [DecidableEq a] in
theorem relationSystemMatrix_bottom_apply (b : Module.Basis ι ℂ Q) (ε : Q →ₐ[ℂ] ℂ)
    (F : a → k → X → Q) (x : X) (c : k × ι → ℂ) (j : k) :
    (∑ q, relationSystemMatrix b ε F (Sum.inr j) q x * c q) =
      ε (reconstructColumn b c j) := by
  simp [relationSystemMatrix, Fintype.sum_prod_type, reconstructColumn, map_sum,
    map_smul, smul_eq_mul, mul_comm]

omit [FiniteDimensional ℂ Q] [NormedAddCommGroup X] [NormedSpace ℂ X]
  [DecidableEq ι] [Fintype a] [DecidableEq a] [Fintype k] [DecidableEq k] in
theorem reconstructColumn_coordinates (b : Module.Basis ι ℂ Q) (v : k → Q) :
    reconstructColumn b (fun q => b.coord q.2 (v q.1)) = v := by
  funext j
  exact b.sum_repr (v j)

section Cartan

open Hironaka.Analytic.GAGA.Core Hironaka.Analytic.GAGA.Core.GermModule Hironaka.Analytic.GAGA.Core.Box Hironaka.Analytic.GAGA.Core.TheoremB

private theorem isOpen_combination_locus {n : ℕ} {r s : Type} [Fintype r] [Fintype s]
    {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U)
    (σ : s → r → EuclideanSpace ℂ (Fin n) → ℂ)
    (v : r → EuclideanSpace ℂ (Fin n) → ℂ) :
    IsOpen {z | z ∈ U ∧ IsCombinationAt σ z v} := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨hzU, c, hc, hcv⟩
  have hev : ∀ᶠ x in 𝓝 z, x ∈ U ∧
      (∀ j, DifferentiableAt ℂ (c j) x) ∧
      ∀ i, v i x = ∑ j, c j x * σ j i x :=
    (show ∀ᶠ x in 𝓝 z, x ∈ U from hU.mem_nhds hzU).and
      ((eventually_all.mpr hc).and (eventually_all.mpr hcv))
  obtain ⟨V, hV, hVo, hzV⟩ := _root_.eventually_nhds_iff.mp hev
  refine Filter.mem_of_superset (hVo.mem_nhds hzV) fun y hy => ⟨(hV y hy).1, c, ?_, ?_⟩
  · intro j
    filter_upwards [hVo.mem_nhds hy] with x hx
    exact (hV x hx).2.1 j
  · intro i
    filter_upwards [hVo.mem_nhds hy] with x hx
    exact (hV x hx).2.2 i

/-- Cartan division globalizes local solutions of an actual finite
holomorphic complex linear system near a compact convex product set. -/
private theorem exists_box_linear_solution {n : ℕ} {r s : Type} [Fintype r] [Fintype s]
    (C : Fin n → Set ℂ) (hC : IsBox C)
    {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U) (hKU : boxSet C ⊆ U)
    (σ : s → r → EuclideanSpace ℂ (Fin n) → ℂ)
    (hσ : ∀ j i, DifferentiableOn ℂ (σ j i) U)
    (v : r → EuclideanSpace ℂ (Fin n) → ℂ)
    (hloc : ∀ z ∈ boxSet C, IsCombinationAt σ z v) :
    ∃ V, IsOpen V ∧ boxSet C ⊆ V ∧ V ⊆ U ∧
      ∃ c : s → EuclideanSpace ℂ (Fin n) → ℂ,
        (∀ j, DifferentiableOn ℂ (c j) V) ∧
        ∀ x ∈ V, ∀ i, v i x = ∑ j, c j x * σ j i x := by
  let W := {z | z ∈ U ∧ IsCombinationAt σ z v}
  have hW : IsOpen W := isOpen_combination_locus hU σ v
  have hKW : boxSet C ⊆ W := fun z hz => ⟨hKU hz, hloc z hz⟩
  have hdiv := division_box hC hU hKU (span_isCoherentOn hU hσ)
  obtain ⟨V, hVo, hKV, c, hc, hcv⟩ := hdiv.of_section hU hW hKU hKW
    (span_generatedOn hσ) (fun _ hz => hz.2)
  refine ⟨V ∩ U, hVo.inter hU, subset_inter hKV hKU, inter_subset_right, c,
    fun j => (hc j).mono inter_subset_left, fun x hx i => hcv x hx.1 i⟩

private theorem exists_box_relation_lift {n : ℕ}
    (b : Module.Basis ι ℂ Q) (ε : Q →ₐ[ℂ] ℂ) (C : Fin n → Set ℂ) (hC : IsBox C)
    {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U) (hKU : boxSet C ⊆ U)
    (F : a → k → EuclideanSpace ℂ (Fin n) → Q)
    (g₀ : k → EuclideanSpace ℂ (Fin n) → ℂ)
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) U)
    (hg₀ : ∀ j, DifferentiableOn ℂ (g₀ j) U)
    (hrel : ∀ z ∈ boxSet C, ∀ i, ∀ᶠ x in 𝓝 z, ∑ j, ε (F i j x) * g₀ j x = 0)
    (hflat : ∀ z ∈ boxSet C, Module.Flat Q
      ((a → Q ⊗[ℂ] HolGerm (EuclideanSpace ℂ (Fin n))) ⧸
        LinearMap.range (matrixGermMap b z F))) :
    ∃ V, IsOpen V ∧ boxSet C ⊆ V ∧ V ⊆ U ∧
      ∃ g : k → EuclideanSpace ℂ (Fin n) → Q,
        (∀ j, DifferentiableOn ℂ (g j) V) ∧
        (∀ x ∈ V, ∀ i, ∑ j, F i j x * g j x = 0) ∧
        ∀ x ∈ V, ∀ j, ε (g j x) = g₀ j x := by
  have hFat (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U) (i : a) (j : k) :
      ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ (F i j) x :=
    (show ∀ᶠ x in 𝓝 z, x ∈ U from hU.mem_nhds hz).mono
      fun x hx => (hF i j).differentiableAt (hU.mem_nhds hx)
  let σ : (k × ι) → ((a × ι) ⊕ k) → EuclideanSpace ℂ (Fin n) → ℂ :=
    fun q p => relationSystemMatrix b ε F p q
  have hσ : ∀ q p, DifferentiableOn ℂ (σ q p) U := by
    intro q p
    cases p with
    | inl p =>
      intro x hx
      exact (holomorphic_complexBlockMatrix b (hFat x hx) p q).self_of_nhds.differentiableWithinAt
    | inr j => exact differentiableOn_const _
  have hloc : ∀ z ∈ boxSet C, IsCombinationAt σ z (relationSystemTarget g₀) := by
    intro z hz
    obtain ⟨g, hg, hFg, hεg⟩ := exists_local_relation_lift b ε F g₀
      (hFat z (hKU hz)) (fun j => holAt_of_differentiableOn hU (hg₀ j) (hKU hz))
      (hrel z hz) (hflat z hz)
    refine ⟨fun q x => b.coord q.2 (g q.1 x),
      fun q => holomorphic_coordinate b q.2 (hg q.1), ?_⟩
    intro p
    cases p with
    | inl p =>
      filter_upwards [hFg p.1] with x hx
      have hm := relationSystemMatrix_top_apply b ε F x
        (fun q => b.coord q.2 (g q.1 x)) p.1 p.2
      rw [reconstructColumn_coordinates b (fun j => g j x)] at hm
      have hm0 : ∑ q, relationSystemMatrix b ε F (Sum.inl p) q x *
          b.coord q.2 (g q.1 x) = 0 := by simpa only [hx, map_zero] using hm
      simpa only [σ, relationSystemTarget, mul_comm] using hm0.symm
    | inr j =>
      filter_upwards [hεg j] with x hx
      have hm := relationSystemMatrix_bottom_apply b ε F x
        (fun q => b.coord q.2 (g q.1 x)) j
      rw [reconstructColumn_coordinates b (fun j => g j x), hx] at hm
      simpa only [σ, relationSystemTarget, mul_comm] using hm.symm
  obtain ⟨V, hVo, hKV, hVU, c, hc, hcv⟩ :=
    exists_box_linear_solution C hC hU hKU σ hσ (relationSystemTarget g₀) hloc
  let g : k → EuclideanSpace ℂ (Fin n) → Q :=
    fun j x => reconstructColumn b (fun q => c q x) j
  refine ⟨V, hVo, hKV, hVU, g, ?_, ?_, ?_⟩
  · intro j x hx
    exact DifferentiableWithinAt.fun_sum fun l _ => (hc (j, l) x hx).smul_const _
  · intro x hx i
    apply b.repr.injective
    apply Finsupp.ext
    intro r
    have hsys : ∑ q, relationSystemMatrix b ε F (Sum.inl (i, r)) q x * c q x = 0 := by
      simpa only [σ, relationSystemTarget, mul_comm] using (hcv x hx (Sum.inl (i, r))).symm
    rw [relationSystemMatrix_top_apply] at hsys
    simpa only [g, Module.Basis.coord_apply, map_zero, Finsupp.zero_apply] using hsys
  · intro x hx j
    change ε (reconstructColumn b (fun q => c q x) j) = g₀ j x
    rw [← relationSystemMatrix_bottom_apply b ε F x (fun q => c q x) j]
    simpa only [σ, relationSystemTarget, mul_comm] using (hcv x hx (Sum.inr j)).symm

/-- Actual flatness of the germ cokernel at every point of a closed
polydisc lifts finitely many holomorphic residue-relation columns on one
open neighborhood of that same compact set. -/
theorem exists_compact_relation_lift {n : ℕ} {c : Type} [Fintype c]
    (b : Module.Basis ι ℂ Q) (ε : Q →ₐ[ℂ] ℂ)
    {K U : Set (EuclideanSpace ℂ (Fin n))}
    (hK : K ∈ HironakaG10FlatPrivilegedEuclidean.closedPolydiscs n)
    (hU : IsOpen U) (hKU : K ⊆ U)
    (F : a → k → EuclideanSpace ℂ (Fin n) → Q)
    (G₀ : k → c → EuclideanSpace ℂ (Fin n) → ℂ)
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) U)
    (hG₀ : ∀ j l, DifferentiableOn ℂ (G₀ j l) U)
    (hrel : ∀ z ∈ K, ∀ i l, ∀ᶠ x in 𝓝 z, ∑ j, ε (F i j x) * G₀ j l x = 0)
    (hflat : ∀ z ∈ K, Module.Flat Q
      ((a → Q ⊗[ℂ] HolGerm (EuclideanSpace ℂ (Fin n))) ⧸
        LinearMap.range (matrixGermMap b z F))) :
    ∃ V, IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧
      ∃ G : k → c → EuclideanSpace ℂ (Fin n) → Q,
        (∀ j l, DifferentiableOn ℂ (G j l) V) ∧
        (∀ x ∈ V, ∀ i l, ∑ j, F i j x * G j l x = 0) ∧
        ∀ x ∈ V, ∀ j l, ε (G j l x) = G₀ j l x := by
  obtain ⟨center, ρ, _hρ, rfl⟩ := hK
  let C : Fin n → Set ℂ := fun i => closedBall (center i) (ρ i)
  have hC : IsBox C := ⟨fun i => isCompact_closedBall (center i) (ρ i),
    fun i => convex_closedBall (center i) (ρ i)⟩
  have hcol (l : c) := exists_box_relation_lift b ε C hC hU hKU F
    (fun j => G₀ j l) hF (fun j => hG₀ j l) (fun z hz i => hrel z hz i l) hflat
  choose V hVo hKV hVU G hG hFG hεG using hcol
  let W := U ∩ ⋂ l, V l
  have hWV (l : c) : W ⊆ V l := fun _ hx => mem_iInter.mp hx.2 l
  refine ⟨W, hU.inter (isOpen_iInter_of_finite hVo), ?_, inter_subset_left,
    fun j l => G l j, fun j l => (hG l j).mono (hWV l), ?_, ?_⟩
  · intro x hx
    exact ⟨hKU hx, mem_iInter.mpr fun l => hKV l hx⟩
  · intro x hx i l
    exact hFG l x (hWV l hx) i
  · intro x hx j l
    exact hεG l x (hWV l hx) j

end Cartan

end

end Hironaka.Analytic.Unibranch.HironakaG10CompactArtinianRelationLift
