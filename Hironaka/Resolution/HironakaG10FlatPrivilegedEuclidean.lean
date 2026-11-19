import Hironaka.Resolution.HironakaG10FlatPrivilegedAssembly

/-! # Douady's theorem of privileged neighbourhoods on `ℂⁿ`

Douady 1966, §7 n° 4, **Th. 1**: every point of `ℂⁿ` has a fundamental system of compact polydisc
neighbourhoods privileged for any given finite family of coherent sheaves (here: cokernels of finite
holomorphic matrices, with finite free resolutions whose first matrix is the given one).

* Base case (`Subsingleton X`, i.e. `ℂ⁰`): `kerMat` (a basis of the kernel of a complex matrix),
  `ptChain` (the finite free resolution `0 → ker c → ℂ^b → ℂ^a` of a constant matrix),
  `finiteResolutionOn_ptChain`; `privilegedOn_univ` (every finite free resolution on a point is
  privileged on it: `B(pt) = ℂ`, finite dimension); **`privilegedNbhdsProperty_of_subsingleton`**.
* `closedPolydiscs n`: the compact polydiscs `∏ D̄(c_i, ρ_i)`, `ρ_i > 0`, of `ℂⁿ`;
  `image_snoc_discProd_subset`.
* **`privilegedNbhdsProperty_euclidean`**: `PrivilegedNbhdsProperty (EuclideanSpace ℂ (Fin n))
  (closedPolydiscs n)` for every `n` (induction with
  `HironakaG10FlatPrivilegedAssembly.privilegedNbhdsProperty_prod`, Oka's theorem and Noetherianity
  of `HolGerm ℂⁿ`, transport along `euclideanSnocCLE`).
BP: hironaka-g10-flat-privileged-euclidean.tex. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter Metric
open scoped Topology
namespace Hironaka.HironakaG10FlatPrivilegedEuclidean
noncomputable section
open OkaRelationSheaf HironakaG10FlatResolutionStart HironakaG10FlatPolydiscAlgebra
  HironakaG10FlatPrivilegedNbhd HironakaG10FlatSplitComplex HironakaG10FlatPrivilegedAssembly

/-! ## Linear algebra: a basis of the kernel of a complex matrix -/

section Kernel
variable {a b : ℕ}

/-- The kernel of `c` acting on column vectors. -/
abbrev kerSub (c : Fin a → Fin b → ℂ) : Submodule ℂ (Fin b → ℂ) :=
  LinearMap.ker (Matrix.mulVecLin (Matrix.of c))

/-- Its dimension. -/
def kerDim (c : Fin a → Fin b → ℂ) : ℕ := Module.finrank ℂ (kerSub c)

/-- The matrix whose columns are a basis of `ker c`. -/
def kerMat (c : Fin a → Fin b → ℂ) : Fin b → Fin (kerDim c) → ℂ :=
  fun j l => ((Module.finBasis ℂ (kerSub c) l : kerSub c) : Fin b → ℂ) j

theorem mem_kerSub {c : Fin a → Fin b → ℂ} {v : Fin b → ℂ} :
    v ∈ kerSub c ↔ ∀ i, ∑ j, c i j * v j = 0 := by
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, funext_iff, Pi.zero_apply,
    Matrix.mulVec, dotProduct, Matrix.of_apply]

theorem kerMat_comp (c : Fin a → Fin b → ℂ) (i : Fin a) (l : Fin (kerDim c)) :
    ∑ j, c i j * kerMat c j l = 0 :=
  mem_kerSub.mp (Module.finBasis ℂ (kerSub c) l).2 i

theorem exists_kerMat (c : Fin a → Fin b → ℂ) {v : Fin b → ℂ} (hv : ∀ i, ∑ j, c i j * v j = 0) :
    ∃ u : Fin (kerDim c) → ℂ, ∀ j, v j = ∑ l, kerMat c j l * u l := by
  set B := Module.finBasis ℂ (kerSub c)
  have hw : v ∈ kerSub c := mem_kerSub.mpr hv
  refine ⟨B.repr ⟨v, hw⟩, fun j => ?_⟩
  have h := congrArg (fun w : kerSub c => (w : Fin b → ℂ) j) (B.sum_repr ⟨v, hw⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at h
  rw [← h]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

theorem kerMat_injective (c : Fin a → Fin b → ℂ) {u : Fin (kerDim c) → ℂ}
    (hu : ∀ j, ∑ l, kerMat c j l * u l = 0) : u = 0 := by
  set B := Module.finBasis ℂ (kerSub c)
  have hli : LinearIndependent ℂ fun l => ((B l : kerSub c) : Fin b → ℂ) :=
    B.linearIndependent.map' (kerSub c).subtype (Submodule.ker_subtype _)
  funext l
  refine Fintype.linearIndependent_iff.mp hli u ?_ l
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  rw [← hu j]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

end Kernel

/-! ## The base case: a point -/

section Point
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [Subsingleton X]

theorem apply_eq_of_subsingleton (f : X → ℂ) (x y : X) : f y = f x :=
  congrArg f (Subsingleton.elim y x)

theorem differentiableAt_of_subsingleton (f : X → ℂ) (x : X) : DifferentiableAt ℂ f x := by
  have : f = fun _ => f x := funext fun y => apply_eq_of_subsingleton f x y
  rw [this]
  exact differentiableAt_const _

theorem differentiableOn_of_subsingleton (f : X → ℂ) (U : Set X) : DifferentiableOn ℂ f U :=
  fun x _ => (differentiableAt_of_subsingleton f x).differentiableWithinAt

/-- The ranks `kerDim c, 0, 0, …` beyond the first matrix. -/
def ptRank (n : ℕ) : ℕ → ℕ
  | 0 => n
  | _ + 1 => 0

variable {a b : ℕ}

/-- **The finite free resolution `0 → ker c → ℂ^b → ℂ^a` of a constant matrix** (first matrix `A`,
`c = A(x₀)`). -/
def ptChain (A : Fin a → Fin b → X → ℂ) (x₀ : X) :
    (k : ℕ) → Fin (rankSeq a b (ptRank (kerDim fun i j => A i j x₀)) k) →
      Fin (rankSeq a b (ptRank (kerDim fun i j => A i j x₀)) (k + 1)) → X → ℂ
  | 0 => A
  | 1 => fun j l _ => kerMat (fun i j => A i j x₀) j l
  | _ + 2 => fun _ _ _ => 0

theorem finiteResolutionOn_ptChain (A : Fin a → Fin b → X → ℂ) (x₀ : X) :
    FiniteResolutionOn univ 2 (ptChain A x₀) := by
  set c : Fin a → Fin b → ℂ := fun i j => A i j x₀ with hc
  refine ⟨by omega, rfl, fun k i j => differentiableOn_of_subsingleton _ _, fun k hk => ?_⟩
  match k, hk with
  | 0, _ =>
    show ExactStartOn univ (fun j l (_ : X) => kerMat c j l) A
    refine ⟨fun i j => differentiableOn_of_subsingleton _ _, fun j l => differentiableOn_const _,
      fun i l x _ => ?_, fun y _ v hv => ?_⟩
    · rw [← kerMat_comp c i l]
      exact Finset.sum_congr rfl fun j _ => by rw [apply_eq_of_subsingleton (A i j) x₀ x]
    · obtain ⟨u, hu⟩ := exists_kerMat c (v := fun j => v j y) fun i => by
        have h := (hv.2 i).self_of_nhds
        rw [← h]
        exact Finset.sum_congr rfl fun j _ => by
          rw [apply_eq_of_subsingleton (A i j) x₀ y, mul_comm]
      refine ⟨fun l _ => u l, fun l => holAt_const _ _, fun j => Eventually.of_forall fun x => ?_⟩
      rw [apply_eq_of_subsingleton (v j) y x, hu j]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  | 1, _ =>
    show ExactStartOn univ (fun (_ : Fin (kerDim c)) (_ : Fin 0) (_ : X) => (0 : ℂ))
      (fun j l (_ : X) => kerMat c j l)
    refine ⟨fun j l => differentiableOn_const _, fun j l => differentiableOn_const _,
      fun i l => l.elim0, fun y _ v hv => ?_⟩
    have hu := kerMat_injective c (u := fun l => v l y) fun j => by
      have h := (hv.2 j).self_of_nhds
      rw [← h]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    refine ⟨fun l _ => (0 : ℂ), fun l => holAt_const _ _, fun l => Eventually.of_forall fun x => ?_⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    rw [apply_eq_of_subsingleton (v l) y x]
    exact congrFun hu l

/-- Evaluation `B(univ) → ℂ` at a point. -/
def evPt (x₀ : X) : holSubalgebra (univ : Set X) →ₐ[ℂ] ℂ where
  toFun f := (f : C(univ, ℂ)) ⟨x₀, mem_univ _⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem evPt_injective (x₀ : X) : Function.Injective (evPt x₀) := by
  intro f g h
  refine Subtype.ext (ContinuousMap.ext fun z => ?_)
  have hz : z = ⟨x₀, mem_univ _⟩ := Subsingleton.elim _ _
  rw [hz]
  exact h

theorem evPt_restrict (x₀ : X) {U : Set X} (hU : univ ⊆ U) (F : X → ℂ) (hF : DifferentiableOn ℂ F U) :
    evPt x₀ (restrict univ hU F hF) = F x₀ := rfl

instance finiteDimensional_holSubalgebra_univ [Nonempty X] :
    FiniteDimensional ℂ (holSubalgebra (univ : Set X)) :=
  FiniteDimensional.of_injective (evPt (Classical.arbitrary X)).toLinearMap
    (evPt_injective (Classical.arbitrary X))

/-- **On a point, every finite free resolution is privileged** (`B(pt) = ℂ`, finite dimension). -/
theorem privilegedOn_univ {m : ℕ} {r : ℕ → ℕ} {d : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → X → ℂ}
    (hd : FiniteResolutionOn univ m d) [CompactSpace (univ : Set X)] (x₀ : X) :
    PrivilegedOn univ subset_rfl m d hd.hol := by
  have : Nonempty X := ⟨x₀⟩
  intro k hk
  refine ⟨restrictMatrix_chain_comp hd univ subset_rfl k hk, fun x hx => ?_,
    Submodule.ClosedComplemented.of_finiteDimensional _,
    Submodule.ClosedComplemented.of_finiteDimensional _,
    Submodule.ClosedComplemented.of_finiteDimensional _⟩
  -- the values of `x` form a relation of `d k` at `x₀`
  have hrel : IsRelationAt (d k) x₀ (fun j _ => evPt x₀ (x j)) := by
    refine ⟨fun j => holAt_const _ _, fun i => Eventually.of_forall fun y => ?_⟩
    have h := congrArg (evPt x₀) (congrFun hx i)
    simp only [matrixOperator_apply, map_sum, map_mul, Pi.zero_apply, map_zero] at h
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => by
      show evPt x₀ (x j) * d k i j y = d k i j x₀ * evPt x₀ (x j)
      rw [mul_comm, apply_eq_of_subsingleton (d k i j) x₀ y]
  obtain ⟨c, -, hc⟩ := (hd.exact k hk).exact x₀ (mem_univ _) _ hrel
  refine ⟨fun l => algebraMap ℂ _ (c l x₀), funext fun j => evPt_injective x₀ ?_⟩
  simp only [matrixOperator_apply, map_sum, map_mul, AlgHom.commutes, Algebra.algebraMap_self,
    RingHom.id_apply]
  have h2 : evPt x₀ (x j) = ∑ l, c l x₀ * d (k + 1) j l x₀ := (hc j).self_of_nhds
  rw [h2]
  exact Finset.sum_congr rfl fun l _ => by
    show d (k + 1) j l x₀ * c l x₀ = c l x₀ * d (k + 1) j l x₀
    ring

/-- **Douady's §7 Th. 1 for a point**: the only compact neighbourhood `univ` is privileged. -/
theorem privilegedNbhdsProperty_of_subsingleton : PrivilegedNbhdsProperty X {univ} := by
  intro ι _ a b A x _
  have hcpt : IsCompact (univ : Set X) := (Set.subsingleton_of_subsingleton).isCompact
  have : CompactSpace (univ : Set X) := isCompact_iff_compactSpace.mp hcpt
  refine ⟨univ, fun _ => 2, fun l => ptRank (kerDim fun i j => A l i j x), fun l => ptChain (A l) x,
    fun l => finiteResolutionOn_ptChain (A l) x, isOpen_univ, mem_univ _, fun l => rfl,
    fun N hN => ⟨univ, rfl, ?_, subset_rfl, hcpt, univ_mem, by simp, fun {_} l => ?_⟩⟩
  · intro y _
    rw [Subsingleton.elim y x]
    exact mem_of_mem_nhds hN
  · exact privilegedOn_univ (finiteResolutionOn_ptChain (A l) x) x

end Point

/-! ## `ℂⁿ` -/

section Euclidean

/-- **The compact polydiscs of `ℂⁿ`**: `∏ᵢ D̄(cᵢ, ρᵢ)` with all `ρᵢ > 0`. -/
def closedPolydiscs (n : ℕ) : Set (Set (EuclideanSpace ℂ (Fin n))) :=
  {K | ∃ (c : EuclideanSpace ℂ (Fin n)) (ρ : Fin n → ℝ), (∀ i, 0 < ρ i) ∧
    K = {z | ∀ i, z i ∈ closedBall (c i) (ρ i)}}

theorem univ_mem_closedPolydiscs_zero :
    (univ : Set (EuclideanSpace ℂ (Fin 0))) ∈ closedPolydiscs 0 :=
  ⟨0, fun i => i.elim0, fun i => i.elim0, by ext z; simp⟩

theorem snocCLE_fst_apply (n : ℕ) (z : EuclideanSpace ℂ (Fin (n + 1))) (i : Fin n) :
    (euclideanSnocCLE n z).1 i = z i.castSucc := by
  simp [euclideanSnocCLE]

theorem snocCLE_snd (n : ℕ) (z : EuclideanSpace ℂ (Fin (n + 1))) :
    (euclideanSnocCLE n z).2 = z (Fin.last n) := by
  simp [euclideanSnocCLE]

theorem snocCLE_symm_apply_castSucc (n : ℕ) (q : EuclideanSpace ℂ (Fin n) × ℂ) (i : Fin n) :
    (euclideanSnocCLE n).symm q i.castSucc = q.1 i := by
  simp [euclideanSnocCLE]

theorem snocCLE_symm_apply_last (n : ℕ) (q : EuclideanSpace ℂ (Fin n) × ℂ) :
    (euclideanSnocCLE n).symm q (Fin.last n) = q.2 := by
  simp [euclideanSnocCLE]

/-- Products `K' × D̄(c,ρ)` of polydiscs are polydiscs of `ℂⁿ⁺¹`. -/
theorem image_snoc_discProd_subset (n : ℕ) :
    (fun K => (euclideanSnocCLE n).symm.toHomeomorph '' K) '' discProd (closedPolydiscs n) ⊆
      closedPolydiscs (n + 1) := by
  rintro _ ⟨_, ⟨K', ⟨c', ρ', hρ', rfl⟩, c, ρ, hρ, rfl⟩, rfl⟩
  set L := euclideanSnocCLE n with hL
  refine ⟨L.symm (c', c), Fin.snoc ρ' ρ, fun i => ?_, ?_⟩
  · refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa using hρ
    · simpa using hρ' i
  · ext z
    have hmem : z ∈ L.symm.toHomeomorph '' ({y | ∀ i, y i ∈ closedBall (c' i) (ρ' i)} ×ˢ
        closedBall c ρ) ↔ L z ∈ ({y | ∀ i, y i ∈ closedBall (c' i) (ρ' i)} ×ˢ closedBall c ρ) := by
      constructor
      · rintro ⟨q, hq, rfl⟩
        simpa using hq
      · intro hz
        exact ⟨L z, hz, by simp⟩
    rw [hmem, mem_prod, mem_ofPred_eq, mem_ofPred_eq, Fin.forall_fin_succ']
    simp only [hL, snocCLE_fst_apply, snocCLE_snd, snocCLE_symm_apply_castSucc,
      snocCLE_symm_apply_last, Fin.snoc_castSucc, Fin.snoc_last]

/-- **Douady's theorem of privileged neighbourhoods** (1966, §7 n° 4, Th. 1) on `ℂⁿ`: for every finite
family of matrices `A_l` holomorphic near a point `x` of `ℂⁿ` there are finite free resolutions of the
`coker A_l` with first matrices `A_l` on a common open neighbourhood `U` of `x`, and inside every
neighbourhood of `x` a compact polydisc neighbourhood `K ⊆ U` of `x` (regular closed) privileged for all
of them. -/
theorem privilegedNbhdsProperty_euclidean :
    ∀ n : ℕ, PrivilegedNbhdsProperty (EuclideanSpace ℂ (Fin n)) (closedPolydiscs n)
  | 0 => by
    have : Subsingleton (EuclideanSpace ℂ (Fin 0)) := ⟨fun x y => by ext i; exact i.elim0⟩
    intro ι _ a b A x hA
    exact (privilegedNbhdsProperty_of_subsingleton ι a b A x hA).mono_class
      (by rintro _ rfl; exact univ_mem_closedPolydiscs_zero)
  | n + 1 => by
    have hIH := privilegedNbhdsProperty_euclidean n
    have : IsNoetherianRing (HolGerm (EuclideanSpace ℂ (Fin (n + 1)))) :=
      isNoetherianRing_holGerm_euclidean (n + 1)
    have : IsNoetherianRing (HolGerm (EuclideanSpace ℂ (Fin n) × ℂ)) :=
      isNoetherianRing_of_ringEquiv _ (HolGerm.comapEquiv (euclideanSnocCLE n)).symm
    have hprod := privilegedNbhdsProperty_prod
      (OkaCoherence.okaProperty_prod (OkaCoherence.okaProperty_euclidean n)) hIH
    set L := euclideanSnocCLE n
    intro ι _ a b A x hA
    have hB : ∀ l i j, HolAt (A l i j ∘ L.symm.toHomeomorph) (L x) := fun l i j => by
      have h1 : HolAt (A l i j) (L.symm.toHomeomorph (L x)) := by simpa using hA l i j
      exact h1.comp L.symm.toHomeomorph.continuous fun _ => L.symm.differentiableAt
    have h := hasPrivilegedNbhds_of_comp_homeomorph L.symm.toHomeomorph
      (fun _ => L.symm.differentiableAt) (fun _ => L.differentiableAt) (hprod ι a b _ (L x) hB)
    have hx : L.symm.toHomeomorph (L x) = x := L.symm_apply_apply x
    rw [hx] at h
    exact h.mono_class (image_snoc_discProd_subset n)

end Euclidean

end
end Hironaka.HironakaG10FlatPrivilegedEuclidean
