import DeJongAlterations.Geometry.ProperSteinProjectiveCechShiftedPresentation

/-! # Internal gradings on actual homogeneous syzygy modules

The grading of an actual homogeneous submodule is constructed by restricting
actual homogeneous projections and their actual finite supports. This permits
finite shifted free presentations of actual successive kernels.
-/

/-!
Adapted from the same workspace `BingWangEntropy/HomogeneousSyzygyResolution.lean`,
SHA256 4ff980e56c1ecb2df4f2ec6f7afc7469c1008fa00e2301d6801ab6cfb34c917d.
Only native Mathlib and owned DeJongAlterations modules are imported.
-/

universe u

open DirectSum

namespace DeJongAlterations.Geometry.ProperSteinProjectiveCech

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

section SubmoduleDecomposition

variable {K R M : Type u} [CommRing K] [CommRing R] [Algebra K R]
  [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M]
  (ℳ : ℤ → Submodule K M) [DirectSum.Decomposition ℳ] (p : Submodule R M)

/-- The actual degree piece in an actual homogeneous submodule. -/
def homogeneousSubmodulePiece (d : ℤ) : Submodule K p :=
  (ℳ d).comap (p.subtype.restrictScalars K)

/-- The actual finite-support decomposition of an actual homogeneous submodule element. -/
def homogeneousSubmoduleDecompose (hp : p.IsHomogeneous ℳ) (m : p) :
    ⨁ d, homogeneousSubmodulePiece ℳ p d := by
  classical
  exact DirectSum.mk (fun d => homogeneousSubmodulePiece ℳ p d)
    (DirectSum.decompose ℳ m.val).support
      (fun d => ⟨⟨DirectSum.decompose ℳ m.val d.val, hp d.val m.property⟩,
        (DirectSum.decompose ℳ m.val d.val).property⟩)

/-- The actual induced homogeneous components are the actual ambient homogeneous components. -/
theorem homogeneousSubmoduleDecompose_apply (hp : p.IsHomogeneous ℳ) (m : p) (d : ℤ) :
    ((homogeneousSubmoduleDecompose ℳ p hp m d : p) : M) =
      (DirectSum.decompose ℳ m.val d : M) := by
  classical
  unfold homogeneousSubmoduleDecompose
  by_cases hd : d ∈ (DirectSum.decompose ℳ m.val).support
  · rw [DirectSum.mk_apply_of_mem hd]
  · rw [DirectSum.mk_apply_of_notMem hd, DFinsupp.notMem_support_iff.mp hd]
    rfl

/-- The actual induced finite-support decomposition is a true linear map. -/
def homogeneousSubmoduleDecomposeMap (hp : p.IsHomogeneous ℳ) :
    p →ₗ[K] ⨁ d, homogeneousSubmodulePiece ℳ p d where
  toFun := homogeneousSubmoduleDecompose ℳ p hp
  map_add' m n := by
    apply DFinsupp.ext
    intro d
    apply Subtype.ext
    apply Subtype.ext
    simp only [homogeneousSubmoduleDecompose_apply, DirectSum.add_apply,
      Submodule.coe_add, DirectSum.decompose_add]
  map_smul' r m := by
    apply DFinsupp.ext
    intro d
    apply Subtype.ext
    apply Subtype.ext
    rw [homogeneousSubmoduleDecompose_apply]
    change (DirectSum.decompose ℳ (r • m.val) d : M) =
      r • ((homogeneousSubmoduleDecompose ℳ p hp m d : p) : M)
    rw [homogeneousSubmoduleDecompose_apply, DirectSum.decompose_smul]
    rfl

/-- The genuine inclusion of one actual submodule degree piece into its actual ambient degree. -/
def homogeneousSubmodulePieceInclusion (d : ℤ) :
    homogeneousSubmodulePiece ℳ p d →ₗ[K] ℳ d :=
  (((p.subtype.restrictScalars K).comp
    (homogeneousSubmodulePiece ℳ p d).subtype)).codRestrict _ fun m => m.property

/-- The genuine inclusion of all actual submodule components into actual ambient components. -/
def homogeneousSubmoduleComponentsInclusion :
    (⨁ d, homogeneousSubmodulePiece ℳ p d) →ₗ[K] (⨁ d, ℳ d) :=
  DirectSum.lmap (homogeneousSubmodulePieceInclusion ℳ p)

omit [DirectSum.Decomposition ℳ] in
/-- The true inclusion of submodule components is injective. -/
theorem homogeneousSubmoduleComponentsInclusion_injective :
    Function.Injective (homogeneousSubmoduleComponentsInclusion ℳ p) := by
  intro a b hab
  apply DFinsupp.ext
  intro d
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : ⨁ d, ℳ d => (z d : M)) hab

/-- Restricting the true projections is compatible with their genuine ambient inclusion. -/
theorem homogeneousSubmoduleDecomposeMap_inclusion (hp : p.IsHomogeneous ℳ) (m : p) :
    homogeneousSubmoduleComponentsInclusion ℳ p (homogeneousSubmoduleDecomposeMap ℳ p hp m) =
      DirectSum.decompose ℳ m.val := by
  apply DFinsupp.ext
  intro d
  apply Subtype.ext
  exact homogeneousSubmoduleDecompose_apply ℳ p hp m d

omit [DirectSum.Decomposition ℳ] in
/-- Recombining true submodule components commutes with true ambient inclusion. -/
theorem homogeneousSubmoduleComponentsInclusion_recompose :
    (DirectSum.coeLinearMap ℳ).comp (homogeneousSubmoduleComponentsInclusion ℳ p) =
      (p.subtype.restrictScalars K).comp
        (DirectSum.coeLinearMap (homogeneousSubmodulePiece ℳ p)) := by
  apply DirectSum.linearMap_ext
  intro d
  apply LinearMap.ext
  intro m
  simp only [LinearMap.comp_apply, homogeneousSubmoduleComponentsInclusion,
    DirectSum.lmap_lof, DirectSum.coeLinearMap_lof]
  rfl

/-- Actual homogeneous submodules have genuine internal gradings, derived from actual ambient projections. -/
@[instance_reducible]
def homogeneousSubmoduleDecomposition (hp : p.IsHomogeneous ℳ) :
    DirectSum.Decomposition (homogeneousSubmodulePiece ℳ p) := by
  refine DirectSum.Decomposition.ofLinearMap (homogeneousSubmodulePiece ℳ p)
    (homogeneousSubmoduleDecomposeMap ℳ p hp) ?_ ?_
  · apply LinearMap.ext
    intro m
    apply p.subtype_injective
    have h := LinearMap.congr_fun (homogeneousSubmoduleComponentsInclusion_recompose ℳ p)
      (homogeneousSubmoduleDecomposeMap ℳ p hp m)
    rw [LinearMap.comp_apply, homogeneousSubmoduleDecomposeMap_inclusion] at h
    change (DirectSum.coeLinearMap ℳ) (DirectSum.decompose ℳ m.val) =
      ((DirectSum.coeLinearMap (homogeneousSubmodulePiece ℳ p))
        (homogeneousSubmoduleDecomposeMap ℳ p hp m)).val at h
    change ((DirectSum.coeLinearMap (homogeneousSubmodulePiece ℳ p))
      (homogeneousSubmoduleDecomposeMap ℳ p hp m)).val = m.val
    exact h.symm.trans ((DirectSum.decompose ℳ).left_inv m.val)
  · apply LinearMap.ext
    intro a
    apply homogeneousSubmoduleComponentsInclusion_injective ℳ p
    rw [LinearMap.comp_apply, homogeneousSubmoduleDecomposeMap_inclusion]
    have h := LinearMap.congr_fun (homogeneousSubmoduleComponentsInclusion_recompose ℳ p) a
    change (DirectSum.coeLinearMap ℳ) (homogeneousSubmoduleComponentsInclusion ℳ p a) =
      ((DirectSum.coeLinearMap (homogeneousSubmodulePiece ℳ p)) a).val at h
    rw [← h]
    exact (DirectSum.decompose ℳ).right_inv _

end SubmoduleDecomposition

section GradedSubmodules

variable {K R M : Type u} [CommRing K] [CommRing R] [Algebra K R]
  [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M]
  (𝒜 : ℤ → Submodule K R) (ℳ : ℤ → Submodule K M)
  [SetLike.GradedSMul 𝒜 ℳ] (p : Submodule R M)

/-- True homogeneous multiplication restricts to the actual submodule degree pieces. -/
instance homogeneousSubmoduleGradedSMul :
    SetLike.GradedSMul 𝒜 (homogeneousSubmodulePiece ℳ p) where
  smul_mem := by
    intro d e r m hr hm
    change r • (m : M) ∈ ℳ (d +ᵥ e)
    exact SetLike.GradedSMul.smul_mem hr hm

end GradedSubmodules

section KernelDecomposition

variable {K R M N : Type u} [CommRing K] [CommRing R] [Algebra K R]
  [AddCommGroup M] [AddCommGroup N]
  [Module K M] [Module R M] [IsScalarTower K R M]
  [Module K N] [Module R N] [IsScalarTower K R N]
  (ℳ : ℤ → Submodule K M) (𝒩 : ℤ → Submodule K N)
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩]

/-- The actual kernel of a true homogeneous map has its derived true internal grading. -/
@[instance_reducible]
def actualHomogeneousKernelDecomposition (f : M →ₗ[R] N)
    (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d) :
    DirectSum.Decomposition (homogeneousSubmodulePiece ℳ (LinearMap.ker f)) :=
  homogeneousSubmoduleDecomposition ℳ (LinearMap.ker f)
    (homogeneousMap_kernel ℳ 𝒩 f hf)

omit [Module K N] [IsScalarTower K R N] [DirectSum.Decomposition 𝒩]
  [DirectSum.Decomposition ℳ] in
/-- The literal actual kernel inclusion is a true homogeneous map. -/
theorem actualHomogeneousKernelInclusion_homogeneous (f : M →ₗ[R] N)
    (d : ℤ) (m : LinearMap.ker f)
    (hm : m ∈ homogeneousSubmodulePiece ℳ (LinearMap.ker f) d) :
    (LinearMap.ker f).subtype m ∈ ℳ d := hm

end KernelDecomposition

section FiniteIteration

variable (K R : Type u) [CommRing K] [CommRing R] [Algebra K R]
  (𝒜 : ℤ → Submodule K R) [GradedRing 𝒜]

/-- A finite chain of true shifted free covers of actual successive kernels.
Each next module is literally the kernel of the preceding actual summation map,
with its internally derived grading. -/
def actualFiniteGradedSyzygySteps (n : ℕ) (M : Type u)
    [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M]
    (ℳ : ℤ → Submodule K M) [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ] : Prop := by
  classical
  exact match n with
  | 0 => True
  | n + 1 =>
    ∃ s : Finset M, ∃ δ : s → ℤ, ∃ hg : ∀ i : s, (i : M) ∈ ℳ (δ i),
      Function.Surjective (finiteHomogeneousPresentationMap (R := R) (fun i : s => (i : M))) ∧
      let f := finiteHomogeneousPresentationMap (R := R) (fun i : s => (i : M))
      let ℱ := finiteShiftedFreePiece 𝒜 δ
      let p := LinearMap.ker f
      letI : DirectSum.Decomposition ℱ := finiteShiftedFreeDecomposition 𝒜 δ
      letI := actualHomogeneousKernelDecomposition ℱ ℳ f
        (finiteHomogeneousPresentationMap_homogeneous 𝒜 ℳ δ _ hg)
      actualFiniteGradedSyzygySteps n p (homogeneousSubmodulePiece ℱ p)
  termination_by n

/-- Noetherianness genuinely produces any finite number of actual shifted free syzygy steps. -/
theorem actualFiniteGradedSyzygySteps_exists [IsNoetherianRing R] (n : ℕ) :
    ∀ (M : Type u) [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M]
      (ℳ : ℤ → Submodule K M) [DirectSum.Decomposition ℳ]
      [SetLike.GradedSMul 𝒜 ℳ] [Module.Finite R M],
      actualFiniteGradedSyzygySteps K R 𝒜 n M ℳ := by
  classical
  induction n with
  | zero =>
    intro M _ _ _ _ ℳ _ _ _
    unfold actualFiniteGradedSyzygySteps
    trivial
  | succ n ih =>
    intro M _ _ _ _ ℳ _ _ _
    obtain ⟨s, δ, hg, hs, _⟩ := finiteShiftedGradedPresentation_exists 𝒜 ℳ
    unfold actualFiniteGradedSyzygySteps
    refine ⟨s, δ, hg, hs, ?_⟩
    let f := finiteHomogeneousPresentationMap (R := R) (fun i : s => (i : M))
    let ℱ := finiteShiftedFreePiece 𝒜 δ
    let p := LinearMap.ker f
    let _ : DirectSum.Decomposition ℱ := finiteShiftedFreeDecomposition 𝒜 δ
    let _ := actualHomogeneousKernelDecomposition ℱ ℳ f
      (finiteHomogeneousPresentationMap_homogeneous 𝒜 ℳ δ _ hg)
    exact ih p (homogeneousSubmodulePiece ℱ p)

end FiniteIteration

end

end DeJongAlterations.Geometry.ProperSteinProjectiveCech
