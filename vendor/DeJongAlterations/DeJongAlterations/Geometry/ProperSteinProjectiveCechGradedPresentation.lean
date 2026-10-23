import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.Tactic
import Mathlib.Algebra.Module.GradedModule
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
import Mathlib.Algebra.Exact.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Polynomial.Basic

/-! # Genuine homogeneous presentations and localized exactness

These are algebraic producers for the closed-projective-subscheme section
argument. Finite generators are derived from actual decompositions and
Noetherianness; localized exactness is derived from actual fractions.
-/

/-!
Adapted from the same workspace `BingWangEntropy/GradedSectionPresentation.lean`,
SHA256 5ab45400deb6d3194878591482e94b0832fa305c4f2a88a4d601be09e470b7b5.
Only native Mathlib and the owned DeJongAlterations modules are imported.
-/

universe u v w

open DirectSum

namespace DeJongAlterations.Geometry.ProperSteinProjectiveCech

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

section HomogeneousGenerators

variable {K : Type u} {A : Type v} {M : Type w} {D : Type*}
  [Semiring K] [Semiring A] [AddCommMonoid M] [Module K M] [Module A M]
  [DecidableEq D]
  (ℳ : D → Submodule K M) [DirectSum.Decomposition ℳ]

/-- The actual homogeneous elements of an actual submodule. -/
def homogeneousModuleElements (p : Submodule A M) : Set M :=
  {m | m ∈ p ∧ ∃ d, m ∈ ℳ d}

/-- Homogeneous components of actual elements generate the actual homogeneous submodule. -/
theorem homogeneousModuleElements_span (p : Submodule A M)
    (hp : p.IsHomogeneous ℳ) :
    Submodule.span A (homogeneousModuleElements ℳ p) = p := by
  classical
  apply le_antisymm
  · exact Submodule.span_le.mpr fun _ hm => hm.1
  · intro m hm
    rw [← DirectSum.sum_support_decompose ℳ m]
    exact Submodule.sum_mem _ fun d _ => Submodule.subset_span
      ⟨hp d hm, d, (DirectSum.decompose ℳ m d).property⟩

/-- An actual Noetherian homogeneous submodule has actual finite homogeneous generators. -/
theorem homogeneousModule_finiteGenerators [IsNoetherian A M]
    (p : Submodule A M) (hp : p.IsHomogeneous ℳ) :
    ∃ s : Finset M, (∀ m ∈ s, m ∈ p ∧ ∃ d, m ∈ ℳ d) ∧
      Submodule.span A (s : Set M) = p := by
  classical
  have hs : (Submodule.span A (homogeneousModuleElements ℳ p)).FG :=
    IsNoetherian.noetherian _
  obtain ⟨s, hsub, heq⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset _).mp hs
  exact ⟨s, fun m hm => hsub hm,
    heq.symm.trans (homogeneousModuleElements_span ℳ p hp)⟩

end HomogeneousGenerators

section HomogeneousMaps

variable {K : Type u} {A : Type v} {M N : Type w} {D : Type*}
  [Semiring K] [Ring A] [AddCommGroup M] [AddCommGroup N]
  [Module K M] [Module K N] [Module A M] [Module A N]
  [DecidableEq D]
  (ℳ : D → Submodule K M) (𝒩 : D → Submodule K N)
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩]

/-- An actual degree-preserving map commutes with every actual homogeneous projection. -/
theorem homogeneousMap_decompose (f : M →ₗ[A] N)
    (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d) (d : D) (m : M) :
    f (DirectSum.decompose ℳ m d : M) =
      (DirectSum.decompose 𝒩 (f m) d : N) := by
  classical
  refine DirectSum.Decomposition.inductionOn ℳ
    (motive := fun x => f (DirectSum.decompose ℳ x d : M) =
      (DirectSum.decompose 𝒩 (f x) d : N)) ?_ ?_ ?_ m
  · simp
  · intro i m
    by_cases h : i = d
    · subst i
      rw [DirectSum.decompose_of_mem_same ℳ m.property,
        DirectSum.decompose_of_mem_same 𝒩 (hf d m m.property)]
    · rw [DirectSum.decompose_of_mem_ne ℳ m.property h,
        DirectSum.decompose_of_mem_ne 𝒩 (hf i m m.property) h, map_zero]
  · intro x y hx hy
    simpa only [DirectSum.decompose_add, DirectSum.add_apply,
      Submodule.coe_add, map_add] using congrArg₂ (· + ·) hx hy

/-- Genuine homogeneous maps have genuine homogeneous kernels. -/
theorem homogeneousMap_kernel (f : M →ₗ[A] N)
    (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d) :
    (LinearMap.ker f).IsHomogeneous ℳ := by
  intro d m hm
  change f _ = 0
  rw [homogeneousMap_decompose ℳ 𝒩 f hf,
    LinearMap.mem_ker.mp hm, DirectSum.decompose_zero]
  rfl

/-- Every genuine homogeneous syzygy module in a finite Noetherian source has finite
actual homogeneous generators. -/
theorem homogeneousMap_kernel_finiteGenerators [IsNoetherianRing A] [Module.Finite A M]
    (f : M →ₗ[A] N) (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d) :
    ∃ s : Finset M, (∀ m ∈ s, f m = 0 ∧ ∃ d, m ∈ ℳ d) ∧
      Submodule.span A (s : Set M) = LinearMap.ker f := by
  obtain ⟨s, hs, heq⟩ := homogeneousModule_finiteGenerators ℳ (LinearMap.ker f)
    (homogeneousMap_kernel ℳ 𝒩 f hf)
  exact ⟨s, fun m hm => ⟨LinearMap.mem_ker.mp (hs m hm).1, (hs m hm).2⟩, heq⟩

/-- A surjective actual homogeneous map is surjective in each actual degree. -/
theorem homogeneousMap_surjectiveDegree (f : M →ₗ[A] N)
    (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d) (hs : Function.Surjective f)
    (d : D) (n : N) (hn : n ∈ 𝒩 d) :
    ∃ m : M, m ∈ ℳ d ∧ f m = n := by
  obtain ⟨m, hm⟩ := hs n
  refine ⟨DirectSum.decompose ℳ m d, (DirectSum.decompose ℳ m d).property, ?_⟩
  rw [homogeneousMap_decompose ℳ 𝒩 f hf, hm,
    DirectSum.decompose_of_mem_same 𝒩 hn]

/-- Actual exactness of actual homogeneous maps is exactness in every actual degree. -/
theorem homogeneousMap_exactDegree {P : Type*} [AddCommMonoid P] [Module A P]
    (f : M →ₗ[A] N) (g : N →ₗ[A] P)
    (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d) (h : Function.Exact f g)
    (d : D) (n : N) (hn : n ∈ 𝒩 d) (hz : g n = 0) :
    ∃ m : M, m ∈ ℳ d ∧ f m = n := by
  obtain ⟨m, hm⟩ := (h n).mp hz
  refine ⟨DirectSum.decompose ℳ m d, (DirectSum.decompose ℳ m d).property, ?_⟩
  rw [homogeneousMap_decompose ℳ 𝒩 f hf, hm,
    DirectSum.decompose_of_mem_same 𝒩 hn]

end HomogeneousMaps

section HomogeneousQuotients

variable {K : Type u} {M : Type v} {D : Type*}
  [Ring K] [AddCommGroup M] [Module K M] [DecidableEq D]
  (ℳ : D → Submodule K M) [DirectSum.Decomposition ℳ] (p : Submodule K M)

/-- The actual degree piece in the actual quotient module. -/
def homogeneousQuotientPiece (d : D) : Submodule K (M ⧸ p) :=
  (ℳ d).map p.mkQ

/-- The actual quotient map on an actual homogeneous piece. -/
def homogeneousQuotientPieceMap (d : D) :
    ℳ d →ₗ[K] homogeneousQuotientPiece ℳ p d :=
  (p.mkQ.comp (ℳ d).subtype).codRestrict _ fun m =>
    Submodule.mem_map.mpr ⟨m, m.property, rfl⟩

/-- The actual simultaneous quotient maps on all actual homogeneous components. -/
def homogeneousQuotientComponents :
    M →ₗ[K] ⨁ d, homogeneousQuotientPiece ℳ p d :=
  (DirectSum.lmap (homogeneousQuotientPieceMap ℳ p)).comp
    (DirectSum.decomposeLinearEquiv ℳ).toLinearMap

/-- Genuine homogeneous relations vanish in the genuine quotient decomposition. -/
theorem homogeneousQuotientComponents_kernel (hp : p.IsHomogeneous ℳ) :
    p ≤ LinearMap.ker (homogeneousQuotientComponents ℳ p) := by
  intro m hm
  change homogeneousQuotientComponents ℳ p m = 0
  ext d
  change p.mkQ (DirectSum.decompose ℳ m d : M) = 0
  exact (Submodule.Quotient.mk_eq_zero p).mpr (hp d hm)

/-- Recombining the actual quotient components is the actual quotient map. -/
theorem homogeneousQuotientComponents_recompose :
    (DirectSum.coeLinearMap (homogeneousQuotientPiece ℳ p)).comp
      (homogeneousQuotientComponents ℳ p) = p.mkQ := by
  apply DirectSum.decompose_lhom_ext ℳ
  intro d
  ext m
  change (DirectSum.coeLinearMap (homogeneousQuotientPiece ℳ p))
    ((DirectSum.lmap (homogeneousQuotientPieceMap ℳ p))
      ((DirectSum.decomposeLinearEquiv ℳ) (m : M))) = p.mkQ (m : M)
  rw [DirectSum.decomposeLinearEquiv_apply_coe,
    DirectSum.lmap_lof, DirectSum.coeLinearMap_lof]
  rfl

/-- The actual quotient by actual homogeneous relations has an actual internal grading. -/
def homogeneousQuotientDecomposeMap (hp : p.IsHomogeneous ℳ) :
    (M ⧸ p) →ₗ[K] ⨁ d, homogeneousQuotientPiece ℳ p d := by
  let q : (M ⧸ p) →+ ⨁ d, homogeneousQuotientPiece ℳ p d :=
    QuotientAddGroup.lift p.toAddSubgroup
      (homogeneousQuotientComponents ℳ p).toAddMonoidHom
      (by intro m hm; exact homogeneousQuotientComponents_kernel ℳ p hp hm)
  refine { q with map_smul' := ?_ }
  intro r m
  refine Submodule.Quotient.induction_on p m ?_
  intro m
  change homogeneousQuotientComponents ℳ p (r • m) =
    r • homogeneousQuotientComponents ℳ p m
  exact (homogeneousQuotientComponents ℳ p).map_smul r m

/-- Actual homogeneous quotient components form the actual quotient's internal grading. -/
@[instance_reducible]
def homogeneousQuotientDecomposition (hp : p.IsHomogeneous ℳ) :
    DirectSum.Decomposition (homogeneousQuotientPiece ℳ p) := by
  let f := homogeneousQuotientDecomposeMap ℳ p hp
  refine DirectSum.Decomposition.ofLinearMap (homogeneousQuotientPiece ℳ p) f ?_ ?_
  · apply Submodule.quot_hom_ext
    intro m
    change (DirectSum.coeLinearMap (homogeneousQuotientPiece ℳ p))
      (homogeneousQuotientComponents ℳ p m) = p.mkQ m
    exact DFunLike.congr_fun (homogeneousQuotientComponents_recompose ℳ p) m
  · apply DirectSum.linearMap_ext
    intro d
    apply LinearMap.ext
    intro m
    obtain ⟨x, hx, hm⟩ := Submodule.mem_map.mp m.property
    have he : homogeneousQuotientPieceMap ℳ p d ⟨x, hx⟩ = m :=
      Subtype.ext hm
    rw [← he]
    simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof, LinearMap.id_apply]
    change homogeneousQuotientComponents ℳ p x =
      DirectSum.lof K D (fun d => homogeneousQuotientPiece ℳ p d) d
        (homogeneousQuotientPieceMap ℳ p d ⟨x, hx⟩)
    simp only [homogeneousQuotientComponents, LinearMap.comp_apply,
      LinearEquiv.coe_toLinearMap, DirectSum.decomposeLinearEquiv_apply,
      DirectSum.decompose_of_mem ℳ hx, DirectSum.lmap_of]
    rfl

/-- The actual quotient homogeneous projection is induced by the original actual projection. -/
theorem homogeneousQuotientDecomposition_projection (hp : p.IsHomogeneous ℳ)
    (m : M) (d : D) :
    letI := homogeneousQuotientDecomposition ℳ p hp
    (DirectSum.decompose (homogeneousQuotientPiece ℳ p) (p.mkQ m) d : M ⧸ p) =
      p.mkQ (DirectSum.decompose ℳ m d : M) := by
  rfl

end HomogeneousQuotients

section LocalizedExactness

variable {R : Type u} [CommRing R] (S : Submonoid R)
  {M N P M' N' P' : Type v}
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [AddCommGroup M'] [AddCommGroup N'] [AddCommGroup P']
  [Module R M] [Module R N] [Module R P]
  [Module R M'] [Module R N'] [Module R P']
  (lM : M →ₗ[R] M') (lN : N →ₗ[R] N') (lP : P →ₗ[R] P')
  [IsLocalizedModule S lM] [IsLocalizedModule S lN] [IsLocalizedModule S lP]

/-- Actual localization maps preserve an actual exact sequence, including modules
with localization torsion. -/
theorem localizedModuleMap_exact (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (h : Function.Exact f g) :
    Function.Exact (IsLocalizedModule.map S lM lN f)
      (IsLocalizedModule.map S lN lP g) := by
  intro y
  constructor
  · intro hy
    obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S lN y
    simp only [Function.uncurry_apply_pair] at hy ⊢
    rw [IsLocalizedModule.map_mk'] at hy
    obtain ⟨t, ht⟩ := (IsLocalizedModule.mk'_eq_zero' lP s).mp hy
    obtain ⟨a, ha⟩ := (h (t • b)).mp (by simpa using ht)
    refine ⟨IsLocalizedModule.mk' lM a (t * s), ?_⟩
    rw [IsLocalizedModule.map_mk', ha, IsLocalizedModule.mk'_cancel_left]
  · rintro ⟨x, rfl⟩
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S lM x
    simp only [Function.uncurry_apply_pair]
    rw [IsLocalizedModule.map_mk', IsLocalizedModule.map_mk',
      h.apply_apply_eq_zero, IsLocalizedModule.mk'_zero]

/-- A true kernel inclusion and its true map remain exact after actual localization. -/
theorem localizedModule_kernel_exact (g : N →ₗ[R] P)
    (lKer : LinearMap.ker g →ₗ[R] M') [IsLocalizedModule S lKer] :
    Function.Exact
      (IsLocalizedModule.map S lKer lN (LinearMap.ker g).subtype)
      (IsLocalizedModule.map S lN lP g) :=
  localizedModuleMap_exact S lKer lN lP _ g (LinearMap.exact_subtype_ker_map g)

end LocalizedExactness

end

end DeJongAlterations.Geometry.ProperSteinProjectiveCech
