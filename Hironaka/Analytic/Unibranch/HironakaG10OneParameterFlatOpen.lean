import Hironaka.Analytic.Unibranch.HironakaG10LocEuclideanCartan
import Hironaka.Resolution.HironakaG10OneParameterFlatCriterion

/-!
# Actual stalk flatness is open over one smooth analytic parameter

Every presentation quotient below uses the literal matrix `germMat p F`.
Its base action is restriction through the first-projection germ map, with
local coordinate `t - p.1`. Recentering derives the comparison with the
centred one-parameter criterion. The open-domain holomorphy hypothesis
prevents use of the default zero value of `germAt` outside its domain.
This proves one-parameter stalk-flat openness, not general flattener persistence.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology Matrix

namespace Hironaka.Analytic.Unibranch.HironakaG10OneParameterFlatOpen

noncomputable section

open Hironaka OkaRelationSheaf OkaGermBridge
  HironakaG10FlatResolutionStart HironakaG10FlatPrivilegedNbhd HironakaG10FlatGermChain
  HironakaG10LocFibreOpen HironakaG10OneVariableFlatness
  HironakaG10OneParameterCokernelFlatness HironakaG10OneParameterFlatCriterion

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]

/-- Translation in the actual base parameter, preserving every fibre coordinate. -/
def shift (s : ℂ) : (ℂ × P) ≃ₜ (ℂ × P) where
  toFun p := (s + p.1, p.2)
  invFun p := (-s + p.1, p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  continuous_toFun := (continuous_const.add continuous_fst).prodMk continuous_snd
  continuous_invFun := (continuous_const.add continuous_fst).prodMk continuous_snd

omit [NormedSpace ℂ P] in
@[simp] theorem shift_apply (s : ℂ) (p : ℂ × P) : shift s p = (s + p.1, p.2) := rfl

private theorem differentiable_shift (s : ℂ) (p : ℂ × P) :
    DifferentiableAt ℂ (shift s) p :=
  ((differentiableAt_const s).add differentiableAt_fst).prodMk differentiableAt_snd

private theorem differentiable_shift_symm (s : ℂ) (p : ℂ × P) :
    DifferentiableAt ℂ (shift s).symm p :=
  ((differentiableAt_const (-s)).add differentiableAt_fst).prodMk differentiableAt_snd

/-- The original matrix after translation of its parameter alone. -/
def recenterMatrix {ι κ : Type*} (F : ι → κ → ℂ × P → ℂ) (s : ℂ) :
    ι → κ → ℂ × P → ℂ := fun i j => F i j ∘ shift s

omit [NormedSpace ℂ P] in
private theorem recenterMatrix_add {ι κ : Type*} (F : ι → κ → ℂ × P → ℂ) (s t : ℂ) :
    recenterMatrix (recenterMatrix F s) t = recenterMatrix F (s + t) := by
  funext i j p
  change F i j (s + (t + p.1), p.2) = F i j ((s + t) + p.1, p.2)
  rw [add_assoc]

omit [NormedSpace ℂ P] in
private theorem recenterMatrix_zero {ι κ : Type*} (F : ι → κ → ℂ × P → ℂ) :
    recenterMatrix F 0 = F := by
  funext i j p
  change F i j (0 + p.1, p.2) = F i j p
  simp

variable {a b : ℕ}

/-- Pulling an exact start back by base translation also preserves its fibre start. -/
theorem fibreFlatAt_recenter_apply (F : Fin a → Fin b → ℂ × P → ℂ)
    (s : ℂ) (p : ℂ × P) (h : FibreFlatAt F (shift s p)) :
    FibreFlatAt (recenterMatrix F s) p := by
  obtain ⟨c, G, U, hU, hpU, hstart, hfib⟩ := h
  refine ⟨c, recenterMatrix G s, (shift s) ⁻¹' U,
    hU.preimage (shift s).continuous, hpU,
    exactStartOn_comp_homeomorph (shift s) (differentiable_shift s)
      (differentiable_shift_symm s) hstart, ?_⟩
  have hFibF : HironakaG10LocSheafExact.fib (recenterMatrix F s) p.1 =
      HironakaG10LocSheafExact.fib F (s + p.1) := by
    funext i j z
    rfl
  have hFibG : HironakaG10LocSheafExact.fib (recenterMatrix G s) p.1 =
      HironakaG10LocSheafExact.fib G (s + p.1) := by
    funext i j z
    rfl
  change FibreExactAt G F (s + p.1) p.2 at hfib
  unfold FibreExactAt
  rw [hFibF, hFibG]
  exact hfib

/-- The exact-start condition is unchanged by recentering the parameter at its actual value. -/
theorem fibreFlatAt_recenter_iff (F : Fin a → Fin b → ℂ × P → ℂ) (s : ℂ) (z : P) :
    FibreFlatAt (recenterMatrix F s) ((0 : ℂ), z) ↔ FibreFlatAt F (s, z) := by
  constructor
  · intro h
    have h' := fibreFlatAt_recenter_apply (recenterMatrix F s) (-s) (s, z)
      (by simpa only [shift_apply, neg_add_cancel] using h)
    simpa only [recenterMatrix_add, add_neg_cancel, recenterMatrix_zero] using h'
  · intro h
    exact fibreFlatAt_recenter_apply F s (0, z)
      (by simpa only [shift_apply, add_zero] using h)

/-- The literal image of the original matrix in the actual stalk at `p`. -/
def imageAt (F : Fin a → Fin b → ℂ × P → ℂ) (p : ℂ × P) :
    Submodule (HolGerm (ℂ × P)) (Fin a → HolGerm (ℂ × P)) :=
  LinearMap.range (germMat p F).mulVecLin

/-- The actual stalk presentation quotient. -/
abbrev cokernelAt (F : Fin a → Fin b → ℂ × P → ℂ) (p : ℂ × P) : Type _ :=
  (Fin a → HolGerm (ℂ × P)) ⧸ imageAt F p

/-- The actual first-projection action after identifying both local rings by translation. -/
@[instance_reducible]
def parameterModuleAt (F : Fin a → Fin b → ℂ × P → ℂ) (p : ℂ × P) :
    Module (HolGerm ℂ) (cokernelAt F p) :=
  Module.compHom (cokernelAt F p) (basePullback P)

/-- Actual flatness of the literal stalk quotient over the translated base local ring. -/
def StalkFlatAt (F : Fin a → Fin b → ℂ × P → ℂ) (p : ℂ × P) : Prop :=
  letI : Module (HolGerm ℂ) (cokernelAt F p) := parameterModuleAt F p
  Module.Flat (HolGerm ℂ) (cokernelAt F p)

/-- The action is the pullback of the centred local base coordinate, at every actual point. -/
theorem basePullback_coordinate_at (p : ℂ × P) :
    basePullback P coordinate = germAt p (fun q : ℂ × P => q.1 - p.1) := by
  have hφ : HolAt (fun q : ℂ × P => q.1 - p.1) p :=
    Eventually.of_forall fun _ => differentiableAt_fst.sub (differentiableAt_const p.1)
  rw [basePullback, coordinate, HolGerm.comap_mk, germAt_of_holAt hφ]
  apply HolGerm.mk_eq_mk_iff.mpr
  filter_upwards with q
  simp

private theorem holAt_recenter (F : Fin a → Fin b → ℂ × P → ℂ) (s : ℂ) (z : P)
    (hF : ∀ i j, HolAt (F i j) (s, z)) :
    ∀ i j, HolAt (recenterMatrix F s i j) ((0 : ℂ), z) := by
  intro i j
  have h : HolAt (F i j) (shift s ((0 : ℂ), z)) := by simpa using hF i j
  exact h.comp (shift s).continuous (differentiable_shift s)

/-- Recentering identifies the literal germ matrices, under actual local holomorphy. -/
theorem germMat_recenter (F : Fin a → Fin b → ℂ × P → ℂ) (s : ℂ) (z : P)
    (hF : ∀ i j, HolAt (F i j) (s, z)) :
    germMat ((0 : ℂ), z) (recenterMatrix F s) = germMat (s, z) F := by
  funext i j
  change germAt ((0 : ℂ), z) (recenterMatrix F s i j) = germAt (s, z) (F i j)
  rw [germAt_of_holAt (holAt_recenter F s z hF i j), germAt_of_holAt (hF i j)]
  apply HolGerm.mk_eq_mk_iff.mpr
  filter_upwards with q
  simp only [recenterMatrix, Function.comp_apply, shift_apply, Prod.fst_add, Prod.snd_add,
    zero_add]
  apply congrArg (F i j)
  ext <;> simp

/-- The centred criterion concerns the same quotient and the same first-projection action. -/
theorem flat_recenter_iff_stalkFlatAt (F : Fin a → Fin b → ℂ × P → ℂ) (s : ℂ) (z : P)
    (hF : ∀ i j, HolAt (F i j) (s, z)) :
    letI : Module (HolGerm ℂ) (germCokernel (recenterMatrix F s) z) :=
      parameterModule (recenterMatrix F s) z
    Module.Flat (HolGerm ℂ) (germCokernel (recenterMatrix F s) z) ↔ StalkFlatAt F (s, z) := by
  have hImage : germImage (recenterMatrix F s) z = imageAt F (s, z) := by
    change LinearMap.range (germMat ((0 : ℂ), z) (recenterMatrix F s)).mulVecLin =
      LinearMap.range (germMat (s, z) F).mulVecLin
    rw [germMat_recenter F s z hF]
  let _ : Module (HolGerm ℂ) (germCokernel (recenterMatrix F s) z) :=
    parameterModule (recenterMatrix F s) z
  let _ : Module (HolGerm ℂ) (cokernelAt F (s, z)) := parameterModuleAt F (s, z)
  let eR := Submodule.quotEquivOfEq (germImage (recenterMatrix F s) z) (imageAt F (s, z)) hImage
  let e : germCokernel (recenterMatrix F s) z ≃ₗ[HolGerm ℂ] cokernelAt F (s, z) :=
    { eR.toAddEquiv with
      map_smul' := fun c q => eR.map_smul (basePullback P c) q }
  change Module.Flat (HolGerm ℂ) (germCokernel (recenterMatrix F s) z) ↔
    Module.Flat (HolGerm ℂ) (cokernelAt F (s, z))
  constructor
  · intro h
    let _ := h
    exact Module.Flat.of_linearEquiv e.symm
  · intro h
    let _ := h
    exact Module.Flat.of_linearEquiv e

/-- At every actual point, exact-start flatness is precisely actual module flatness. -/
theorem fibreFlatAt_iff_stalkFlatAt (hX : OkaProperty (ℂ × P))
    (F : Fin a → Fin b → ℂ × P → ℂ) (p : ℂ × P)
    (hF : ∀ i j, HolAt (F i j) p) : FibreFlatAt F p ↔ StalkFlatAt F p := by
  rcases p with ⟨s, z⟩
  have hcentred := fibreFlatAt_iff_flat_germCokernel hX (recenterMatrix F s) z
    (holAt_recenter F s z hF)
  exact (fibreFlatAt_recenter_iff F s z).symm.trans
    (hcentred.trans (flat_recenter_iff_stalkFlatAt F s z hF))

variable {n : ℕ}

/-- The actual module-flat locus of a holomorphic presentation on an open product domain is open. -/
theorem isOpen_stalkFlatLocus (F : Fin a → Fin b → ℂ × EuclideanSpace ℂ (Fin n) → ℂ)
    {U : Set (ℂ × EuclideanSpace ℂ (Fin n))} (hU : IsOpen U)
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) U) :
    IsOpen {p | p ∈ U ∧ StalkFlatAt F p} := by
  have hSet : {p | p ∈ U ∧ StalkFlatAt F p} = U ∩ {p | FibreFlatAt F p} := by
    ext p
    constructor
    · rintro ⟨hp, hflat⟩
      exact ⟨hp, (fibreFlatAt_iff_stalkFlatAt
        (HironakaG10FlatRelationLift.okaProperty_prod_euclidean n) F p
        (fun i j => holAt_of_differentiableOn hU (hF i j) hp)).mpr hflat⟩
    · rintro ⟨hp, hflat⟩
      exact ⟨hp, (fibreFlatAt_iff_stalkFlatAt
        (HironakaG10FlatRelationLift.okaProperty_prod_euclidean n) F p
        (fun i j => holAt_of_differentiableOn hU (hF i j) hp)).mp hflat⟩
  rw [hSet]
  exact hU.inter (HironakaG10LocEuclideanCartan.isOpen_fibreFlatAt F)

/-- Actual stalk flatness persists uniformly on any compact fibre set inside the holomorphic domain. -/
theorem eventually_stalkFlatAt_compact
    (F : Fin a → Fin b → ℂ × EuclideanSpace ℂ (Fin n) → ℂ)
    {U : Set (ℂ × EuclideanSpace ℂ (Fin n))} (hU : IsOpen U)
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) U)
    {K : Set (EuclideanSpace ℂ (Fin n))} (hK : IsCompact K) {s₀ : ℂ}
    (h : ∀ z ∈ K, (s₀, z) ∈ U ∧ StalkFlatAt F (s₀, z)) :
    ∀ᶠ s in 𝓝 s₀, ∀ z ∈ K, (s, z) ∈ U ∧ StalkFlatAt F (s, z) :=
  HironakaG10LocEuclideanCartan.eventually_forall_mem_of_isOpen hK
    (isOpen_stalkFlatLocus F hU hF) h

end

end Hironaka.Analytic.Unibranch.HironakaG10OneParameterFlatOpen
