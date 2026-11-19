import Hironaka.Analytic.Unibranch.HironakaG10LfGradedFlat

/-!
# Flatness of `Bᵃ ⧸ N` from its cyclic pieces (lane G10LF, ALG-2 of lane G10GN's route N)

For a submodule `N ⊆ Bᵃ` and `i < a`, `cyclicIdeal N i` is the ideal of `i`-th coordinates of the elements of
`N` vanishing in the coordinates `> i`. The quotient `Bᵃ ⧸ N` is filtered by the classes `Fₖ` of the vectors
supported in the coordinates `< k`, with `Fₖ₊₁ ⧸ Fₖ ≅ B ⧸ cyclicIdeal N k`; hence
**`flat_quotient_of_flat_cyclicIdeal`**: if every `B ⧸ cyclicIdeal N i` is flat over `R` (`B` an `R`-algebra),
so is `Bᵃ ⧸ N`.

No named input. BP: hironaka-g10lf-generic-freeness.tex.
-/

set_option autoImplicit false

open Function

namespace Hironaka.Analytic.Unibranch.HironakaG10LfCyclicFlat

variable {B : Type*} [CommRing B]

/-- `{v i | v ∈ N, v l = 0 for l > i}`. -/
def cyclicIdeal {a : ℕ} (N : Submodule B (Fin a → B)) (i : Fin a) : Ideal B where
  carrier := {f | ∃ v ∈ N, v i = f ∧ ∀ l, i < l → v l = 0}
  add_mem' := by
    rintro _ _ ⟨v, hv, rfl, hv'⟩ ⟨w, hw, rfl, hw'⟩
    exact ⟨v + w, N.add_mem hv hw, rfl, fun l hl => by rw [Pi.add_apply, hv' l hl, hw' l hl, add_zero]⟩
  zero_mem' := ⟨0, N.zero_mem, rfl, fun _ _ => rfl⟩
  smul_mem' := by
    rintro c _ ⟨v, hv, rfl, hv'⟩
    exact ⟨c • v, N.smul_mem c hv, rfl, fun l hl => by rw [Pi.smul_apply, hv' l hl, smul_zero]⟩

theorem mem_cyclicIdeal {a : ℕ} (N : Submodule B (Fin a → B)) (i : Fin a) (f : B) :
    f ∈ cyclicIdeal N i ↔ ∃ v ∈ N, v i = f ∧ ∀ l, i < l → v l = 0 := Iff.rfl

variable (B) in
/-- Vectors supported in the coordinates `< k`. -/
def lowVec (a k : ℕ) : Submodule B (Fin a → B) where
  carrier := {v | ∀ l : Fin a, k ≤ l.val → v l = 0}
  add_mem' := fun hv hw l hl => by rw [Pi.add_apply, hv l hl, hw l hl, add_zero]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c v hv l hl => by rw [Pi.smul_apply, hv l hl, smul_zero]

/-- The filtration of `Bᵃ ⧸ N`. -/
def cycFilt {a : ℕ} (N : Submodule B (Fin a → B)) (k : ℕ) : Submodule B ((Fin a → B) ⧸ N) :=
  (lowVec B a k).map N.mkQ

theorem cycFilt_mono {a : ℕ} (N : Submodule B (Fin a → B)) {k l : ℕ} (hkl : k ≤ l) :
    cycFilt N k ≤ cycFilt N l :=
  Submodule.map_mono fun _ hv m hm => hv m (le_trans hkl hm)

variable {R : Type*} [CommRing R] [Algebra R B]

theorem flat_cycFilt_succ {a : ℕ} (N : Submodule B (Fin a → B)) (k : ℕ) (hk : k < a)
    [Module.Flat R (cycFilt N k)] [Module.Flat R (B ⧸ cyclicIdeal N ⟨k, hk⟩)] :
    Module.Flat R (cycFilt N (k + 1)) := by
  let i : Fin a := ⟨k, hk⟩
  let ψ : lowVec B a (k + 1) →ₗ[B] (Fin a → B) ⧸ N := N.mkQ.comp (lowVec B a (k + 1)).subtype
  have hrange : LinearMap.range ψ = cycFilt N (k + 1) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
    rfl
  let ψ' : lowVec B a (k + 1) →ₗ[B] cycFilt N (k + 1) :=
    LinearMap.codRestrict (cycFilt N (k + 1)) ψ fun v => hrange ▸ LinearMap.mem_range_self ψ v
  have hψ' : Surjective ψ' := by
    rintro ⟨_, ⟨v, hv, rfl⟩⟩
    exact ⟨⟨v, hv⟩, rfl⟩
  let φ : lowVec B a (k + 1) →ₗ[B] B ⧸ cyclicIdeal N i :=
    (Submodule.mkQ (cyclicIdeal N i)).comp ((LinearMap.proj i).comp (lowVec B a (k + 1)).subtype)
  have hφ : ∀ v, φ v = Submodule.Quotient.mk ((v : Fin a → B) i) := fun v => rfl
  have hvhigh : ∀ v : lowVec B a (k + 1), ∀ l : Fin a, i < l → (v : Fin a → B) l = 0 :=
    fun v l hl => v.2 l (Nat.succ_le_of_lt hl)
  have hker : LinearMap.ker ψ' ≤ LinearMap.ker φ := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have hN : (v : Fin a → B) ∈ N := by
      have h0 : N.mkQ (v : Fin a → B) = 0 := congrArg Subtype.val hv
      rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
    rw [hφ, Submodule.Quotient.mk_eq_zero]
    exact ⟨v, hN, rfl, hvhigh v⟩
  let e := ψ'.quotKerEquivOfSurjective hψ'
  let g : cycFilt N (k + 1) →ₗ[B] B ⧸ cyclicIdeal N i :=
    (LinearMap.ker ψ').liftQ φ hker ∘ₗ e.symm.toLinearMap
  have hg : ∀ v, g (ψ' v) = φ v := by
    intro v
    have h1 : e.symm (ψ' v) = Submodule.Quotient.mk v := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    change (LinearMap.ker ψ').liftQ φ hker (e.symm (ψ' v)) = φ v
    rw [h1, Submodule.liftQ_apply]
  let f : cycFilt N k →ₗ[B] cycFilt N (k + 1) := Submodule.inclusion (cycFilt_mono N (Nat.le_succ k))
  have hf : Injective f := Submodule.inclusion_injective _
  have hgs : Surjective g := by
    intro z
    obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective (cyclicIdeal N i) z
    have hmem : (Pi.single i c : Fin a → B) ∈ lowVec B a (k + 1) := by
      intro l hl
      rw [Pi.single_eq_of_ne]
      intro hli
      rw [hli] at hl
      exact absurd hl (by simp [i])
    refine ⟨ψ' ⟨_, hmem⟩, ?_⟩
    rw [hg, hφ]
    change Submodule.Quotient.mk ((Pi.single i c : Fin a → B) i) = _
    rw [Pi.single_eq_same]
    rfl
  have hfg : Exact f g := by
    intro v
    obtain ⟨v, rfl⟩ := hψ' v
    rw [hg, hφ, Submodule.Quotient.mk_eq_zero, mem_cyclicIdeal]
    constructor
    · rintro ⟨w, hwN, hwi, hw⟩
      have hlow : (v : Fin a → B) - w ∈ lowVec B a k := by
        intro l hl
        rw [Pi.sub_apply]
        rcases eq_or_lt_of_le hl with h | h
        · have hli : l = i := Fin.ext h.symm
          rw [hli, hwi, sub_self]
        · have hil : i < l := h
          rw [hvhigh v l hil, hw l hil, sub_self]
      refine ⟨⟨_, ⟨_, hlow, rfl⟩⟩, ?_⟩
      apply Subtype.ext
      change N.mkQ ((v : Fin a → B) - w) = N.mkQ (v : Fin a → B)
      have h0 : N.mkQ w = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hwN
      rw [map_sub, h0, sub_zero]
    · rintro ⟨⟨_, ⟨u, hu, rfl⟩⟩, hw⟩
      have h1 : N.mkQ u = N.mkQ (v : Fin a → B) := congrArg Subtype.val hw
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h1
      refine ⟨(v : Fin a → B) - u, ?_, ?_, fun l hl => ?_⟩
      · rw [← neg_sub]
        exact N.neg_mem h1
      · rw [Pi.sub_apply, hu i le_rfl, sub_zero]
      · rw [Pi.sub_apply, hvhigh v l hl, hu l (le_of_lt hl), sub_self]
  exact HironakaG10LfGradedFlat.flat_of_exact (f.restrictScalars R) (g.restrictScalars R) hf hgs hfg

/-- **ALG-2: flatness of `Bᵃ ⧸ N` from its cyclic pieces.** -/
theorem flat_quotient_of_flat_cyclicIdeal {a : ℕ} (N : Submodule B (Fin a → B))
    (h : ∀ i, Module.Flat R (B ⧸ cyclicIdeal N i)) : Module.Flat R ((Fin a → B) ⧸ N) := by
  have hF : ∀ k, k ≤ a → Module.Flat R (cycFilt N k) := by
    intro k
    induction k with
    | zero =>
      intro _
      have : Subsingleton (cycFilt N 0) := by
        refine ⟨fun x y => ?_⟩
        have hz : ∀ z : cycFilt N 0, z = 0 := by
          rintro ⟨_, ⟨v, hv, rfl⟩⟩
          have hv0 : v = 0 := funext fun l => hv l (Nat.zero_le _)
          apply Subtype.ext
          change N.mkQ v = 0
          rw [hv0, map_zero]
        rw [hz x, hz y]
      infer_instance
    | succ k ih =>
      intro hk
      have := ih (Nat.le_of_succ_le hk)
      have := h ⟨k, hk⟩
      exact flat_cycFilt_succ N k hk
  have htop : cycFilt N a = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective N x
    exact ⟨v, fun l hl => absurd l.2 (not_lt.2 hl), rfl⟩
  have := hF a le_rfl
  have e : cycFilt N a ≃ₗ[R] (Fin a → B) ⧸ N :=
    ((LinearEquiv.ofEq _ _ htop).trans Submodule.topEquiv).restrictScalars R
  exact Module.Flat.of_linearEquiv e.symm

end Hironaka.Analytic.Unibranch.HironakaG10LfCyclicFlat
