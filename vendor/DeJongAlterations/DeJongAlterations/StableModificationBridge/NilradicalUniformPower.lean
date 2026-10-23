import DeJongAlterations.StableModificationBridge.NilradicalCoverEngine

/-! The actual Noetherian nilradical has one internally produced uniform positive zero power. -/

noncomputable section

namespace DeJongAlterations.StableModificationBridge.NilradicalUniformPower

open CategoryTheory AlgebraicGeometry
open StableModification.Cohomology

set_option autoImplicit false

universe u

/-- The SAME original nilradical has a uniform positive zero power, INTERNALLY from native Noetherianity. -/
theorem exists_positive_pow_eq_bot (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))] :
    ∃ e : ℕ, 0 < e ∧ X.nilradical ^ e = ⊥ := by
  classical
  let C := FiniteAffineCover.choose X
  let : Fintype C.ι := Fintype.ofFinite C.ι
  have hnil (i : C.ι) : IsNilpotent (X.nilradical.ideal ⟨C.U i, C.isAffineOpen i⟩) := by
    let : IsNoetherianRing Γ(X, C.U i) :=
      IsLocallyNoetherian.component_noetherian ⟨C.U i, C.isAffineOpen i⟩
    exact IsNoetherianRing.isNilpotent_nilradical Γ(X, C.U i)
  choose e he using hnil
  refine ⟨Finset.univ.sup e + 1, Nat.succ_pos _, ?_⟩
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun i : C.ι => ⟨C.U i, C.isAffineOpen i⟩) C.iSup_eq_top
  intro i
  change X.nilradical.ideal ⟨C.U i, C.isAffineOpen i⟩ ^ (Finset.univ.sup e + 1) = ⊥
  apply le_antisymm _ bot_le
  calc
    X.nilradical.ideal ⟨C.U i, C.isAffineOpen i⟩ ^ (Finset.univ.sup e + 1) ≤
        X.nilradical.ideal ⟨C.U i, C.isAffineOpen i⟩ ^ e i :=
      Ideal.pow_le_pow_right ((Finset.le_sup (Finset.mem_univ i)).trans (Nat.le_succ _))
    _ = ⊥ := he i

end DeJongAlterations.StableModificationBridge.NilradicalUniformPower
