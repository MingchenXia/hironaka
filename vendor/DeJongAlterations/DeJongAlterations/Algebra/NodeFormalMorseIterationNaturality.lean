import DeJongAlterations.Algebra.NodeFormalMorseIteration

/-! # Actual coefficient compatibility of every finite Morse iteration -/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFormalMorse

open MvPowerSeries

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {R : Type u} [CommRing R] {S : Type v} [CommRing S]

/-- Naturality of every internally constructed finite state, on every input series. -/
theorem iteration_map (f : R →+* S) (J : Ideal R) (K : Ideal S)
    (hJ : IsNilpotent J) (hK : IsNilpotent K) (H : Series R) (T : Series S)
    (hH : ∀ d, coeff d H ∈ J) (hT : ∀ d, coeff d T ∈ K)
    (he : MvPowerSeries.map f H = T) (k : ℕ) :
    f (iteration J hJ H hH k).scalar = (iteration K hK T hT k).scalar ∧
      MvPowerSeries.map f (iteration J hJ H hH k).error = (iteration K hK T hT k).error ∧
      ∀ g, MvPowerSeries.map f ((iteration J hJ H hH k).equiv g) =
        (iteration K hK T hT k).equiv (MvPowerSeries.map f g) := by
  induction k with
  | zero =>
    change f 0 = 0 ∧ MvPowerSeries.map f H = T ∧
      ∀ g : Series R, MvPowerSeries.map f g = MvPowerSeries.map f g
    exact ⟨map_zero f, he, fun _ => rfl⟩
  | succ k ih =>
    let s := iteration J hJ H hH k
    let t := iteration K hK T hT k
    have hs : MvPowerSeries.map f s.error = t.error := ih.2.1
    constructor
    · change f (s.scalar + correctedConstant (J ^ s.order) (hJ.pow_of_pos s.order_ne_zero)
          s.error s.error_mem) =
        t.scalar + correctedConstant (K ^ t.order) (hK.pow_of_pos t.order_ne_zero) t.error t.error_mem
      rw [map_add, ih.1, correctedConstant_map f (J ^ s.order) (K ^ t.order)
        (hJ.pow_of_pos s.order_ne_zero) (hK.pow_of_pos t.order_ne_zero)
        s.error t.error s.error_mem t.error_mem hs]
    constructor
    · exact correctedResidual_map f (J ^ s.order) (K ^ t.order)
        (hJ.pow_of_pos s.order_ne_zero) (hK.pow_of_pos t.order_ne_zero)
        s.error t.error s.error_mem t.error_mem hs
    · intro g
      change MvPowerSeries.map f
        ((correctionEquiv (J ^ s.order) (hJ.pow_of_pos s.order_ne_zero) s.error s.error_mem).symm
          (s.equiv g)) =
        (correctionEquiv (K ^ t.order) (hK.pow_of_pos t.order_ne_zero) t.error t.error_mem).symm
          (t.equiv (MvPowerSeries.map f g))
      rw [correctionEquiv_symm_map f (J ^ s.order) (K ^ t.order)
        (hJ.pow_of_pos s.order_ne_zero) (hK.pow_of_pos t.order_ne_zero)
        s.error t.error s.error_mem t.error_mem hs, ih.2.2 g]

/-- The native finite inverse maps also commute on every series. -/
theorem iteration_symm_map (f : R →+* S) (J : Ideal R) (K : Ideal S)
    (hJ : IsNilpotent J) (hK : IsNilpotent K) (H : Series R) (T : Series S)
    (hH : ∀ d, coeff d H ∈ J) (hT : ∀ d, coeff d T ∈ K)
    (he : MvPowerSeries.map f H = T) (k : ℕ) (g : Series R) :
    MvPowerSeries.map f ((iteration J hJ H hH k).equiv.symm g) =
      (iteration K hK T hT k).equiv.symm (MvPowerSeries.map f g) := by
  apply (iteration K hK T hT k).equiv.injective
  rw [AlgEquiv.apply_symm_apply, ← (iteration_map f J K hJ hK H T hH hT he k).2.2,
    AlgEquiv.apply_symm_apply]

/-- An original zero error makes every finite scalar zero. -/
theorem iteration_zero_scalar (J : Ideal R) (hJ : IsNilpotent J)
    (hz : ∀ d, coeff d (0 : Series R) ∈ J) (k : ℕ) :
    (iteration J hJ 0 hz k).scalar = 0 := by
  simpa only [Nat.zero_add, iteration] using (iteration_stable J hJ 0 hz 0 k rfl).2.1

/-- An original zero error makes every actual finite map the identity. -/
theorem iteration_zero_equiv (J : Ideal R) (hJ : IsNilpotent J)
    (hz : ∀ d, coeff d (0 : Series R) ∈ J) (k : ℕ) :
    (iteration J hJ 0 hz k).equiv = AlgEquiv.refl := by
  simpa only [Nat.zero_add, iteration] using (iteration_stable J hJ 0 hz 0 k rfl).2.2

end DeJongAlterations.Algebra.NodeFormalMorse
