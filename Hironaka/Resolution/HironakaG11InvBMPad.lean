import Hironaka.Resolution.HironakaG11InvBMClass

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Padded divisors for Bierstone--Milman's lower ideals (repair (B'), plan module 8, property (4'); decision r7)

Blueprint: `hironaka-g11-inv-bm-max-order.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §6d.

The general value `GeneralValue.genInv` records the members of the divisor through a point by their ABSOLUTE positions, so a
lower invariant does see empty members placed in front of the others (lane G8B, I-1370 C-0002:
`MonomialInvariantEmptyMember.genInv_insertEmpty_of_nmOrd_eq_zero`, `shiftVal_ne_self`).  Bierstone--Milman's lower ideal of
`𝔍` at a stage carries the members born along the tower from the base of `𝔍`; along `P T₁` with `P` empty, that of `𝔍` at
`P H₀` carries `|P|` empty members in front of those of `𝔍_P` at `H₀`.  Decision (G11B r7): the lower invariant is evaluated
on the PADDED lower ideal, the divisor preceded by one empty placeholder per member of `𝔍` (`padE L 𝔍.E.length`); the two
divisors compared in (4') are then literally equal (`𝔍_P.E` has `|𝔍.E| + |P|` members).  In Lean the padding is put into the
lower invariant: the Step 1 value of the family is `stepOneInvBM (Rm 𝔍.E.length) 𝔍` for a family of invariants `Rm` with
`(Rm (m + m')).inv L = (Rm m).inv (padE L m')` (instance: `Rm m L = R (padE L m)`), so every existing theorem about
`stepOneInvBM R` (generic in `R`) applies unchanged.

* `padE L m`: the divisor preceded by `m` empty members; `padE_zero`, `padE_padE`, `pullback_padE`, `cosupp_padE`, field lemmas.

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set

universe u

namespace Hironaka.HironakaG11InvBMPad

open Hironaka.HolomorphicIdealSheaves MarkedIdeals MarkedIdeals.MarkedIdeal
  Hironaka.MarkedIdealBiholomorphism

noncomputable section

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **The divisor preceded by `m` empty members** (same carrier, ideal and mark). -/
def padE (L : MarkedIdeal n M) (m : ℕ) : MarkedIdeal n M :=
  { L with E := List.replicate m ∅ ++ L.E }

@[simp] theorem padE_N (L : MarkedIdeal n M) (m : ℕ) : (padE L m).N = L.N := rfl
@[simp] theorem padE_E (L : MarkedIdeal n M) (m : ℕ) : (padE L m).E = List.replicate m ∅ ++ L.E := rfl
@[simp] theorem padE_ideal (L : MarkedIdeal n M) (m : ℕ) : (padE L m).ideal = L.ideal := rfl
@[simp] theorem padE_d (L : MarkedIdeal n M) (m : ℕ) : (padE L m).d = L.d := rfl

theorem padE_zero (L : MarkedIdeal n M) : padE L 0 = L := rfl

/-- **Padding twice is padding once**: `padE (padE L m') m = padE L (m + m')`. -/
theorem padE_padE (L : MarkedIdeal n M) (m m' : ℕ) : padE (padE L m') m = padE L (m + m') := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_ rfl rfl
  show List.replicate m ∅ ++ (List.replicate m' ∅ ++ L.E) = List.replicate (m + m') ∅ ++ L.E
  rw [← List.append_assoc, List.replicate_append_replicate]

theorem length_E_padE (L : MarkedIdeal n M) (m : ℕ) : (padE L m).E.length = m + L.E.length := by
  simp

/-- The cosupport does not see the divisor. -/
theorem cosupp_padE (L : MarkedIdeal n M) (m : ℕ) : (padE L m).cosupp = L.cosupp := rfl

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']

/-- **Pullbacks commute with padding** (the preimage of `∅` is empty). -/
theorem pullback_padE (f : M' → M) (L : MarkedIdeal n M) (m : ℕ) :
    MarkedIdeal.pullback f (padE L m) = padE (MarkedIdeal.pullback f L) m := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_ rfl rfl
  show (List.replicate m ∅ ++ L.E).map (f ⁻¹' ·) = List.replicate m ∅ ++ L.E.map (f ⁻¹' ·)
  rw [List.map_append, List.map_replicate, preimage_empty]

end

end Hironaka.HironakaG11InvBMPad
