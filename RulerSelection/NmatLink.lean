module

public import Mathlib
public import RulerSelection.Bridge
public import RulerSelection.Kron
public import RulerSelection.EnumProbe

/-!
# B2. The change of basis and `Nmat` (stage 2, lane B)

Conventions (lane A, `Coords.lean`):
* power basis `ρ^i Q^j`, `(i, j) : Fin 3 × Fin 4`; tensor basis `tU a · tV b` with
  `tU = ![1, ρ⁻¹, ρ]`, `tV = ![1, Q⁻¹, Q, Q²]`, `(a, b) : Fin 3 × Fin 4`;
* `U_S := pu3` (`tU a = ∑ᵢ pu3 a i ρ^i`), `U_T := pu4` (`tV b = ∑ⱼ pu4 b j Q^j`), integer and
  unimodular (`pu3_pw3`, `pu4_pw4` in `Bridge.lean` give the integer inverses);
* power coordinates of `∑ y(a,b) tU a tV b` are `powC y = (U_S ⊗ U_T)ᵀ y`, i.e.
  `powC y (i,j) = ∑_{(a,b)} y(a,b) · pu3 a i · pu4 b j` (`pow_coords_of_tens`, lane A);
* the stage-1 list `vecOf y` is the flat vector with index `4a + b`.

Results:
* `Sp_congr`, `Tp_congr` : `U_S S₀ U_Sᵀ = Sp`, `U_T T₀ U_Tᵀ = Tp`, where
  `100·Sp = [[299,−99,0],[−99,320,132],[0,132,325]]`,
  `100·Tp = [[399,−99,0,0],[−99,433,22,188],[0,22,427,88],[0,188,88,504]]`.
* `form_powC` : `(powC y)ᵀ (S₀ ⊗ₖ T₀) (powC y) = yᵀ (Sp ⊗ₖ Tp) y`.
* `qf_Nmat_eq` : `qf Nmat (vecOf y) = 10⁴ · yᵀ (Sp ⊗ₖ Tp) y`.
* `nmat_identity` : `10⁴ · (powC y)ᵀ (S₀ ⊗ₖ T₀) (powC y) = qf Nmat (vecOf y)`.
* `vecOf_getD`, `funOf`, `vecOf_funOf`, `funOf_vecOf` : the list ↔ function conversion.
-/

@[expose] public section

open Matrix
open scoped Kronecker

namespace RulerSelection.LaneB

noncomputable section

open RulerSelection.GramCert RulerSelection.Emb RulerSelection.EnumProbe

/-- The flat list (index `4a + b`) of a tensor-coordinate function. -/
def vecOf (y : Fin 3 × Fin 4 → ℤ) : List ℤ :=
  [y (0, 0), y (0, 1), y (0, 2), y (0, 3), y (1, 0), y (1, 1), y (1, 2), y (1, 3),
   y (2, 0), y (2, 1), y (2, 2), y (2, 3)]

/-- The function of a flat list (index `4a + b`). -/
def funOf (l : List ℤ) : Fin 3 × Fin 4 → ℤ := fun d => l.getD (4 * d.1 + d.2) 0

theorem vecOf_length (y : Fin 3 × Fin 4 → ℤ) : (vecOf y).length = 12 := rfl

theorem vecOf_getD (y : Fin 3 × Fin 4 → ℤ) (d : Fin 3 × Fin 4) :
    (vecOf y).getD (4 * d.1 + d.2) 0 = y d := by
  rcases d with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> rfl

theorem funOf_vecOf (y : Fin 3 × Fin 4 → ℤ) : funOf (vecOf y) = y := by
  funext d; exact vecOf_getD y d

theorem vecOf_funOf (l : List ℤ) (hl : l.length = 12) : vecOf (funOf l) = l := by
  match l, hl with
  | [_, _, _, _, _, _, _, _, _, _, _, _], _ => rfl

theorem vecOf_injective : Function.Injective vecOf := fun y y' h => by
  rw [← funOf_vecOf y, ← funOf_vecOf y', h]

/-- `U_S` as a real matrix (rows: tensor index `a`; columns: power index `i`). -/
def US : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun a i => (pu3 a i : ℝ)
/-- `U_T` as a real matrix. -/
def UT : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun b j => (pu4 b j : ℝ)

/-- The tensor-basis cubic factor `U_S S₀ U_Sᵀ`. -/
def Sp : Matrix (Fin 3) (Fin 3) ℝ :=
  !![299/100, -99/100, 0; -99/100, 320/100, 132/100; 0, 132/100, 325/100]

/-- The tensor-basis quartic factor `U_T T₀ U_Tᵀ`. -/
def Tp : Matrix (Fin 4) (Fin 4) ℝ :=
  !![399/100, -99/100, 0, 0; -99/100, 433/100, 22/100, 188/100;
     0, 22/100, 427/100, 88/100; 0, 188/100, 88/100, 504/100]

theorem Sp_congr : US * S0 * USᵀ = Sp := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [US, Sp, S0, pu3, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

theorem Tp_congr : UT * T0 * UTᵀ = Tp := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [UT, Tp, T0, pu4, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The power-basis lower form at `powC y` is the tensor-basis lower form at `y`. -/
theorem form_powC (y : Fin 3 × Fin 4 → ℤ) :
    (fun p => (powC y p : ℝ)) ⬝ᵥ ((S0 ⊗ₖ T0) *ᵥ (fun p => (powC y p : ℝ))) =
      (fun p => (y p : ℝ)) ⬝ᵥ ((Sp ⊗ₖ Tp) *ᵥ (fun p => (y p : ℝ))) := by
  simp [dotProduct, mulVec, Fintype.sum_prod_type, Fin.sum_univ_succ, kroneckerMap_apply, powC,
    pu3, pu4, S0, T0, Sp, Tp]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The stage-1 table is `10⁴ ·` the tensor-basis lower form. -/
theorem qf_Nmat_eq (y : Fin 3 × Fin 4 → ℤ) :
    (qf Nmat (vecOf y) : ℝ) = 10000 * ((fun p => (y p : ℝ)) ⬝ᵥ ((Sp ⊗ₖ Tp) *ᵥ (fun p => (y p : ℝ)))) := by
  simp [qf, dot, Nmat, vecOf, dotProduct, mulVec, Fintype.sum_prod_type, Fin.sum_univ_succ,
    kroneckerMap_apply, Sp, Tp]
  ring

/-- **B2. The `Nmat` identity.** -/
theorem nmat_identity (y : Fin 3 × Fin 4 → ℤ) :
    10000 * ((fun p => (powC y p : ℝ)) ⬝ᵥ ((S0 ⊗ₖ T0) *ᵥ (fun p => (powC y p : ℝ)))) =
      (qf Nmat (vecOf y) : ℝ) := by
  rw [form_powC, qf_Nmat_eq]

end

end RulerSelection.LaneB
