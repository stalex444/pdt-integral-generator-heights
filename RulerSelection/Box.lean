module

public import Mathlib
public import RulerSelection.NmatLink
public import RulerSelection.EnumProbe.PrunedSound

/-!
# B3. The box (stage 2, lane B)

With the RECOMPUTED diagonal data of SCOPE_GATE_STAGE2 (the blueprint's S4 numbers are retired):
`s = (1311/500, 292/125, 2643/1000)`, `t = (3719/1000, 169/50, 514/125, 504/125)`.

* `Sp_diag0..2`, `Tp_diag0..3` : the seven facts `Sp − s_a E_aa ⪰ 0`, `Tp − t_b E_bb ⪰ 0`
  (rational LDLᵀ certificates, checked exactly in Python first).
* `Sp_herm`, `Tp_herm`, `Sp_diag`, `Tp_diag`.
* `coord_sq_le` : `s_a t_b y(a,b)² ≤ yᵀ (Sp ⊗ₖ Tp) y` (from `Kron.kron_ge_diag`).
* `box_of_qf` : integer `y` with `qf Nmat (vecOf y) ≤ 240300` has every `|y d| ≤ 1`.
* `mem_box_of`, `mem_box_iff` : the converse of stage 1's `box_length`/`box_entries`.
* `vecOf_mem_box`, `vecOf_mem_L12` : the bridge to the stage-1 list form (`enum12`).
-/

@[expose] public section

open Matrix
open scoped Kronecker

namespace RulerSelection.LaneB

noncomputable section

open RulerSelection.EnumProbe

theorem Sp_diag0 (v : Fin 3 → ℝ) : 0 ≤ v ⬝ᵥ ((Sp - Kron.diagE 0 (1311/500 : ℝ)) *ᵥ v) := by
  simp [dotProduct, mulVec, Fin.sum_univ_succ, Sp, Kron.diagE, diagonal_apply, Pi.single_apply, Matrix.sub_apply]
  linarith [mul_nonneg (show (0:ℝ) ≤ (46/125:ℝ) by norm_num) (sq_nonneg ((1:ℝ)*v 0 + (-495/184:ℝ)*v 1)), mul_nonneg (show (0:ℝ) ≤ (395/736:ℝ) by norm_num) (sq_nonneg ((1:ℝ)*v 1 + (24288/9875:ℝ)*v 2)), mul_nonneg (show (0:ℝ) ≤ (3359/987500:ℝ) by norm_num) (sq_nonneg ((1:ℝ)*v 2))]

theorem Sp_diag1 (v : Fin 3 → ℝ) : 0 ≤ v ⬝ᵥ ((Sp - Kron.diagE 1 (292/125 : ℝ)) *ᵥ v) := by
  simp [dotProduct, mulVec, Fin.sum_univ_succ, Sp, Kron.diagE, diagonal_apply, Pi.single_apply, Matrix.sub_apply]
  linarith [mul_nonneg (show (0:ℝ) ≤ (299/100:ℝ) by norm_num) (sq_nonneg ((1:ℝ)*v 0 + (-99/299:ℝ)*v 1)), mul_nonneg (show (0:ℝ) ≤ (80163/149500:ℝ) by norm_num) (sq_nonneg ((1:ℝ)*v 1 + (65780/26721:ℝ)*v 2)), mul_nonneg (show (0:ℝ) ≤ (91/178140:ℝ) by norm_num) (sq_nonneg ((1:ℝ)*v 2))]

theorem Sp_diag2 (v : Fin 3 → ℝ) : 0 ≤ v ⬝ᵥ ((Sp - Kron.diagE 2 (2643/1000 : ℝ)) *ᵥ v) := by
  simp [dotProduct, mulVec, Fin.sum_univ_succ, Sp, Kron.diagE, diagonal_apply, Pi.single_apply, Matrix.sub_apply]
  linarith [mul_nonneg (show (0:ℝ) ≤ (299/100:ℝ) by norm_num) (sq_nonneg ((1:ℝ)*v 0 + (-99/299:ℝ)*v 1)), mul_nonneg (show (0:ℝ) ≤ (85879/29900:ℝ) by norm_num) (sq_nonneg ((1:ℝ)*v 1 + (39468/85879:ℝ)*v 2)), mul_nonneg (show (0:ℝ) ≤ (30793/85879000:ℝ) by norm_num) (sq_nonneg ((1:ℝ)*v 2))]

theorem Tp_diag0 (v : Fin 4 → ℝ) : 0 ≤ v ⬝ᵥ ((Tp - Kron.diagE 0 (3719/1000 : ℝ)) *ᵥ v) := by
  simp [dotProduct, mulVec, Fin.sum_univ_succ, Tp, Kron.diagE, diagonal_apply, Pi.single_apply, Matrix.sub_apply]
  linarith [mul_nonneg (show (0:ℝ) ≤ (271/1000:ℝ) by norm_num) (sq_nonneg ((1:ℝ)*v 0 + (-990/271:ℝ)*v 1)), mul_nonneg (show (0:ℝ) ≤ (19333/27100:ℝ) by norm_num) (sq_nonneg ((1:ℝ)*v 1 + (5962/19333:ℝ)*v 2 + (50948/19333:ℝ)*v 3)), mul_nonneg (show (0:ℝ) ≤ (8124027/1933300:ℝ) by norm_num) (sq_nonneg ((1:ℝ)*v 2 + (580448/8124027:ℝ)*v 3)), mul_nonneg (show (0:ℝ) ≤ (13040966/203100675:ℝ) by norm_num) (sq_nonneg ((1:ℝ)*v 3))]

theorem Tp_diag1 (v : Fin 4 → ℝ) : 0 ≤ v ⬝ᵥ ((Tp - Kron.diagE 1 (169/50 : ℝ)) *ᵥ v) := by
  simp [dotProduct, mulVec, Fin.sum_univ_succ, Tp, Kron.diagE, diagonal_apply, Pi.single_apply, Matrix.sub_apply]
  linarith [mul_nonneg (show (0:ℝ) ≤ (399/100:ℝ) by norm_num) (sq_nonneg ((1:ℝ)*v 0 + (-33/133:ℝ)*v 1)), mul_nonneg (show (0:ℝ) ≤ (2342/3325:ℝ) by norm_num) (sq_nonneg ((1:ℝ)*v 1 + (1463/4684:ℝ)*v 2 + (6251/2342:ℝ)*v 3)), mul_nonneg (show (0:ℝ) ≤ (983941/234200:ℝ) by norm_num) (sq_nonneg ((1:ℝ)*v 2 + (68574/983941:ℝ)*v 3)), mul_nonneg (show (0:ℝ) ≤ (42103/24598525:ℝ) by norm_num) (sq_nonneg ((1:ℝ)*v 3))]

theorem Tp_diag2 (v : Fin 4 → ℝ) : 0 ≤ v ⬝ᵥ ((Tp - Kron.diagE 2 (514/125 : ℝ)) *ᵥ v) := by
  simp [dotProduct, mulVec, Fin.sum_univ_succ, Tp, Kron.diagE, diagonal_apply, Pi.single_apply, Matrix.sub_apply]
  linarith [mul_nonneg (show (0:ℝ) ≤ (399/100:ℝ) by norm_num) (sq_nonneg ((1:ℝ)*v 0 + (-33/133:ℝ)*v 1)), mul_nonneg (show (0:ℝ) ≤ (27161/6650:ℝ) by norm_num) (sq_nonneg ((1:ℝ)*v 1 + (1463/27161:ℝ)*v 2 + (12502/27161:ℝ)*v 3)), mul_nonneg (show (0:ℝ) ≤ (1984789/13580500:ℝ) by norm_num) (sq_nonneg ((1:ℝ)*v 2 + (10575620/1984789:ℝ)*v 3)), mul_nonneg (show (0:ℝ) ≤ (1254688/49619725:ℝ) by norm_num) (sq_nonneg ((1:ℝ)*v 3))]

theorem Tp_diag3 (v : Fin 4 → ℝ) : 0 ≤ v ⬝ᵥ ((Tp - Kron.diagE 3 (504/125 : ℝ)) *ᵥ v) := by
  simp [dotProduct, mulVec, Fin.sum_univ_succ, Tp, Kron.diagE, diagonal_apply, Pi.single_apply, Matrix.sub_apply]
  linarith [mul_nonneg (show (0:ℝ) ≤ (399/100:ℝ) by norm_num) (sq_nonneg ((1:ℝ)*v 0 + (-33/133:ℝ)*v 1)), mul_nonneg (show (0:ℝ) ≤ (27161/6650:ℝ) by norm_num) (sq_nonneg ((1:ℝ)*v 1 + (1463/27161:ℝ)*v 2 + (12502/27161:ℝ)*v 3)), mul_nonneg (show (0:ℝ) ≤ (11565561/2716100:ℝ) by norm_num) (sq_nonneg ((1:ℝ)*v 2 + (2115124/11565561:ℝ)*v 3)), mul_nonneg (show (0:ℝ) ≤ (338696/1445695125:ℝ) by norm_num) (sq_nonneg ((1:ℝ)*v 3))]

/-- Diagonal data. -/
def sv : Fin 3 → ℝ := ![1311/500, 292/125, 2643/1000]
def tv : Fin 4 → ℝ := ![3719/1000, 169/50, 514/125, 504/125]

theorem Sp_herm : Sp.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Sp, conjTranspose_apply]

theorem Tp_herm : Tp.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Tp, conjTranspose_apply]

theorem Sp_diag (a : Fin 3) (v : Fin 3 → ℝ) : 0 ≤ v ⬝ᵥ ((Sp - Kron.diagE a (sv a)) *ᵥ v) := by
  fin_cases a
  · exact Sp_diag0 v
  · exact Sp_diag1 v
  · exact Sp_diag2 v

theorem Tp_diag (b : Fin 4) (v : Fin 4 → ℝ) : 0 ≤ v ⬝ᵥ ((Tp - Kron.diagE b (tv b)) *ᵥ v) := by
  fin_cases b
  · exact Tp_diag0 v
  · exact Tp_diag1 v
  · exact Tp_diag2 v
  · exact Tp_diag3 v

theorem sv_pos (a : Fin 3) : 0 ≤ sv a := by fin_cases a <;> norm_num [sv]
theorem tv_pos (b : Fin 4) : 0 ≤ tv b := by fin_cases b <;> norm_num [tv]

/-- `s_a t_b ≥ 7 > 24.03 / 4` (the box factor is `24.03 / min(s_a t_b) = 3.0434… < 4`). -/
theorem svtv_ge (a : Fin 3) (b : Fin 4) : 7 ≤ sv a * tv b := by
  fin_cases a <;> fin_cases b <;> norm_num [sv, tv]

theorem coord_sq_le (y : Fin 3 × Fin 4 → ℝ) (d : Fin 3 × Fin 4) :
    sv d.1 * tv d.2 * y d ^ 2 ≤ y ⬝ᵥ ((Sp ⊗ₖ Tp) *ᵥ y) :=
  Kron.kron_ge_diag Sp_herm Tp_herm d.1 d.2 (sv d.1) (tv d.2) (sv_pos _) (tv_pos _)
    (Sp_diag d.1) (Tp_diag d.2) y

/-- **B3. The box.** -/
theorem box_of_qf (y : Fin 3 × Fin 4 → ℤ) (h : qf Nmat (vecOf y) ≤ 240300) (d : Fin 3 × Fin 4) :
    -1 ≤ y d ∧ y d ≤ 1 := by
  have hq := qf_Nmat_eq y
  have hR : (qf Nmat (vecOf y) : ℝ) ≤ 240300 := by exact_mod_cast h
  have hc := coord_sq_le (fun p => (y p : ℝ)) d
  have hst := svtv_ge d.1 d.2
  have hsq : ((y d : ℝ)) ^ 2 < 4 := by
    nlinarith [sq_nonneg ((y d : ℝ))]
  have hsqZ : (y d) ^ 2 < 4 := by exact_mod_cast hsq
  constructor <;> nlinarith

/-- Converse of `box_length` + `box_entries`. -/
theorem mem_box_of : ∀ (k : ℕ) (l : List ℤ), l.length = k →
    (∀ t ∈ l, t = -1 ∨ t = 0 ∨ t = 1) → l ∈ box k
  | 0, l, hl, _ => by
    rw [List.length_eq_zero_iff] at hl; subst hl; simp [box]
  | k + 1, l, hl, he => by
    rcases List.eq_nil_or_concat l with h | ⟨l', t, rfl⟩
    · subst h; simp at hl
    · have hl' : l'.length = k := by simpa using hl
      have ih := mem_box_of k l' hl' (fun s hs => he s (by simp [hs]))
      have ht := he t (by simp)
      simp only [box, List.mem_flatMap, List.mem_map]
      refine ⟨l', ih, t, ?_, by simp⟩
      rcases ht with h | h | h <;> simp [h]

theorem mem_box_iff (k : ℕ) (l : List ℤ) :
    l ∈ box k ↔ l.length = k ∧ ∀ t ∈ l, t = -1 ∨ t = 0 ∨ t = 1 :=
  ⟨fun h => ⟨box_length k l h, box_entries k l h⟩, fun h => mem_box_of k l h.1 h.2⟩

theorem vecOf_mem_box (y : Fin 3 × Fin 4 → ℤ) (hy : ∀ d, -1 ≤ y d ∧ y d ≤ 1) :
    vecOf y ∈ box 12 := by
  have hy' : ∀ d, y d = -1 ∨ y d = 0 ∨ y d = 1 := fun d => by have := hy d; omega
  refine mem_box_of 12 _ rfl ?_
  intro t ht
  simp only [vecOf, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> exact hy' _

/-- **B3, list form.** An integer tensor vector under the cut lies in the stage-1 list. -/
theorem vecOf_mem_L12 (y : Fin 3 × Fin 4 → ℤ) (h : qf Nmat (vecOf y) ≤ 240300) :
    vecOf y ∈ L12 :=
  enum12 _ (vecOf_mem_box y (box_of_qf y h)) h

end

end RulerSelection.LaneB
