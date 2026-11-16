module

public import Mathlib

/-!
# EnumProbe — common definitions for the kernel-cost probe (Stage 1, P3)

`Nmat` is `10⁴ · q₀` in the tensor basis `{1, ρ⁻¹, ρ} ⊗ {1, Q⁻¹, Q, Q²}` (flat index `4·a + b`,
row-major `(a, b)`, `a ∈ Fin 3`, `b ∈ Fin 4`), with `100·S₀`, `100·T₀` the two-decimal lower forms.
The probe restricts to the first `k` coordinates (the rest fixed at `0`): `subMat k`.
-/

@[expose] public section

namespace RulerSelection.EnumProbe

/-- `10⁴ · q₀` as an integer `12 × 12` matrix (list of rows). -/
def Nmat : List (List ℤ) := [
  [119301, -29601, 0, 0, -39501, 9801, 0, 0, 0, 0, 0, 0],
  [-29601, 129467, 6578, 56212, 9801, -42867, -2178, -18612, 0, 0, 0, 0],
  [0, 6578, 127673, 26312, 0, -2178, -42273, -8712, 0, 0, 0, 0],
  [0, 56212, 26312, 150696, 0, -18612, -8712, -49896, 0, 0, 0, 0],
  [-39501, 9801, 0, 0, 127680, -31680, 0, 0, 52668, -13068, 0, 0],
  [9801, -42867, -2178, -18612, -31680, 138560, 7040, 60160, -13068, 57156, 2904, 24816],
  [0, -2178, -42273, -8712, 0, 7040, 136640, 28160, 0, 2904, 56364, 11616],
  [0, -18612, -8712, -49896, 0, 60160, 28160, 161280, 0, 24816, 11616, 66528],
  [0, 0, 0, 0, 52668, -13068, 0, 0, 129675, -32175, 0, 0],
  [0, 0, 0, 0, -13068, 57156, 2904, 24816, -32175, 140725, 7150, 61100],
  [0, 0, 0, 0, 0, 2904, 56364, 11616, 0, 7150, 138775, 28600],
  [0, 0, 0, 0, 0, 24816, 11616, 66528, 0, 61100, 28600, 163800]]

/-- Principal `k × k` submatrix. -/
def subMat (k : ℕ) : List (List ℤ) := (Nmat.take k).map (·.take k)

def dot (r x : List ℤ) : ℤ := (List.zipWith (· * ·) r x).sum

/-- The quadratic form `xᵀ M x`. -/
def qf (M : List (List ℤ)) (x : List ℤ) : ℤ := dot (M.map (fun r => dot r x)) x

/-- All lists of length `k` with entries in `{-1, 0, 1}`. -/
def box : ℕ → List (List ℤ)
  | 0 => [[]]
  | k + 1 => (box k).flatMap (fun l => [(-1 : ℤ), 0, 1].map (fun t => l ++ [t]))

/-- Bool checker: every box point with `qf ≤ B` is in `L`. -/
def checkB (k : ℕ) (B : ℤ) (L : List (List ℤ)) : Bool :=
  (box k).all (fun x => !(decide (qf (subMat k) x ≤ B)) || L.contains x)

theorem checkB_sound (k : ℕ) (B : ℤ) (L : List (List ℤ)) (h : checkB k B L = true) :
    ∀ x ∈ box k, qf (subMat k) x ≤ B → x ∈ L := by
  intro x hx hq
  unfold checkB at h
  rw [List.all_eq_true] at h
  have := h x hx
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_le] at this
  rcases this with h1 | h1
  · exact absurd hq (not_le.2 h1)
  · simpa using h1

/-- Function-style form (Mahler-box style): `x : Fin k → ℤ`. -/
def qfF (k : ℕ) (x : Fin k → ℤ) : ℤ :=
  ∑ i : Fin k, ∑ j : Fin k, ((Nmat.getD i.1 []).getD j.1 0) * x i * x j

/-- The box as a `Finset` of functions. -/
def boxF (k : ℕ) : Finset (Fin k → ℤ) := Fintype.piFinset (fun _ => Finset.Icc (-1 : ℤ) 1)

end RulerSelection.EnumProbe
