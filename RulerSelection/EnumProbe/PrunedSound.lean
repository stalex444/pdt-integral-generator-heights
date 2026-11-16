module

public import RulerSelection.EnumProbe.Pruned

/-!
# Soundness of the pruned walk (P3c)

`go_sound`: a `true` walk certifies every completion whose LDL partial sums stay under the bound.
`enum12`: every point of the full box `{-1,0,1}¹²` with `N(x) ≤ 240300` lies in the 71-element list.
-/

@[expose] public section

namespace RulerSelection.EnumProbe

theorem cVec_nonneg (i : ℕ) : 0 ≤ cVec.getD i 0 := by
  have h := certIdentity
  unfold certOK at h
  rw [Bool.and_eq_true] at h
  have h2 := h.2
  rw [List.all_eq_true] at h2
  by_cases hi : i < cVec.length
  · rw [List.getD_eq_getElem _ _ hi]
    have := h2 (cVec[i]) (List.getElem_mem hi)
    simpa using this
  · rw [List.getD_eq_default _ _ (by omega)]

theorem sum_range_nonneg (j : ℕ) (x : List ℤ) :
    0 ≤ ((List.range j).map (fun i => cVec.getD i 0 * lin i (x.drop i) ^ 2)).sum := by
  apply List.sum_nonneg
  intro a ha
  rw [List.mem_map] at ha
  obtain ⟨i, _, rfl⟩ := ha
  exact mul_nonneg (cVec_nonneg i) (sq_nonneg _)

theorem go_sound : ∀ (j : ℕ) (suf : List ℤ) (p : ℤ), go j suf p = true →
    ∀ pre : List ℤ, pre.length = j + 1 → (∀ t ∈ pre, t = -1 ∨ t = 0 ∨ t = 1) →
    p + ((List.range (j + 1)).map
        (fun i => cVec.getD i 0 * lin i ((pre ++ suf).drop i) ^ 2)).sum ≤ KK * 240300 →
    pre ++ suf ∈ L12 := by
  intro j
  induction j with
  | zero =>
    intro suf p hgo pre hlen hent hsum
    match pre, hlen with
    | [t], _ =>
      have ht := hent t (by simp)
      rw [go] at hgo
      rw [List.all_eq_true] at hgo
      have hg := hgo t (by rcases ht with h | h | h <;> simp [h])
      simp only [Nat.zero_add, List.range_one, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        List.drop_zero, add_zero] at hsum
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hg
      simp only [List.cons_append, List.nil_append] at hsum ⊢
      rcases hg with hg | hg
      · exfalso; linarith
      · simpa using hg
  | succ j' ih =>
    intro suf p hgo pre hlen hent hsum
    obtain ⟨pre', t, rfl⟩ : ∃ pre' t, pre = pre' ++ [t] := by
      rcases List.eq_nil_or_concat pre with h | ⟨L, b, h⟩
      · subst h; simp at hlen
      · exact ⟨L, b, by simpa using h⟩
    have hlen' : pre'.length = j' + 1 := by simpa using hlen
    have ht := hent t (by simp)
    have hent' : ∀ s ∈ pre', s = -1 ∨ s = 0 ∨ s = 1 := fun s hs => hent s (by simp [hs])
    have happ : pre' ++ [t] ++ suf = pre' ++ (t :: suf) := by simp
    rw [happ] at hsum ⊢
    have hdrop : (pre' ++ (t :: suf)).drop (j' + 1) = t :: suf := by
      rw [List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega)]
      · simp [hlen']
    rw [List.range_succ, List.map_append, List.sum_append] at hsum
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hdrop] at hsum
    rw [go] at hgo
    rw [List.all_eq_true] at hgo
    have hg := hgo t (by rcases ht with h | h | h <;> simp [h])
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hg
    rcases hg with hg | hg
    · exfalso
      have := sum_range_nonneg (j' + 1) (pre' ++ (t :: suf))
      omega
    · exact ih (t :: suf) _ hg pre' hlen' hent' (by linarith)

theorem box_length : ∀ k, ∀ x ∈ box k, x.length = k
  | 0, x, hx => by simp [box] at hx; simp [hx]
  | k + 1, x, hx => by
    simp only [box, List.mem_flatMap, List.mem_map] at hx
    obtain ⟨l, hl, t, _, rfl⟩ := hx
    simp [box_length k l hl]

theorem box_entries : ∀ k, ∀ x ∈ box k, ∀ t ∈ x, t = -1 ∨ t = 0 ∨ t = 1
  | 0, x, hx => by simp [box] at hx; simp [hx]
  | k + 1, x, hx => by
    simp only [box, List.mem_flatMap, List.mem_map] at hx
    obtain ⟨l, hl, s, hs, rfl⟩ := hx
    intro t ht
    rw [List.mem_append] at ht
    rcases ht with ht | ht
    · exact box_entries k l hl t ht
    · simp at ht hs; subst ht; rcases hs with h | h | h <;> simp [h]

set_option maxHeartbeats 4000000 in
theorem ldl_identity (x : List ℤ) (hx : x.length = 12) :
    KK * qf Nmat x = ((List.range 12).map
        (fun i => cVec.getD i 0 * lin i (x.drop i) ^ 2)).sum := by
  match x, hx with
  | [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11], _ =>
    simp [qf, dot, lin, Nmat, ellM, cVec, KK, List.range_succ]
    ring

/-- **The finite check, kernel-verified via the pruned walk.** -/
theorem enum12 : ∀ x ∈ box 12, qf Nmat x ≤ 240300 → x ∈ L12 := by
  intro x hx hq
  have hlen := box_length 12 x hx
  have hent := box_entries 12 x hx
  have hK : (0 : ℤ) < KK := by decide
  have h := go_sound 11 [] 0 goCheck_true x hlen hent (by
    rw [List.append_nil, zero_add, ← ldl_identity x hlen]
    exact mul_le_mul_of_nonneg_left hq hK.le)
  simpa using h

end RulerSelection.EnumProbe
