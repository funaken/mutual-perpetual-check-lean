import MPC.Basic.Move
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
/-!
# MPC.Basic.SlidePath

Membership and clearance for exact, nonzero slide rays.
The existing path enumerator is unchanged. No geometric interpretation of
nonaligned inputs, or list order/length/uniqueness theorem, is asserted here.
-/

namespace MPC

private def rayPoint (cur : ℤ × ℤ) (d : Dir) (j : ℕ) : ℤ × ℤ :=
  (cur.1 + ↑j * d.1, cur.2 + ↑j * d.2)

private theorem rayPoint_injective (cur : ℤ × ℤ) (d : Dir) (hd : d ≠ (0, 0)) :
    Function.Injective (rayPoint cur d) := by
  intro a b h
  by_contra hab
  have hne : (↑a - ↑b : ℤ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hab)
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  dsimp only [rayPoint] at hx hy
  have hdx : d.1 = 0 :=
    (mul_eq_zero.mp (show (↑a - ↑b : ℤ) * d.1 = 0 by nlinarith)).resolve_left hne
  have hdy : d.2 = 0 :=
    (mul_eq_zero.mp (show (↑a - ↑b : ℤ) * d.2 = 0 by nlinarith)).resolve_left hne
  exact hd (Prod.ext hdx hdy)

private theorem rayPoint_shift (cur : ℤ × ℤ) (d : Dir) (j : ℕ) :
    rayPoint (rayPoint cur d 1) d j = rayPoint cur d (j + 1) := by
  ext <;> simp [rayPoint, Nat.cast_add] <;> ring

-- Recursion stops at the exact endpoint before the fuel can truncate a ray.
private theorem slidePathAux_mem_exact (d : Dir) (hd : d ≠ (0, 0)) :
    ∀ (fuel n : ℕ) (cur q : ℤ × ℤ), 1 ≤ n → n ≤ fuel →
      (q ∈ slidePathAux d (rayPoint cur d n) cur fuel ↔
        ∃ j : ℕ, 1 ≤ j ∧ j < n ∧ q = rayPoint cur d j) := by
  intro fuel
  induction fuel with
  | zero => intro n cur q hn hf; omega
  | succ fuel ih =>
    intro n cur q hn hf
    by_cases hn1 : n = 1
    · subst n
      simp [slidePathAux, rayPoint]
    · have hn2 : 2 ≤ n := by omega
      have hstep : rayPoint cur d 1 ≠ rayPoint cur d n := by
        intro h
        have := rayPoint_injective cur d hd h
        omega
      have hshift : rayPoint (rayPoint cur d 1) d (n - 1) = rayPoint cur d n := by
        rw [rayPoint_shift, show n - 1 + 1 = n from by omega]
      rw [slidePathAux, ite_eq_right (by simpa [rayPoint] using hstep)]
      rw [show (cur.1 + d.1, cur.2 + d.2) = rayPoint cur d 1 by simp [rayPoint]]
      rw [← hshift, List.mem_cons, ih (n - 1) (rayPoint cur d 1) q (by omega) (by omega)]
      constructor
      · rintro (h | ⟨j, hj, hjn, hq⟩)
        · exact ⟨1, by omega, by omega, h⟩
        · exact ⟨j + 1, by omega, by omega, hq.trans (rayPoint_shift cur d j)⟩
      · rintro ⟨j, hj, hjn, hq⟩
        by_cases hj1 : j = 1
        · subst j; exact Or.inl hq
        · right
          refine ⟨j - 1, by omega, by omega, ?_⟩
          rw [rayPoint_shift, show j - 1 + 1 = j from by omega]
          exact hq

/-- Two board endpoints on a nonzero integer ray are at most eight steps apart.
    Normalization and positivity are not needed for this bound. -/
theorem slideSteps_le_eight_of_endpoints (src dst : Pos) (d : Dir) (n : ℕ)
    (hd : d ≠ (0, 0))
    (hx : dst.toInt.1 = src.toInt.1 + ↑n * d.1)
    (hy : dst.toInt.2 = src.toInt.2 + ↑n * d.2) : n ≤ 8 := by
  have coord (a b : Fin 9) (v : ℤ) (hv : v ≠ 0)
      (h : (b.val : ℤ) = a.val + ↑n * v) : n ≤ 8 := by
    have ha := a.isLt
    have hb := b.isLt
    have hn : (0 : ℤ) ≤ n := by omega
    rcases lt_or_gt_of_ne hv with hneg | hpos
    · have hmul := mul_nonneg hn (show 0 ≤ -v - 1 by omega)
      have ha' : (a.val : ℤ) ≤ 8 := by omega
      have hb' : (0 : ℤ) ≤ b.val := by omega
      have : (n : ℤ) ≤ 8 := by nlinarith
      omega
    · have hmul := mul_nonneg hn (show 0 ≤ v - 1 by omega)
      have ha' : (0 : ℤ) ≤ a.val := by omega
      have hb' : (b.val : ℤ) ≤ 8 := by omega
      have : (n : ℤ) ≤ 8 := by nlinarith
      omega
  by_cases hdx : d.1 = 0
  · have hdy : d.2 ≠ 0 := by intro hdy; exact hd (Prod.ext hdx hdy)
    exact coord src.2 dst.2 d.2 hdy hy
  · exact coord src.1 dst.1 d.1 hdx hx

/-- Exact slide membership: precisely the positive steps before the endpoint.
    The board-size bound supplies the enumerator's fuel; it is not an extra premise. -/
theorem mem_slidePath_iff_of_exact_steps (src dst : Pos) (d : Dir) (n : ℕ)
    (hd : d ≠ (0, 0)) (hn : 1 ≤ n) (hdir : (Pos.dirTo src dst).normalize = d)
    (hx : dst.toInt.1 = src.toInt.1 + ↑n * d.1)
    (hy : dst.toInt.2 = src.toInt.2 + ↑n * d.2) (q : ℤ × ℤ) :
    q ∈ slidePath src dst ↔
      ∃ j : ℕ, 1 ≤ j ∧ j < n ∧ q = (src.toInt.1 + ↑j * d.1, src.toInt.2 + ↑j * d.2) := by
  have hdst : dst.toInt = rayPoint src.toInt d n := Prod.ext hx hy
  simp only [slidePath, hdir, ite_eq_right hd]
  rw [hdst]
  exact slidePathAux_mem_exact d hd 8 n src.toInt q hn
    (slideSteps_le_eight_of_endpoints src dst d n hd hx hy)

/-- All steps between the two endpoints are on board, including steps zero and n.
    This coordinate fact does not require normalization or a nonzero direction. -/
theorem slidePoint_onBoard_of_exact_steps (src dst : Pos) (d : Dir) (n j : ℕ)
    (hj : j ≤ n)
    (hx : dst.toInt.1 = src.toInt.1 + ↑n * d.1)
    (hy : dst.toInt.2 = src.toInt.2 + ↑n * d.2) :
    onBoard (src.toInt.1 + ↑j * d.1, src.toInt.2 + ↑j * d.2) := by
  have coord (a b : Fin 9) (v : ℤ)
      (h : (b.val : ℤ) = a.val + ↑n * v) :
      0 ≤ (a.val : ℤ) + ↑j * v ∧ (a.val : ℤ) + ↑j * v < 9 := by
    have ha := a.isLt
    have hb := b.isLt
    have ha0 : (0 : ℤ) ≤ a.val := by omega
    have hb0 : (0 : ℤ) ≤ b.val := by omega
    have ha9 : (a.val : ℤ) < 9 := by omega
    have hb9 : (b.val : ℤ) < 9 := by omega
    have hj0 : (0 : ℤ) ≤ j := by omega
    have hjn : (0 : ℤ) ≤ (n : ℤ) - j := by omega
    rcases le_total 0 v with hv | hv
    · have h1 := mul_nonneg hj0 hv
      have h2 := mul_nonneg hjn hv
      constructor <;> nlinarith
    · have h1 := mul_nonpos_of_nonneg_of_nonpos hj0 hv
      have h2 := mul_nonpos_of_nonneg_of_nonpos hjn hv
      constructor <;> nlinarith
  exact ⟨(coord src.1 dst.1 d.1 hx).1, (coord src.1 dst.1 d.1 hx).2,
    (coord src.2 dst.2 d.2 hy).1, (coord src.2 dst.2 d.2 hy).2⟩

/-- Clearance is emptiness at every intermediate step. The preceding theorem
    guarantees that each quantified onBoard proof exists, so no step is skipped. -/
theorem pathClear_iff_of_exact_steps (board : Board) (src dst : Pos) (d : Dir) (n : ℕ)
    (hd : d ≠ (0, 0)) (hn : 1 ≤ n) (hdir : (Pos.dirTo src dst).normalize = d)
    (hx : dst.toInt.1 = src.toInt.1 + ↑n * d.1)
    (hy : dst.toInt.2 = src.toInt.2 + ↑n * d.2) :
    pathClear board src dst ↔ ∀ j : ℕ, 1 ≤ j → j < n →
      ∀ h : onBoard (src.toInt.1 + ↑j * d.1, src.toInt.2 + ↑j * d.2),
        board.grid (toPos (src.toInt.1 + ↑j * d.1, src.toInt.2 + ↑j * d.2) h) = none := by
  have hm := mem_slidePath_iff_of_exact_steps src dst d n hd hn hdir hx hy
  constructor
  · intro hc j hj hjn hob
    exact hc _ ((hm _).mpr ⟨j, hj, hjn, rfl⟩) hob hob
  · intro hc q hq _ hob
    obtain ⟨j, hj, hjn, rfl⟩ := (hm q).mp hq
    exact hc j hj hjn hob

end MPC
