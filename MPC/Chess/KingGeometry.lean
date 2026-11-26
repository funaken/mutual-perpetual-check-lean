import MPC.Chess.LegalMove
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Local geometry for the paper's Proposition 2.2. Alignment here means a
common file, rank or diagonal. No trace-wide immobility is assumed. -/

namespace MPC.Chess

def Pos.aligned (a b : Pos) : Prop :=
  a.toInt.1 = b.toInt.1 ∨ a.toInt.2 = b.toInt.2 ∨
    b.toInt.1 - a.toInt.1 = b.toInt.2 - a.toInt.2 ∨
    b.toInt.1 - a.toInt.1 = -(b.toInt.2 - a.toInt.2)

instance (a b : Pos) : Decidable (a.aligned b) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

theorem Pos.aligned_comm (a b : Pos) : a.aligned b ↔ b.aligned a := by
  unfold Pos.aligned
  omega

private theorem pos_ext {a b : Pos} (hx : a.toInt.1 = b.toInt.1)
    (hy : a.toInt.2 = b.toInt.2) : a = b := by
  apply Prod.ext <;> apply Fin.ext <;> simp only [Pos.toInt] at hx hy <;> omega

private theorem pos_ne {a b : Pos} (h : a ≠ b) :
    a.toInt.1 ≠ b.toInt.1 ∨ a.toInt.2 ≠ b.toInt.2 := by
  by_contra hn
  push Not at hn
  exact h (pos_ext hn.1 hn.2)

theorem king_attack_symm (b b' : Board) (c c' : Color) (a d : Pos)
    (h : attacks b ⟨c, .king⟩ a d) : attacks b' ⟨c', .king⟩ d a := by
  refine ⟨Ne.symm h.1, ?_⟩
  simp only [attacks, Pos.delta, abs_le] at h ⊢
  omega

theorem attacks_aligned_of_slider {b : Board} {p : Piece} {a t : Pos}
    (hk : p.kind = .queen ∨ p.kind = .rook ∨ p.kind = .bishop)
    (ha : attacks b p a t) : a.aligned t := by
  rcases hk with h | h | h <;>
    simp only [attacks, h, Pos.delta, abs_eq_abs] at ha <;>
    unfold Pos.aligned <;> omega

private theorem between_line_cases {a t s : Pos} (ha : a.aligned t) (hs : Between a t s) :
    (a.toInt.1 = t.toInt.1 ∧ s.toInt.1 = a.toInt.1) ∨
    (a.toInt.2 = t.toInt.2 ∧ s.toInt.2 = a.toInt.2) ∨
    (t.toInt.1 - a.toInt.1 = t.toInt.2 - a.toInt.2 ∧
      s.toInt.1 - a.toInt.1 = s.toInt.2 - a.toInt.2) ∨
    (t.toInt.1 - a.toInt.1 = -(t.toInt.2 - a.toInt.2) ∧
      s.toInt.1 - a.toInt.1 = -(s.toInt.2 - a.toInt.2)) := by
  obtain ⟨_, _, hc, hx0, hx1, hy0, hy1⟩ := hs
  rcases ha with h | h | h | h
  · left; constructor; exact h; rw [h] at hx0 hx1; simp only [min_self, max_self] at hx0 hx1; omega
  · right; left; constructor; exact h; rw [h] at hy0 hy1; simp only [min_self, max_self] at hy0 hy1; omega
  · by_cases hz : t.toInt.1 - a.toInt.1 = 0
    · left; constructor; omega; have he : a.toInt.1 = t.toInt.1 := by omega
      rw [he] at hx0 hx1; simp only [min_self, max_self] at hx0 hx1; omega
    · right; right; left; refine ⟨h, ?_⟩
      apply mul_right_cancel₀ hz
      rwa [← h] at hc
  · by_cases hz : t.toInt.1 - a.toInt.1 = 0
    · left; constructor; omega; have he : a.toInt.1 = t.toInt.1 := by omega
      rw [he] at hx0 hx1; simp only [min_self, max_self] at hx0 hx1; omega
    · right; right; right; refine ⟨h, ?_⟩
      apply mul_right_cancel₀ hz
      rw [show t.toInt.2 - a.toInt.2 = -(t.toInt.1 - a.toInt.1) by omega] at hc
      nlinarith only [hc]

theorem aligned_of_between {a t s : Pos} (ha : a.aligned t) (hs : Between a t s) :
    s.aligned t := by
  have h := between_line_cases ha hs
  unfold Pos.aligned
  omega

set_option maxHeartbeats 1000000 in
/-- A unit king step that opens an aligned checker's path leaves all four
line orientations through the target, provided both old and new kings are apart. -/
theorem not_aligned_of_king_step {a t s d : Pos} (ha : a.aligned t)
    (hs : Between a t s) (hd : ¬ Between a t d) (hda : d ≠ a) (hdt : d ≠ t)
    (hstep : attacks Board.empty ⟨.white, .king⟩ s d)
    (hsa : ¬ attacks Board.empty ⟨.white, .king⟩ s t)
    (hda' : ¬ attacks Board.empty ⟨.white, .king⟩ d t) : ¬ d.aligned t := by
  intro hal
  have hlines := between_line_cases ha hs
  have hsn := pos_ne hs.1
  have hstn := pos_ne hs.2.1
  have hapart0 : ¬ (|t.toInt.1 - s.toInt.1| ≤ 1 ∧ |t.toInt.2 - s.toInt.2| ≤ 1) :=
    fun h => hsa ⟨hs.2.1, h⟩
  have hdist : ¬ (|t.toInt.1 - d.toInt.1| ≤ 1 ∧ |t.toInt.2 - d.toInt.2| ≤ 1) :=
    fun h => hda' ⟨hdt, h⟩
  have hb := hs.2.2.2
  simp only [attacks, Pos.delta, abs_le] at hstep hapart0 hdist
  unfold Pos.aligned at hal
  have hld :
      (a.toInt.1 = t.toInt.1 ∧ s.toInt.1 = a.toInt.1 ∧ d.toInt.1 = a.toInt.1) ∨
      (a.toInt.2 = t.toInt.2 ∧ s.toInt.2 = a.toInt.2 ∧ d.toInt.2 = a.toInt.2) ∨
      (t.toInt.1 - a.toInt.1 = t.toInt.2 - a.toInt.2 ∧
        s.toInt.1 - a.toInt.1 = s.toInt.2 - a.toInt.2 ∧
        d.toInt.1 - a.toInt.1 = d.toInt.2 - a.toInt.2) ∨
      (t.toInt.1 - a.toInt.1 = -(t.toInt.2 - a.toInt.2) ∧
        s.toInt.1 - a.toInt.1 = -(s.toInt.2 - a.toInt.2) ∧
        d.toInt.1 - a.toInt.1 = -(d.toInt.2 - a.toInt.2)) := by
    clear ha hs hd hda hdt hsa hda' hb hsn hstn
    rcases hlines with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩
    · left; refine ⟨h, h', ?_⟩; omega
    · right; left; refine ⟨h, h', ?_⟩; omega
    · right; right; left; refine ⟨h, h', ?_⟩; omega
    · right; right; right; refine ⟨h, h', ?_⟩; omega
  apply hd
  refine ⟨hda, hdt, ?_, ?_⟩
  · rcases hld with ⟨h, _, he⟩ | ⟨h, _, he⟩ | ⟨h, _, he⟩ | ⟨h, _, he⟩
    · rw [← h, he]; ring
    · rw [← h, he]; ring
    · rw [h, he]
    · rw [h, he]; ring
  · clear ha hs hd hda hdt hsa hda' hal hlines hapart0 hdist
    rcases hld with ⟨h, h', he⟩ | ⟨h, h', he⟩ | ⟨h, h', he⟩ | ⟨h, h', he⟩ <;> omega

/-- A newly acquired attack after an ordinary update must be a sliding
attack whose path used the source but does not use the occupied destination. -/
theorem new_attack_source_between (b : Board) (src dst : Pos) (mover p : Piece) (a t : Pos)
    (hm : b src = some mover) (hn : ¬ attacks b p a t)
    (ha : attacks (b.relocate src dst none) p a t) :
    (p.kind = .queen ∨ p.kind = .rook ∨ p.kind = .bishop) ∧
      Between a t src ∧ ¬ Between a t dst := by
  have hd : b.relocate src dst none dst = some mover := by simp [hm, Piece.promote]
  have key (hpath : pathClear (b.relocate src dst none) a t)
      (hnot : ¬ pathClear b a t) : Between a t src ∧ ¬ Between a t dst := by
    have hdst : ¬ Between a t dst := by
      intro h
      have he := hpath dst h
      rw [hd] at he
      contradiction
    refine ⟨?_, hdst⟩
    by_contra hsrc
    apply hnot
    intro q hq
    have hs : q ≠ src := fun he => hsrc (he ▸ hq)
    have hd' : q ≠ dst := fun he => hdst (he ▸ hq)
    simpa only [Board.relocate_other b src dst q none hs hd'] using hpath q hq
  cases hk : p.kind with
  | king | knight | pawn => exact (hn (by simpa only [attacks, hk] using ha)).elim
  | queen =>
    simp only [attacks, hk] at ha hn
    exact ⟨Or.inl rfl, key ha.2.2 (fun h => hn ⟨ha.1, ha.2.1, h⟩)⟩
  | rook =>
    simp only [attacks, hk] at ha hn
    exact ⟨Or.inr (Or.inl rfl), key ha.2.2 (fun h => hn ⟨ha.1, ha.2.1, h⟩)⟩
  | bishop =>
    simp only [attacks, hk] at ha hn
    exact ⟨Or.inr (Or.inr rfl), key ha.2.2 (fun h => hn ⟨ha.1, ha.2.1, h⟩)⟩

end MPC.Chess
