import MPC.Basic.Lemmas
import MPC.Invariants.AnglePotential
/-!
# MPC.Invariants.DiscoveredCheckNecessity

Proposition 4.1 on traces: in a periodic
mutual-check trace each side makes a discovered check at some move.

Following the paper's §4, suppose a side `o` (the paper's "enemy") never does.
Then every move of `o` is a direct check, and 's angle potential for `o`
never rises: `o`'s moves keep it, and the other side's moves change it by
`iang m ≤ 0`. The trace returns to its first state, so the potential returns to
its first value (`anglePotential_last_eq`), and no step can lower it
(`eq_of_step_le_of_last_eq`). Hence every move of the other side captures the
checker it answers (Remark 4.4: `iang m = 0`). Each such capture adds a piece to
that side's hand, and `o`'s moves leave that hand alone
(`hand_card_succ_of_capture`, `hand_card_succ_of_turn_ne`). So its hand grows at
each of its moves, and it moves at least once (`exists_move_of_turn`), against
the periodicity. This is the paper's "the own hand would grow forever".

The paper's sum of `dang m` over all moves (Lemma 4.7) is the potential's sum
over non-glaring squares; no separate telescoping is needed.

-/

namespace MPC

/-- A rational sequence that never rises along `Fin (n + 1)` and ends where it
    starts is constant at every step. -/
theorem eq_of_step_le_of_last_eq {n : ℕ} (f : Fin (n + 1) → ℚ)
    (hstep : ∀ i : Fin n, f i.succ ≤ f i.castSucc) (hlast : f (Fin.last n) = f 0)
    (i : Fin n) : f i.succ = f i.castSucc := by
  have mono : ∀ (b : ℕ) (hb : b < n + 1) (a : ℕ) (hab : a ≤ b),
      f ⟨b, hb⟩ ≤ f ⟨a, by omega⟩ := by
    intro b
    induction b with
    | zero =>
      intro hb a hab
      obtain rfl : a = 0 := by omega
      exact le_rfl
    | succ b ih =>
      intro hb a hab
      rcases Nat.eq_or_lt_of_le hab with h | h
      · subst h
        exact le_rfl
      · exact le_trans (hstep ⟨b, by omega⟩) (ih (by omega) a (by omega))
  have h1 : f (Fin.last n) ≤ f i.succ := mono n (by omega) (i.val + 1) (by omega)
  have h2 : f i.castSucc ≤ f 0 := mono i.val (by omega) 0 (by omega)
  exact le_antisymm (hstep i) (by rw [hlast] at h1; exact le_trans h2 h1)

namespace MoveTrace

/-- The potential returns to its first value: the last state is the first, and the
    kings do not move. -/
theorem anglePotential_last_eq (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (hm : tr.MutualPerpetualCheck kp) (o : Player) :
    tr.anglePotential kp o (Fin.last tr.len) = tr.anglePotential kp o 0 := by
  have hgrid : ∀ q, (tr.states (Fin.last tr.len)).board.grid q = (tr.states 0).board.grid q :=
    fun q => by rw [hm.periodic]
  have hkp : kp (Fin.last tr.len) = kp 0 := hm.periodic.kingPos_last hm.kingsWellPlaced
  have hc : tr.checkerSquare kp (Fin.last tr.len) = tr.checkerSquare kp 0 := by
    symm
    apply tr.checkerSquare_eq_of_isCheckerAt kp hm
    obtain ⟨X, hX, hatk⟩ := tr.isCheckerAt_checkerSquare kp hm (Fin.last tr.len)
    refine ⟨X, by rw [← hgrid]; exact hX, ?_⟩
    rw [← hm.periodic, ← hkp]
    exact hatk
  have hs : tr.ownNonGlaringSquares kp o.opponent (Fin.last tr.len) =
      tr.ownNonGlaringSquares kp o.opponent 0 := by
    ext q
    rw [mem_ownNonGlaringSquares, mem_ownNonGlaringSquares, hgrid q,
      tr.glaresAtEnemyKing_congr kp hm.transitions (hgrid q) hkp]
  unfold anglePotential
  rw [hc, hs]

/-- A move leaves the other side's hand alone. -/
theorem hand_card_succ_of_turn_ne (tr : MoveTrace) (ht : tr.FollowsTransitions)
    (i : Fin tr.len) (p : Player) (hp : (tr.before i).turn ≠ p) :
    Multiset.card ((tr.after i).board.hand p) = Multiset.card ((tr.before i).board.hand p) := by
  rw [ht i]
  have hne : p ≠ (tr.before i).turn := fun h => hp h.symm
  cases tr.moves i with
  | boardMove src dst promote =>
    simp only [applyMove]
    split <;> simp [Board.setGrid, Board.addToHand, hne]
  | dropMove pt dst => simp [applyMove, Board.setGrid, Board.removeFromHand, hne]

/-- A capture adds the captured piece to the mover's hand. -/
theorem hand_card_succ_of_capture (tr : MoveTrace) (ht : tr.FollowsTransitions)
    (i : Fin tr.len) (src dst : Pos) (promote : Bool)
    (hmv : tr.moves i = .boardMove src dst promote) (X : Piece)
    (hX : (tr.before i).board.grid dst = some X) :
    Multiset.card ((tr.after i).board.hand (tr.before i).turn) =
      Multiset.card ((tr.before i).board.hand (tr.before i).turn) + 1 := by
  rw [ht i, hmv]
  simp only [applyMove, hX, Board.addToHand, Board.setGrid, ite_true, Multiset.card_add,
    Multiset.card_singleton]

/-- In a periodic mutual-check trace each side makes at least one move: the trace
    is not empty, and if the first move is one side's, the turn must come back. -/
theorem exists_move_of_turn (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (hm : tr.MutualPerpetualCheck kp) (p : Player) :
    ∃ i : Fin tr.len, (tr.before i).turn = p := by
  have hlen := hm.nonempty
  let i0 : Fin tr.len := ⟨0, hlen⟩
  rcases Player.eq_or_eq_opponent (tr.before i0).turn p with h | h
  · exact ⟨i0, h⟩
  · have hafter : (tr.after i0).turn = p := by
      rw [tr.turn_after_move hm.transitions, h]
      cases p <;> rfl
    by_cases h1 : tr.len = 1
    · exfalso
      have hl : i0.succ = Fin.last tr.len := Fin.ext (by simp [i0, h1])
      have h0 : (tr.states 0).turn = p := by
        rw [← hm.periodic, ← hl]
        exact hafter
      have hb : (tr.before i0).turn = (tr.states 0).turn := rfl
      rw [hb, h0] at h
      exact Player.opponent_ne_self p h.symm
    · refine ⟨⟨1, by omega⟩, ?_⟩
      have he : (⟨1, by omega⟩ : Fin tr.len).castSucc = i0.succ := Fin.ext rfl
      show (tr.states (⟨1, by omega⟩ : Fin tr.len).castSucc).turn = p
      rw [he]
      exact hafter

/-- Proposition 4.1: in a periodic mutual-check trace each side makes a discovered
    check, a move with an unblocked checker, at some move. -/
theorem discoveredCheckByEachSide_of_mutualPerpetualCheck (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp) :
    tr.DiscoveredCheckByEachSide kp := by
  intro o
  by_contra hno
  have hdirect : ∀ i : Fin tr.len, (tr.before i).turn = o →
      ¬ hasUnblockedCheckerOriented (tr.before i).board (tr.after i).board (tr.moves i)
        (tr.before i).turn.opponent (kp i.succ (tr.before i).turn.opponent) :=
    fun i hi hu => hno ⟨i, hi, hu⟩
  -- The potential never rises, and returns to its first value.
  have hstep : ∀ i : Fin tr.len,
      tr.anglePotential kp o i.succ ≤ tr.anglePotential kp o i.castSucc := by
    intro i
    rcases Player.eq_or_eq_opponent (tr.before i).turn o with h | h
    · exact (tr.anglePotential_succ_of_direct kp hm o i h (hdirect i h)).le
    · exact (tr.anglePotential_succ_le_of_turn_opponent kp hm o i h).1
  have hconst := eq_of_step_le_of_last_eq (tr.anglePotential kp o) hstep
    (tr.anglePotential_last_eq kp hm o)
  -- So every move of the other side captures the checker, and its hand grows.
  have hgrow : ∀ i : Fin tr.len, (tr.before i).turn = o.opponent →
      Multiset.card ((tr.after i).board.hand o.opponent) =
        Multiset.card ((tr.before i).board.hand o.opponent) + 1 := by
    intro i hi
    have hcap := (tr.anglePotential_succ_le_of_turn_opponent kp hm o i hi).2 (hconst i)
    obtain ⟨X, hX, _, _⟩ := tr.checkerSquare_before kp hm i
    rw [← hcap] at hX
    have key : ∀ mv : Move, tr.moves i = mv →
        Multiset.card ((tr.after i).board.hand o.opponent) =
          Multiset.card ((tr.before i).board.hand o.opponent) + 1 := by
      intro mv hmv
      cases mv with
      | boardMove src dst promote =>
        rw [hmv] at hX
        rw [← hi]
        exact tr.hand_card_succ_of_capture hm.transitions i src dst promote hmv X hX
      | dropMove pt dst =>
        rw [hmv] at hX
        have hX' : (tr.before i).board.grid dst = some X := hX
        rw [hm.dropsEmpty i pt dst hmv] at hX'
        cases hX'
    exact key _ rfl
  have hkeep : ∀ i : Fin tr.len, (tr.before i).turn = o →
      Multiset.card ((tr.after i).board.hand o.opponent) =
        Multiset.card ((tr.before i).board.hand o.opponent) := by
    intro i hi
    exact tr.hand_card_succ_of_turn_ne hm.transitions i o.opponent
      (by rw [hi]; exact (Player.opponent_ne_self o).symm)
  -- The hand size, negated, never rises and returns to its first value.
  let g : Fin (tr.len + 1) → ℚ :=
    fun k => -(Multiset.card ((tr.states k).board.hand o.opponent) : ℚ)
  have gstep : ∀ i : Fin tr.len, g i.succ ≤ g i.castSucc := by
    intro i
    show -(Multiset.card ((tr.after i).board.hand o.opponent) : ℚ) ≤
      -(Multiset.card ((tr.before i).board.hand o.opponent) : ℚ)
    rcases Player.eq_or_eq_opponent (tr.before i).turn o with h | h
    · rw [hkeep i h]
    · rw [hgrow i h]
      push_cast
      linarith
  have glast : g (Fin.last tr.len) = g 0 := by
    show -(Multiset.card ((tr.states (Fin.last tr.len)).board.hand o.opponent) : ℚ) =
      -(Multiset.card ((tr.states 0).board.hand o.opponent) : ℚ)
    rw [hm.periodic]
  obtain ⟨i, hi⟩ := tr.exists_move_of_turn kp hm o.opponent
  have he := eq_of_step_le_of_last_eq g gstep glast i
  have hc : -(Multiset.card ((tr.after i).board.hand o.opponent) : ℚ) =
      -(Multiset.card ((tr.before i).board.hand o.opponent) : ℚ) := he
  rw [hgrow i hi] at hc
  push_cast at hc
  linarith

end MoveTrace
end MPC
