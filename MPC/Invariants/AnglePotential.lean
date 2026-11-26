import MPC.Basic.Lemmas
import MPC.Invariants.CheckerAngle
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
/-!
# MPC.Invariants.AnglePotential

The angle potential of the paper's §4.

Fix a side `o` (the paper's "enemy"), its king `K = kp 0 o` and the other king
`L = kp 0 o.opponent`. The paper sums, over `o.opponent`'s moves, the changes
`ang m = iang m + dang m` of the checker's angle at `K`, and uses Lemma 4.7 to see
that the `dang` part sums to zero. Traces have no piece identities, so this file
adds the angles of `o.opponent`'s non-glaring pieces to the state instead:

  `anglePotential o k = θ (checkerSquare k) + Σ θ q` over `o.opponent`'s
  non-glaring squares `q` of state `k`, where `θ = angleKey K L`.

- `o`'s moves never change `o.opponent`'s non-glaring squares
  (`ownNonGlaringSquares_succ_of_opponent`). If such a move is a direct check, its
  checker makes the angle of the checker it answers, so the potential is
  unchanged (`anglePotential_succ_of_direct`).
- For a move of `o.opponent` with destination `C` answering the checker `Q`, the
  potential changes by `θ C - θ Q`, the paper's `iang m`
  (`anglePotential_succ_of_turn_opponent`):
  - a direct check moves a glaring piece, so the non-glaring squares stay
    (`ownNonGlaringSquares_succ_of_direct`), and the new checker is on `C`;
  - a discovered check moves a non-glaring piece from `D` to `C`
    (`ownNonGlaringSquares_succ_of_unblocked`), and the new checker makes the angle
    of `D` (Remark 4.5). The two `θ D` cancel, as in Lemma 4.7.
- So such a move never raises the potential, and leaves it unchanged only when it
  captures the checker (`anglePotential_succ_le_of_turn_opponent`, Remark 4.4).

-/

namespace MPC
namespace MoveTrace

open Classical in
/-- The squares of state `k` holding a non-glaring piece of `p`. -/
noncomputable def ownNonGlaringSquares (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (p : Player) (k : Fin (tr.len + 1)) : Finset Pos :=
  Finset.univ.filter fun q =>
    (∃ X : Piece, (tr.states k).board.grid q = some X ∧ X.owner = p) ∧
      ¬ tr.GlaresAtEnemyKing kp k q

theorem mem_ownNonGlaringSquares (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (p : Player) (k : Fin (tr.len + 1)) (q : Pos) :
    q ∈ tr.ownNonGlaringSquares kp p k ↔
      (∃ X : Piece, (tr.states k).board.grid q = some X ∧ X.owner = p) ∧
        ¬ tr.GlaresAtEnemyKing kp k q := by
  simp [ownNonGlaringSquares]

open Classical in
/-- The angle potential of state `k` for the side `o`: the angle key, at `o`'s king
    against the other king, of the checking square plus those of the other side's
    non-glaring squares. -/
noncomputable def anglePotential (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (o : Player) (k : Fin (tr.len + 1)) : ℚ :=
  angleKey (kp 0 o) (kp 0 o.opponent) (tr.checkerSquare kp k) +
    ∑ q ∈ tr.ownNonGlaringSquares kp o.opponent k, angleKey (kp 0 o) (kp 0 o.opponent) q

/-- A move's destination never held a non-glaring piece: removing one would lower
    the number of non-glaring squares, which is constant. -/
theorem destination_not_mem_nonGlaringSquares (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp) (i : Fin tr.len) :
    (tr.moves i).destination ∉ tr.nonGlaringSquares kp i.castSucc := by
  intro h
  have hd := tr.boardMoveEndpointsDistinct_of_oriented hm.sourcesOwned hm.movementRules
  have hkp : kp i.succ = kp i.castSucc := by
    rw [tr.kingPos_eq_of_mutualPerpetualCheck kp hm i.succ,
      tr.kingPos_eq_of_mutualPerpetualCheck kp hm i.castSucc]
  have hlt := tr.nonGlaringSquares_card_succ_lt_of_occupied_destination kp hm.transitions
    hm.sourcesOwned hm.kingsWellPlaced hm.ownKingSafe hm.initialOpponentSafe hm.checks hd i hkp h
  have e1 := tr.nonGlaringSquares_card_eq_of_periodic kp hm.transitions hm.sourcesOwned
    hm.kingsWellPlaced hm.ownKingSafe hm.initialOpponentSafe hm.checks hm.movementRules
    hm.periodic i.succ
  have e2 := tr.nonGlaringSquares_card_eq_of_periodic kp hm.transitions hm.sourcesOwned
    hm.kingsWellPlaced hm.ownKingSafe hm.initialOpponentSafe hm.checks hm.movementRules
    hm.periodic i.castSucc
  omega

/-- No side has a non-glaring piece on a move's destination before the move. -/
theorem destination_not_mem_ownNonGlaringSquares (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp) (i : Fin tr.len)
    (p : Player) : (tr.moves i).destination ∉ tr.ownNonGlaringSquares kp p i.castSucc := by
  intro h
  rw [mem_ownNonGlaringSquares] at h
  obtain ⟨⟨X, hX, _⟩, hng⟩ := h
  apply tr.destination_not_mem_nonGlaringSquares kp hm i
  rw [mem_nonGlaringSquares]
  exact ⟨by rw [hX]; exact Option.some_ne_none X, hng⟩

/-- A square the move does not touch keeps its membership. -/
theorem mem_ownNonGlaringSquares_succ_iff_of_untouched (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp) (i : Fin tr.len)
    (p : Player) (q : Pos) (hq : ¬ (tr.moves i).Touches q) :
    q ∈ tr.ownNonGlaringSquares kp p i.succ ↔
      q ∈ tr.ownNonGlaringSquares kp p i.castSucc := by
  have hg : (tr.states i.succ).board.grid q = (tr.states i.castSucc).board.grid q := by
    have key : ∀ mv : Move, tr.moves i = mv →
        (tr.after i).board.grid q = (tr.before i).board.grid q := by
      intro mv hmv
      rw [hmv] at hq
      cases mv with
      | boardMove src dst promote =>
        exact tr.boardMove_grid_other hm.transitions i src dst promote q hmv
          (fun h => hq (Or.inl h)) (fun h => hq (Or.inr h))
      | dropMove pt dst => exact tr.dropMove_grid_other hm.transitions i pt dst q hmv hq
    exact key _ rfl
  have hkp : kp i.succ = kp i.castSucc := by
    rw [tr.kingPos_eq_of_mutualPerpetualCheck kp hm i.succ,
      tr.kingPos_eq_of_mutualPerpetualCheck kp hm i.castSucc]
  rw [mem_ownNonGlaringSquares, mem_ownNonGlaringSquares, hg,
    tr.glaresAtEnemyKing_congr kp hm.transitions hg hkp]

/-- After a move, the destination holds a piece of the mover. -/
private theorem destination_owner_succ (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (hm : tr.MutualPerpetualCheck kp) (i : Fin tr.len) :
    ∃ X : Piece, (tr.after i).board.grid (tr.moves i).destination = some X ∧
      X.owner = (tr.before i).turn := by
  have key : ∀ mv : Move, tr.moves i = mv →
      ∃ X : Piece, (tr.after i).board.grid mv.destination = some X ∧
        X.owner = (tr.before i).turn := by
    intro mv hmv
    cases mv with
    | boardMove src dst promote =>
      obtain ⟨piece, hp, ho⟩ := hm.sourcesOwned i src dst promote hmv
      refine ⟨{ piece with pieceType := if promote then piece.pieceType.promote
          else piece.pieceType }, ?_, ho⟩
      show (tr.after i).board.grid dst = _
      rw [tr.boardMove_grid_dst hm.transitions i src dst promote hmv, hp]
    | dropMove pt dst => exact ⟨_, tr.dropMove_grid_dst hm.transitions i pt dst hmv, rfl⟩
  obtain ⟨X, hX, ho⟩ := key _ rfl
  exact ⟨X, hX, ho⟩

/-- A move never changes the other side's non-glaring squares: its source and
    destination hold the mover's pieces or nothing, and a non-glaring piece is never
    captured. -/
theorem ownNonGlaringSquares_succ_of_opponent (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp) (i : Fin tr.len) :
    tr.ownNonGlaringSquares kp (tr.before i).turn.opponent i.succ =
      tr.ownNonGlaringSquares kp (tr.before i).turn.opponent i.castSucc := by
  have hne := Player.opponent_ne_self (tr.before i).turn
  ext q
  by_cases hq : (tr.moves i).Touches q
  · -- `q` is the source or the destination: a member on neither side.
    have hdst : q = (tr.moves i).destination ∨
        ∃ src dst promote, tr.moves i = .boardMove src dst promote ∧ q = src ∧ q ≠ dst := by
      have key : ∀ mv : Move, tr.moves i = mv → mv.Touches q →
          q = mv.destination ∨
            ∃ src dst promote, tr.moves i = .boardMove src dst promote ∧
              q = src ∧ q ≠ dst := by
        intro mv hmv ht
        cases mv with
        | boardMove src dst promote =>
          rcases ht with h | h
          · by_cases hqd : q = dst
            · exact Or.inl hqd
            · exact Or.inr ⟨src, dst, promote, hmv, h, hqd⟩
          · exact Or.inl h
        | dropMove pt dst => exact Or.inl ht
      have h := key _ rfl hq
      exact h
    constructor
    · intro h
      exfalso
      rcases hdst with rfl | ⟨src, dst, promote, hmv, rfl, hqd⟩
      · obtain ⟨⟨X, hX, hXo⟩, _⟩ := (tr.mem_ownNonGlaringSquares kp _ _ _).mp h
        obtain ⟨Y, hY, hYo⟩ := tr.destination_owner_succ kp hm i
        have : X = Y := Option.some.inj (hX.symm.trans hY)
        exact hne (hXo.symm.trans (this ▸ hYo))
      · obtain ⟨⟨X, hX, _⟩, _⟩ := (tr.mem_ownNonGlaringSquares kp _ _ _).mp h
        have hsd : q ≠ dst := hqd
        rw [show (tr.states i.succ).board.grid q = none from
          tr.boardMove_grid_src hm.transitions i q dst promote hmv hsd] at hX
        cases hX
    · intro h
      exfalso
      rcases hdst with rfl | ⟨src, dst, promote, hmv, rfl, _⟩
      · exact tr.destination_not_mem_ownNonGlaringSquares kp hm i _ h
      · obtain ⟨⟨X, hX, hXo⟩, _⟩ := (tr.mem_ownNonGlaringSquares kp _ _ _).mp h
        obtain ⟨piece, hp, ho⟩ := hm.sourcesOwned i q dst promote hmv
        have : X = piece := Option.some.inj (hX.symm.trans hp)
        exact hne (hXo.symm.trans (this ▸ ho))
  · exact tr.mem_ownNonGlaringSquares_succ_iff_of_untouched kp hm i _ q hq

/-- A direct check keeps the mover's non-glaring squares: the checker on the
    destination glares, so the moved piece glared at its source too (Lemma 2.8). -/
theorem ownNonGlaringSquares_succ_of_direct (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp) (i : Fin tr.len)
    (hdir : tr.checkerSquare kp i.succ = (tr.moves i).destination) :
    tr.ownNonGlaringSquares kp (tr.before i).turn i.succ =
      tr.ownNonGlaringSquares kp (tr.before i).turn i.castSucc := by
  -- The destination glares after the move.
  have hgd : tr.GlaresAtEnemyKing kp i.succ (tr.moves i).destination := by
    obtain ⟨X, hX, hatk⟩ := tr.isCheckerAt_checkerSquare kp hm i.succ
    rw [hdir] at hX hatk
    exact tr.glaresAtEnemyKing_of_attacks kp i.succ _ X hX hatk
  ext q
  by_cases hq : (tr.moves i).Touches q
  · constructor
    · intro h
      exfalso
      obtain ⟨⟨X, hX, _⟩, hng⟩ := (tr.mem_ownNonGlaringSquares kp _ _ _).mp h
      have key : ∀ mv : Move, tr.moves i = mv → False := by
        intro mv hmv
        have hq' := hq
        rw [hmv] at hq'
        cases mv with
        | boardMove src dst promote =>
          rcases hq' with rfl | rfl
          · by_cases hsd : q = dst
            · subst hsd
              exact hng (by simpa [hmv, Move.destination] using hgd)
            · rw [show (tr.states i.succ).board.grid q = none from
                tr.boardMove_grid_src hm.transitions i q dst promote hmv hsd] at hX
              cases hX
          · exact hng (by simpa [hmv, Move.destination] using hgd)
        | dropMove pt dst =>
          have hqd : q = dst := hq'
          subst hqd
          exact hng (by simpa [hmv, Move.destination] using hgd)
      exact key _ rfl
    · intro h
      exfalso
      obtain ⟨⟨X, hX, hXo⟩, hng⟩ := (tr.mem_ownNonGlaringSquares kp _ _ _).mp h
      have key : ∀ mv : Move, tr.moves i = mv → False := by
        intro mv hmv
        have hq' := hq
        rw [hmv] at hq'
        cases mv with
        | boardMove src dst promote =>
          rcases hq' with rfl | rfl
          · -- The source: the moved piece glared there (Lemma 2.8).
            have hgd' : tr.GlaresAtEnemyKing kp i.succ dst := by
              simpa [hmv, Move.destination] using hgd
            exact hng ((tr.glares_destination_iff_source_of_periodic kp hm.transitions
              hm.sourcesOwned hm.kingsWellPlaced hm.ownKingSafe hm.initialOpponentSafe hm.checks
              hm.movementRules hm.periodic i q dst promote hmv).mp hgd')
          · exact tr.destination_not_mem_ownNonGlaringSquares kp hm i _
              (by simpa [hmv, Move.destination] using h)
        | dropMove pt dst =>
          have hqd : q = dst := hq'
          subst hqd
          exact tr.destination_not_mem_ownNonGlaringSquares kp hm i _
            (by simpa [hmv, Move.destination] using h)
      exact key _ rfl
  · exact tr.mem_ownNonGlaringSquares_succ_iff_of_untouched kp hm i _ q hq

/-- A board move with an unblocked checker moves a non-glaring piece of the mover
    from its source to its destination, where it stays non-glaring (Lemmas 2.5, 2.6). -/
theorem ownNonGlaringSquares_succ_of_unblocked (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp) (i : Fin tr.len)
    (src dst : Pos) (promote : Bool) (hmv : tr.moves i = .boardMove src dst promote)
    (hu : hasUnblockedCheckerOriented (tr.before i).board (tr.after i).board (tr.moves i)
      (tr.before i).turn.opponent (kp i.succ (tr.before i).turn.opponent)) :
    src ∈ tr.ownNonGlaringSquares kp (tr.before i).turn i.castSucc ∧
      dst ∉ (tr.ownNonGlaringSquares kp (tr.before i).turn i.castSucc).erase src ∧
      tr.ownNonGlaringSquares kp (tr.before i).turn i.succ =
        insert dst ((tr.ownNonGlaringSquares kp (tr.before i).turn i.castSucc).erase src) := by
  have hsd : src ≠ dst :=
    tr.boardMoveEndpointsDistinct_of_oriented hm.sourcesOwned hm.movementRules i src dst promote hmv
  have hng_src : ¬ tr.GlaresAtEnemyKing kp i.castSucc src := fun hg =>
    tr.not_unblockedChecker_of_source_glares kp hm.transitions hm.sourcesOwned hm.kingsWellPlaced
      hm.ownKingSafe hm.initialOpponentSafe i src dst promote hmv hg hu
  have hng_dst : ¬ tr.GlaresAtEnemyKing kp i.succ dst := fun hg =>
    hng_src ((tr.glares_destination_iff_source_of_periodic kp hm.transitions hm.sourcesOwned
      hm.kingsWellPlaced hm.ownKingSafe hm.initialOpponentSafe hm.checks hm.movementRules
      hm.periodic i src dst promote hmv).mp hg)
  obtain ⟨piece, hp, ho⟩ := hm.sourcesOwned i src dst promote hmv
  have hsrc : src ∈ tr.ownNonGlaringSquares kp (tr.before i).turn i.castSucc :=
    (tr.mem_ownNonGlaringSquares kp _ _ _).mpr ⟨⟨piece, hp, ho⟩, hng_src⟩
  have hdst0 : dst ∉ tr.ownNonGlaringSquares kp (tr.before i).turn i.castSucc := by
    have h := tr.destination_not_mem_ownNonGlaringSquares kp hm i (tr.before i).turn
    rw [hmv] at h
    exact h
  refine ⟨hsrc, fun h => hdst0 (Finset.mem_of_mem_erase h), ?_⟩
  ext q
  rw [Finset.mem_insert, Finset.mem_erase]
  by_cases hqd : q = dst
  · subst hqd
    simp only [true_or, iff_true]
    obtain ⟨Y, hY, hYo⟩ := tr.destination_owner_succ kp hm i
    rw [hmv] at hY
    exact (tr.mem_ownNonGlaringSquares kp _ _ _).mpr ⟨⟨Y, hY, hYo⟩, hng_dst⟩
  · by_cases hqs : q = src
    · subst hqs
      constructor
      · intro h
        exfalso
        obtain ⟨⟨X, hX, _⟩, _⟩ := (tr.mem_ownNonGlaringSquares kp _ _ _).mp h
        rw [show (tr.states i.succ).board.grid q = none from
          tr.boardMove_grid_src hm.transitions i q dst promote hmv hsd] at hX
        cases hX
      · rintro (h | ⟨hne, _⟩)
        · exact absurd h hqd
        · exact absurd rfl hne
    · simp only [hqd, false_or, ne_eq, hqs, not_false_eq_true, true_and]
      refine tr.mem_ownNonGlaringSquares_succ_iff_of_untouched kp hm i _ q ?_
      rw [hmv]
      rintro (h | h)
      · exact hqs h
      · exact hqd h

/-- The paper's "enemy" makes a direct check: the potential does not change. Its
    checker makes the angle of the checker it answers, and the other side's
    non-glaring squares stay. -/
theorem anglePotential_succ_of_direct (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (hm : tr.MutualPerpetualCheck kp) (o : Player) (i : Fin tr.len)
    (hturn : (tr.before i).turn = o)
    (hdir : ¬ hasUnblockedCheckerOriented (tr.before i).board (tr.after i).board (tr.moves i)
      (tr.before i).turn.opponent (kp i.succ (tr.before i).turn.opponent)) :
    tr.anglePotential kp o i.succ = tr.anglePotential kp o i.castSucc := by
  have hc : tr.checkerSquare kp i.succ = (tr.moves i).destination := by
    rcases tr.checkerSquare_succ_cases kp hm i with h | ⟨_, _, _, _, hu, _⟩
    · exact h
    · exact absurd hu hdir
  have hθ := tr.angleKey_destination_eq_checker kp hm i (kp 0 o.opponent)
  rw [hturn, tr.kingPos_eq_of_mutualPerpetualCheck kp hm i.castSucc] at hθ
  have hset := tr.ownNonGlaringSquares_succ_of_opponent kp hm i
  rw [hturn] at hset
  unfold anglePotential
  rw [hc, hθ, hset]

/-- A move of the other side changes the potential by `θ C - θ Q`, for its
    destination `C` and the checker `Q` it answers: the paper's `iang m`. -/
theorem anglePotential_succ_of_turn_opponent (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp) (o : Player)
    (i : Fin tr.len) (hturn : (tr.before i).turn = o.opponent) :
    tr.anglePotential kp o i.succ = tr.anglePotential kp o i.castSucc +
      (angleKey (kp 0 o) (kp 0 o.opponent) (tr.moves i).destination -
        angleKey (kp 0 o) (kp 0 o.opponent) (tr.checkerSquare kp i.castSucc)) := by
  unfold anglePotential
  rcases tr.checkerSquare_succ_cases kp hm i with hc | ⟨src, dst, promote, hmv, hu, hθ⟩
  · -- A direct check.
    have hset := tr.ownNonGlaringSquares_succ_of_direct kp hm i hc
    rw [hturn] at hset
    rw [hc, hset]
    ring
  · -- A discovered check: the source's key moves from the sum to the checker.
    obtain ⟨hsrc, hdst, hset⟩ :=
      tr.ownNonGlaringSquares_succ_of_unblocked kp hm i src dst promote hmv hu
    rw [hturn] at hsrc hdst hset
    have hθ' := hθ (kp 0 o.opponent)
    rw [hturn, Player.opponent_opponent, tr.kingPos_eq_of_mutualPerpetualCheck kp hm i.succ] at hθ'
    rw [hθ', hset, Finset.sum_insert hdst, hmv]
    rw [← Finset.add_sum_erase _ _ hsrc]
    simp only [Move.destination]
    ring

/-- Remark 4.4 for the potential: a move of the other side never raises it, and
    leaves it unchanged only when it captures the checker. -/
theorem anglePotential_succ_le_of_turn_opponent (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp) (o : Player)
    (i : Fin tr.len) (hturn : (tr.before i).turn = o.opponent) :
    tr.anglePotential kp o i.succ ≤ tr.anglePotential kp o i.castSucc ∧
      (tr.anglePotential kp o i.succ = tr.anglePotential kp o i.castSucc →
        (tr.moves i).destination = tr.checkerSquare kp i.castSucc) := by
  rw [tr.anglePotential_succ_of_turn_opponent kp hm o i hturn]
  have hside : lineSide (kp 0 o) (kp i.castSucc (tr.before i).turn)
      (tr.checkerSquare kp i.castSucc) ≠ 0 := by
    rw [hturn, tr.kingPos_eq_of_mutualPerpetualCheck kp hm i.castSucc]
    exact tr.lineSide_kings_checkerSquare_ne_zero kp hm i.castSucc o
  have h := tr.destination_eq_or_angleKey_lt_checker kp hm i (kp 0 o) hside
  rw [hturn, tr.kingPos_eq_of_mutualPerpetualCheck kp hm i.castSucc] at h
  rcases h with h | h
  · rw [h]
    simp
  · constructor
    · linarith
    · intro he
      exfalso
      linarith

end MoveTrace
end MPC
