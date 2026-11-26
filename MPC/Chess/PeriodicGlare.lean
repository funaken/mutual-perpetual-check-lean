import MPC.Chess.GlaringMove
import Mathlib.Data.Finset.Card

/-! Periodic preservation of glare classification (the paper's Lemma 2.8).
Count occupied non-glaring squares without assigning identities to pieces.
The local count lemmas expose fixed kings and forward glare preservation;
periodic legal mutual checks supply both premises and forbid a strict loss.
Captures are already excluded by the stronger material reduction in Part 3. -/

namespace MPC.Chess.MoveTrace

/-- Empty squares do not contribute, even though they cannot glare. -/
def nonGlaringSquares (tr : MoveTrace) (kp : Fin (tr.len + 1) → Color → Pos)
    (k : Fin (tr.len + 1)) : Finset Pos :=
  Finset.univ.filter fun q => (tr.states k).board q ≠ none ∧ ¬ tr.GlaresAtEnemyKing kp k q

theorem mem_nonGlaringSquares (tr : MoveTrace) (kp : Fin (tr.len + 1) → Color → Pos)
    (k : Fin (tr.len + 1)) (q : Pos) :
    q ∈ tr.nonGlaringSquares kp k ↔
      (tr.states k).board q ≠ none ∧ ¬ tr.GlaresAtEnemyKing kp k q := by
  simp [nonGlaringSquares]

/-- Keeping the same piece at a square and the same king positions preserves
its glare. Movable blockers elsewhere do not enter the stripped board. -/
theorem glares_congr (tr : MoveTrace) (kp : Fin (tr.len + 1) → Color → Pos)
    (hl : tr.FollowsLegalMoves) {k l : Fin (tr.len + 1)} {q : Pos}
    (hq : (tr.states k).board q = (tr.states l).board q) (hkp : kp k = kp l) :
    tr.GlaresAtEnemyKing kp k q ↔ tr.GlaresAtEnemyKing kp l q := by
  have hb : tr.strippedBoard k q = tr.strippedBoard l q := by
    funext r
    simp only [strippedBoard]
    split_ifs with hr
    · rcases hr with rfl | hi
      · exact hq
      · exact tr.immovable_board_eq hl r hi k l
    · rfl
  simp only [GlaresAtEnemyKing, hq, hb, hkp]

private theorem boardMove_facts (tr : MoveTrace) (hl : tr.FollowsLegalMoves)
    (i : Fin tr.len) (src dst : Pos) (hm : tr.moves i = .boardMove src dst none) :
    ∃ p, (tr.before i).board src = some p ∧ src ≠ dst ∧
      (tr.after i).board = (tr.before i).board.relocate src dst none := by
  obtain ⟨_, hv, he⟩ := hl i
  have hv' : PseudoLegal (tr.before i) (.boardMove src dst none) := by
    simpa only [hm] using hv.movement
  obtain ⟨p, hs, _, hne, _⟩ := hv'
  refine ⟨p, hs, hne, ?_⟩
  rw [he, hm]; rfl

private theorem boardMove_mapsTo (tr : MoveTrace) (kp : Fin (tr.len + 1) → Color → Pos)
    (hl : tr.FollowsLegalMoves) (i : Fin tr.len) (src dst : Pos)
    (hm : tr.moves i = .boardMove src dst none) (hkp : kp i.succ = kp i.castSucc)
    (hg : tr.GlaresAtEnemyKing kp i.castSucc src → tr.GlaresAtEnemyKing kp i.succ dst)
    (q : Pos) (hq : q ∈ tr.nonGlaringSquares kp i.succ) :
    (if q = dst then src else q) ∈ tr.nonGlaringSquares kp i.castSucc ∧ q ≠ src := by
  obtain ⟨p, hs, hne, he⟩ := tr.boardMove_facts hl i src dst hm
  obtain ⟨hocc, hng⟩ := (tr.mem_nonGlaringSquares kp i.succ q).mp hq
  by_cases hd : q = dst
  · subst q
    rw [ite_eq_left rfl]
    refine ⟨(tr.mem_nonGlaringSquares kp i.castSucc src).mpr ⟨?_, fun h => hng (hg h)⟩, hne.symm⟩
    change (tr.before i).board src ≠ none
    rw [hs]; exact Option.some_ne_none _
  · rw [ite_eq_right hd]
    have hqs : q ≠ src := by
      intro hqs
      subst q
      apply hocc
      change (tr.after i).board src = none
      rw [he, Board.relocate_source _ _ _ _ hne]
    have hb : (tr.states i.succ).board q = (tr.states i.castSucc).board q := by
      change (tr.after i).board q = (tr.before i).board q
      rw [he, Board.relocate_other _ _ _ _ _ hqs hd]
    refine ⟨(tr.mem_nonGlaringSquares kp i.castSucc q).mpr ⟨hb ▸ hocc, ?_⟩, hqs⟩
    exact fun h => hng ((tr.glares_congr kp hl hb hkp).mpr h)

private theorem boardMove_injOn (tr : MoveTrace) (kp : Fin (tr.len + 1) → Color → Pos)
    (hl : tr.FollowsLegalMoves) (i : Fin tr.len) (src dst : Pos)
    (hm : tr.moves i = .boardMove src dst none) :
    Set.InjOn (fun q => if q = dst then src else q) (tr.nonGlaringSquares kp i.succ : Set Pos) := by
  obtain ⟨_, _, hne, he⟩ := tr.boardMove_facts hl i src dst hm
  have hsrc (q : Pos) (hq : q ∈ tr.nonGlaringSquares kp i.succ) : q ≠ src := by
    intro hqs
    subst q
    apply ((tr.mem_nonGlaringSquares kp i.succ src).mp hq).1
    change (tr.after i).board src = none
    rw [he, Board.relocate_source _ _ _ _ hne]
  intro q₁ h₁ q₂ h₂ heq
  simp only at heq
  by_cases h₁d : q₁ = dst <;> by_cases h₂d : q₂ = dst
  · rw [h₁d, h₂d]
  · rw [ite_eq_left h₁d, ite_eq_right h₂d] at heq
    exact (hsrc q₂ h₂ heq.symm).elim
  · rw [ite_eq_right h₁d, ite_eq_left h₂d] at heq
    exact (hsrc q₁ h₁ heq).elim
  · rwa [ite_eq_right h₁d, ite_eq_right h₂d] at heq

/-- Local monotonicity, without periodicity. The source-to-destination glare
implication is explicit here and is supplied by Lemma 2.6 in the periodic use. -/
theorem nonGlaringSquares_card_succ_le (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (i : Fin tr.len) (src dst : Pos) (hm : tr.moves i = .boardMove src dst none)
    (hkp : kp i.succ = kp i.castSucc)
    (hg : tr.GlaresAtEnemyKing kp i.castSucc src → tr.GlaresAtEnemyKing kp i.succ dst) :
    (tr.nonGlaringSquares kp i.succ).card ≤ (tr.nonGlaringSquares kp i.castSucc).card :=
  Finset.card_le_card_of_injOn _
    (fun q hq => (tr.boardMove_mapsTo kp hl i src dst hm hkp hg q hq).1)
    (tr.boardMove_injOn kp hl i src dst hm)

/-- Moving a non-glaring piece to a glaring square strictly decreases the
count. This local statement can be exercised on nonperiodic legal prefixes. -/
theorem nonGlaringSquares_card_succ_lt_of_new_glare (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (i : Fin tr.len) (src dst : Pos) (hm : tr.moves i = .boardMove src dst none)
    (hkp : kp i.succ = kp i.castSucc)
    (hsrc : ¬ tr.GlaresAtEnemyKing kp i.castSucc src)
    (hdst : tr.GlaresAtEnemyKing kp i.succ dst) :
    (tr.nonGlaringSquares kp i.succ).card < (tr.nonGlaringSquares kp i.castSucc).card := by
  have hs : src ∈ tr.nonGlaringSquares kp i.castSucc := by
    refine (tr.mem_nonGlaringSquares kp i.castSucc src).mpr ⟨?_, hsrc⟩
    obtain ⟨p, hp, _⟩ := tr.boardMove_facts hl i src dst hm
    change (tr.before i).board src ≠ none
    rw [hp]; exact Option.some_ne_none _
  refine lt_of_le_of_lt (Finset.card_le_card_of_injOn (fun q => if q = dst then src else q) ?_
    (tr.boardMove_injOn kp hl i src dst hm)) (Finset.card_erase_lt_of_mem hs)
  intro q hq
  have hg : tr.GlaresAtEnemyKing kp i.castSucc src → tr.GlaresAtEnemyKing kp i.succ dst :=
    fun h => (hsrc h).elim
  obtain ⟨hmap, hqs⟩ := tr.boardMove_mapsTo kp hl i src dst hm hkp hg q hq
  have hqd : q ≠ dst := by
    intro hqd
    subst q
    exact ((tr.mem_nonGlaringSquares kp i.succ dst).mp hq).2 hdst
  simp only [ite_eq_right hqd] at hmap ⊢
  exact Finset.mem_erase.mpr ⟨hqs, hmap⟩

/-- The non-glaring count is constant across all states, including the empty
trace and reversed state pairs. Recurrence compares board and turn, without
requiring the castling rights or en-passant data to recur. -/
theorem nonGlaringSquares_card_eq_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (k l : Fin (tr.len + 1)) :
    (tr.nonGlaringSquares kp k).card = (tr.nonGlaringSquares kp l).card := by
  have hconst := tr.kingPositions_eq_of_periodic_checks kp hl hk hc hp
  have hstep (i : Fin tr.len) :
      (tr.nonGlaringSquares kp i.succ).card ≤ (tr.nonGlaringSquares kp i.castSucc).card := by
    obtain ⟨src, dst, _, hm, _⟩ := tr.ordinary_nonKing_nonPawn_move_of_periodic_checks kp hl hk hc hp i
    exact tr.nonGlaringSquares_card_succ_le kp hl i src dst hm (hconst _ _)
      (tr.destination_glares_of_source_glares kp hl hk hc hp i src dst hm)
  have hmono : Antitone (fun k => (tr.nonGlaringSquares kp k).card) :=
    Fin.antitone_iff_succ_le.mpr hstep
  have hlast : tr.nonGlaringSquares kp (Fin.last tr.len) = tr.nonGlaringSquares kp 0 := by
    ext q
    have hb : (tr.states (Fin.last tr.len)).board q = (tr.states 0).board q := by rw [hp.1]
    rw [tr.mem_nonGlaringSquares, tr.mem_nonGlaringSquares, hb,
      tr.glares_congr kp hl hb (hconst _ _)]
  have hz (j : Fin (tr.len + 1)) :
      (tr.nonGlaringSquares kp j).card = (tr.nonGlaringSquares kp 0).card := by
    have h₁ := hmono (Fin.zero_le j)
    have h₂ := hmono (Fin.le_last j)
    dsimp only at h₁ h₂
    rw [hlast] at h₂
    omega
  exact (hz k).trans (hz l).symm

/-- Lemma 2.8: a move to a glaring square must have started at a glaring square.
The missing converse in Lemma 2.6 follows from recurrence of the finite count. -/
theorem glares_source_of_destination_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) (src dst : Pos)
    (hm : tr.moves i = .boardMove src dst none)
    (hd : tr.GlaresAtEnemyKing kp i.succ dst) : tr.GlaresAtEnemyKing kp i.castSucc src := by
  by_contra hs
  have hlt := tr.nonGlaringSquares_card_succ_lt_of_new_glare kp hl i src dst hm
    (tr.kingPositions_eq_of_periodic_checks kp hl hk hc hp _ _) hs hd
  have he := tr.nonGlaringSquares_card_eq_of_periodic_checks kp hl hk hc hp i.succ i.castSucc
  omega

theorem glares_destination_iff_source_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) (src dst : Pos)
    (hm : tr.moves i = .boardMove src dst none) :
    tr.GlaresAtEnemyKing kp i.succ dst ↔ tr.GlaresAtEnemyKing kp i.castSucc src :=
  ⟨tr.glares_source_of_destination_of_periodic_checks kp hl hk hc hp i src dst hm,
    tr.destination_glares_of_source_glares kp hl hk hc hp i src dst hm⟩

/-- The same classification is also preserved for every non-endpoint square. -/
theorem glares_other_iff_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) (src dst q : Pos)
    (hm : tr.moves i = .boardMove src dst none) (hs : q ≠ src) (hd : q ≠ dst) :
    tr.GlaresAtEnemyKing kp i.succ q ↔ tr.GlaresAtEnemyKing kp i.castSucc q := by
  obtain ⟨_, _, _, he⟩ := tr.boardMove_facts hl i src dst hm
  apply tr.glares_congr kp hl _ (tr.kingPositions_eq_of_periodic_checks kp hl hk hc hp _ _)
  change (tr.after i).board q = (tr.before i).board q
  rw [he, Board.relocate_other _ _ _ _ _ hs hd]

/-- A non-glaring mover gives an unblocked check, and only such a mover does. -/
theorem unblockedChecker_iff_not_source_glares_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) (src dst : Pos)
    (hm : tr.moves i = .boardMove src dst none) :
    hasUnblockedChecker (tr.before i).board (tr.after i).board src dst
      (tr.before i).turn.opponent (kp i.succ (tr.before i).turn.opponent) ↔
      ¬ tr.GlaresAtEnemyKing kp i.castSucc src := by
  constructor
  · intro hu hg
    exact tr.not_unblockedChecker_of_source_glares kp hl hk hc hp i src dst hm hg hu
  · intro hg
    apply tr.unblockedChecker_of_destination_not_glares kp hl hk hc hp i src dst hm
    exact fun hd => hg (tr.glares_source_of_destination_of_periodic_checks kp hl hk hc hp i src dst hm hd)

/-- In the periodic setting destination checks are precisely the moves of
already-glaring pieces. Together with the previous theorem this excludes double
checks here, while the local board classification remains inclusive. -/
theorem destinationChecker_iff_source_glares_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) (src dst : Pos)
    (hm : tr.moves i = .boardMove src dst none) :
    hasDestinationChecker (tr.after i).board dst (tr.before i).turn.opponent
      (kp i.succ (tr.before i).turn.opponent) ↔ tr.GlaresAtEnemyKing kp i.castSucc src := by
  constructor
  · intro hd
    exact tr.glares_source_of_destination_of_periodic_checks kp hl hk hc hp i src dst hm
      (tr.glares_of_destinationChecker kp i.succ dst _ hd)
  · exact tr.destinationChecker_of_source_glares kp hl hk hc hp i src dst hm

end MPC.Chess.MoveTrace
