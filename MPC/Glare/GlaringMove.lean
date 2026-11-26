import MPC.Basic.Lemmas
import MPC.Glare.TraceGlare
/-!
# MPC.Glare.GlaringMove

The paper's Lemma 2.5 on independent traces: moving a piece that glares at the
enemy king is not a discovered check. An unblocked checker's line passes through
the source and avoids the destination, so before the move the segment from the
source to the king is already clear. A piece at the source that reaches the king
on some board (for a glare, the stripped board) would therefore already give
check, contradicting the unchecked start. With the stated transition and safety premises and every move
checking, a glaring piece's move is a direct check and its destination glares
(Lemma 2.6). No GameSeq, periodicity, or global immovability premise is used.
-/

namespace MPC

private theorem toPos_eq_int (q : ℤ × ℤ) (h : onBoard q) (p : Pos)
    (he : toPos q h = p) : q = p.toInt := by
  subst p
  have h1 := h.1
  have h2 := h.2.2.1
  ext <;> simp [toPos, Pos.toInt] <;> omega

/-- Direction and step data of an attack do not depend on the board; only path
    clearance does. -/
theorem attacksOriented_of_pathClear (S board : Board) (owner : Player) (pt : PieceType)
    (src dst : Pos) (h : attacksOriented S owner pt src dst)
    (hc : pathClear board src dst) : attacksOriented board owner pt src dst := by
  rcases h with hs | ⟨sd, hsd, hn, k, hk, hx, hy, _⟩
  · exact Or.inl hs
  · exact Or.inr ⟨sd, hsd, hn, k, hk, hx, hy, hc⟩

/-- Beyond an intermediate point of an exact slide, the remaining segment lies on
    the original path and avoids that point. -/
theorem mem_slidePath_of_mem_tail (pos src target : Pos) (d : Dir) (n : ℕ)
    (hd : d ≠ (0, 0)) (hn : 1 ≤ n) (hdir : (Pos.dirTo pos target).normalize = d)
    (hx : target.toInt.1 = pos.toInt.1 + ↑n * d.1)
    (hy : target.toInt.2 = pos.toInt.2 + ↑n * d.2)
    (hmem : src.toInt ∈ slidePath pos target) (q : ℤ × ℤ)
    (hq : q ∈ slidePath src target) :
    q ∈ slidePath pos target ∧ q ≠ src.toInt := by
  have hm := mem_slidePath_iff_of_exact_steps pos target d n hd hn hdir hx hy
  obtain ⟨j, hj, hjn, hsrc⟩ := (hm src.toInt).mp hmem
  have hs1 : src.toInt.1 = pos.toInt.1 + ↑j * d.1 := by rw [hsrc]
  have hs2 : src.toInt.2 = pos.toInt.2 + ↑j * d.2 := by rw [hsrc]
  have hx' : target.toInt.1 = src.toInt.1 + ↑(n - j) * d.1 := by
    rw [hx, hs1, Nat.cast_sub hjn.le]; ring
  have hy' : target.toInt.2 = src.toInt.2 + ↑(n - j) * d.2 := by
    rw [hy, hs2, Nat.cast_sub hjn.le]; ring
  have hpos : (0 : ℤ) < ((n - j : ℕ) : ℤ) := by
    have : 0 < n - j := by omega
    exact_mod_cast this
  have hd1 : Int.sign d.1 = d.1 := by subst hdir; exact Int.sign_sign
  have hd2 : Int.sign d.2 = d.2 := by subst hdir; exact Int.sign_sign
  have hdir' : (Pos.dirTo src target).normalize = d := by
    have e1 : (Pos.dirTo src target).1 = ↑(n - j) * d.1 := by
      change target.toInt.1 - src.toInt.1 = _
      rw [hx']; ring
    have e2 : (Pos.dirTo src target).2 = ↑(n - j) * d.2 := by
      change target.toInt.2 - src.toInt.2 = _
      rw [hy']; ring
    change (Int.sign (Pos.dirTo src target).1, Int.sign (Pos.dirTo src target).2) = d
    rw [e1, e2, Int.sign_mul, Int.sign_mul, Int.sign_eq_one_of_pos hpos, one_mul, one_mul,
      hd1, hd2]
  obtain ⟨l, hl, hln, rfl⟩ :=
    (mem_slidePath_iff_of_exact_steps src target d (n - j) hd (by omega) hdir' hx' hy' q).mp hq
  refine ⟨(hm _).mpr ⟨j + l, by omega, by omega, ?_⟩, ?_⟩
  · rw [hs1, hs2]
    congr 1 <;> push_cast <;> ring
  · intro he
    have e1 : src.toInt.1 + ↑l * d.1 = src.toInt.1 := congrArg Prod.fst he
    have e2 : src.toInt.2 + ↑l * d.2 = src.toInt.2 := congrArg Prod.snd he
    have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast (show l ≠ 0 by omega)
    apply hd
    refine Prod.ext ?_ ?_
    · exact (mul_eq_zero.mp (show (l : ℤ) * d.1 = 0 by linarith)).resolve_left hl0
    · exact (mul_eq_zero.mp (show (l : ℤ) * d.2 = 0 by linarith)).resolve_left hl0

/-- From an unchecked fixed target, an unblocked checker of a board move makes
    the segment from the source to the target clear on the before board: the
    checker's line runs through the source, and its remaining squares are neither
    endpoint, so they were already empty. -/
theorem applyMove_boardMove_pathClear_source_of_unblockedChecker (bs : BoardState)
    (src dst target : Pos) (promote : Bool) (kingOwner : Player)
    (hbefore : ¬ inCheckOriented bs.board kingOwner target)
    (h : hasUnblockedCheckerOriented bs.board (applyMove bs (.boardMove src dst promote)).board
      (.boardMove src dst promote) kingOwner target) :
    pathClear bs.board src target := by
  obtain ⟨pos, piece, _, _, hp0, _, ho, ha, hmem, hdst, _, hclr⟩ := h
  rcases ha with hstep | ⟨d, hdm, hnorm, n, hn, hx, hy, _⟩
  · exact False.elim (hbefore ⟨pos, piece, hp0, ho, Or.inl hstep⟩)
  have hd : d ≠ (0, 0) := by
    intro he
    rw [he] at hdm
    rcases piece with ⟨owner, pt⟩
    cases owner <;> cases pt <;>
      simp [PieceType.slideDirs, Dir.forPlayer, Dir.flip, Prod.ext_iff] at hdm
  have hx' : target.toInt.1 = pos.toInt.1 + ↑n * d.1 := by
    dsimp [Pos.dirTo, Pos.toInt] at hx ⊢
    omega
  have hy' : target.toInt.2 = pos.toInt.2 + ↑n * d.2 := by
    dsimp [Pos.dirTo, Pos.toInt] at hy ⊢
    omega
  intro q hq hob hproof
  obtain ⟨hqp, hqs⟩ := mem_slidePath_of_mem_tail pos src target d n hd hn hnorm hx' hy' hmem q hq
  have hne_src : toPos q hproof ≠ src := fun he => hqs (toPos_eq_int q hproof src he)
  have hne_dst : toPos q hproof ≠ dst := fun he => hdst (toPos_eq_int q hproof dst he ▸ hqp)
  rw [← applyMove_boardMove_grid_other bs src dst promote _ hne_src hne_dst]
  exact hclr q hqp hob hproof

/-- Lemma 2.5 on boards: if the moving piece belongs to the checking side and
    reaches the unchecked target on some board, its move has no unblocked
    checker. The board may differ from the actual one, e.g. a stripped board. -/
theorem applyMove_boardMove_not_unblockedChecker_of_attacks (bs : BoardState)
    (src dst target : Pos) (promote : Bool) (kingOwner : Player) (S : Board) (moving : Piece)
    (hsrc : bs.board.grid src = some moving) (ho : moving.owner = kingOwner.opponent)
    (hline : attacksOriented S moving.owner moving.pieceType src target)
    (hbefore : ¬ inCheckOriented bs.board kingOwner target) :
    ¬ hasUnblockedCheckerOriented bs.board (applyMove bs (.boardMove src dst promote)).board
      (.boardMove src dst promote) kingOwner target := fun h =>
  hbefore ⟨src, moving, hsrc, ho, attacksOriented_of_pathClear S bs.board _ _ src target hline
    (applyMove_boardMove_pathClear_source_of_unblockedChecker bs src dst target promote
      kingOwner hbefore h)⟩

namespace MoveTrace

/-- Lemma 2.5 on traces: under the stated transition and safety premises, moving a piece that glares at
    the enemy king in the before state has no unblocked checker. -/
theorem not_unblockedChecker_of_source_glares (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (ht : tr.FollowsTransitions)
    (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (i : Fin tr.len) (src dst : Pos) (promote : Bool)
    (hm : tr.moves i = .boardMove src dst promote)
    (hg : tr.GlaresAtEnemyKing kp i.castSucc src) :
    ¬ hasUnblockedCheckerOriented (tr.before i).board (tr.after i).board (tr.moves i)
      (tr.before i).turn.opponent (kp i.succ (tr.before i).turn.opponent) := by
  obtain ⟨piece, hp, ha⟩ := hg
  obtain ⟨moving, hp', ho⟩ := hs i src dst promote hm
  have he : piece = moving := Option.some.inj (hp.symm.trans hp')
  rw [he] at ha
  have ha' : attacksOriented (tr.strippedBoard i.castSucc src) moving.owner moving.pieceType
      src (kp i.castSucc (tr.before i).turn.opponent) := by
    rw [← ho]; exact ha
  rw [tr.opponentKingPos_succ_eq kp ht hs hk i, ht i, hm]
  exact applyMove_boardMove_not_unblockedChecker_of_attacks (tr.before i) src dst _ promote _
    _ moving hp' (by rw [ho, Player.opponent_opponent]) ha'
    (tr.before_opponent_not_inCheck kp ht hsafe h0 i)

/-- The paper's classification: in a mutual-check trace satisfying the stated transition and safety
    premises, a move of a glaring piece is a direct check. -/
theorem destinationChecker_of_source_glares (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (ht : tr.FollowsTransitions)
    (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (i : Fin tr.len) (src dst : Pos) (promote : Bool)
    (hm : tr.moves i = .boardMove src dst promote)
    (hg : tr.GlaresAtEnemyKing kp i.castSucc src) :
    hasDestinationCheckerOriented (tr.after i).board (tr.moves i)
      (tr.before i).turn.opponent (kp i.succ (tr.before i).turn.opponent) :=
  ((tr.everyMoveChecksOpponent_iff_destination_or_unblocked_of_safe kp ht hs hk hsafe h0).mp
    hc i).resolve_right
    (tr.not_unblockedChecker_of_source_glares kp ht hs hk hsafe h0 i src dst promote hm hg)

/-- Lemma 2.6: under the same premises, a glaring piece is never moved to a
    non-glaring square; its destination glares in the after state. -/
theorem destination_glares_of_source_glares (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (ht : tr.FollowsTransitions)
    (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (i : Fin tr.len) (src dst : Pos) (promote : Bool)
    (hm : tr.moves i = .boardMove src dst promote)
    (hg : tr.GlaresAtEnemyKing kp i.castSucc src) :
    tr.GlaresAtEnemyKing kp i.succ dst := by
  have h := tr.glaresAtEnemyKing_of_destinationChecker kp i.succ (tr.moves i) _
    (tr.destinationChecker_of_source_glares kp ht hs hk hsafe h0 hc i src dst promote hm hg)
  rw [hm] at h
  exact h

end MoveTrace
end MPC
