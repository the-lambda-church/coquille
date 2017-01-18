from coqtop import *

def get_goals():
    r = goals()
    if r is None:
        return r
    if isinstance(r, Err):
        return r

    if r.msg is not None:
        r.msg

    if r.val.val is None:
        return "no goals"

    gs = r.val.val
    return gs


cmd1 = "Theorem plus_0_r : forall n : nat, n + 0 = n."
cmd2 = "Proof."
cmd3 = "  intro n."
cmd4 = "  induction n as [| n']."
cmd5 = "  reflexivity."
cmd6 = "  simpl."
cmd7 = "  rewrite -> IHn'."
cmd8 = "  reflexivity."
cmd9 = "Qed."


def test_proof():
    global states
    launch_coq()

    advance(cmd1)
    assert get_goals() == Goals([Goal('2', [], 'forall n : nat, n + 0 = n')], [], [], [])
    advance(cmd2)
    assert get_goals() == Goals([Goal('2', [], 'forall n : nat, n + 0 = n')], [], [], [])
    advance(cmd3)
    assert get_goals() == Goals([Goal('3', ['n : nat'], 'n + 0 = n')], [], [], [])
    advance(cmd4)
    assert get_goals() == Goals([Goal('7', [], '0 + 0 = 0'), Goal('10', ["n' : nat", "IHn' : n' + 0 = n'"], "S n' + 0 = S n'")], [], [], [])
    advance(cmd5)
    assert get_goals() == Goals([Goal('10', ["n' : nat", "IHn' : n' + 0 = n'"], "S n' + 0 = S n'")], [], [], [])
    advance(cmd6)
    assert get_goals() == Goals([Goal('13', ["n' : nat", "IHn' : n' + 0 = n'"], "S (n' + 0) = S n'")], [], [], [])
    advance(cmd7)
    assert get_goals() == Goals([Goal('14', ["n' : nat", "IHn' : n' + 0 = n'"], "S n' = S n'")], [], [], [])
    advance(cmd8)
    assert get_goals() == Goals([], [], [], [])
    advance(cmd9)
    assert get_goals() == "no goals"

    assert states == [StateId(1), StateId(2), StateId(3), StateId(4), StateId(5), StateId(6), StateId(7), StateId(8), StateId(9)]

    rewind()
    assert get_goals() == Goals([], [], [], [])
    rewind()
    assert get_goals() == Goals([Goal('14', ["n' : nat", "IHn' : n' + 0 = n'"], "S n' = S n'")], [], [], [])
    rewind()
    assert get_goals() == Goals([Goal('13', ["n' : nat", "IHn' : n' + 0 = n'"], "S (n' + 0) = S n'")], [], [], [])

    assert read_states() == [StateId(1), StateId(2), StateId(3), StateId(4), StateId(5), StateId(6)]
    assert cur_state() == StateId(7)

    advance(cmd7)
    assert get_goals() == Goals([Goal('14', ["n' : nat", "IHn' : n' + 0 = n'"], "S n' = S n'")], [], [], [])
    advance(cmd8)
    assert get_goals() == Goals([], [], [], [])
    advance(cmd9)
    assert get_goals() == "no goals"

    assert read_states() == [StateId(1), StateId(2), StateId(3), StateId(4), StateId(5), StateId(6), StateId(7), StateId(11), StateId(12)]

    assert query("Print plus_0_r.") == Ok('', "plus_0_r = \nfun n : nat =>\nnat_ind (fun n0 : nat => n0 + 0 = n0) eq_refl\n  (fun (n' : nat) (IHn' : n' + 0 = n') =>\n   eq_ind_r (fun n0 : nat => S n0 = S n') eq_refl IHn') n\n     : forall n : nat, n + 0 = n\n\nArgument scope is [nat_scope]")
    assert query("Check plus_0_r.") == Ok('', 'plus_0_r\n     : forall n : nat, n + 0 = n')

    kill_coqtop()
