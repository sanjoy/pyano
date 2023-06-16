from axioms import *
from formula_helpers import *


def test_is_induction_axiom_0():
    p = Eq(Var("x"), Zero())

    induction = gen_induction_axiom("x", p)
    assert is_induction_axiom(induction)


def test_is_induction_axiom_1():
    p = ForAll("z", Eq(Var("x"), Var("z")))

    induction = gen_induction_axiom("x", p)
    assert is_induction_axiom(induction)


def test_is_induction_axiom_2():
    two = Succ(Succ(Zero()))
    p = Or(LessThan(Var("x"), two), LessThan(two, Var("x")))

    induction = gen_induction_axiom("x", p)
    assert is_induction_axiom(induction)


def test_is_induction_axiom_3():
    p = Or(LessThan(Var("x"), Var("i")), LessThan(Var("i"), Var("x")))

    induction = ForAll("i", gen_induction_axiom("x", p))
    assert is_induction_axiom(induction)


def test_is_induction_axiom_4():
    p = Or(LessThan(Var("x"), Var("i")), LessThan(Var("i"), Var("x")))

    induction = gen_induction_axiom("x", p)
    assert not is_induction_axiom(induction)


def test_is_induction_axiom_3():
    two = Succ(Succ(Zero()))
    p1 = Or(LessThan(Var("x"), two), LessThan(two, Var("x")))
    p2 = Or(LessThan(two, Var("x")), LessThan(Var("x"), two))

    induction = Implies(
        And(
            substitute_free_var(p1, "x", Zero()),
            ForAll(
                "$k",
                Implies(
                    substitute_free_var(p1, "x", Var("$k")),
                    substitute_free_var(p1, "x", Succ(Var("$k"))),
                ),
            ),
        ),
        ForAll("$x", substitute_free_var(p2, "x", Var("$x"))),
    )

    assert not is_induction_axiom(induction)


def test_is_tautology_0():
    pred = Eq(Var("x"), Var("y"))
    taut = ForAllN(["x", "y"], Or(pred, Not(pred)))
    assert is_tautology(taut)


def test_is_tautology_1():
    pred = Eq(Var("x"), Var("y"))
    taut = ForAllN(["x", "y"], And(pred, Not(pred)))
    assert not is_tautology(taut)


def test_is_tautology_2():
    pred0 = Eq(Var("x"), Var("y"))
    pred1 = Eq(Var("x"), Var("z"))
    taut = ForAllN(["x", "y", "z"], Implies(And(pred0, pred1), pred1))
    assert is_tautology(taut)


def test_is_tautology_3():
    addition_axiom = ForAll(
        "x",
        ForAll("y", Eq(Add(Var("x"), Succ(Var("y"))), Succ(Add(Var("x"), Var("y"))))),
    )
    assert not is_tautology(addition_axiom)


def test_is_tautology_4():
    pred0 = Eq(Var("x"), Var("y"))
    pred1 = Eq(Var("x"), Var("z"))
    taut = ForAllN(["x", "y", "z"], Implies(And(pred0, pred1), pred1))
    assert is_tautology(taut)


def test_is_tautology_5():
    x = Var("x")
    y = Var("y")
    eq = Eq(x, y)

    taut = ForAllN(["x", "y"], Implies(Not(Not(eq)), eq))
    assert is_tautology(taut)


def test_is_forall_elimination_0():
    addition_axiom = ForAll(
        "x",
        ForAll("y", Eq(Add(Var("x"), Succ(Var("y"))), Succ(Add(Var("x"), Var("y"))))),
    )

    one = Succ(Zero())
    add_one = ForAll("x", Eq(Add(one, Succ(Var("x"))), Succ(Add(one, Var("x")))))

    eliminate_forall = Implies(addition_axiom, add_one)

    assert is_forall_elimination(eliminate_forall)


def test_is_forall_elimination_1():
    addition_axiom = ForAll(
        "x",
        ForAll("y", Eq(Add(Var("x"), Succ(Var("y"))), Succ(Add(Var("x"), Var("y"))))),
    )

    one = Succ(Zero())
    add_one_notok = ForAll(
        "x", Eq(Add(one, Succ(Var("x"))), Succ(Add(Zero(), Var("x"))))
    )

    eliminate_forall = Implies(addition_axiom, add_one_notok)

    assert not is_forall_elimination(eliminate_forall)


def test_is_forall_introduction_0():
    axiom = Implies(
        Not(Eq(Zero(), Succ(Zero()))), ForAll("x", Not(Eq(Zero(), Succ(Zero()))))
    )

    assert is_forall_introduction(axiom)


def test_is_forall_introduction_1():
    axiom = Implies(Not(Eq(Zero(), Var("x"))), ForAll("x", Not(Eq(Zero(), Var("x")))))

    assert not is_forall_introduction(axiom)


def test_is_forall_introduction_2():
    axiom = ForAll(
        "k", Implies(Not(Eq(Zero(), Var("k"))), ForAll("x", Not(Eq(Zero(), Var("k")))))
    )

    assert is_forall_introduction(axiom)


def test_is_forall_split_0():
    one = Succ(Zero())
    p = ForAll("x", Implies(Eq(Var("x"), Zero()), Eq(Var("x"), one)))
    qp = ForAll("x", Eq(Var("x"), Zero()))
    qq = ForAll("x", Eq(Var("x"), one))

    axiom = Implies(p, Implies(qp, qq))

    assert is_forall_split(axiom)


def test_is_forall_split_1():
    one = Succ(Zero())
    p = ForAll("x", Implies(Eq(Var("x"), Zero()), Eq(Var("x"), one)))
    qp = ForAll("x", Eq(Var("x"), Zero()))
    qq = ForAll("x", Eq(Var("x"), one))

    axiom = Implies(p, Implies(qq, qq))

    assert not is_forall_split(axiom)


def test_is_reflexivity_axiom_0():
    axiom = Eq(Zero(), Zero())
    assert is_reflexivity_axiom(axiom)


def test_is_reflexivity_axiom_1():
    axiom = Eq(Zero(), Succ(Zero()))
    assert not is_reflexivity_axiom(axiom)


def test_is_reflexivity_axiom_2():
    axiom = ForAll(
        "x", ForAll("y", Eq(Add(Var("x"), Var("y")), Add(Var("x"), Var("y"))))
    )
    assert is_reflexivity_axiom(axiom)


def test_is_reflexivity_axiom_3():
    axiom = ForAll(
        "x", ForAll("y", Eq(Add(Var("x"), Var("y")), Add(Var("y"), Var("x"))))
    )
    assert not is_reflexivity_axiom(axiom)


def test_is_subst_axiom_0():
    one = Succ(Zero())
    one_plus_zero = Add(one, Zero())
    one_plus_one = Add(one, one)
    p = Eq(one, one_plus_zero)
    qp = Eq(one_plus_one, one)
    qq = Eq(Add(one_plus_zero, one), one)

    axiom = Implies(p, Implies(qp, qq))
    assert is_subst_axiom(axiom)


def test_is_subst_axiom_1():
    one = Succ(Zero())
    one_plus_zero = Add(one, Zero())
    one_plus_one = Add(one, one)
    p = Eq(one, one_plus_zero)
    qp = Eq(one_plus_one, one)
    qq = Eq(Add(one_plus_zero, one), Add(one_plus_zero, one))

    axiom = Implies(p, Implies(qp, qq))
    assert not is_subst_axiom(axiom)


def test_is_subst_axiom_2():
    one = Succ(Zero())
    two = Succ(one)

    p = Eq(Var("x"), Var("y"))
    qp = Eq(Add(Var("x"), one), two)
    qq = Eq(Add(Var("y"), one), two)

    axiom = ForAll("x", ForAll("y", Implies(p, Implies(qp, qq))))
    assert is_subst_axiom(axiom)


def test_eq_transitive():
    x = Var("x")
    y = Var("y")
    z = Var("z")
    eq_is_transitive = ForAllN(
        ["x", "y", "z"], Implies(Eq(x, y), Implies(Eq(x, z), Eq(y, z)))
    )

    assert is_subst_axiom(eq_is_transitive)


def test_eq_reflexive():
    x = Var("x")
    y = Var("y")
    eq_is_transitive = ForAllN(
        ["x", "y"], Implies(Eq(x, y), Implies(Eq(x, x), Eq(y, x)))
    )

    assert is_subst_axiom(eq_is_transitive)


def test_first_order_peano_0():
    axiom = ForAll("x", Not(Eq(Zero(), Succ(Var("x")))))

    assert is_first_order_peano_axiom(axiom)
    assert is_axiom(axiom)


def test_first_order_peano_1():
    axiom = ForAll("x", Not(Eq(Zero(), Var("x"))))

    assert not is_first_order_peano_axiom(axiom)
    assert not is_axiom(axiom)


def test_all_peano_axioms_parse():
    get_peano_axiom_zero_is_not_succ()
    get_peano_axiom_succ_is_injective()
    get_peano_axiom_x_plus_zero()
    get_peano_axiom_x_plus_succ_y()
    get_peano_axiom_x_times_zero()
    get_peano_axiom_x_times_succ_y()
