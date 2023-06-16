from formula import *

import itertools as it


def test_serialization_0():
    assert str(Succ(Zero())) == "S(0)"


def test_serialization_1():
    addition_axiom = ForAll(
        "x",
        ForAll("y", Eq(Add(Var("x"), Succ(Var("y"))), Succ(Add(Var("x"), Var("y"))))),
    )
    assert str(addition_axiom) == "(forall x. (forall y. ((x + S(y)) = S((x + y)))))"


def test_serialization_2():
    pred = Eq(Var("x"), Var("y"))
    lem_axiom = Implies(Not(Not(pred)), pred)
    assert str(lem_axiom) == "!!(x = y) => (x = y)"


def test_serialization_3():
    pred0 = Eq(Var("x"), Var("y"))
    pred1 = Eq(Var("p"), Var("q"))
    and_axiom = Implies(And(pred0, pred1), pred1)
    assert str(and_axiom) == "((x = y) & (p = q)) => (p = q)"


def test_serialization_4():
    pred0 = Eq(Var("x"), Var("y"))
    pred1 = Eq(Var("p"), Var("q"))
    pred2 = Eq(Var("r"), Var("s"))
    impl = Implies(Implies(pred0, pred1), pred2)
    assert str(impl) == "((x = y) => (p = q)) => (r = s)"


def test_serialization_5():
    pred0 = Eq(Var("x"), Var("y"))
    pred1 = Eq(Var("p"), Var("q"))
    pred2 = Eq(Var("r"), Var("s"))
    impl = Implies(pred0, Implies(pred1, pred2))
    assert str(impl) == "(x = y) => (p = q) => (r = s)"


def test_get_all_subformulae():
    addition_axiom = ForAll(
        "x",
        ForAll("y", Eq(Add(Var("x"), Succ(Var("y"))), Succ(Add(Var("x"), Var("y"))))),
    )

    subformulae = list(get_all_subformulae(addition_axiom))
    assert len(subformulae) == 11

    node_types = it.groupby(sorted(subformulae, key=lambda x: str(type(x))), key=type)

    node_types_dict = {key: list(group) for key, group in node_types}

    assert len(node_types_dict[ForAll]) == 2
    assert len(node_types_dict[Eq]) == 1
    assert len(node_types_dict[Add]) == 2
    assert len(node_types_dict[Var]) == 4
    assert len(node_types_dict[Succ]) == 2


def test_eq_0():
    addition_axiom_0 = ForAll(
        "x",
        ForAll("y", Eq(Add(Var("x"), Succ(Var("y"))), Succ(Add(Var("x"), Var("y"))))),
    )

    addition_axiom_1 = ForAll(
        "x",
        ForAll("y", Eq(Add(Var("x"), Succ(Var("y"))), Succ(Add(Var("x"), Var("y"))))),
    )

    assert addition_axiom_0 == addition_axiom_1
    assert addition_axiom_0 == addition_axiom_0
    assert addition_axiom_1 == addition_axiom_1


def test_eq_1():
    addition_axiom_0 = ForAll(
        "x",
        ForAll("y", Eq(Add(Var("x"), Succ(Var("y"))), Succ(Add(Var("x"), Var("y"))))),
    )

    addition_axiom_1 = ForAll(
        "x",
        ForAll("z", Eq(Add(Var("x"), Succ(Var("z"))), Succ(Add(Var("x"), Var("z"))))),
    )

    assert addition_axiom_0 == addition_axiom_1
    assert addition_axiom_0 == addition_axiom_0
    assert addition_axiom_1 == addition_axiom_1


def test_eq_2():
    addition_axiom_0 = ForAll(
        "x",
        ForAll("y", Eq(Add(Var("x"), Succ(Var("y"))), Succ(Add(Var("x"), Var("y"))))),
    )

    addition_axiom_1 = ForAll(
        "x",
        ForAll("z", Eq(Add(Var("z"), Succ(Var("x"))), Succ(Add(Var("x"), Var("z"))))),
    )

    assert not addition_axiom_0 == addition_axiom_1
    assert addition_axiom_0 == addition_axiom_0
    assert addition_axiom_1 == addition_axiom_1


def test_substitute_forall_0():
    addition_axiom = ForAll(
        "x",
        ForAll("y", Eq(Add(Var("x"), Succ(Var("y"))), Succ(Add(Var("x"), Var("y"))))),
    )

    one = Succ(Zero())
    two = Succ(one)
    subst_0 = substitute_forall(addition_axiom, one)
    subst_1 = substitute_forall(subst_0, two)

    assert str(subst_1) == "((S(0) + S(S(S(0)))) = S((S(0) + S(S(0)))))"


def test_substitute_forall_1():
    repeated_bound_vars = ForAll(
        "x", And(Eq(Var("x"), Zero()), ForAll("x", Eq(Var("x"), Zero())))
    )

    subst = substitute_forall(repeated_bound_vars, Succ(Zero()))

    assert str(subst) == "((S(0) = 0) & (forall x. (x = 0)))"


def test_get_free_vars_0():
    addition_axiom = ForAll(
        "x",
        ForAll("y", Eq(Add(Var("x"), Succ(Var("y"))), Succ(Add(Var("x"), Var("y"))))),
    )

    assert get_free_vars(addition_axiom) == set()


def test_get_free_vars_1():
    addition_axiom = ForAll(
        "x",
        ForAll("y", Eq(Add(Var("x"), Succ(Var("y"))), Succ(Add(Var("x"), Var("y"))))),
    )

    assert get_free_vars(addition_axiom.body) == set(["x"])


def test_replace_subformula():
    one = Succ(Zero())
    add_1 = ForAll("y", Eq(Add(one, Succ(Var("y"))), Succ(Add(one, Var("y")))))

    two = Succ(one)
    result = replace_subformula(add_1, one, two)
    assert str(result) == "(forall y. ((S(S(0)) + S(y)) = S((S(S(0)) + y))))"


def test_replace_subformula_gen():
    one = Succ(Zero())
    add_1 = ForAll("y", Eq(Add(one, Succ(Var("y"))), Succ(Add(one, Var("y")))))

    var_counter = 0

    def genvar():
        nonlocal var_counter
        x = f"${var_counter}"
        var_counter = var_counter + 1
        return Var(x)

    result = replace_subformula(add_1, one, genvar)
    assert str(result) == "(forall y. (($0 + S(y)) = S(($1 + y))))"


def test_match_exprs_0():
    forall_template = ForAll("x", Eq(Var("x"), Var("y")))
    forall_formula = ForAll("x", Eq(Var("x"), Succ(Zero())))

    assert match_template(forall_template, forall_formula, ["y"])


def test_match_exprs_1():
    forall_template = ForAll("x", Eq(Var("x"), Var("y")))
    forall_formula = ForAll("z", Eq(Var("z"), Succ(Zero())))

    assert match_template(forall_template, forall_formula, ["y"])


def test_match_exprs_2():
    forall_template = ForAll("x", Eq(Var("x"), Var("x")))
    forall_formula = ForAll("z", Eq(Var("z"), Succ(Zero())))

    assert not match_template(forall_template, forall_formula, [])


def test_match_exprs_3():
    forall_template = ForAll("x", Eq(Var("x"), Var("x")))
    forall_formula = ForAll("z", Eq(Var("z"), Var("z")))

    assert match_template(forall_template, forall_formula, [])


def test_match_exprs_4():
    forall_template = ForAll("j", ForAll("x", Eq(Var("x"), Var("A"))))
    forall_formula = ForAll("i", ForAll("z", Eq(Var("z"), Zero())))

    assert match_template(forall_template, forall_formula, ["A"])


def test_match_exprs_5():
    forall_template = ForAll("j", ForAll("x", Eq(Var("x"), Var("A"))))
    forall_formula = ForAll("i", ForAll("z", Eq(Var("z"), Var("z"))))

    assert not match_template(forall_template, forall_formula, ["A"])


def test_formula_in_python_sets():
    s = set()
    s.add(ForAll("x", Eq(Var("x"), Zero())))
    s.add(ForAll("y", Eq(Var("y"), Zero())))

    assert len(s) == 1


def test_canonicalize_bound_vars_0():
    addition_axiom = ForAll(
        "x",
        ForAll("y", Eq(Add(Var("x"), Succ(Var("y"))), Succ(Add(Var("x"), Var("y"))))),
    )

    free_vars = set()
    uniqued = canonicalize_bound_vars(addition_axiom, free_vars)

    assert str(uniqued) == "(forall $0. (forall $1. (($0 + S($1)) = S(($0 + $1)))))"
    assert len(free_vars) == 0


def test_canonicalize_bound_vars_1():
    open_sentence = ForAll(
        "x",
        ForAll("y", Eq(Add(Var("x"), Succ(Var("z"))), Succ(Add(Var("x"), Var("y"))))),
    )

    free_vars = set()
    uniqued = canonicalize_bound_vars(open_sentence, free_vars)

    assert str(uniqued) == "(forall $0. (forall $1. (($0 + S(z)) = S(($0 + $1)))))"
    assert [x.name for x in free_vars] == ["z"]
