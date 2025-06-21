from formula import *

import itertools as it


def test_serialization_0():
    assert str(Succ(Zero())) == "S(0)"


def test_serialization_1():
    addition_axiom = ForAll(
        "x",
        ForAll("y", Eq(Add(Var("x"), Succ(Var("y"))), Succ(Add(Var("x"), Var("y"))))),
    )
    assert str(addition_axiom) == "(forall x, y. ((x + S(y)) = S((x + y))))"


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

    assert str(uniqued) == "(forall $0, $1. (($0 + S($1)) = S(($0 + $1))))"
    assert len(free_vars) == 0


def test_canonicalize_bound_vars_1():
    open_sentence = ForAll(
        "x",
        ForAll("y", Eq(Add(Var("x"), Succ(Var("z"))), Succ(Add(Var("x"), Var("y"))))),
    )

    free_vars = set()
    uniqued = canonicalize_bound_vars(open_sentence, free_vars)

    assert str(uniqued) == "(forall $0, $1. (($0 + S(z)) = S(($0 + $1))))"
    assert [x.name for x in free_vars] == ["z"]


def test_mul_serialization():
    x = Var("x")
    y = Var("y")
    mul_expr = Mul(x, y)
    assert str(mul_expr) == "(x * y)"


def test_mul_with_numbers():
    two = Succ(Succ(Zero()))
    three = Succ(Succ(Succ(Zero())))
    mul_expr = Mul(two, three)
    assert str(mul_expr) == "(S(S(0)) * S(S(S(0))))"


def test_mul_equality():
    x = Var("x")
    y = Var("y")
    mul1 = Mul(x, y)
    mul2 = Mul(x, y)
    assert mul1 == mul2


def test_mul_in_formula():
    x = Var("x")
    y = Var("y")
    z = Var("z")
    formula = ForAll("x", Eq(Mul(x, y), z))
    assert str(formula) == "(forall x. ((x * y) = z))"


def test_complex_nested_formula():
    x = Var("x")
    y = Var("y")
    z = Var("z")
    nested = ForAll("x", 
        ForAll("y", 
            Implies(
                And(Eq(x, Zero()), Eq(y, Succ(Zero()))),
                Eq(Add(x, Mul(y, z)), z)
            )
        )
    )
    expected = "(forall x, y. ((x = 0) & (y = S(0))) => ((x + (y * z)) = z))"
    assert str(nested) == expected


def test_deeply_nested_implications():
    p = Eq(Var("p"), Zero())
    q = Eq(Var("q"), Zero())
    r = Eq(Var("r"), Zero())
    s = Eq(Var("s"), Zero())
    nested_impl = Implies(p, Implies(q, Implies(r, s)))
    assert str(nested_impl) == "(p = 0) => (q = 0) => (r = 0) => (s = 0)"


def test_variable_shadowing():
    inner_forall = ForAll("x", Eq(Var("x"), Zero()))
    outer_forall = ForAll("x", And(Eq(Var("x"), Succ(Zero())), inner_forall))
    assert str(outer_forall) == "(forall x. ((x = S(0)) & (forall x. (x = 0))))"


def test_exists_via_not_forall_not():
    x = Var("x")
    exists_x = Not(ForAll("x", Not(Eq(x, Zero()))))
    assert str(exists_x) == "(exists x. (x = 0))"


def test_multiple_quantifiers_with_same_name():
    formula = ForAll("x", 
        And(
            Eq(Var("x"), Zero()),
            ForAll("x", Eq(Var("x"), Succ(Zero())))
        )
    )
    subst = substitute_forall(formula, Succ(Succ(Zero())))
    assert str(subst) == "((S(S(0)) = 0) & (forall x. (x = S(0))))"


def test_get_free_vars_complex():
    formula = ForAll("x", 
        And(
            Eq(Var("x"), Var("y")),
            ForAll("z", Eq(Var("z"), Var("w")))
        )
    )
    free_vars = get_free_vars(formula)
    assert free_vars == {"y", "w"}


def test_replace_subformula_in_quantifier():
    original = ForAll("x", Eq(Add(Var("x"), Zero()), Var("x")))
    replaced = replace_subformula(original, Zero(), Succ(Zero()))
    assert str(replaced) == "(forall x. ((x + S(0)) = x))"


def test_match_template_with_multiplication():
    template = ForAll("x", Eq(Mul(Var("x"), Var("A")), Var("B")))
    formula = ForAll("y", Eq(Mul(Var("y"), Succ(Zero())), Zero()))
    assert match_template(template, formula, ["A", "B"])


def test_get_all_subformulae_complex():
    formula = ForAll("x", 
        Implies(
            And(Eq(Var("x"), Zero()), Not(Eq(Var("x"), Succ(Zero())))),
            Eq(Mul(Var("x"), Var("x")), Zero())
        )
    )
    subformulae = list(get_all_subformulae(formula))
    assert len(subformulae) == 14


def test_hash_consistency():
    x = Var("x")
    y = Var("y")
    formula1 = ForAll("x", Eq(x, y))
    formula2 = ForAll("z", Eq(Var("z"), y))
    assert hash(formula1) == hash(formula2)


def test_canonicalize_with_free_vars():
    formula = ForAll("x", 
        And(
            Eq(Var("x"), Var("free1")),
            ForAll("y", Eq(Var("y"), Var("free2")))
        )
    )
    free_vars = set()
    canonicalized = canonicalize_bound_vars(formula, free_vars)
    assert str(canonicalized) == "(forall $0. (($0 = free1) & (forall $1. ($1 = free2))))"
    assert len(free_vars) == 2
