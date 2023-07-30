"""Axioms for first order logic and integers."""

from formula import *

import itertools


def _is_general_axiom(f, inner_matcher):
    if len(get_free_vars(f)) != 0:
        return False

    while True:
        if inner_matcher(f):
            return True
        if isinstance(f, ForAll):
            f = f.body
        else:
            return False


def _is_induction_axiom_impl(f):
    # (P(0) & (forall k. P(k) => P(k+1))) => forall x. P(x)
    if not isinstance(f, Implies):
        return False

    rhs_forall = f.q
    if not isinstance(rhs_forall, ForAll):
        return False

    lhs_and = f.p
    if not isinstance(lhs_and, And):
        return False

    if lhs_and.a != substitute_forall(rhs_forall, Zero()):
        return False

    inductive_step = lhs_and.b
    if not isinstance(inductive_step, ForAll):
        return False

    k = inductive_step.var
    expected_inductive_step = ForAll(
        k,
        Implies(
            substitute_forall(rhs_forall, Var(k)),
            substitute_forall(rhs_forall, Succ(Var(k))),
        ),
    )

    return expected_inductive_step == inductive_step


def is_induction_axiom(f):
    return _is_general_axiom(f, _is_induction_axiom_impl)


def _evaluate_with_truth_assignments(f, truth_assignment):
    def recurse(f):
        return _evaluate_with_truth_assignments(f, truth_assignment)

    if f in truth_assignment:
        return truth_assignment[f]

    ftype = type(f)
    if ftype == And:
        return recurse(f.a) and recurse(f.b)
    elif ftype == Not:
        return not recurse(f.x)
    elif ftype == Implies:
        return not recurse(f.p) or recurse(f.q)
    else:
        raise ValueError(f"Cannot evaluate {f} with truth_assignment")


def _get_all_toplevel_preds(f):
    ftype = type(f)
    if ftype == ForAll or ftype == Eq:
        yield f
        return

    if ftype == Succ or ftype == Not:
        yield from _get_all_toplevel_preds(f.x)
    elif ftype == Add or ftype == And:
        yield from _get_all_toplevel_preds(f.a)
        yield from _get_all_toplevel_preds(f.b)
    elif ftype == Implies:
        yield from _get_all_toplevel_preds(f.p)
        yield from _get_all_toplevel_preds(f.q)


def _is_tautology_impl(f):
    preds = list(set(_get_all_toplevel_preds(f)))

    for truth_assignments in itertools.product([True, False], repeat=len(preds)):
        truth_assignments_dict = dict(zip(preds, truth_assignments))
        try:
            result = _evaluate_with_truth_assignments(f, truth_assignments_dict)
        except ValueError:
            return False
        if not result:
            return False
    return True


def is_tautology(f):
    return _is_general_axiom(f, _is_tautology_impl)


def is_forall_elimination(f):
    return _is_general_axiom(f, _is_forall_elimination_impl)


def _is_forall_elimination_impl(f):
    # forall x. P(x) => P(k)

    if not isinstance(f, Implies) or not isinstance(f.p, ForAll):
        return False

    return match_template(f.p.body, f.q, [f.p.var])


def is_forall_introduction(f):
    return _is_general_axiom(f, _is_forall_introduction_impl)


def _is_forall_introduction_impl(f):
    # f => forall x. f

    if not isinstance(f, Implies) or not isinstance(f.q, ForAll):
        return False

    return f.q.var not in get_free_vars(f.p) and f.q.body == f.p


def is_forall_split(f):
    return _is_general_axiom(f, _is_forall_split_impl)


def _is_forall_split_impl(f):
    # forall x. (A => B) => ((forall x. A) => (forall x. B)
    #     ^                         ^              ^
    #     P                         Q              R

    if not (
        isinstance(f, Implies)
        and isinstance(f.p, ForAll)
        and isinstance(f.q, Implies)
        and isinstance(f.q.p, ForAll)
        and isinstance(f.q.q, ForAll)
        and isinstance(f.p.body, Implies)
    ):
        return False

    P = f.p
    Q = f.q.p
    R = f.q.q

    return ForAll(P.var, P.body.p) == Q and ForAll(P.var, P.body.q) == R


def is_reflexivity_axiom(f):
    return _is_general_axiom(f, _is_reflexivity_axiom_impl)


def _is_reflexivity_axiom_impl(f):
    return f == ForAll("x", Eq(Var("x"), Var("x")))


def is_subst_axiom(f):
    return _is_general_axiom(f, _is_subst_axiom_impl)


def _is_subst_axiom_impl(f):
    # x = y => (A => B) where B is A with x replaced by Y in some places.
    if not (
        isinstance(f, Implies) and isinstance(f.p, Eq) and isinstance(f.q, Implies)
    ):
        return False

    x = f.p.a
    y = f.p.b
    a = f.q.p
    b = f.q.q

    gen_varname = get_name_generator(f)
    varnames = []

    def local_genvar():
        nonlocal gen_varname, varnames
        varname = gen_varname()
        varnames.append(varname)
        return Var(varname)

    template = replace_subformula(a, x, local_genvar)

    captured_formulae = {}
    if not match_template(
        template, b, vars_to_capture=varnames, captured_formulae=captured_formulae
    ):
        return False

    for k, v in captured_formulae.items():
        if not (v == x or v == y):
            return False

    return True


def _gen_first_order_peano_axioms():
    x = Var("x")
    y = Var("y")

    def forallx(body):
        return ForAll("x", body)

    def forallxy(body):
        return ForAll("x", ForAll("y", body))

    zero_is_not_succ = forallx(Not(Eq(Zero(), Succ(x))))
    succ_is_injective = forallxy(Implies(Eq(Succ(x), Succ(y)), Eq(x, y)))
    x_plus_zero = forallx(Eq(Add(x, Zero()), x))
    x_plus_succ_y = forallxy(Eq(Add(x, Succ(y)), Succ(Add(x, y))))
    x_times_zero = forallx(Eq(Mul(x, Zero()), Zero()))
    x_times_succ_y = forallxy(Eq(Mul(x, Succ(y)), Add(Mul(x, y), x)))

    return {
        "zero_is_not_succ": zero_is_not_succ,
        "succ_is_injective": succ_is_injective,
        "x_plus_zero": x_plus_zero,
        "x_plus_succ_y": x_plus_succ_y,
        "x_times_zero": x_times_zero,
        "x_times_succ_y": x_times_succ_y,
    }


_FIRST_ORDER_PEANO_AXIOMS = _gen_first_order_peano_axioms()


def get_peano_axiom_zero_is_not_succ():
    """forall x. 0 != S(x)."""
    return _FIRST_ORDER_PEANO_AXIOMS["zero_is_not_succ"]


def get_peano_axiom_succ_is_injective():
    """forall x, y. S(x)=S(y) => x=y."""
    return _FIRST_ORDER_PEANO_AXIOMS["succ_is_injective"]


def get_peano_axiom_x_plus_zero():
    """forall x. x+0=x."""
    return _FIRST_ORDER_PEANO_AXIOMS["x_plus_zero"]


def get_peano_axiom_x_plus_succ_y():
    """forall x, y. x+S(y)=S(x+y)."""
    return _FIRST_ORDER_PEANO_AXIOMS["x_plus_succ_y"]


def get_peano_axiom_x_times_zero():
    """forall x, y. x*0=0."""
    return _FIRST_ORDER_PEANO_AXIOMS["x_times_zero"]


def get_peano_axiom_x_times_succ_y():
    """forall x, y. x*S(y)=Add(x*y, x)."""
    return _FIRST_ORDER_PEANO_AXIOMS["x_times_succ_y"]


def is_first_order_peano_axiom(f):
    return f in [v for k, v in _FIRST_ORDER_PEANO_AXIOMS.items()]


def is_axiom(f):
    """Returns True iff `f` is an axiom in first order logic or Peano."""

    assert isinstance(
        f, Formula
    ), f"Expected `f` to be a Formula instead found {type(f)}"

    return (
        is_induction_axiom(f)
        or is_tautology(f)
        or is_forall_elimination(f)
        or is_forall_introduction(f)
        or is_forall_split(f)
        or is_reflexivity_axiom(f)
        or is_subst_axiom(f)
        or is_first_order_peano_axiom(f)
    )
