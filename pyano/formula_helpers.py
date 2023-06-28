from formula import *

import string


def Exists(var, predicate_with_free_var):
    return Not(ForAll(var, Not(predicate_with_free_var)))


def LessThanOrEq(x, y):
    varname = get_name_generator([x, y])()
    return Exists(varname, Eq(Add(x, Var(varname)), y))


def Or(x, y):
    return Not(And(Not(x), Not(y)))


def ForAllN(vs, body):
    if len(vs) == 1:
        return ForAll(vs[0], body)
    return ForAll(vs[0], ForAllN(vs[1:], body))


def ImpliesN(*args):
    """Returns a formula of the form A -> (B -> (C -> D -> ...)).

    >>> A = Eq(Zero(), Succ(Zero()))
    >>> B = Eq(Zero(), Zero())
    >>> C = Eq(Succ(Zero()), Zero())
    >>> D = Eq(Succ(Zero()), Succ(Zero()))
    >>> print(ImpliesN(A, B, C, D))
    (0 = S(0)) => (0 = 0) => (S(0) = 0) => (S(0) = S(0))
    """
    assert len(args) > 1
    if len(args) == 2:
        return Implies(args[0], args[1])
    else:
        return Implies(args[0], ImpliesN(*args[1:]))


def gen_induction_axiom(var, P):
    """Generates the induction axiom for predicate `P`.  The induction will be on `var`,
    which must be a free variable in `P`.

    >>> print(gen_induction_axiom("x", Eq(Var("x"), Zero())))
    ((0 = 0) & (forall $0. ($0 = 0) => (S($0) = 0))) => (forall $1. ($1 = 0))

    """

    assert isinstance(var, str), f"Expected var to be a string, got {type(var)}"
    assert isinstance(P, Formula), f"Expected P to be a Formula, got {type(P)}"
    assert var in get_free_vars(P), f"P must have `var` as a free variable"

    namegen = get_name_generator([P])
    k = namegen()
    x = namegen()
    return Implies(
        And(
            substitute_free_var(P, var, Zero()),
            ForAll(
                k,
                Implies(
                    substitute_free_var(P, var, Var(k)),
                    substitute_free_var(P, var, Succ(Var(k))),
                ),
            ),
        ),
        ForAll(x, substitute_free_var(P, var, Var(x))),
    )


def _make_getter(field_name):
    return lambda x: getattr(x, field_name)


class _CachedVars:
    def __init__(self):
        for _v in string.ascii_lowercase + string.ascii_uppercase[:-1]:
            v = str(_v)
            var = Var(v)
            setattr(self, f"_{v}", var)
            setattr(_CachedVars, v, property(_make_getter(f"_{v}")))

            setattr(self, f"_s{v}", Succ(var))
            setattr(_CachedVars, f"s{v}", property(_make_getter(f"_s{v}")))

        ivalue = Zero()
        for i in range(0, 20):
            setattr(self, f"_i{i}", ivalue)
            setattr(_CachedVars, f"i{i}", property(_make_getter(f"_i{i}")))
            ivalue = Succ(ivalue)

    @property
    def Z(self):
        return self.i0

    @property
    def sZ(self):
        return self.i1


_CACHED_VARS = _CachedVars()


def get_cached_vars():
    """Returns an object with fields for some commonly used variables to save typing.

    >>> v = get_cached_vars()
    >>> print(v.x)
    x
    >>> type(v.x)
    <class 'formula.Var'>

    The returned object has fields for a..z and A..Y.

    v.Z is not a symbol, instead it refers to Zero().
    >>> print(get_cached_vars().Z)
    0
    >>> print(get_cached_vars().sZ)
    S(0)

    Each for each symbol $A this also has a s$A symbol that is Succ($A).

    >>> print(get_cached_vars().sx)
    S(x)

    Finally, the object has i0..i19, representing the first 20 natural numbers.
    >>> print(get_cached_vars().i6)
    S(S(S(S(S(S(0))))))

    """
    return _CACHED_VARS


def _generate_forall_helpers():
    """This function generates some helpers in the global scope to reduce the boilerplate
    for writing forall expressions.

        It generates forall* for all letters of the alphabet and all pairs.

        >>> print(forallx(Eq(Zero(), Zero())))
        (forall x. (0 = 0))
        >>> print(forallde(Eq(Zero(), Zero())))
        (forall d, e. (0 = 0))

        It also generates forallxyz and forallabc.

        >>> print(forallxyz(Eq(Zero(), Zero())))
        (forall x. (forall y. (forall z. (0 = 0))))

    """
    for letter in string.ascii_lowercase:
        function_name = f"forall{letter}"
        function_code = (
            f"def {function_name}(body):\n    return ForAll('{letter}', body)"
        )
        exec(function_code, globals())

    multi_letter_names = []

    for x in string.ascii_lowercase:
        for y in string.ascii_lowercase:
            multi_letter_names.append(x + y)

    multi_letter_names.append("abc")
    multi_letter_names.append("xyz")

    for letter_seq in multi_letter_names:
        function_name = f"forall{letter_seq}"
        function_code = f"def {function_name}(body):\n    return ForAllN([x for x in '{letter_seq}'], body)"
        exec(function_code, globals())


_generate_forall_helpers()
