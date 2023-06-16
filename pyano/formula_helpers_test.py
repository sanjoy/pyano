from formula_helpers import *


def test_cached_vars():
    v = get_cached_vars()
    assert str(v.x) == "x"
    assert str(v.B) == "B"
