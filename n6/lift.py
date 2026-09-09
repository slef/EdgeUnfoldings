"""Replace arithmetic expression DAGs by existential, low-degree equations.

This is a formula transformation, not a proof checker. Every auxiliary is
defined exactly; projecting solutions onto the original variables preserves the
original formula in both directions. Its purpose is to prevent a nonlinear
solver from expanding the unfolding's deeply nested homogeneous products.
"""


def arithmetic_lift(assertions):
    import z3
    cache = {}
    degrees = {}
    definitions = []
    auxiliaries = []

    def visit(expr):
        key = expr.get_id()
        if key in cache:
            return cache[key]
        if not z3.is_app(expr) or expr.num_args() == 0:
            cache[key] = expr
            degrees[key] = 0 if z3.is_rational_value(expr) or z3.is_int_value(expr) else 1
            return expr
        children = [visit(x) for x in expr.children()]
        child_degrees = [degrees[x.get_id()] for x in expr.children()]
        rebuilt = expr.decl()(*children)
        degree = 0
        if z3.is_arith(expr):
            kind = expr.decl().kind()
            if kind == z3.Z3_OP_MUL:
                value = children[0]
                degree = child_degrees[0]
                for x,d in zip(children[1:],child_degrees[1:]):
                    if degree+d<=1:
                        value=value*x;degree+=d
                    else:
                        aux = z3.FreshReal('lift')
                        definitions.append(aux == value * x)
                        auxiliaries.append(aux)
                        value = aux;degree=1
            elif kind == z3.Z3_OP_POWER:
                # Current geometry uses integer squares. Do not silently
                # introduce algebraic principal-root semantics for other powers.
                if not z3.is_int_value(children[1]) and not z3.is_rational_value(children[1]):
                    raise ValueError('Nonconstant exponent in polynomial formula')
                from fractions import Fraction
                exponent = Fraction(children[1].as_long()) if z3.is_int_value(children[1]) else children[1].as_fraction()
                if exponent.denominator != 1 or exponent < 0:
                    raise ValueError('Expected a nonnegative integer power')
                value = z3.RealVal(1)
                degree = 0
                for _ in range(int(exponent)):
                    if degree+child_degrees[0]<=1:
                        value=value*children[0];degree+=child_degrees[0]
                    else:
                        aux = z3.FreshReal('lift')
                        definitions.append(aux == value * children[0])
                        auxiliaries.append(aux)
                        value = aux;degree=1
            elif kind in (z3.Z3_OP_ADD, z3.Z3_OP_SUB, z3.Z3_OP_UMINUS):
                # Keep linear combinations intact; only nonlinear operations
                # need auxiliaries to bound the degree of the definitions.
                value=rebuilt;degree=max(child_degrees)
            else:
                raise ValueError('Unsupported arithmetic operator: ' + str(expr.decl()))
        else:
            value = rebuilt
        cache[key] = value
        degrees[key] = degree
        return value

    # Keep every simplified AST alive while its ID is used as a cache key;
    # otherwise Z3 may recycle an ID after a temporary root is released.
    simplified = [z3.simplify(a) for a in assertions]
    transformed = [visit(a) for a in simplified]
    return definitions + transformed, auxiliaries


def lifted_solver(timeout_ms):
    import z3
    # In particular, omit solve-eqs and disable NLSat substitution: otherwise
    # the definitions are expanded back into the original high-degree formula.
    solver = z3.Then('simplify', 'tseitin-cnf',
                     z3.With('nlsat', inline_vars=False)).solver()
    solver.set(timeout=timeout_ms)
    return solver
