import sympy as sp

def get_class(P, vars_list):
    """Obtain the mainvariable"""
    for x in reversed(vars_list):
        if sp.degree(P, x) > 0:
            return x
    return None

def get_basic_set(Polys, vars_list):
    """Obtain the basic set"""
    def sort_key(p):
        c = get_class(p, vars_list)
        if c is None: return (-1, 0)
        return (vars_list.index(c), sp.degree(p, c))

    sorted_polys = sorted(Polys, key=sort_key)

    ASC = []
    used_classes = set()
    for p in sorted_polys:
        c = get_class(p, vars_list)
        if c is not None and c not in used_classes:
            ASC.append(p)
            used_classes.add(c)
    return ASC

def wu_characteristic_set(polys, vars_list):
    if not polys:
        return []

    F = [sp.expand(p) for p in polys if p != 0]

    while True:
        if not F:
            return []

        ASC = get_basic_set(F, vars_list)

        added_new = False
        new_F = list(ASC)

        for p in F:
            if p in ASC:
                continue
            R = p
            for q in reversed(ASC):
                c = get_class(q, vars_list)
                if sp.degree(R, c) > 0:
                    R = sp.prem(R, q, c)
            R = sp.expand(R)

            if R != 0 and R not in new_F:
                new_F.append(R)
                added_new = True

        if not added_new:
            return ASC

        F = new_F

if __name__ == "__main__":
    X = sp.symbols('X0:8')
    vars_list = list(X)

    p1 = X[1] - X[0] - (X[3] - X[2])
    p2 = X[2] - X[0] - (X[3] - X[1])
    p3 = X[5] - X[4] - (X[7] - X[6])
    p4 = X[6] - X[4] - (X[7] - X[5])

    input_polys = [p1, p2, p3, p4]

    char_set = wu_characteristic_set(input_polys, vars_list)

    for i, poly in enumerate(char_set):
        print(f"C_{i+1} = {poly}")