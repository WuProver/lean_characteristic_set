# input : Mvpolynomial set `S = [f1,...fn]`
# output : The characteristic sets of S decomposed by Wu's method,
import argparse
import re
import io
import sys
import contextlib
import json

from sage.all import PolynomialRing, QQ, singular

def extract_vars(set_str):
    tokens = re.findall(r'[a-zA-Z_][a-zA-Z0-9_]*', set_str)
    seen = set()
    unique_vars = []
    for var in tokens:
        if var not in seen:
            seen.add(var)
            unique_vars.append(var)

    def natural_keys(text):
        return [int(c) if c.isdigit() else c for c in re.split(r'(\d+)', text)]

    unique_vars.sort(key=natural_keys)
    return unique_vars

def create_polynomial_ring(vars_list, order='lex', base_ring=QQ):
    if order not in ['lex', 'degrevlex', 'deglex']:
        raise ValueError(f"Unsupported order: {order}")
    R = PolynomialRing(base_ring, vars_list, order=order, implementation="singular")
    return R

def get_main_var(poly, ring):
    if poly.is_zero():
        return None
    for var in ring.gens():
        if poly.degree(var) > 0:
            return var
    return None

def convert_poly_to_json(poly, vars_list):
    terms_list = []
    ring_gens = poly.parent().gens()

    if poly.is_zero():
        terms_list.append({"c": [int(0), int(1)], "e": []})
    else:
        for exp_tuple, coeff in poly.dict().items():
            if hasattr(coeff, 'numerator') and hasattr(coeff, 'denominator'):
                coeff_num = int(coeff.numerator())
                coeff_den = int(coeff.denominator())
            else:
                coeff_num = int(coeff)
                coeff_den = 1

            exponent_pairs = []
            for i, power in enumerate(exp_tuple):
                if power != 0:
                    var_name = str(ring_gens[i])
                    match = re.search(r'_(\d+)$', var_name)
                    if match:
                        real_index = int(match.group(1))
                    else:
                        try:
                            real_index = vars_list.index(var_name)
                        except ValueError:
                             raise ValueError(f"Variable {var_name} not found.")

                    exponent_pairs.append([real_index, int(power)])

            exponent_pairs.sort(key=lambda x: x[0])
            terms_list.append({"c": [coeff_num, coeff_den], "e": exponent_pairs})

    return terms_list


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Compute Characteristic Series and Exact I_G")
    parser.add_argument('-s', '--set', type=str, required=True, help="Input polynomial set, e.g. '[X_1-X_0, X_2-X_1]'")
    args = parser.parse_args()

    try:
        vars_list = extract_vars(args.set)

        if not vars_list:
            raise ValueError("We can not find any variable in the input polynomials")

        ring = create_polynomial_ring(vars_list)

        with contextlib.redirect_stdout(io.StringIO()):
            ring.inject_variables()

        cleaned_str = args.set.strip().strip('[]')
        if not cleaned_str:
            poly_objs = []
        else:
            str_list = [s.strip() for s in cleaned_str.split(',') if s.strip()]
            poly_objs = [ring(s) for s in str_list]

        if not poly_objs:
            print(json.dumps([]))
            sys.exit(0)


        I = ring.ideal(poly_objs)

        char_sets_singular = singular.char_series(I)

        # results = []
        # num_components = int(char_sets_singular.size())

        # cs_ideal = char_sets_singular[1]
        # num_polys = int(cs_ideal.size())

        # cs_polys_json = []
        # for j in range(1, num_polys + 1):
        #     p = ring(cs_ideal[j])
        #     cs_polys_json.append(convert_poly_to_json(p, vars_list))

        # results.append(cs_polys_json)

        # print(json.dumps(results))
        print(f"{char_sets_singular}")



    except Exception as e:
        sys.stderr.write(f"\n[!!! CharSet Error !!!] : {e}\n")
        import traceback
        traceback.print_exc(file=sys.stderr)
        sys.exit(1)