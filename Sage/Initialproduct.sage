# Input : a polynomial `f` and a set of polynomials `S`
# Output : the I_k and e_k produced by pseudo division
def pseudo_division(f, C, V):
    """
    Input:
    f: polynomial
    C: characteristic set [c1, c2, ..., cs]
    V: variables list [x1, x2, ..., xs]

    Return:
    r: remainder
    I_list: initial list
    E_list: exponent list
    """
    s = len(C)
    r = f

    I_list = [1] * s
    E_list = [0] * s

    for k in range(s - 1, -1, -1):
        c = C[k]
        x = V[k]

        deg_c = c.degree(x)
        
        I_k = c.coefficient({x: deg_c})

        I_list[k] = I_k
        e_k = 0

        while r != 0 and r.degree(x) >= deg_c:
            deg_r = r.degree(x)
            
            lc_r = r.coefficient({x: deg_r})


            r = I_k * r - lc_r * c * (x**(deg_r - deg_c))

            e_k += 1

        E_list[k] = e_k

    return r, I_list, E_list

R.<x0, x1, x2, x3, x4, x5, x6, x7> = PolynomialRing(QQ, order='lex')


c1 = x0-x1-x2+x3
c2 = x4-x5-x6+x7
C = [c1, c2]
V = [x3, x7]

f = x0 + x3 - (x1+x2)

r, I_list, E_list = pseudo_division(f, C, V)

print("被除数 f =", f)
print("-" * 30)
print("最终伪余 r =", r)
print(f"初式列表 I = {I_list}")
print(f"幂次列表 E = {E_list} ")