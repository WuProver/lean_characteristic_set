
R.<X0, X1, X2, X3, X4, X5, X6, X7> = PolynomialRing(QQ, order='lex')
p1 = X1 - X0 - (X3 - X2)
p2 = X2 - X0 - (X3 - X1)
p3 = X5 - X4 - (X7 - X6)
p4 = X6 - X4 - (X7 - X5)
I = R.ideal(p1, p2, p3, p4)


char_sets = singular.char_series(I)
print(char_sets)