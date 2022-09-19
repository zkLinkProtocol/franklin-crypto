# Decomposition of the scalar k in two scalars k1 and k2 with half bit-length, such that k=k1+k2*THETA (mod p)
# param theta is a root of the characteristic polynomial of an endomorphism of the curve
def endomorphism_params_calc(theta, n):
    bound = n.isqrt()
    u = n
    v = theta
    x1 = 1 
    y1 = 0
    x2 = 0
    y2 = 1
    while True:
        q = int(v/u)
        r = v - q*u 
        x = x2 - q*x1
        y = y2 - q*y1
        v = u
        u = r
        x2 = x1
        x1 = x
        y2 = y1
        y1 = y
        if r < bound:
            a1= r 
            b1 = -y1
            r_l = x2 * n + y2 * theta
            t_l = y2
            q = int(v/u)
            r_l2 = v - q*u 
            x_l2 = x2 - q*x1
            y_l2 = y2 - q*y1
            if r_l^2 + t_l^2 <= r_l2^2 + y_l2^2:
                a2 = r_l,
                b2 = -t_l
            else:
                a2 = r_l2
                b2 = -y_l2
            return (a1, b1, a2, b2)
            
            

n = 1461501637330902918203687013445034429194588307251
theta = 903860042511079968555273866340564498116022318806
print endomorphism_params_calc(theta, n)

Fq = 21888242871839275222246405745257275088696311157297823662689037894645226208583
Fr = 21888242871839275222246405745257275088548364400416034343698204186575808495617
Fs = 21888242871839275222246405745257275088844257914179612981679871602714643921551
# char poly is X^2 + X + 1
# lambda is the solution to char poly mod Fr
# R.<k>=PolynomialRing(GF(Fr))
# print (k^2+k+1).roots()
lambda1 = 21888242871839275217838484774961031246154997185409878258781734729429964517155
lambda2 = 4407920970296243842393367215006156084916469457145843978461
print factor(Fq - 1)
field = GF(Fq)
beta = field(3)^(2 * 3 * 13 * 29 * 67 * 229 * 311 * 983 * 11003 * 405928799 * 11465965001 * 13427688667394608761327070753331941386769)
print beta
curve = EllipticCurve(field, [0, 3])
P = curve.random_point()
print lambda1 * P
print beta * P[0], P[1]
theta = lambda1
print endomorphism_params_calc(theta, Fr)
print beta

curve = EllipticCurve(field, [0, 3 * 2])
print curve.order()
print kronecker(1, Fq)
print 2035606587081052595668915734308926583248756937628697600630080524202006037398219 / Fq
print 93 * Fq