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



Fq = 21888242871839275222246405745257275088696311157297823662689037894645226208583
Fr = 21888242871839275222246405745257275088548364400416034343698204186575808495617
non_residue = 1
curve_b_coef = 3
base_field = GF(Fq)
scalar_field = GF(Fr)
R.<x>=PolynomialRing(field)
base_field_ext = field.extension(x^2 + non_residue, 'a')

base_curve = EllipticCurve(base_field, [0, non_residue])
ext_curve = EllipticCurve(base_field_ext, [0, non_residue])
num_of_points = base_curve.order()
trace_of_frobenius = Fq + 1 - num_of_points
s_0 = 2 
s_1 = trace_of_frobenius
s_2 = trace_of_frobenius * s_1 - Fq * s_0
num_of_points_ext = Fq^2 + 1 - s_2
print "here"
print factor(num_of_points_ext)


from enum import Enum

class Curve(Enum):
    BN256 = 0
    BLS12 = 1
    SECP256K1 = 2


class Params:
    def __init__(self, mode):
        if isinstance(Curve.BN256, mode):
            self.Fq = 21888242871839275222246405745257275088696311157297823662689037894645226208583
            self.Fr = 21888242871839275222246405745257275088548364400416034343698204186575808495617
            self.non_residue = Fq - 1
            self.curve_b_coef = 3
            self.is_prime_order_curve = True
        elif isinstance(Curve.BN256, mode):
            self.Fr = 52435875175126190479447740508185965837690552500527637822603658699938581184513
            self.Fq = 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787
        else:
            print "ewwq"
# def gen_params_for_BN256_curve():
#     
    

# def

    
# base_field = GF(Fq)
# scalar_field = GF(Fr)
# R.<x>=PolynomialRing(base_field)
# base_field_ext = base_field.extension(x^2 - non_residue, 'a')

# base_curve = EllipticCurve(base_field, [0, curve_b_coef])
# ext_curve = EllipticCurve(base_field_ext, [0, curve_b_coef])
# num_of_points = base_curve.order()
# cofactor = 2*Fq + 2 - num_of_points
# ext_num_of_points = num_of_points * cofactor
# # s_2 = t^2 - 2p = (p+1 - n)^2 - 2p = (p+1)^2 +n^2 - 2 (p+1) * n - 2p = p^2 + 1 + n^2 - 2 * (p+1) * n
# # x = p^2 + 1 - (p^2 + 1 + n^2 - 2 * (p+1) * n) = 2*(p+1)*n - n^2 = n * (2p+2 - n) 
# # if n is odd, then cofactor is also odd
# print num_of_points == Fr
# print factor(cofactor)

# # what if cofactor is divisible by 3?


from enum import Enum

class Curve(Enum):
    BN256 = 0
    BLS12 = 1
    SECP256K1 = 2


class Params:
    def __init__(self, mode):
        if mode == Curve.BN256:
            self.Fq = 21888242871839275222246405745257275088696311157297823662689037894645226208583
            self.Fr = 21888242871839275222246405745257275088548364400416034343698204186575808495617
            self.non_residue = -1
            self.curve_b_coef = 3
            self.is_prime_order_curve = True
        elif mode == Curve.BLS12:
            self.Fr = 52435875175126190479447740508185965837690552500527637822603658699938581184513
            self.Fq = 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787
            self.non_residue = -1
            self.curve_b_coef = 4
            self.is_prime_order_curve = False
        elif mode == Curve.SECP256K1:
            print "here"
            self.Fr = 115792089237316195423570985008687907852837564279074904382605163141518161494337
            self.Fq = 115792089237316195423570985008687907853269984665640564039457584007908834671663
            self.non_residue = -1
            self.curve_b_coef = 7
            self.is_prime_order_curve = True
        else:
            raise ValueError("Unreachable")
                     
mode = Curve.BLS12
print mode
params = Params(mode)

assert kronecker(params.non_residue, params.Fq) == -1
base_field = GF(params.Fq)
scalar_field = GF(params.Fr)
R.<x>=PolynomialRing(base_field)
base_field_ext = base_field.extension(x^2 - params.non_residue, 'a')
 
base_curve = EllipticCurve(base_field, [0, params.curve_b_coef])
ext_curve = EllipticCurve(base_field_ext, [0, params.curve_b_coef])
num_of_points = base_curve.order()

if params.is_prime_order_curve:
    assert params.Fr == num_of_points
    cofactor = 2*params.Fq + 2 - num_of_points
    print cofactor % 3
else:
    print factor(num_of_points)