from enum import Enum
from functools import reduce 


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
            self.curve_a_coef = 0
            self.curve_b_coef = 3
            self.is_prime_order_curve = True
        elif mode == Curve.BLS12:
            self.Fr = 52435875175126190479447740508185965837690552500527637822603658699938581184513
            self.Fq = 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787
            self.non_residue = -1
            self.curve_a_coef = 0
            self.curve_b_coef = 4
            self.is_prime_order_curve = False
        elif mode == Curve.SECP256K1:
            self.Fr = 115792089237316195423570985008687907852837564279074904382605163141518161494337
            self.Fq = 115792089237316195423570985008687907853269984665640564039457584007908834671663
            self.non_residue = -1
            self.curve_a_coef = 0
            self.curve_b_coef = 7
            self.is_prime_order_curve = True
        else:
            raise ValueError("Unreachable")
            
                     
mode = Curve.BN256
print mode
params = Params(mode)

assert kronecker(params.non_residue, params.Fq) == -1
base_field = GF(params.Fq)
scalar_field = GF(params.Fr)
R.<x>=PolynomialRing(base_field)
base_field_ext = base_field.extension(x^2 - params.non_residue, 'a')
 
base_curve = EllipticCurve(base_field, [params.curve_a_coef, params.curve_b_coef])
ext_curve = EllipticCurve(base_field_ext, [params.curve_a_coef, params.curve_b_coef])
num_of_points = base_curve.order()

if params.is_prime_order_curve:
    # ext_num_of_points = num_of_points * cofactor
    # using the strategy from John J. McGee thesis: 
    # "René Schoof’s Algorithm for Determining the Order of the Group of Points 
    # on an Elliptic Curve over a Finite Field"
    # https://math.stackexchange.com/questions/144194/how-to-find-the-order-of-elliptic-curve-over-finite-field-extension?rq=1
    # s_2 = t^2 - 2p = (p+1 - n)^2 - 2p = (p+1)^2 +n^2 - 2 (p+1) * n - 2p = p^2 + 1 + n^2 - 2 * (p+1) * n
    # x = p^2 + 1 - (p^2 + 1 + n^2 - 2 * (p+1) * n) = 2*(p+1)*n - n^2 = n * (2p+2 - n) 
    # if n is odd, then cofactor is also odd
    assert params.Fr == num_of_points
    cofactor = 2*params.Fq + 2 - num_of_points
    num_of_points_ext = params.Fr * cofactor
    factors = list(factor(cofactor))
    
    offset_0_order = factors[0][0]
    offset_1_order = factors[-1][0]
    assert offset_0_order == 3
    assert offset_1_order != params.Fr
    assert factors[0][1] == 1
    assert factors[-1][1] == 1
    
    cofactor_0 = reduce(lambda acc, x : acc * x[0] * x[1], factors[1:], 1)
    cofactor_0 *= params.Fr
    cofactor_1 = reduce(lambda acc, x : acc * x[0] * x[1], factors[:-1], 1)
    cofactor_1 *= params.Fr
    
    point_at_infty = ext_curve(0, 1, 0)
    Q1 = point_at_infty
    Q2 = point_at_infty
    
    while Q1 == point_at_infty:
        P = ext_curve.random_point()
        Q1 = cofactor_0 * P
    assert offset_0_order * Q1 == point_at_infty
    
    while Q2 == point_at_infty:
        P = ext_curve.random_point()
        Q2 = cofactor_1 * P
    assert offset_1_order * Q2 == point_at_infty
    
    print "point on E(F_q^2) of order 3 is: ", Q1
    print "point on E(F_q^2) of large order coprime to Fr=|E(F_q)| is: ", Q2
else:
    factors = list(factor(num_of_points))
    print factors
    assert factors[0][0] == 3
    assert factors[0][1] == 1
    assert factors[-1][0] == params.Fr
    assert factors[-1][1] == 1
    assert len(factors) > 2 
    factors = factors[:-1]
    
    offset_0_order = factors[0][0]
    offset_1_order = factors[-1][0] * factors[-1][1]
    
    cofactor_0 = reduce(lambda acc, x : acc * x[0] * x[1], factors[1:], 1)
    cofactor_0 *= params.Fr
    cofactor_1 = reduce(lambda acc, x : acc * x[0] * x[1], factors[:-1], 1)
    cofactor_1 *= params.Fr
    
    point_at_infty = base_curve(0, 1, 0)
    Q1 = point_at_infty
    Q2 = point_at_infty
    
    while Q1 == point_at_infty:
        P = base_curve.random_point()
        Q1 = cofactor_0 * P
    assert offset_0_order * Q1 == point_at_infty
    
    while Q2 == point_at_infty:
        P = base_curve.random_point()
        Q2 = cofactor_1 * P
    assert offset_1_order * Q2 == point_at_infty
    
    print "point on E(F_q) of order 3 is: ", Q1
    print "point on E(F_q) of large order coprime to Fr is: ", Q2
    
# From now we are going to calculate endomorphism parameters : Phi = \lambda P(x, y) = (\beta x, y)
# For the existense of this particular enodmorphism Phi the following conditions should be fullfilled:
# Fq ≡ 1 (mod 3) be a prime, and the equation of the curve is E: y^2 = x^3 + b (a = 0)
# \beta is element of F_q* of order 3
# characteristic poly for Phi is X^2 + X + 1: lambda is the solution to characteristic poly mod Fr
# in general there are two roots: \lambda1 and \lambda 2, but only one of the satisfies: \lambda P(x, y) = (\beta x, y)
# reference: Guide to Elliptic Curve Cryptography (book), section 3.5
assert params.curve_a_coef == 0
assert params.Fq % 3 == 1
power = int((params.Fq - 1) / 3)
beta = base_field.multiplicative_generator()^power

R.<y>=PolynomialRing(scalar_field)
roots = (y^2+y+1).roots(multiplicities=False)
assert roots[0] != roots[1]

P = base_curve.random_point()
R1 = int(roots[0]) * P
R2 = int(roots[1]) * P
first_root_is_ok = R1[0] == int(beta) * P[0] and R1[1] == P[1]
second_root_is_ok = R2[0] == int(beta) * P[0] and R2[1] == P[1]
assert first_root_is_ok ^ second_root_is_ok
Lambda = roots[0] if first_root_is_ok else roots[1]
print "lambda: ", int(Lambda)
print "beta: ", int(beta)

# Decomposition of the scalar k in two scalars k1 and k2 with half bit-length, such that k=k1+k2 * \lambda (mod Fr)
# requires precomputation of auxiliary biguints a1, a2, b1, b2
# reference: Guide to Elliptic Curve Cryptography (book), Algorithm 3.74
bound = params.Fr.isqrt()
u = params.Fr
v = int(Lambda)
x1 = 1; y1 = 0; x2 = 0; y2 = 1
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
        a1 = r 
        b1 = -y1
        r_l = x2 * params.Fq + y2 * int(Lambda)
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
        break
        
print "a1: ", a1
print "a2: ", a2
print "minus_b1: ", -b1
print "b2: ", b2