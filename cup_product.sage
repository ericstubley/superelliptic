#! /usr/local/bin/sage

def is_l_th_power(l, a):
	q = a.parent().order()
	if l.divides(q-1):		
		ex = (q - 1)/l
		return (a^(ex) == 1)
	else:
		return True


def frobenius_coefficients(q, pol):
	# return the polynomial obtained by applying Frob_q to the coefficients of pol

	frob_pol = 0
	v = pol.variables()[0]
	for i in range(pol.degree()+1):
		ai = pol.monomial_coefficient(v^i)
		frob_ai = ai^q
		frob_pol += frob_ai*(v^i)
	return frob_pol


def all_irred_polynomials(q, d):
    # return the list of all irreducible polynomials over Fq of degree d
    R.<x> = PolynomialRing(GF(q), 'x')
    base = x^(q^d) - x
    factors = [t[0] for t in base.factor() if t[0].degree() == d]
    return factors


def frobenius_order_factors(K, q, f):
	# return the irreducible factors of f over K, forgetting multiplicities
	# the important feature here is that we put the factors in Frobenius order
	R.<x> = PolynomialRing(K, 'x')
	new_f = R(f)
	# the list that new_f.factor() generates is not necessarily in the correct Frobenius order!	
	# so we create that list by hand
	f0 = new_f.factor()[0][0]
	new_factors = [f0]
	fi = f0

	while True:
		f_next = frobenius_coefficients(q, fi)
		if f_next == f0:
			break
		else:
			new_factors.append(f_next)
			fi = f_next

	return new_factors


def test_product_with_b(ls, l, q, j):
	# return the sum_i f_i(alpha_0)^(q^(i(j-1)) - 1) product, where ls is the f_i(alpha_0)
	# pass it j=l-1 rather than j=0
	# should pass it a list of length of l-1 with the first factor being 0

	aj = l-1 if j == 0 else j
	power_ls = [ls[i]^(q^(i*(aj-1)) - 1) for i in range(1, len(ls))]
	prod = product(power_ls)
	return prod


def test_product_with_a0(ls, l, q, j):
	# return the sum_i f_i(alpha_0)^(q^(i(j-1)) - 1) product, where ls is the f_i(alpha_0)
	# pass it j=l-1 rather than j=0
	# should pass it a list of length of l-1 with the first factor being 0

	aj = l-1 if j == 0 else j
	power_ls = [ls[i]^(q^(i*(l-2)) - q^(i*(aj-1))) for i in range(1, len(ls))]
	prod = product(power_ls)
	return prod


def test_product_with_dual(ls, l, q, j):
	# same deal but now with the dual pair instead of b

	ex1 = j-1
	ex2 = l-1 - j

	power_ls = [ls[i]^(q^(i*ex1) - q^(i*ex2)) for i in range(1, len(ls))]
	prod = product(power_ls)
	return prod


def data_set(output_file, l, q, d):
    with open(output_file, 'w') as fout:
        fout.write(f"l, q, d, gamma, r, polynomial, cup products aj cup b (0=vanish | 1=not) for j=0..l-2\n")

        print(f"Computing all irreducibles of degree {d} over F_{q}")
        polynomials = all_irred_polynomials(q, d)

        F = GF(q)
        gamma = GF(l)(q).multiplicative_order()
        r = gcd(d, gamma)

        print("Looping over polynomials")
        for index, pol in enumerate(polynomials):
            print(f"\r{index+1}/{len(polynomials)}", end='')
            cup_products = polynomial_cup_products(F, l, pol)
            vanishing = ["0" if c == True else "1" for c in cup_products]
            vanishing_string = ", ".join(vanishing)

            output_string = f"{l}, {q}, {d}, {gamma}, {r}, {pol}, {vanishing_string}\n"
            fout.write(output_string)
        print("\nDone!")



def polynomial_cup_products(F, l, pol):
    Fgamma.<z> = F.extension(pol)
    ordered_factors = frobenius_order_factors(Fgamma, F.order(), pol)
    root = ordered_factors[0].roots()[0][0]
    evaluated_factors = [a(root) for a in ordered_factors]
    assert evaluated_factors[0] == 0

    cup_products = []
    for j in range(0, l-1):
        kummer_quotient = test_product_with_b(evaluated_factors, l, F.order(), j)
        cup_products.append(is_l_th_power(l, kummer_quotient))

    return cup_products


if __name__ == "__main__":
    data_set("cup_product_7_2_3.txt", 7, 2, 3)


# def main_loop():
# 	for q in primes(10):
# 		if q.mod(l) in [3, 5]:
# 			F = GF(q)
# 			R.<x> = PolynomialRing(F, 'x')
# 			pol = R.irreducible_element(l-1)
# 
# 			FF.<z> = F.extension(pol)
# 			factors_ls = irred_factors(FF, q, pol)
# 			root = factors_ls[0].roots()[0][0]
# 			fi_ls = [a(root) for a in factors_ls]
# 			print("Sanity Check: {}".format(fi_ls[0] == 0))
# 			for j in [0, 1, 2, 3, 4, 5]:
# 				prod = test_product_with_b(fi_ls, q, j)
# 				print("{}, {}, {}, {}".format(q, j, pol, is_l_th_power(prod)))
# 			for j in [0, 1, 2, 3, 4, 5]:
# 				prod = test_product_with_a0(fi_ls, q, j)
# 				print("{}, {}, {}, {}".format(q, j, pol, is_l_th_power(prod)))
# 
# 			for j in [1, 3, 5]:
# 				prod = test_product_with_dual(fi_ls, q, j)
# 				print("{}, {}, {}, {}".format(q, j, pol, is_l_th_power(prod)))
