"""Exact comparison with the proposed corrected Gaussian envelope."""
from fractions import Fraction as F
from pathlib import Path
from centered_permanent_coefficients import coefficients
from verify_regular_catalogue_results import parse


def multiply(a, b):
    n = len(a)
    return [[sum(a[i][k]*b[k][j] for k in range(n)) for j in range(n)]
            for i in range(n)]


def envelope(s):
    n = len(s)
    gram = [[sum(s[i][k]*s[j][k] for k in range(n)) for j in range(n)]
            for i in range(n)]
    power = [[int(i == j) for j in range(n)] for i in range(n)]
    log_coeff = [F(0)]*(n//2+1)
    for m in range(1, n//2+1):
        power = multiply(power, gram)
        log_coeff[m] = F(sum(power[i][i] for i in range(n)), 2*m*n**(2*m))
    log_coeff[1] += F(1, 2*n)
    result = [F(1)]
    for m in range(1, n//2+1):
        result.append(sum(k*log_coeff[k]*result[m-k] for k in range(1, m+1))/m)
    return result


def main():
    lines = (Path(__file__).parent/'rt11.txt').read_text().splitlines()
    for line in (210, 902, 1223):
        rows = parse(lines[line-1], 11)
        s = [[0 if i == j else (1 if rows[i] >> j & 1 else -1)
              for j in range(11)] for i in range(11)]
        actual = coefficients(s, 11)
        upper = envelope(s)
        print('line', line, 'rows', rows, flush=True)
        for m in range(1, 6):
            print('degree', 2*m, 'actual', actual[2*m], 'envelope', upper[m],
                  'ratio', float(actual[2*m]/upper[m]),
                  'FAIL' if actual[2*m] > upper[m] else 'holds', flush=True)


if __name__ == '__main__':
    main()
