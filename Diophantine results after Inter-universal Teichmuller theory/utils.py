# %%
from math import sqrt,log,ceil,exp,pi
from tqdm import trange,tqdm
from fractions import Fraction
# %%
def is_prime(n):
    if n < 2:
        return False
    for i in range(2,n):
        if n%i == 0:
            return False
        if i * i > n:
            break
    return True

def primes(n):
    if n < 2:
        return []
    res = list()
    sieve = [True] * (n+1)
    for p in range(2, n+1):
        if (sieve[p]):
            res.append(p)
            for i in range(2*p, n+1, p):
                sieve[i] = False
    return res
            
def prime_counting(x):
    return len(primes(int(x)))

def merge_intervals(intervals):
    intervals.sort(key=lambda x: x[0])
    merged = []
    for interval in intervals:
        if not merged or merged[-1][-1] < interval[0]:
            merged.append(interval)
        else:
            merged[-1][-1] = max(merged[-1][-1], interval[-1])
    return merged

# %% cf. Lemma 2.5 (i)
def f1(x):
    n = int(x)
    sum1, sum2, sum3 = 0, 0, 0
    for p in primes(n):
        sum1 += log(p) / (p-1)
        sum2 += log(p)
        sum3 += log(p) * p
    res = sum1 + (1+1/x)*sum2 - sum3/x
    return res

def f2(x):
    res = f1(3*x)
    res += (log(18)+(x-1)*log(x))/(3*x)
    res += log(32*9*pi*x*x)
    res *= (x*x+5*x) / (x*x+x-12)
    return res

def f3(x):
    res = f1(30*x+1)
    res += (log(2*9*625)+(x-1)*log(x))/(30*x)
    res += log(pow(2,7)*pow(3,5)*pow(5,2)*pi*x*x)
    res *= (x*x+5*x) / (x*x+x-12)
    return res

def list_of_f1(n):
    # the list [0,0,f1(2), ..., f(n)]
    # sieve for prime numbers <= n
    sieve = [True] * (n+1)
    for p in trange(2, n+1):
        if (sieve[p]):
            for i in range(2*p, n+1, p):
                sieve[i] = False
    # compute the values of $f1$
    res = [0] * (n+1)
    sum1, sum2, sum3 = 0, 0, 0
    for x in trange(2,n+1):
        if (sieve[x]):
            p = x
            sum1 += log(p) / (p-1)
            sum2 += log(p)
            sum3 += log(p) * p
        res[x] = sum1 + (1+1/x)*sum2 - sum3/x
    return res

def list_of_f2(n):
    # the list [0,0,0,0,f2(4), ..., f2(n)]
    list_of_f1_n = list_of_f1(3*n)
    res = [0] * (n+1)
    for x1,f1 in zip(trange(0,3*n+1), list_of_f1_n):
        if x1%3 != 0 or x1 < 12:
            continue
        x = x1 // 3
        tmp = f1 + (log(18)+(x-1)*log(x))/(3*x) + log(32*9*pi*x*x)
        tmp *= (x*x+5*x) / (x*x+x-12)
        res[x] = tmp
    return res

def list_of_f3(n):
    # the list [0,0,0,0,f3(4), ..., f3(n)]
    list_of_f1_n = list_of_f1(30*n+1)
    res = [0] * (n+1)
    for x1,f1 in zip(trange(0,30*n+2), list_of_f1_n):
        if (x1-1)%30 != 0 or x1 < 121:
            continue
        x = x1 // 30
        tmp = f1 + (log(2*9*625)+(x-1)*log(x))/(30*x) + log(pow(2,7)*pow(3,5)*pow(5,2)*pi*x*x)
        tmp *= (x*x+5*x) / (x*x+x-12)
        res[x] = tmp
    return res

# %% cf. Proposition 2.7 & its remark
def log_volume_at_p(l, p, ep, delta_p):
    l1 = l//2
    upper_bound = 0
    # the p-adic valuation of ep
    vp_ep = 0
    tmp_ep = ep
    while tmp_ep % p == 0:
        vp_ep += 1
        tmp_ep = tmp_ep / p
    # the value of dp
    if vp_ep == 0:
        dp = 1 - Fraction(1, ep)
    else:
        dp = vp_ep + 1
    # the value of ap and bp
    ap = Fraction(ep//(p-1) + 1, ep)
    bp = max(1-Fraction(p,ep), Fraction(-1,ep))

    # the contribution at vp in \log\rad(N)
    cp = delta_p * (1 - Fraction(1,3*l)) * (l+5) / 4

    # the upper bound of B_1(p)
    if delta_p == 0 or ep % l != 0:
        # In this case, v_p(N) \equiv 0 mod l
        for j in range(1,l1+1):
            upper_bound += max(ceil(j*dp+(j+1)*ap), (j+1)*(1+(p==2)))+ (j+1)*bp
        upper_bound = Fraction(upper_bound, l1) - cp
        return upper_bound
    if ep % l == 0:
        # the largest B_1(p) for vp(N) mod l in [1,2,...,l-1].
        tmp_upper_bounds = []
        for vp in range(1,l):
            tmp_upper_bound = 0
            for j in range(1,l1+1):
                lambda1 = Fraction(-j*j*vp,l)
                tmp_upper_bound += max(ceil(lambda1+j*dp+(j+1)*ap) - lambda1, (j+1)*(1+(p==2))) + (j+1)*bp
            tmp_upper_bounds.append(tmp_upper_bound)
        upper_bound = max(tmp_upper_bounds)
        upper_bound = Fraction(upper_bound, l1) - cp
        return upper_bound

def compute_log_volume(l, is_bad_at_2 = False):
    if l < 5:
        return 'NAN'
    my_primes = primes(3*l+1)
    res = 0
    for p in my_primes:
        tmp_volumes = []
        if p not in (2,3,l):
            for ep in (1, 3, l, 3*l):
                tmp_volumes.append(log_volume_at_p(l,p,ep,delta_p=1))
            tmp_volumes.append(log_volume_at_p(l,p,1,delta_p=0))
        elif p==3:
            for ep in (2,6,2*l, 6*l):
                tmp_volumes.append(log_volume_at_p(l,p,ep,delta_p=1))
            for ep in (2,6,8):
                tmp_volumes.append(log_volume_at_p(l,p,ep,delta_p=0))   
        elif p==l:
            for ep in (l-1,3*(l-1),l*(l-1),3*l*(l-1)):
                tmp_volumes.append(log_volume_at_p(l,p,ep,delta_p=1))
            for ep in (l-1,l*(l-1),l*l-1):
                tmp_volumes.append(log_volume_at_p(l,p,ep,delta_p=0))  
        else: # p==2
            for ep in (2,6,2*l,6*l):
                tmp_volumes.append(log_volume_at_p(l,p,ep,delta_p=1))
            if not is_bad_at_2:
                for ep in (2,4,6,8,12,16,24,48):
                    tmp_volumes.append(log_volume_at_p(l,p,ep,delta_p=0))
        tmp_volume = max(tmp_volumes)
        res += tmp_volume * log(p)
    res = res * Fraction(4*l,l*l+l-12) + log(pi) * Fraction(l*l+5*l,l*l+l-12)
    return res
