from random import uniform as ru
from math import*
import numpy as np
from scipy.optimize import fsolve

def Hi(v):
    if v==1:
        return 0.5
    if v<0.00001:
        return 0

    return fsolve(lambda x:v -(-x*log2(x)-(1-x)*log2(1-x)),0.0000001)[0]


def H(c):
    if c == 0. or c == 1.:
        return 0.
    
    if c < 0. or c > 1.:
        return -1000
    
    return -(c * log2(c) + (1 - c) * log2(1 - c))

def binomH(n,k):
    if k>n or n==0:
        return 0
    if k==n:
        return 0
    return n * H(k/n)

def wrap(f,g) :
    def inner(x):
        return f(g(*x))
    return inner

def r(x,y,z):
    return [(ru(x,y)) for i in range(z)]

def mo_nn(L,n,w):
    if n<=0 or L<0:
        return 100
    Lnorm=L/n
    if Lnorm>0.999999999:
        Lnorm=0.999999999
        
    wnorm=w/n
    if wnorm>0.5:
        wnorm=1-wnorm

    d=Hi(1-Lnorm)

    if wnorm<=2*d*(1-d):
        mo_exp=(1-wnorm)*(1-H((d-wnorm/2)/(1-wnorm))) 
    else:
        mo_exp=2*Lnorm+H(wnorm)-1
    return max(mo_exp*n,2*L-n+binomH(n,w))

def reps(p, d, l): 
    if p == 0. or l == 0.:
        return 0
    if l < p or l - p < d:
        return 0.
    return binomH(p, p/2.) + binomH(l-p, d) 

