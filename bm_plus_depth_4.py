import collections
from basic_functionalities import *
import scipy.optimize as opt

set_vars = collections.namedtuple('BM', 'p d1 d2 d3 da1 da2 da3 db2 db3 dc3 la lb lc wa wb wc')

num_vars=16

def bm(f) : return wrap(f, set_vars)

k = lambda x : 0.1
w_=Hi(1-k([0]))
w = lambda x : w_

p3 = lambda x: x.p/2   + x.d3
p2 = lambda x: p3(x)/2 + x.d2
p1 = lambda x: p2(x)/2 + x.d1

wa3 = lambda x: x.wa/2   + x.da3
wa2 = lambda x: wa3(x)/2 + x.da2
wa1 = lambda x: wa2(x)/2 + x.da1

wb3 = lambda x: x.wb/2   + x.db3
wb2 = lambda x: wb3(x)/2 + x.db2

wc3 = lambda x: x.wc/2 + x.dc3

r1 = lambda x: reps(p2(x), x.d1, k(x)) 
r2 = lambda x: reps(p3(x), x.d2, k(x))
r3 = lambda x: reps(x.p  , x.d3, k(x))  

c1 = lambda x: x.la - reps(wa2(x), x.da1, x.la) 
c2 = lambda x: x.la - reps(wa3(x), x.da2, x.la) + x.lb - reps(wb3(x), x.db2, x.lb) 
c3 = lambda x: x.la - reps(x.wa  , x.da3, x.la) + x.lb - reps(x.wb  , x.db3, x.lb) + x.lc - reps(x.wc, x.dc3, x.lc)

L1 = lambda x: binomH((k(x))/2, (p1(x))/2.)
L2 = lambda x: binomH( k(x)    , p1(x)    ) - x.la + binomH(x.la,wa1(x)) 
L3 = lambda x: binomH( k(x)    , p2(x)    ) - x.la + binomH(x.la,wa2(x)) - x.lb + binomH(x.lb,wb2(x)) 
L4 = lambda x: binomH( k(x)    , p3(x)    ) - x.la + binomH(x.la,wa3(x)) - x.lb + binomH(x.lb,wb3(x)) - x.lc + binomH(x.lc,wc3(x))

constraints = [
#representation constraints
{ 'type' : 'eq',   'fun' : bm(lambda x : r1(x) - c1(x))},
{ 'type' : 'eq',   'fun' : bm(lambda x : r2(x) - c2(x)) },
{ 'type' : 'eq',   'fun' : bm(lambda x : r3(x) - c3(x)) },
    
#correctness
{ 'type' : 'ineq',   'fun' : bm(lambda x : (1 - k(x) - x.la              ) - (w(x) - x.p - x.wa              ))},
{ 'type' : 'ineq',   'fun' : bm(lambda x : (1 - k(x) - x.la - x.lb       ) - (w(x) - x.p - x.wa - x.wb       ))}, 
{ 'type' : 'ineq',   'fun' : bm(lambda x : (1 - k(x) - x.la - x.lb - x.lc) - (w(x) - x.p - x.wa - x.wb - x.wc))}, 
{ 'type' : 'ineq',   'fun' : bm(lambda x :  1 - k(x) - x.la - x.lb - x.lc                                  )}, 
    
{ 'type' : 'ineq',   'fun' : bm(lambda x : w(x) - x.p - x.wa - x.wb - x.wc) },

{ 'type' : 'ineq',   'fun' : bm(lambda x : k(x) - x.p - x.d3  )},
{ 'type' : 'ineq',   'fun' : bm(lambda x : k(x) - p3(x) - x.d2)},
{ 'type' : 'ineq',   'fun' : bm(lambda x : k(x) - p2(x) - x.d1)},
{ 'type' : 'ineq',   'fun' : bm(lambda x : k(x) - p1(x)       )},
    
{ 'type' : 'ineq',   'fun' : bm(lambda x : x.la - x.wa   - x.da3) },    
{ 'type' : 'ineq',   'fun' : bm(lambda x : x.la - wa3(x) - x.da2) },
{ 'type' : 'ineq',   'fun' : bm(lambda x : x.la - wa2(x) - x.da1) },
{ 'type' : 'ineq',   'fun' : bm(lambda x : x.la - wa1(x)        ) },
    
{ 'type' : 'ineq',   'fun' : bm(lambda x : x.lb - x.wb   - x.db3) },    
{ 'type' : 'ineq',   'fun' : bm(lambda x : x.lb - wb3(x) - x.db2) },
{ 'type' : 'ineq',   'fun' : bm(lambda x : x.lb - wb2(x))         },
    
{ 'type' : 'ineq',   'fun' : bm(lambda x : x.lc - x.wc   - x.dc3) }, 
{ 'type' : 'ineq',   'fun' : bm(lambda x : x.lc - wc3(x))         },
]

def indyk_nn(size,length,w2,w1):
    """
    w1: weight of elements in list
    w2: target difference
    size: list size
    length: length of vectors
    """
    if length<0.0001 or w1<0.000001:
        return 2*size
    
    n_w1=w1/length
    n_w2=w2/length
    n_size=size/length
    
    if size >=binomH(length,w1) or n_w2>2*n_w1*(1-n_w1):
        return 2*size
    lam=min(1/2*(2*n_w1**2 - 2*n_w1 + n_w2)/(n_w1**2 - n_w1), -n_size*log2(2)/log2(2*n_w1**2 - 2*n_w1 + 1))
    
    return( binomH(1,n_w2)-binomH(1-lam,n_w2)+max(2*n_size+log2(1-n_w1*(1-n_w1)*2)*lam,n_size))*length

def prob_p(k,delta):
    return binomH(k,k*delta)-k

def prob_q(k,delta,gamma):
    return binomH(gamma*k,gamma*k/2)+binomH((1-gamma)*k,(delta-gamma/2)*k)-k

def mo_plus(lam,n,gamma,w2,w1,l):
    if n<=0:
        return 100
    lam=lam/n
    lam_prime=lam
    if lam > 1:
        lam=0.99999999
    gamma=gamma/n
    
    if gamma>0.5:
        gamma=1-gamma
    def opti(x):
        r=10000000000
        k=1/r
        return max(-r*prob_q(k,x,gamma),lam+(r-1)*prob_p(k,x)-r*prob_q(k,x,gamma),indyk_nn(lam_prime+r*prob_p(k,x),l,w2,w1)-prob_q(k,x,gamma)*r)
    r=10000000000
    k=1/r
    a= opt.fminbound(opti, 0,0.5, xtol=1e-10, full_output=1)
    
    return min(2*lam_prime*n,a[1]*n)


def memory(x):
    return max(L1(x),L2(x),L3(x),L4(x))

def time_lists(x):
    timeL1=mo_nn(L1(x), x.la, wa1(x))
    
    timeL2=mo_plus(L2(x), x.lb, wb2(x),p2(x),p1(x),k(x))
    timeL3=mo_plus(L3(x), x.lc, wc3(x),p3(x),p2(x),k(x))
    timeL4=mo_plus(L4(x), 1 - k(x) -x.la - x.lb - x.lc, w(x) - x.p - x.wa - x.wb - x.wc,x.p,p3(x),k(x))
    
    return timeL1, timeL2, timeL3, timeL4

def time_perms(x):
    perms_p = binomH(1.                    , w(x)                    ) - binomH(1 - k(x)                     , w(x) - x.p                     ) - binomH(k(x), x.p )
    perms_a = binomH(1 - k(x)              , w(x) - x.p              ) - binomH(1 - k(x) - x.la              , w(x) - x.p - x.wa              ) - binomH(x.la, x.wa)
    perms_b = binomH(1 - k(x) - x.la       , w(x) - x.p - x.wa       ) - binomH(1 - k(x) - x.la - x.lb       , w(x) - x.p - x.wa - x.wb       ) - binomH(x.lb, x.wb)
    perms_c = binomH(1 - k(x) - x.la - x.lb, w(x) - x.p - x.wa - x.wb) - binomH(1 - k(x) - x.la - x.lb - x.lc, w(x) - x.p - x.wa - x.wb - x.wc) - binomH(x.lc, x.wc)
    
    return perms_p, perms_a, perms_b, perms_c

def time(x):  
    x = set_vars(*x)
    perms_p, perms_a, perms_b, perms_c = time_perms(x)
    timeL1, timeL2, timeL3, timeL4 = time_lists(x)
    
    return perms_p + perms_a + max(timeL1, perms_b + timeL2, perms_b + perms_c + max(timeL3,timeL4))



