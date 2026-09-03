import numpy as np, json, sys, time
from opt import Solver, h, F_easy

class Solver2(Solver):
    def __init__(self, *a, umargin=1e-5, **k):
        super().__init__(*a, **k)
        self.Ubase = np.minimum(h(self.mu), F_easy(self.mu)) + umargin   # chord-error margin
        self.U = self.Ubase.copy()
    def min_slope(self, lamv, Fv):
        lY = self.logYmax_curve(lamv)
        g = self.logX + lamv*lY
        def slope_for(M):
            target = -2.0*Fv - lamv*np.log(M)
            idx = np.nonzero(g >= target)[0]
            if idx.size == 0: return np.inf, None, None
            i = idx[-1]; lx, lYv = self.logX[i], lY[i]
            if i+1 < len(self.logX) and g[i] != g[i+1]:
                t = (g[i]-target)/(g[i]-g[i+1])
                lx = self.logX[i] + t*(self.logX[i+1]-self.logX[i]); lYv = lY[i] + t*(lY[i+1]-lY[i])
            if lx >= np.log1p(-M): return np.inf, None, None
            q = (lx - np.log1p(-M))*(1-M)
            return -np.log(-np.expm1(q)), lx, lYv
        vals = [slope_for(M)[0] for M in self.Mgrid]
        i = int(np.argmin(vals))
        lo = self.Mgrid[max(i-1,0)]; hi = self.Mgrid[min(i+1,len(self.Mgrid)-1)]
        # golden-section refine on [lo,hi]
        gr = (np.sqrt(5)-1)/2
        a, b = lo, hi; c = b - gr*(b-a); d = a + gr*(b-a)
        fc, fd = slope_for(c)[0], slope_for(d)[0]
        for _ in range(40):
            if fc < fd: b, d, fd = d, c, fc; c = b - gr*(b-a); fc = slope_for(c)[0]
            else:       a, c, fc = c, d, fd; d = a + gr*(b-a); fd = slope_for(d)[0]
        M = c if fc < fd else d
        s, lx, lYv = slope_for(M)
        return s, M, lx, lYv

    def iterate(self, tol=1e-9, maxit=60, verbose=True, warm=None):
        if warm is not None:
            self.U[self.n_extra:] = np.minimum(self.U[self.n_extra:], np.interp(self.lam, warm[0], warm[1]) + 1e-6)
        F0 = self.Ubase[self.n_extra]
        hist = []; self.monotone = True
        for it in range(maxit):
            t0 = time.time()
            F, S, Mw, Xw, Yw = self.solve_once(F0)
            excess = (F - self.U[self.n_extra:]).max()
            if excess > 1e-12: self.monotone = False
            Unew = self.U.copy(); Unew[self.n_extra:] = np.minimum(self.U[self.n_extra:], F)
            diff = np.abs(Unew - self.U).max(); self.U = Unew
            hist.append(float(np.exp(F[-1])))
            if verbose: print(f" it {it:2d}: c={np.exp(F[-1]):.8f}  max|dU|={diff:.2e}  maxexcess={excess:.1e} ({time.time()-t0:.0f}s)", flush=True)
            if diff < tol: break
        self.F, self.S, self.Mw, self.Xw, self.Yw = F, S, Mw, Xw, Yw
        return hist

    def certified(self, dF=2e-7, dY=1e-7):
        """final certificate with explicit slack; verify against U = this F itself"""
        lam, F, S, M, X = self.lam, self.F + dF, self.S, self.Mw, self.Xw
        Y = self.Yw*np.exp(-dY)
        U = self.U.copy(); U[self.n_extra:] = F           # self-consistent region
        mu = self.mu
        m25 = np.inf; m24a = np.inf; m24b = np.inf
        bind = None
        for j in range(len(S)):
            Xj = (1-np.exp(-S[j]))**(1/(1-M[j]))*(1-M[j])
            for l in (lam[j], lam[j+1]):
                Fl = F[j] + S[j]*(l-lam[j])
                m25 = min(m25, Fl + 0.5*(np.log(Xj) + l*(np.log(M[j]) + np.log(Y[j]))))
            A = (mu >= lam[j]) if self.relaxed else np.ones_like(mu, bool)
            ra = ((-np.log(Xj) - mu*np.log(Y[j])) - U); rb = ((-np.log(Y[j]) - mu*np.log(Xj)) - U)
            m24a = min(m24a, ra[A].min()); m24b = min(m24b, rb.min())
            if j == len(S)-1:
                bind = dict(a_min=float(ra[A].min()), a_mu=float(mu[A][ra[A].argmin()]), b_min=float(rb.min()), b_mu=float(mu[rb.argmin()]))
        return dict(c=float(np.exp(F[-1])), min25=float(m25), min24a=float(m24a), min24b=float(m24b),
                    concave=bool(np.diff(S).max() < 0), Ymax=float(Y.max()), bind_at_1=bind)

if __name__ == "__main__":
    relaxed = sys.argv[1] == "relaxed"; n_lin = int(sys.argv[2])
    warm = None
    if len(sys.argv) > 3:
        z = np.load(sys.argv[3]); warm = (z['lam'], z['F'])
    S = Solver2(relaxed=relaxed, n_lin=n_lin, n_geo=max(60, n_lin//10))
    print("variant:", "relaxed" if relaxed else "strict", "intervals:", len(S.lam)-1, flush=True)
    S.iterate(warm=warm)
    print("monotone chain:", S.monotone)
    print("certified:", S.certified())
    j = len(S.S)-1
    print(f"at lam=1: slope={S.S[j]:.6f} M={S.Mw[j]:.6f} X={S.Xw[j]:.6f} Y={S.Yw[j]:.6f}")
    np.savez(f"cert_{'relaxed' if relaxed else 'strict'}_{n_lin}.npz", lam=S.lam, F=S.F, S=S.S, M=S.Mw, X=S.Xw, Y=S.Yw, U=S.U, mu=S.mu)
