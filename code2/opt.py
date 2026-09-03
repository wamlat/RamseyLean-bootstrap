"""
Optimum of the GNNW Theorem-13 framework with the CORRECT admissible-region test
(both colour orientations). Certificate structure:
  * partition lam_0 < ... < lam_N = 1
  * F piecewise linear (slope s_j on interval j), M_j, Y_j piecewise constant
  * X_j = (1-e^{-s_j})^{1/(1-M_j)} (1-M_j)
  * (24): -log X_j - mu log Y_j >= U(mu)  for mu in A_j   [orientation a: k' >= l]
          -log Y_j - mu log X_j >= U(mu)  for mu in (0,1] [orientation b: k' <  l]
  * (25): F(lam) > -1/2 (log X_j + lam (log M_j + log Y_j))  at both endpoints
  * U = previously established bound (bootstrap), U = min(h, Cor.6) below lam_0.
On each interval the minimal admissible slope is found exactly (greedy = optimal
for a piecewise-linear certificate), and the bootstrap U <- F is iterated to its
fixed point.
"""
import numpy as np, json, sys, time

SQ5 = np.sqrt(5.0)
def h(l):      return (1+l)*np.log1p(l) - l*np.log(l)
def F_easy(l): return l*np.log((SQ5+1)*(1+2*l)/(4*l)) + 0.5*np.log1p(2*l)

class Solver:
    def __init__(self, lam_min=1e-4, n_geo=120, n_lin=1200, relaxed=False, mu_extra=150, nX=1600):
        self.lam = np.concatenate([np.geomspace(lam_min, 0.02, n_geo, endpoint=False),
                                   np.linspace(0.02, 1.0, n_lin+1)])
        self.relaxed = relaxed
        self.mu = np.concatenate([np.geomspace(1e-7, lam_min, mu_extra, endpoint=False), self.lam])
        self.n_extra = mu_extra
        self.Ubase = np.minimum(h(self.mu), F_easy(self.mu))
        self.U = self.Ubase.copy()
        self.negLogX = np.geomspace(1e-8, 14.0, nX)      # -log X candidates
        self.logX = -self.negLogX
        self.Mgrid = np.geomspace(1e-6, 0.995, 400)

    # ---- for a given lam and U: logYmax(logX) on the logX grid ----
    def logYmax_curve(self, lamv):
        U, mu, lX = self.U, self.mu, self.logX
        b = -(U[None,:] + mu[None,:]*lX[:,None]).max(axis=1)           # min_mu(-U - mu logX)
        a_all = -(U[None,:] + lX[:,None])/mu[None,:]
        if self.relaxed:
            a_all = np.where(mu[None,:] >= lamv, a_all, np.inf)
        a = a_all.min(axis=1)
        return np.minimum(0.0, np.minimum(a, b))

    # ---- minimal slope at (lam, F) and the witnesses ----
    def min_slope(self, lamv, Fv):
        lY = self.logYmax_curve(lamv)
        g = self.logX + lamv*lY                                          # must be >= -2F - lam log M
        best = (np.inf, None, None, None)
        for M in self.Mgrid:
            target = -2.0*Fv - lamv*np.log(M)
            idx = np.nonzero(g >= target)[0]
            if idx.size == 0: continue
            i = idx[0]                                                   # smallest |logX| ... grid is increasing in |logX|? no:
            # logX grid goes from ~0 down to -14 (negLogX increasing) -> logX decreasing, g typically decreasing
            # we want the LARGEST logX (smallest X) ... careful: smaller s -> smaller X -> more negative logX.
            # We need the minimal s, i.e. the minimal X satisfying g(logX) >= target, i.e. the most negative logX.
            # Since g decreases as logX decreases, the set {g>=target} is an initial segment; take its last index.
            i = idx[-1]
            lx = self.logX[i]
            if i+1 < len(self.logX):                                     # refine between i (ok) and i+1 (fails)
                g0, g1 = g[i], g[i+1]
                if g0 != g1:
                    t = (g0 - target)/(g0 - g1)
                    lx = self.logX[i] + t*(self.logX[i+1]-self.logX[i])
                    lYv = lY[i] + t*(lY[i+1]-lY[i])
                else: lYv = lY[i]
            else: lYv = lY[i]
            if lx >= np.log1p(-M): continue                              # X must be < 1-M
            q = (lx - np.log1p(-M))*(1-M)                                # = log(1-e^{-s})
            s = -np.log(-np.expm1(q))
            if s < best[0]: best = (s, M, lx, lYv)
        return best

    def solve_once(self, F0):
        lam = self.lam; N = len(lam)
        F = np.empty(N); S = np.empty(N-1); Mw = np.empty(N-1); Xw = np.empty(N-1); Yw = np.empty(N-1)
        F[0] = F0
        for j in range(N-1):
            s, M, lx, ly = self.min_slope(lam[j], F[j])
            if not np.isfinite(s): raise RuntimeError(f"infeasible at lam={lam[j]}, F={F[j]}")
            S[j], Mw[j], Xw[j], Yw[j] = s, M, np.exp(lx), np.exp(ly)
            F[j+1] = F[j] + s*(lam[j+1]-lam[j])
        return F, S, Mw, Xw, Yw

    def iterate(self, tol=1e-9, maxit=60, verbose=True):
        F0 = self.Ubase[self.n_extra]                                     # known bound at lam_min
        hist = []
        for it in range(maxit):
            t0 = time.time()
            F, S, Mw, Xw, Yw = self.solve_once(F0)
            Unew = self.U.copy()
            Unew[self.n_extra:] = np.minimum(self.U[self.n_extra:], F)
            diff = np.abs(Unew - self.U).max()
            self.U = Unew
            hist.append(float(np.exp(F[-1])))
            if verbose:
                print(f" it {it:2d}: F(1)={F[-1]:.8f}  c={np.exp(F[-1]):.7f}  max|dU|={diff:.2e}  ({time.time()-t0:.1f}s)", flush=True)
            if diff < tol: break
        self.F, self.S, self.Mw, self.Xw, self.Yw = F, S, Mw, Xw, Yw
        return hist

    # ---- independent replay of the certificate ----
    def verify(self, slack=0.0):
        lam, F, S, M, X, Y = self.lam, self.F, self.S, self.Mw, self.Xw, self.Yw
        U = self.U; mu = self.mu
        m25 = np.inf; m24a = np.inf; m24b = np.inf; conc = np.diff(S).max()
        worst = {}
        for j in range(len(S)):
            Xj = (1-np.exp(-S[j]))**(1/(1-M[j]))*(1-M[j])
            assert abs(Xj - X[j]) < 1e-9
            for l in (lam[j], lam[j+1]):
                Fl = F[j] + S[j]*(l-lam[j])
                r = -0.5*(np.log(Xj) + l*(np.log(M[j]) + np.log(Y[j])))
                if Fl - r < m25: m25 = Fl - r; worst['25'] = (l,)
            A = (mu >= lam[j]) if self.relaxed else np.ones_like(mu, bool)
            ma = ((-np.log(Xj) - mu*np.log(Y[j])) - U)[A].min()
            mb = ((-np.log(Y[j]) - mu*np.log(Xj)) - U).min()
            if ma < m24a: m24a = ma; worst['24a'] = (lam[j], mu[A][((-np.log(Xj) - mu*np.log(Y[j])) - U)[A].argmin()])
            if mb < m24b: m24b = mb; worst['24b'] = (lam[j], mu[((-np.log(Y[j]) - mu*np.log(Xj)) - U).argmin()])
        return dict(min25=m25, min24a=m24a, min24b=m24b, max_slope_increase=conc, worst=worst,
                    Ymax=Y.max(), Xmin=X.min(), Mmin=M.min(), Mmax=M.max())

if __name__ == "__main__":
    relaxed = (len(sys.argv) > 1 and sys.argv[1] == "relaxed")
    n_lin = int(sys.argv[2]) if len(sys.argv) > 2 else 600
    S = Solver(relaxed=relaxed, n_lin=n_lin, n_geo=max(60, n_lin//10))
    print("variant:", "relaxed (a) on [lam,1]" if relaxed else "strict (a) on (0,1]", " intervals:", len(S.lam)-1)
    hist = S.iterate()
    print("verify:", S.verify())
    j = len(S.S)-1
    print(f"at lam=1: slope={S.S[j]:.6f} M={S.Mw[j]:.6f} X={S.Xw[j]:.6f} Y={S.Yw[j]:.6f}")
    np.savez(f"/home/claude/ramsey/cert_{'relaxed' if relaxed else 'strict'}_{n_lin}.npz",
             lam=S.lam, F=S.F, S=S.S, M=S.Mw, X=S.Xw, Y=S.Yw, U=S.U, mu=S.mu)
